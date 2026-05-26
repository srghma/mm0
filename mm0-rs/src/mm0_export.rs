//! MM1 to MM0 translation utility
use std::fs;
use std::io::{self, Write};
use std::sync::Arc;
use std::fmt;
use std::collections::HashSet;
use std::path::PathBuf;
use mm0_util::{FileRef, LinedString, Modifiers, Span};
use mm1_parser::{parse, ast::{Ast, Stmt, StmtKind, DeclKind}};
use crate::compiler;
use crate::elab::ElabResult;
use crate::lisp::print::FormatEnv;
use crate::lisp::pretty::Pretty;
use crate::DeclKey;
use futures::executor::block_on;

/// Command line arguments for `mm0-rs mm1-to-mm0` subcommand.
#[derive(clap::Args, Debug)]
pub struct Args {
  /// Strip comments from the output
  #[clap(long)]
  pub strip_comments: bool,
  /// Do not inline imports. If you use this, you probably want to use the `join` command later to inline the imports, since conforming MM0 verifiers (like `mm0-c`) do not support `import` statements.
  #[clap(long)]
  pub no_inline_imports: bool,
  /// Sets the input file (.mm1)
  pub input: String,
  /// Sets the output file (.mm0), or defaults to same path as input with .mm0 extension if omitted
  pub output: Option<String>,
}

struct NewlineFilter<W: Write> {
  w: W,
  newlines: usize,
  pending_whitespace: Vec<u8>,
  has_non_ws: bool,
}

impl<W: Write> NewlineFilter<W> {
  fn new(w: W) -> Self {
    NewlineFilter {
      w,
      newlines: 0,
      pending_whitespace: Vec::new(),
      has_non_ws: false,
    }
  }
}

impl<W: Write> Write for NewlineFilter<W> {
  fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
    for &c in buf {
      if c == b'\n' {
        if self.has_non_ws {
          self.pending_whitespace.clear();
          self.w.write_all(&[b'\n'])?;
          self.newlines = 1;
          self.has_non_ws = false;
        } else {
          self.pending_whitespace.clear();
          self.newlines += 1;
          if self.newlines <= 2 {
            self.w.write_all(&[b'\n'])?;
          }
        }
      } else if c == b' ' || c == b'\t' || c == b'\r' {
        self.pending_whitespace.push(c);
      } else {
        if !self.pending_whitespace.is_empty() {
          self.w.write_all(&self.pending_whitespace)?;
          self.pending_whitespace.clear();
        }
        self.w.write_all(&[c])?;
        self.newlines = 0;
        self.has_non_ws = true;
      }
    }
    Ok(buf.len())
  }

  fn flush(&mut self) -> io::Result<()> {
    self.pending_whitespace.clear();
    self.w.flush()
  }
}

struct PrettyDecl<'a> {
  fe: FormatEnv<'a>,
  tid: crate::TermId,
  show_def: bool,
}

impl fmt::Display for PrettyDecl<'_> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    self.fe.pretty(|p: &Pretty<'_>| p.term(self.tid, self.show_def).render_fmt(80, f))
  }
}

struct PrettyThm<'a> {
  fe: FormatEnv<'a>,
  tid: crate::ThmId,
}

impl fmt::Display for PrettyThm<'_> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    self.fe.pretty(|p: &Pretty<'_>| p.thm(self.tid).render_fmt(80, f))
  }
}

fn write_stripped(w: &mut impl Write, bytes: &[u8]) -> io::Result<()> {
  let mut in_string = false;
  let mut in_math = false;
  let mut in_comment = false;
  let mut i = 0;
  while i < bytes.len() {
    let c = bytes[i];
    if in_comment {
      if c == b'\n' {
        in_comment = false;
        w.write_all(&[b'\n'])?;
      }
    } else if in_string {
      if c == b'\\' && i + 1 < bytes.len() {
        w.write_all(&bytes[i..i+2])?;
        i += 2;
        continue;
      } else if c == b'\"' {
        in_string = false;
      }
      w.write_all(&[c])?;
    } else if in_math {
      if c == b'$' {
        in_math = false;
      }
      w.write_all(&[c])?;
    } else {
      if c == b'\"' {
        in_string = true;
        w.write_all(&[c])?;
      } else if c == b'$' {
        in_math = true;
        w.write_all(&[c])?;
      } else if c == b'-' && i + 1 < bytes.len() && bytes[i+1] == b'-' {
        in_comment = true;
        i += 1;
      } else {
        w.write_all(&[c])?;
      }
    }
    i += 1;
  }
  Ok(())
}

fn is_local_id(fe: FormatEnv<'_>, ast: &Ast, id: Span) -> bool {
  let name_bytes = &ast.source[id];
  if let Some(&name_atom) = fe.env.atoms.get(name_bytes) {
    let ad = &fe.env.data[name_atom];
    if let Some(DeclKey::Term(tid)) = ad.decl {
      let td = &fe.env.terms[tid];
      return td.vis.contains(Modifiers::LOCAL);
    }
  }
  false
}

fn will_omit(s: &Stmt, ast: &Ast, fe: FormatEnv<'_>, input_path: &FileRef) -> bool {
  match &s.k {
    StmtKind::Do(_) => true,
    StmtKind::Decl(decl) => match decl.k {
      DeclKind::Def => decl.mods.contains(Modifiers::LOCAL),
      DeclKind::Thm => !decl.mods.contains(Modifiers::PUB),
      _ => false,
    },
    StmtKind::SimpleNota(n) => is_local_id(fe, ast, n.id),
    StmtKind::Notation(n) => is_local_id(fe, ast, n.id),
    StmtKind::Coercion { id, .. } => is_local_id(fe, ast, *id),
    StmtKind::Annot(_, s2) => will_omit(s2, ast, fe, input_path),
    StmtKind::DocComment(_, s2) => will_omit(s2, ast, fe, input_path),
    StmtKind::Inout { .. } => true,
    _ => false,
  }
}

fn translate_import<W: Write>(
  w: &mut W,
  path_bytes: &[u8],
  input_path: &FileRef,
  no_inline_imports: bool,
  fe: FormatEnv<'_>,
  strip_comments: bool,
  working: &mut HashSet<FileRef>,
) -> io::Result<()> {
  let path_str = std::str::from_utf8(path_bytes).map_err(|_|
    io::Error::new(io::ErrorKind::InvalidInput, "invalid utf8"))?;
  if no_inline_imports {
    let new_path = if path_str.ends_with(".mm1") {
      format!("{}{}", &path_str[..path_str.len() - 4], ".mm0")
    } else {
      path_str.to_string()
    };
    write!(w, "import \"{}\";", new_path)?;
  } else {
    let r: FileRef = input_path.path().parent()
      .map_or_else(|| PathBuf::from(path_str), |p| p.join(path_str))
      .canonicalize()?.into();
    if working.insert(r.clone()) {
      translate_file(w, &r, fe, strip_comments, no_inline_imports, working)?;
    }
  }
  Ok(())
}

fn translate_notation<W: Write>(
  w: &mut W,
  n: &mm1_parser::ast::GenNota,
  span: Span,
  ast: &Ast,
  fe: FormatEnv<'_>,
  strip_comments: bool,
) -> io::Result<()> {
  let write_raw = |w: &mut W, span: Span| -> io::Result<()> {
    let bytes = &ast.source.as_bytes()[span.start..span.end];
    if strip_comments {
      write_stripped(w, bytes)
    } else {
      w.write_all(bytes)
    }
  };

  if !is_local_id(fe, ast, n.id) {
    if !n.lits.isds_empty() && matches!(n.lits[0], mm1_parser::ast::Literal::Var(_)) {
      let term_name = std::str::from_utf8(&ast.source[n.id]).unwrap();
      let mut binder_names = Vec::new();
      for bi in &n.bis {
        let span = bi.local.unwrap_or(bi.span);
        binder_names.push(std::str::from_utf8(&ast.source[span]).unwrap());
      }
      let binders_str = binder_names.join(" ");
      write!(w, "notation {term_name} ({binders_str}) = (${term_name}$:max) {binders_str};")?;
    } else {
      write_raw(w, span)?;
    }
  }
  Ok(())
}

fn translate_decl<W: Write>(
  w: &mut W,
  decl: &mm1_parser::ast::Decl,
  span: Span,
  ast: &Ast,
  fe: FormatEnv<'_>,
  strip_comments: bool,
) -> io::Result<()> {
  let write_raw = |w: &mut W, span: Span| -> io::Result<()> {
    let bytes = &ast.source.as_bytes()[span.start..span.end];
    if strip_comments {
      write_stripped(w, bytes)
    } else {
      w.write_all(bytes)
    }
  };

  let name_bytes = &ast.source[decl.id];
  if let Some(&name_atom) = fe.env.atoms.get(name_bytes) {
    let ad = &fe.env.data[name_atom];
    match decl.k {
      DeclKind::Term => {
        write_raw(w, span)?;
      }
      DeclKind::Axiom => {
        if let Some(DeclKey::Thm(tid)) = ad.decl {
          let mut printed = format!("{}", PrettyThm { fe, tid });
          if printed.starts_with("pub ") {
            printed = printed["pub ".len()..].to_string();
          }
          write!(w, "{printed}")?;
        } else {
          write_raw(w, span)?;
        }
      }
      DeclKind::Def => {
        if decl.mods.contains(Modifiers::LOCAL) {
          return Ok(());
        }
        let show_def = !decl.mods.contains(Modifiers::ABSTRACT);
        if let Some(DeclKey::Term(tid)) = ad.decl {
          let mut printed = format!("{}", PrettyDecl { fe, tid, show_def });
          if printed.starts_with("abstract ") {
            printed = printed["abstract ".len()..].to_string();
          }
          if printed.starts_with("pub ") {
            printed = printed["pub ".len()..].to_string();
          }
          if printed.starts_with("local ") {
            printed = printed["local ".len()..].to_string();
          }
          write!(w, "{printed}")?;
        } else {
          write_raw(w, span)?;
        }
      }
      DeclKind::Thm => {
        if !decl.mods.contains(Modifiers::PUB) {
          return Ok(());
        }
        if let Some(DeclKey::Thm(tid)) = ad.decl {
          let mut printed = format!("{}", PrettyThm { fe, tid });
          if printed.starts_with("pub ") {
            printed = printed["pub ".len()..].to_string();
          }
          write!(w, "{printed}")?;
        } else {
          write_raw(w, span)?;
        }
      }
    }
  } else {
    write_raw(w, span)?;
  }
  Ok(())
}

fn translate_stmt<W: Write>(
  w: &mut W,
  s: &Stmt,
  ast: &Ast,
  fe: FormatEnv<'_>,
  strip_comments: bool,
  input_path: &FileRef,
  no_inline_imports: bool,
  working: &mut HashSet<FileRef>,
) -> io::Result<()> {
  let write_raw = |w: &mut W, span: Span| -> io::Result<()> {
    let bytes = &ast.source.as_bytes()[span.start..span.end];
    if strip_comments {
      write_stripped(w, bytes)
    } else {
      w.write_all(bytes)
    }
  };

  match &s.k {
    StmtKind::Sort(_, _) |
    StmtKind::Delimiter(_) => {
      write_raw(w, s.span)?;
    }
    StmtKind::Inout { .. } => {}
    StmtKind::SimpleNota(n) => {
      if !is_local_id(fe, ast, n.id) {
        write_raw(w, s.span)?;
      }
    }
    StmtKind::Coercion { id, .. } => {
      if !is_local_id(fe, ast, *id) {
        write_raw(w, s.span)?;
      }
    }
    StmtKind::Notation(n) => {
      translate_notation(w, n, s.span, ast, fe, strip_comments)?;
    }
    StmtKind::Annot(_, s2) => {
      if !will_omit(s2, ast, fe, input_path) {
        translate_stmt(w, s2, ast, fe, strip_comments, input_path, no_inline_imports, working)?;
      }
    }
    StmtKind::DocComment(_doc, s2) => {
      if !will_omit(s2, ast, fe, input_path) {
        if !strip_comments {
          write_raw(w, (s.span.start..s2.span.start).into())?;
        }
        translate_stmt(w, s2, ast, fe, strip_comments, input_path, no_inline_imports, working)?;
      }
    }
    StmtKind::Do(_) => {}
    StmtKind::Import(_sp, path_bytes) => {
      translate_import(w, path_bytes, input_path, no_inline_imports, fe, strip_comments, working)?;
    }
    StmtKind::Decl(decl) => {
      translate_decl(w, decl, s.span, ast, fe, strip_comments)?;
    }
  }
  Ok(())
}

fn translate_file<W: Write>(
  w: &mut W,
  path: &FileRef,
  fe: FormatEnv<'_>,
  strip_comments: bool,
  no_inline_imports: bool,
  working: &mut HashSet<FileRef>,
) -> io::Result<()> {
  let src = Arc::<LinedString>::new(fs::read_to_string(path.path())?.into());
  let (_, ast) = parse(src.clone(), None);
  let fe_file = FormatEnv { source: &src, env: fe.env };

  let mut start = 0;
  for s in &ast.stmts {
    let before_span: Span = (start..s.span.start).into();
    let before_bytes = &src.as_bytes()[before_span.start..before_span.end];
    if strip_comments {
      write_stripped(w, before_bytes)?;
    } else {
      w.write_all(before_bytes)?;
    }
    translate_stmt(w, s, &ast, fe_file, strip_comments, path, no_inline_imports, working)?;
    start = s.span.end;
  }
  let remaining_span: Span = (start..src.as_bytes().len()).into();
  let remaining_bytes = &src.as_bytes()[remaining_span.start..remaining_span.end];
  if strip_comments {
    write_stripped(w, remaining_bytes)?;
  } else {
    w.write_all(remaining_bytes)?;
  }
  Ok(())
}

fn elaborate_input_file(path: &FileRef) -> io::Result<crate::elab::frozen::FrozenEnv> {
  match block_on(compiler::elaborate(path.clone(), Default::default()))? {
    ElabResult::Ok(_, _, env) => Ok(env),
    ElabResult::Canceled => Err(io::Error::new(io::ErrorKind::Interrupted, "canceled")),
    ElabResult::ImportCycle(cyc) => {
      let mut s = "import cycle: ".to_owned();
      for p in &cyc { s += &format!("{p} -> ") }
      Err(io::Error::new(io::ErrorKind::InvalidInput, s))
    }
  }
}

fn rewrite_generalized_infixes(env_mut_ref: &mut crate::Environment) {
  let mut to_rewrite = Vec::new();
  for (&term_id, &(_has_coe, ref fix)) in &env_mut_ref.pe.decl_nota {
    if let Some(&(ref tk, infix)) = fix.first() {
      if infix {
        if let Some(info) = env_mut_ref.pe.infixes.get(tk) {
          if info.is_infix().is_none() {
            to_rewrite.push((term_id, tk.clone()));
          }
        }
      }
    }
  }

  for (term_id, tk) in to_rewrite {
    if let Some(info) = env_mut_ref.pe.infixes.remove(&tk) {
      let term_name = env_mut_ref.terms[term_id].atom;
      let term_name_str = env_mut_ref.data[term_name].name.clone();

      let lits = (0..info.nargs)
        .map(|i| crate::Literal::Var(i, crate::Prec::Max))
        .collect::<Vec<_>>();

      let prefix_info = crate::NotaInfo {
        span: info.span.clone(),
        term: term_id,
        nargs: info.nargs,
        rassoc: Some(true),
        lits,
      };

      env_mut_ref.pe.prefixes.insert(term_name_str.clone(), prefix_info);
      env_mut_ref.pe.decl_nota.insert(term_id, (false, vec![(term_name_str.clone(), false)]));
      env_mut_ref.pe.consts.insert(term_name_str.clone(), (info.span.clone(), crate::Prec::Max));
    }
  }
}

fn determine_output_path(input: &str, output: Option<&str>) -> PathBuf {
  match output {
    Some(path) => PathBuf::from(path),
    None => {
      let mut p = PathBuf::from(input);
      p.set_extension("mm0");
      p
    }
  }
}

impl Args {
  /// Executable entry point for the `mm1-to-mm0` subcommand.
  pub fn main(self) -> io::Result<()> {
    let path: FileRef = fs::canonicalize(&self.input)?.into();
    let env = elaborate_input_file(&path)?;

    // We rewrite any generalized infix notation into a prefix notation in the environment
    // to comply with the minimal MM0 specification!
    // Since this runs synchronously during export, we mutably cast the environment safely.
    let env_mut_ref: &mut crate::Environment = unsafe { env.as_mut_env() };
    rewrite_generalized_infixes(env_mut_ref);

    let src = Arc::<LinedString>::new(fs::read_to_string(&self.input)?.into());
    let fe = FormatEnv { source: &src, env: env_mut_ref };

    let out_path = determine_output_path(&self.input, self.output.as_deref());
    let mut out = NewlineFilter::new(fs::File::create(out_path)?);

    let mut working = HashSet::new();
    working.insert(path.clone());
    translate_file(&mut out, &path, fe, self.strip_comments, self.no_inline_imports, &mut working)?;
    Ok(())
  }
}
