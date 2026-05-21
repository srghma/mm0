#![no_main]
#[macro_use]
extern crate libfuzzer_sys;
extern crate mm0_util;
extern crate mm0b_parser;

fuzz_target!(|data: &[u8]| {
  if let Ok(mmb) = mm0b_parser::BareMmbFile::parse(data) {
    for i in 0..data.len() {
      let term_id = mm0_util::TermId(i as u32);
      let thm_id = mm0_util::ThmId(i as u32);
      let _ = mmb.term(term_id);
      let _ = mmb.thm(thm_id);
    }
  }
});
