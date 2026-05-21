
# Vim syntax

This directory contains some basic vim files for syntax coloring.

## Install

Copy the subdirectories into `$HOME/.vim/`
(e.g. with `cp -r vim/* ~/.vim/`).

With [vim-plug](https://github.com/junegunn/vim-plug), the following stanza
should work (in `.vimrc`):

```
Plug 'digama0/mm0', { 'rtp': 'vim' }
```

With lazy.nvim

```
return { "digama0/mm0", rtp = "vim" }
```

or if local copy

```
return { "digama0/mm0", dir = "/home/srghma/projects/mm0/vim" }
```

## LSP integration (neovim)

Using [LanguageClient](https://github.com/autozimu/LanguageClient-neovim/),
just add to your config file:

```vim
let g:LanguageClient_serverCommands = {
\ 'metamath-zero': ['mm0-rs', 'server'],
\ }
```

(there can be other lines for other languages, of course.)
