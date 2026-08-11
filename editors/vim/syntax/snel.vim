" Vim syntax file for Snel (see ../../../SPEC.md)
" Install: copy to ~/.vim/syntax/snel.vim (and ftdetect/snel.vim alongside).

if exists("b:current_syntax")
  finish
endif

" comments: a full-line `--` before a declaration is a doc comment
syn match   snelDocComment "^\s*--.*$"
syn match   snelComment    "--.*$" contains=@Spell

syn keyword snelKeyword let fun typ mod pub use do end
syn keyword snelConditional if then else try err is where
syn keyword snelBoolean true false
syn keyword snelConstant nil inf nan
syn keyword snelOperatorWord and or not

syn keyword snelType bit i64 f64 u8 str sym

" builtins (language-level names, never shadowed)
syn keyword snelBuiltin add sub mul div rem neg abs itof ftoi sqrt floor ceil
syn keyword snelBuiltin sign ord chr eq ne lt le gt ge len cat iota grade sum
syn keyword snelBuiltin prod min max isnil all any rev take drop first last
syn keyword snelBuiltin which distinct in map map2 fold scan filter group get
syn keyword snelBuiltin select find split join locals reflect show encode
syn keyword snelBuiltin decode parse unparse at rep scatter shift sums prods
syn keyword snelBuiltin member matches runs partition windows
syn keyword snelBuiltin tojson fromjson tocsv fromcsv

" literals
syn match   snelNumber  "\<\d[0-9_]*\>"
syn match   snelNumber  "\<0[xX][0-9a-fA-F_]\+\>"
syn match   snelNumber  "\<0[bB][01_]\+\>"
syn match   snelFloat   "\<\d[0-9_]*\.\d[0-9_]*\([eE][-+]\?\d\+\)\?\>"
syn match   snelFloat   "\<\d[0-9_]*[eE][-+]\?\d\+\>"
syn match   snelBitVec  ":[01][01_]*"
syn match   snelSymbol  ":\a\w*"
syn match   snelChar    "'\(\\x\x\x\|\\.\|[^'\\]\)'"
syn region  snelString  start=+"+ skip=+\\.+ end=+"+ contains=snelEscape
syn match   snelEscape  "\\\(x\x\x\|[nt\\\"]\)" contained

syn match   snelPipe    "|>"
syn match   snelArrow   "->"

hi def link snelDocComment   SpecialComment
hi def link snelComment      Comment
hi def link snelKeyword      Keyword
hi def link snelConditional  Conditional
hi def link snelBoolean      Boolean
hi def link snelConstant     Constant
hi def link snelOperatorWord Operator
hi def link snelType         Type
hi def link snelBuiltin      Function
hi def link snelNumber       Number
hi def link snelFloat        Float
hi def link snelBitVec       Number
hi def link snelSymbol       Constant
hi def link snelChar         Character
hi def link snelString       String
hi def link snelEscape       SpecialChar
hi def link snelPipe         Operator
hi def link snelArrow        Operator

let b:current_syntax = "snel"
