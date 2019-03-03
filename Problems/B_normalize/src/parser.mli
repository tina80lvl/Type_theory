type token =
  | VAR of (string)
  | OPEN
  | CLOSE
  | DOT
  | EOF
  | LMBD

val main :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Tree.tree
