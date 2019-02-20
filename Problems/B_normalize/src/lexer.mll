{
open Parser
}

let variable = ['a' - 'z'] + ['a' - 'z' '0' - '9' '\'']*
let white_space = [' ' '\t' '\n' '\r' '\b']+

rule main = parse
        | white_space   { main lexbuf }
        | variable as v { VAR(v) }
        | "\\"          { LMBD }
        | "."           { DOT }
        | "("           { OPEN }
        | ")"           { CLOSE }
        | eof           { EOF }

(* type Token? *)
