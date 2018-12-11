{
open Parser
}

let variable = ['a' - 'z'] + ['a' - 'z' '0' - '9' '\'']*
let whitespace = [' ' '\t' '\n']*

rule main = parse
        | variable as v { VAR(v) }
        | "\\"          { LMBD }
        | "."           { DOT }
        | "("           { OPEN }
        | ")"           { CLOSE }
        | eof           { EOF }
