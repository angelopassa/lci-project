{
    open MiniTyFunParser
    exception LexingError of string
}

let white = [' ' '\t']+ | '\r' | '\n' | "\r\n"
let variable = ['a'-'z''A'-'Z'] ['a'-'z''A'-'Z''0'-'9''_']*
let integer = ['0'-'9']+

rule read = parse
| white         {read lexbuf}
| integer       {INT(int_of_string (Lexing.lexeme lexbuf))}
| "let"         {LET}
| "letfun"      {LETFUN}
| "fun"         {FUN}
| ":"           {DOTS}
| "=>"          {ARROWFUN}
| "->"          {ARROWTYPE}
| "="           {EQUAL}
| "in"          {IN}
| "int"         {TINT}
| "bool"        {TBOOL}
| "if"          {IF}
| "then"        {THEN}
| "else"        {ELSE}
| "+"           {PLUS}
| "-"           {MINUS}
| "*"           {TIMES}
| "<"           {LESS}
| "and"         {AND}
| "not"         {NOT}
| "true"        {BOOL(true)}
| "false"       {BOOL(false)}
| "("           {LEFTP}
| ")"           {RIGHTP}
| variable      {VAR(Lexing.lexeme lexbuf)}
| eof           {EOF}
| _ {raise (LexingError (Lexing.lexeme lexbuf))}
