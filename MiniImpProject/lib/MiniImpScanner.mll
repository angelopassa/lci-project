{
    open MiniImpParser
    exception LexingError of string
}

let keywords = "{def}" | "{main}" | "{with}" | "{input}" | "{output}" | " {as} " | "{and}" | "{not}" | "{do}" | "{if}" | "{then}" | "{else}" | "{skip}"
let white = [' ' '\t']+ | '\r' | '\n' | "\r\n"
let variable = ['a'-'z''A'-'Z'] ['a'-'z''A'-'Z''0'-'9''_']*
let number = ['0'-'9']+

rule read = parse
| white         {read lexbuf}
| number        {NUM(int_of_string (Lexing.lexeme lexbuf))}
| "def"         {DEF}
| "main"        {MAIN}
| "with"        {WITH}
| "input"       {INPUT}
| "output"      {OUTPUT}
| "as"          {AS}
| "skip"        {SKIP}
| ";"           {SEQ}
| "if"          {IF}
| "then"        {THEN}
| "else"        {ELSE}
| "while"       {WHILE}
| "do"          {DO}
| "and"         {AND}
| "not"         {NOT}
| "+"           {PLUS}
| "-"           {MINUS}
| "*"           {TIMES}
| "<"           {LESS}
| ":="          {ASSIGN}
| "("           {LEFTP}
| ")"           {RIGHTP}
| "true"        {TRUE}
| "false"       {FALSE}
| variable      {VAR(Lexing.lexeme lexbuf)}
| eof           {EOF}
| _ {raise (LexingError (Lexing.lexeme lexbuf))}
