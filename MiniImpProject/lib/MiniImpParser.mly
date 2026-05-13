%{
    open MiniImp
%}

%token <string> VAR
%token <int> NUM
%token DEF MAIN WITH INPUT OUTPUT AS IF THEN ELSE WHILE DO AND NOT PLUS MINUS TIMES LESS TRUE FALSE SKIP ASSIGN SEQ EOF LEFTP RIGHTP
%left PLUS MINUS
%left TIMES AND
%nonassoc NOT
%left SEQ
%nonassoc DO ELSE

%start prg
%type <main> prg

%%

prg:
    | DEF MAIN WITH INPUT VAR OUTPUT VAR AS cmd EOF     {Main ($5, $7, $9)}
cmd:
    | SKIP                              {Skip}
    | VAR ASSIGN num                    {Assign ($1, $3)}
    | cmd SEQ cmd                       {Sequence ($1, $3)}
    | IF boolean THEN cmd ELSE cmd      {IfThenElse ($2, $4, $6)}
    | WHILE boolean DO cmd              {While ($2, $4)}
    | LEFTP cmd RIGHTP                  {$2}
boolean:
    | TRUE                              {True}
    | FALSE                             {False}
    | boolean AND boolean               {And ($1, $3)}
    | NOT boolean                       {Not ($2)}
    | num LESS num                      {LessThan ($1, $3)}
    | LEFTP boolean RIGHTP              {$2}
num:
    | VAR                               {Var ($1)}
    | NUM                               {Number ($1)}
    | num PLUS num                      {Plus ($1, $3)}
    | num MINUS num                     {Minus ($1, $3)}
    | num TIMES num                     {Times ($1, $3)}
    | PLUS num                          {$2}
    | MINUS num                         {Minus (Number(0), $2)}
    | LEFTP num RIGHTP                  {$2}
