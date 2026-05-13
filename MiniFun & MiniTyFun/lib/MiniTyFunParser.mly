%{
    open MiniTyFun
%}

%token <string> VAR
%token <int> INT
%token <bool> BOOL
%token PLUS MINUS TIMES LESS AND NOT
%token IF THEN ELSE
%token LET LETFUN FUN DOTS EQUAL IN ARROWFUN LEFTP RIGHTP EOF
%token TINT TBOOL ARROWTYPE

%right ARROWTYPE
%nonassoc ARROWFUN ELSE IN
%left PLUS MINUS
%left TIMES
%left AND
%left LESS
%nonassoc NOT

%start initial
%type <term> initial
%type <term> first_level
%type <term> second_level
%type <term> third_level
%type <tau> types

%%

initial:
    | first_level EOF                                                   {$1}
first_level:
    | second_level                                                      {$1}
    | LET VAR EQUAL first_level IN first_level                          {Let ($2, $4, $6)}
    | IF first_level THEN first_level ELSE first_level                  {IfThenElse ($2, $4, $6)}
    | FUN VAR DOTS types ARROWFUN first_level                           {Fun ($2, $4, $6)}
    | LETFUN VAR VAR DOTS types EQUAL first_level IN first_level        {LetFun ($2, $5, $3, $7, $9)}
    | first_level AND first_level                                       {Bop ($1, $3, And)}
    | first_level TIMES first_level                                     {Bop ($1, $3, Times)}
    | first_level MINUS first_level                                     {Bop ($1, $3, Minus)}
    | first_level LESS first_level                                      {Bop ($1, $3, LessThan)}
    | first_level PLUS first_level                                      {Bop ($1, $3, Plus)}
    | NOT first_level                                                   {Not ($2)}
    | PLUS first_level                                                  {$2}
    | MINUS first_level                                                 {Bop (Int(0), $2, Minus)}
second_level:
    | third_level                                                       {$1}
    | third_level second_level                                          {App ($1, $2)}
third_level:
    | LEFTP first_level RIGHTP                                          {$2}
    | VAR                                                               {Var ($1)}
    | INT                                                               {Int ($1)}
    | BOOL                                                              {Bool ($1)}
types:
    | TINT                                                              {TInt}
    | TBOOL                                                             {TBool}
    | LEFTP types RIGHTP                                                {$2}
    | types ARROWTYPE types                                             {Arrow ($1, $3)}