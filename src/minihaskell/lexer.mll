{
  open Parser
  open Lexing
}

let var = ['_' 'a'-'z'] ['_' 'a'-'z' 'A'-'Z' '0'-'9']*
let cname = ['A'-'Z'] ['_' 'a'-'z' 'A'-'Z' '0'-'9']*

rule token = parse
    "--" [^'\n']* '\n' { Lexing.new_line lexbuf; token lexbuf }
  | '\n'            { Lexing.new_line lexbuf; token lexbuf }
  | [' ' '\t']      { token lexbuf }
  | ['0'-'9']+      { INT (int_of_string(lexeme lexbuf)) }
  | "Bool"          { TBOOL }
  | "case"          { CASE }
  | "data"          { DATA }
  | "else"          { ELSE }
  | "end"           { END }
  | "false"         { FALSE }
  | "fst"           { FST }
  | "fun"           { FUN }
  | "if"            { IF }
  | "Int"           { TINT }
  | "is"            { IS }
  | "let"           { LET }  
  | "list"          { TLIST }
  | "match"         { MATCH }
  | "of"            { OF }
  | "rec"           { REC }
  | "snd"           { SND }
  | "then"          { THEN }
  | "true"          { TRUE }
  | ":quit"         { QUIT }
  | "with"          { WITH }
  | "->"            { TARROW }
  | "=>"            { DARROW }
  | "::"            { CONS }
  | ";;"            { SEMICOLON2 }
  | '%'             { MOD }
  | '('             { LPAREN }
  | ')'             { RPAREN }
  | '*'             { TIMES }
  | '+'             { PLUS }
  | ','             { COMMA }
  | '-'             { MINUS }
  | '_'             { EMPTY }
  | '/'             { DIVIDE }
  | ':'             { COLON }
  | '<'             { LESS }
  | '='             { EQUAL }
  | '['             { LBRACK }
  | ']'             { RBRACK }
  | '|'             { ALTERNATIVE }
  | var             { VAR (lexeme lexbuf) }
  | cname           { CNAME (lexeme lexbuf) }
  | eof             { EOF }

{
}
