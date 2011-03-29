let id_re = ['A'-'Z' 'a'-'z'] ['A'-'Z' 'a'-'z' '0'-'9' '_' '\'']*

rule id hash = parse
  | "(*" { comment lexbuf; id hash lexbuf }
  | id_re as x { Hashtbl.replace hash x (); id hash lexbuf }
  | eof { () }
  | _ { id hash lexbuf }
and id_decl hash = parse
  | "(*" { comment lexbuf; id_decl hash lexbuf }
  | ("val"|"exception") [' ' '\t']+ (id_re as x) [^'\n']* 
    { Hashtbl.replace hash x (); id_decl hash lexbuf }
  | eof { () }
  | _ { id_decl hash lexbuf }
and comment = parse
  | "(*" { comment lexbuf; comment lexbuf }
  | "*)" { () }
  | eof { () }
  | _ { comment lexbuf }
