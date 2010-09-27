val load_logic_extra_rules :
  string list ->
  string ->
  Psyntax.rules Load.importoption list ->
  Psyntax.sequent_rule list * Psyntax.rewrite_rule list * string list
val load_logic :
  string list ->
  string ->
  Psyntax.sequent_rule list * Psyntax.rewrite_rule list * string list
