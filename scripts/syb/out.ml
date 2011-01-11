open Jstar_std

class mapper = object(self)
  method map_array_brackets : array_brackets -> array_brackets =
    self#map_string
  method map_array_descriptor : array_descriptor -> array_descriptor =
    fmap self#map_immediate
  method map_at_identifier : at_identifier -> at_identifier = self#map_string
  method map_binop : binop -> binop =
    function And -> And| Or -> Or| Xor -> Xor| Mod -> Mod| Cmp -> Cmp
    | Cmpg -> Cmpg| Cmpl -> Cmpl| Cmpeq -> Cmpeq| Cmpne -> Cmpne
    | Cmpgt -> Cmpgt| Cmpge -> Cmpge| Cmplt -> Cmplt| Cmple -> Cmple
    | Shl -> Shl| Shr -> Shr| Ushr -> Ushr| Plus -> Plus| Minus -> Minus
    | Mult -> Mult| Div -> Div
  method map_bool_expr : bool_expr -> bool_expr =
    function True -> True| False -> False
  method map_case_label : case_label -> case_label =
    function Case_label_default -> Case_label_default
    | Case_label(_2, _4) -> Case_label (self#map_sign _2, self#map_int _4)
  method map_case_statement : case_statement -> case_statement =
    function
    Case_stmt(_2, _4) ->
    Case_stmt (self#map_case_label _2, self#map_label_name _4)
  method map_catch_clause : catch_clause -> catch_clause =
    function
    Catch_clause(_2, _4, _6, _8) ->
    Catch_clause (self#map_class_name _2, self#map_label_name _4
    , self#map_label_name _6, self#map_label_name _8)
  method map_class_name : class_name -> class_name =
    function Quoted_clname _2 -> Quoted_clname (self#map_string _2)
    | Identifier_clname _2 -> Identifier_clname (self#map_string _2)
    | Full_identifier_clname _2 ->
      Full_identifier_clname (self#map_string _2)
    
  method map_constant : constant -> constant =
    function
    Int_const(_2, _4) -> Int_const (self#map_sign _2, self#map_int _4)
    | Int_const_long(_2, _4) ->
      Int_const_long (self#map_sign _2, self#map_int _4)
    | Float_const(_2, _4) ->
      Float_const (self#map_sign _2, self#map_float _4)
    | String_const _2 -> String_const (self#map_string _2)
    | Clzz_const _2 -> Clzz_const (self#map_string _2)
    | Null_const -> Null_const
  method map_declaration : declaration -> declaration =
    function
    Declaration(_3, _6) ->
    Declaration ((fmap self#map_j_type) _3, (List.map self#map_name) _6)
  method map_expression : expression -> expression =
    function New_simple_exp _2 -> New_simple_exp (self#map_j_base_type _2)
    | New_array_exp(_2, _4) ->
      New_array_exp (self#map_nonvoid_type _2
      , self#map_fixed_array_descriptor _4)
    | New_multiarray_exp(_2, _5) ->
      New_multiarray_exp (self#map_j_base_type _2
      , (List.map self#map_array_descriptor) _5)
    | Cast_exp(_2, _4) ->
      Cast_exp (self#map_nonvoid_type _2, self#map_immediate _4)
    | Instanceof_exp(_2, _4) ->
      Instanceof_exp (self#map_immediate _2, self#map_nonvoid_type _4)
    | Binop_exp(_2, _4, _6) ->
      Binop_exp (self#map_binop _2, self#map_immediate _4
      , self#map_immediate _6)
    | Unop_exp(_2, _4) -> Unop_exp (self#map_unop _2, self#map_immediate _4)
    | Invoke_exp _2 -> Invoke_exp (self#map_invoke_expr _2)
    | Immediate_exp _2 -> Immediate_exp (self#map_immediate _2)
    | Reference_exp _2 -> Reference_exp (self#map_reference _2)
  method map_extends_clause : extends_clause -> extends_clause =
    List.map self#map_class_name
  method map_field_signature : field_signature -> field_signature =
    function
    _2, _4, _6 ->
    (self#map_class_name _2, self#map_j_type _4, self#map_name _6)
  method map_fixed_array_descriptor : fixed_array_descriptor -> fixed_array_descriptor =
    self#map_immediate
  method map_float : float -> float = identity
  method map_full_identifier : full_identifier -> full_identifier =
    self#map_string
  method map_identifier : identifier -> identifier = self#map_string
  method map_immediate : immediate -> immediate =
    function
    Immediate_local_name _2 -> Immediate_local_name (self#map_name _2)
    | Immediate_constant _2 -> Immediate_constant (self#map_constant _2)
  method map_implements_clause : implements_clause -> implements_clause =
    List.map self#map_class_name
  method map_int : int -> int = identity
  method map_invoke_expr : invoke_expr -> invoke_expr =
    function
    Invoke_nostatic_exp(_2, _4, _6, _9) ->
    Invoke_nostatic_exp (self#map_nonstatic_invoke _2, self#map_name _4
    , self#map_signature _6, (List.map self#map_immediate) _9)
    | Invoke_static_exp(_2, _5) ->
      Invoke_static_exp (self#map_signature _2
      , (List.map self#map_immediate) _5)
    
  method map_j_base_type : j_base_type -> j_base_type =
    function Boolean -> Boolean| Byte -> Byte| Char -> Char| Short -> Short
    | Int -> Int| Long -> Long| Float -> Float| Double -> Double
    | Null_type -> Null_type
    | Class_name _2 -> Class_name (self#map_class_name _2)
  method map_j_file_type : j_file_type -> j_file_type =
    function ClassFile -> ClassFile| InterfaceFile -> InterfaceFile
  method map_j_type : j_type -> j_type =
    function Void -> Void| Non_void _2 -> Non_void (self#map_nonvoid_type _2)
  method map_label_name : label_name -> label_name = self#map_identifier
  method map_list_class_file : list_class_file -> list_class_file =
    function
    ListClassFile _3 -> ListClassFile ((List.map self#map_string) _3)
  method map_local_var : local_var -> local_var =
    function _3, _5 -> ((fmap self#map_j_type) _3, self#map_name _5)
  method map_method_signature : method_signature -> method_signature =
    function
    _2, _4, _6, _9 ->
    (self#map_class_name _2, self#map_j_type _4, self#map_name _6
    , (List.map self#map_parameter) _9)
  method map_method_signature_short : method_signature_short -> method_signature_short =
    function
    _3, _5, _7, _10 ->
    ((List.map self#map_modifier) _3, self#map_j_type _5, self#map_name _7
    , (List.map self#map_parameter) _10)
  method map_modifier : modifier -> modifier =
    function Abstract -> Abstract| Final -> Final| Native -> Native
    | Public -> Public| Protected -> Protected| Private -> Private
    | Static -> Static| Synchronized -> Synchronized| Transient -> Transient
    | Volatile -> Volatile| Strictfp -> Strictfp| Enum -> Enum
    | Annotation -> Annotation
  method map_name : name -> name =
    function Quoted_name _2 -> Quoted_name (self#map_string _2)
    | Identifier_name _2 -> Identifier_name (self#map_string _2)
  method map_nodekind : nodekind -> nodekind =
    function Start_node -> Start_node| Exit_node -> Exit_node
    | Call_node -> Call_node| Return_Site_node -> Return_Site_node
    | Stmt_node -> Stmt_node
  method map_nonstatic_invoke : nonstatic_invoke -> nonstatic_invoke =
    function Special_invoke -> Special_invoke
    | Virtual_invoke -> Virtual_invoke| Interface_invoke -> Interface_invoke
  method map_nonvoid_type : nonvoid_type -> nonvoid_type =
    function
    Base(_2, _5) ->
    Base (self#map_j_base_type _2, (List.map self#map_array_brackets) _5)
    | Quoted(_2, _5) ->
      Quoted (self#map_quoted_name _2, (List.map self#map_array_brackets) _5)
    | Ident_NVT(_2, _5) ->
      Ident_NVT (self#map_identifier _2
      , (List.map self#map_array_brackets) _5)
    | Full_ident_NVT(_2, _5) ->
      Full_ident_NVT (self#map_full_identifier _2
      , (List.map self#map_array_brackets) _5)
    
  method map_parameter : parameter -> parameter = self#map_nonvoid_type
  method map_parameter_named_option : parameter_named_option -> parameter_named_option =
    function
    _2, _5 -> (self#map_nonvoid_type _2, (fmap self#map_identifier) _5)
  method map_quoted_name : quoted_name -> quoted_name = self#map_string
  method map_reference : reference -> reference =
    function
    Array_ref(_2, _4) ->
    Array_ref (self#map_identifier _2, self#map_immediate _4)
    | Field_local_ref(_2, _4) ->
      Field_local_ref (self#map_name _2, self#map_signature _4)
    | Field_sig_ref _2 -> Field_sig_ref (self#map_signature _2)
  method map_sign : sign -> sign =
    function Positive -> Positive| Negative -> Negative
  method map_signature : signature -> signature =
    function
    Method_signature _2 -> Method_signature (self#map_method_signature _2)
    | Field_signature _2 -> Field_signature (self#map_field_signature _2)
  method map_string : string -> string = identity
  method map_throws_clause : throws_clause -> throws_clause =
    fmap (List.map self#map_class_name)
  method map_unop : unop -> unop = function Lengthof -> Lengthof| Neg -> Neg
  method map_variable : variable -> variable =
    function Var_ref _2 -> Var_ref (self#map_reference _2)
    | Var_name _2 -> Var_name (self#map_name _2)
end
class ['a] evaluator = fun default_value -> object(self)
  method eval_array_brackets : array_brackets -> 'a = self#eval_string
  method eval_array_descriptor : array_descriptor -> 'a =
    (maybe default_value) self#eval_immediate
  method eval_at_identifier : at_identifier -> 'a = self#eval_string
  method eval_binop : binop -> 'a = function _ -> default_value
  method eval_bool_expr : bool_expr -> 'a = function _ -> default_value
  method eval_case_label : case_label -> 'a =
    function Case_label_default -> default_value
    | Case_label(_2, _4) ->
      ((List.fold_left self#combine) default_value)
       [self#eval_sign _2; self#eval_int _4]
    
  method eval_case_statement : case_statement -> 'a =
    function
    Case_stmt(_2, _4) ->
    ((List.fold_left self#combine) default_value)
     [self#eval_case_label _2; self#eval_label_name _4]
  method eval_catch_clause : catch_clause -> 'a =
    function
    Catch_clause(_2, _4, _6, _8) ->
    ((List.fold_left self#combine) default_value)
     [self#eval_class_name _2; self#eval_label_name _4
     ; self#eval_label_name _6; self#eval_label_name _8]
    
  method eval_class_name : class_name -> 'a =
    function Quoted_clname _2 -> self#eval_string _2
    | Identifier_clname _2 -> self#eval_string _2
    | Full_identifier_clname _2 -> self#eval_string _2
  method eval_constant : constant -> 'a =
    function
    Int_const(_2, _4) ->
    ((List.fold_left self#combine) default_value)
     [self#eval_sign _2; self#eval_int _4]
    | Int_const_long(_2, _4) ->
      ((List.fold_left self#combine) default_value)
       [self#eval_sign _2; self#eval_int _4]
    | Float_const(_2, _4) ->
      ((List.fold_left self#combine) default_value)
       [self#eval_sign _2; self#eval_float _4]
    | String_const _2 -> self#eval_string _2
    | Clzz_const _2 -> self#eval_string _2| Null_const -> default_value
  method eval_declaration : declaration -> 'a =
    function
    Declaration(_3, _7) ->
    ((List.fold_left self#combine) default_value)
     [((maybe default_value) self#eval_j_type) _3
     ; (compose
        (((List.fold_left self#combine) default_value)
         (List.map self#eval_name))
       ) _7
     ]
    
  method eval_expression : expression -> 'a =
    function New_simple_exp _2 -> self#eval_j_base_type _2
    | New_array_exp(_2, _4) ->
      ((List.fold_left self#combine) default_value)
       [self#eval_nonvoid_type _2; self#eval_fixed_array_descriptor _4]
    | New_multiarray_exp(_2, _6) ->
      ((List.fold_left self#combine) default_value)
       [self#eval_j_base_type _2
       ; (compose
          (((List.fold_left self#combine) default_value)
           (List.map self#eval_array_descriptor))
         ) _6
       ]
      | Cast_exp(_2, _4) ->
        ((List.fold_left self#combine) default_value)
         [self#eval_nonvoid_type _2; self#eval_immediate _4]
    | Instanceof_exp(_2, _4) ->
      ((List.fold_left self#combine) default_value)
       [self#eval_immediate _2; self#eval_nonvoid_type _4]
    | Binop_exp(_2, _4, _6) ->
      ((List.fold_left self#combine) default_value)
       [self#eval_binop _2; self#eval_immediate _4; self#eval_immediate _6]
    | Unop_exp(_2, _4) ->
      ((List.fold_left self#combine) default_value)
       [self#eval_unop _2; self#eval_immediate _4]
    | Invoke_exp _2 -> self#eval_invoke_expr _2
    | Immediate_exp _2 -> self#eval_immediate _2
    | Reference_exp _2 -> self#eval_reference _2
  method eval_extends_clause : extends_clause -> 'a =
    compose
     (((List.fold_left self#combine) default_value)
      (List.map self#eval_class_name))
    
  method eval_field_signature : field_signature -> 'a =
    function
    _2, _4, _6 ->
    ((List.fold_left self#combine) default_value)
     [self#eval_class_name _2; self#eval_j_type _4; self#eval_name _6]
  method eval_fixed_array_descriptor : fixed_array_descriptor -> 'a =
    self#eval_immediate
  method eval_float : float -> 'a = function _ -> default_value
  method eval_full_identifier : full_identifier -> 'a = self#eval_string
  method eval_identifier : identifier -> 'a = self#eval_string
  method eval_immediate : immediate -> 'a =
    function Immediate_local_name _2 -> self#eval_name _2
    | Immediate_constant _2 -> self#eval_constant _2
  method eval_implements_clause : implements_clause -> 'a =
    compose
     (((List.fold_left self#combine) default_value)
      (List.map self#eval_class_name))
    
  method eval_int : int -> 'a = function _ -> default_value
  method eval_invoke_expr : invoke_expr -> 'a =
    function
    Invoke_nostatic_exp(_2, _4, _6, _10) ->
    ((List.fold_left self#combine) default_value)
     [self#eval_nonstatic_invoke _2; self#eval_name _4
     ; self#eval_signature _6
     ; (compose
        (((List.fold_left self#combine) default_value)
         (List.map self#eval_immediate))
       ) _10
     ]
    | Invoke_static_exp(_2, _6) ->
      ((List.fold_left self#combine) default_value)
       [self#eval_signature _2
       ; (compose
          (((List.fold_left self#combine) default_value)
           (List.map self#eval_immediate))
         ) _6
       ]
      
  method eval_j_base_type : j_base_type -> 'a =
    function Boolean -> default_value| Byte -> default_value
    | Char -> default_value| Short -> default_value| Int -> default_value
    | Long -> default_value| Float -> default_value| Double -> default_value
    | Null_type -> default_value| Class_name _2 -> self#eval_class_name _2
  method eval_j_file_type : j_file_type -> 'a = function _ -> default_value
  method eval_j_type : j_type -> 'a =
    function Void -> default_value| Non_void _2 -> self#eval_nonvoid_type _2
  method eval_label_name : label_name -> 'a = self#eval_identifier
  method eval_list_class_file : list_class_file -> 'a =
    function
    ListClassFile _4 ->
    (compose
     (((List.fold_left self#combine) default_value)
      (List.map self#eval_string))
    ) _4
  method eval_local_var : local_var -> 'a =
    function
    _3, _5 ->
    ((List.fold_left self#combine) default_value)
     [((maybe default_value) self#eval_j_type) _3; self#eval_name _5]
  method eval_method_signature : method_signature -> 'a =
    function
    _2, _4, _6, _10 ->
    ((List.fold_left self#combine) default_value)
     [self#eval_class_name _2; self#eval_j_type _4; self#eval_name _6
     ; (compose
        (((List.fold_left self#combine) default_value)
         (List.map self#eval_parameter))
       ) _10
     ]
    
  method eval_method_signature_short : method_signature_short -> 'a =
    function
    _4, _6, _8, _12 ->
    ((List.fold_left self#combine) default_value)
     [(compose
       (((List.fold_left self#combine) default_value)
        (List.map self#eval_modifier))
      ) _4
     ; self#eval_j_type _6; self#eval_name _8
     ; (compose
        (((List.fold_left self#combine) default_value)
         (List.map self#eval_parameter))
       ) _12
     ]
    
  method eval_modifier : modifier -> 'a = function _ -> default_value
  method eval_name : name -> 'a =
    function Quoted_name _2 -> self#eval_string _2
    | Identifier_name _2 -> self#eval_string _2
  method eval_nodekind : nodekind -> 'a = function _ -> default_value
  method eval_nonstatic_invoke : nonstatic_invoke -> 'a =
    function _ -> default_value
  method eval_nonvoid_type : nonvoid_type -> 'a =
    function
    Base(_2, _6) ->
    ((List.fold_left self#combine) default_value)
     [self#eval_j_base_type _2
     ; (compose
        (((List.fold_left self#combine) default_value)
         (List.map self#eval_array_brackets))
       ) _6
     ]
    | Quoted(_2, _6) ->
      ((List.fold_left self#combine) default_value)
       [self#eval_quoted_name _2
       ; (compose
          (((List.fold_left self#combine) default_value)
           (List.map self#eval_array_brackets))
         ) _6
       ]
      | Ident_NVT(_2, _6) ->
        ((List.fold_left self#combine) default_value)
         [self#eval_identifier _2
         ; (compose
            (((List.fold_left self#combine) default_value)
             (List.map self#eval_array_brackets))
           ) _6
         ]
        | Full_ident_NVT(_2, _6) ->
          ((List.fold_left self#combine) default_value)
           [self#eval_full_identifier _2
           ; (compose
              (((List.fold_left self#combine) default_value)
               (List.map self#eval_array_brackets))
             ) _6
           ]
          
  method eval_parameter : parameter -> 'a = self#eval_nonvoid_type
  method eval_parameter_named_option : parameter_named_option -> 'a =
    function
    _2, _5 ->
    ((List.fold_left self#combine) default_value)
     [self#eval_nonvoid_type _2
     ; ((maybe default_value) self#eval_identifier) _5]
    
  method eval_quoted_name : quoted_name -> 'a = self#eval_string
  method eval_reference : reference -> 'a =
    function
    Array_ref(_2, _4) ->
    ((List.fold_left self#combine) default_value)
     [self#eval_identifier _2; self#eval_immediate _4]
    | Field_local_ref(_2, _4) ->
      ((List.fold_left self#combine) default_value)
       [self#eval_name _2; self#eval_signature _4]
    | Field_sig_ref _2 -> self#eval_signature _2
  method eval_sign : sign -> 'a = function _ -> default_value
  method eval_signature : signature -> 'a =
    function Method_signature _2 -> self#eval_method_signature _2
    | Field_signature _2 -> self#eval_field_signature _2
  method eval_string : string -> 'a = function _ -> default_value
  method eval_throws_clause : throws_clause -> 'a =
    (maybe default_value)
     (compose
      (((List.fold_left self#combine) default_value)
       (List.map self#eval_class_name))
     )
    
  method eval_unop : unop -> 'a = function _ -> default_value
  method eval_variable : variable -> 'a =
    function Var_ref _2 -> self#eval_reference _2
    | Var_name _2 -> self#eval_name _2
end
