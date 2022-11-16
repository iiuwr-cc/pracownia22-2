open Ast

let string_of_binop = function
  | BINOP_And -> "&"
  | BINOP_Or -> "|"
  | BINOP_Add -> "+"
  | BINOP_Sub -> "-"
  | BINOP_Mult -> "*"
  | BINOP_Div -> "/"
  | BINOP_Rem -> "%"

let string_of_relop = function
  | RELOP_Eq -> "=="
  | RELOP_Ne -> "!="
  | RELOP_Lt -> "<"
  | RELOP_Gt -> ">"
  | RELOP_Le -> "<="
  | RELOP_Ge -> ">="

let string_of_unop = function UNOP_Not -> "not" | UNOP_Neg -> "-"
let indent x = "  " ^ x
let indentxs = List.map indent

let rec show_expression e =
  match e.data with
  | EXPR_Id x -> string_of_identifier x
  | EXPR_Int value -> Int32.to_string value
  | EXPR_Char value -> Format.sprintf "'%s'" (Char.escaped value)
  | EXPR_String value -> Format.sprintf "\"%s\"" (String.escaped value)
  | EXPR_Bool value -> string_of_bool value
  | EXPR_Binop { op; lhs; rhs } ->
      String.concat ""
        [
          "(";
          show_expression lhs;
          " ";
          string_of_binop op;
          " ";
          show_expression rhs;
          ")";
        ]
  | EXPR_Relation { op; lhs; rhs; _ } ->
      String.concat ""
        [
          "(";
          show_expression lhs;
          " ";
          string_of_relop op;
          " ";
          show_expression rhs;
          ")";
        ]
  | EXPR_Length arg -> String.concat "" [ "length("; show_expression arg; ")" ]
  | EXPR_Unop { op; expr; _ } ->
      String.concat " " [ string_of_unop op; show_expression expr ]
  | EXPR_Call { callee; arguments } -> show_call callee arguments
  | EXPR_Index { expr; index; _ } ->
      String.concat "" [ show_expression expr; "["; show_expression index; "]" ]
  | EXPR_Field { expr; field; _ } ->
      String.concat "" [ show_expression expr; "."; string_of_identifier field ]
  | EXPR_Unfold expr -> String.concat "" [ show_expression expr; "^" ]
  | EXPR_Array elements ->
      String.concat ""
        [ "{"; String.concat ", " (List.map show_expression elements); "}" ]
  | EXPR_Record fields ->
      String.concat ""
        [ "{"; String.concat ", " (List.map show_field_expression fields); "}" ]
  | EXPR_EmptyStruct -> "{}"

and show_field_expression fld =
  match fld.data with
  | FieldExpr { name; value } ->
      String.concat " "
        [ string_of_identifier name; "="; show_expression value ]

and show_call callee arguments =
  String.concat ""
    [
      string_of_identifier callee;
      "(";
      String.concat ", " (List.map show_expression arguments);
      ")";
    ]

let rec show_type_expression tp =
  match tp.data with
  | TEXPR_Id id -> string_of_identifier id
  | TEXPR_Int -> "int"
  | TEXPR_Bool -> "bool"
  | TEXPR_Array sub -> String.concat "" [ show_type_expression sub; "["; "]" ]
  | TEXPR_Record fields ->
      String.concat ""
        [ "{"; String.concat ", " (List.map show_field_type fields); "}" ]

and show_field_type fld =
  match fld.data with
  | FieldType { name; tp } ->
      String.concat " "
        [ string_of_identifier name; "="; show_type_expression tp ]

let show_var_declaration { data = VarDecl { id; tp }; _ } =
  String.concat "" [ string_of_identifier id; ":"; show_type_expression tp ]

let show_lvalue lv =
  match lv.data with
  | LVALUE_Id id -> string_of_identifier id
  | LVALUE_Index { expr; index } ->
      String.concat "" [ show_expression expr; "["; show_expression index; "]" ]
  | LVALUE_Field { expr; field } ->
      String.concat "" [ show_expression expr; "."; string_of_identifier field ]

let rec showxs_statement stmt =
  match stmt.data with
  | STMT_Call { callee; arguments } -> [ show_call callee arguments ]
  | STMT_VarDecl { var; init = None } -> [ show_var_declaration var ]
  | STMT_VarDecl { var; init = Some v } ->
      [ String.concat " " [ show_var_declaration var; "="; show_expression v ] ]
  | STMT_ArrayDecl { id; tp; sizes; _ } ->
      let show_size n = String.concat "" [ "["; show_expression n; "]" ] in
      [
        String.concat ""
          [
            string_of_identifier id;
            show_type_expression tp;
            String.concat "" (List.map show_size sizes);
          ];
      ]
  | STMT_Return None -> [ "return;" ]
  | STMT_Return (Some v) ->
      [ String.concat " " [ "return"; show_expression v ] ]
  | STMT_Block block ->
      List.concat
        [
          [ "{" ];
          indentxs @@ List.concat @@ List.map showxs_statement block;
          [ "}" ];
        ]
  | STMT_While { cond; body; _ } ->
      List.concat
        [
          [ String.concat " " [ "while"; "("; show_expression cond; ")" ] ];
          showxs_statement_as_block body;
        ]
  | STMT_If { cond; then_branch; else_branch = None; _ } ->
      List.concat
        [
          [ String.concat " " [ "if"; "("; show_expression cond; ")" ] ];
          showxs_statement_as_block then_branch;
        ]
  | STMT_If { cond; then_branch; else_branch = Some else_branch; _ } ->
      List.concat
        [
          [ String.concat " " [ "if"; "("; show_expression cond; ")" ] ];
          showxs_statement_as_block then_branch;
          [ "else" ];
          showxs_statement_as_block else_branch;
        ]
  | STMT_Assign { lhs; rhs; _ } ->
      [ String.concat " " [ show_lvalue lhs; "="; show_expression rhs ] ]

and showxs_statement_as_block stmt =
  showxs_statement { stmt with data = STMT_Block [ stmt ] }

let show_formal_parameters params =
  String.concat ", " @@ List.map show_var_declaration params

let show_return_type = function
  | None -> ""
  | Some tp -> ": " ^ show_type_expression tp

let showxs_global_definition def =
  match def.data with
  | GDEF_Use id -> [ String.concat " " [ "use"; string_of_identifier id ] ]
  | GDEF_Type { id; body; _ } ->
      [
        String.concat " "
          [ "type"; string_of_identifier id; "="; show_type_expression body ];
      ]
  | GDEF_Function { id; body; formal_parameters; return_type; _ } ->
      List.concat
        [
          [
            String.concat ""
              [
                string_of_identifier id;
                "(";
                show_formal_parameters formal_parameters;
                ")";
                show_return_type return_type;
              ];
          ];
          showxs_statement body;
        ]

let showxs_module_definition (ModuleDefinition { global_definitions; _ }) =
  let f x = showxs_global_definition x @ [ "" ] in
  List.flatten (List.map f global_definitions)

let show_module_definition m = String.concat "\n" @@ showxs_module_definition m
