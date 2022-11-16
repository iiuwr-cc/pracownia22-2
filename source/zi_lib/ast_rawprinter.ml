open Ast

let string_of_binop = function
  | BINOP_And -> "BINOP_And"
  | BINOP_Or -> "BINOP_Or"
  | BINOP_Add -> "BINOP_Add"
  | BINOP_Sub -> "BINOP_Sub"
  | BINOP_Mult -> "BINOP_Mult"
  | BINOP_Div -> "BINOP_Div"
  | BINOP_Rem -> "BINOP_Rem"

let string_of_relop = function
  | RELOP_Eq -> "RELOP_Eq"
  | RELOP_Ne -> "RELOP_Ne"
  | RELOP_Lt -> "RELOP_Lt"
  | RELOP_Gt -> "RELOP_Gt"
  | RELOP_Le -> "RELOP_Le"
  | RELOP_Ge -> "RELOP_Ge"

let string_of_unop = function UNOP_Not -> "UNOP_Not" | UNOP_Neg -> "UNOP_Neg"
let indent x = "  " ^ x

let indentfmt fmt =
  let cont = Format.sprintf "   %s" in
  Format.ksprintf cont fmt

let indentxs = List.map indent

type p =
  | P_String of string
  | P_Sequence of p list
  | P_List of p list
  | P_Dict of string * (string * p) list

type r =
  | R_String of string
  | R_Indent of r
  | R_Break
  | R_Tab
  | R_Group of r list

let render_r = function
  | R_String s -> s
  | R_Tab -> "   "
  | R_Break -> "\n"
  | R_Group _ -> failwith "R_Group should be eliminated"
  | R_Indent _ -> failwith "R_Indent should be eliminated"

let rec insert_tabs tabs = function
  | R_Indent r -> insert_tabs (R_Tab :: tabs) r
  | R_Break -> R_Group [ R_Break; R_Group tabs ]
  | R_Group rs -> R_Group (List.map (insert_tabs tabs) rs)
  | r -> r

let rec flatten = function
  | R_Indent _ -> failwith "R_Indent should be eliminated"
  | R_Group xs -> Seq.flat_map flatten (List.to_seq xs)
  | r -> Seq.cons r Seq.empty

let render_r r =
  let b = Buffer.create 1000 in
  Seq.iter (fun r -> Buffer.add_string b (render_r r))
  @@ flatten @@ insert_tabs [] r;
  Buffer.contents b

let rec render_p = function
  | P_String s -> R_String s
  | P_List xs ->
      let rec f acc = function
        | [] -> R_Group (List.rev acc)
        | x :: xs ->
            let entry = R_Group [ render_p x; R_String ";"; R_Break ] in
            f (entry :: acc) xs
      in
      R_Group
        [ R_String "["; R_Indent (R_Group [ R_Break; f [] xs ]); R_String "]" ]
  | P_Dict (kind, items) ->
      let rec f acc = function
        | [] -> R_Group (List.rev acc)
        | (k, v) :: xs ->
            let entry =
              R_Group
                [
                  R_String k;
                  R_String " = ";
                  R_Indent (render_p v);
                  R_String ";";
                  R_Break;
                ]
            in
            f (entry :: acc) xs
      in
      R_Group
        [
          R_String kind;
          R_String " ";
          R_String "{";
          R_Indent (R_Group [ R_Break; f [] items ]);
          R_String "}";
        ]
  | P_Sequence xs -> R_Group (List.map render_p xs)

let p_dict k items = P_Dict (k, items)

let p_identifier id =
  P_String (Format.sprintf "\"%s\"" @@ string_of_identifier id)

let p_string id = P_String (Format.sprintf "\"%s\"" @@ String.escaped id)
let p_location loc = P_String (string_of_location loc)
let p_node_tag tag = P_String (string_of_node_tag tag)
let p_i32 i = P_String (Int32.to_string i)
let p_char c = P_String (Format.sprintf "'%s'" (Char.escaped c))
let p_bool b = P_String (string_of_bool b)

let p_node node p_data =
  p_dict "node"
    [
      ("loc", p_location node.loc);
      ("tag", p_node_tag node.tag);
      ("data", p_data node.data);
    ]

let p_opt f = function
  | None -> P_String "None"
  | Some x -> P_Sequence [ P_String "Some "; f x ]

let rec p_expression e =
  p_node e (function
    | EXPR_Id id -> p_dict "EXPR_Id" [ ("id", p_identifier id) ]
    | EXPR_Int value -> p_dict "EXPR_Int" [ ("value", p_i32 value) ]
    | EXPR_Char value -> p_dict "EXPR_Char" [ ("value", p_char value) ]
    | EXPR_String value -> p_dict "EXPR_String" [ ("value", p_string value) ]
    | EXPR_Bool value -> p_dict "EXPR_Bool" [ ("value", p_bool value) ]
    | EXPR_Relation { op; lhs; rhs } ->
        p_dict "EXPR_Relation"
          [
            ("op", P_String (string_of_relop op));
            ("lhs", p_expression lhs);
            ("rhs", p_expression rhs);
          ]
    | EXPR_Binop { op; lhs; rhs } ->
        p_dict "EXPR_Binop"
          [
            ("op", P_String (string_of_binop op));
            ("lhs", p_expression lhs);
            ("rhs", p_expression rhs);
          ]
    | EXPR_Unop { op; expr } ->
        p_dict "EXPR_Unop"
          [ ("op", P_String (string_of_unop op)); ("expr", p_expression expr) ]
    | EXPR_Length arg -> p_dict "EXPR_Length" [ ("arg", p_expression arg) ]
    | EXPR_Index { expr; index } ->
        p_dict "EXPR_Index"
          [ ("expr", p_expression expr); ("index", p_expression index) ]
    | EXPR_Field { expr; field } ->
        p_dict "EXPR_Field"
          [ ("expr", p_expression expr); ("field", p_identifier field) ]
    | EXPR_Unfold expr -> p_dict "EXPR_Unfold" [ ("expr", p_expression expr) ]
    | EXPR_Array elements ->
        p_dict "EXPR_Array"
          [ ("elements", P_List (List.map p_expression elements)) ]
    | EXPR_Record fields ->
        p_dict "EXPR_Record"
          [ ("fields", P_List (List.map p_field_expression fields)) ]
    | EXPR_EmptyStruct -> p_dict "EXPR_EmptyStruct" []
    | EXPR_Call { callee; arguments } ->
        p_dict "EXPR_Call"
          [
            ("callee", p_identifier callee);
            ("arguments", P_List (List.map p_expression arguments));
          ])

and p_field_expression fld =
  p_node fld (function FieldExpr { name; value } ->
      p_dict "FieldExpr"
        [ ("name", p_identifier name); ("value", p_expression value) ])

let rec p_type_expression tp =
  p_node tp (function
    | TEXPR_Id id -> p_dict "TEXPR_Id" [ ("id", p_identifier id) ]
    | TEXPR_Int -> p_dict "TEXPR_Int" []
    | TEXPR_Bool -> p_dict "TEXPR_Bool" []
    | TEXPR_Array sub -> p_dict "TEXPR_Array" [ ("sub", p_type_expression sub) ]
    | TEXPR_Record fields ->
        p_dict "TPEXPR_Record"
          [ ("fields", P_List (List.map p_field_type fields)) ])

and p_field_type fld =
  p_node fld (function FieldType { name; tp } ->
      p_dict "FieldType"
        [ ("name", p_identifier name); ("tp", p_type_expression tp) ])

let p_lvalue lv =
  p_node lv (function
    | LVALUE_Id id -> p_dict "LVALUE_Id" [ ("id", p_identifier id) ]
    | LVALUE_Index { expr; index } ->
        p_dict "LVALUE_Index"
          [ ("expr", p_expression expr); ("index", p_expression index) ]
    | LVALUE_Field { expr; field } ->
        p_dict "LVALUE_Field"
          [ ("expr", p_expression expr); ("field", p_identifier field) ])

let p_var_declaration vd =
  p_node vd (function VarDecl { id; tp } ->
      p_dict "VarDecl" [ ("id", p_identifier id); ("tp", p_type_expression tp) ])

let rec p_statement stmt =
  p_node stmt (function
    | STMT_Call { callee; arguments } ->
        p_dict "STMT_Call"
          [
            ("callee", p_identifier callee);
            ("arguments", P_List (List.map p_expression arguments));
          ]
    | STMT_Assign { lhs; rhs } ->
        p_dict "STMT_Assign"
          [ ("lhs", p_lvalue lhs); ("rhs", p_expression rhs) ]
    | STMT_VarDecl { var; init } ->
        p_dict "STMT_VarDecl"
          [ ("var", p_var_declaration var); ("init", p_opt p_expression init) ]
    | STMT_ArrayDecl { id; tp; sizes } ->
        p_dict "STMT_ArrayDecl"
          [
            ("id", p_identifier id);
            ("tp", p_type_expression tp);
            ("sizes", P_List (List.map p_expression sizes));
          ]
    | STMT_If { cond; then_branch; else_branch } ->
        p_dict "STMT_If"
          [
            ("cond", p_expression cond);
            ("then_branch", p_statement then_branch);
            ("else_branch", p_opt p_statement else_branch);
          ]
    | STMT_While { cond; body } ->
        p_dict "STMT_While"
          [ ("cond", p_expression cond); ("body", p_statement body) ]
    | STMT_Block block ->
        p_dict "STMT_Block"
          [ ("statements", P_List (List.map p_statement block)) ]
    | STMT_Return value ->
        p_dict "STMT_Return" [ ("value", p_opt p_expression value) ])

let p_global_definition def =
  p_node def (function
    | GDEF_Use id -> p_dict "GDEF_Use" [ ("id", p_identifier id) ]
    | GDEF_Type { id; body } ->
        p_dict "GDEF_Type"
          [ ("id", p_identifier id); ("body", p_type_expression body) ]
    | GDEF_Function { id; formal_parameters; return_type; body } ->
        p_dict "GDEF_Function"
          [
            ("id", p_identifier id);
            ( "formal_parameters",
              P_List (List.map p_var_declaration formal_parameters) );
            ("return_type", p_opt p_type_expression return_type);
            ("body", p_statement body);
          ])

let p_module_definition = function
  | ModuleDefinition { global_definitions } ->
      P_Sequence
        [
          P_String "ModuleDefinition ";
          P_List (List.map p_global_definition global_definitions);
        ]

let show_module_definition mdef =
  let p = p_module_definition mdef in
  render_r @@ render_p p
