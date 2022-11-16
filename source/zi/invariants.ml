open Zi_lib
open Ast
open Types

module AllExpressionsAreTypecheck = struct
  exception MissingTypeInformation of location

  module Implementation (M : sig
    val node2type : (node_tag, normal_type) Hashtbl.t
  end) =
  struct
    open M

    let check_tag loc tag =
      match Hashtbl.find_opt node2type tag with
      | Some _ -> ()
      | None -> raise (MissingTypeInformation loc)

    let expr_subexpressions e =
      match e.data with
      | EXPR_Id _ -> []
      | EXPR_Int _ -> []
      | EXPR_Char _ -> []
      | EXPR_String _ -> []
      | EXPR_Bool _ -> []
      | EXPR_Relation { lhs; rhs; _ } -> [ lhs; rhs ]
      | EXPR_Binop { lhs; rhs; _ } -> [ lhs; rhs ]
      | EXPR_Length arg -> [ arg ]
      | EXPR_Unop { expr; _ } -> [ expr ]
      | EXPR_Call { arguments; _ } -> arguments
      | EXPR_Index { expr; index; _ } -> [ expr; index ]
      | EXPR_Field { expr; _ } -> [ expr ]
      | EXPR_Unfold expr -> [ expr ]
      | EXPR_Array elements -> elements
      | EXPR_Record fields -> List.map Ast.field_subexpr fields
      | EXPR_EmptyStruct -> []

    let some2list = function Some x -> [ x ] | None -> []

    let stmt_subexpressions stmt =
      match stmt.data with
      | STMT_Call { arguments; _ } -> arguments
      | STMT_Assign { rhs; _ } -> [ rhs ]
      | STMT_VarDecl { init = Some init; _ } -> [ init ]
      | STMT_VarDecl { init = None; _ } -> []
      | STMT_ArrayDecl { sizes; _ } -> sizes
      | STMT_If { cond; _ } -> [ cond ]
      | STMT_While { cond; _ } -> [ cond ]
      | STMT_Return None -> []
      | STMT_Return (Some value) -> [ value ]
      | STMT_Block _ -> []

    let stmt_substatements stmt =
      match stmt.data with
      | STMT_Call _ -> []
      | STMT_Assign _ -> []
      | STMT_VarDecl _ -> []
      | STMT_ArrayDecl _ -> []
      | STMT_If { then_branch; else_branch; _ } ->
          [ then_branch ] @ some2list else_branch
      | STMT_While { body; _ } -> [ body ]
      | STMT_Return _ -> []
      | STMT_Block block -> block

    let rec verify_expression e =
      check_tag e.loc e.tag;
      let sube = expr_subexpressions e in
      List.iter verify_expression sube

    let rec verify_statement s =
      let exprs = stmt_subexpressions s in
      let stmts = stmt_substatements s in
      List.iter verify_expression exprs;
      List.iter verify_statement stmts

    let verify_global_definition def =
      match def.data with
      | GDEF_Use _ | GDEF_Type _ -> ()
      | GDEF_Function { body; _ } -> verify_statement body

    let verify_module_definition (ModuleDefinition { global_definitions }) =
      List.iter verify_global_definition global_definitions
  end

  let verify_module_definition node2tag mdef =
    try
      let module Instance = Implementation (struct
        let node2type = node2tag
      end) in
      Instance.verify_module_definition mdef;
      true
    with MissingTypeInformation e ->
      Format.eprintf "Missing type information for expression %s\n%!"
        (string_of_location e);
      false
end
