open Zi_lib
open Ast
open Types

(* Pomocnicza funkcja sprawdzająca czy lista zawiera
 * obiekty o unikalnych nazwach
 *)
let check_uniqueness xs ~name_of ~loc_of ~report_error =
  let loc_map = Hashtbl.create 32 in
  let rec loop xs =
    match xs with
    | [] -> ()
    | x :: xs -> (
        match name_of x with
        | None -> ()
        | Some name -> (
            match Hashtbl.find_opt loc_map name with
            | None ->
                Hashtbl.add loc_map name (loc_of x);
                loop xs
            | Some prev_loc -> report_error x prev_loc))
  in
  loop xs

module Make (Toolbox : Iface.TYPECHECKER_TOOLBOX) = struct
  (* Moduł pozwalający na zgłaszanie błędów, a także przerwanie sprawdzania
   * typów (w przypadku gdy błąd nie pozwala na dalszą pracę) za pomocą
   * funkcji `ErrorReporter.fail`
   *)
  module ErrorReporter = Toolbox.ErrorReporter

  (* Logger *)
  let logf fmt = Logger.make_logf __MODULE__ fmt

  (* Moduł odpowiedzialny za sprawdzanie poprawności wyrażeń typowych
   * i tłumaczenie ich do formatu używanego przez typechecker
   *)
  module TypeExprChecker = struct
    let rec check_type_expression top_env (tp : type_expression) : normal_type =
      match tp.data with
      | TEXPR_Id x ->
          (* Sprawdź czy jest to istniejąca nazwa typu *)
          failwith "Not implemented";
          TP_Id x
      | TEXPR_Int -> TP_Int
      | TEXPR_Bool -> TP_Bool
      | TEXPR_Array tp -> failwith "Not implemented"
      | TEXPR_Record flds -> failwith "Not implemented"

    let check_formal_parameters top_env =
      List.map (fun { data = VarDecl { tp; _ }; _ } ->
          check_type_expression top_env tp)

    let check_return_type top_env = function
      | None -> None
      | Some tp -> Some (check_type_expression top_env tp)
  end

  module TopEnv = struct
    type t = global_symbols

    let empty = IdMap.empty

    let declare_type top_env ~loc id =
      (* Dodaj deklarację typu do znanych symboli,
       * pamiętaj o poprawnym obsłużeniu przesłaniania nazw
       *)
      failwith "Not implemented"

    let define_type top_env ~loc id body =
      (* Dodaj definicję typu do znanych symboli, pamiętaj aby sprawdzić
       * potencjalne konflikty z istniejącą już definicją lub deklaracją
       *)
      failwith "Not implemented"

    let declare_function top_env ~loc id param_types return_type =
      (* Dodaj deklarację funkcji do znanych symboli, pamiętaj aby sprawdzić
       * potencjalne konflikty z istniejącą już deklaracją
       *)
      failwith "Not implemented"

    let use_interface top_env intf =
      let use_interface_entity id sym top_env =
        match sym with
        | ST_AbstractType { loc } -> declare_type ~loc top_env id
        | ST_TypeDef { loc; body } -> define_type ~loc top_env id body
        | ST_Function { loc; param_types; return_type } ->
            declare_function ~loc top_env id param_types return_type
      in
      IdMap.fold use_interface_entity intf top_env
  end

  module InterfaceChecker = struct
    let collect_type_names top_env (ModuleInterface { global_declarations }) =
      let scan top_env decl =
        match decl.data with
        | GDECL_Type { id; _ } | GDECL_TypeDecl id ->
            TopEnv.declare_type ~loc:decl.loc top_env id
        | GDECL_Function _ -> top_env
      in
      List.fold_left scan top_env global_declarations

    let collect_function_types_and_type_definitions top_env
        (ModuleInterface { global_declarations }) =
      let scan top_env decl =
        match decl.data with
        | GDECL_Type { id; body } ->
            (* Sprawdź poprawność i dodaj definicję typu do top_env *)
            failwith "Not implemented"
        | GDECL_TypeDecl _ -> top_env
        | GDECL_Function { id; formal_parameters; return_type } ->
            (* Sprawdź poprawność i dodaj deklarację funkcji do top_env *)
            failwith "Not implemented"
      in
      List.fold_left scan top_env global_declarations

    let check_interface idef =
      let top_env = TopEnv.empty in
      let top_env = collect_type_names top_env idef in
      let top_env = collect_function_types_and_type_definitions top_env idef in
      top_env
  end

  (* Hashtablica którą zwracamy jak wszystko jest OK.
   * Mapuje znacznik węzła na przypisany typ *)
  let node2type_map = Hashtbl.create 513

  (* Tablica pamiętająca typy funkcji. (dla każdego tagu definicji)
   * Zapamiętujemy typy funkcji, by nie tłumaczyć ich na wewnętrzną
   * reprezentację dwa razy. Ma do duże znaczenie dla raportowania błędów --
   * jeśli jakieś wyrażenie typowe jest niepoprawne, to nie chcemy dwa razy
   * oglądać błędu *)
  let function_types = Hashtbl.create 42

  (* Środowisko *)
  module Env = struct
    type t = {
      return_type : normal_type option;
      top_env : TopEnv.t;
      local_variables : normal_type IdMap.t;
    }

    let create top_env return_type =
      { return_type; top_env; local_variables = IdMap.empty }

    let extend ~loc env id tp =
      match IdMap.find_opt id env.local_variables with
      | None ->
          { env with local_variables = IdMap.add id tp env.local_variables }
      | _ ->
          (* Zgłaszamy błąd ale nie przerywamy działania *)
          ErrorReporter.report_shadows_previous_definition ~loc ~id;
          env

    let lookup_local env id = IdMap.find_opt id env.local_variables
    let lookup_global env id = IdMap.find_opt id env.top_env
    let top_env env = env.top_env
    let return_type env = env.return_type
  end

  (* 
   * Procedury inferencji i sprawdzania. Dla implementacyjnej wygody dwie
   * główna funkcja funkcja inferencji typu jest wraperem co wpisuje
   * wynik udanej inferencji do hashtablicy node2type_map.
   *)
  let rec infer_expression env e =
    match _infer_expression env e with
    | Some tp ->
        Hashtbl.replace node2type_map e.tag tp;
        logf "%s: inferred type %s" (string_of_location e.loc)
          (string_of_normal_type tp);
        Some tp
    | None ->
        logf "%s: failed" (string_of_location e.loc);
        None

  (* Rzeczywista funkcja inferencji. Implementacja mniej więcej jak w
   * specyfikacji. Chcemy aby
   *
   * infer_expression G e = Some T
   *    oznaczało, że zachodzi
   * G |- e : T 
   *)
  and _infer_expression env e =
    match e.data with
    | EXPR_EmptyStruct ->
        ErrorReporter.report_cannot_infer ~loc:e.loc;
        None
    | EXPR_Id id -> failwith "Not implemented"
    | EXPR_Int _ | EXPR_Char _ -> Some TP_Int
    (* Literały łańcuchowe to tablice intów *)
    | EXPR_String _ -> Some (TP_Array TP_Int)
    | EXPR_Bool _ -> Some TP_Bool
    (* Wyinferuj argument i zwróć info że wyrażenie ma typ int *)
    | EXPR_Length arg -> failwith "Not implemented"
    (* Relacje porządku się prosto sprawdza, wymagamy po prostu aby
     * podwyrażenia były typu int, bo tylko na nim mamy porządek. *)
    | EXPR_Relation { lhs; rhs; op = RELOP_Ge }
    | EXPR_Relation { lhs; rhs; op = RELOP_Gt }
    | EXPR_Relation { lhs; rhs; op = RELOP_Lt }
    | EXPR_Relation { lhs; rhs; op = RELOP_Le } ->
        failwith "Not implemented"
    (* Równość jest bardziej subtelna. Na każdym typie mamy równosć.
     * Inferujemy lewą stronę i sprawdzamy prawą kontra wynik.
     * Gdy się nie uda to dla wygody użytkownika inferujemy typ prawej strony
     * tylko po to aby być-może zgłosić jakieś błędy tam.
     *)
    | EXPR_Relation { lhs; rhs; op = RELOP_Eq }
    | EXPR_Relation { lhs; rhs; op = RELOP_Ne } ->
        failwith "Not implemented"
    (* Dodawnaie jest podobne *)
    | EXPR_Binop { lhs; rhs; op = BINOP_Add } -> failwith "Not implemented"
    (* Operatory logiczne śmigają tylko z boolami *)
    | EXPR_Binop { lhs; rhs; op = BINOP_And; _ }
    | EXPR_Binop { lhs; rhs; op = BINOP_Or; _ } ->
        failwith "Not implemented"
    (* ...a arytmetyczne tylko z intami *)
    | EXPR_Binop { lhs; rhs; op = BINOP_Sub; _ }
    | EXPR_Binop { lhs; rhs; op = BINOP_Rem; _ }
    | EXPR_Binop { lhs; rhs; op = BINOP_Mult; _ }
    | EXPR_Binop { lhs; rhs; op = BINOP_Div; _ } ->
        failwith "Not implemented"
    (* Negacja tylko z intem *)
    | EXPR_Unop { op = UNOP_Neg; expr; _ } -> failwith "Not implemented"
    (* Negacja logiczna tylko z boolem *)
    | EXPR_Unop { op = UNOP_Not; expr; _ } -> failwith "Not implemented"
    (* Sprawdzenie wywołania *)
    | EXPR_Call { callee; arguments } -> failwith "Not implemented"
    (* inferencja expr[index] oznacza inferencje `expr` i sprawdzenie że
     * wynik jest postaci A[] gdzie A to jakiś typ. Index sprawdzamy
     * kontra typ `int` *)
    | EXPR_Index { expr; index } -> failwith "Not implemented"
    | EXPR_Field { expr; field } -> failwith "Not implemented"
    | EXPR_Unfold expr -> failwith "Not implemented"
    (* Pusta tablica lub rekord, nie powinno się nigdy zdarzyć *)
    | EXPR_Array [] | EXPR_Record [] -> assert false
    (* Inferujemy typ pierwszego elementu i sprawdzamy resztę
     * kontra uzyskany wynik. Infer na {...} będzie tylko działał w przypadku
     * `length` i jest mało istotny.
     *)
    | EXPR_Array (x :: xs) -> failwith "Not implemented"
    | EXPR_Record flds -> failwith "Not implemented"

  (* Sprawdź wyrażenie kontra oczekiwany typ. Ta procedura jest używana
   * w większości przypadku bo niemalże wszędzie mamy jakieś oczekiwanie.
   *
   * Jej rola to obsłużenie specjalnych przypadków gdzie potrafimy z
   * oczekiwania coś wyłuskać i pchać w dół nowe oczekiwanie. 
   * Gdy nie mamy specjalnego przypadku to jest to zwykły fallback do
   * procedury inferencji.
   *)
  and check_expression env e expected =
    Hashtbl.replace node2type_map e.tag expected;
    match (e.data, expected) with
    | EXPR_EmptyStruct, (TP_Array _ | TP_Record []) -> ()
    | EXPR_EmptyStruct, _ ->
        ErrorReporter.report_type_mismatch ~loc:e.loc ~actual:(TP_Record [])
          ~expected
    (* Jeżeli oczekujemy dodawania tablic to sprawdzamy podwyrażenia
     * pchając w dół info że mają być oczekiwanego typu. Gdy chcemy
     * dodać inty to fallback do inferencji sobie poradzi. *)
    | EXPR_Binop { op = BINOP_Add; lhs; rhs }, _ -> failwith "Not implemented"
    | EXPR_Index { index; expr }, _ -> failwith "Not implemented"
    | EXPR_Array elements, TP_Array tp -> failwith "Not implemented"
    | EXPR_Record fields, TP_Record ftypes -> failwith "Not implemented"
    (* Fallback *)
    | ( ( EXPR_Id _ | EXPR_Int _ | EXPR_Char _ | EXPR_String _ | EXPR_Bool _
        | EXPR_Length _ | EXPR_Relation _ | EXPR_Binop _ | EXPR_Unop _
        | EXPR_Call _ | EXPR_Field _ | EXPR_Unfold _ | EXPR_Array _
        | EXPR_Record _ ),
        _ ) -> (
        match infer_expression env e with
        | Some actual when actual = expected -> ()
        | None -> ()
        | Some actual ->
            ErrorReporter.report_type_mismatch ~loc:e.loc ~actual ~expected)

  let check_lvalue env lv =
    match lv.data with
    | LVALUE_Id id -> failwith "Not implemented"
    | LVALUE_Index { expr; index } -> failwith "Not implemented"
    | LVALUE_Field { expr; field } -> failwith "Not implemented"

  (* Sprawdź statementy, dostajemy środowisko i zwracamy środowisko
   * z nowo zdefiniowanymi zmiennymi
   *)
  let rec check_statement env stmt =
    match stmt.data with
    (* Wyinferuj typ `lhs` i sprawdź `rhs` kontra wynik *)
    | STMT_Assign { lhs; rhs; _ } -> failwith "Not implemented"
    | STMT_Call { callee; arguments } -> failwith "Not implemented"
    | STMT_VarDecl { var = { data = VarDecl { id; tp }; loc; _ }; init } ->
        let tp = TypeExprChecker.check_type_expression (Env.top_env env) tp in
        let env = Env.extend ~loc env id tp in
        (match init with None -> () | Some e -> check_expression env e tp);
        env
    | STMT_ArrayDecl { id; tp; sizes } -> failwith "Not implemented"
    | STMT_If { cond; then_branch; else_branch } -> failwith "Not implemented"
    | STMT_While { cond; body } ->
        check_expression env cond TP_Bool;
        let (_ : Env.t) = check_statement env body in
        env
    | STMT_Return rv -> failwith "Not implemented"
    | STMT_Block block ->
        let (_ : Env.t) = List.fold_left check_statement env block in
        env

  (* syntaktyczne sprawdzenie, czy komenda zawsze wraca *)
  let rec always_returns stmt =
    match stmt.data with
    | STMT_Assign _ | STMT_Call _ | STMT_VarDecl _ | STMT_ArrayDecl _
    | STMT_While _
    | STMT_If { else_branch = None; _ } ->
        false
    | STMT_Return _ -> true
    | STMT_If { then_branch; else_branch = Some else_branch; _ } ->
        always_returns then_branch && always_returns else_branch
    | STMT_Block stmts -> List.exists always_returns stmts

  let check_return_paths ~loc ~id body return_type =
    match return_type with
    | None -> () (* Jest domyślny powrót na końcu funkcji *)
    | Some _ ->
        if not (always_returns body) then
          ErrorReporter.report_not_all_control_paths_return_value ~loc ~id

  let check_formal_parameters =
    List.fold_left2 (fun env { data = VarDecl { id; _ }; loc; _ } tp ->
        Env.extend ~loc env id tp)

  let collect_type_names_and_interfaces top_env
      (ModuleDefinition { global_definitions }) =
    let scan top_env def =
      match def.data with
      | GDEF_Function _ ->
          (* To będziemy robić w późniejszych etapach *)
          top_env
      | GDEF_Use (Identifier name) ->
          let iface = Toolbox.find_interface ~loc:def.loc name in
          let iface_env = InterfaceChecker.check_interface iface in
          TopEnv.use_interface top_env iface_env
      | GDEF_Type { id; _ } -> TopEnv.declare_type top_env ~loc:def.loc id
    in
    List.fold_left scan top_env global_definitions

  (* Znajdź i sprawdź wszystkie definicje typów oraz typy funkcji *)
  let collect_function_types_and_type_definitions top_env
      (ModuleDefinition { global_definitions }) =
    let scan top_env def =
      match def.data with
      | GDEF_Use _ ->
          (* Ten przypadek obsłużyliśmy w poprzednim etapie *)
          top_env
      | GDEF_Type { id; body } ->
          let tp = TypeExprChecker.check_type_expression top_env body in
          TopEnv.define_type top_env ~loc:def.loc id tp
      | GDEF_Function { id; formal_parameters; return_type; _ } ->
          let ftp =
            TypeExprChecker.check_formal_parameters top_env formal_parameters
          in
          let rtp = TypeExprChecker.check_return_type top_env return_type in
          Hashtbl.add function_types def.tag (ftp, rtp);
          TopEnv.declare_function top_env ~loc:def.loc id ftp rtp
    in
    List.fold_left scan top_env global_definitions

  (* Sprawdź ciało funkcji *)
  let check_global_definition top_env def =
    match def.data with
    | GDEF_Use _ | GDEF_Type _ ->
        (* Te przypadki były już obsłużone w poprzednich etapach *)
        ()
    | GDEF_Function { id; formal_parameters; body; _ } ->
        let ftp, rtp = Hashtbl.find function_types def.tag in
        let env = Env.create top_env rtp in
        let env = check_formal_parameters env formal_parameters ftp in
        let (_ : Env.t) = check_statement env body in
        check_return_paths ~loc:def.loc ~id body rtp

  let check_global_definitions top_env (ModuleDefinition { global_definitions })
      =
    List.iter (check_global_definition top_env) global_definitions

  let check_function_uniqueness (ModuleDefinition { global_definitions }) =
    let name_of def =
      match def.data with GDEF_Function { id; _ } -> Some id | _ -> None
    in
    let report_error def prev_loc =
      match def.data with
      | GDEF_Function { id; _ } ->
          ErrorReporter.report_other_error ~loc:def.loc
            ~descr:"This function is defined more than once"
      | _ -> assert false
    in
    check_uniqueness global_definitions ~name_of
      ~loc_of:(fun def -> def.loc)
      ~report_error

  (* Kolejność deklaracji nie ma znaczenia, a zarówno funkcje jak i typy
   * mogą być wzajemnie rekurencyjnie. Więc sprawdzamy w trzech etapach.
   * 1. zbieramy nazwy typów oraz definicje z interfejów
   * 2. zbieramy definicje typów i sygnatury funkcji
   * 3. sprawdzamy typy wewnątrz funkcji
   *)
  let check_module mdef =
    check_function_uniqueness mdef;
    let top_env = TopEnv.empty in
    let top_env = collect_type_names_and_interfaces top_env mdef in
    let top_env = collect_function_types_and_type_definitions top_env mdef in
    check_global_definitions top_env mdef;
    (node2type_map, top_env)
end
