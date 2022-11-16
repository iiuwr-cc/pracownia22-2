(*
 * Menhir wygeneruje funkcje o nazwach source_file oraz interface_file 
 *)
%start <Zi_lib.Ast.module_definition> source_file
%start <Zi_lib.Ast.module_interface> interface_file

%{
open Zi_lib
open Ast
open Parser_utils

(* Generator znaczników *)
let mk_node loc data =
  { loc  = mkLocation loc
  ; tag  = fresh_node_tag ()
  ; data = data
  }

  (* vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv 
   * Miejsce na twój kod w Ocamlu
   *)

  (* ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
   ----------------------------------------------------------------------------- *)

%}

(* vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv 
 * Miejsce na dyrektywy
 *)

%token EOF
%token <string>IDENTIFIER

(* ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
   ----------------------------------------------------------------------------- *)

%%

(* vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv 
 * Miejsce na gramatykę
 *)


(* Obecnie potrafimy sparsować tylko pusty plik (wymagamy od razu tokena EOF) *)
source_file:
    |  EOF
    { ModuleDefinition {global_definitions=[]} }

(* Oraz pusty interfejs *)
interface_file:
    | EOF
    { ModuleInterface {global_declarations=[]} }

identifier:
    | IDENTIFIER
    { Identifier $1 }

(* 
   ** przykład użycia mk_node

    atomic_expression:
        | identifier
        { mk_node $loc (EXPR_Id $1) }
*)

(* ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
   ----------------------------------------------------------------------------- *)
