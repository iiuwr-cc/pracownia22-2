open Zi_lib
open Iface

module MakeTypecheckerToolbox
    (LexerAndParser : LEXER_AND_PARSER)
    (ErrorReporter : Typechecker_errors.ERROR_REPORTER) : TYPECHECKER_TOOLBOX =
struct
  module Parser_wrapper = Parser_wrapper.Make (LexerAndParser)
  module ErrorReporter = ErrorReporter

  let zi_interface_extension = ".zii"
  let zi_lib_dir = "zisdk/lib"

  let parse_interface ~loc ifile =
    match Parser_wrapper.parse_interface ifile with
    | Ok intf -> intf
    | Error (loc, descr) ->
        ErrorReporter.report_other_error ~loc ~descr;
        ErrorReporter.fail ()

  let find_interface ~loc iname =
    let ifile = iname ^ zi_interface_extension in
    let (Ast.Location { file; _ }) = loc in
    let program_dir = Filename.dirname file in
    if Sys.file_exists (Filename.concat program_dir ifile) then
      parse_interface ~loc (Filename.concat program_dir ifile)
    else if Sys.file_exists (Filename.concat zi_lib_dir ifile) then
      parse_interface ~loc (Filename.concat zi_lib_dir ifile)
    else (
      ErrorReporter.report_other_error ~loc
        ~descr:(Printf.sprintf "Could not locate interface of %s module" iname);
      ErrorReporter.fail ())
end

module WrapTypechecker
    (LexerAndParser : LEXER_AND_PARSER)
    (MakeTypechecker : Zi_lib.Plugin.MAKE_TYPECHECKER) : TYPECHECKER_STEP =
struct
  let check_module mdef =
    let module ErrorReporter = Typechecker_errors.MakeErrorReporter () in
    let module Toolbox = MakeTypecheckerToolbox (LexerAndParser) (ErrorReporter)
    in
    let module Typechecker = MakeTypechecker (Toolbox) in
    ErrorReporter.wrap Typechecker.check_module mdef
end
