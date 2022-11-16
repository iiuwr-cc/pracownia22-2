open Zi_lib

module CommandLine = struct
  open Cmdliner

  let compile zi_log extra_debug mod_uwr plugin reg_descr stop_after output
      source =
    Logger.init zi_log;
    Logger.set_extra_debug extra_debug;
    Plugin_manager.load_plugin mod_uwr;
    let reg_descr =
      match List.assoc_opt reg_descr Ir_arch.descriptions with
      | Some reg_descr -> reg_descr
      | None -> failwith "Unknown registers description"
    in
    (match plugin with
    | Some path -> Plugin_manager.load_plugin path
    | None -> ());
    let module Steps = (val Plugin_manager.resolve_compiler_steps reg_descr) in
    let module Params = struct
      let output = output
      let stop_point = match stop_after with Some s -> s | None -> ""
    end in
    let module Pipeline = Pipeline.Make (Steps) (Params) in
    match Pipeline.compile source with
    | Ok () ->
        Format.print_string "Success";
        0
    | Error xs ->
        Format.eprintf "Failed: %s\n%!" xs;
        1

  let stop_after =
    let doc = "Stops compiler after given phase" in
    Arg.(value & opt (some string) None & info [ "stop-after" ] ~doc)

  let mod_uwr =
    let doc = "Base module" in
    Arg.(value & opt string "zisdk/mod_uwr.cma" & info [ "mod-uwr" ] ~doc)

  let reg_descr =
    let doc =
      "EXPERIMENTAL: Registers description (see Ir_arch.descriptions)"
    in
    Arg.(value & opt string "normal" & info [ "registers-description" ] ~doc)

  let plugin =
    let doc = "Plugin module" in
    Arg.(value & opt (some string) None & info [ "plugin" ] ~doc)

  let output =
    let doc = "Output file" in
    Arg.(value & opt string "main.s" & info [ "o"; "output" ] ~doc)

  let zi_log =
    let doc = "Log directory" in
    Arg.(value & opt string "zilog" & info [ "zi-log" ] ~doc)

  let _ =
    let doc = "Runtime" in
    Arg.(value & opt file "zisdk/runtime.s" & info [ "runtime" ] ~doc)

  let extra_debug =
    let doc = "Enables extra debug" in
    Arg.(value & flag & info [ "extra-debug" ] ~doc)

  let source_file =
    let doc = "Zi Source File" in
    Arg.(required & pos 0 (some file) None & info [] ~doc)

  let cmd =
    let doc = "Compile Źi Program" in
    let version = "pracownia22-2-0-g6f56689" in
    let info = Cmd.info "zi" ~doc ~version in
    Cmd.v info
      Term.(
        const compile $ zi_log $ extra_debug $ mod_uwr $ plugin $ reg_descr
        $ stop_after $ output $ source_file)

  let main () = exit (Cmd.eval' cmd)
  let () = main ()
end
