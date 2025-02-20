module MiniHaskell = Zoo.Main(struct

  let name = "MiniHaskell"

  type command = Syntax.toplevel_cmd

  type environment = Type_check.context * Interpret.environment

  let print_depth = ref 100

  let options = [("-p", Arg.Int (fun n -> print_depth := n), "set print depth")]

  let initial_environment = (Type_check.empty_ctx, [])

  let file_parser = Some (fun _ -> Parser.file Lexer.token)

  let toplevel_parser = Some (fun _ -> Parser.toplevel Lexer.token)

  let exec (ctx, env) = function
    | Syntax.Expr e ->
      (* type check [e], evaluate, and print result *)
       let ty = Type_check.type_of ctx e in
       let v = Interpret.interp env e in
       Zoo.print_info "- : %s = " (Syntax.string_of_type ty) ;
       Interpret.print_result !print_depth v ;
       Zoo.print_info "@." ;
       (ctx, env)
    | Syntax.Def (x, e) ->
       (* type check [e], and store it unevaluated! *)
       let ty = Type_check.type_of ctx e in
       Zoo.print_info "val %s : %s@." x (Syntax.string_of_type ty) ;
       (Type_check.extend_var x ty ctx, (x, ref (Interpret.VClosure (env,e)))::env)
    | Syntax.DataDef (name, constructors) ->
      Zoo.print_info "type %s is defined@." name ;
      (Type_check.extend_datadef name constructors ctx, env)
    | Syntax.Quit -> raise End_of_file

end) ;;

MiniHaskell.main () ;;
