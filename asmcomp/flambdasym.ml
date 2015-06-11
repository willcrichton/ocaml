(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*                     Pierre Chambart, OCamlPro                       *)
(*                                                                     *)
(*  Copyright 2014 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

(*
Transform an expression to prepare conversion to clambda
- attributes symbols to structured constants
- replace access to constants from the current compilation unit by Fsymbol nodes,
  including access to fields from a constant closure inside the body of the function.
- Find used closure fields and remove unused ones.
- build value approximations for export

During symbol assignment, some alias can be created (when building let rec for instance).
They are replaced by their cannonical representent in the Prepare functor application.

Then the tables needed to build the Flambdaexport.exported type are build.
*)

open Misc
open Symbol
open Abstract_identifiers
open Flambda
open Flambdaexport
open Flambdautils

let all_closures expr =
  let closures = ref Set_of_closures_id.Set.empty in
  Flambdaiter.iter_on_closures
    (fun cl _ -> closures := Set_of_closures_id.Set.add cl.cl_fun.ident !closures) expr;
  !closures

let constant_closures constant_result expr =
  Set_of_closures_id.Set.diff
    (all_closures expr)
    (constant_result.Flambdaconstants.not_constant_closure)

let functions not_constants expr =
  let cf_map = ref Closure_id.Map.empty in
  let fun_id_map = ref Set_of_closures_id.Map.empty in
  let argument_kept = ref Set_of_closures_id.Map.empty in
  let aux ({ cl_fun } as cl) _ =
    let add var _ map =
      Closure_id.Map.add (Closure_id.wrap var) cl_fun map in
    cf_map := Variable.Map.fold add cl_fun.funs !cf_map;
    fun_id_map := Set_of_closures_id.Map.add cl.cl_fun.ident cl.cl_fun !fun_id_map;
    argument_kept :=
      Set_of_closures_id.Map.add cl.cl_fun.ident
          (Flambdautils.unchanging_params_in_recursion cl_fun) !argument_kept
  in
  Flambdaiter.iter_on_closures aux expr;
  !fun_id_map, !cf_map, !argument_kept

let list_used_variable_withing_closure expr =
  let used = ref Var_within_closure.Set.empty in
  let aux expr = match expr with
    | Fvar_within_closure({ vc_var },_) ->
        used := Var_within_closure.Set.add vc_var !used
    | e -> ()
  in
  Flambdaiter.iter aux expr;
  !used

module type Param1 = sig
  type t
  val expr : t Flambda.flambda
  val not_constants : Flambdaconstants.constant_result
  val constant_closures : Set_of_closures_id.Set.t
end

type const_sym =
  | Lbl of Symbol.t
  | No_lbl
  | Not_const
  | Const_closure

type infos =
  { global : (int, approx) Hashtbl.t;
    ex_table : descr EidMap.t ref;
    ex_symbol_id : ExportId.t SymbolMap.t ref;
    constants : unit flambda SymbolTbl.t;
    symbol_alias : Symbol.t SymbolTbl.t }

let init_infos () =
  { global = Hashtbl.create 10;
    ex_table = ref EidMap.empty;
    ex_symbol_id = ref SymbolMap.empty;
    constants = SymbolTbl.create 10;
    symbol_alias = SymbolTbl.create 10 }

let rec canonical_symbol s infos =
  try
    let s' = SymbolTbl.find infos.symbol_alias s in
    let s'' = canonical_symbol s' infos in
    if s' != s''
    then SymbolTbl.replace infos.symbol_alias s s'';
    s''
  with Not_found -> s

let new_descr descr infos =
  let id = ExportId.create (Compilenv.current_unit ()) in
  infos.ex_table := EidMap.add id descr !(infos.ex_table);
  id

module Conv(P:Param1) = struct
  open Flambdaexport

  let functions, closures, ex_kept_arguments = functions P.not_constants P.expr

  (* functions comming from a linked module *)
  let ex_closures () =
    (Compilenv.approx_env ()).Flambdaexport.ex_functions_off

  let ex_functions () =
    (Compilenv.approx_env ()).Flambdaexport.ex_functions

  let ex_constant_closures () =
    (Compilenv.approx_env ()).Flambdaexport.ex_constant_closures

  let used_variable_withing_closure = list_used_variable_withing_closure P.expr

  type ('a,'b) declaration_position =
    | Local of 'a
    | External of 'b
    | Not_declared

  let function_declaration_position cf =
    try Local (Closure_id.Map.find cf closures) with
    | Not_found ->
        try External (Closure_id.Map.find cf (ex_closures ())) with
        | Not_found ->
            Not_declared

  let functions_declaration_position fid =
    try Local (Set_of_closures_id.Map.find fid functions) with
    | Not_found ->
        try External (Set_of_closures_id.Map.find fid (ex_functions ())) with
        | Not_found ->
            Not_declared

  let is_function_constant cf =
    match function_declaration_position cf with
    | Local { ident } ->
        Set_of_closures_id.Set.mem ident P.constant_closures
    | External { ident } ->
        Set_of_closures_id.Set.mem ident (ex_constant_closures ())
    | Not_declared ->
        fatal_error (Format.asprintf "missing closure %a"
                       Closure_id.print cf)

  let is_local_function_constant cf =
    match function_declaration_position cf with
    | Local { ident } ->
        Set_of_closures_id.Set.mem ident P.constant_closures
    | External _ -> false
    | Not_declared ->
        fatal_error (Format.asprintf "missing closure %a"
                       Closure_id.print cf)

  let is_closure_constant fid =
    match functions_declaration_position fid with
    | Local { ident } ->
        Set_of_closures_id.Set.mem ident P.constant_closures
    | External { ident } ->
        Set_of_closures_id.Set.mem ident (ex_constant_closures ())
    | Not_declared ->
        fatal_error (Format.asprintf "missing closure %a"
                       Set_of_closures_id.print fid)

  let function_arity fun_id =
    let arity clos off = function_arity (find_declaration fun_id clos) in
    try arity (Closure_id.Map.find fun_id closures) fun_id with
    | Not_found ->
        try arity (Closure_id.Map.find fun_id (ex_closures ())) fun_id with
        | Not_found ->
            fatal_error (Format.asprintf "missing closure %a"
                           Closure_id.print fun_id)

  let not_constants = P.not_constants
  let is_constant id = not (Variable.Set.mem id not_constants.Flambdaconstants.not_constant_id)

  type env =
    { sb : unit flambda Variable.Map.t; (* substitution *)
      cm : Symbol.t Variable.Map.t; (* variables associated to constants *)
      approx : approx Variable.Map.t;
      toplevel : bool }

  let infos = init_infos ()

  let empty_env =
    { sb = Variable.Map.empty;
      cm = Variable.Map.empty;
      approx = Variable.Map.empty;
      toplevel = false }

  let canonical_symbol s = canonical_symbol s infos
  let set_symbol_alias s1 s2 =
    let s1' = canonical_symbol s1 in
    let s2' = canonical_symbol s2 in
    if s1' <> s2'
    then SymbolTbl.add infos.symbol_alias s1' s2'

  let add_sb id subst env =
    { env with sb = Variable.Map.add id subst env.sb }

  let add_cm id const env =
    { env with cm = Variable.Map.add id const env.cm }

  let copy_env id' id env =
    try
      let const = Variable.Map.find id env.cm in
      add_cm id' const env
    with Not_found -> env

  let add_global i approx =
    Hashtbl.add infos.global i approx
  let get_global i =
    try Hashtbl.find infos.global i
    with Not_found ->
      (* Value_unknown *)
      fatal_error (Format.asprintf "no global %i" i)

  let add_approx id approx env =
    { env with approx = Variable.Map.add id approx env.approx }
  let get_approx id env =
    try Variable.Map.find id env.approx with Not_found -> Value_unknown

  let extern_symbol_descr sym =
    if Compilenv.is_predefined_exception sym
    then None
    else
      let export = Compilenv.approx_for_global sym.sym_unit in
      try
        let id = SymbolMap.find sym export.ex_symbol_id in
        let descr = find_description id export in
        Some descr
      with
      | Not_found -> None

  let extern_id_descr ex =
    let export = Compilenv.approx_env () in
    try Some (find_description ex export)
    with Not_found -> None

  let get_descr approx =
    match approx with
    | Value_unknown -> None
    | Value_id ex ->
        (try Some (EidMap.find ex !(infos.ex_table)) with
         | Not_found ->
             extern_id_descr ex)
    | Value_symbol sym ->
        try
          let ex = SymbolMap.find sym !(infos.ex_symbol_id) in
          Some (EidMap.find ex !(infos.ex_table))
        with Not_found ->
          extern_symbol_descr sym

  let add_symbol sym id =
    infos.ex_symbol_id := SymbolMap.add sym id !(infos.ex_symbol_id)

  let symbol_id sym =
    try Some (SymbolMap.find sym !(infos.ex_symbol_id)) with Not_found -> None

  let add_constant lam ex_id =
    let sym = Compilenv.new_const_symbol' () in
    SymbolTbl.add infos.constants sym lam;
    add_symbol sym ex_id;
    sym

  let new_descr descr = new_descr descr infos
  let unit_approx () = Value_id (new_descr (Value_constptr 0))

  let rec conv env expr = fst (conv_approx env expr)
  and conv_approx (env : env) : P.t flambda -> unit flambda * approx = function
    | Fvar (id,_) ->
        begin
          (* If the variable reference a constant, it is replaced by the
             constant label *)
          try
            let lbl = Variable.Map.find id env.cm in
            Fsymbol(lbl, ()), Value_symbol lbl
          with Not_found ->

            (* If the variable is a recursive access to the function
               currently being defined: it is replaced by an offset in the
               closure. If the variable is bound by the closure, it is
               replace by a field access inside the closure *)
            try
              let lam = Variable.Map.find id env.sb in
              lam, get_approx id env
            with Not_found ->
              Fvar (id, ()), get_approx id env
        end

    | Fsymbol (sym,_) ->
        Fsymbol (sym,()),
        Value_symbol sym

    | Fconst (Fconst_base c as cst,_) ->
        begin let open Asttypes in
          match c with
          | Const_int i ->
              Fconst(cst, ()),
              Value_id (new_descr (Value_int i))
          | Const_char c ->
              Fconst(cst, ()),
              Value_id (new_descr (Value_int (Char.code c)))
          | Const_float s ->
              Fconst (cst, ()),
              Value_id (new_descr (Value_float (float_of_string s)))
          | Const_int32 i ->
              Fconst(cst, ()),
              Value_id (new_descr (Value_boxed_int (Int32, i)))
          | Const_int64 i ->
              Fconst(cst, ()),
              Value_id (new_descr (Value_boxed_int (Int64, i)))
          | Const_nativeint i ->
              Fconst(cst, ()),
              Value_id (new_descr (Value_boxed_int (Nativeint, i)))
          | Const_string (s,_) ->
              let v_string = { size = String.length s; contents = None } in
              let ex_id = new_descr (Value_string v_string) in
              Fsymbol (add_constant (Fconst (cst,())) ex_id,()),
              Value_id ex_id
        end
    | Fconst (Fconst_float f as cst, _) ->
        Fconst (cst, ()), Value_id (new_descr (Value_float f))
    | Fconst (Fconst_pointer c as cst,_) ->
        Fconst (cst, ()), Value_id (new_descr (Value_constptr c))
    | Fconst (Fconst_float_array c as cst, _) ->
        let ex_id = new_descr (Value_float_array (List.length c)) in
        Fsymbol(add_constant (Fconst (cst,())) ex_id,()),
        Value_id ex_id
    | Fconst (Fconst_immstring c as cst, _) ->
        let v_string = { size = String.length c; contents = Some c } in
        let ex_id = new_descr (Value_string v_string) in
        Fsymbol(add_constant (Fconst (cst,())) ex_id,()),
        Value_id ex_id

    | Flet(str, id, lam, body, _) ->
        let lam, approx = conv_approx env lam in
        let env =
          if is_constant id || str = Not_assigned
          then add_approx id approx env
          else add_approx id Value_unknown env
        in
        begin match is_constant id, constant_symbol lam, str with
        | _, _, Assigned
        | false, (Not_const | No_lbl | Const_closure), _ ->
            let ubody, body_approx = conv_approx env body in
            Flet(str, id, lam, ubody, ()), body_approx
        | true, No_lbl, Not_assigned ->
            (* no label: the value is an integer: substitute it *)
            conv_approx (add_sb id lam env) body
        | _, Lbl lbl, Not_assigned ->
            (* label: the value is a block: reference it *)
            conv_approx (add_cm id lbl env) body
        | true, Const_closure, Not_assigned ->
            conv_approx env body
        | true, Not_const, Not_assigned ->
            Format.eprintf "%a@.%a" Variable.print id
              Printflambda.flambda lam;
            assert false
        end

    | Fletrec(defs, body, _) ->
        let consts, not_consts =
          List.partition (fun (id,_) -> is_constant id) defs in

        let env, consts = List.fold_left
            (fun (env, acc) (id,def) ->
               let open Asttypes in
               match def with
               | Fconst (( Fconst_pointer _
                         | Fconst_base
                             (Const_int _ | Const_char _
                             | Const_float _ | Const_int32 _
                             | Const_int64 _ | Const_nativeint _)), _) ->
                   (* When the value is an integer constant, we cannot affect a label
                      to it: hence we must substitute it directly.
                      For other numerical constant, a label could be attributed, but
                      unboxing doesn't handle it well *)
                   add_sb id (conv env def) env, acc
               | Fvar (var_id, _) ->
                   assert(List.for_all(fun (id,_) -> not (Variable.equal var_id id)) consts);
                   (* For variables: the variable could have been substituted to
                      a constant: avoid it by substituting it directly *)
                   add_sb id (conv env def) env, acc
               | _ ->
                   let sym = Compilenv.new_const_symbol' () in
                   let env = add_cm id sym env in
                   env, (id,sym,def)::acc) (env,[]) consts in

        List.iter (fun (id,sym,def) ->
            match constant_symbol (conv env def) with
            | Lbl sym' ->
                (match symbol_id sym' with
                 | None -> ()
                 | Some eid -> add_symbol sym eid);
                set_symbol_alias sym sym'
            | _ ->
                fatal_error (Format.asprintf
                               "recursive constant value without symbol %a"
                               Variable.print id))
          consts;

        let not_consts, env =
          List.fold_right (fun (id,def) (not_consts,env') ->
              let flam, approx = conv_approx env def in
              let env' = add_approx id approx env' in
              (id, flam) :: not_consts, env') not_consts ([],env) in

        let body, approx = conv_approx env body in
        (match not_consts with
         | [] -> body
         | _ -> Fletrec(not_consts, body, ())),
        approx

    | Fset_of_closures ({ cl_fun = funct;
                  cl_free_var = fv;
                  cl_specialised_arg = spec_arg }, _) ->
        let args_approx = Variable.Map.map (fun id -> get_approx id env) spec_arg in
        conv_closure env funct args_approx spec_arg fv

    | Fclosure({ fu_closure = lam; fu_fun = id; fu_relative_to = rel }, _) as expr ->
        let ulam, fun_approx = conv_approx env lam in
        if is_local_function_constant id
        then
          (* Only function declared in the current module may need
             rewritting to a symbol. For external function it should
             already have been done at the original declaration. *)
          let sym = Compilenv.closure_symbol id in
          Fsymbol (sym,()),
          Value_symbol sym
        else
          let approx = match get_descr fun_approx with
            | Some (Value_set_of_closures closure)
            | Some (Value_closure { closure }) ->
                let ex = new_descr (Value_closure { fun_id = id; closure }) in
                Value_id ex
            | _ when not (Closure_id.in_compilation_unit
                            (Compilenv.current_unit ())
                            id) ->
                (* If some cmx files are missing, the value could be unknown.
                   Notice that this is valid only for something comming from
                   another compilation unit, otherwise this is a bug. *)
                Value_unknown
            | Some _ -> assert false
            | _ ->
                Format.printf "Unknown closure in offset %a@."
                  Printflambda.flambda expr;
                assert false
          in
          Fclosure({ fu_closure = ulam; fu_fun = id; fu_relative_to = rel },()),
          approx

    | Fvar_within_closure({vc_closure = lam;vc_var = env_var;vc_fun = env_fun_id}, _) as expr ->
        let ulam, fun_approx = conv_approx env lam in
        let approx = match get_descr fun_approx with
          | Some (Value_closure { closure = { bound_var } }) ->
              (try Var_within_closure.Map.find env_var bound_var with
               | Not_found ->
                   Format.printf "Wrong closure in env_field %a@.%a@."
                     Printflambda.flambda expr
                     Printflambda.flambda ulam;
                   assert false)
          | _ when not (Closure_id.in_compilation_unit
                          (Compilenv.current_unit ())
                          env_fun_id) ->
              (* If some cmx files are missing, the value could be unknown.
                   Notice that this is valid only for something comming from
                   another compilation unit, otherwise this is a bug. *)
              Value_unknown
          | Some _ -> assert false
          | None ->
              Format.printf "Unknown closure in env_field %a@.%a@."
                Printflambda.flambda expr
                Printflambda.flambda ulam;
              assert false in
        Fvar_within_closure({vc_closure = ulam;vc_var = env_var;vc_fun = env_fun_id}, ()),
        approx

    (* | Fapply({ap_function = *)
    (*             Fclosure ({fu_closure = Fset_of_closures ({ cl_fun = ffuns; *)
    (*                                                  cl_free_var = fv; *)
    (*                                                  cl_specialised_arg }, _); *)
    (*                         fu_fun = off; *)
    (*                         fu_relative_to = (None as rel)}, _); *)
    (*           ap_arg = args; *)
    (*           ap_kind = Direct direc; *)
    (*           ap_dbg = dbg}, _) -> *)
    (*     assert (Closure_id.equal off direc); *)
    (*     let uargs, args_approx = conv_list_approx env args in *)
    (*     let func = *)
    (*       try find_declaration off ffuns *)
    (*       with Not_found -> assert false in *)
    (*     assert(List.length uargs = List.length func.params); *)
    (*     let args_approx = *)
    (*       List.fold_right2 Variable.Map.add func.params args_approx Variable.Map.empty *)
    (*       |> Variable.Map.filter (fun var _ -> Variable.Map.mem var cl_specialised_arg) in *)
    (*     let uffuns, fun_approx = conv_closure env ffuns args_approx cl_specialised_arg fv in *)
    (*     let approx = match get_descr fun_approx with *)
    (*       | Some(Value_closure { fun_id; closure = { results } }) -> *)
    (*           Closure_id.Map.find fun_id results *)
    (*       | _ -> Value_unknown *)
    (*     in *)

    (*     Fapply({ap_function = *)
    (*               Fclosure ({fu_closure = uffuns; *)
    (*                           fu_fun = off; *)
    (*                           fu_relative_to = rel}, ()); *)
    (*             ap_arg = uargs; *)
    (*             ap_kind = Direct direc; *)
    (*             ap_dbg = dbg}, ()), *)
    (*     approx *)

    | Fapply({ap_function = funct; ap_arg = args; ap_kind; ap_dbg; ap_return_arity}, _) ->
        let ufunct, fun_approx = conv_approx env funct in
        let ap_kind = match ap_kind with
          | Direct _ -> ap_kind
          | Indirect -> match get_descr fun_approx with
            (* We mark some calls as direct when it is unknown:
               for instance if simplify wasn't run before. *)
            | Some (Value_closure { fun_id }) when
                (function_arity fun_id) = List.length args ->
                Direct fun_id
            | _ -> Indirect
        in
        let approx = match get_descr fun_approx with
          | Some(Value_closure { fun_id; closure = { results } }) ->
              Closure_id.Map.find fun_id results
          | _ -> Value_unknown
        in
        Fapply({ap_function = ufunct; ap_arg = conv_list env args;
                ap_kind; ap_dbg; ap_return_arity;}, ()),
        approx

    | Fswitch(arg, sw, _) ->
        Fswitch(conv env arg,
                { sw with
                  fs_consts = List.map (fun (i,lam) -> i, conv env lam) sw.fs_consts;
                  fs_blocks = List.map (fun (i,lam) -> i, conv env lam) sw.fs_blocks;
                  fs_failaction = may_map (conv env) sw.fs_failaction }, ()),
        Value_unknown

    | Fstringswitch(arg, sw, def, _) ->
        Fstringswitch
          (conv env arg,
           List.map (fun (i,lam) -> i, conv env lam) sw,
           may_map (conv env) def, ()),
        Value_unknown

    | Fprim(Lambda.Pgetglobal id, l, dbg, _) ->
        assert(l = []);
        let sym = Compilenv.symbol_for_global' id in
        Fsymbol (sym, ()),
        Value_symbol sym

    | Fprim(Lambda.Pgetglobalfield(id,i), l, dbg, v) ->
        assert(l = []);
        let lam = Fprim(Lambda.Pfield i, [Fprim(Lambda.Pgetglobal id, l, dbg, v)], dbg, v) in
        if id = Compilenv.current_unit_id ()
        then let approx = get_global i in
          match approx with
          | Value_symbol sym ->
              Fsymbol(sym,()), approx
          | _ ->
              conv env lam, approx
        else
          conv_approx env lam

    | Fprim(Lambda.Psetglobalfield (ex, i), [arg], dbg, _) ->
        let uarg, approx = conv_approx env arg in
        add_global i approx;
        Fprim(Lambda.Psetglobalfield (ex, i), [uarg], dbg, ()),
        Value_unknown

    | Fprim(Lambda.Pmakeblock(tag, Asttypes.Immutable) as p, args, dbg, _) ->
        let args, approxs = conv_list_approx env args in
        let block = Fprim(p, args, dbg, ()) in
        let ex = new_descr (Value_block (tag, Array.of_list approxs)) in
        if not (List.for_all is_simple_constant args)
        then block, Value_id ex
        else
          let sym = add_constant block ex in
          Fsymbol(sym, ()), Value_symbol sym

    (* TODO(wcrichton): add something for makeblock_noheap here? *)

(*  (* If global mutables are allowed: *)
    | Fprim(Lambda.Pmakeblock(tag, Asttypes.Mutable) as p, args, dbg, _)
      when env.toplevel ->
        let args, _approxs = conv_list_approx env args in
        let block = Fprim(p, args, dbg, ()) in
        let ex = new_descr (Value_mutable_block (tag, List.length args)) in
        if not (List.for_all is_simple_constant args)
        then block, Value_id ex
        else
          let sym = add_constant block ex in
          Fsymbol(sym, ()), Value_symbol sym
*)

    | Fprim(Lambda.Pfield i, [arg], dbg, _) ->
        let block, block_approx = conv_approx env arg in
        let approx = match get_descr block_approx with
          | Some (Value_block (_,fields)) ->
              if i >= 0 && i < Array.length fields
              then fields.(i)
              else Value_unknown
          | _ -> Value_unknown
        in
        Fprim(Lambda.Pfield i, [block], dbg, ()),
        approx

    | Fprim(p, args, dbg, _) ->
        Fprim(p, conv_list env args, dbg, ()),
        Value_unknown

    | Fstaticraise (i, args, _) ->
        Fstaticraise (i, conv_list env args, ()),
        Value_unknown

    | Fstaticcatch (i, vars, body, handler, _) ->
        Fstaticcatch (i, vars, conv env body, conv env handler, ()),
        Value_unknown

    | Ftrywith(body, id, handler, _) ->
        Ftrywith(conv env body, id, conv env handler, ()),
        Value_unknown

    | Fifthenelse(arg, ifso, ifnot, _) ->
        Fifthenelse(conv env arg, conv env ifso, conv env ifnot, ()),
        Value_unknown

    | Fsequence(lam1, lam2, _) ->
        let ulam1 = conv env lam1 in
        let ulam2, approx = conv_approx env lam2 in
        Fsequence(ulam1, ulam2, ()),
        approx

    | Fwhile(cond, body, _) ->
        Fwhile(conv env cond, conv env body, ()),
        unit_approx ()

    | Ffor(id, lo, hi, dir, body, _) ->
        Ffor(id, conv env lo, conv env hi, dir, conv env body, ()),
        unit_approx ()

    | Fassign(id, lam, _) ->
        Fassign(id, conv env lam, ()),
        unit_approx ()

    | Fsend(kind, met, obj, args, dbg, _) ->
        Fsend(kind, conv env met, conv env obj, conv_list env args, dbg, ()),
        Value_unknown

    | Funreachable _ ->
        Funreachable (),
        Value_unknown

  and conv_closure env functs param_approxs spec_arg fv =
    let closed = Set_of_closures_id.Set.mem functs.ident P.constant_closures in

    let fv_ulam_approx = Variable.Map.map (conv_approx env) fv in
    let fv_ulam = Variable.Map.map (fun (lam,approx) -> lam) fv_ulam_approx in

    let kept_fv id =
      let cv = Var_within_closure.wrap id in
      not (is_constant id)
      || (Var_within_closure.Set.mem cv used_variable_withing_closure) in

    let used_fv_approx = Variable.Map.filter (fun id _ -> kept_fv id) fv_ulam_approx in
    let used_fv = Variable.Map.map (fun (lam,approx) -> lam) used_fv_approx in

    let varmap_to_closfun_map map =
      Variable.Map.fold (fun var v acc ->
          let cf = Closure_id.wrap var in
          Closure_id.Map.add cf v acc)
        map Closure_id.Map.empty in

    let value_closure' =
      { closure_id = functs.ident;
        bound_var =
          Variable.Map.fold (fun off_id (_,approx) map ->
              let cv = Var_within_closure.wrap off_id in
              Var_within_closure.Map.add cv approx map)
            used_fv_approx Var_within_closure.Map.empty;
        results =
          varmap_to_closfun_map
            (Variable.Map.map (fun _ -> Value_unknown) functs.funs) } in

    (* add informations about free variables *)
    let env =
      Variable.Map.fold (fun id (_,approx) -> add_approx id approx)
        fv_ulam_approx env in

    (* add info about symbols in specialised_arg *)
    let env = Variable.Map.fold copy_env spec_arg env in

    (* Constant closures will be moved out of their scope and assigned to
       symbols.  When this happens, we must erase any constraint that
       specializes an argument to another variable, since that variable may
       no longer be in scope.  (Specializations of variables to values that
       are now referenced by symbols, rather than variables, will already have
       been performed.  As such, the operation is equivalent to erasing all
       specialization information.) *)
    let spec_arg =
      if closed then Variable.Map.empty
      else
        Variable.Map.filter (fun _ id -> not (Variable.Map.mem id env.cm))
          spec_arg
    in

    let conv_function id func =

      (* inside the body of the function, we cannot access variables
         declared outside, so take a clean substitution table. *)
      let env = { env with sb = Variable.Map.empty } in
      let env = { env with toplevel = false } in

      (* add informations about currently defined functions to
         allow direct call *)
      let env =
        Variable.Map.fold (fun id _ env ->
            let fun_id = Closure_id.wrap id in
            let desc = Value_closure { fun_id; closure = value_closure' } in
            let ex = new_descr desc in
            if closed then add_symbol (Compilenv.closure_symbol fun_id) ex;
            add_approx id (Value_id ex) env)
          functs.funs env
      in

      let env =
        (* param_approxs must be constants: part of specialised_args *)
        Variable.Map.fold (fun id approx env -> add_approx id approx env)
          param_approxs env in

      (* Add to the substitution the value of the free variables *)
      let add_env_variable id lam env =
        match constant_symbol lam with
        | Not_const ->
            assert(not closed);
            env
        | No_lbl ->
            add_sb id lam env
        | Lbl lbl ->
            add_cm id lbl env
        | Const_closure ->
            env
      in
      let env = Variable.Map.fold add_env_variable fv_ulam env in

      let env =
        if closed
        then
          (* if the function is closed, recursive call access those constants *)
          Variable.Map.fold (fun id _ env ->
              let fun_id = Closure_id.wrap id in
              add_cm id (Compilenv.closure_symbol fun_id) env) functs.funs env
        else env
      in
      let body, approx = conv_approx env func.body in
      { func with
        free_variables = Variable.Set.filter kept_fv func.free_variables;
        body }, approx
    in

    let funs_approx = Variable.Map.mapi conv_function functs.funs in

    let ufunct = { functs with funs = Variable.Map.map fst funs_approx } in

    let value_closure' =
      { value_closure' with
        results = varmap_to_closfun_map (Variable.Map.map snd funs_approx) } in

    let closure_ex_id = new_descr (Value_set_of_closures value_closure') in
    let value_closure = Value_id closure_ex_id in

    let expr =
      let expr =
        Fset_of_closures ({ cl_fun = ufunct;
                    cl_free_var = used_fv;
                    cl_specialised_arg = spec_arg }, ()) in
      if Set_of_closures_id.Set.mem ufunct.ident P.constant_closures
      then
        let sym = add_constant expr closure_ex_id in
        Fsymbol(sym, ())
      else expr in
    expr, value_closure


  and conv_list env l = List.map (conv env) l
  and conv_list_approx env l =
    List.split (List.map (conv_approx env) l)

  and is_simple_constant = function
    | Fconst _
    | Fsymbol _ -> true
    | _ -> false

  and constant_symbol : unit flambda -> const_sym = function
    | Fsymbol(sym, ()) ->
        Lbl sym
    | Fconst(_, ()) ->
        No_lbl
    | Fset_of_closures ({ cl_fun }, _) ->
        if Set_of_closures_id.Set.mem cl_fun.ident P.constant_closures
        then Const_closure
        else Not_const
    | _ -> Not_const


  let expr = conv { empty_env with toplevel = true } P.expr

end

module type Param2 = sig
  include Param1
  val infos : infos
  val expr : unit flambda
end

module Prepare(P:Param2) = struct
  open P

  (*** Preparing export informations: Replacing every symbol by its
       cannonical representant ***)

  let canonical_symbol s = canonical_symbol s infos

  (* Replace all symbols occurences by their representative *)
  let expr, constants =
    let use_canonical_symbols = function
      | Fsymbol(sym, ()) as expr ->
          let sym' = canonical_symbol sym in
          if sym == sym' then expr
          else Fsymbol(sym', ())
      | expr -> expr in
    let aux sym lam map =
      let sym' = canonical_symbol sym in
      SymbolMap.add sym' (Flambdaiter.map use_canonical_symbols lam) map
    in
    Flambdaiter.map use_canonical_symbols expr,
    SymbolTbl.fold aux infos.constants SymbolMap.empty

  let ex_functions =
    let ex_functions = ref Set_of_closures_id.Map.empty in
    let aux { cl_fun } _ =
      ex_functions := Set_of_closures_id.Map.add cl_fun.ident cl_fun !ex_functions
    in
    Flambdaiter.iter_on_closures aux expr;
    SymbolMap.iter (fun _ -> Flambdaiter.iter_on_closures aux) constants;
    !ex_functions

  (* Preparing export informations *)

  let canonical_approx = function
    | Value_unknown
    | Value_id _ as v -> v
    | Value_symbol sym ->
        Value_symbol (canonical_symbol sym)

  let rec canonical_descr = function
    | Value_block (tag, fields) ->
        Value_block (tag, Array.map canonical_approx fields)
    | Value_int _
    | Value_constptr _
    | Value_string _
    | Value_float _
    | Value_float_array _
    | Value_boxed_int _ as v -> v
    | Value_closure offset ->
        Value_closure { offset with closure = (aux_closure offset.closure) }
    | Value_set_of_closures clos ->
        Value_set_of_closures (aux_closure clos)
    | Value_mutable_block (tag, size) ->
        Value_mutable_block (tag, size)

  and aux_closure clos =
    { closure_id = clos.closure_id;
      bound_var = Var_within_closure.Map.map canonical_approx clos.bound_var;
      results = Closure_id.Map.map canonical_approx clos.results }

  let new_descr descr = new_descr descr infos

  (* build the approximation of the root module *)
  let root_id =
    let size_global =
      1 + (Hashtbl.fold (fun k _ acc -> max k acc) infos.global (-1)) in
    let fields = Array.init size_global (fun i ->
        try canonical_approx (Hashtbl.find infos.global i) with
        | Not_found -> Value_unknown) in
    new_descr (Value_block (0,fields))

  let root_approx =
    Value_id root_id

  (* replace symbol by their representative in value approximations *)
  let ex_values =
    EidMap.map canonical_descr !(infos.ex_table)

  (* build the symbol to id and id to symbol maps *)
  let module_symbol =
    Compilenv.current_unit_symbol ()

  let ex_symbol_id =
    let aux sym ex map =
      let sym' = canonical_symbol sym in
      SymbolMap.add sym' ex map
    in
    SymbolMap.fold aux !(infos.ex_symbol_id) SymbolMap.empty

  let ex_symbol_id =
    SymbolMap.add module_symbol root_id
      ex_symbol_id
  let ex_id_symbol =
    SymbolMap.fold (fun sym id map -> EidMap.add id sym map)
      ex_symbol_id EidMap.empty

  let ex_functions_off =
    let aux_fun ffunctions off_id _ map =
      let fun_id = Closure_id.wrap off_id in
      Closure_id.Map.add fun_id ffunctions map in
    let aux _ f map = Variable.Map.fold (aux_fun f) f.funs map in
    Set_of_closures_id.Map.fold aux ex_functions Closure_id.Map.empty

end

let convert (type a) ~compilation_unit (expr:a Flambda.flambda) =
  let not_constants = Flambdaconstants.not_constants ~compilation_unit ~for_clambda:true expr in
  let constant_closures = constant_closures not_constants expr in
  let module P1 = struct
    type t = a
    let expr = expr
    let not_constants = not_constants
    let constant_closures = constant_closures
  end in
  let module C = Conv(P1) in
  let module P2 = struct
    include P1
    let expr = C.expr
    let infos = C.infos
  end in
  let module C2 = Prepare(P2) in

  let export = let open Flambdaexport in
    { empty_export with
      ex_values = Flambdaexport.nest_eid_map C2.ex_values;
      ex_globals = Ident.Map.singleton
          (Compilenv.current_unit_id ()) C2.root_approx;
      ex_symbol_id = C2.ex_symbol_id;
      ex_id_symbol = Flambdaexport.nest_eid_map C2.ex_id_symbol;
      ex_functions = C2.ex_functions;
      ex_functions_off = C2.ex_functions_off;
      ex_constant_closures = constant_closures;
      ex_kept_arguments = C.ex_kept_arguments }
  in
  C2.expr, C2.constants, export

