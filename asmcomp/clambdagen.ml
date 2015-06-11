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

open Misc
open Symbol
open Abstract_identifiers
open Lambda
open Clambda
open Flambda

module Symbol_SCC = Sort_connected_components.Make(Symbol_Identifiable)

type ('a,'b) declaration_position =
  | Local of 'a
  | External of 'b
  | Not_declared

let list_closures expr constants =
  let closures = ref Closure_id.Map.empty in
  let aux expr = match expr with
    | Fset_of_closures({ cl_fun = functs; cl_free_var = fv }, data) ->
        let add off_id _ map =
          Closure_id.Map.add
            (Closure_id.wrap off_id)
            functs map in
        closures := Variable.Map.fold add functs.funs !closures;
    | e -> ()
  in
  Flambdaiter.iter aux expr;
  SymbolMap.iter (fun _ flam -> Flambdaiter.iter aux flam) constants;
  !closures

let reexported_offset extern_fun_offset_table extern_fv_offset_table expr constants =
  let set_fun = ref Closure_id.Set.empty in
  let set_fv = ref Var_within_closure.Set.empty in
  let aux expr = match expr with
    | Fvar_within_closure({vc_var = env_var; vc_fun = env_fun_id}, _) ->
        set_fun := Closure_id.Set.add env_fun_id !set_fun;
        set_fv := Var_within_closure.Set.add env_var !set_fv;
    | Fclosure({fu_fun = id; fu_relative_to = rel}, _) ->
        let set = match rel with
          | None -> !set_fun
          | Some rel -> Closure_id.Set.add rel !set_fun in
        set_fun := Closure_id.Set.add id set;
    | e -> ()
  in
  Flambdaiter.iter aux expr;
  SymbolMap.iter (fun _ flam -> Flambdaiter.iter aux flam) constants;
  let f extern_map offset new_map =
    try
      Closure_id.Map.add offset (Closure_id.Map.find offset extern_map) new_map
    with Not_found -> new_map (* local function *)
  in
  let f' extern_map offset new_map =
    try
      Var_within_closure.Map.add offset (Var_within_closure.Map.find offset extern_map) new_map
    with Not_found -> new_map (* local function *)
  in
  let fun_map = Closure_id.Set.fold (f extern_fun_offset_table) !set_fun in
  let fv_map = Var_within_closure.Set.fold (f' extern_fv_offset_table) !set_fv in
  fun_map, fv_map

let structured_constant_label expected_symbol ~shared cst =
  match expected_symbol with
  | None ->
      Compilenv.new_structured_constant cst ~shared
  | Some sym ->
      let lbl = string_of_linkage_name sym.sym_label in
      Compilenv.add_structured_constant lbl cst ~shared

module type Param1 = sig
  type t
  val expr : t flambda
  val constants : t flambda SymbolMap.t
end

module Offsets(P:Param1) = struct

  module Storer =
    Switch.Store
      (struct
        type t = P.t flambda
        type key = Flambdautils.sharing_key
        let make_key = Flambdautils.make_key
      end)

  (* The offset table associate a function label to its offset
     inside a closure *)
  let fun_offset_table = ref Closure_id.Map.empty
  (* The offset table associate a free variable to its offset inside a
     closure *)
  let fv_offset_table = ref Var_within_closure.Map.empty

  let rec iter = function
    | Fset_of_closures({cl_fun = funct; cl_free_var = fv}, _) ->
        iter_closure funct fv
    | _ -> ()

  and iter_closure functs fv =

    let funct = Variable.Map.bindings functs.funs in
    let fv = Variable.Map.bindings fv in

    (* build the table mapping the function to the offset of its code
       pointer inside the closure value *)
    let aux_fun_offset (map,env_pos) (id, func) =
      let pos = env_pos + 1 in
      let arity = Flambdautils.function_arity func in
      let env_pos = env_pos + 1 +
                    (if arity <> 1 then 3 else 2) in
      let map = Closure_id.Map.add (Closure_id.wrap id) pos map in
      (map,env_pos)
    in
    let fun_offset, fv_pos =
      List.fold_left aux_fun_offset (!fun_offset_table, -1) funct in

    (* Adds the mapping of free variables to their offset. It is not
       used inside the body of the function: it is directly
       substituted here. But if the function is inlined, it is
       possible that the closure is accessed from outside its body. *)
    let aux_fv_offset (map,pos) (id, _) =
      let off = Var_within_closure.wrap id in
      assert(not (Var_within_closure.Map.mem off map));
      let map = Var_within_closure.Map.add off pos map in
      (map,pos + 1)
    in
    let fv_offset, _ = List.fold_left aux_fv_offset
        (!fv_offset_table, fv_pos) fv in

    fun_offset_table := fun_offset;
    fv_offset_table := fv_offset;

    List.iter (fun (_,{body}) -> Flambdaiter.iter_toplevel iter body) funct

  let res =
    let run flam = Flambdaiter.iter_toplevel iter flam in
    run P.expr;
    SymbolMap.iter (fun _ -> run) P.constants;
    !fun_offset_table, !fv_offset_table

end

module type Param2 = sig
  include Param1
  val fun_offset_table : int Closure_id.Map.t
  val fv_offset_table : int Var_within_closure.Map.t
  val closures : t Flambda.function_declarations Closure_id.Map.t
  val constant_closures : Set_of_closures_id.Set.t
  val functions : unit Flambda.function_declarations Set_of_closures_id.Map.t
end

type const_lbl =
  | Lbl of string
  | No_lbl
  | Not_const

module Conv(P:Param2) = struct

  module Storer =
    Switch.Store
      (struct
        type t = P.t flambda
        type key = Flambdautils.sharing_key
        let make_key = Flambdautils.make_key
      end)

  (* The offset table associate a function label to its offset
     inside a closure *)
  let fun_offset_table = P.fun_offset_table
  let fv_offset_table = P.fv_offset_table
  let closures = P.closures

  (* offsets of functions and free variables in closures comming from
     a linked module *)
  let extern_fun_offset_table =
    (Compilenv.approx_env ()).Flambdaexport.ex_offset_fun
  let extern_fv_offset_table =
    (Compilenv.approx_env ()).Flambdaexport.ex_offset_fv
  let ex_closures =
    (Compilenv.approx_env ()).Flambdaexport.ex_functions_off
  let ex_functions =
    (Compilenv.approx_env ()).Flambdaexport.ex_functions
  let ex_constant_closures =
    (Compilenv.approx_env ()).Flambdaexport.ex_constant_closures

  let is_current_unit unit =
    Compilation_unit.equal (Compilenv.current_unit ()) unit

  let get_fun_offset off =
    try
      if Closure_id.in_compilation_unit (Compilenv.current_unit ()) off
      then Closure_id.Map.find off fun_offset_table
      else Closure_id.Map.find off extern_fun_offset_table
    with Not_found ->
      fatal_error (Format.asprintf "missing offset %a" Closure_id.print off)

  let get_fv_offset off =
    if Var_within_closure.in_compilation_unit (Compilenv.current_unit ()) off
    then
      if not (Var_within_closure.Map.mem off fv_offset_table)
      then fatal_error (Format.asprintf "env field offset not found: %a\n%!"
                          Var_within_closure.print off)
      else Var_within_closure.Map.find off fv_offset_table
    else Var_within_closure.Map.find off extern_fv_offset_table

  let function_declaration_position cf =
    try Local (Closure_id.Map.find cf P.closures) with
    | Not_found ->
        try External (Closure_id.Map.find cf ex_closures) with
        | Not_found ->
            Not_declared

  let functions_declaration_position fid =
    try Local (Set_of_closures_id.Map.find fid P.functions) with
    | Not_found ->
        try External (Set_of_closures_id.Map.find fid ex_functions) with
        | Not_found ->
            Not_declared

  let is_function_constant cf =
    match function_declaration_position cf with
    | Local { ident } ->
        Set_of_closures_id.Set.mem ident P.constant_closures
    | External { ident } ->
        Set_of_closures_id.Set.mem ident ex_constant_closures
    | Not_declared ->
        fatal_error (Format.asprintf "missing closure %a"
                       Closure_id.print cf)

  let is_closure_constant fid =
    match functions_declaration_position fid with
    | Local { ident } ->
        Set_of_closures_id.Set.mem ident P.constant_closures
    | External { ident } ->
        Set_of_closures_id.Set.mem ident ex_constant_closures
    | Not_declared ->
        fatal_error (Format.asprintf "missing closure %a"
                       Set_of_closures_id.print fid)

  type env =
    { subst : ulambda Variable.Map.t;
      var : Ident.t Variable.Map.t;
      toplevel : bool }

  let empty_env =
    { subst = Variable.Map.empty;
      var = Variable.Map.empty;
      toplevel = false }

  let add_sb id subst env =
    { env with subst = Variable.Map.add id subst env.subst }

  let find_sb id env = Variable.Map.find id env.subst
  let find_var id env = Variable.Map.find id env.var

  let add_unique_ident var env =
    let id = Variable.unique_ident var in
    id, { env with var = Variable.Map.add var id env.var }

  let rec conv ?(expected_symbol:Symbol.t option) (env : env) = function
    | Fvar (var,_) ->
        begin
          (* If the variable is a recursive access to the function
             currently being defined: it is replaced by an offset in the
             closure. If the variable is bound by the closure, it is
             replace by a field access inside the closure *)
          try find_sb var env
          with Not_found ->
            try Uvar (find_var var env)
            with Not_found ->
              fatal_error
                (Format.asprintf "Clambdagen.conv: unbound variable %a@."
                   Variable.print var)
        end

    | Fsymbol (sym,_) ->
        let lbl = Compilenv.cannonical_symbol (string_of_linkage_name sym.sym_label) in
        Uconst (Uconst_ref
                  (* Should delay the conversion a bit more *)
                  (lbl, None))

    | Fconst (cst,_) ->
        Uconst (conv_const expected_symbol cst)

    | Flet(str, var, lam, body, _) ->
        let id, env_body = add_unique_ident var env in
        Ulet(id, conv env lam, conv env_body body)

    | Fletrec(defs, body, _) ->
        let env, defs = List.fold_right (fun (var,def) (env, defs) ->
            let id, env = add_unique_ident var env in
            env, (id, def) :: defs) defs (env, []) in
        let udefs = List.map (fun (id,def) -> id, conv env def) defs in
        Uletrec(udefs, conv env body)

    | Fset_of_closures({ cl_fun = funct; cl_free_var = fv }, _) ->
        conv_closure env ~expected_symbol funct fv

    | Fclosure({ fu_closure = lam; fu_fun = id; fu_relative_to = rel }, _) ->
        let ulam = conv env lam in
        let offset = get_fun_offset id in
        let relative_offset = match rel with
          | None -> offset
          | Some rel -> offset - get_fun_offset rel
        in
        if relative_offset = 0
        then ulam
        (* compilation of let rec in cmmgen assumes
           that a closure is not offseted (Cmmgen.expr_size) *)
        else Uoffset(ulam, relative_offset)

    | Fvar_within_closure({vc_closure = lam;vc_var = env_var;vc_fun = env_fun_id}, _) ->
        let ulam = conv env lam in
        let fun_offset = get_fun_offset env_fun_id in
        let var_offset = get_fv_offset env_var in
        let pos = var_offset - fun_offset in
        Uprim(Pfield pos, [ulam], Debuginfo.none)

    | Fapply({ ap_function = funct; ap_arg = args; ap_return_arity = return_arity;
               ap_kind = Direct direct_func; ap_dbg = dbg }, _) ->
        conv_direct_apply (conv env funct) args direct_func return_arity dbg env

    | Fapply({ ap_function = funct; ap_arg = args;
               ap_kind = Indirect; ap_dbg = dbg }, _) ->
        (* the closure parameter of the function is added by cmmgen, but
           it already appears in the list of parameters of the clambda
           function for generic calls. Notice that for direct calls it is
           added here. *)
        Ugeneric_apply(conv env funct, conv_list env args, dbg)

    | Fswitch(arg, sw, d) ->
        let aux () =
          let const_index, const_actions =
            conv_switch env sw.fs_consts sw.fs_numconsts sw.fs_failaction
          and block_index, block_actions =
            conv_switch env sw.fs_blocks sw.fs_numblocks sw.fs_failaction in
          Uswitch(conv env arg,
                  {us_index_consts = const_index;
                   us_actions_consts = const_actions;
                   us_index_blocks = block_index;
                   us_actions_blocks = block_actions})
        in
        let rec simple_expr = function
          | Fconst( Fconst_base (Asttypes.Const_string _), _ ) -> false
          | Fvar _ | Fsymbol _ | Fconst _ -> true
          | Fstaticraise (_,args,_) -> List.for_all simple_expr args
          | _ -> false in
        (* Check that failaction is effectively copiable: i.e. it
           can't declare symbols. If it is not the case, share it
           through a staticraise/staticcatch *)
        begin match sw.fs_failaction with
        | None -> aux ()
        | Some (Fstaticraise (_,args,_))
          when List.for_all simple_expr args -> aux ()
        | Some failaction ->
            let exn = Static_exception.create () in
            let fs_failaction = Some (Fstaticraise(exn,[], d)) in
            let sw = { sw with fs_failaction } in
            let expr =
              Fstaticcatch(exn, [], Fswitch(arg, sw, d), failaction, d) in
            conv env expr
        end

    | Fstringswitch(arg, sw, def, d) ->
        let arg = conv env arg in
        let sw = List.map (fun (s, e) -> s, conv env e) sw in
        let def = Misc.may_map (conv env) def in
        Ustringswitch(arg, sw, def)

    | Fprim(Pgetglobal id, l, dbg, _) ->
        assert false

    | Fprim(Pgetglobalfield(id,i), l, dbg, _) ->
        assert(l = []);
        Uprim(Pfield i,
              [Uprim(Pgetglobal (Ident.create_persistent
                                   (Compilenv.symbol_for_global id)), [], dbg)],
              dbg)

    | Fprim(Psetglobalfield (_ex, i), [arg], dbg, _) ->
        Uprim(Psetfield (i,false),
              [Uprim(Pgetglobal (Ident.create_persistent
                                   (Compilenv.make_symbol None)), [], dbg);
               conv env arg],
              dbg)

    | Fprim(Pmakeblock(tag, Asttypes.Immutable) as p, args, dbg, _) ->
        let args = conv_list env args in
        begin match constant_list args with
        | None ->
            Uprim(p, args, dbg)
        | Some l ->
            let cst = Uconst_block (tag,l) in
            let lbl = structured_constant_label expected_symbol ~shared:true cst in
            Uconst(Uconst_ref (lbl, Some (cst)))
        end

(*  (* If global mutables are allowed: *)
    | Fprim(Pmakeblock(tag, Asttypes.Mutable) as p, args, dbg, _) when
        env.toplevel ->
        let args = conv_list env args in
        begin match constant_list args with
        | None ->
            Uprim(p, args, dbg)
        | Some l ->
            let cst = Uconst_block (tag,l) in
            let lbl = structured_constant_label expected_symbol ~shared:false cst in
            Uconst(Uconst_ref (lbl, Some (cst)))
        end
*)

    | Fprim(p, args, dbg, _) ->
        Uprim(p, conv_list env args, dbg)
    | Fstaticraise (i, args, _) ->
        Ustaticfail (Static_exception.to_int i, conv_list env args)
    | Fstaticcatch (i, vars, body, handler, _) ->
        let env_handler, ids =
          List.fold_right (fun var (env, ids) ->
              let id, env = add_unique_ident var env in
              env, id :: ids) vars (env, []) in
        Ucatch (Static_exception.to_int i, ids,
                conv env body, conv env_handler handler)
    | Ftrywith(body, var, handler, _) ->
        let id, env_handler = add_unique_ident var env in
        Utrywith(conv env body, id, conv env_handler handler)
    | Fifthenelse(arg, ifso, ifnot, _) ->
        Uifthenelse(conv env arg, conv env ifso, conv env ifnot)
    | Fsequence(lam1, lam2, _) ->
        Usequence(conv env lam1, conv env lam2)
    | Fwhile(cond, body, _) ->
        Uwhile(conv env cond, conv env body)
    | Ffor(var, lo, hi, dir, body, _) ->
        let id, env_body = add_unique_ident var env in
        Ufor(id, conv env lo, conv env hi, dir, conv env_body body)
    | Fassign(var, lam, _) ->
        let id = try find_var var env with Not_found -> assert false in
        Uassign(id, conv env lam)
    | Fsend(kind, met, obj, args, dbg, _) ->
        Usend(kind, conv env met, conv env obj, conv_list env args, dbg)

    | Funreachable _ ->
        (* shoudl'nt be executable, maybe build something else *)
       Uunreachable
    (* Uprim(Praise, [Uconst (Uconst_pointer 0, None)], Debuginfo.none) *)

  and conv_switch env cases num_keys default =
    let num_keys =
      if Ext_types.Int.Set.cardinal num_keys = 0
      then 0
      else Ext_types.Int.Set.max_elt num_keys + 1 in
    let index = Array.make num_keys 0
    and store = Storer.mk_store () in

    (* First default case *)
    begin match default with
    | Some def when List.length cases < num_keys ->
        ignore (store.Switch.act_store def)
    | _ -> ()
    end ;
    (* Then all other cases *)
    List.iter (fun (key,lam) -> index.(key) <- store.Switch.act_store lam) cases;
    (* Compile action *)
    let actions = Array.map (conv env) (store.Switch.act_get ()) in
    match actions with
    | [| |] -> [| |], [| |] (* May happen when default is None *)
    | _     -> index, actions

  and conv_direct_apply ufunct args direct_func return_arity dbg env =
    let closed = is_function_constant direct_func in
    let label = Compilenv.function_label direct_func in
    let uargs =
      let uargs = conv_list env args in
      if closed then uargs else uargs @ [ufunct] in

    let apply = Udirect_apply(label, uargs, return_arity, dbg) in

    (* This is usualy sufficient to detect closure with side effects *)
    let rec no_effect = function
      | Uvar _ | Uconst _ | Uprim(Pgetglobalfield _, _, _)
      | Uprim(Pgetglobal _, _, _) -> true
      | Uprim(Pfield _, [arg], _) -> no_effect arg
      | _ -> false in

    let no_effect = function
      | Uclosure _ ->
          (* if the function is closed, then it is a Uconst otherwise,
             we do not call this function *)
          assert false
      | e -> no_effect e in

    (* if the function is closed, the closure is not in the parameters,
       so we must ensure that it is executed if it does some side effects *)
    if closed && not (no_effect ufunct)
    then Usequence(ufunct, apply)
    else apply

  and conv_closure env functs fv ~expected_symbol =
    (* Make the susbtitutions for variables bound by the closure:
       the variables bounds are the functions inside the closure and
       the free variables of the functions.

       For instance the closure for a code like

         let rec fun_a x =
           if x <= 0 then 0 else fun_b (x-1) v1
         and fun_b x y =
           if x <= 0 then 0 else v1 + v2 + y + fun_a (x-1)

       will be represented in memory as:

         [ closure header; fun_a;
           1; infix header; fun caml_curry_2;
           2; fun_b; v1; v2 ]

       fun_a and fun_b will take an additional parameter 'env' to
       access their closure.  It will be shifted such that in the body
       of a function the env parameter points to its code
       pointer. i.e. in fun_b it will be shifted by 3 words.

       Hence accessing to v1 in the body of fun_a is accessing to the
       6th field of 'env' and in the body of fun_b it is the 1st
       field.

       If the closure can be compiled to a constant, the env parameter
       is not always passed to the function (for direct calls). Inside
       the body of the function, we acces a constant globaly defined:
       there are label camlModule__id created to access the functions.
       fun_a can be accessed by 'camlModule__id' and fun_b by
       'camlModule__id_3' (3 is the offset of fun_b in the closure).

       Inside a constant closure, there will be no access to the
       closure for the free variables, but if the function is inlined,
       some variables can be retrieved from the closure outside of its
       body, so constant closure still contains their free
       variables. *)

    let funct = Variable.Map.bindings functs.funs in
    let fv = Variable.Map.bindings fv in
    let closed = is_closure_constant functs.ident in

    (* the environment variable used for non constant closures *)
    let env_var = Ident.create "env" in
    (* the label used for constant closures *)
    let closure_lbl = match expected_symbol with
      | None ->
          assert(not closed);
          Compilenv.new_const_symbol ()
      | Some sym ->
          (* should delay conversion *)
          string_of_linkage_name sym.sym_label
    in

    let fv_ulam = List.map (fun (id,lam) -> id,conv env lam) fv in

    let conv_function (id,func) =
      let cf = Closure_id.wrap id in
      (* adds variables from the closure to the substitution environment *)
      let fun_offset = Closure_id.Map.find cf fun_offset_table in

      (* inside the body of the function, we cannot access variables
         declared outside, so take a clean substitution table. *)
      let env = empty_env in

      let env =
        (* Add to the substitution the value of the free variables *)

        let add_env_variable env (id,lam) =
          match constant_label lam with
          | Not_const ->
              assert(not closed);
              let var_offset = Var_within_closure.Map.find
                  (Var_within_closure.wrap id) fv_offset_table in
              let pos = var_offset - fun_offset in
              add_sb id (Uprim(Pfield pos, [Uvar env_var], Debuginfo.none)) env
          | No_lbl
          | Lbl _ -> env
        in

        let env = List.fold_left add_env_variable env fv_ulam in

        (* Add to the substitution the value of the functions defined in
           the current closure:
           this can be retrieved by shifting the environment. *)
        if closed
        then env
        else
          let add_offset_subst pos env (id,_) =
            let offset = Closure_id.Map.find (Closure_id.wrap id) fun_offset_table in
            let exp = Uoffset(Uvar env_var, offset - pos) in
            add_sb id exp env in
          List.fold_left (add_offset_subst fun_offset) env funct
      in

      let env_body, params =
        List.fold_right (fun var (env, params) ->
            let id, env = add_unique_ident var env in
            env, id :: params) func.params (env, []) in

      { Clambda.label = Compilenv.function_label cf;
        arity = Flambdautils.function_arity func;
        params = if closed then params else params @ [env_var];
        body = conv env_body func.body;
        dbg = func.dbg } in

    let ufunct = List.map conv_function funct in

    if closed
    then
      match constant_list (List.map snd fv_ulam) with
      | None -> assert false
      | Some fv_const ->
          let cst = Uconst_closure (ufunct, closure_lbl, fv_const) in
          let closure_lbl = Compilenv.add_structured_constant closure_lbl cst ~shared:true in
          Uconst(Uconst_ref (closure_lbl, Some cst))
    else
      Uclosure (ufunct, List.map snd fv_ulam)

  and conv_list env l = List.map (conv env) l

  and conv_const expected_symbol cst =
    let open Asttypes in
    let str ~shared cst =
      let name = structured_constant_label expected_symbol ~shared cst in
      Uconst_ref (name, Some cst)
    in
    match cst with
    | Fconst_pointer c -> Uconst_ptr c
    | Fconst_base (Const_int c) -> Uconst_int c
    | Fconst_base (Const_char c) -> Uconst_int (Char.code c)
    | Fconst_float f ->
        str ~shared:true (Uconst_float f)
    | Fconst_base (Const_float x) ->
        str ~shared:true (Uconst_float (float_of_string x))
    | Fconst_base (Const_int32 x) ->
        str ~shared:true (Uconst_int32 x)
    | Fconst_base (Const_int64 x) ->
        str ~shared:true (Uconst_int64 x)
    | Fconst_base (Const_nativeint x) ->
        str ~shared:true (Uconst_nativeint x)
    | Fconst_base (Const_string (s,o)) ->
        str ~shared:false (Uconst_string s)
    | Fconst_float_array c ->
        (* constant float arrays are really immutable *)
        str ~shared:true (Uconst_float_array (List.map float_of_string c))
    | Fconst_immstring c ->
        str ~shared:true (Uconst_string c)

  and constant_list l =
    let rec aux acc = function
      | [] ->
          Some (List.rev acc)
      | Uconst(v) :: q ->
          aux (v :: acc) q
      | _ -> None
    in
    aux [] l

  and constant_label : ulambda -> const_lbl = function
    | Uconst(Uconst_int _ | Uconst_ptr _) -> No_lbl
    | Uconst(Uconst_ref (lbl, _)) -> Lbl lbl
    | Uprim(Pgetglobal id, [], _) ->
        Lbl (Ident.name id)
    | _ -> Not_const

  let structured_constant_for_symbol sym = function
    | Uconst(Uconst_ref (lbl', Some cst)) ->
        let lbl = Compilenv.cannonical_symbol (string_of_linkage_name sym.sym_label) in
        assert(lbl = Compilenv.cannonical_symbol lbl');
        cst
    (* | Uconst(Uconst_ref(None, Some cst)) -> cst *)
    | _ -> assert false

  let symbol_dependency existing expr =
    let r = ref SymbolSet.empty in
    Flambdaiter.iter
      (function
        | Fsymbol (sym,_) ->
            if SymbolMap.mem sym existing
            then r := SymbolSet.add sym !r
        | _ -> ())
      expr;
    !r

  (* Symbols needs to be sorted before transforming their definition to allow as
     much sharing as possible. For instance if the existing symbols are:
       sym_1 -> (sym_3,sym_3)
       sym_2 -> (sym_4,sym_4)
       sym_3 -> (1,2)
       sym_4 -> (1,2)
     In that case, we expect sym_3 and sym_4 to be shared and also sym_1 and
     sym_2. If it is converted in that order, when sym_1 and sym_2 are converted,
     sym_3 and sym_4 havent and are not known to be equal yet. Hence sym_1 and
     sym_2 won't be shared. To avoid that problem, we need to convert the symbol
     from leaf to roots, the dependency topological order:
        sym_3 -> (1,2)
        sym_4 -> (1,2)
        sym_1 -> (sym_3,sym_3)
        sym_2 -> (sym_4,sym_4)

      Notice that for cyclic values there is no good order that allows to find
      this sharing. We would need some kind of automata minimization procedure.
  *)

  let constants =
    let symbol_dependency_map =
      SymbolMap.map (fun expr -> symbol_dependency P.constants expr)
        P.constants
    in
    let sorted_symbols =
      List.flatten
        (List.map (function
             | Symbol_SCC.Has_loop l -> l
             | No_loop v -> [v])
            (List.rev
               (Array.to_list
                  (Symbol_SCC.connected_components_sorted_from_roots_to_leaf
                     symbol_dependency_map))))
    in
    List.fold_left (fun acc sym ->
        let lam = SymbolMap.find sym P.constants in
        let ulam = conv { empty_env with toplevel = true } ~expected_symbol:sym lam in
        SymbolMap.add sym (structured_constant_for_symbol sym ulam) acc)
      SymbolMap.empty sorted_symbols

  let res = conv { empty_env with toplevel = true } P.expr

end

let convert (type a)
    ((expr:a flambda),
     (constants:a flambda SymbolMap.t),
     exported) =
  let closures = list_closures expr constants in
  let module P1 = struct
    type t = a
    let expr = expr
    let constants = constants
    let constant_closures = exported.Flambdaexport.ex_constant_closures
  end in
  let fun_offset_table, fv_offset_table =
    let module O = Offsets(P1) in
    O.res
  in
  let extern_fun_offset_table =
    (Compilenv.approx_env ()).Flambdaexport.ex_offset_fun in
  let extern_fv_offset_table =
    (Compilenv.approx_env ()).Flambdaexport.ex_offset_fv in
  let add_ext_offset_fun, add_ext_offset_fv =
    reexported_offset extern_fun_offset_table extern_fv_offset_table expr constants in
  let module P2 = struct include P1
    let fun_offset_table = fun_offset_table
    let fv_offset_table = fv_offset_table
    let closures = closures
    let functions = exported.Flambdaexport.ex_functions
  end in
  let module C = Conv(P2) in
  let export = let open Flambdaexport in
    { exported with
      ex_offset_fun = add_ext_offset_fun fun_offset_table;
      ex_offset_fv = add_ext_offset_fv fv_offset_table }
  in
  Compilenv.set_export_info export;
  SymbolMap.iter
    (fun sym cst ->
       let lbl = string_of_linkage_name sym.sym_label in
       Compilenv.add_exported_constant lbl)
    C.constants;
  C.res
