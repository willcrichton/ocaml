open Flambda
open Ext_types

let plam flam =
  if !Clflags.dump_flambda (* && false *) then begin
    Flambda_printers.named Format.std_formatter flam;
    Format.printf "\n"
  end

(*  let check_can_unbox ({body; return_arity} : 'a function_declaration) =
 *   let fail_return = (false, 0, Int.Map.empty) in
 *   if return_arity <> 1 then fail_return else
 *   let unbox_return (can_unbox, num_returns, map) flam = match flam with
 *     | Fprim(Pmakeblock(tag, Immutable), arg, _, _) ->
 *       (\* 9 is an arbitrary maximum number of registers, see Proc.loc_results *\)
 *       let arity = List.length arg in
 *       if arity > 9 || arity = 0 then (fail_return, flam)
 *       else ((can_unbox, arity, Int.Map.add tag arity map), flam)
 *     | Fstaticraise _ | Fconst(Fconst_pointer _, _) -> ((can_unbox, num_returns, map), flam)
 *     | _ -> (fail_return, flam) in
 *   fst (Flambdaiter.fold_return_sites unbox_return (true, 1, Int.Map.empty) body)
 *
 * let no_arg_variant = 10 (\* TODO(wcrichton): appropriate value for this? *\)
 * let dummy_value = 1337
 *
 * let fold_return_sites (type acc) f f_named (acc : acc) tree =
 *   let rec aux acc (tree : Flambda.t) : acc * Flambda.t = match tree with
 *     | Var _
 *     | Apply _
 *     | Send _
 *     | Assign _
 *     | Static_raise _
 *     | Static_catch _
 *     | While _
 *     | For _
 *     | Proved_unreachable -> f acc tree
 *
 *     | Let (kind, var, def, body) ->
 *       let (acc, body') = aux acc body in
 *       (acc, Let (kind, var, def, body'))
 *
 *     | Let_rec (bindings, body) ->
 *       let (acc, body') = aux acc body in
 *       (acc, Let_rec (bindings, body'))
 *
 *     | If_then_else (var, then_, else_) ->
 *       let (acc, then_') = aux acc then_ in
 *       let (acc, else_') = aux acc else_ in
 *       (acc, If_then_else (var, then_', else_'))
 *
 *     | Switch (var, switch) ->
 *       let (acc, consts') = List.fold_left listfold (acc, []) switch.consts in
 *       let (acc, blocks') = List.fold_left listfold (acc, []) switch.blocks in
 *       let (acc, failaction') = begin
 *         match switch.failaction with
 *         | Some action ->
 *           let (acc, action') = aux acc action in
 *           (acc, Some action')
 *         | None -> (acc, None)
 *       end in
 *       (acc, Switch(var, {switch with consts = consts';
 *                                      blocks = blocks';
 *                                      failaction = failaction'}))
 *
 *
 *     | String_switch (var, branches, failaction) ->
 *       let (acc, branches') = List.fold_left listfold (acc, []) branches in
 *       let (acc, failaction') = begin
 *         match failaction with
 *         | Some action ->
 *           let (acc, action') = aux acc action in
 *           (acc, Some action')
 *         | None -> (acc, None)
 *       end in
 *       (acc, String_switch(var, branches', failaction'))
 *
 *     | Try_with (try_, exception_, catch) ->
 *       let (acc, try_') = aux acc try_ in
 *       let (acc, catch') = aux acc catch in
 *       (acc, Try_with(try_', exception_, catch'))
 *
 *   (\* and aux_named acc (tree : Flambda.named) : acc * Flambda.named = match tree with
 *    *   | Expr flam ->
 *    *     let (acc, flam') = aux acc flam in
 *    *     (acc, Expr flam')
 *    *   | _ -> f_named acc tree *\)
 *
 *   and listfold : 'a .
 *     acc * ('a * Flambda.t) list
 *     -> 'a * Flambda.t
 *     -> acc * ('a * Flambda.t) list =
 *     fun (acc, list) (i, flam) ->
 *       let (acc, flam') = aux acc flam in
 *       (acc, (i, flam') :: list)
 *
 *   in aux acc tree
 *
 *
 * let unbox_fn ({body} : 'a function_declaration) num_returns =
 *   let int_to_flam n = Fconst(Fconst_base(Const_int(n)), Expr_id.create()) in
 *   let rec generator = function
 *       0 -> [] | n -> (int_to_flam dummy_value) :: generator (n - 1) in
 *   let unbox_return () = function
 *     | Fprim(Pmakeblock(tag, Immutable), arg, dbg, attr) ->
 *       let len = num_returns - (List.length arg) in
 *       ((), Fprim(
 *          Pmakeblock_noheap,
 *          ((int_to_flam tag) :: arg) @ (generator len),
 *          dbg,
 *          attr))
 *     | Fconst(Fconst_pointer n, attr)  ->
 *       let len = num_returns - 1 in
 *       ((), Fprim(
 *          Pmakeblock_noheap,
 *          (int_to_flam no_arg_variant) :: (int_to_flam n) :: (generator len),
 *          Debuginfo.none,
 *          attr))
 *     | Fstaticraise _ as e -> ((), e)
 *     | _ -> Misc.fatal_error "Unboxed invalid return site" in
 *   let (_, body) = Flambdaiter.fold_return_sites unbox_return () body in
 *   body  *)

let no_arg_variant = 10 (* CR wcrichton: appropriate value for this? *)
(* let dummy_value = 1337 *)

let check_can_unbox {body; return_arity} =
  if return_arity <> 1 then None
  else begin
    let returned_vars = ref Variable.Set.empty in
    ignore (Flambda_iterators.map_return_vars (fun v ->
      returned_vars := Variable.Set.add v !returned_vars; v)
      body);
    let can_unbox = ref `No_blocks_found in
    ignore (Flambda_iterators.iter (fun t -> match t with
      | Let (Immutable, var, binding, _) ->
        if not (Variable.Set.mem var !returned_vars) then ()
        else begin
           match binding with
            | Prim (Pmakeblock (_, Immutable), _, _) ->
              begin match !can_unbox with
              | `Bad_return -> ()
              | _ -> can_unbox := `Ok_return
              end
            | Const (Const_pointer _) -> ()
            | _ -> can_unbox := `Bad_return
        end
      | Let (Mutable, var, _, _) ->
        if Variable.Set.mem var !returned_vars then
          can_unbox := `Bad_return
      | _ -> ())
      (fun _ -> ())
      body);
    match !can_unbox with
    | `Ok_return -> Some returned_vars
    | _ -> None
  end


let unbox_returns tree =
  Flambda_iterators.map (fun x -> x) (function
    | Set_of_closures ({function_decls; free_vars; (*specialised_args*)} as closure_set)
      as original_tree ->
      if not (!Clflags.dump_flambda) ||
        Variable.Map.cardinal function_decls.funs <> 1
      then original_tree else begin
      let mkvar =
        Variable.create ~current_compilation_unit:function_decls.compilation_unit in
      let mkvar_suffix v s = mkvar ((Variable.unique_name v) ^ s) in
      let (fn_id, fn) = Variable.Map.choose function_decls.funs in
      begin match check_can_unbox fn with
      | None -> original_tree
      | Some returned_vars ->
        plam original_tree;
        let updated_vars = ref Variable.Map.empty in
        let tag_arities = ref Int.Map.empty in
        let body = Flambda_iterators.map (fun t -> match t with
          | Let (Immutable, var, binding, body) ->
            if not (Variable.Set.mem var !returned_vars) then t
            else begin
              let new_var = mkvar_suffix var "_unboxed" in
              let tag_var = mkvar_suffix var "_tag" in
              let (args, tag) = begin match binding with
                | Prim (Pmakeblock (tag, Immutable), args, _) -> (args, tag)
                | Const (Const_pointer _) -> ([var], no_arg_variant)
                | _ -> Misc.fatal_error "Returned variable must be block or ptr"
              end in
              updated_vars := Variable.Map.add var (new_var, List.length args) !updated_vars;
              tag_arities := Int.Map.add tag (List.length args) !tag_arities;
              Let (Immutable, var, binding,
                   Let (Immutable, tag_var, Const (Const_base (Const_int tag)),
                        Let (Immutable, new_var,
                             Prim (Pmakeblock_noheap, tag_var :: args, Debuginfo.none),
                             body)))
            end
          | _ -> t)
          (fun x -> x)
          fn.body
        in
        let body = Flambda_iterators.map_return_vars (fun v ->
          try fst (Variable.Map.find v !updated_vars) with Not_found -> v)
          body
        in
        let max_return_arity = Variable.Map.fold (fun _ (_, arity) acc ->
          max arity acc)
          !updated_vars
          0
        in
        let result_vars =
          let rec builder = function
            | 0 -> []
            | n -> ("_result" ^ (string_of_int (n - 1))) :: (builder (n - 1))
          in
          List.map (mkvar_suffix fn_id) (List.rev (builder max_return_arity))
        in
        let gen name binding =
          let var = mkvar name in
          (var, Let (Immutable, var, binding, Var var))
        in
        let rebind let_ body = match let_ with
          | Let (Immutable, var, binding, _) -> Let (Immutable, var, binding, body)
          | _ -> assert false
        in
        let unboxed_return_id = mkvar_suffix fn_id "_unboxed_return" in
        let tag_var = mkvar_suffix fn_id "_tag" in
        let switch =
          let tags = List.map fst (Int.Map.bindings !tag_arities) in
          let mkblock tag =
            let return_arity = Int.Map.find tag !tag_arities in
            let (_, let_) =
              gen "switch_branch" (Prim (
                Pmakeblock (tag, Immutable),
                (result_vars
                 |> List.mapi (fun i x -> (i, x))
                 |> List.filter (fun (i, _) -> i < return_arity)
                 |> List.map snd),
                Debuginfo.none))
            in
            (tag, let_)
          in
          Switch (
            tag_var,
            {
              numconsts = Int.Set.of_list tags;
              consts = List.map mkblock tags;
              numblocks = Int.Set.empty;
              blocks = [];
              failaction = None;
            })
        in
        let (special_const_var, special_const_body) =
          gen "special_const" (Const (Const_base (Const_int no_arg_variant)))
        in
        let (cmp_var, cmp_body) =
          gen "cmp" (Prim (Pintcomp Cneq, [tag_var; special_const_var], Debuginfo.none))
        in
        let (switch_var, switch_body) = gen "switch" (Expr switch) in
        (* let (_, if_then_let) =
         *   gen "if_then" (Prim (Pisblock, [cmp_var; switch_var; List.nth result_vars 0],
         *                        Debuginfo.none))
         * in *)
        let if_then_let =
          List.fold_right rebind [special_const_body; cmp_body; switch_body] (Prim (Pisblock, [cmp_var; switch_var; List.nth result_vars 0],
                               Debuginfo.none))(* if_then_let *)
        in
        let field_bindings =
          List.fold_left
            (fun acc (index, result_var) ->
               Let (Immutable,
                    result_var,
                    Prim (Pgetblock_noheap index, [unboxed_return_id], Debuginfo.none),
                    acc))
            if_then_let
            (List.mapi (fun i x -> (i, x)) (tag_var :: result_vars))
        in
        let wrapper_params = List.map (fun id -> mkvar_suffix id "_wrapper") fn.params in
        let inner_closure_id = mkvar_suffix fn_id "_multireturn" in
        let inner_fn_id = mkvar_suffix fn_id "_unboxed" in
        let apply_inner =
          Let (
            Immutable,
            unboxed_return_id,
            Expr (Apply ({
              func = inner_closure_id;
              args = wrapper_params;
              kind = Direct (Closure_id.wrap inner_fn_id);
              dbg = Debuginfo.none;
              return_arity = max_return_arity + 1;
            })),
            field_bindings)
        in
        let new_free_closure_var =
          List.map
            (fun (key, value) -> (key, value, mkvar "new_free_var"))
            (Variable.Map.bindings free_vars)
        in
        let inner_free_closure_var =
          List.fold_left
            (fun map (value, _, key) ->
               Variable.Map.add key value map)
            Variable.Map.empty
            new_free_closure_var
        in
        let inner_free_fn_var =
          fn.free_variables
          |> List.fold_right
               Variable.Set.remove
               (List.map (fun (k, _, _) -> k) new_free_closure_var)
          |> List.fold_right
               Variable.Set.add
               (List.map (fun (_ ,_, v) -> v) new_free_closure_var)
        in
        let final_fn =
          let reverse_map =
            List.fold_left
              (fun map (key, _, value) -> Variable.Map.add key value map)
              Variable.Map.empty
              new_free_closure_var in
          let body = Flambda_iterators.map (function
            | Var var ->
              (try Var (Variable.Map.find var reverse_map) with Not_found -> Var var)
            | e -> e)
            (fun x -> x)
            body
          in
          {fn with
           body;
           free_variables = inner_free_fn_var;
           return_arity = max_return_arity + 1}
        in
        let (inner_closure_set_var, inner_closure_set_body) =
          gen "set_of_closures" (Set_of_closures ({
            function_decls =
              {function_decls with funs = Variable.Map.singleton inner_fn_id final_fn};
            free_vars = inner_free_closure_var;
            specialised_args = Variable.Map.empty;
          }))
        in
        let fn_binding =
          rebind inner_closure_set_body (Let (
            Immutable,
            inner_closure_id,
            Project_closure ({
              set_of_closures = inner_closure_set_var;
              closure_id = Closure_id.wrap inner_fn_id;
            }),
            apply_inner))
        in
        let outer_free_fn_variables =
          fn.free_variables
          |> List.fold_right Variable.Set.remove fn.params
          |> List.fold_right Variable.Set.add wrapper_params
        in
        let new_fn = {
          fn with
          body = fn_binding;
          params = wrapper_params;
          free_variables = outer_free_fn_variables;
          stub = true}
        in
        let result =
          Set_of_closures
            {closure_set with
             function_decls =
               {function_decls with
                funs = Variable.Map.singleton fn_id new_fn}};
        in
        plam result;
        result
      end
      end

      (* (\* Update return sites in the closure if eligible *\)
       * let (fn_id, fn) = Variable.Map.choose function_decls.funs in
       * let (can_unbox, num_returns, return_map) = check_can_unbox fn in
       * if (not can_unbox) then flam else
       *
       * let fn = {fn with body = (unbox_fn fn num_returns); return_arity = num_returns} in
       *
       * let mkvar = Variable.create ~current_compilation_unit:function_decls.compilation_unit in
       * let mkvar_suffix v s = mkvar ((Variable.unique_name v) ^ s) in
       *
       * let unboxed_return_id = mkvar_suffix fn_id "_unboxed_return" in
       * let tag_var = mkvar_suffix fn_id "_tag" in
       * let result_vars =
       *   let rec builder = function
       *     | 0 -> []
       *     | n -> ("_result" ^ (string_of_int (n - 1))) :: (builder (n - 1)) in
       *   List.map (mkvar_suffix fn_id) (List.rev (builder num_returns)) in
       *
       * (\* Construct new wrapper function piece-by-piece *\)
       * let switch =
       *   let tags = List.map (fun (tag, _) -> tag) (Int.Map.bindings return_map) in
       *   let mkblock tag =
       *     let return_arity = Int.Map.find tag return_map in
       *     (tag, Fprim(
       *       Pmakeblock(tag, Immutable),
       *       (result_vars
       *        |> List.mapi (fun i x -> (i, x))
       *        |> List.filter (fun (i, _) -> i < return_arity)
       *        |> List.map (fun v -> Fvar(snd v, Expr_id.create()))),
       *       Debuginfo.none,
       *       Expr_id.create())) in
       *   Fswitch(
       *     Fvar(tag_var, Expr_id.create()),
       *     {
       *       numconsts = Int.Set.of_list tags;
       *       consts = List.map mkblock tags;
       *       numblocks = Int.Set.empty;
       *       blocks = [];
       *       failaction = None;
       *     },
       *     Expr_id.create()) in
       *
       * let ifthen =
       *   Fprim(
       *     Pisblock,
       *     [Fprim(
       *        Pintcomp(Cneq),
       *        [Fvar(tag_var, Expr_id.create());
       *         Fconst(Fconst_base(Const_int(10)), Expr_id.create())],
       *        Debuginfo.none,
       *        Expr_id.create());
       *      switch;
       *      Fvar(List.nth result_vars 0, Expr_id.create())
       *      ],
       *     Debuginfo.none,
       *     Expr_id.create()) in
       *
       * let field_bindings =
       *   List.fold_left
       *     (fun acc (index, result_var) ->
       *        Flet(
       *          Immutable,
       *          result_var,
       *          Fprim(Pgetblock_noheap(index),
       *                [Fvar(unboxed_return_id, Expr_id.create())],
       *                Debuginfo.none,
       *                Expr_id.create()),
       *          acc,
       *          Expr_id.create()))
       *     ifthen
       *     (List.mapi (fun i x -> (i, x)) (tag_var :: result_vars)) in
       *
       * let wrapper_params = List.map (fun id -> mkvar_suffix id "_wrapper") fn.params in
       * let inner_closure_id = mkvar_suffix fn_id "_multireturn" in
       * let inner_fn_id = mkvar_suffix fn_id "_unboxed" in
       * let apply_inner =
       *   Flet(
       *     Immutable,
       *     unboxed_return_id,
       *     Fapply({
       *       func = Fvar(inner_closure_id, Expr_id.create());
       *       args = List.map (fun v -> Fvar(v, Expr_id.create())) wrapper_params;
       *       kind = Direct(Closure_id.wrap inner_fn_id);
       *       dbg = Debuginfo.none;
       *       return_arity = num_returns + 1;
       *     }, Expr_id.create()),
       *     field_bindings,
       *     Expr_id.create()) in
       *
       * (\* List of free variables in the original closure of the form
       *    (original key, original value, new temporary key) *\)
       * let new_free_closure_var =
       *   List.map
       *     (fun (key, value) -> (key, value, mkvar "tmp"))
       *     (Variable.Map.bindings free_vars) in
       *
       * let inner_free_closure_var =
       *   List.fold_left
       *     (fun map (value, _, key) ->
       *        Variable.Map.add key (Fvar(value, Expr_id.create())) map)
       *     Variable.Map.empty
       *     new_free_closure_var in
       *
       * let inner_free_fn_var =
       *   fn.free_variables
       *   |> List.fold_right
       *        Variable.Set.remove
       *        (List.map (fun (k, _, _) -> k) new_free_closure_var)
       *   |> List.fold_right
       *        Variable.Set.add
       *        (List.map (fun (_ ,_, v) -> v) new_free_closure_var) in
       *
       * let final_fn =
       *   let reverse_map =
       *     List.fold_left
       *       (fun map (key, _, value) -> Variable.Map.add key value map)
       *       Variable.Map.empty
       *       new_free_closure_var in
       *   let body = Flambdaiter.map (function
       *     | Fvar(id, d) as fv ->
       *       begin try
       *         let id' = Variable.Map.find id reverse_map in
       *         Fvar(id', d)
       *       with Not_found -> fv end
       *     | e -> e)
       *     fn.body in
       *   {fn with body; free_variables = inner_free_fn_var;
       *            return_arity = num_returns + 1} in
       *
       * let fn_binding =
       *   Flet(
       *     Immutable,
       *     inner_closure_id,
       *     Fselect_closure({
       *       closure with set_of_closures = Fset_of_closures({
       *         function_decls = {function_decls with funs = Variable.Map.singleton inner_fn_id final_fn};
       *         free_vars = inner_free_closure_var;
       *         specialised_args = Variable.Map.empty;
       *       }, dset);
       *       closure_id = Closure_id.wrap inner_fn_id},
       *     Expr_id.create()),
       *     apply_inner,
       *     Expr_id.create()) in
       *
       * let outer_free_fn_variables =
       *   fn.free_variables
       *   |> List.fold_right Variable.Set.remove fn.params
       *   |> List.fold_right Variable.Set.add wrapper_params in
       *
       * let new_fn = {
       *   body = fn_binding;
       *   params = wrapper_params;
       *   free_variables = outer_free_fn_variables;
       *   return_arity = 1;
       *   stub = true; (\* We want our wrapper to always get inlined *\)
       *   dbg = Debuginfo.none} in
       *
       * Fselect_closure({
       *   set_of_closures = Fset_of_closures({
       *     function_decls = {
       *       set_of_closures_id = Set_of_closures_id.create function_decls.compilation_unit;
       *       funs = Variable.Map.singleton fn_id new_fn;
       *       compilation_unit = function_decls.compilation_unit;
       *     };
       *     free_vars;
       *     specialised_args;
       *   }, Expr_id.create());
       *   closure_id = Closure_id.wrap fn_id;
       *   relative_to = None;
       * }, closure_expr_id) *)

   | flam -> flam)
    tree

let duplicate tree =
  tree
  (* let module Sexn = Static_exception in
   * let var_map = ref Variable.Map.empty in
   * let exn_map = ref Sexn.Map.empty in
   * let rename var =
   *   let var' =
   *     Variable.rename
   *       ~current_compilation_unit:(Variable.get_compilation_unit var)
   *       ~append:"_dup"
   *       var in
   *   var_map := Variable.Map.add var var' !var_map in
   * Flambdaiter.iter (function
   *   | Flet(_, var, _, _, _) -> rename var
   *   | Fletrec(l, _, _) ->
   *     List.iter (fun (var, _) -> rename var) l
   *   | Fset_of_closures({function_decls}, _) ->
   *     Variable.Map.iter
   *       (fun var {params} -> rename var; List.iter rename params)
   *       function_decls.funs
   *   | Fstaticcatch(exn, _, _, _, _) ->
   *     exn_map := Sexn.Map.add exn (Sexn.create()) !exn_map
   *   | _ -> ())
   *   tree;
   * let lookup_var var =
   *   try Variable.Map.find var !var_map with Not_found -> var in
   * let lookup_exn exn =
   *   try Sexn.Map.find exn !exn_map with Not_found -> exn in
   * let tree =
   *   Flambdaiter.map (function
   *     | Flet(a, var, b, c, d) ->
   *       Flet(a, lookup_var var, b, c, d)
   *     | Fletrec(l, a, b) ->
   *       Fletrec(List.map (fun (var, t) -> (lookup_var var, t)) l, a, b)
   *     | Fset_of_closures({function_decls} as fset, d) ->
   *       let funs =
   *         Variable.Map.fold
   *           (fun k ({params; free_variables} as decl) map ->
   *              let params = List.map lookup_var params in
   *              let free_variables = Variable.Set.fold (fun v set ->
   *                Variable.Set.add (lookup_var v) set)
   *                free_variables
   *                Variable.Set.empty in
   *              Variable.Map.add (lookup_var k) {decl with params; free_variables} map)
   *           function_decls.funs
   *           Variable.Map.empty in
   *       Fset_of_closures({fset with function_decls = {function_decls with funs}}, d)
   *     | Fselect_closure({closure_id} as fsel, d) ->
   *       let closure_id = closure_id |> Closure_id.unwrap |> lookup_var |> Closure_id.wrap in
   *       Fselect_closure({fsel with closure_id}, d)
   *     | Fstaticcatch(exn, a, b, c, d) ->
   *       Fstaticcatch(lookup_exn exn, a, b, c, d)
   *     | Fstaticraise(exn, a, b) ->
   *       Fstaticraise(lookup_exn exn, a, b)
   *     | e -> e)
   *     tree in
   * Alpha_renaming.substitution !var_map tree *)

let lift_ifs tree =
  Flambda_iterators.map (function
    | Let (Immutable, var, Prim(Pisblock, [cond; thn; els], _), body) ->
      let qq = If_then_else(
        cond,
        Let (Immutable, var, Expr (Var thn), body),
        duplicate (Let (Immutable, var, Expr (Var els), body)))
      in Flambda_printers.flambda Format.std_formatter body; qq

    | e -> e)
    (fun x -> x)
    tree
