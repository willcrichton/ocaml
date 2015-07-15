open Ext_types
open Flambda

(* let plam flam =
 *   if !Clflags.dump_flambda then Printflambda.flambda Format.std_formatter flam else () *)

let check_can_unbox ({body; return_arity} : 'a function_declaration) =
  let fail_return = (false, 0, Int.Map.empty) in
  if return_arity <> 1 then fail_return else
  let unbox_return (can_unbox, num_returns, map) flam = match flam with
    | Fprim(Pmakeblock(tag, Immutable), arg, _, _) ->
      (* 9 is an arbitrary maximum number of registers, see Proc.loc_results *)
      let arity = List.length arg in
      if arity > 9 || arity = 0 then (fail_return, flam)
      else ((can_unbox, arity, Int.Map.add tag arity map), flam)
    | Fstaticraise _ | Fconst(Fconst_pointer _, _) -> ((can_unbox, num_returns, map), flam)
    | _ -> (fail_return, flam) in
  fst (Flambdaiter.fold_return_sites unbox_return (true, 1, Int.Map.empty) body)

let no_arg_variant = 10 (* TODO(wcrichton): appropriate value for this? *)
let dummy_value = 1337

let unbox_fn ({body} : 'a function_declaration) num_returns =
  let int_to_flam n = Fconst(Fconst_base(Const_int(n)), Expr_id.create()) in
  let rec generator = function
      0 -> [] | n -> (int_to_flam dummy_value) :: generator (n - 1) in
  let unbox_return () = function
    | Fprim(Pmakeblock(tag, Immutable), arg, dbg, attr) ->
      let len = num_returns - (List.length arg) in
      ((), Fprim(
         Pmakeblock_noheap,
         ((int_to_flam tag) :: arg) @ (generator len),
         dbg,
         attr))
    | Fconst(Fconst_pointer n, attr)  ->
      let len = num_returns - 1 in
      ((), Fprim(
         Pmakeblock_noheap,
         (int_to_flam no_arg_variant) :: (int_to_flam n) :: (generator len),
         Debuginfo.none,
         attr))
    | Fstaticraise _ as e -> ((), e)
    | _ -> Misc.fatal_error "Unboxed invalid return site" in
  let (_, body) = Flambdaiter.fold_return_sites unbox_return () body in
  body

let unbox_returns tree =
  Flambdaiter.map (function
    | Fselect_closure(
      {set_of_closures =
         Fset_of_closures({function_decls; free_vars; specialised_args}, dset)
      } as closure,
      closure_expr_id) as flam ->
      if not (!Clflags.dump_flambda) ||
        Variable.Map.cardinal function_decls.funs <> 1
      then flam else

      (* Update return sites in the closure if eligible *)
      let (fn_id, fn) = Variable.Map.choose function_decls.funs in
      let (can_unbox, num_returns, return_map) = check_can_unbox fn in
      if (not can_unbox) then flam else

      let fn = {fn with body = (unbox_fn fn num_returns); return_arity = num_returns} in

      let mkvar = Variable.create ~current_compilation_unit:function_decls.compilation_unit in
      let mkvar_suffix v s = mkvar ((Variable.unique_name v) ^ s) in

      let unboxed_return_id = mkvar_suffix fn_id "_unboxed_return" in
      let tag_var = mkvar_suffix fn_id "_tag" in
      let result_vars =
        let rec builder = function
          | 0 -> []
          | n -> ("_result" ^ (string_of_int (n - 1))) :: (builder (n - 1)) in
        List.map (mkvar_suffix fn_id) (List.rev (builder num_returns)) in

      (* Construct new wrapper function piece-by-piece *)
      let switch =
        let tags = List.map (fun (tag, _) -> tag) (Int.Map.bindings return_map) in
        let mkblock tag =
          let return_arity = Int.Map.find tag return_map in
          (tag, Fprim(
            Pmakeblock(tag, Immutable),
            (result_vars
             |> List.mapi (fun i x -> (i, x))
             |> List.filter (fun (i, _) -> i < return_arity)
             |> List.map (fun v -> Fvar(snd v, Expr_id.create()))),
            Debuginfo.none,
            Expr_id.create())) in
        Fswitch(
          Fvar(tag_var, Expr_id.create()),
          {
            numconsts = Int.Set.of_list tags;
            consts = List.map mkblock tags;
            numblocks = Int.Set.empty;
            blocks = [];
            failaction = None;
          },
          Expr_id.create()) in

      let ifthen =
        Fprim(
          Pisblock,
          [Fprim(
             Pintcomp(Cneq),
             [Fvar(tag_var, Expr_id.create());
              Fconst(Fconst_base(Const_int(10)), Expr_id.create())],
             Debuginfo.none,
             Expr_id.create());
           switch;
           Fvar(List.nth result_vars 0, Expr_id.create())
           ],
          Debuginfo.none,
          Expr_id.create()) in

      let field_bindings =
        List.fold_left
          (fun acc (index, result_var) ->
             Flet(
               Immutable,
               result_var,
               Fprim(Pgetblock_noheap(index),
                     [Fvar(unboxed_return_id, Expr_id.create())],
                     Debuginfo.none,
                     Expr_id.create()),
               acc,
               Expr_id.create()))
          ifthen
          (List.mapi (fun i x -> (i, x)) (tag_var :: result_vars)) in

      let wrapper_params = List.map (fun id -> mkvar_suffix id "_wrapper") fn.params in
      let inner_closure_id = mkvar_suffix fn_id "_multireturn" in
      let inner_fn_id = mkvar_suffix fn_id "_unboxed" in
      let apply_inner =
        Flet(
          Immutable,
          unboxed_return_id,
          Fapply({
            func = Fvar(inner_closure_id, Expr_id.create());
            args = List.map (fun v -> Fvar(v, Expr_id.create())) wrapper_params;
            kind = Direct(Closure_id.wrap inner_fn_id);
            dbg = Debuginfo.none;
            return_arity = num_returns + 1;
          }, Expr_id.create()),
          field_bindings,
          Expr_id.create()) in

      (* List of free variables in the original closure of the form
         (original key, original value, new temporary key) *)
      let new_free_closure_var =
        List.map
          (fun (key, value) -> (key, value, mkvar "tmp"))
          (Variable.Map.bindings free_vars) in

      let inner_free_closure_var =
        List.fold_left
          (fun map (value, _, key) ->
             Variable.Map.add key (Fvar(value, Expr_id.create())) map)
          Variable.Map.empty
          new_free_closure_var in

      let inner_free_fn_var =
        fn.free_variables
        |> List.fold_right
             Variable.Set.remove
             (List.map (fun (k, _, _) -> k) new_free_closure_var)
        |> List.fold_right
             Variable.Set.add
             (List.map (fun (_ ,_, v) -> v) new_free_closure_var) in

      let final_fn =
        let reverse_map =
          List.fold_left
            (fun map (key, _, value) -> Variable.Map.add key value map)
            Variable.Map.empty
            new_free_closure_var in
        let body = Flambdaiter.map (function
          | Fvar(id, d) as fv ->
            begin try
              let id' = Variable.Map.find id reverse_map in
              Fvar(id', d)
            with Not_found -> fv end
          | e -> e)
          fn.body in
        {fn with body; free_variables = inner_free_fn_var;
                 return_arity = num_returns + 1} in

      let fn_binding =
        Flet(
          Immutable,
          inner_closure_id,
          Fselect_closure({
            closure with set_of_closures = Fset_of_closures({
              function_decls = {function_decls with funs = Variable.Map.singleton inner_fn_id final_fn};
              free_vars = inner_free_closure_var;
              specialised_args = Variable.Map.empty;
            }, dset);
            closure_id = Closure_id.wrap inner_fn_id},
          Expr_id.create()),
          apply_inner,
          Expr_id.create()) in

      let outer_free_fn_variables =
        fn.free_variables
        |> List.fold_right Variable.Set.remove fn.params
        |> List.fold_right Variable.Set.add wrapper_params in

      let new_fn = {
        body = fn_binding;
        params = wrapper_params;
        free_variables = outer_free_fn_variables;
        return_arity = 1;
        stub = true; (* We want our wrapper to always get inlined *)
        dbg = Debuginfo.none} in

      Fselect_closure({
        set_of_closures = Fset_of_closures({
          function_decls = {
            set_of_closures_id = Set_of_closures_id.create function_decls.compilation_unit;
            funs = Variable.Map.singleton fn_id new_fn;
            compilation_unit = function_decls.compilation_unit;
          };
          free_vars;
          specialised_args;
        }, Expr_id.create());
        closure_id = Closure_id.wrap fn_id;
        relative_to = None;
      }, closure_expr_id)

   | flam -> flam)
    tree

let duplicate tree =
  let module Sexn = Static_exception in
  let var_map = ref Variable.Map.empty in
  let exn_map = ref Sexn.Map.empty in
  let rename var =
    let var' =
      Variable.rename
        ~current_compilation_unit:(Variable.get_compilation_unit var)
        ~append:"_dup"
        var in
    var_map := Variable.Map.add var var' !var_map in
  Flambdaiter.iter (function
    | Flet(_, var, _, _, _) -> rename var
    | Fletrec(l, _, _) ->
      List.iter (fun (var, _) -> rename var) l
    | Fset_of_closures({function_decls}, _) ->
      Variable.Map.iter
        (fun var {params} -> rename var; List.iter rename params)
        function_decls.funs
    | Fstaticcatch(exn, _, _, _, _) ->
      exn_map := Sexn.Map.add exn (Sexn.create()) !exn_map
    | _ -> ())
    tree;
  let lookup_var var =
    try Variable.Map.find var !var_map with Not_found -> var in
  let lookup_exn exn =
    try Sexn.Map.find exn !exn_map with Not_found -> exn in
  let tree =
    Flambdaiter.map (function
      | Flet(a, var, b, c, d) ->
        Flet(a, lookup_var var, b, c, d)
      | Fletrec(l, a, b) ->
        Fletrec(List.map (fun (var, t) -> (lookup_var var, t)) l, a, b)
      | Fset_of_closures({function_decls} as fset, d) ->
        let funs =
          Variable.Map.fold
            (fun k ({params; free_variables} as decl) map ->
               let params = List.map lookup_var params in
               let free_variables = Variable.Set.fold (fun v set ->
                 Variable.Set.add (lookup_var v) set)
                 free_variables
                 Variable.Set.empty in
               Variable.Map.add (lookup_var k) {decl with params; free_variables} map)
            function_decls.funs
            Variable.Map.empty in
        Fset_of_closures({fset with function_decls = {function_decls with funs}}, d)
      | Fselect_closure({closure_id} as fsel, d) ->
        let closure_id = closure_id |> Closure_id.unwrap |> lookup_var |> Closure_id.wrap in
        Fselect_closure({fsel with closure_id}, d)
      | Fstaticcatch(exn, a, b, c, d) ->
        Fstaticcatch(lookup_exn exn, a, b, c, d)
      | Fstaticraise(exn, a, b) ->
        Fstaticraise(lookup_exn exn, a, b)
      | e -> e)
      tree in
  Alpha_renaming.substitution !var_map tree

let lift_ifs tree =
  Flambdaiter.map (function
    | Flet(Immutable, var, Fprim(Pisblock, [cond; thn; els], _, _), body, annot) ->
      Fifthenelse(
        cond,
        Flet(Immutable, var, thn, body, annot),
        duplicate (Flet(Immutable, var, els, body, annot)),
        Expr_id.create())
    | e -> e)
    tree
