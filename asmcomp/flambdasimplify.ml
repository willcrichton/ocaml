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

open Ext_types
open Abstract_identifiers

module A = Simple_value_approx
module C = Inlining_cost

external swap16 : int -> int = "%bswap16"
external swap32 : int32 -> int32 = "%bswap_int32"
external swap64 : int64 -> int64 = "%bswap_int64"
external swapnative : nativeint -> nativeint = "%bswap_native"

(* CR mshinwell for pchambart: add comment. *)
let lift_lets tree =
  let rec aux (expr : _ Flambda.t) : _ Flambda.t =
    match expr with
    | Fsequence(Flet(str, v, def, body, d1), seq, dseq) ->
        Flet(str, v, def, Fsequence( aux body, seq, dseq), d1)
    | Flet(str1, v1, Flet(str2, v2, def2, body2, d2), body1, d1) ->
        Flet(str2, v2, def2, aux (Flet(str1, v1, body2, body1, d1)), d2)
    | e -> e
  in
  Flambdaiter.map aux tree

let lift_set_of_closures tree =
  let aux (expr : _ Flambda.t) : _ Flambda.t =
    match expr with
    | Fselect_closure({ set_of_closures = Fset_of_closures(set, dset) } as closure, d) ->
        let decl = Flambdautils.find_declaration closure.closure_id set.function_decls in
        if not decl.stub then
          expr
        else
          (* If the function is a stub, we create an intermediate let to allow
             eliminating it *)
          let set_of_closures_var =
            Variable.create
              ~current_compilation_unit:(Compilenv.current_unit ())
              "set_of_closures"
          in
          Flet(Immutable, set_of_closures_var,
               Fset_of_closures(set, dset),
               Fselect_closure({ closure with
                          set_of_closures =
                            Fvar (set_of_closures_var, Expr_id.create ()) },
                        d),
               Expr_id.create ())
    | e -> e
  in
  Flambdaiter.map aux tree

(** A variable in a closure can either be used by the closure itself
    or by an inlined version of the function. *)
let remove_unused_closure_variables tree =
  let used_variable_within_closure,
      used_closure_id =
    let used = ref Var_within_closure.Set.empty in
    let used_fun = ref Closure_id.Set.empty in
    let aux (expr : _ Flambda.t) =
      match expr with
      | Fvar_within_closure({ var; closure_id }, _) ->
          used := Var_within_closure.Set.add var !used;
          used_fun := Closure_id.Set.add closure_id !used_fun;
      | Fselect_closure({ closure_id; relative_to }, _) ->
          used_fun := Closure_id.Set.add closure_id !used_fun;
          begin match relative_to with
          | None -> ()
          | Some relative_to ->
              used_fun := Closure_id.Set.add relative_to !used_fun
          end
      | _ -> ()
    in
    Flambdaiter.iter aux tree;
    !used, !used_fun
  in
  let aux (expr : _ Flambda.t) : _ Flambda.t =
    match expr with
    | Fset_of_closures ({ function_decls; free_vars } as closure, eid) ->
       let all_free_var =
         Variable.Map.fold
           (fun _ { Flambda. free_variables } acc ->
             Variable.Set.union free_variables acc)
           function_decls.funs
           Variable.Set.empty in
       let free_vars =
         Variable.Map.filter (fun id expr ->
             Variable.Set.mem id all_free_var
             || Var_within_closure.Set.mem (Var_within_closure.wrap id)
               used_variable_within_closure
             || not (Effect_analysis.no_effects expr))
           free_vars in
       let function_decls =
         { function_decls with
           funs = Variable.Map.filter (fun fun_id _ ->
               Variable.Set.mem fun_id all_free_var
               || Closure_id.Set.mem (Closure_id.wrap fun_id)
                 used_closure_id)
               function_decls.funs } in
       Fset_of_closures ({ closure with free_vars; function_decls }, eid)
    | e -> e
  in
  Flambdaiter.map aux tree

(* CR mshinwell: rename [eid] and/or [annot] to be consistent *)
let const_int_expr expr n eid =
  if Effect_analysis.no_effects expr then
    let (new_expr, approx) = A.make_const_int n eid in
    new_expr, approx, C.Benefit.remove_code expr C.Benefit.zero
  else expr, A.value_int n, C.Benefit.zero
let const_char_expr expr c eid =
  if Effect_analysis.no_effects expr then
    let (new_expr, approx) = A.make_const_int (Char.code c) eid in
    new_expr, approx, C.Benefit.remove_code expr C.Benefit.zero
  else expr, A.value_int (Char.code c), C.Benefit.zero
let const_ptr_expr expr n eid =
  if Effect_analysis.no_effects expr then
    let (new_expr, approx) = A.make_const_ptr n eid in
    new_expr, approx, C.Benefit.remove_code expr C.Benefit.zero
  else expr, A.value_constptr n, C.Benefit.zero
let const_bool_expr expr b eid =
  const_ptr_expr expr (if b then 1 else 0) eid
let const_float_expr expr f eid =
  if Effect_analysis.no_effects expr then
    let (new_expr, approx) = A.make_const_float f eid in
    new_expr, approx, C.Benefit.remove_code expr C.Benefit.zero
  else expr, A.value_float f, C.Benefit.zero
let const_boxed_int_expr expr t i eid =
  if Effect_analysis.no_effects expr then
    let (new_expr, approx) = A.make_const_boxed_int t i eid in
    new_expr, approx, C.Benefit.remove_code expr C.Benefit.zero
  else expr, A.value_boxed_int t i, C.Benefit.zero

let const_comparison_expr expr cmp x y eid =
  let open Lambda in
  const_bool_expr expr
    (match cmp with
     | Ceq -> x = y
     | Cneq -> x <> y
     | Clt -> x < y
     | Cgt -> x > y
     | Cle -> x <= y
     | Cge -> x >= y)
    eid

module Simplify_sequential_logical_operator (G : sig
  val canonical_absorbing_element : int
  val is_absorbing_element : int -> bool
  val primitive : Lambda.primitive
end) = struct
  (* Simplify a sequential ("short-circuiting") operator using knowledge from
     (a) value approximations; and (b) side effect analysis. *)
  let sequential_op ~arg1 ~(arg1_approx : A.t) ~arg2 ~(arg2_approx : A.t)
        ~dbg ~annot =
    let arg1_no_effects = Effect_analysis.no_effects arg1 in
    let arg2_no_effects = Effect_analysis.no_effects arg2 in
    let arg2_annot = Flambdautils.data_at_toplevel_node arg2 in
    let module B = C.Benefit in
    let completely_eliminated () : _ Flambda.t * A.t * B.t =
      Fconst (Fconst_pointer G.canonical_absorbing_element, annot),
        A.value_constptr G.canonical_absorbing_element,
        B.remove_branch (B.remove_code arg1 (
          B.remove_code arg2 B.zero))
    in
    match arg1_approx.descr with
    | (Value_int n | Value_constptr n) when G.is_absorbing_element n ->
      if arg1_no_effects then
        completely_eliminated ()
      else
        arg1, arg1_approx, B.remove_branch (B.remove_code arg2 B.zero)
    | (Value_int _ | Value_constptr _) -> (* when not the absorbing element *)
      if arg1_no_effects then
        arg2, arg2_approx, B.remove_branch (B.remove_code arg1 B.zero)
      else
        begin match arg2_approx.descr with
        | (Value_int arg2_val | Value_constptr arg2_val)
            when arg2_no_effects ->
          Fsequence (arg1, Fconst (Fconst_pointer arg2_val, arg2_annot),
              annot), arg2_approx,
            B.remove_branch (B.remove_code arg2 B.zero)
        | _ ->
          Fsequence (arg1, arg2, annot), arg2_approx,
            B.remove_branch B.zero
        end
    | _ ->
      match arg2_approx.descr with
      | (Value_int n | Value_constptr n)
          when G.is_absorbing_element n ->
        begin match arg1_no_effects, arg2_no_effects with
        | true, true -> completely_eliminated ()
        | true, false (* we must run [arg1]: it might short-circuit [arg2] *)
        | false, false ->
          Fprim (G.primitive, [arg1; arg2], dbg, annot),
            A.value_constptr G.canonical_absorbing_element,
              B.zero
        | false, true ->
          Fsequence (arg1,
              Fconst (Fconst_pointer G.canonical_absorbing_element,
                arg2_annot), annot),
            A.value_constptr G.canonical_absorbing_element,
              B.remove_branch (B.remove_code arg2 B.zero)
        end
      | _ ->
        Fprim (G.primitive, [arg1; arg2], dbg, annot),
          A.value_unknown, B.zero
end

module Simplify_and = Simplify_sequential_logical_operator (struct
  let canonical_absorbing_element = 0
  let is_absorbing_element n = (n = 0)
  let primitive = Lambda.Psequand
end)
let sequential_and = Simplify_and.sequential_op

module Simplify_or = Simplify_sequential_logical_operator (struct
  let canonical_absorbing_element = 1
  let is_absorbing_element n = (n <> 0)
  let primitive = Lambda.Psequor
end)
let sequential_or = Simplify_or.sequential_op

(* Simplification of operations on boxed integers (nativeint, Int32, Int64). *)
module Simplify_boxed_integer_operator (I : sig
  type t
  val kind : Lambda.boxed_integer
  val zero : t
  val add : t -> t -> t
  val sub : t -> t -> t
  val mul : t -> t -> t
  val div : t -> t -> t
  val rem : t -> t -> t
  val logand : t -> t -> t
  val logor : t -> t -> t
  val logxor : t -> t -> t
  val shift_left : t -> int -> t
  val shift_right : t -> int -> t
  val shift_right_logical : t -> int -> t
  val to_int : t -> int
  val to_int32 : t -> Int32.t
  val to_int64 : t -> Int64.t
  val neg : t -> t
  val swap : t -> t
  val compare : t -> t -> int
end) = struct
  let simplify_unop (p : Lambda.primitive) (kind : I.t A.boxed_int)
        expr (n : I.t) eid =
    let eval op = const_boxed_int_expr expr kind (op n) eid in
    let eval_conv kind op = const_boxed_int_expr expr kind (op n) eid in
    let eval_unboxed op = const_int_expr expr (op n) eid in
    match p with
    | Pintofbint kind when kind = I.kind -> eval_unboxed I.to_int
    | Pcvtbint (kind, Pint32) when kind = I.kind -> eval_conv A.Int32 I.to_int32
    | Pcvtbint (kind, Pint64) when kind = I.kind -> eval_conv A.Int64 I.to_int64
    | Pnegbint kind when kind = I.kind -> eval I.neg
    | Pbbswap kind when kind = I.kind -> eval I.swap
    | _ -> expr, A.value_unknown, C.Benefit.zero

  let simplify_binop (p : Lambda.primitive) (kind : I.t A.boxed_int)
        expr (n1 : I.t) (n2 : I.t) eid =
    let eval op = const_boxed_int_expr expr kind (op n1 n2) eid in
    let non_zero n = (I.compare I.zero n) <> 0 in
    match p with
    | Paddbint kind when kind = I.kind -> eval I.add
    | Psubbint kind when kind = I.kind -> eval I.sub
    | Pmulbint kind when kind = I.kind -> eval I.mul
    | Pdivbint kind when kind = I.kind && non_zero n2 -> eval I.div
    | Pmodbint kind when kind = I.kind && non_zero n2 -> eval I.rem
    | Pandbint kind when kind = I.kind -> eval I.logand
    | Porbint kind when kind = I.kind -> eval I.logor
    | Pxorbint kind when kind = I.kind -> eval I.logxor
    | Pbintcomp (kind, c) when kind = I.kind ->
      const_comparison_expr expr c n1 n2 eid
    | _ -> expr, A.value_unknown, C.Benefit.zero

  let simplify_binop_int (p : Lambda.primitive) (kind : I.t A.boxed_int)
        expr (n1 : I.t) (n2 : int) eid =
    let eval op = const_boxed_int_expr expr kind (op n1 n2) eid in
    let precond = 0 <= n2 && n2 < 8 * Arch.size_int in
    match p with
    | Plslbint kind when kind = I.kind && precond -> eval I.shift_left
    | Plsrbint kind when kind = I.kind && precond -> eval I.shift_right_logical
    | Pasrbint kind when kind = I.kind && precond -> eval I.shift_right
    | _ -> expr, A.value_unknown, C.Benefit.zero
end

module Simplify_boxed_nativeint = Simplify_boxed_integer_operator (struct
  include Nativeint
  let to_int64 = Int64.of_nativeint
  let swap = swapnative
  let kind = Lambda.Pnativeint
end)

module Simplify_boxed_int32 = Simplify_boxed_integer_operator (struct
  include Int32
  let to_int32 i = i
  let to_int64 = Int64.of_int32
  let swap = swap32
  let kind = Lambda.Pint32
end)

module Simplify_boxed_int64 = Simplify_boxed_integer_operator (struct
  include Int64
  let to_int64 i = i
  let swap = swap64
  let kind = Lambda.Pint64
end)

let primitive (p : Lambda.primitive) (args, approxs) expr dbg
  : _ Flambda.t * A.t * Inlining_cost.Benefit.t =
  let fpc = !Clflags.float_const_prop in
  match p with
  | Pmakeblock(tag, Asttypes.Immutable) ->
    let tag = Simple_value_approx.Tag.create_exn tag in
    expr, A.value_block(tag, Array.of_list approxs), C.Benefit.zero
  | Pignore -> begin
      let eid = Flambdautils.data_at_toplevel_node expr in
      match args, A.descrs approxs with
      | [arg], [(Value_int 0 | Value_constptr 0)] ->
          const_ptr_expr arg 0 eid
      | _ ->
          const_ptr_expr expr 0 eid
    end
  | _ ->
    let eid = Flambdautils.data_at_toplevel_node expr in
    match A.descrs approxs with
    | [Value_int x] ->
      begin match p with
      | Pidentity -> const_int_expr expr x eid
      | Pnot -> const_bool_expr expr (x = 0) eid
      | Pnegint -> const_int_expr expr (-x) eid
      | Pbswap16 -> const_int_expr expr (swap16 x) eid
      | Poffsetint y -> const_int_expr expr (x + y) eid
      | Pfloatofint when fpc -> const_float_expr expr (float_of_int x) eid
      | Pbintofint Pnativeint ->
        const_boxed_int_expr expr Nativeint (Nativeint.of_int x) eid
      | Pbintofint Pint32 ->
        const_boxed_int_expr expr Int32 (Int32.of_int x) eid
      | Pbintofint Pint64 ->
        const_boxed_int_expr expr Int64 (Int64.of_int x) eid
      | _ -> expr, A.value_unknown, C.Benefit.zero
      end
    | [(Value_int x | Value_constptr x); (Value_int y | Value_constptr y)] ->
      let shift_precond = 0 <= y && y < 8 * Arch.size_int in
      begin match p with
      | Paddint -> const_int_expr expr (x + y) eid
      | Psubint -> const_int_expr expr (x - y) eid
      | Pmulint -> const_int_expr expr (x * y) eid
      | Pdivint when y <> 0 -> const_int_expr expr (x / y) eid
      | Pmodint when y <> 0 -> const_int_expr expr (x mod y) eid
      | Pandint -> const_int_expr expr (x land y) eid
      | Porint -> const_int_expr expr (x lor y) eid
      | Pxorint -> const_int_expr expr (x lxor y) eid
      | Plslint when shift_precond -> const_int_expr expr (x lsl y) eid
      | Plsrint when shift_precond -> const_int_expr expr (x lsr y) eid
      | Pasrint when shift_precond -> const_int_expr expr (x asr y) eid
      | Pintcomp cmp -> const_comparison_expr expr cmp x y eid
      | Pisout -> const_bool_expr expr (y > x || y < 0) eid
      (* [Psequand] and [Psequor] have special simplification rules, above. *)
      | _ -> expr, A.value_unknown, C.Benefit.zero
      end
    | [Value_constptr x] ->
      begin match p with
      | Pidentity -> const_ptr_expr expr x eid
      | Pnot -> const_bool_expr expr (x = 0) eid
      | Pisint -> const_bool_expr expr true eid
      | Poffsetint y -> const_ptr_expr expr (x + y) eid
      | Pctconst c ->
        begin match c with
        | Big_endian -> const_bool_expr expr Arch.big_endian eid
        | Word_size -> const_int_expr expr (8*Arch.size_int) eid
        | Int_size -> const_int_expr expr (8*Arch.size_int - 1) eid
        | Max_wosize ->
          (* CR mshinwell: this function should maybe not live here. *)
          const_int_expr expr ((1 lsl ((8*Arch.size_int) - 10)) - 1) eid
        | Ostype_unix -> const_bool_expr expr (Sys.os_type = "Unix") eid
        | Ostype_win32 -> const_bool_expr expr (Sys.os_type = "Win32") eid
        | Ostype_cygwin -> const_bool_expr expr (Sys.os_type = "Cygwin") eid
        end
      | _ -> expr, A.value_unknown, C.Benefit.zero
      end
    | [Value_float x] when fpc ->
      begin match p with
      | Pintoffloat -> const_int_expr expr (int_of_float x) eid
      | Pnegfloat -> const_float_expr expr (-. x) eid
      | Pabsfloat -> const_float_expr expr (abs_float x) eid
      | _ -> expr, A.value_unknown, C.Benefit.zero
      end
    | [Value_float n1; Value_float n2] when fpc ->
      begin match p with
      | Paddfloat -> const_float_expr expr (n1 +. n2) eid
      | Psubfloat -> const_float_expr expr (n1 -. n2) eid
      | Pmulfloat -> const_float_expr expr (n1 *. n2) eid
      | Pdivfloat -> const_float_expr expr (n1 /. n2) eid
      | Pfloatcomp c  -> const_comparison_expr expr c n1 n2 eid
      | _ -> expr, A.value_unknown, C.Benefit.zero
      end
    | [A.Value_boxed_int(A.Nativeint, n)] ->
      Simplify_boxed_nativeint.simplify_unop p Nativeint expr n eid
    | [A.Value_boxed_int(A.Int32, n)] ->
      Simplify_boxed_int32.simplify_unop p Int32 expr n eid
    | [A.Value_boxed_int(A.Int64, n)] ->
      Simplify_boxed_int64.simplify_unop p Int64 expr n eid
    | [A.Value_boxed_int(A.Nativeint, n1);
       A.Value_boxed_int(A.Nativeint, n2)] ->
      Simplify_boxed_nativeint.simplify_binop p Nativeint expr n1 n2 eid
    | [A.Value_boxed_int(A.Int32, n1); A.Value_boxed_int(A.Int32, n2)] ->
      Simplify_boxed_int32.simplify_binop p Int32 expr n1 n2 eid
    | [A.Value_boxed_int(A.Int64, n1); A.Value_boxed_int(A.Int64, n2)] ->
      Simplify_boxed_int64.simplify_binop p Int64 expr n1 n2 eid
    | [A.Value_boxed_int(A.Nativeint, n1); Value_int n2] ->
      Simplify_boxed_nativeint.simplify_binop_int p Nativeint expr n1 n2 eid
    | [A.Value_boxed_int(A.Int32, n1); Value_int n2] ->
      Simplify_boxed_int32.simplify_binop_int p Int32 expr n1 n2 eid
    | [A.Value_boxed_int(A.Int64, n1); Value_int n2] ->
      Simplify_boxed_int64.simplify_binop_int p Int64 expr n1 n2 eid
    | [Value_block _] when p = Pisint -> const_bool_expr expr false eid
    | [Value_string { size }] when p = Pstringlength ->
        const_int_expr expr size eid
    | [Value_string { size; contents = Some s };
       (Value_int x | Value_constptr x)] when x >= 0 && x < size ->
        begin match p with
        | Pstringrefu
        | Pstringrefs ->
            const_char_expr expr s.[x] eid
        | _ -> expr, A.value_unknown, C.Benefit.zero
        end
    | [Value_string { size; contents = None };
       (Value_int x | Value_constptr x)]
      when x >= 0 && x < size && p = Pstringrefs ->
        Flambda.Fprim(Pstringrefu, args, dbg, eid),
        A.value_unknown,
        C.Benefit.zero (* we improved it, but there is no way to account for that *)
    | _ -> expr, A.value_unknown, C.Benefit.zero

let rename_var var =
  Variable.rename ~current_compilation_unit:(Compilenv.current_unit ()) var
let nid () = Expr_id.create ()

let remove_params unused (fun_decl: _ Flambda.function_declaration) =
  let unused_params, used_params = List.partition (fun v -> Variable.Set.mem v unused) fun_decl.params in
  let unused_params = List.filter (fun v ->
      Variable.Set.mem v fun_decl.free_variables) unused_params in
  let body = List.fold_left (fun body var ->
      Flambda.Flet(Immutable,
           var,
           Fconst(Fconst_pointer 0, nid ()),
           body,
           nid ()))
      fun_decl.body
      unused_params
  in
  let free_variables =
    Variable.Set.filter (fun var -> not (Variable.Set.mem var unused))
      fun_decl.free_variables
  in
  { fun_decl with
    params = used_params;
    free_variables;
    body }

let make_stub unused var (fun_decl : _ Flambda.function_declaration) =
  let renamed = rename_var var in
  let args' = List.map (fun var -> var, rename_var var) fun_decl.params in
  let args =
    List.map (fun (_, var) -> Flambda.Fvar(var, nid ()))
      (List.filter (fun (var, _) -> not (Variable.Set.mem var unused)) args')
  in
  let kind = Flambda.Direct (Closure_id.wrap renamed) in
  let dbg = fun_decl.dbg in
  let body : _ Flambda.t =
    Fapply(
      { func = Fvar(renamed, nid ());
        args;
        kind;
        dbg;
        return_arity = 1 },
      nid ())
  in
  let free_variables =
    List.fold_left
      (fun set (_, renamed_arg) -> Variable.Set.add renamed_arg set)
      (Variable.Set.singleton renamed)
      args'
  in
  let decl : _ Flambda.function_declaration = {
    params = List.map snd args';
    body;
    free_variables;
    stub = true;
    return_arity = 1;
    dbg = fun_decl.dbg;
  }
  in
  decl, renamed

let separate_unused_arguments (set_of_closures : _ Flambda.set_of_closures) =
  let decl = set_of_closures.function_decls in
  let unused = Invariant_params.unused_arguments decl in
  let non_stub_arguments =
    Variable.Map.fold (fun _ (decl : _ Flambda.function_declaration) acc ->
        if decl.stub then
          acc
        else
          Variable.Set.union acc (Variable.Set.of_list decl.Flambda.params))
      decl.funs Variable.Set.empty
  in
  let unused = Variable.Set.inter non_stub_arguments unused in
  if Variable.Set.is_empty unused
  then None
  else begin
    let funs =
      Variable.Map.fold (fun fun_id (fun_decl : _ Flambda.function_declaration) acc ->
          if List.exists (fun v -> Variable.Set.mem v unused) fun_decl.params
          then begin
            let stub, renamed_fun_id = make_stub unused fun_id fun_decl in
            let cleaned = remove_params unused fun_decl in
            Variable.Map.add fun_id stub
              (Variable.Map.add renamed_fun_id cleaned acc)
          end
          else
            Variable.Map.add fun_id fun_decl acc
        )
        decl.funs Variable.Map.empty
    in
    let specialised_args =
      Variable.Map.filter (fun param _ -> not (Variable.Set.mem param unused))
        set_of_closures.specialised_args
    in
    Some
      { set_of_closures with
        function_decls = { decl with funs };
        specialised_args; }
  end

(* Spliting is not always beneficial. For instance when a function
   is only indirectly called, suppressing unused arguments does not
   benefit, and introduce an useless intermediate call *)
let candidate_for_spliting_for_unused_arguments
    (fun_decl : _ Flambda.function_declarations) =
  let no_recursive_functions =
    Variable.Set.is_empty
      (Flambdautils.recursive_functions fun_decl)
  in
  let number_of_non_stub_functions =
    Variable.Map.cardinal
      (Variable.Map.filter (fun _ { Flambda.stub } -> not stub)
         fun_decl.funs)
  in
  (not no_recursive_functions) ||
  (number_of_non_stub_functions > 1)

let separate_unused_arguments_in_closures tree =
  let aux (expr : _ Flambda.t) : _ Flambda.t =
    match expr with
    | Fset_of_closures (set_of_closures, eid) -> begin
        if candidate_for_spliting_for_unused_arguments
            set_of_closures.function_decls then
          match separate_unused_arguments set_of_closures with
          | None -> expr
          | Some set_of_closures ->
              Fset_of_closures (set_of_closures, eid)
        else
          expr
      end
    | e -> e
  in
  Flambdaiter.map aux tree

let used_globals id tree =
  let used = ref Ext_types.Int.Set.empty in
  Flambdaiter.iter (function
      | Fprim(Pgetglobalfield(modul, pos), _, _, _) when Ident.same id modul ->
          used := Ext_types.Int.Set.add pos !used
      | _ -> ()) tree;
  !used

let remove_unused_globals tree =
  let id = Compilenv.current_unit_id () in
  let used = used_globals id tree in
  Flambdaiter.map (function
      | Fprim(Psetglobalfield(Not_exported, pos), arg, dbg, attr)
        when not (Ext_types.Int.Set.mem pos used) ->
          Fprim(Pignore, arg, dbg, attr)
      | e -> e)
    tree

let plam flam =
  if !Clflags.dump_flambda then Printflambda.flambda Format.std_formatter flam else ()

let check_can_unbox ({body; return_arity} : 'a Flambda.function_declaration) =
  let open Flambda in
  let fail_return = (false, 0, Int.Map.empty) in
  if return_arity <> 1 then fail_return else
  let unbox_return (can_unbox, num_returns, map) flam = match flam with
    | Fprim(Pmakeblock(tag, Immutable), arg, dbg, attr) ->
      (* 9 is an arbitrary maximum number of registers, see Proc.loc_results *)
      let arity = List.length arg in
      if arity > 9 || arity = 0 then (fail_return, flam)
      else ((can_unbox, arity, Int.Map.add tag arity map), flam)
    | Fstaticraise _ | Fconst(Fconst_pointer _, _) -> ((can_unbox, num_returns, map), flam)
    | _ -> (fail_return, flam) in
  fst (Flambdaiter.fold_return_sites unbox_return (true, 1, Int.Map.empty) body)

let no_arg_variant = 10 (* TODO(wcricton): appropriate value for this? *)
let dummy_value = 1337

let unbox_fn ({body} : 'a Flambda.function_declaration) num_returns =
  let open Flambda in
  let int_to_flam n = Fconst(Fconst_base(Const_int(n)), Expr_id.create()) in
  let rec generator = function 0 -> [] | n -> (int_to_flam dummy_value) :: generator (n - 1) in
  let unbox_return () = function
    | Fprim(Pmakeblock(tag, Immutable), arg, dbg, attr) ->
      let len = num_returns - (List.length arg) in
      ((), Fprim(Pmakeblock_noheap,
                 ((int_to_flam tag) :: arg) @ (generator len),
                 dbg,
                 attr))
    | Fconst(Fconst_pointer(n), attr)  ->
      let len = num_returns - 1 in
      ((), Fprim(Pmakeblock_noheap,
                 (int_to_flam no_arg_variant) :: (int_to_flam n) :: (generator len),
                 Debuginfo.none,
                 attr))
    | Fstaticraise _ as e -> ((), e)
    | e -> Misc.fatal_error "Unboxed invalid return site" in
  let (_, body) = Flambdaiter.fold_return_sites unbox_return () body in
  body

let unbox_returns tree =
  let open Flambda in
  Flambdaiter.map (function
    | Fselect_closure({set_of_closures =
                  Fset_of_closures({function_decls; free_vars; specialised_args}, dset)}
               as closure,
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
             |> List.filter (fun (i, x) -> i < return_arity)
             |> List.map (fun v -> Fvar(snd v, Expr_id.create()))),
            Debuginfo.none,
            Expr_id.create())) in
        let no_variant_case = Fvar(List.nth result_vars 0, Expr_id.create()) in
        Fswitch(
          Fvar(tag_var, Expr_id.create()),
          {
            numconsts = Int.Set.of_list (no_arg_variant :: tags);
            consts = (no_arg_variant, no_variant_case) :: (List.map mkblock tags);
            numblocks = Int.Set.empty;
            blocks = [];
            failaction = None;
          },
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
          switch
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
        List.fold_right
          Variable.Set.remove
          (List.map (fun (k, _, _) -> k) new_free_closure_var)
          fn.free_variables in
      let inner_free_fn_var =
        List.fold_right
          Variable.Set.add
          (List.map (fun (_ ,_, v) -> v) new_free_closure_var)
          inner_free_fn_var in

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
        {fn with body; free_variables = inner_free_fn_var; return_arity = num_returns + 1} in

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
        List.fold_right Variable.Set.remove fn.params fn.free_variables in
      let outer_free_fn_variables =
        List.fold_right Variable.Set.add wrapper_params outer_free_fn_variables in

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

