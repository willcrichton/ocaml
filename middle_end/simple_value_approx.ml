(**************************************************************************)
(*                                                                        *)
(*                                OCaml                                   *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*                  Mark Shinwell, Jane Street Europe                     *)
(*                                                                        *)
(*   Copyright 2015 Institut National de Recherche en Informatique et     *)
(*   en Automatique.  All rights reserved.  This file is distributed      *)
(*   under the terms of the Q Public License version 1.0.                 *)
(*                                                                        *)
(**************************************************************************)

type 'a boxed_int =
  | Int32 : int32 boxed_int
  | Int64 : int64 boxed_int
  | Nativeint : nativeint boxed_int

type value_string = {
  contents : string option; (* None if unknown or mutable *)
  size : int;
}

type descr =
  | Value_block of Tag.t * t array
  | Value_int of int
  | Value_constptr of int
  | Value_float of float
  | Value_boxed_int : 'a boxed_int * 'a -> descr
  | Value_set_of_closures of value_set_of_closures
  | Value_closure of value_closure
  | Value_string of value_string
  | Value_float_array of int (* size *)
  | Value_unknown
  | Value_bottom
  | Value_extern of Export_id.t
  | Value_symbol of Symbol.t
  | Value_unresolved of Symbol.t
  | Value_conditional of t * t

and value_closure =
  { closure_id : Closure_id.t;
    set_of_closures : value_set_of_closures;
    set_of_closures_var : Variable.t option;
  }

and value_set_of_closures =
  { function_decls : Expr_id.t Flambda.function_declarations;
    bound_var : t Var_within_closure.Map.t;
    unchanging_params : Variable.Set.t;
    specialised_args : Variable.Set.t;
    alpha_renaming :
      Alpha_renaming.Ids_and_bound_vars_of_closures.t;
  }

and t =
  { descr : descr;
    var : Variable.t option;
    symbol : Symbol.t option;
  }

let descr t = t.descr

let rec print_descr ppf = function
  | Value_int i -> Format.pp_print_int ppf i
  | Value_constptr i -> Format.fprintf ppf "%ia" i
  | Value_block (tag,fields) ->
    let p ppf fields =
      Array.iter (fun v -> Format.fprintf ppf "%a@ " print_approx v) fields in
    Format.fprintf ppf "[%i:@ @[<1>%a@]]" (Tag.to_int tag) p fields
  | Value_unknown -> Format.fprintf ppf "?"
  | Value_bottom -> Format.fprintf ppf "bottom"
  | Value_extern id -> Format.fprintf ppf "_%a_" Export_id.print id
  | Value_symbol sym -> Format.fprintf ppf "%a" Symbol.print sym
  | Value_closure { closure_id } ->
    Format.fprintf ppf "(fun:@ %a)" Closure_id.print closure_id
  | Value_set_of_closures { function_decls = { funs } } ->
    Format.fprintf ppf "(set_of_closures:@ %a)"
      (fun ppf -> Variable.Map.iter (fun id _ -> Variable.print ppf id)) funs
  | Value_unresolved sym ->
    Format.fprintf ppf "(unresolved %a)" Symbol.print sym
  | Value_float f -> Format.pp_print_float ppf f
  | Value_string { contents; size } -> begin
      match contents with
      | None ->
          Format.fprintf ppf "string %i" size
      | Some s ->
          let s =
            if size > 10
            then String.sub s 0 8 ^ "..."
            else s
          in
          Format.fprintf ppf "string %i %S" size s
    end
  | Value_float_array size ->
      Format.fprintf ppf "float_array %i" size
  | Value_boxed_int (t, i) -> begin
    match t with
    | Int32 -> Format.fprintf ppf "%li" i
    | Int64 -> Format.fprintf ppf "%Li" i
    | Nativeint -> Format.fprintf ppf "%ni" i
    end
  | Value_conditional (thn, els) ->
    Format.printf "(conditional @ %a %a)" print_descr thn.descr print_descr els.descr

and print_approx ppf { descr } = print_descr ppf descr

(** Smart constructors *)

let approx descr = { descr; var = None; symbol = None }

let value_unknown = approx Value_unknown
let value_int i = approx (Value_int i)
let value_constptr i = approx (Value_constptr i)
let value_float f = approx (Value_float f)
let value_boxed_int bi i = approx (Value_boxed_int (bi,i))
let value_closure c = approx (Value_closure c)
let value_set_of_closures c = approx (Value_set_of_closures c)
let value_block (t,b) = approx (Value_block (t,b))
let value_extern ex = approx (Value_extern ex)
let value_symbol sym = { (approx (Value_symbol sym)) with symbol = Some sym }
let value_bottom = approx Value_bottom
let value_unresolved sym = approx (Value_unresolved sym)
let value_conditional thn els = approx (Value_conditional (thn,els))

let value_string size contents = approx (Value_string {size; contents })
let value_float_array size = approx (Value_float_array size)

let make_const_int n eid : _ Flambda.t * t =
  Fconst(Fconst_base(Asttypes.Const_int n),eid), value_int n

let make_const_ptr n eid : _ Flambda.t * t =
  Fconst(Fconst_pointer n,eid), value_constptr n

let make_const_bool b eid : _ Flambda.t * t =
  make_const_ptr (if b then 1 else 0) eid

let make_const_float f eid : _ Flambda.t * t =
  Fconst(Fconst_float f,eid), value_float f

let make_const_boxed_int (type bi) (t:bi boxed_int) (i:bi) eid
      : _ Flambda.t * t =
  let c : Asttypes.constant =
    match t with
    | Int32 -> Const_int32 i
    | Int64 -> Const_int64 i
    | Nativeint -> Const_nativeint i
  in
  Fconst (Fconst_base c, eid), value_boxed_int t i

let const_approx (flam : Flambda.const) =
  match flam with
  | Fconst_base const ->
    begin match const with
    | Const_int i -> value_int i
    | Const_char c -> value_int (Char.code c)
    | Const_string (s,_) -> value_string (String.length s) None
    | Const_float s -> value_float (float_of_string s)
    | Const_int32 i -> value_boxed_int Int32 i
    | Const_int64 i -> value_boxed_int Int64 i
    | Const_nativeint i -> value_boxed_int Nativeint i
    end
  | Fconst_pointer i -> value_constptr i
  | Fconst_float f -> value_float f
  | Fconst_float_array a -> value_float_array (List.length a)
  | Fconst_immstring s -> value_string (String.length s) (Some s)

let check_constant_result (lam : _ Flambda.t) approx
      : _ Flambda.t * t =
  if Effect_analysis.no_effects lam then
    match approx.descr with
    | Value_int n ->
      make_const_int n (Flambdautils.data_at_toplevel_node lam)
    | Value_constptr n ->
      make_const_ptr n (Flambdautils.data_at_toplevel_node lam)
    | Value_float f ->
      make_const_float f (Flambdautils.data_at_toplevel_node lam)
    | Value_boxed_int (t,i) ->
      make_const_boxed_int t i (Flambdautils.data_at_toplevel_node lam)
    | Value_symbol sym ->
      Fsymbol (sym, Flambdautils.data_at_toplevel_node lam), approx
    | Value_string _ | Value_float_array _ | Value_conditional _
    | Value_block _ | Value_set_of_closures _ | Value_closure _
    | Value_unknown | Value_bottom | Value_extern _ | Value_unresolved _ ->
      lam, approx
  else
    lam, approx

let check_var_and_constant_result ~is_present_in_env lam approx =
  let res : _ Flambda.t =
    match approx.var with
    | Some var when is_present_in_env var ->
      Fvar(var, Flambdautils.data_at_toplevel_node lam)
    | _ ->
      match approx.symbol with
      | Some sym ->
          Fsymbol(sym, Flambdautils.data_at_toplevel_node lam)
      | None -> lam
  in
  check_constant_result res approx

let known t =
  match t.descr with
  | Value_unresolved _
  | Value_unknown -> false
  | Value_string _ | Value_float_array _ | Value_conditional _
  | Value_bottom | Value_block _ | Value_int _ | Value_constptr _
  | Value_set_of_closures _ | Value_closure _ | Value_extern _
  | Value_float _ | Value_boxed_int _ | Value_symbol _ -> true

let useful t =
  match t.descr with
  | Value_unresolved _ | Value_unknown | Value_bottom -> false
  | Value_string _ | Value_float_array _ | Value_conditional _
  | Value_block _ | Value_int _ | Value_constptr _ | Value_set_of_closures _
  | Value_float _ | Value_boxed_int _ | Value_closure _ | Value_extern _
  | Value_symbol _ -> true

let is_certainly_immutable t =
  match t.descr with
  | Value_string { contents = Some _ } | Value_conditional _
  | Value_block _ | Value_int _ | Value_constptr _ | Value_set_of_closures _
  | Value_float _ | Value_boxed_int _ | Value_closure _ -> true
  | Value_string { contents = None } | Value_float_array _
  | Value_unresolved _ | Value_unknown | Value_bottom -> false
  | Value_extern _ | Value_symbol _ -> assert false

let get_field i = function
  | [] | _ :: _ :: _ -> assert false
  | [{descr}] ->
    match descr with
    | Value_block (_tag, fields) ->
      if i >= 0 && i < Array.length fields
      then fields.(i)
      else value_unknown
    | Value_bottom
    | Value_int _ | Value_constptr _ ->
        (* Something seriously wrong is happening: either the user is doing something
           exceptionnaly unsafe, or it is an unreachable branch:
           We consider this is unreachable and mark the result as it *)
        value_bottom
    | Value_float_array _ ->
        (* float_arrays are immutable *)
        value_unknown
    | Value_string _ | Value_float _ | Value_boxed_int _  (* The user is doing something unsafe *)
    | Value_set_of_closures _ | Value_closure _
    (* This is used by CamlinternalMod... *)
    | Value_symbol _ | Value_extern _
      (* Should have been resolved *)
    | Value_unknown ->
        value_unknown
    | Value_unresolved sym ->
        (* We don't know anything, but we must remember that it comes
           from another compilation unit in case it contained a closure *)
      value_unresolved sym
    | Value_conditional _ ->
      value_unknown

let descrs approxs = List.map (fun v -> v.descr) approxs

let equal_boxed_int (type t1) (type t2)
    (bi1:t1 boxed_int) (i1:t1)
    (bi2:t2 boxed_int) (i2:t2) =
  match bi1, bi2 with
  | Int32, Int32 -> Int32.equal i1 i2
  | Int64, Int64 -> Int64.equal i1 i2
  | Nativeint, Nativeint -> Nativeint.equal i1 i2
  | _ -> false

(* Closures and set of closures descriptions cannot be merged.

   let f x =
     let g y -> x + y in
     g
   in
   let v =
     if ...
     then f 1
     else f 2
   in
   v 3

   The approximation for [f 1] and [f 2] could both contain the
   description of [g]. But if [f] where inlined, a new [g] would
   be created in each branch, leading to incompatible description.
   And we must never make the descrition for a function less
   precise that it used to be: its information are needed for
   rewriting [Fvar_within_closure] and [Fselect_closure] constructions
   in [Flambdainline.loop]
*)
let rec meet_descr d1 d2 = match d1, d2 with
  | Value_int i, Value_int j when i = j ->
      d1
  | Value_constptr i, Value_constptr j when i = j ->
      d1
  | Value_symbol s1, Value_symbol s2 when Symbol.equal s1 s2 ->
      d1
  | Value_extern e1, Value_extern e2 when Export_id.equal e1 e2 ->
      d1
  | Value_float i, Value_float j when i = j ->
      d1
  | Value_boxed_int (bi1, i1), Value_boxed_int (bi2, i2) when
      equal_boxed_int bi1 i1 bi2 i2 ->
      d1
  | Value_block (tag1, a1), Value_block (tag2, a2)
    when tag1 = tag2 && Array.length a1 = Array.length a2 ->
      Value_block (tag1, Array.mapi (fun i v -> meet v a2.(i)) a1)
  | _ -> Value_unknown

and meet a1 a2 =
  match a1, a2 with
  | { descr = Value_bottom }, a
  | a, { descr = Value_bottom } -> a
  | _ ->
      let var =
        match a1.var, a2.var with
        | None, _ | _, None -> None
        | Some v1, Some v2 ->
            if Variable.equal v1 v2
            then Some v1
            else None
      in
      let symbol =
        match a1.symbol, a2.symbol with
        | None, _ | _, None -> None
        | Some v1, Some v2 ->
            if Symbol.equal v1 v2
            then Some v1
            else None
      in
      { descr = meet_descr a1.descr a2.descr;
        var;
        symbol }
