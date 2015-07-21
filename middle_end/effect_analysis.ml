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

(* CR mshinwell: I made this match exhaustive, but we still need to
   double-check that the assignment for each primitive is correct. *)
let no_effects_prim (prim : Lambda.primitive) =
  match prim with
  | Pidentity
  | Pignore
  | Prevapply _
  | Pdirapply _
  | Ploc _
  | Pgetglobal _
  | Pgetglobalfield _
  | Pmakeblock _
  | Pfield _
  | Pgetblock_noheap _
  | Pmakeblock_noheap
  | Pisblock
  | Pfloatfield _
  | Plazyforce
  | Pccall { prim_name =
               ( "caml_format_float" | "caml_format_int" |
                 "caml_int32_format" | "caml_nativeint_format" |
                 "caml_int64_format" ) }
  | Pnot
  | Pnegint | Paddint | Psubint | Pmulint | Pdivint | Pmodint
  | Pandint | Porint | Pxorint
  | Plslint | Plsrint | Pasrint
  | Pintcomp _
  | Poffsetint _
  | Pintoffloat | Pfloatofint
  | Pnegfloat | Pabsfloat
  | Paddfloat | Psubfloat | Pmulfloat | Pdivfloat
  | Pfloatcomp _
  | Pstringlength
  | Pstringrefu
  | Pmakearray _
  | Parraylength _
  | Parrayrefu _
  | Pisint
  | Pisout
  | Pbittest
  | Pbintofint _
  | Pintofbint _
  | Pcvtbint _
  | Pnegbint _
  | Paddbint _
  | Psubbint _
  | Pmulbint _
  | Pdivbint _
  | Pmodbint _
  | Pandbint _
  | Porbint _
  | Pxorbint _
  | Plslbint _
  | Plsrbint _
  | Pasrbint _
  | Pbintcomp _
  | Pbigarrayref (true, _, _, _)
  | Pbigarraydim _
  | Pstring_load_16 true
  | Pstring_load_32 true
  | Pstring_load_64 true
  | Pbigstring_load_16 true
  | Pbigstring_load_32 true
  | Pbigstring_load_64 true
  | Pctconst _
  | Pbswap16
  | Pbbswap _
  | Pint_as_pointer -> true
  | Psetglobal _ | Psetfield _ | Psetfloatfield _ | Pduprecord _
  | Pccall _ | Praise _ | Poffsetref _ | Pstringsetu | Pstringsets
  | Parraysetu _ | Parraysets _ | Pbigarrayset _
  | Psetglobalfield _
  | Pstringrefs | Parrayrefs _ | Pbigarrayref (false, _, _, _)
  | Pstring_load_16 false | Pstring_load_32 false | Pstring_load_64 false
  | Pbigstring_load_16 false | Pbigstring_load_32 false
  | Pbigstring_load_64 false
  | Pstring_set_16 _ | Pstring_set_32 _ | Pstring_set_64 _
  | Pbigstring_set_16 _ | Pbigstring_set_32 _ | Pbigstring_set_64 _ -> false
  | Psequand | Psequor -> false

let rec no_effects (flam : Flambda.t) =
  match flam with
  | Var _ -> true
  | Let (_, _, def, body) -> no_effects_named def && no_effects body
  | Let_rec (defs, body) ->
    no_effects body
      && List.for_all (fun (_, def) -> no_effects_named def) defs
  | If_then_else (_, ifso, ifnot) -> no_effects ifso && no_effects ifnot
  | Switch (_, sw) ->
    let aux (_, flam) = no_effects flam in
    List.for_all aux sw.blocks
      && List.for_all aux sw.consts
      && Misc.may_default no_effects sw.failaction true
  | String_switch (_, sw, def) ->
    List.for_all (fun (_, lam) -> no_effects lam) sw
      && Misc.may_default no_effects def true
  | Static_catch (_, _, body, _) | Try_with (body, _, _) ->
    (* If there is a [raise] in [body], the whole [Try_with] may have an
       effect, so there is no need to test the handler. *)
    no_effects body
  (* CR mshinwell for pchambart: Is there something subtle here about the
     compilation of [While] and [For] which means that even a
     non-side-effecting loop body does not imply that the loop itself has
     no effects? *)
  | While _ | For _ | Apply _ | Send _ | Assign _ | Static_raise _ -> false
  | Proved_unreachable -> true

and no_effects_named (named : Flambda.named) =
  match named with
  | Symbol _ | Const _ | Set_of_closures _ | Project_closure _
  | Project_var _ | Move_within_set_of_closures _ -> true
  | Prim (prim, _, _) -> no_effects_prim prim
  | Expr flam -> no_effects flam
