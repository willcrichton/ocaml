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

open Abstract_identifiers

let apply_on_subexpressions f (flam : _ Flambda.t) =
  match flam with
  | Fsymbol _
  | Fvar _
  | Fconst _
  | Funreachable _ -> ()

  | Fassign (_,f1,_)
  | Fselect_closure({set_of_closures = f1},_)
  | Fvar_within_closure({closure = f1},_) ->
    f f1

  | Flet ( _, _, f1, f2,_)
  | Ftrywith (f1,_,f2,_)
  | Fsequence (f1,f2,_)
  | Fwhile (f1,f2,_)
  | Fstaticcatch (_,_,f1,f2,_) ->
    f f1; f f2;

  | Ffor (_,f1,f2,_,f3,_)
  | Fifthenelse (f1,f2,f3,_) ->
    f f1;f f2;f f3

  | Fstaticraise (_,l,_)
  | Fprim (_,l,_,_) ->
    List.iter f l

  | Fapply ({func;args},_) ->
    List.iter f (func::args)
  | Fset_of_closures ({function_decls;free_vars},_) ->
    Variable.Map.iter (fun _ v -> f v) free_vars;
    Variable.Map.iter (fun _ (ffun : _ Flambda.function_declaration) ->
        f ffun.body)
      function_decls.funs
  | Fletrec (defs, body,_) ->
    List.iter (fun (_,l) -> f l) defs;
    f body
  | Fswitch (arg,sw,_) ->
    f arg;
    List.iter (fun (_,l) -> f l) sw.consts;
    List.iter (fun (_,l) -> f l) sw.blocks;
    Misc.may f sw.failaction
  | Fstringswitch (arg,sw,def,_) ->
    f arg;
    List.iter (fun (_,l) -> f l) sw;
    Misc.may f def
  | Fsend (_,f1,f2,fl,_,_) ->
    List.iter f (f1::f2::fl)

let subexpressions (flam : _ Flambda.t) =
  match flam with
  | Fsymbol _
  | Fvar _
  | Fconst _
  | Funreachable _ -> []

  | Fassign (_,f1,_)
  | Fselect_closure({set_of_closures = f1},_)
  | Fvar_within_closure({closure = f1},_) ->
      [f1]

  | Flet ( _, _, f1, f2,_)
  | Ftrywith (f1,_,f2,_)
  | Fsequence (f1,f2,_)
  | Fwhile (f1,f2,_)
  | Fstaticcatch (_,_,f1,f2,_) ->
      [f1; f2]

  | Ffor (_,f1,f2,_,f3,_)
  | Fifthenelse (f1,f2,f3,_) ->
      [f1; f2; f3]

  | Fstaticraise (_,l,_)
  | Fprim (_,l,_,_) -> l

  | Fapply ({func;args},_) ->
      (func::args)

  | Fset_of_closures ({function_decls;free_vars},_) ->
      let l = Variable.Map.fold (fun _ v l -> v :: l) free_vars [] in
      Variable.Map.fold (fun _ (f : _ Flambda.function_declaration) l ->
          f.body :: l)
        function_decls.funs l

  | Fletrec (defs, body,_) ->
      body :: (List.map snd defs)

  | Fswitch (arg,sw,_) ->
      let l = List.fold_left (fun l (_,v) -> v :: l) [arg] sw.consts in
      let l = List.fold_left (fun l (_,v) -> v :: l) l sw.blocks in
      Misc.may_fold (fun f1 l -> f1 :: l) sw.failaction l

  | Fstringswitch (arg,sw,def,_) ->
      let l = List.fold_left (fun l (_,v) -> v :: l) [arg] sw in
      Misc.may_fold (fun f1 l -> f1 :: l) def l

  | Fsend (_,f1,f2,fl,_,_) ->
      (f1::f2::fl)

let iter_general ~toplevel f t =
  let rec aux (t : _ Flambda.t) =
    f t;
    match t with
    | Fsymbol _
    | Fvar _
    | Fconst _ -> ()

    | Fassign (_,f1,_)
    | Fselect_closure({set_of_closures = f1},_)
    | Fvar_within_closure({closure = f1},_) ->
      aux f1

    | Flet ( _, _, f1, f2,_)
    | Ftrywith (f1,_,f2,_)
    | Fsequence (f1,f2,_)
    | Fwhile (f1,f2,_)
    | Fstaticcatch (_,_,f1,f2,_) ->
      aux f1; aux f2;

    | Ffor (_,f1,f2,_,f3,_)
    | Fifthenelse (f1,f2,f3,_) ->
      aux f1;aux f2;aux f3

    | Fstaticraise (_,l,_)
    | Fprim (_,l,_,_) ->
      iter_list l

    | Fapply ({func = f1; args = fl},_) ->
      iter_list (f1::fl)

    | Fset_of_closures ({function_decls = funcs; free_vars = fv},_) ->
      Variable.Map.iter (fun _ v -> aux v) fv;
      if not toplevel then begin
        Variable.Map.iter (fun _ (ffun : _ Flambda.function_declaration) ->
            aux ffun.body)
          funcs.funs
      end

    | Fletrec (defs, body,_) ->
      List.iter (fun (_,l) -> aux l) defs;
      aux body
    | Fswitch (arg,sw,_) ->
      aux arg;
      List.iter (fun (_,l) -> aux l) sw.consts;
      List.iter (fun (_,l) -> aux l) sw.blocks;
      Misc.may aux sw.failaction
    | Fstringswitch (arg,sw,def,_) ->
      aux arg;
      List.iter (fun (_,l) -> aux l) sw;
      Misc.may aux def

    | Fsend (_,f1,f2,fl,_,_) ->
      iter_list (f1::f2::fl)
    | Funreachable _ -> ()

  and iter_list l = List.iter aux l in
  aux t

let iter f t = iter_general ~toplevel:false f t
let iter_toplevel f t = iter_general ~toplevel:true f t

let iter_on_closures f t =
  let aux (flam : _ Flambda.t) =
    match flam with
    | Fset_of_closures (clos,data) ->
        f clos data
    | Fassign _ | Fvar _
    | Fsymbol _ | Fconst _ | Fapply _ | Fselect_closure _
    | Fvar_within_closure _ | Flet _ | Fletrec _
    | Fprim _ | Fswitch _ | Fstaticraise _ | Fstaticcatch _
    | Ftrywith _ | Fifthenelse _ | Fsequence _ | Fstringswitch _
    | Fwhile _ | Ffor _ | Fsend _ | Funreachable _
      -> ()
  in
  iter aux t

let map_general ~toplevel f tree =
  let rec aux (tree : _ Flambda.t) =
    let exp = match tree with
      | Fsymbol _ -> tree
      | Fvar _ -> tree
      | Fconst _ -> tree
      | Fapply ({ func; args; kind; dbg; return_arity }, annot) ->
          Fapply ({ func = aux func;
                    args = List.map aux args;
                    kind; dbg; return_arity }, annot)
      | Fset_of_closures ({ function_decls; free_vars;
                    specialised_args },annot) ->
          let function_decls =
            if toplevel
            then function_decls
            else
              { function_decls with
                funs = Variable.Map.map
                    (fun (ffun : _ Flambda.function_declaration) ->
                      { ffun with body = aux ffun.body })
                    function_decls.funs } in
          Fset_of_closures ({ function_decls;
                      free_vars = Variable.Map.map aux free_vars;
                      specialised_args }, annot)
      | Fselect_closure ({ set_of_closures; closure_id; relative_to}, annot) ->
          Fselect_closure ({ set_of_closures = aux set_of_closures;
                       closure_id; relative_to}, annot)
      | Fvar_within_closure (vc, annot) ->
          Fvar_within_closure ({ vc with closure = aux vc.closure }, annot)
      | Flet(str, id, lam, body, annot) ->
          let lam = aux lam in
          let body = aux body in
          Flet (str, id, lam, body, annot)
      | Fletrec(defs, body, annot) ->
          let defs = List.map (fun (id,lam) -> id,aux lam) defs in
          let body = aux body in
          Fletrec (defs, body, annot)
      | Fprim(p, args, dbg, annot) ->
          let args = List.map aux args in
          Fprim (p, args, dbg, annot)
      | Fstaticraise(i, args, annot) ->
          let args = List.map aux args in
          Fstaticraise (i, args, annot)
      | Fstaticcatch (i, vars, body, handler, annot) ->
          let body = aux body in
          let handler = aux handler in
          Fstaticcatch (i, vars, body, handler, annot)
      | Ftrywith(body, id, handler, annot) ->
          let body = aux body in
          let handler = aux handler in
          Ftrywith(body, id, handler, annot)
      | Fifthenelse(arg, ifso, ifnot, annot) ->
          let arg = aux arg in
          let ifso = aux ifso in
          let ifnot = aux ifnot in
          Fifthenelse(arg, ifso, ifnot, annot)
      | Fsequence(lam1, lam2, annot) ->
          let lam1 = aux lam1 in
          let lam2 = aux lam2 in
          Fsequence(lam1, lam2, annot)
      | Fwhile(cond, body, annot) ->
          let cond = aux cond in
          let body = aux body in
          Fwhile(cond, body, annot)
      | Fsend(kind, met, obj, args, dbg, annot) ->
          let met = aux met in
          let obj = aux obj in
          let args = List.map aux args in
          Fsend(kind, met, obj, args, dbg, annot)
      | Ffor(id, lo, hi, dir, body, annot) ->
          let lo = aux lo in
          let hi = aux hi in
          let body = aux body in
          Ffor(id, lo, hi, dir, body, annot)
      | Fassign(id, lam, annot) ->
          let lam = aux lam in
          Fassign(id, lam, annot)
      | Fswitch(arg, sw, annot) ->
          let arg = aux arg in
          let sw =
            { sw with
              failaction = Misc.may_map aux sw.failaction;
              consts = List.map (fun (i,v) -> i, aux v) sw.consts;
              blocks = List.map (fun (i,v) -> i, aux v) sw.blocks; } in
          Fswitch(arg, sw, annot)
      | Fstringswitch(arg, sw, def, annot) ->
          let arg = aux arg in
          let sw = List.map (fun (i,v) -> i, aux v) sw in
          let def = Misc.may_map aux def in
          Fstringswitch(arg, sw, def, annot)

      | Funreachable _ -> tree
    in
    f exp
  in
  aux tree

let map f tree = map_general ~toplevel:false f tree
let map_toplevel f tree = map_general ~toplevel:true f tree

let expression_free_variables (flam : _ Flambda.t) =
  match flam with
  | Fvar (id,_) -> Variable.Set.singleton id
  | Fassign (id,_,_) -> Variable.Set.singleton id
  | Fset_of_closures ({free_vars; specialised_args},_) ->
      let set = Variable.Map.keys (Variable.Map.revert specialised_args) in
      Variable.Map.fold (fun _ expr set ->
          (* HACK:
             This is not needed, but it avoids moving lets inside free_vars *)
          match (expr : _ Flambda.t) with
          | Fvar(var, _) -> Variable.Set.add var set
          | _ -> set)
        free_vars set
  | _ -> Variable.Set.empty

let fold_subexpressions (type acc) f (acc : acc) (flam : _ Flambda.t)
      : acc * _ Flambda.t =
  match flam with
  | Ftrywith(body,id,handler,d) ->
      let acc, body = f acc Variable.Set.empty body in
      let acc, handler = f acc (Variable.Set.singleton id) handler in
      acc, Ftrywith(body,id,handler,d)

  | Ffor(id, lo, hi, dir, body, d) ->
      let acc, lo = f acc Variable.Set.empty lo in
      let acc, hi = f acc Variable.Set.empty hi in
      let acc, body = f acc (Variable.Set.singleton id) body in
      acc, Ffor(id, lo, hi, dir, body, d)

  | Flet (kind, id, def, body, d) ->
      let acc, def = f acc Variable.Set.empty def in
      let acc, body = f acc (Variable.Set.singleton id) body in
      acc, Flet (kind, id, def, body, d)

  | Fletrec (defs, body, d) ->
      let vars = Variable.Set.of_list (List.map fst defs) in
      let acc, defs =
        List.fold_right (fun (var,def) (acc, defs) ->
            let acc, def = f acc vars def in
            acc, (var,def) :: defs)
          defs (acc,[]) in
      let acc, body = f acc vars body in
      acc, Fletrec (defs, body, d)

  | Fstaticcatch (exn,ids,body,handler,d) ->
      let acc, body = f acc Variable.Set.empty body in
      let acc, handler = f acc (Variable.Set.of_list ids) handler in
      acc, Fstaticcatch (exn,ids,body,handler,d)

  | Fstaticraise (exn, args, d) ->
      let acc, args =
        List.fold_right
          (fun arg (acc, l) ->
             let acc, arg = f acc Variable.Set.empty arg in
             acc, arg :: l) args (acc,[]) in
      acc, Fstaticraise (exn, args, d)

  | Fset_of_closures ({ function_decls; free_vars } as closure, d) ->
      let acc, funs =
        Variable.Map.fold
          (fun v (fun_decl : _ Flambda.function_declaration) (acc, funs) ->
            let acc, body = f acc fun_decl.free_variables fun_decl.body in
            acc, Variable.Map.add v { fun_decl with body } funs)
          function_decls.funs (acc, Variable.Map.empty)
      in
      let function_decls = { function_decls with funs } in
      let acc, free_vars =
        Variable.Map.fold (fun v flam (acc, free_vars) ->
            let acc, flam = f acc Variable.Set.empty flam in
            acc, Variable.Map.add v flam free_vars)
          free_vars (acc, Variable.Map.empty)
      in
      acc, Fset_of_closures({ closure with function_decls; free_vars }, d)

  | Fswitch (arg,
             { numconsts; consts; numblocks;
               blocks; failaction }, d) ->
      let acc, arg = f acc Variable.Set.empty arg in
      let aux (i,flam) (acc, l) =
        let acc, flam = f acc Variable.Set.empty flam in
        acc, (i,flam) :: l
      in
      let acc, consts = List.fold_right aux consts (acc,[]) in
      let acc, blocks = List.fold_right aux blocks (acc,[]) in
      let acc, failaction =
        match failaction with
        | None -> acc, None
        | Some flam ->
            let acc, flam = f acc Variable.Set.empty flam in
            acc, Some flam in
      acc,
      Fswitch (arg,
               { numconsts; consts; numblocks;
                 blocks; failaction }, d)

  | Fstringswitch (arg, sw, def, d) ->
      let acc, arg = f acc Variable.Set.empty arg in
      let aux (i,flam) (acc, l) =
        let acc, flam = f acc Variable.Set.empty flam in
        acc, (i,flam) :: l
      in
      let acc, sw = List.fold_right aux sw (acc,[]) in
      let acc, def =
        match def with
        | None -> acc, None
        | Some def ->
            let acc, def = f acc Variable.Set.empty def in
            acc, Some def in
      acc, Fstringswitch (arg, sw, def, d)

  | Fapply ({ func; args; kind; dbg; return_arity }, d) ->
      let acc, func = f acc Variable.Set.empty func in
      let acc, args =
        List.fold_right
          (fun args (acc, l) ->
             let acc, args = f acc Variable.Set.empty args in
             acc, args :: l) args (acc,[]) in
      acc, Fapply ({ func; args; kind; dbg; return_arity }, d)

  | Fsend (kind, e1, e2, args, dbg, d) ->
      let acc, args =
        List.fold_right
          (fun arg (acc, l) ->
             let acc, arg = f acc Variable.Set.empty arg in
             acc, arg :: l) args (acc,[]) in
      let acc, e1 = f acc Variable.Set.empty e1 in
      let acc, e2 = f acc Variable.Set.empty e2 in
      acc, Fsend (kind, e1, e2, args, dbg, d)

  | Fsequence(e1, e2, d) ->
      let acc, e1 = f acc Variable.Set.empty e1 in
      let acc, e2 = f acc Variable.Set.empty e2 in
      acc, Fsequence(e1, e2, d)

  | Fwhile(cond, body, d) ->
      let acc, cond = f acc Variable.Set.empty cond in
      let acc, body = f acc Variable.Set.empty body in
      acc, Fwhile(cond, body, d)

  | Fifthenelse(cond,ifso,ifnot,d) ->
      let acc, cond = f acc Variable.Set.empty cond in
      let acc, ifso = f acc Variable.Set.empty ifso in
      let acc, ifnot = f acc Variable.Set.empty ifnot in
      acc, Fifthenelse(cond,ifso,ifnot,d)

  | Fprim (p,args,dbg,d) ->
      let acc, args =
        List.fold_right
          (fun arg (acc, l) ->
             let acc, arg = f acc Variable.Set.empty arg in
             acc, arg :: l) args (acc,[]) in
      acc, Fprim (p,args,dbg,d)

  | Fassign (v,flam,d) ->
      let acc, flam = f acc Variable.Set.empty flam in
      acc, Fassign (v,flam,d)

  | Fselect_closure(clos,d) ->
      let acc, set_of_closures = f acc Variable.Set.empty clos.set_of_closures in
      acc, Fselect_closure({clos with set_of_closures},d)

  | Fvar_within_closure(clos,d) ->
      let acc, closure = f acc Variable.Set.empty clos.closure in
      acc, Fvar_within_closure({clos with closure},d)

  | ( Fsymbol _
    | Fvar _
    | Fconst _
    | Funreachable _) as e ->
      acc, e

let subexpression_bound_variables (flam : _ Flambda.t) =
  match flam with
  | Ftrywith(body,id,handler,_) ->
      [Variable.Set.singleton id, handler;
       Variable.Set.empty, body]
  | Ffor(id, lo, hi, _, body, _) ->
      [Variable.Set.empty, lo;
       Variable.Set.empty, hi;
       Variable.Set.singleton id, body]
  | Flet ( _, id, def, body,_) ->
      [Variable.Set.empty, def;
       Variable.Set.singleton id, body]
  | Fletrec (defs, body,_) ->
      let vars = Variable.Set.of_list (List.map fst defs) in
      let defs = List.map (fun (_,def) -> vars, def) defs in
      (vars, body) :: defs
  | Fstaticcatch (_,ids,body,handler,_) ->
      [Variable.Set.empty, body;
       Variable.Set.of_list ids, handler]
  | Fset_of_closures ({ function_decls; free_vars },_) ->
      let free_vars =
        List.map (fun (_, def) -> Variable.Set.empty, def)
          (Variable.Map.bindings free_vars) in
      let funs =
        List.map (fun (_, (fun_def : _ Flambda.function_declaration)) ->
            fun_def.free_variables, fun_def.body)
          (Variable.Map.bindings function_decls.funs)in
      funs @ free_vars
  | e ->
      List.map (fun s -> Variable.Set.empty, s) (subexpressions e)

let free_variables tree =
  let free = ref Variable.Set.empty in
  let bound = ref Variable.Set.empty in
  let add id =
    if not (Variable.Set.mem id !free) then free := Variable.Set.add id !free in
  let aux (flam : _ Flambda.t) =
    match flam with
    | Fvar (id,_) -> add id
    | Fassign (id,_,_) -> add id
    | Fset_of_closures ({specialised_args},_) ->
        Variable.Map.iter (fun _ id -> add id) specialised_args
    | Ftrywith(_,id,_,_)
    | Ffor(id, _, _, _, _, _)
    | Flet ( _, id, _, _,_) ->
        bound := Variable.Set.add id !bound
    | Fletrec (l, _,_) ->
        List.iter (fun (id,_) -> bound := Variable.Set.add id !bound) l
    | Fstaticcatch (_,ids,_,_,_) ->
        List.iter (fun id -> bound := Variable.Set.add id !bound) ids
    | _ -> ()
  in
  iter_toplevel aux tree;
  Variable.Set.diff !free !bound

let rec fold_return_sites f acc tree =
  let open Flambda in
  let aux (acc, list) (i, flam) =
    let (acc, flam') = fold_return_sites f acc flam in
    (acc, (i, flam') :: list)
  in
  match tree with
  | Fsymbol _
  | Fvar _
  | Fprim _
  | Fstaticraise _
  | Fapply _
  | Fset_of_closures _
  | Fselect_closure _
  | Fvar_within_closure _
  | Fwhile _
  | Ffor _
  | Fassign _
  | Fsend _
  | Funreachable _
  | Fconst _ -> f acc tree

  | Flet(kind, id, def, body, d) ->
    let (acc, body') = fold_return_sites f acc body in
    (acc, Flet(kind, id, def, body', d))

  | Fletrec(defs, body, d) ->
    let (acc, body') = fold_return_sites f acc body in
    (acc, Fletrec(defs, body', d))

  | Fifthenelse(cond, body_then, body_else, d) ->
    let (acc, body_then') = fold_return_sites f acc body_then in
    let (acc, body_else') = fold_return_sites f acc body_else in
    (acc, Fifthenelse(cond, body_then', body_else', d))

  | Fswitch(arg, sw, d) ->
    let (acc, consts') = List.fold_left aux (acc, []) sw.consts in
    let (acc, blocks') = List.fold_left aux (acc, []) sw.blocks in
    let (acc, failaction') = match sw.failaction with
      | Some(flam) ->
        let (acc, flam') = fold_return_sites f acc flam in
        (acc, Some(flam'))
      | None -> (acc, None)
    in
    (acc, Fswitch(arg, {sw with consts = consts';
                                blocks = blocks';
                                failaction = failaction'},
                  d))

  | Fstringswitch(arg, sw, def, v) ->
    let (acc, sw') = List.fold_left aux (acc, []) sw in
    let (acc, def') = match def with
      | Some(flam) ->
        let (acc, flam') = fold_return_sites f acc flam in
        (acc, Some(flam'))
      | None -> (acc, None)
    in
    (acc, Fstringswitch(arg, sw', def', v))

  | Ftrywith(body, id, handler, d) ->
    let (acc, body') = fold_return_sites f acc body in
    let (acc, handler') = fold_return_sites f acc handler in
    (acc, Ftrywith(body', id, handler', d))

  | Fsequence(e1, e2, d) ->
    let (acc, e2') = fold_return_sites f acc e2 in
    (acc, Fsequence(e1, e2', d))

  | Fstaticcatch(exn, ids, body, handler, d) ->
    let (acc, body') = fold_return_sites f acc body in
    let (acc, handler') = fold_return_sites f acc handler in
    (acc, Fstaticcatch(exn, ids, body', handler', d))

let map_data (type t1) (type t2) (f:t1 -> t2)
      (tree:t1 Flambda.t) : t2 Flambda.t =
  let rec mapper : t1 Flambda.t -> t2 Flambda.t = function
    | Fsymbol (sym, v) -> Fsymbol (sym, f v)
    | Fvar (id, v) -> Fvar (id, f v)
    | Fconst (cst, v) -> Fconst (cst, f v)
    | Flet(str, id, lam, body, v) ->
        Flet(str, id, mapper lam, mapper body, f v)
    | Fletrec(defs, body, v) ->
        let defs = List.map (fun (id,def) -> (id, mapper def)) defs in
        Fletrec( defs, mapper body, f v)
    | Fapply ({ func; args; kind; dbg; return_arity }, v) ->
        Fapply ({ func = mapper func;
                  args = list_mapper args;
                  kind; dbg; return_arity }, f v)
    | Fset_of_closures ({ function_decls; free_vars;
                  specialised_args }, v) ->
        let function_decls =
          { function_decls with
            funs = Variable.Map.map
                (fun (ffun : _ Flambda.function_declaration) ->
                  { ffun with body = mapper ffun.body })
                function_decls.funs } in
        Fset_of_closures ({ function_decls;
                    free_vars = Variable.Map.map mapper free_vars;
                    specialised_args }, f v)
    | Fselect_closure ({ set_of_closures; closure_id; relative_to}, v) ->
        Fselect_closure ({ set_of_closures = mapper set_of_closures;
                     closure_id; relative_to}, f v)
    | Fvar_within_closure (vc, v) ->
        Fvar_within_closure ({ vc with closure = mapper vc.closure }, f v)
    | Fswitch(arg, sw, v) ->
        let aux l = List.map (fun (i,v) -> i, mapper v) l in
        let sw = { sw with
                   consts = aux sw.consts;
                   blocks = aux sw.blocks;
                   failaction = Misc.may_map mapper sw.failaction } in
        Fswitch(mapper arg, sw, f v)
    | Fstringswitch (arg, sw, def, v) ->
        let sw = List.map (fun (i,v) -> i, mapper v) sw in
        Fstringswitch (mapper arg, sw, Misc.may_map mapper def, f v)
    | Fsend(kind, met, obj, args, dbg, v) ->
        Fsend(kind, mapper met, mapper obj, list_mapper args, dbg, f v)
    | Fprim(prim, args, dbg, v) ->
        Fprim(prim, list_mapper args, dbg, f v)
    | Fstaticraise (i, args, v) ->
        Fstaticraise (i, list_mapper args, f v)
    | Fstaticcatch (i, vars, body, handler, v) ->
        Fstaticcatch (i, vars, mapper body, mapper handler, f v)
    | Ftrywith(body, id, handler, v) ->
        Ftrywith(mapper body, id, mapper handler, f v)
    | Fifthenelse(arg, ifso, ifnot, v) ->
        Fifthenelse(mapper arg, mapper ifso, mapper ifnot, f v)
    | Fsequence(lam1, lam2, v) ->
        Fsequence(mapper lam1, mapper lam2, f v)
    | Fwhile(cond, body, v) ->
        Fwhile(mapper cond, mapper body, f v)
    | Ffor(id, lo, hi, dir, body, v) ->
        Ffor(id, mapper lo, mapper hi, dir, mapper body, f v)
    | Fassign(id, lam, v) ->
        Fassign(id, mapper lam, f v)
    | Funreachable v -> Funreachable (f v)
  and list_mapper l = List.map mapper l in
  mapper tree
