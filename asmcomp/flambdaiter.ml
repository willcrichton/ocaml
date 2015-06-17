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

open Abstract_identifiers
open Flambda

let apply_on_subexpressions f = function
  | Fsymbol _
  | Fvar _
  | Fconst _
  | Funreachable _ -> ()

  | Fassign (_,f1,_)
  | Fclosure({fu_closure = f1},_)
  | Fvar_within_closure({vc_closure = f1},_) ->
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

  | Fapply ({ap_function;ap_arg},_) ->
    List.iter f (ap_function::ap_arg)
  | Fset_of_closures ({cl_fun;cl_free_var},_) ->
    Variable.Map.iter (fun _ v -> f v) cl_free_var;
    Variable.Map.iter (fun _ ffun -> f ffun.body) cl_fun.funs
  | Fletrec (defs, body,_) ->
    List.iter (fun (_,l) -> f l) defs;
    f body
  | Fswitch (arg,sw,_) ->
    f arg;
    List.iter (fun (_,l) -> f l) sw.fs_consts;
    List.iter (fun (_,l) -> f l) sw.fs_blocks;
    Misc.may f sw.fs_failaction
  | Fstringswitch (arg,sw,def,_) ->
    f arg;
    List.iter (fun (_,l) -> f l) sw;
    Misc.may f def
  | Fsend (_,f1,f2,fl,_,_) ->
    List.iter f (f1::f2::fl)

let subexpressions = function
  | Fsymbol _
  | Fvar _
  | Fconst _
  | Funreachable _ -> []

  | Fassign (_,f1,_)
  | Fclosure({fu_closure = f1},_)
  | Fvar_within_closure({vc_closure = f1},_) ->
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

  | Fapply ({ap_function;ap_arg},_) ->
      (ap_function::ap_arg)

  | Fset_of_closures ({cl_fun;cl_free_var},_) ->
      let l = Variable.Map.fold (fun _ v l -> v :: l) cl_free_var [] in
      Variable.Map.fold (fun _ f l -> f.body :: l) cl_fun.funs l

  | Fletrec (defs, body,_) ->
      body :: (List.map snd defs)

  | Fswitch (arg,sw,_) ->
      let l = List.fold_left (fun l (_,v) -> v :: l) [arg] sw.fs_consts in
      let l = List.fold_left (fun l (_,v) -> v :: l) l sw.fs_blocks in
      Misc.may_fold (fun f1 l -> f1 :: l) sw.fs_failaction l

  | Fstringswitch (arg,sw,def,_) ->
      let l = List.fold_left (fun l (_,v) -> v :: l) [arg] sw in
      Misc.may_fold (fun f1 l -> f1 :: l) def l

  | Fsend (_,f1,f2,fl,_,_) ->
      (f1::f2::fl)


let iter_general ~toplevel f t =
  let rec aux t =
    f t;
    match t with
    | Fsymbol _
    | Fvar _
    | Fconst _ -> ()

    | Fassign (_,f1,_)
    | Fclosure({fu_closure = f1},_)
    | Fvar_within_closure({vc_closure = f1},_) ->
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

    | Fapply ({ap_function = f1; ap_arg = fl},_) ->
      iter_list (f1::fl)

    | Fset_of_closures ({cl_fun = funcs; cl_free_var = fv},_) ->
      Variable.Map.iter (fun _ v -> aux v) fv;
      if not toplevel
      then Variable.Map.iter (fun _ ffun -> aux ffun.body) funcs.funs

    | Fletrec (defs, body,_) ->
      List.iter (fun (_,l) -> aux l) defs;
      aux body
    | Fswitch (arg,sw,_) ->
      aux arg;
      List.iter (fun (_,l) -> aux l) sw.fs_consts;
      List.iter (fun (_,l) -> aux l) sw.fs_blocks;
      Misc.may aux sw.fs_failaction
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
  let aux = function
    | Fset_of_closures (clos,data) ->
        f clos data
    | Fassign _ | Fvar _
    | Fsymbol _ | Fconst _ | Fapply _ | Fclosure _
    | Fvar_within_closure _ | Flet _ | Fletrec _
    | Fprim _ | Fswitch _ | Fstaticraise _ | Fstaticcatch _
    | Ftrywith _ | Fifthenelse _ | Fsequence _ | Fstringswitch _
    | Fwhile _ | Ffor _ | Fsend _ | Funreachable _
      -> ()
  in
  iter aux t

let map_general ~toplevel f tree =
  let rec aux tree =
    let exp = match tree with
      | Fsymbol _ -> tree
      | Fvar (id,annot) -> tree
      | Fconst (cst,annot) -> tree
      | Fapply ({ ap_function; ap_arg } as ap, annot) ->
          Fapply ({ ap with ap_function = aux ap_function;
                            ap_arg = List.map aux ap_arg; },
                  annot)
      | Fset_of_closures ({ cl_fun; cl_free_var;
                    cl_specialised_arg },annot) ->
          let cl_fun =
            if toplevel
            then cl_fun
            else
              { cl_fun with
                funs = Variable.Map.map
                    (fun ffun -> { ffun with body = aux ffun.body })
                    cl_fun.funs } in
          Fset_of_closures ({ cl_fun;
                      cl_free_var = Variable.Map.map aux cl_free_var;
                      cl_specialised_arg }, annot)
      | Fclosure ({ fu_closure; fu_fun; fu_relative_to}, annot) ->
          Fclosure ({ fu_closure = aux fu_closure;
                       fu_fun; fu_relative_to}, annot)
      | Fvar_within_closure (vc, annot) ->
          Fvar_within_closure ({ vc with vc_closure = aux vc.vc_closure }, annot)
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
              fs_failaction = Misc.may_map aux sw.fs_failaction;
              fs_consts = List.map (fun (i,v) -> i, aux v) sw.fs_consts;
              fs_blocks = List.map (fun (i,v) -> i, aux v) sw.fs_blocks; } in
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

let expression_free_variables = function
  | Fvar (id,_) -> Variable.Set.singleton id
  | Fassign (id,_,_) -> Variable.Set.singleton id
  | Fset_of_closures ({cl_free_var; cl_specialised_arg},_) ->
      let set = Variable.Map.keys (Variable.Map.revert cl_specialised_arg) in
      Variable.Map.fold (fun _ expr set ->
          (* HACK:
             This is not needed, but it avoids moving lets inside free_vars *)
          match expr with
          | Fvar(var, _) -> Variable.Set.add var set
          | _ -> set)
        cl_free_var set
  | _ -> Variable.Set.empty

let fold_subexpressions f acc = function
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

  | Fset_of_closures ({ cl_fun; cl_free_var } as closure, d) ->
      let acc, funs =
        Variable.Map.fold (fun v fun_decl (acc, funs) ->
            let acc, body = f acc fun_decl.free_variables fun_decl.body in
            acc, Variable.Map.add v { fun_decl with body } funs)
          cl_fun.funs (acc, Variable.Map.empty)
      in
      let cl_fun = { cl_fun with funs } in
      let acc, cl_free_var =
        Variable.Map.fold (fun v flam (acc, free_vars) ->
            let acc, flam = f acc Variable.Set.empty flam in
            acc, Variable.Map.add v flam free_vars)
          cl_free_var (acc, Variable.Map.empty)
      in
      acc, Fset_of_closures({ closure with cl_fun; cl_free_var }, d)

  | Fswitch (arg,
             { fs_numconsts; fs_consts; fs_numblocks;
               fs_blocks; fs_failaction }, d) ->
      let acc, arg = f acc Variable.Set.empty arg in
      let aux (i,flam) (acc, l) =
        let acc, flam = f acc Variable.Set.empty flam in
        acc, (i,flam) :: l
      in
      let acc, fs_consts = List.fold_right aux fs_consts (acc,[]) in
      let acc, fs_blocks = List.fold_right aux fs_blocks (acc,[]) in
      let acc, fs_failaction =
        match fs_failaction with
        | None -> acc, None
        | Some flam ->
            let acc, flam = f acc Variable.Set.empty flam in
            acc, Some flam in
      acc,
      Fswitch (arg,
               { fs_numconsts; fs_consts; fs_numblocks;
                 fs_blocks; fs_failaction }, d)

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

  | Fapply ({ ap_function; ap_arg } as ap, d) ->
      let acc, ap_function = f acc Variable.Set.empty ap_function in
      let acc, ap_arg =
        List.fold_right
          (fun arg (acc, l) ->
             let acc, arg = f acc Variable.Set.empty arg in
             acc, arg :: l) ap_arg (acc,[]) in
      acc, Fapply ({ ap with ap_function; ap_arg }, d)

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

  | Fclosure(clos,d) ->
      let acc, fu_closure = f acc Variable.Set.empty clos.fu_closure in
      acc, Fclosure({clos with fu_closure},d)

  | Fvar_within_closure(clos,d) ->
      let acc, vc_closure = f acc Variable.Set.empty clos.vc_closure in
      acc, Fvar_within_closure({clos with vc_closure},d)

  | ( Fsymbol _
    | Fvar _
    | Fconst _
    | Funreachable _) as e ->
      acc, e

let subexpression_bound_variables = function
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
  | Fset_of_closures ({ cl_fun; cl_free_var },_) ->
      let free_vars =
        List.map (fun (_, def) -> Variable.Set.empty, def)
          (Variable.Map.bindings cl_free_var) in
      let funs =
        List.map (fun (_, fun_def) ->
            fun_def.free_variables, fun_def.body)
          (Variable.Map.bindings cl_fun.funs)in
      funs @ free_vars
  | e ->
      List.map (fun s -> Variable.Set.empty, s) (subexpressions e)

let free_variables tree =
  let free = ref Variable.Set.empty in
  let bound = ref Variable.Set.empty in
  let add id =
    if not (Variable.Set.mem id !free) then free := Variable.Set.add id !free in
  let aux = function
    | Fvar (id,_) -> add id
    | Fassign (id,_,_) -> add id
    | Fset_of_closures ({cl_specialised_arg},_) ->
        Variable.Map.iter (fun _ id -> add id) cl_specialised_arg
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
  | Fclosure _
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
    let (acc, fs_consts') = List.fold_left aux (acc, []) sw.fs_consts in
    let (acc, fs_blocks') = List.fold_left aux (acc, []) sw.fs_blocks in
    let (acc, fs_failaction') = match sw.fs_failaction with
      | Some(flam) ->
        let (acc, flam') = fold_return_sites f acc flam in
        (acc, Some(flam'))
      | None -> (acc, None)
    in
    (acc, Fswitch(arg, {sw with fs_consts = fs_consts';
                                fs_blocks = fs_blocks';
                                fs_failaction = fs_failaction'},
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

let map_data (type t1) (type t2) (f:t1 -> t2) (tree:t1 flambda) : t2 flambda =
  let rec mapper : t1 flambda -> t2 flambda = function
    | Fsymbol (sym, v) -> Fsymbol (sym, f v)
    | Fvar (id, v) -> Fvar (id, f v)
    | Fconst (cst, v) -> Fconst (cst, f v)
    | Flet(str, id, lam, body, v) ->
        Flet(str, id, mapper lam, mapper body, f v)
    | Fletrec(defs, body, v) ->
        let defs = List.map (fun (id,def) -> (id, mapper def)) defs in
        Fletrec( defs, mapper body, f v)
    | Fapply ({ ap_function; ap_arg; } as ap, v) ->
        Fapply ({ ap with ap_function = mapper ap_function;
                          ap_arg = list_mapper ap_arg; },
                f v)
    | Fset_of_closures ({ cl_fun; cl_free_var;
                  cl_specialised_arg }, v) ->
        let cl_fun =
          { cl_fun with
            funs = Variable.Map.map
                (fun ffun -> { ffun with body = mapper ffun.body })
                cl_fun.funs } in
        Fset_of_closures ({ cl_fun;
                    cl_free_var = Variable.Map.map mapper cl_free_var;
                    cl_specialised_arg }, f v)
    | Fclosure ({ fu_closure; fu_fun; fu_relative_to}, v) ->
        Fclosure ({ fu_closure = mapper fu_closure;
                     fu_fun; fu_relative_to}, f v)
    | Fvar_within_closure (vc, v) ->
        Fvar_within_closure ({ vc with vc_closure = mapper vc.vc_closure }, f v)
    | Fswitch(arg, sw, v) ->
        let aux l = List.map (fun (i,v) -> i, mapper v) l in
        let sw = { sw with
                   fs_consts = aux sw.fs_consts;
                   fs_blocks = aux sw.fs_blocks;
                   fs_failaction = Misc.may_map mapper sw.fs_failaction } in
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
