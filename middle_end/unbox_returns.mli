(** Convert functions which return boxes such that if inlined directly into
    an unbox (e.g. let (x, y) = foo()) then the boxing is eliminated.

    For example, it turns
      [fun foo x = (x, x)]
    into
      [fun foo x =
         let foo' x' = multi_return (x, x) in
         let result = foo' x in
         let tup0 = multi_get result 0 in
         let tup1 = multi_get result 1 in
         makeblock tup0 tup1]

    If foo is inlined into a call site that looks like [let (x, y) = foo()]
    then later optimization passes will eliminate the makeblock call.
*)
val unbox_returns : Flambda.t -> Flambda.t

val lift_ifs : Flambda.t -> Flambda.t
