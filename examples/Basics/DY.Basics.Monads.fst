module DY.Basics.Monads

open Comparse
open DY.Core
open DY.Lib

#set-options "--fuel 3 --ifuel 1 --z3rlimit 25  --z3cliopt 'smt.qi.eager_threshold=100'"


let rec trace_from_rev_list (ens: list trace_entry) : trace =
  match ens with
  | [] -> Nil
  | hd::tl -> Snoc (trace_from_rev_list tl ) hd

open FStar.List.Tot.Base

let trace_from_list ens = trace_from_rev_list (rev ens)

let _ = 
  let ev1 = Corrupt 1 in
  let ev2 = Corrupt 2 in
  let ens = [ev1; ev2] in
  let tr_rev = trace_from_rev_list ens in
  assert(tr_rev == Snoc (Snoc Nil ev2) ev1);

  let tr = trace_from_list ens in
  assert(tr == Snoc (Snoc Nil ev1) ev2)


#push-options "--fuel 1"
val add_entry_: trace_entry -> traceful (option unit)
let add_entry_ e tr =
  reveal_opaque (`%grows) (grows #label);
  norm_spec [zeta; delta_only [`%prefix]] (prefix #label);
  (Some (), Snoc tr e)
#pop-options

let en = Corrupt 1


(*** Composition in the traceful + option monad ***)

let f (x:nat) : traceful (option string) =
  if x < 2 
    then ( 
      add_entry_ en;*?
      return (Some "added entry")
    )
    else return None


let f3 :traceful (option string) = 
  f 1;*?
  f 2;*?
  f 0

let f3' :traceful (option string) = 
  f 0;*?
  f 1;*?
  f 2

let f3'' :traceful (option string) = 
  f 2;*?
  f 1;*?
  f 0

let f3''' :traceful (option string) = 
  f 0;*?
  f 1

let _ = 
  let t = trace_from_list [] in

  let (opt_s1, t1) = f 1 t in
  assert(Some? opt_s1);
  assert(t1 == trace_from_list [en]);
  
  let (opt_s2, t2) = f 2 t1 in
  assert(None? opt_s2);
  assert(t2 == t1);
  
  let (opt_s3, t3) = f 0 t2 in
  assert(Some? opt_s3);
  assert(t3 == trace_from_list [en; en]);

  let (opt_s_ges, t_ges) = f3 t in
  assert(None? opt_s_ges);
  assert(t_ges == trace_from_list [en]);

 

  let (opt_s_ges, t_ges) = f3' t in
  assert(None? opt_s_ges);
  assert(t_ges == trace_from_list [en; en]);

  let (opt_s_ges, t_ges) = f3'' t in
  assert(None? opt_s_ges);
  assert(t_ges == trace_from_list []);

  let (opt_s_ges, t_ges) = f3''' t in
  assert(Some? opt_s_ges);
  assert(t_ges == trace_from_list [en; en]);
  ()

(*** Comparing traceful+option with plain traceful actions ***)


let f3_tr :traceful (option string) = 
  f 1;*
  f 2;*
  f 0


let _ = 
  let t = trace_from_list [] in

  let (opt_s_ges, t_ges) = f3_tr t in
  assert(Some? opt_s_ges);
  assert(t_ges == trace_from_list [en;en]);
  ()


(*** Combining traceful+option with option actions ***)

val f_opt: nat -> option nat
let f_opt n =
  if n < 2 
  then None
  else Some (n-1)

val f_combine_tropt_and_opt: nat -> traceful (option string)
let f_combine_tropt_and_opt n =
  let*? nn = return (f_opt n) in
  f nn

let _ = 
  let t = trace_from_list [] in

  // f_opt 1 fails
  let (opt_str, tr) = f_combine_tropt_and_opt 1 t in
  assert(None? opt_str);
  assert(tr == t);

  // everything is successful
  let (opt_str, tr) = f_combine_tropt_and_opt 2 t in
  assert(Some? opt_str);
  assert(tr == trace_from_list [en]);

  // f 2 fails
  let (opt_str, tr) = f_combine_tropt_and_opt 3 t in
  assert(None? opt_str);
  assert(tr == t)

(*** Combining traceful+option with plain non-optional traceful actions ***)

let entr x = Corrupt x

val f_tr_nonopt: nat -> traceful nat
let f_tr_nonopt x =
  add_entry (entr x);*
  return (x + 1 <: nat)

val f_combine_tropt_and_trnonopt: nat -> traceful (option string)
let f_combine_tropt_and_trnonopt x =
  f_tr_nonopt x;*
  f x

val f_combine_tropt_and_trnonopt_with_let: nat -> traceful (option string)
let f_combine_tropt_and_trnonopt_with_let x =
  let* nx = f_tr_nonopt x in
  f nx

/// Having a non-optional traceful action as last step
val f_combine_tropt_and_trnonopt_more: nat -> traceful (option nat)
let f_combine_tropt_and_trnonopt_more x =
  let* nx = f_tr_nonopt x in
  f nx;*?
  // the following intuitive call will NOT work
  // f_tr_nonopt nx
  
  // instead, we need to access the return value and 
  // return it as a Some
  let* nnx = f_tr_nonopt nx in
  return (Some nnx)

#push-options "--fuel 4"
let _ =
  let t = trace_from_list [] in
  let x = 0 in

  let (nx, tr) = f_tr_nonopt x t in
  assert(nx = 1);
  assert(tr == trace_from_list [entr x] );


  let (opt_str, tr_opt) = f_combine_tropt_and_trnonopt x t in
  assert(Some? opt_str);
  assert(tr_opt == trace_from_list [entr x; en]);

  let (opt_str, tr_opt) = f_combine_tropt_and_trnonopt_with_let 1 t in
  assert(None? opt_str);
  assert(tr_opt == trace_from_list [entr 1]);
  
  let (opt_n, tr_opt) = f_combine_tropt_and_trnonopt_more 0 t in
  assert(opt_n = Some 2);
  assert(tr_opt == trace_from_list [entr 0; en; entr 1]);
  
  
  let (opt_str, tr_opt) = f_combine_tropt_and_trnonopt_more 1 t in
  assert(None? opt_str);
  assert(tr_opt == trace_from_list [entr 1]);
  ()
#pop-options

(*** Combining traceful+option with traceful actions ***)

let f3_ :traceful (option string) = 
  f 1;*?
  f 2;*
  f 0

let f3_' :traceful (option string) = 
  f 1;*
  f 3;*
  f 1;*
  f 2;*?
  f 0

let f3_'' :traceful (option string) = 
  f 1;*
  f 3;*?
  f 1;*
  f 2;*?
  f 0

let _ =
  let t = trace_from_list [] in
  
  let (opt_s_ges, t_ges) = f3_ t in
  assert(Some? opt_s_ges);
  assert(t_ges == trace_from_list [en; en]);

  let (opt_s_ges, t_ges) = f3_' t in
  assert(None? opt_s_ges);
  assert(t_ges == trace_from_list [en; en]);

  let (opt_s_ges, t_ges) = f3_'' t in
  assert(None? opt_s_ges);
  assert(t_ges == trace_from_list [en]);
  ()
