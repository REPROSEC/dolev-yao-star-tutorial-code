module DY.Basics.Monads

open Comparse
open DY.Core
open DY.Lib

#set-options "--fuel 0 --ifuel 1 --z3rlimit 25  --z3cliopt 'smt.qi.eager_threshold=100'"

let en = Corrupt 1

let f (x:int) : traceful (option string) =
  if x < 2 
    then ( 
      add_entry en;*
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


let rec trace_from_rev_list (ens: list trace_entry) : trace =
  match ens with
  | [] -> Nil
  | hd::tl -> Snoc (trace_from_rev_list tl ) hd

open FStar.List.Tot.Base

let trace_from_list ens = trace_from_rev_list (rev ens)

#push-options "--fuel 3"
let _ = 
  let ev1 = Corrupt 1 in
  let ev2 = Corrupt 2 in
  let ens = [ev1; ev2] in
  let tr_rev = trace_from_rev_list ens in
  assert(tr_rev == Snoc (Snoc Nil ev2) ev1);

  let tr = trace_from_list ens in
  assert(tr == Snoc (Snoc Nil ev1) ev2)


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
#pop-options
