module DY.Extend

open Comparse
open DY.Core
open DY.Lib
open DY.Core.Trace.Base

val is_secret_is_knowable: 
  {|cinvs: crypto_invariants|} ->
  l:label  -> 
  tr: trace ->
  b:bytes ->
  Lemma 
  (requires is_secret l tr b)
  (ensures is_knowable_by l tr b)
  [SMTPat (is_secret #cinvs l tr b)]
let is_secret_is_knowable l tr b = ()

let rand_generated_before tr b = 
  is_not_empty tr /\
  exists ts. rand_generated_at tr ts b

let state_was_set_some_id (#a:Type) {|local_state a|} tr prin (cont : a) =
  exists sid. DY.Lib.state_was_set tr prin sid cont

val empty_invariants:
  {| protocol_invariants |} ->
  Lemma (trace_invariant empty_trace)
let empty_invariants #pinvs = 
  normalize_term_spec trace_invariant


/// Lookup the most recent state of a principal satisfying some property.
/// Returns the state and corresponding state id,
/// or `None` if no such state exists.
///
/// ATTENTION: This may NOT return the most recent version of the session!
/// A session could look like this [st1, st2, st3], where
/// * st1 and st2 satisfy the property p
/// * st3 does NOT satisfy property p
/// The returned state will then be s2.


val trace_search_last_state_for: principal -> (state_id -> bytes -> bool) -> trace -> option (state_id & bytes)
let trace_search_last_state_for prin p tr =
  let is_state_for_satisfying prin p e =
    match e with
    | SetState prin' sid cont -> prin' = prin 
        && p sid cont
    | _ -> false in
  let? state_ts = trace_search_last tr (is_state_for_satisfying prin p) in
  let SetState _ sid content = get_entry_at tr state_ts in
  Some (sid, content)

val get_state_aux_: principal -> state_id -> tr:trace -> option bytes
let get_state_aux_ prin sid tr =
  let? (_, cont) = trace_search_last_state_for prin (fun sid' _ -> sid' = sid) tr in
  Some cont

val lookup_state_: principal -> (bytes -> bool) -> trace -> (option (state_id & bytes))
let lookup_state_ prin p tr =
  trace_search_last_state_for prin (fun _ cont -> p cont) tr

val core_lookup_state: principal -> (bytes -> bool) -> traceful (option (state_id & bytes))
let core_lookup_state prin p =
  let* tr = get_trace in
  return (lookup_state_ prin p tr)

/// Lookup the most recent tagged state for a principal that satisfys some property.
/// The property given as argument is on the _content_ of the state.

val lookup_tagged_state:
 string -> principal -> (bytes -> bool) -> traceful (option (state_id & bytes))
let lookup_tagged_state the_tag prin p =
  let p_ b =
    match parse tagged_state b with
    | None -> false
    | Some ({tag; content;}) -> tag = the_tag && p content in
  let*? (sid, full_content_bytes) = core_lookup_state prin p_ in
  match parse tagged_state full_content_bytes with
    | None -> return None
    | Some ({tag; content;}) ->
        if (tag = the_tag)
        then return (Some (sid, content))
        else return None

val lookup_tagged_state_pred:
  tag:string ->
  prin:principal -> p:(bytes -> bool) -> tr:trace ->
  Lemma
  (ensures (
    let (opt_content, tr_out) = lookup_tagged_state tag prin p tr in
    tr == tr_out /\
    (match opt_content with
     | None -> True
     | Some (sid, content) ->
           p content
         /\ tagged_state_was_set tr tag prin sid content
    )
  ))
  [SMTPat (lookup_tagged_state tag prin p tr);
  ]
let lookup_tagged_state_pred the_tag prin p tr =
  let (opt_content, tr_out) = lookup_tagged_state the_tag prin p tr in
  match opt_content with
  | None -> ()
  | Some (cont, sid) -> (
  reveal_opaque (`%tagged_state_was_set) (tagged_state_was_set);
  let p_ b =
    match parse tagged_state b with
    | None -> false
    | Some ({tag; content;}) -> tag = the_tag && p content in
  let (Some (sid, full_cont_bytes), _) = core_lookup_state prin p_ tr in
  serialize_parse_inv_lemma #bytes tagged_state full_cont_bytes
  )

val lookup_tagged_state_invariant:
  {|protocol_invariants|} ->
  tag:string -> spred:local_bytes_state_predicate tag ->
  prin:principal -> p:(bytes -> bool) -> tr:trace ->
  Lemma
  (requires
    trace_invariant tr /\
    has_local_bytes_state_predicate (|tag, spred|)
  )
  (ensures (
    let (opt_content, tr_out) = lookup_tagged_state tag prin p tr in
    tr == tr_out /\
    (match opt_content with
     | None -> True
     | Some (sid, content) ->
           spred.pred tr prin sid content
         /\ p content
         /\ tagged_state_was_set tr tag prin sid content
    )
  ))
  [SMTPat (lookup_tagged_state tag prin p tr);
   SMTPat (trace_invariant tr);
   SMTPat (has_local_bytes_state_predicate (|tag, spred|))]
let lookup_tagged_state_invariant #invs the_tag spred prin p tr =
  reveal_opaque (`%has_local_bytes_state_predicate) (has_local_bytes_state_predicate);
  let (opt_content, tr_out) = lookup_tagged_state the_tag prin p tr in
  match opt_content with
  | None -> ()
  | Some (sid, content) -> (
      let p_ b =
        match parse tagged_state b with
        | None -> false
        | Some ({tag; content;}) -> tag = the_tag && p content in

      let (Some (l_sid, l_cont), _) = core_lookup_state prin p_ tr in
      serialize_parse_inv_lemma #bytes tagged_state l_cont;
      reveal_opaque (`%tagged_state_was_set) (tagged_state_was_set);

      let (Some (sid, full_content_bytes), tr) = core_lookup_state prin p_ tr in
      local_eq_global_lemma split_local_bytes_state_predicate_params state_pred.pred the_tag spred (tr, prin, sid, full_content_bytes) the_tag (tr, prin, sid, content)
     )


/// Lookup the most recent state of a principal that satisfys some property.

val lookup_state:
  #a:Type -> {|local_state a|} ->
  principal -> (a -> bool) -> traceful (option (state_id & a))
let lookup_state #a #ls prin p =
  let p_ b =
    match parse a b with
    | None -> false
    | Some x -> p x in
  let*? (sid, content_bytes) = lookup_tagged_state ls.tag prin p_ in
  match parse a content_bytes with
  | None -> return None
  | Some content -> return (Some (sid, content))

val lookup_state_pred:
  #a:Type -> {|ls:local_state a|} ->
  prin:principal -> p:(a -> bool) -> tr:trace ->
  Lemma
  (ensures (
    let (opt_content, tr_out) = lookup_state prin p tr in
    tr == tr_out /\
    (match opt_content with
     | None -> True
     | Some (sid, content) ->
          p content
          /\ DY.Lib.state_was_set tr prin sid content
    )
  ))
  [SMTPat (lookup_state #a #ls prin p tr);
   ]
let lookup_state_pred #a #ls prin p tr =
  let (opt_content, tr_out) = lookup_state prin p tr in
  match opt_content with
  | None -> ()
  | Some _ -> (
      let p_ b =
        match parse a b with
        | None -> false
        | Some x -> p x in
      let (Some (l_sid, l_cont), _) = lookup_tagged_state ls.tag prin p_ tr in
     serialize_parse_inv_lemma #bytes a l_cont;
     reveal_opaque (`%DY.Lib.state_was_set) (DY.Lib.state_was_set #a)
  )



val lookup_state_invariant:
  #a:Type -> {|local_state a|} ->
  {|protocol_invariants|} ->
  spred:local_state_predicate a ->
  prin:principal -> p:(a -> bool) -> tr:trace ->
  Lemma
  (requires
    trace_invariant tr /\
    has_local_state_predicate spred
  )
  (ensures (
    let (opt_content, tr_out) = lookup_state prin p tr in
    tr == tr_out /\
    (match opt_content with
     | None -> True
     | Some (sid, content) ->
         spred.pred tr prin sid content
         /\ p content
         /\ DY.Lib.state_was_set tr prin sid content
    )
  ))
  [SMTPat (lookup_state #a prin p tr);
   SMTPat (trace_invariant tr);
   SMTPat (has_local_state_predicate spred)]
let lookup_state_invariant #a #ls #invs spred prin p tr =
  let (opt_content, tr_out) = lookup_state prin p tr in
  match opt_content with
  | None -> ()
  | Some _ -> (
      let p_ b =
        match parse a b with
        | None -> false
        | Some x -> p x in
      let (Some (l_sid, l_cont), _) = lookup_tagged_state ls.tag prin p_ tr in
      serialize_parse_inv_lemma #bytes a l_cont;
      reveal_opaque (`%DY.Lib.state_was_set) (DY.Lib.state_was_set #a)
  )
