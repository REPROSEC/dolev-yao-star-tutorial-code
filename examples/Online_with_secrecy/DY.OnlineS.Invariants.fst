module DY.OnlineS.Invariants

open Comparse 
open DY.Core
open DY.Lib
open DY.OnlineS.Protocol

#set-options "--fuel 0 --ifuel 1 --z3rlimit 25  --z3cliopt 'smt.qi.eager_threshold=100'"



(*** Trace invariants ***)

// Needed for `pred_knowable`
%splice [ps_sent_ping_is_well_formed] (gen_is_well_formed_lemma (`sent_ping))
%splice [ps_sent_ack_is_well_formed] (gen_is_well_formed_lemma (`sent_ack))
%splice [ps_received_ack_is_well_formed] (gen_is_well_formed_lemma (`received_ack))
%splice [ps_state_is_well_formed] (gen_is_well_formed_lemma (`state))

// needed for `pred_later`
%splice [ps_ping_t_is_well_formed] (gen_is_well_formed_lemma (`ping_t))
%splice [ps_ack_is_well_formed] (gen_is_well_formed_lemma (`ack))
%splice [ps_message_is_well_formed] (gen_is_well_formed_lemma (`message))


instance crypto_usages_p : crypto_usages = default_crypto_usages

let crypto_p : crypto_predicates = { 
  default_crypto_predicates with 
  pkenc_pred = { 
    pred = (fun tr sk_usage msg ->
    exists prin. (
      match parse message msg with
      | Some (Ping ping) ->
          get_label tr ping.p_n_a == nonce_label ping.p_alice prin
      | _ -> False
      )
      ); 
    pred_later = (fun tr1 tr2 pk msg -> 
      parse_wf_lemma message (bytes_well_formed tr1) msg
    ) 
  } 
}

instance crypto_invariants_p: crypto_invariants = {
  usages = crypto_usages_p;
  preds =  crypto_p
}

/// The (local) state predicate.

let state_predicate_p: local_state_predicate state = {
  pred = (fun tr prin sess_id st ->
    match st with
    | SentPing ping -> (
      let alice = prin in
      is_knowable_by (principal_label alice) tr ping.sp_n_a /\
      is_secret (nonce_label alice ping.sp_bob) tr ping.sp_n_a
    )
    | SentAck ack -> (
      let bob = prin in
      is_knowable_by (principal_label bob) tr ack.sa_n_a /\
      is_secret (nonce_label ack.sa_alice bob) tr ack.sa_n_a
    )
    | ReceivedAck rack  -> (
      let alice = prin in
      is_knowable_by (principal_label alice) tr rack.ra_n_a /\
      is_secret (nonce_label alice rack.ra_bob) tr rack.ra_n_a
    )
  );
  pred_later = (fun tr1 tr2 prin sess_id st -> ());
  pred_knowable = (fun tr prin sess_id st -> ());
}


/// List of all local state predicates.

let all_sessions = [
  pki_tag_and_invariant;
  private_keys_tag_and_invariant;
  (|local_state_state.tag, local_state_predicate_to_local_bytes_state_predicate state_predicate_p|);
]

/// List of all local event predicates.

let all_events = []

/// Create the global trace invariants.

let trace_invariants_p: trace_invariants = {
  state_pred = mk_state_pred all_sessions;
  event_pred = mk_event_pred all_events;
}

instance protocol_invariants_p: protocol_invariants = {
  crypto_invs = crypto_invariants_p;
  trace_invs = trace_invariants_p;
}


// Needed for `n_a_secrecy`

/// Lemmas that the global state predicate contains all the local ones

val all_sessions_has_all_sessions: unit -> Lemma (norm [delta_only [`%all_sessions; `%for_allP]; iota; zeta] (for_allP (has_local_bytes_state_predicate) all_sessions))
let all_sessions_has_all_sessions () =
  assert_norm(List.Tot.no_repeats_p (List.Tot.map dfst (all_sessions)));
  mk_state_pred_correct all_sessions;
  norm_spec [delta_only [`%all_sessions; `%for_allP]; iota; zeta] (for_allP (has_local_bytes_state_predicate) all_sessions)

val protocol_invariants_p_has_p_session_invariant: squash (has_local_state_predicate state_predicate_p)
let protocol_invariants_p_has_p_session_invariant = all_sessions_has_all_sessions ()

val protocol_invariants_p_has_pki_invariant: squash (has_pki_invariant #protocol_invariants_p)
let protocol_invariants_p_has_pki_invariant = all_sessions_has_all_sessions ()

// val protocol_invariants_p_has_private_keys_invariant: squash (has_private_keys_invariant #protocol_invariants_p)
// let protocol_invariants_p_has_private_keys_invariant = all_sessions_has_all_sessions ()
