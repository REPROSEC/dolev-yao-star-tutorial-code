module DY.OnlineS.Invariants

open Comparse 
open DY.Core
open DY.Lib

open DY.OnlineS.Data
open DY.OnlineS.Protocol

#set-options "--fuel 0 --ifuel 1 --z3rlimit 25"

/// In this module, we define the protocol invariants.
/// They consist of
/// * crypto invariants and
/// * trace invariants which in turn consist of
///   * state invariants and
///   * event invariants
///
/// We then have to show
/// * these invariants imply the secrecy property (see DY.OnlineS.Secrecy) and
/// * every protocol step maintains these invariants (see DY.OnlineS.Invariants.Proofs)
/// With this, we then know that
/// the protocol model satisfies the secrecy property.


(*** Crypto Invariants ***)


(** TODO **)
// needed for `crypto_prediates.pke_pred.pred_later`
%splice [ps_ping_t_is_well_formed] (gen_is_well_formed_lemma (`ping_t))
%splice [ps_ack_t_is_well_formed] (gen_is_well_formed_lemma (`ack_t))
%splice [ps_message_t_is_well_formed] (gen_is_well_formed_lemma (`message_t))



// ignore this for now
instance crypto_usages_online : crypto_usages = default_crypto_usages

#push-options "--ifuel 3"
let crypto_predicates_online : crypto_predicates = { 
  default_crypto_predicates with 
  (* we restrict when a message is allowed to be encrypted 
     with some secret key

     Or put differently:
     What are the guarantees that an honest sender can provide
     that are available at the receiver after decryption?
  *)
  pke_pred = { 
    pred = (fun tr sk_usage pk msg ->
    exists prin. // the intended receiver of the message
    (
      // needed for `decode_ping_proof` [Why?]
      (* the key used for the encryption is
         a protocol-level public key for the intended receiver (prin) 
      *)
      sk_usage == long_term_key_type_to_usage (LongTermPkeKey key_tag) prin /\
      (match parse message_t msg with
      | Some (Ping {alice; n_a}) ->
          (* a Ping message can only be encrypted if
             (Or: if you decrypt a Ping from an honest party 
             you get the guarantees that:)
             the contained nonce n_a
             is labeled for 
             * the name provided in the message (alice)
             * and the intended receiver of the message (bob)
          *)
          let bob = prin in
          get_label tr n_a == nonce_label alice bob
      | Some (Ack {n_a}) ->
         (* No conditions / guarantees needed for an Ack *)
          True
      | _ -> False // other messages can not be encrypted
      ))
      ); 
    (* a lemma guaranteeing:
       if the predicate specified above holds for some trace tr1
       it also holds for any extension tr2 of tr1
    *)
    pred_later = (fun tr1 tr2 sk_usage pk msg ->
      parse_wf_lemma message_t (bytes_well_formed tr1) msg
    ) 
  } 
}
#pop-options

/// Collecting the usages and prediates in the final crypto invariants

instance crypto_invariants_online: crypto_invariants = {
  usages = crypto_usages_online;
  preds =  crypto_predicates_online
}


(*** State Invariant ***)

// TODO
// Needed for `state_predicate.pred_knowable`
%splice [ps_sent_ping_t_is_well_formed] (gen_is_well_formed_lemma (`sent_ping_t))
%splice [ps_sent_ack_t_is_well_formed] (gen_is_well_formed_lemma (`sent_ack_t))
%splice [ps_received_ack_t_is_well_formed] (gen_is_well_formed_lemma (`received_ack_t))
%splice [ps_state_t_is_well_formed] (gen_is_well_formed_lemma (`state_t))

#push-options "--ifuel 2 --z3cliopt 'smt.qi.eager_threshold=50'"
(* We restrict what states are allowed to be stored by principals *)
let state_predicate_online: local_state_predicate state_t = {
  pred = (fun tr prin sess_id st ->
    match st with
    | SentPing {bob; n_a} -> (
        (* a SentPing state may only be stored if
           the stored nonce is labeled for
           * the storing principal (alice)
           * the principal stored in the state 
             (the intended receiver of the Ping: bob)
        *) 
        let alice = prin in
        is_secret (nonce_label alice bob) tr n_a
    )
    | SentAck {alice; n_a} -> (
        (* a SentAck state may only be stored if
           the stored nonce is readable by
           the storing principal (bob)

           -- this is a condition that must always hold,
           and is enforced by the `pred_knowable` Lemma.
        *)
        let bob = prin in
        is_knowable_by (principal_label bob) tr n_a
    )
    | ReceivedAck {bob; n_a}  -> (
        (* a ReceivedAck state may only be stored if
           the stored nonce is labeled for
           * the storing principal (alice)
           * the principal stored in the state
             (the expected sender of the Ack)
        *)
        let alice = prin in
        is_secret (nonce_label alice bob) tr n_a
    )
  );
  (* as for encryption we have a lemma guaranteeing:
     if the state predicate holds on some trace tr1
     it also holds for any extension tr2 of tr2
  *)
  pred_later = (fun tr1 tr2 prin sess_id st -> () );
  (* a lemma guaranteeing that
     the content of the state to be stored
     is readable by the storing principal
  *)
  pred_knowable = (fun tr prin sess_id st -> () );
}
#pop-options

(*** Trace invariants ***)

// TODO: can this (all_sessions and all_events) be hidden somehow?
let all_sessions = [
  pki_tag_and_invariant;
  private_keys_tag_and_invariant;
  (|local_state_state_t.tag, local_state_predicate_to_local_bytes_state_predicate state_predicate_online|);
]

/// We have no events here,
/// but we need to specify that for the trace invariants
let all_events = []


/// The final trace invariants
/// consisting of
/// * the state invariant and
/// * the event invariant

let trace_invariants_online: trace_invariants = {
  state_pred = mk_state_pred all_sessions;
  event_pred = mk_event_pred all_events;
}


(*** Protocol Invariants ***)

/// The final protocol invariants
/// consisting of
/// * the crypto invariants and
/// * the trace invariants

instance protocol_invariants_online: protocol_invariants = {
  crypto_invs = crypto_invariants_online;
  trace_invs = trace_invariants_online;
}

let complies_with_online_protocol tr = trace_invariant #protocol_invariants_online tr

/// Lemmas that the global state predicate contains all the local ones
(*TODO: can all of this be hidden ?*)

val all_sessions_has_all_sessions: unit -> Lemma (norm [delta_only [`%all_sessions; `%for_allP]; iota; zeta] (for_allP (has_local_bytes_state_predicate) all_sessions))
let all_sessions_has_all_sessions () =
  assert_norm(List.Tot.no_repeats_p (List.Tot.map dfst (all_sessions)));
  mk_state_pred_correct all_sessions;
  norm_spec [delta_only [`%all_sessions; `%for_allP]; iota; zeta] (for_allP (has_local_bytes_state_predicate) all_sessions)

val protocol_invariants_p_has_p_session_invariant: squash (has_local_state_predicate state_predicate_online)
let protocol_invariants_p_has_p_session_invariant = all_sessions_has_all_sessions ()

val protocol_invariants_p_has_pki_invariant: squash (has_pki_invariant #protocol_invariants_online)
let protocol_invariants_p_has_pki_invariant = all_sessions_has_all_sessions ()

val protocol_invariants_p_has_private_keys_invariant: squash (has_private_keys_invariant #protocol_invariants_online)
let protocol_invariants_p_has_private_keys_invariant = all_sessions_has_all_sessions ()
