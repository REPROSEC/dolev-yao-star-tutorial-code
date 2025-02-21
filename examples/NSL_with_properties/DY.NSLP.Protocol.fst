module DY.NSLP.Protocol

open Comparse
open DY.Core
open DY.Lib

open DY.Simplified
open DY.Extend

open DY.NSLP.Data

/// Here, we define the model of the 
/// Needham-Schroeder-Lowe Fixed Public Key Protocol (NSL)
///
/// A -> B: enc{A, N_A}_B       Msg 1
/// B -> A: enc{B, N_A, N_B}_A  Msg 2
/// A -> B: enc{N_B}_B          Msg 3
///
/// The model consists of 4 function,
/// one for each protocol step:
/// 1. Alice sends the first message to Bob (`send_msg1`)
/// 2. Bob sends the second message to Alice (`send_msg2`)
/// 3. Alice sends the third message to Bob (`send_msg3`)
/// 4. Bob receives the third message from Alice (`receive_msg3`)

(*** Sending the first message (Alice, n_a) ***)

/// Alice sends the first message to Bob:
/// * Alice generates a new nonce [n_a]
/// * encrypts the message (Alice, n_a) for Bob
/// * sends the encrypted message
/// * stores n_a and Bob in a state (in a new session)
/// The step returns the ID of the new state
/// and the timestamp of the message on the trace
/// The step fails, if
/// encryption was not successful, i.e.,
/// Alice does not have a public key of Bob.

let nonce_label alice bob = join (principal_label alice) (principal_label bob)

val send_msg1: principal -> principal -> state_id -> traceful (option (state_id & timestamp))
let send_msg1 alice bob alice_public_keys_sid =
  let* n_a = gen_rand_labeled (nonce_label alice bob) in

  trigger_event alice (Initiating {alice; bob; n_a});*

  let msg1 = Msg1 {alice; n_a} in 
  let*? msg1_encrypted = pke_enc_for alice bob alice_public_keys_sid key_tag msg1 in
  let* msg_ts = send_msg msg1_encrypted in

  let state = SentMsg1 {bob; n_a} in
  let* sid = start_new_session alice state in

  return (Some (sid, msg_ts))

(*** Replying to a first message ***)

/// Bob receives the first messages and replies:
/// * read the message from the trace
/// * decrypt the message to (Alice, n_a)
/// * generate a new nonce [n_b]
/// * encrypt the reply (Bob, n_a, n_b) for Alice
/// * send the encrypted reply
/// * store n_a, n_b and Alice in a state in a new session
/// The step returns the ID of the new state
/// and the timestamp of the reply on the trace.
/// The step fails, if one of
/// * decryption fails
/// * the message is not of the right type, i.e., not a first message
/// * encryption fails (for example, if Bob doesn't have a public key for Alice)

val receive_msg1_and_send_msg2: principal -> state_id -> state_id -> timestamp -> traceful (option (state_id & timestamp))
let receive_msg1_and_send_msg2 bob bob_private_keys_sid bob_public_keys_sid msg_ts =
  let*? msg = recv_msg msg_ts in

  let*? msg1_ = pke_dec_with_key_lookup #message_t bob bob_private_keys_sid key_tag msg in
  guard_tr (Msg1? msg1_);*?
  let Msg1 msg1 = msg1_ in
  let alice = msg1.alice in
  let n_a = msg1.n_a in

  let* n_b = gen_rand_labeled (nonce_label alice bob) in

  let msg2 = Msg2 {bob; n_a; n_b} in
  let*? msg2_encrypted = pke_enc_for bob alice bob_public_keys_sid key_tag msg2 in
  let* msg2_ts = send_msg msg2_encrypted in

  trigger_event bob (Responding1 {alice; bob; n_a; n_b});*

  let state = SentMsg2 {alice; n_a; n_b} in
  let* sess_id = start_new_session bob state in
  
  return (Some (sess_id, msg2_ts))

(*** Sending the final message ***)


/// Alice receives the second messages and replies:
/// * read the message from the trace
/// * decrypt the message to (Bob, n_a, n_b)
/// * encrypt the reply (n_b) for Bob
/// * send the encrypted reply
/// * store n_a, n_b and Bob in a state in the session related to Bob and n_a
/// The step returns the ID of the new state
/// and the timestamp of the reply on the trace.
/// The step fails, if one of
/// * decryption fails
/// * the message is not of the right type, i.e., not a first message
/// * encryption fails (for example, if Bob doesn't have a public key for Alice)
/// * there is no prior session related to Bob and n_a

val receive_msg2_and_send_msg3: principal -> state_id -> state_id -> timestamp -> traceful (option (state_id & timestamp))
let receive_msg2_and_send_msg3 alice alice_private_keys_sid alice_public_keys_sid msg_ts =
  let*? msg = recv_msg msg_ts in

  let*? msg2_ = pke_dec_with_key_lookup #message_t alice alice_private_keys_sid key_tag msg in
  guard_tr (Msg2? msg2_);*?
  let Msg2 msg2 = msg2_ in
  let bob = msg2.bob in
  let n_a = msg2.n_a in
  let n_b = msg2.n_b in

  let*? (sid, st) = lookup_state #state_t alice
    (fun st -> 
          SentMsg1? st
      && (SentMsg1?.sentmsg1 st).n_a = n_a
      && (SentMsg1?.sentmsg1 st).bob = bob
    ) in
  guard_tr(SentMsg1? st);*?
  

  let msg3 = Msg3 {n_b} in
  let*? msg3_encrypted = pke_enc_for alice bob alice_public_keys_sid key_tag msg3 in
  let* msg3_ts = send_msg msg3_encrypted in

  trigger_event alice (Responding2 {alice; bob; n_a; n_b});*

  let state = SentMsg3 {bob; n_a; n_b} in
  set_state alice sid state;*
  
  return (Some (sid, msg3_ts))

(*** Receiving the final message ***)

/// Bob receives the reply from Alice:
/// * read the message from the trace
/// * decrypt the message to (n_b)
/// * check if Bob previously sent n_b in some session
/// * store completion of this session in a new state
/// Returns the ID of the session that is marked as completed.
/// The step fails, if one of
/// * decryption fails
/// * the message is not of the right type, i.e., not a reply
/// * there is no prior session related to n_a

val receive_msg3: principal -> state_id -> timestamp -> traceful (option state_id)
let receive_msg3 bob bob_private_keys_sid msg3_ts =
  let*? msg = recv_msg msg3_ts in
  let*? msg3 = pke_dec_with_key_lookup #message_t bob bob_private_keys_sid key_tag msg in
  guard_tr (Msg3? msg3);*?
  let Msg3 msg3 = msg3 in
  let n_b = msg3.n_b in

  let*? (sid, st) = lookup_state #state_t bob
    (fun st -> 
          SentMsg2? st
      && (SentMsg2?.sentmsg2 st).n_b = n_b
    ) in
  guard_tr(SentMsg2? st);*?
  let alice = (SentMsg2?.sentmsg2 st).alice in
  let n_a = (SentMsg2?.sentmsg2 st).n_a in

  trigger_event bob (Finishing {alice; bob; n_a; n_b});*

  set_state alice sid (ReceivedMsg3 {alice; n_a; n_b});*

  return (Some sid)
