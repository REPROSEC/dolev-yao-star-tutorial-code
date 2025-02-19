module DY.OnlineA.Protocol

open Comparse
open DY.Core
open DY.Lib

open DY.Simplified
open DY.Extend

open DY.OnlineA.Data

/// Here we define the DY* mode of the "Online?" protocol,
/// an extension of the simple Two-Message protocol:
/// the two messages are now (asymmetrically) encrypted
///
/// A -> B: enc{Ping (A, n_A)}_B
/// B -> A: enc{Ack n_A}_A
///
/// The model consists of 3 functions,
/// one for each protocol step
/// (just as for the simple Two-Message protocol):
/// 1. Alice sends the Ping to Bob (`send_ping`)
/// 2. Bob receives the Ping and replies with the Ack (`receive_ping_and_send_ack`)
/// 3. Alice receives the Ack (`receive_ack`)
///
/// Additionally, there are two helper functions
/// for steps 2 and 3 (`decode_ping` and `decode_ack`).

/// We only highlight the differences to the previous model
/// for nonce secrecy.

(*** Sending the Ping ***)

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

val send_ping: principal -> principal -> state_id -> traceful (option (state_id & timestamp))
let send_ping alice bob alice_public_keys_sid =
  let* n_a = gen_rand_labeled (nonce_label alice bob) in

  (* This is the new step of triggering the Initiating event.
     ATTENTION: it has to be called right after generating the nonce
     (for the event predicate we will see later)
  *)
  trigger_event alice (Initiating {alice = alice; bob = bob; n_a = n_a});*

  let ping = Ping {alice; n_a} in 

  let*? ping_encrypted = pke_enc_for alice bob alice_public_keys_sid key_tag ping in
  let* msg_ts = send_msg ping_encrypted in

  let ping_state = SentPing {bob; n_a} in
  let* sid = start_new_session alice ping_state in

  return (Some (sid, msg_ts))


(*** Replying to a Ping with an Ack ***)


/// Bob receives the first messages and replies:
/// * read the message from the trace
/// * decrypt the message to (Alice, n_a)
/// * encrypt the reply (n_a) for Alice
/// * send the encrypted reply
/// * store n_a and Alice in a state in a new session
/// The step returns the ID of the new state
/// and the timestamp of the reply on the trace.
/// The step fails, if one of
/// * decryption fails
/// * the message is not of the right type, i.e., not a first message
/// * encryption fails (for example, if Bob doesn't have a public key for Alice)

/// Decrypting the message (Step 2 from above) is pulled out to a separate function
/// The function
/// * decrypts the message
/// * checks that the message is of the right type (a Ping)
/// * returns the content of the message
/// The function fails if decryption fails.

val decode_ping : principal -> state_id -> bytes -> traceful (option ping_t)
let decode_ping bob bob_private_keys_sid msg =
  let*? png = pke_dec_with_key_lookup #message_t bob bob_private_keys_sid key_tag msg in
  
  guard_tr (Ping? png);*?

  return (Some (Ping?.ping png))

/// Now the actual receive and reply step
/// using the decode function
val receive_ping_and_send_ack: principal -> state_id -> state_id -> timestamp -> traceful (option (state_id & timestamp))
let receive_ping_and_send_ack bob bob_private_keys_sid bob_public_keys_sid msg_ts =
  let*? msg = recv_msg msg_ts in
  let*? png = decode_ping bob bob_private_keys_sid msg in

  let n_a = png.n_a in
  let alice = png.alice in
  
  (* This is the new step, where Bob triggers the Responding event for the current run
  *)
  trigger_event bob (Responding {alice = alice; bob = bob; n_a = n_a});* 

  let ack = Ack {n_a} in
  let*? ack_encrypted = pke_enc_for bob alice bob_public_keys_sid key_tag ack in
  let* ack_ts = send_msg ack_encrypted in

  let ack_state = SentAck {alice; n_a} in
  let* sess_id = start_new_session bob ack_state in
  
  return (Some (sess_id, ack_ts))


(*** Receiving an Ack ***)


/// Alice receives the reply from Bob:
/// * read the message from the trace
/// * decrypt the message to (n_a)
/// * check if Alice previously sent n_a in some session
/// * store completion of this session in a new state
/// Returns the ID of the session that is marked as completed.
/// The step fails, if one of
/// * decryption fails
/// * the message is not of the right type, i.e., not a reply
/// * there is no prior session related to n_a


/// Again, we pull out decryption of the message (Step 2):
/// * decrypt the message
/// * check that the message is of the Ack type
/// Returns the content of the reply.
/// Fails if decryption fails.

val decode_ack : principal -> state_id -> bytes -> traceful (option ack_t)
let decode_ack alice alice_private_keys_sid cipher =
  let*? ack = pke_dec_with_key_lookup #message_t alice alice_private_keys_sid key_tag cipher in

  guard_tr (Ack? ack);*?

  return (Some (Ack?.ack ack))

/// The actual protocol step using the decode function
val receive_ack: principal -> state_id -> timestamp -> traceful (option state_id)
let receive_ack alice alice_private_keys_sid ack_ts =
  let*? msg = recv_msg ack_ts in
  let*? ack = decode_ack alice alice_private_keys_sid msg in

  let n_a = ack.n_a in

  let*? (sid, st) = lookup_state #state_t alice
    (fun st -> 
          SentPing? st
      && (SentPing?.ping st).n_a = n_a
    ) in
  guard_tr(SentPing? st);*?
  let bob = (SentPing?.ping st).bob in
  
  (* This is the new step, where Alice triggers the Finishing event for the current run
  *)
  trigger_event alice (Finishing {alice; bob; n_a});*
  set_state alice sid (ReceivedAck {bob; n_a});*

  return (Some sid)
