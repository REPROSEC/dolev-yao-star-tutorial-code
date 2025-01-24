module DY.Online.Protocol

open Comparse
open DY.Core
open DY.Lib

open DY.Simplified
open DY.Extend

open DY.Online.Data

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
/// We highlight the differences to the model of the Two-Message protocol.

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

val send_ping: principal -> principal -> state_id -> traceful (option (state_id & timestamp))
let send_ping alice bob alice_public_keys_sid =
  let* n_a = gen_rand in
  
  let ping = Ping {alice; n_a} in 

  (* Instead of just serializing the message,
     (as in the Two-Message Protocol model),
     we need to encrypt the Ping for Bob,
     using a public key of Bob with the protocol tag
     stored in Alice's public key storage.

     (may fail, Alice doesn't have a public key
     for Bob with the right tag stored in her key session)
    *)
  // returns the cipher text in wire format (i.e., includes serializing)
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

val receive_ping_and_send_ack: principal -> state_id -> state_id -> timestamp -> traceful (option (state_id & timestamp))
let receive_ping_and_send_ack bob bob_private_keys_sid bob_public_keys_sid msg_ts =
  let*? msg = recv_msg msg_ts in

  (* Instead of just parsing the message msg
     (as in the Two-Message Protocol model),
     we now have to decrypt the received message
     with a private key of Bob having the protocol tag.
     (fails, if no such key exists)
  *)
  // returns the abstract message (i.e., includes parsing)
  let*? png_ = pke_dec_with_key_lookup #message_t bob bob_private_keys_sid key_tag msg in

  guard_tr (Ping? png_);*?

  let Ping png = png_ in
  let alice = png.alice in
  let n_a = png.n_a in

  let ack = Ack {n_a} in

  (* Instead of just serializing the message,
     (as in the Two-Message Protocol model),
     we need to encrypt it for Alice,
     using a public key of Alice with the protocol tag
     stored in Bob's public key storage.
  *)
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

val receive_ack: principal -> state_id -> timestamp -> traceful (option state_id)
let receive_ack alice alice_private_keys_sid ack_ts =
  let*? msg = recv_msg ack_ts in

  (* Instead of just parsing the message msg
     (as in the Two-Message Protocol model),
     we now have to decrypt the received message
     with a private key of Alice having the protocol tag.
     (fails, if no such key exists)
  *)
  // returns the abstract message (i.e., includes parsing)
  let*? ack = pke_dec_with_key_lookup #message_t alice alice_private_keys_sid key_tag msg in

  guard_tr (Ack? ack);*?

  let Ack ack = ack in
  let n_a = ack.n_a in

  let*? (sid, st) = lookup_state #state_t alice
    (fun st -> 
          SentPing? st
      && (SentPing?.ping st).n_a = n_a
    ) in
  guard_tr(SentPing? st);*?
  let bob = (SentPing?.ping st).bob in

  set_state alice sid (ReceivedAck {bob; n_a});*

  return (Some sid)
