module DY.TwoMessage.Protocol

open Comparse
open DY.Core
open DY.Lib

open DY.Simplified
open DY.Extend

open DY.TwoMessage.Data

/// Here we define the DY* model of the
/// simple Two-Message protocol:
///
/// A -> B: Ping (A, n_A)
/// B -> A: Ack n_A
///
/// The model consists of 3 functions,
/// one for each action:
/// 1. Alice sends the Ping to Bob (`send_ping`)
/// 2. Bob receives the Ping and replies with the Ack (`receive_ping_and_send_ack`)
/// 3. Alice receives the Ack (`receive_ack`)


(*** Sending the Ping ***)

/// Alice sends the first message to Bob:
/// * Alice generates a new nonce [n_a]
/// * sends the message (Alice, n_a) (intended for Bob)
/// * stores n_a and Bob in a state (in a new session)
/// The step returns the ID of the new state
/// and the timestamp of the message on the trace

val send_ping: principal -> principal -> traceful (state_id & timestamp)
let send_ping alice bob =
  // generate a new nonce
  let* n_a = gen_rand in

  // the abstract message (alice, n_a)
  let ping = Ping {alice = alice; n_a = n_a} in 
  // send the message (serialize abstract to bytes first!)
  let* msg_ts = send_msg (serialize message_t ping) in

  // the abstract new state (bob, n_a)
  let ping_state = SentPing {bob = bob; n_a = n_a} in
  // start a new session with this new state
  let* sid = start_new_session alice ping_state in

  // return the ID of the new session and the timestamp of the message
  return (sid, msg_ts)


(*** Replying to a Ping with an Ack ***)

/// Bob receives the first messages and replies:
/// * read the message (Alice, n_a) from the trace
/// * send the reply (n_a) (intended for Alice)
/// * store n_a and Alice in a state in a new session
/// The step returns the ID of the new state
/// and the timestamp of the reply on the trace.
/// The step fails, if
/// the message is not of the right type, i.e., not a first message.

val receive_ping_and_send_ack: principal -> timestamp -> traceful (option (state_id & timestamp))
let receive_ping_and_send_ack bob msg_ts =
  // receive the message
  let*? msg = recv_msg msg_ts in 
  // this returns bytes, so we need to translate to our abstract type:
  let*? png_ = return (parse message_t msg) in
  // check that the received message is of the right type
  // (the whole step fails, if the message is not a Ping)
  guard_tr (Ping? png_);*?

  // read the data (alice and n_a) from the received message
  let Ping png = png_ in // this "removes" the Ping constructor from png_
  let alice = png.alice in
  let n_a = png.n_a in

  // the abstract reply (n_a)
  let ack = Ack {n_a} in
  // send the reply (serialize abstract to bytes first!)
  let* ack_ts = send_msg (serialize message_t ack) in

  // the abstract new state storing alice and n_a from the message
  let ack_state = SentAck {alice; n_a} in
  // start a new session wit this new state
  let* sess_id = start_new_session bob ack_state in

  // return the ID of the new session and the timestamp of the message
  return (Some (sess_id, ack_ts))


(*** Receiving an Ack ***)

/// Alice receives the reply from Bob:
/// * read the message (n_a) from the trace
/// * check if Alice previously sent n_a in some session
/// * store completion of this session in a new state
/// Returns the ID of the session that is marked as completed.
/// The step fails, if
/// * the message is not of the right type, i.e., not a reply
/// * there is no prior session related to n_a

val receive_ack: principal -> timestamp -> traceful (option state_id)
let receive_ack alice ack_ts =
  // receive the message and translate to abstract message type
  let*? msg = recv_msg ack_ts in
  let*? ack = return (parse message_t msg) in
  // check that the message is a reply
  // (otherwise this step fails)
  guard_tr (Ack? ack);*?

  // read the data (n_a) from the message
  let Ack ack = ack in
  let n_a = ack.n_a in

  // check if alice has a previous session where
  // * she startet a run
  // * with the nonce n_a (the one received from Bob)
  // (the step fails, if no such session exists)
  let*? (sid, st) = lookup_state #state_t alice
    (fun st -> 
          SentPing? st // st is a state of type SentPing 
      && (SentPing?.ping st).n_a = n_a // the nonce stored in st is n_a
    ) in
  guard_tr(SentPing? st);*?
  // access the name of Bob in the stored state
  let bob = (SentPing?.ping st).bob in

  // mark this session as completed by
  // setting a new state
  set_state alice sid (ReceivedAck {bob; n_a});*

  // return the ID of the completed session
  return (Some sid)
