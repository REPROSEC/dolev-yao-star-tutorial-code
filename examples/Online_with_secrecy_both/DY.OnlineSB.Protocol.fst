module DY.OnlineSB.Protocol

open Comparse
open DY.Core
open DY.Lib

open DY.Simplified
open DY.Extend

/// A simple 2 message protocol
///
/// A -> B: Ping (A, n_A)
/// B -> A: Ack n_A

(*** Message Type ***)

/// for each of the two messages we define an abstract message type

[@@ with_bytes bytes] // ignore this line for now
type ping_t = {
  p_alice: principal;
  p_n_a : bytes;
}

[@@ with_bytes bytes] // ignore this line for now
type ack = {
  a_n_a : bytes;
}

/// the overall abstract message type
/// (consisting of constructors for the two messages
/// and using the above abstract types for each of them)
[@@ with_bytes bytes] // ignore this line for now
type message =
  | Ping: (msg:ping_t) -> message
  | Ack: (msg:ack) -> message


/// We use Comparse to generate the corresponding message formats.
/// I.e., we don't need to write parsing and serializing by hand
///
/// for this we need the `[@@ with_bytes bytes]` annotation for the message types above
///
/// We are not going into the details of how Comparse works.


/// We let Comparse generate a parser `ps_ping` for the abstract `ping` type
%splice [ps_ping_t] (gen_parser (`ping_t))

%splice [ps_ack] (gen_parser (`ack))

%splice [ps_message] (gen_parser (`message))

/// With the above parsers, we can make our `message` type an instance of
/// Comparse's `parseable_serializeable` class.
/// Again, the details are not important here,
/// but this is the step that enables us to call
/// `parse message buff` and `serialize message msg`
/// to translate between bytes and our abstract message type.
instance parseable_serializeable_bytes_message: parseable_serializeable bytes message = mk_parseable_serializeable ps_message


(*** State Type ***)

/// As for the messages we define abstract state types
/// for the three states stored by Alice and Bob after each step of the protocol.

[@@ with_bytes bytes]
type sent_ping = {
  sp_bob : principal;
  sp_n_a : bytes;
}

[@@ with_bytes bytes]
type sent_ack = {
  sa_alice: principal;
  sa_n_a : bytes;
}

[@@ with_bytes bytes]
type received_ack = {
  ra_bob : principal;
  ra_n_a : bytes;
}

[@@ with_bytes bytes]
type state = 
  | SendingPing: (ping:sent_ping) -> state
  | SendingAck: sent_ack -> state
  | ReceivedAck: received_ack -> state

/// As for messages, we use Comparse to generate
/// a parser and serializer for our abstract state type.

%splice [ps_sent_ping] (gen_parser (`sent_ping))
%splice [ps_sent_ack] (gen_parser (`sent_ack))
%splice [ps_received_ack] (gen_parser (`received_ack))
%splice [ps_state] (gen_parser (`state))

/// Now, we can call
/// `parse state buff` and `serialize state st`
/// to translate between bytes and the abstract state type.
instance parseable_serializeable_bytes_state: parseable_serializeable bytes state = mk_parseable_serializeable ps_state

(** TODO **)

instance local_state_state: local_state state = {
  tag = "P.State";
  format = parseable_serializeable_bytes_state;
}


type global_sess_ids = {
  pki: state_id;
  private_keys: state_id;
}

(*** The Protocol ***)

let key_tag = "P.PublicKey"

let nonce_label alice bob = principal_label alice `join` principal_label bob

val send_ping: principal -> principal -> state_id -> traceful (option (state_id & timestamp))
let send_ping alice bob keys_sid =
  // TODO: use public/secret for this label? 
  // or already explain high-level idea of "intended readers"?
  let* n_a = mk_rand NoUsage (join (principal_label alice) (principal_label bob)) 32 in
  let* sid = start_new_session alice (SendingPing {sp_bob = bob; sp_n_a = n_a}) in

  let ping = Ping {p_alice = alice; p_n_a = n_a} in 
  let*? ping_encrypted = pke_enc_for alice bob keys_sid key_tag ping in
  // let* msg_ts = send_msg (serialize message ping) in
  let* msg_ts = send_msg ping_encrypted in
  
  return (Some (sid, msg_ts))


val decode_ping : principal -> state_id -> bytes -> traceful (option ping_t)
let decode_ping bob keys_sid msg =
  // let? png = parse message msg in
  let*? png = pke_dec_with_key_lookup #message bob keys_sid key_tag msg in
  guard_tr (Ping? png);*?
  return (Some (Ping?.msg png))

val receive_ping_and_send_ack: principal -> global_sess_ids -> timestamp -> traceful (option (state_id & timestamp))
let receive_ping_and_send_ack bob global_sids msg_ts =
  let*? msg = recv_msg msg_ts in
  let*? png = decode_ping bob global_sids.private_keys msg in
  let n_a = png.p_n_a in
  let alice = png.p_alice in

  let* sess_id = start_new_session bob (SendingAck {sa_alice = png.p_alice; sa_n_a = png.p_n_a}) in

  let ack = Ack {a_n_a = n_a} in
  let*? ack_encrypted = pke_enc_for bob alice global_sids.pki key_tag ack in
  let* ack_ts = send_msg ack_encrypted in
  
  return (Some (sess_id, ack_ts))


val decode_ack : principal -> state_id -> bytes -> traceful (option ack)
let decode_ack alice keys_sid cipher =
  let*? ack = pke_dec_with_key_lookup #message alice keys_sid key_tag cipher in
  guard_tr (Ack? ack);*?
  return (Some (Ack?.msg ack))

val receive_ack: principal -> state_id -> timestamp -> traceful (option state_id)
let receive_ack alice keys_sid ack_ts =
  let*? msg = recv_msg ack_ts in
//  let*? ack = return (parse message ack) in
  let*? ack = decode_ack alice keys_sid msg in

  let*? (st, sid) = lookup_state #state alice
    (fun st -> SendingPing? st && (SendingPing?.ping st).sp_n_a = ack.a_n_a)
    in
  guard_tr(SendingPing? st);*?
  let SendingPing ping = st in

  set_state alice sid (ReceivedAck {ra_bob=ping.sp_bob; ra_n_a = ack.a_n_a});*

  return (Some sid)
