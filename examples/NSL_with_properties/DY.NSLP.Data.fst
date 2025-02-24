module DY.NSLP.Data

open Comparse
open DY.Core
open DY.Lib

/// Needham-Schroeder-Lowe Fixed Public Key Protocol [1]
///
/// A -> B: {A, N_A}K_PB       Msg 1
/// B -> A: {B, N_A, N_B}K_PA  Msg 2 -- note addition of B
/// A -> B: {N_B}K_PB          Msg 3
///
/// [1] Gavin Lowe. "Breaking and fixing the Needham-Schroeder Public-Key
///     Protocol using FDR". TACAS, pp 147-166, 1996.
///
/// Here, we define the abstract types for the NSL protocol.

(*** Message Type ***)

/// for each of the messages we define an abstract message type

[@@ with_bytes bytes]
type message1_t = {
  alice: principal;
  n_a: bytes;
}

[@@ with_bytes bytes]
type message2_t = {
  bob: principal;
  n_a: bytes;
  n_b: bytes;
}

[@@ with_bytes bytes]
type message3_t = {
  n_b: bytes;
}

/// the overall abstract message type
/// (consisting of constructors for the messages
/// and using the above abstract types for each of them)

[@@ with_bytes bytes]
type message_t =
  | Msg1: (m1:message1_t) -> message_t
  | Msg2: (m2:message2_t) -> message_t
  | Msg3: (m3:message3_t) -> message_t

/// Using Comparse to generate parser and serializer for the message type

%splice [ps_message1_t] (gen_parser (`message1_t))
%splice [ps_message2_t] (gen_parser (`message2_t))
%splice [ps_message3_t] (gen_parser (`message3_t))
%splice [ps_message_t] (gen_parser (`message_t))

instance parseable_serializeable_bytes_message_t: parseable_serializeable bytes message_t = mk_parseable_serializeable ps_message_t

(*** State Type ***)

/// As for the messages we define abstract state types
/// for the four states stored by Alice and Bob after each step of the protocol.

[@@ with_bytes bytes]
type sent_msg1_t  = {
  bob: principal;
  n_a: bytes;
}

[@@ with_bytes bytes]
type sent_msg2_t  = {
  alice: principal;
  n_a: bytes;
  n_b: bytes;
}

[@@ with_bytes bytes]
type sent_msg3_t  = {
  bob: principal;
  n_a: bytes;
  n_b: bytes;
}

[@@ with_bytes bytes]
type received_msg3_t  = {
  alice: principal;
  n_a: bytes;
  n_b: bytes;
}

[@@ with_bytes bytes]
type state_t =
  | SentMsg1: (sentmsg1:sent_msg1_t) -> state_t
  | SentMsg2: (sentmsg2:sent_msg2_t) -> state_t
  | SentMsg3: (sentmsg3:sent_msg3_t) -> state_t
  | ReceivedMsg3: (receivedmsg3:received_msg3_t) -> state_t

/// As for messages, we use Comparse to generate
/// a parser and serializer for our abstract state types.

%splice [ps_sent_msg1_t] (gen_parser (`sent_msg1_t))
%splice [ps_sent_msg2_t] (gen_parser (`sent_msg2_t))
%splice [ps_sent_msg3_t] (gen_parser (`sent_msg3_t))
%splice [ps_received_msg3_t] (gen_parser (`received_msg3_t))
%splice [ps_state_t] (gen_parser (`state_t))

instance parseable_serializeable_bytes_state_t: parseable_serializeable bytes state_t = mk_parseable_serializeable ps_state_t


/// We tag our protocol level states,
/// so that they are distinguishable from any internal DY* states. 

instance local_state_state: local_state state_t = {
  tag = "NSL.State";
  format = parseable_serializeable_bytes_state_t;
}


(*** PKI ***)

/// Similarly as for states,
/// we tag the keys that are used on the protocol level,
/// so that they can not be confused with other keys.

let key_tag = "NSL.Key"

(*** Event type ***)

/// We have one event per protocol step:
/// * an Initiating event,
///   that Alice triggers, when she starts a new run
/// * a Responding1 event,
///   that Bob triggers, when he replies to a first message
/// * a Responding2 event,
///   that Alice triggers, when she replies to a second message
/// * a Finishing event,
///   that Bob triggers, when he receives a final message and finishes the run.

[@@ with_bytes bytes]
type ev_init_t = {
  alice:principal;
  bob:principal;
  n_a:bytes
}

[@@ with_bytes bytes]
type ev_respond1_t = {
  alice:principal;
  bob:principal;
  n_a:bytes;
  n_b:bytes
}

[@@ with_bytes bytes]
type ev_respond2_t = {
  alice:principal;
  bob:principal;
  n_a:bytes;
  n_b:bytes
}

[@@ with_bytes bytes]
type ev_finish_t = {
  alice:principal;
  bob:principal;
  n_a:bytes;
  n_b:bytes
}

[@@ with_bytes bytes]
type event_t =
  | Initiating:  ev_init_t -> event_t
  | Responding1: ev_respond1_t -> event_t
  | Responding2: ev_respond2_t -> event_t
  | Finishing:   ev_finish_t -> event_t 

%splice [ps_ev_init_t] (gen_parser (`ev_init_t))
%splice [ps_ev_respond1_t] (gen_parser (`ev_respond1_t))
%splice [ps_ev_respond2_t] (gen_parser (`ev_respond2_t))
%splice [ps_ev_finish_t] (gen_parser (`ev_finish_t))
%splice [ps_event_t] (gen_parser (`event_t))

instance event_event_t: event event_t = {
  tag = "NSL.Event";
  format = mk_parseable_serializeable ps_event_t;
}
