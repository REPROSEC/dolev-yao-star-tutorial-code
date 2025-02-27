module DY.OnlineA.Data

open Comparse
open DY.Core
open DY.Lib

/// Here, we define the abstract types for the "Online?" Protocol:
///
/// A -> B: enc{Ping (A, n_A)}_B
/// B -> A: enc{Ack n_A}_A
///
/// (They are the same as for the simple 2 message protocol)


/// We only highlight the differences to the previous model
/// for showing nonce secrecy.

(*** Message Type ***)

[@@ with_bytes bytes]
type ping_t = {
  alice: principal;
  n_a : bytes;
}

[@@ with_bytes bytes]
type ack_t = {
  n_a : bytes;
}

/// the overall abstract message type

[@@ with_bytes bytes]
type message_t =
  | Ping: (ping:ping_t) -> message_t
  | Ack: (ack:ack_t) -> message_t

%splice [ps_ping_t] (gen_parser (`ping_t))

%splice [ps_ack_t] (gen_parser (`ack_t))

%splice [ps_message_t] (gen_parser (`message_t))

instance parseable_serializeable_bytes_message_t: parseable_serializeable bytes message_t = mk_parseable_serializeable ps_message_t


(*** State Type ***)

[@@ with_bytes bytes]
type sent_ping_t = {
  bob : principal;
  n_a : bytes;
}

[@@ with_bytes bytes]
type sent_ack_t = {
  alice: principal;
  n_a : bytes;
}

[@@ with_bytes bytes]
type received_ack_t = {
  bob : principal;
  n_a : bytes;
}

[@@ with_bytes bytes]
type state_t = 
  | SentPing: (ping:sent_ping_t) -> state_t
  | SentAck: (ack:sent_ack_t) -> state_t
  | ReceivedAck: (rack:received_ack_t) -> state_t

%splice [ps_sent_ping_t] (gen_parser (`sent_ping_t))
%splice [ps_sent_ack_t] (gen_parser (`sent_ack_t))
%splice [ps_received_ack_t] (gen_parser (`received_ack_t))
%splice [ps_state_t] (gen_parser (`state_t))

instance parseable_serializeable_bytes_state_t: parseable_serializeable bytes state_t = mk_parseable_serializeable ps_state_t

instance local_state_state_t: local_state state_t = {
  tag = "Online.State";
  format = parseable_serializeable_bytes_state_t;
}



(*** PKI ***)

let key_tag = "Online.Key"


(*** Event type ***)

/// We are now using events to show the authentication property.
/// We have one event for each protocol step,
/// that is
/// * an Initiating event, that Alice triggers, when she starts a new run
/// * a Responding event, that Bob triggers, when he replies to a Ping with an Ack
/// * and a Finishing event, that Alice triggers, when she finishes a run.
/// 
/// Just as for messages and states,
/// we define abstract event types

/// The abstract type of the Initiating event
[@@ with_bytes bytes]
type ev_init_t = {
  alice:principal;
  bob:principal;
  n_a:bytes
}

/// The abstract type of the Responding event
[@@ with_bytes bytes]
type ev_respond_t = {
  alice:principal;
  bob:principal;
  n_a:bytes
}

/// The abstract type of the Finishing event
[@@ with_bytes bytes]
type ev_finish_t = {
  alice:principal;
  bob:principal;
  n_a:bytes
}


/// The overall event type
[@@ with_bytes bytes]
type event_t =
  | Initiating: ev_init_t -> event_t
  | Responding: ev_respond_t -> event_t
  | Finishing: ev_finish_t -> event_t


/// Using Comparse to generate parser and serializer for the abstract event types
%splice [ps_ev_init_t] (gen_parser (`ev_init_t))
%splice [ps_ev_respond_t] (gen_parser (`ev_respond_t))
%splice [ps_ev_finish_t] (gen_parser (`ev_finish_t))
%splice [ps_event_t] (gen_parser (`event_t))
%splice [ps_event_t_is_well_formed] (gen_is_well_formed_lemma (`event_t))


/// Make the overall event type an instance of DY.Lib event class
instance event_event_t: event event_t = {
  tag = "Online.Event";
  format = mk_parseable_serializeable ps_event_t;
}
