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

(*** Message Type ***)

/// for each of the two messages we define an abstract message type

[@@ with_bytes bytes] // ignore this line for now
type ping_t = {
  alice: principal;
  n_a : bytes;
}

[@@ with_bytes bytes] // ignore this line for now
type ack_t = {
  n_a : bytes;
}

/// the overall abstract message type
/// (consisting of constructors for the two messages
/// and using the above abstract types for each of them)

[@@ with_bytes bytes] // ignore this line for now
type message_t =
  | Ping: (ping:ping_t) -> message_t
  | Ack: (ack:ack_t) -> message_t


/// We use Comparse to generate the corresponding message formats.
/// I.e., we don't need to write parsing and serializing by hand
///
/// for this we need the `[@@ with_bytes bytes]` annotation for the message types above
///
/// We are not going into the details of how Comparse works.


/// We let Comparse generate a parser `ps_ping_t` for the abstract `ping_t` type

%splice [ps_ping_t] (gen_parser (`ping_t))

/// ... and the same for the other abstract message types

%splice [ps_ack_t] (gen_parser (`ack_t))

%splice [ps_message_t] (gen_parser (`message_t))

/// With the above parsers, we can make our `message` type an instance of
/// Comparse's `parseable_serializeable` class.
/// Again, the details are not important here,
/// but this is the step that enables us to call
/// `parse message buff` and `serialize message msg`
/// to translate between bytes and our abstract message type.

instance parseable_serializeable_bytes_message_t: parseable_serializeable bytes message_t = mk_parseable_serializeable ps_message_t


(*** State Type ***)

/// As for the messages we define abstract state types
/// for the three states stored by Alice and Bob after each step of the protocol.

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

/// As for messages, we use Comparse to generate
/// a parser and serializer for our abstract state types.

%splice [ps_sent_ping_t] (gen_parser (`sent_ping_t))
%splice [ps_sent_ack_t] (gen_parser (`sent_ack_t))
%splice [ps_received_ack_t] (gen_parser (`received_ack_t))
%splice [ps_state_t] (gen_parser (`state_t))

/// Now, we can call
/// `parse state buff` and `serialize state st`
/// to translate between bytes and the abstract state type.

instance parseable_serializeable_bytes_state_t: parseable_serializeable bytes state_t = mk_parseable_serializeable ps_state_t

/// We tag our protocol level states,
/// so that they are distinguishable from any internal DY* states. 

instance local_state_state: local_state state_t = {
  tag = "P.State";
  format = parseable_serializeable_bytes_state_t;
}



(*** PKI ***)

/// For en-/de-cryption we assume some PKI.
/// I.e., every participant has some private decryption keys
/// and some public encryption keys from other participants.
/// All private keys of a participant will be stored in one session
/// and all public keys that the participant knows will be stored in another session.
/// For each participant, we collect both these session IDs in a global record.

type global_sess_ids = {
  pki: state_id;
  private_keys: state_id;
}

/// Similarly as for states,
/// we tag the keys that are used on the protocol level,
/// so that they can not be confused with other keys.
/// (TODO: rephrase this)

let key_tag = "P.Key"


(*** Event type ***)

/// We are now using events to show the authentication property.
/// We will have two events for the first two protocol steps,
/// i.e., there is an Initiating event
/// that Alice triggers, when she starts a new run
/// and a Responding event,
/// that Bob triggers, when he replies to a Ping with an Ack.

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
  tag = "P.Event";
  format = mk_parseable_serializeable ps_event_t;
}
