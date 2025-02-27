module DY.TwoMessage.Data

open Comparse
open DY.Core
open DY.Lib

/// Here we define the abstract types for the simple Two-Message protocol:
/// 
/// A -> B: Ping (A, n_A)
/// B -> A: Ack n_A


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
  | Ping: ping_t -> message_t
  | Ack: ack_t -> message_t


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

instance local_state_state_t: local_state state_t = {
  tag = "TwoMessage.State";
  format = parseable_serializeable_bytes_state_t;
}
