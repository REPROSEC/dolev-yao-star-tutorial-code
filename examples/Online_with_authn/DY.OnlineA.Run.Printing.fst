module DY.OnlineA.Run.Printing

open DY.Core
open DY.Lib
open Comparse

open DY.OnlineA.Data

/// Helper functions for trace printing.
/// Here we define how our abstract message, state and event types
/// should be printed.

val message_to_string: bytes -> option string
let message_to_string b =
  match? parse message_t b with
  | Ping p -> Some (Printf.sprintf "Ping [name = (%s), n_a = (%s)]" (p.alice) (bytes_to_string p.n_a))
  | Ack a -> Some (Printf.sprintf "Ack [n_a = (%s)]" (bytes_to_string a.n_a))

val state_to_string: bytes -> option string
let state_to_string b =
  match? parse state_t b with
  | SentPing p -> Some (Printf.sprintf "SentPing [n_a = (%s), to = (%s)]" (bytes_to_string p.n_a) p.bob)
  | SentAck a -> Some (Printf.sprintf "SentAck [n_a = (%s), to = (%s)]" (bytes_to_string a.n_a) a.alice)
  | ReceivedAck r -> Some (Printf.sprintf "ReceivedAck [n_a = (%s), from = (%s)]" (bytes_to_string r.n_a) r.bob)

val event_to_string: bytes -> option string
let event_to_string b =
  match? parse event_t b with
  | Initiating {alice; bob; n_a} -> Some (Printf.sprintf "Initiating [alice = (%s), n_a = (%s), to = (%s)]" alice (bytes_to_string n_a) bob)
  | Responding {alice; bob; n_a} -> Some (Printf.sprintf "Responding [bob = (%s), n_a = (%s), to = (%s)]" bob (bytes_to_string n_a) alice)
  | Finishing {alice; bob; n_a} -> Some (Printf.sprintf "Finishing [alice = (%s), n_a = (%s), with = (%s)]" alice (bytes_to_string n_a) bob)
  

val get_trace_to_string_printers: trace_to_string_printers
let get_trace_to_string_printers  = 
  trace_to_string_printers_builder 
    message_to_string
    [(local_state_state_t.tag, state_to_string)]
    [(event_event_t.tag, event_to_string)]
