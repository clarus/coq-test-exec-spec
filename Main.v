Require Import Coq.NArith.NArith.
Require Import ListString.All.

Local Open Scope type.

(** External calls. *)
Module Command.
  Inductive t :=
  | AskCard
  | AskPIN
  | CheckPIN (pin : N)
  | AskAmount
  | CheckAmount (amount : N)
  | GiveCard
  | GiveAmount (amount : N)
  | ShowError (message : LString.t).

  (** The type of an answer for a command depends on the value of the command. *)
  Definition answer (command : t) : Type :=
    match command with
    | AskCard => bool (* If the given card seems valid. *)
    | AskPIN => option N (* A number or cancellation. *)
    | CheckPIN _ => bool (* If the PIN number is valid. *)
    | AskAmount => option N (* A number or cancellation. *)
    | CheckAmount _ => bool (* If the amount can be withdrawn. *)
    | GiveCard => bool (* If the card was given. *)
    | GiveAmount _ => bool (* If the money was given. *)
    | ShowError _ => unit (* Show an error message. *)
    end.
End Command.

(** Computations with I/Os. *)
Module C.
  (** A computation can either does nothing, or do a system call and wait
      for the answer to run another computation. *)
  Inductive t : Type :=
  | Ret : t
  | Call : forall (command : Command.t), (Command.answer command -> t) -> t.
  Arguments Ret.
  Arguments Call _ _.
End C.
