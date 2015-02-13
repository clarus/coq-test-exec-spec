Require Import Coq.Strings.Ascii.
Require Import ListString.All.

Local Open Scope char.
Local Open Scope type.

(** External calls. *)
Module Command.
  Inductive t :=
  | Log (message : LString.t)
  | Read
  | Write (value : LString.t).

  (** The type of an answer for a command depends on the value of the command. *)
  Definition answer (command : t) : Type :=
    match command with
    | Log _ => unit
    | Read => LString.t
    | Write _ => unit
    end.
End Command.

(** Computations with I/Os. *)
Module C.
  (** A computation can either return a pure value, or do a system call and wait
      for the answer to run another computation. *)
  Inductive t (A : Type) : Type :=
  | Ret : forall (x : A), t A
  | Call : forall (command : Command.t), (Command.answer command -> t A) -> t A.
  Arguments Ret {A} _.
  Arguments Call {A} _ _.

  (** Some optional notations. *)
  Module Notations.
    (** A nicer notation for `Ret`. *)
    Definition ret {A : Type} (x : A) : t A :=
      Ret x.

    (** We define an explicit apply function so that Coq does not try to expand
        the notations everywhere. *)
    Definition apply {A B} (f : A -> B) (x : A) := f x.

    (** System call. *)
    Notation "'call!' answer ':=' command 'in' X" :=
      (Call command (fun answer => X))
      (at level 200, answer ident, command at level 100, X at level 200).

    (** System call with typed answer. *)
    Notation "'call!' answer : A ':=' command 'in' X" :=
      (Call command (fun (answer : A) => X))
      (at level 200, answer ident, command at level 100, A at level 200, X at level 200).

    (** System call ignoring the answer. *)
    Notation "'do_call!' command 'in' X" :=
      (Call command (fun _ => X))
      (at level 200, command at level 100, X at level 200).

    (** This notation is useful to compose computations which wait for a
        continuation. We do not have an explicit bind operator to simplify the
        language and the proofs. *)
    Notation "'let!' x ':=' X 'in' Y" :=
      (apply X (fun x => Y))
      (at level 200, x ident, X at level 100, Y at level 200).

    (** Let with a typed answer. *)
    Notation "'let!' x : A ':=' X 'in' Y" :=
      (apply X (fun (x : A) => Y))
      (at level 200, x ident, X at level 100, A at level 200, Y at level 200).

    (** Let ignoring the answer. *)
    Notation "'do_let!' X 'in' Y" :=
      (apply X (fun _ => Y))
      (at level 200, X at level 100, Y at level 200).
  End Notations.
End C.

Module Example.
  Import C.Notations.

  Definition read_and_print : C.t unit :=
    call! s := Command.Read in
    do_call! Command.Log s in
    ret tt.

  Fixpoint constant_read {A : Type} (x : C.t A) (s : LString.t) : C.t A :=
    match x with
    | C.Ret _ => x
    | C.Call Command.Read handler => constant_read (handler s) s
    | C.Call command handler => C.Call command (fun answer =>
      constant_read (handler answer) s)
    end.

  Compute constant_read read_and_print (LString.s "hello").
End Example.
