Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import ListString.All.

Import ListNotations.
Local Open Scope char.
Local Open Scope type.

(** External calls. *)
Module Command.
  Inductive t :=
  | Log (message : LString.t)
  | ReadX
  | WriteX (value : LString.t)
  | ReadY
  | WriteY (value : LString.t)
  | Read
  | Write (values : LString.t * LString.t)
  | Error.

  (** The type of an answer for a command depends on the value of the command. *)
  Definition answer (command : t) : Type :=
    match command with
    | Log _ => unit
    | ReadX => LString.t
    | WriteX _ => unit
    | ReadY => LString.t
    | WriteY _ => unit
    | Read => LString.t * LString.t
    | Write _ => unit
    | Error => Empty_set
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

  Module OneRead.
    Definition read_and_print : C.t unit :=
      call! s := Command.ReadX in
      do_call! Command.Log s in
      ret tt.

    Fixpoint exec {A : Type} (x : C.t A) (s : LString.t) : C.t A :=
      match x with
      | C.Ret _ => x
      | C.Call Command.ReadX handler => exec (handler s) s
      | C.Call command handler => C.Call command (fun answer =>
        exec (handler answer) s)
      end.

    Compute exec read_and_print (LString.s "hello").
  End OneRead.

  Module WritesReads.
    Definition writes_reads : C.t unit :=
      do_call! Command.WriteX (LString.s "hello") in
      do_call! Command.WriteY (LString.s "world") in
      call! s_x := Command.ReadX in
      call! s_y := Command.ReadY in
      do_call! Command.Log s_x in
      do_call! Command.Log s_y in
      ret tt.

    Fixpoint exec {A : Type} (x : C.t A) : C.t A :=
      match x with
      | C.Ret _ => x
      | C.Call Command.ReadX handler =>
        call! s := Command.Read in
        exec (handler (fst s))
      | C.Call Command.ReadY handler =>
        call! s := Command.Read in
        exec (handler (snd s))
      | C.Call (Command.WriteX s_x) handler =>
        call! s := Command.Read in
        do_call! Command.Write (s_x, snd s) in
        exec (handler tt)
      | C.Call (Command.WriteY s_y) handler =>
        call! s := Command.Read in
        do_call! Command.Write (fst s, s_y) in
        exec (handler tt)
      | C.Call command handler =>
        call! answer := command in
        exec (handler answer)
      end.

    Compute exec writes_reads.
  End WritesReads.

  Module Exception.
    Definition error {A : Type} : C.t A :=
      call! e := Command.Error in
      match e with end.

    Definition test_non_empty (s : LString.t) : C.t LString.t :=
      match s with
      | [] => error
      | _ => ret s
      end.

    Fixpoint exec {A : Type} (x : C.t A) : C.t (option A) :=
      match x with
      | C.Ret x => C.Ret (Some x)
      | C.Call Command.Error _ => C.Ret None
      | C.Call command handler =>
        call! answer := command in
        exec (handler answer)
      end.

    Compute exec (test_non_empty (LString.s "hello")).
    Compute exec (test_non_empty (LString.s "")).
  End Exception.
End Example.
