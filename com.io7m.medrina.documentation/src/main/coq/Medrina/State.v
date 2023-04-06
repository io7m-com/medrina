(*
 * Copyright © 2023 Mark Raynsford <code@io7m.com> https://www.io7m.com
 *
 * Permission to use, copy, modify, and/or distribute this software for any
 * purpose with or without fee is hereby granted, provided that the above
 * copyright notice and this permission notice appear in all copies.
 *
 * THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 * WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY
 * SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 * WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 * ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF OR
 * IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 *)

(** An abstract specification of a state monad. *)
Module Type StateT.

  (** The type of monadic computations. *)
  Parameter t : Type -> Type -> Type.

  (** The "return" function that injects a result into a computation. *)
  Parameter ret : forall {S A : Type},
    A -> t S A.

  (** The functor map function. *)
  Parameter map : forall {S A B : Type},
    t S A -> (A -> B) -> t S B. 

  (** The monadic bind function. *)
  Parameter bind : forall {S A B : Type},
    t S A -> (A -> t S B) -> t S B. 

  (** The left identity monad law. *)
  Parameter leftIdentity : forall (A B S : Type) (a : A) (f : A -> t S B),
    bind (ret a) f = f a.

  (** The right identity monad law. *)
  Parameter rightIdentity : forall (A S : Type) (a : t S A),
    bind a ret = a.

  (** The associativity monad law. *)
  Parameter associativity : forall (A B C S : Type) (a : t S A) (f : A -> t S B) (g : B -> t S C),
    bind (bind a f) g = bind a (fun x => bind (f x) g).

  (** A computation that has its own state set to _s_. *)
  Parameter put : forall {S : Type} (s : S),
    t S unit.

  (** A computation that returns its own state value. *)
  Parameter get : forall {S : Type},
    t S S.

  (** Evaluate the given computation with the given initial state value. *)
  Parameter eval : forall {A S : Type},
    S -> t S A -> A.

  (** An identity between _eval_ and _ret_. *)
  Parameter evalRetId : forall {A S : Type} (s : S) (x : A),
    eval s (ret x) = x.

  (** Evaluate the given computation with the given initial state value and return the state. *)
  Parameter evalState : forall {A S : Type},
    S -> t S A -> S.

  (** An identity between _evalState_ and _put_. *)
  Parameter evalStatePutId : forall {A S : Type} (s t : S),
    evalState s (put t) = t.

End StateT.

Require Import Coq.Logic.FunctionalExtensionality.

(** A state monad implementation. *)
Module State <: StateT.

  Record state (S A : Type) : Type := St {
    runState : S -> A * S
  }.

  Definition t : Type -> Type -> Type := state.

  Definition ret
    {S A : Type}
    (x   : A)
  : t S A :=
    St _ _ (fun s => (x, s)).

  Definition map
    {S A B : Type}
    (m     : t S A)
    (f     : A -> B)
  : t S B :=
    St S B (fun s0 =>
      match m with
      | St _ _ p0 => let (r0, s1) := p0 s0 in (f r0, s1)
      end
    ).

  Definition bind
    {S A B : Type}
    (m0    : t S A)
    (f     : A -> t S B)
  : t S B :=
    St S B (fun s0 =>
      let (r0, s1) := runState _ _ m0 s0 in
        runState _ _ (f r0) s1).

  Theorem leftIdentity : forall (A B S : Type) (a : A) (f : A -> t S B),
    bind (ret a) f = f a.
  Proof.
    intros A B S a f.
    cbv.
    destruct (f a).
    reflexivity.
  Qed.

  Theorem rightIdentity : forall (A S : Type) (a : t S A),
    bind a ret = a.
  Proof.
    intros A S a.
    destruct a.
    cbv.
    f_equal.
    extensionality s.
    destruct (runState0 s).
    reflexivity.
  Qed.

  Theorem associativity : forall (A B C S : Type) (a : t S A) (f : A -> t S B) (g : B -> t S C),
    bind (bind a f) g = bind a (fun x => bind (f x) g).
  Proof.
    intros A B C S a f g.
    destruct a.
    cbv.
    f_equal.
    extensionality s.
    destruct (runState0 s).
    reflexivity.
  Qed.

  Definition put
    {S : Type}
    (s : S)
  : t S unit :=
    St _ _ (fun _ => (tt, s)).

  Definition get
    {S : Type}
  : t S S :=
    St _ _ (fun s => (s, s)).

  Definition eval
    {A S : Type}
    (s   : S)
    (m   : t S A)
  : A :=
    fst (runState _ _ m s).

  Definition evalState
    {A S : Type}
    (s   : S)
    (m   : t S A)
  : S :=
    snd (runState _ _ m s).

  Theorem evalRetId : forall {A S : Type} (s : S) (x : A),
    eval s (ret x) = x.
  Proof. reflexivity. Qed.

  Theorem evalStatePutId : forall {A S : Type} (s t : S),
    evalState s (put t) = t.
  Proof. reflexivity. Qed.

End State.

Require Import Coq.Lists.List.

(** A module for performing stateful iteration. *)
Module StateIteration (St : StateT).

  Import ListNotations.

  Inductive halt :=
    | HContinue
    | HHalt
    .

  (** Iterate over _xs_, executing _f_ for each element of _xs_.
      If _f_ returns _HHalt_, the iteration is finished early. *)
  Fixpoint iterate
    {A S : Type}
    (xs  : list A)
    (f   : A -> St.t S halt)
  : St.t S halt :=
    match xs with
    | []      => St.ret HHalt
    | x :: xs =>
      St.bind (f x) (fun h =>
        match h with
        | HContinue => iterate xs f
        | HHalt     => St.ret HHalt
        end)
    end.

End StateIteration.
