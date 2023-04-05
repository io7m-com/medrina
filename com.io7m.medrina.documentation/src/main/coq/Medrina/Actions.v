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

Require Import Coq.Strings.String.
Require Import Medrina.Names.

(** The type of action names. *)
Record actionName := ANMake {
  (** The name of the action. *)
  anName  : string;
  (** Action names are valid. *)
  anValid : validName anName
}.

Require Import Coq.Logic.ProofIrrelevance.

(** Equality of action names is decidable. *)
Theorem actionNameDec : forall (a b : actionName),
  {a = b}+{a <> b}.
Proof.
  intros a b.
  destruct a as [a0 [a1 [a2 a3]]].
  destruct b as [b0 [b1 [b2 b3]]].
  destruct (string_dec a0 b0) as [H0|H1]. {
    subst b0.
    left.
    assert (a1 = b1) by apply proof_irrelevance. subst b1.
    assert (a2 = b2) by apply proof_irrelevance. subst b2.
    assert (a3 = b3) by apply proof_irrelevance. subst b3.
    intuition.
  } {
    right.
    congruence.
  }
Qed.

(** Proof irrelevance allows for equality between instances with equal names. *)
Theorem actionNameIrrelevance : forall (a b : actionName),
  anName a = anName b -> a = b.
Proof.
  intros a b Heq.
  destruct a as [a0 a1].
  destruct b as [b0 b1].
  simpl in Heq.
  subst b0.
  assert (a1 = b1) by apply proof_irrelevance.
  subst b1.
  reflexivity.
Qed.

#[export]
Instance actionNameName : IsValidName actionName := {
  ivName            := anName;
  ivValid           := anValid;
  ivIrrelevantEqual := actionNameIrrelevance
}.

(** The type of actions. *)
Record action : Set := AMake {
  aName : actionName
}.
