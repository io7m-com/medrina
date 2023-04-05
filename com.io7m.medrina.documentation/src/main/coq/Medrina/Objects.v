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
Require Import Medrina.Attributes.
Require Import Medrina.Names.

(** The type of attribute names. *)
Record typeName := TNMake {
  (** The name of the type. *)
  tnName  : string;
  (** Type names are valid. *)
  tnValid : validName tnName
}.

Require Import Coq.Logic.ProofIrrelevance.

(** Equality of type names is decidable. *)
Theorem typeNameDec : forall (a b : typeName),
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
Theorem typeNameIrrelevance : forall (a b : typeName),
  tnName a = tnName b -> a = b.
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
Instance typeNameName : IsValidName typeName := {
  ivName            := tnName;
  ivValid           := tnValid;
  ivIrrelevantEqual := typeNameIrrelevance
}.

(** The type of objects. *)
Record object := OMake {
  (** The object type name. *)
  oType : typeName;
  (** The attributes held by the object. *)
  oAttributes : AttributeNameMaps.t attributeValue
}.

