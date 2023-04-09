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

(** The type of attribute names. *)
Record attributeName := ANMake {
  (** The name of the attribute. *)
  anName  : string;
  (** Attribute names are valid. *)
  anValid : validName anName
}.

Require Import Coq.Logic.ProofIrrelevance.

(** Equality of attribute names is decidable. *)
Theorem attributeNameDec : forall (a b : attributeName),
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

(** The type of attribute values. *)
Record attributeValue := AVMake {
  (** The value of the attribute. *)
  avValue : string;
  (** Attribute values are valid. *)
  avValid : validName avValue
}.

(** Equality of attribute values is decidable. *)
Theorem attributeValueDec : forall (a b : attributeValue),
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

Require Import Coq.FSets.FMapInterface.
Require Import Coq.FSets.FMapWeakList.
Require Import Coq.FSets.FMapFacts.
Require Import Coq.Structures.Equalities.

(** A mini decidable type module to instantiate maps. *)
Module AttributeNameMiniDec : MiniDecidableType
  with Definition t := attributeName.

  Definition t        := attributeName.
  Definition eq       := @Logic.eq t.
  Definition eq_refl  := @Logic.eq_refl t.
  Definition eq_sym   := @Logic.eq_sym t.
  Definition eq_trans := @Logic.eq_trans t.

  Theorem eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
  Proof. apply attributeNameDec. Qed.
End AttributeNameMiniDec.

(** A usual decidable type module to instantiate maps. *)
Module AttributeNameDec <: UsualDecidableType
  with Definition t := attributeName
  with Definition eq := @Logic.eq attributeName
:= Make_UDT AttributeNameMiniDec.

(** A Maps module with attribute name keys. *)
Module AttributeNameMaps : FMapInterface.WS
  with Definition E.t  := attributeName
  with Definition E.eq := @Logic.eq attributeName
:= FMapWeakList.Make AttributeNameDec.

Module AttributeNameMapsFacts :=
  Facts AttributeNameMaps.
