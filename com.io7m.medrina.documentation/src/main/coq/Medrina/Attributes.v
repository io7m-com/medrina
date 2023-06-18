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
Require Import Coq.Logic.FunctionalExtensionality.

Require Import com.io7m.lanark.core.Lanark.

(** The type of attribute names. *)
Record attributeName := ANMake {
  (** The name of the attribute. *)
  anName  : name;
  (** Attribute names are valid. *)
  anValid : nameValid anName
}.

Require Import Coq.Logic.ProofIrrelevance.

(** Equality of attribute names is decidable. *)
Theorem attributeNameDec : forall (a b : attributeName),
  {a = b}+{a <> b}.
Proof.
  intros a b.
  destruct a as [a0 a1].
  destruct b as [b0 b1].
  destruct (nameDec a0 b0) as [H0|H1]. {
    subst b0.
    left.
    assert (a1 = b1) by apply proof_irrelevance. subst b1.
    reflexivity.
  } {
    right.
    congruence.
  }
Qed.

(** The type of attribute values. *)
Record attributeValue := AVMake {
  (** The value of the attribute. *)
  avValue : name;
  (** Attribute values are valid. *)
  avValid : nameValid avValue
}.

(** Equality of attribute values is decidable. *)
Theorem attributeValueDec : forall (a b : attributeValue),
  {a = b}+{a <> b}.
Proof.
  intros a b.
  destruct a as [a0 a1].
  destruct b as [b0 b1].
  destruct (nameDec a0 b0) as [H0|H1]. {
    subst b0.
    left.
    assert (a1 = b1) by apply proof_irrelevance. subst b1.
    reflexivity.
  } {
    right.
    congruence.
  }
Qed.

(** Boolean equality of attribute values. *)
Definition attributeValueBool (a b : attributeValue) : bool :=
  match attributeValueDec a b with
  | left _  => true
  | right _ => false
  end.

Theorem attributeValueBoolDecT : forall (a b : attributeValue),
  a = b <-> attributeValueBool a b = true.
Proof.
  intros a b.
  split. {
    intros Heq.
    subst b.
    unfold attributeValueBool.
    destruct (attributeValueDec a a) eqn:Hdec.
      - reflexivity.
      - contradiction.
  } {
    unfold attributeValueBool.
    destruct (attributeValueDec a b).
      - intros. auto.
      - intros H0. contradict H0. discriminate.
  }
Qed.

Theorem attributeValueBoolDecF : forall (a b : attributeValue),
  a <> b <-> attributeValueBool a b = false.
Proof.
  intros a b.
  split. {
    intros Heq.
    unfold attributeValueBool.
    destruct (attributeValueDec a b) eqn:Hdec.
      - contradiction.
      - reflexivity.
  } {
    unfold attributeValueBool.
    destruct (attributeValueDec a b).
      - intros H0. contradict H0. discriminate.
      - intros. auto.
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

Lemma AttributeNameMapsEqEquiv :
  Equivalence (AttributeNameMaps.eq_key_elt (elt:=attributeValue)).
Proof.
  unfold AttributeNameMaps.eq_key_elt.
  constructor. {
    constructor; reflexivity.
  } {
    intros x y [Heq0 Heq1].
    symmetry in Heq0.
    symmetry in Heq1.
    intuition.
  } {
    intros x y z [Heq0 Heq1] [Heq2 Heq3].
    rewrite Heq1.
    rewrite Heq3.
    rewrite <- Heq2.
    rewrite Heq0.
    constructor; reflexivity.
  }
Qed.

Lemma AttributeNameMapsEqLeibniz : forall p0 p1,
  AttributeNameMaps.eq_key_elt (elt:=attributeValue) p0 p1 <-> p0 = p1.
Proof.
  unfold AttributeNameMaps.eq_key_elt.
  intros p0.
  intros p1.
  destruct p0 as [p0k p0v].
  destruct p1 as [p1k p1v].
  simpl.
  unfold AttributeNameMaps.E.eq.
  split. {
    intros [Heq0 Heq1].
    subst p0k.
    subst p0v.
    reflexivity.
  } {
    intros Heq0.
    assert (p0k = p1k) by congruence.
    assert (p0v = p1v) by congruence.
    intuition.
  }
Qed.

Lemma attributesEmptyElements :
  AttributeNameMaps.elements (AttributeNameMaps.empty attributeValue) = nil.
Proof.
  destruct (AttributeNameMaps.elements (AttributeNameMaps.empty _)) eqn:H. {
    reflexivity.
  } {
    assert (In p (AttributeNameMaps.elements (AttributeNameMaps.empty _))) as Hin. {
      rewrite H. intuition.
    }
    assert (InA
      (AttributeNameMaps.eq_key_elt (elt:=attributeValue)) 
      p 
      (AttributeNameMaps.elements (AttributeNameMaps.empty attributeValue))
    ) as H0. {
      apply In_InA.
      exact AttributeNameMapsEqEquiv.
      exact Hin.
    }
    destruct p as [k v].
    rewrite <- AttributeNameMapsFacts.elements_mapsto_iff in H0.
    rewrite AttributeNameMapsFacts.empty_mapsto_iff in H0.
    contradiction.
  }
Qed.

