Require Import Coq.Lists.List.
Require Import Coq.Unicode.Utf8_core.
Require Import Coq.Strings.String.
Require Import Coq.Logic.Decidable.

Require Import Medrina.Names.

Import ListNotations.

Open Scope string_scope.
Open Scope char_scope.

(* Many types carry proofs of their properties, and we want to be able
   to treat equality of values of these types as decidable. *)
Require Import Coq.Logic.ProofIrrelevance.

Set Mangle Names.

Inductive attribute_name_t :=
  AttributeName : ∀ s, valid_name s → attribute_name_t.

Lemma attribute_name_eq_dec : ∀ (s0 s1 : attribute_name_t),
  decidable (s0 = s1).
Proof.
  intros s0 s1.
  destruct s0 as [s0s s0p].
  destruct s1 as [s1s s1p].
  destruct (string_dec s0s s1s) as [Hseq|Hsneq]. {
    left.
    destruct Hseq.
    rewrite (proof_irrelevance (valid_name s0s) s0p s1p).
    reflexivity.
  } {
    right.
    intro H_contra.
    injection H_contra.
    assumption.
  }
Qed.

#[global]
Instance attribute_name_textual : textual attribute_name_t := {
  text_of (s : attribute_name_t) :=
    match s with
    | AttributeName t _ => t
    end
}.

Inductive attribute_value_t :=
  AttributeValue : ∀ s, valid_name s → attribute_value_t.

Lemma attribute_value_eq_dec : ∀ (s0 s1 : attribute_value_t),
  decidable (s0 = s1).
Proof.
  intros s0 s1.
  destruct s0 as [s0s s0p].
  destruct s1 as [s1s s1p].
  destruct (string_dec s0s s1s) as [Hseq|Hsneq]. {
    left.
    destruct Hseq.
    rewrite (proof_irrelevance (valid_name s0s) s0p s1p).
    reflexivity.
  } {
    right.
    intro H_contra.
    injection H_contra.
    assumption.
  }
Qed.

#[global]
Instance attribute_value_textual : textual attribute_value_t := {
  text_of (s : attribute_value_t) :=
    match s with
    | AttributeValue t _ => t
    end
}.

Lemma attribute_eq_dec : ∀ (a b : (attribute_name_t * attribute_value_t)),
  decidable (a = b).
Proof.
  intros a b.
  destruct a as [a_name a_value].
  destruct b as [b_name b_value].

  destruct (attribute_name_eq_dec a_name b_name) as [Hn_eq|Hn_neq]. {
    destruct (attribute_value_eq_dec a_value b_value) as [Hv_eq|Hv_neq]. {
      left.
      subst a_name.
      subst a_value.
      reflexivity.
    } {
      right.
      intro H_contra.
      inversion H_contra.
      contradiction.
    }
  } {
    destruct (attribute_value_eq_dec a_value b_value) as [Hv_eq|Hv_neq]. {
      right.
      intro H_contra.
      inversion H_contra.
      contradiction.
    } {
      right.
      intro H_contra.
      inversion H_contra.
      contradiction.
    }
  }
Qed.
