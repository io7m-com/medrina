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

Inductive type_name_t :=
  TypeName : ∀ s, valid_name s → type_name_t.

Lemma type_name_eq_dec : ∀ (s0 s1 : type_name_t),
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
Instance type_name_textual : textual type_name_t := {
  text_of (s : type_name_t) :=
    match s with
    | TypeName t _ => t
    end
}.
