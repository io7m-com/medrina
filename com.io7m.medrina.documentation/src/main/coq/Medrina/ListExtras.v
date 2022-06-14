Require Import Coq.Lists.List.
Require Import Coq.Unicode.Utf8_core.
Require Import Coq.Logic.Decidable.

Import ListNotations.

Lemma list_eq_dec : ∀ {A : Type}, (∀ x y : A, decidable (x = y)) →
  ∀ xs ys : list A, decidable (xs = ys).
Proof.
  intros A Heqdec.
  intros xs.
  induction xs as [|x xxs H_xind]. {
    intros ys.
    destruct ys.
      left; reflexivity.
      right; discriminate.
  } {
    intros ys.
    destruct ys as [|y yys]. {
      right; discriminate.
    } {
      destruct (H_xind yys) as [H_resteq|H_restneq]. {
        destruct H_resteq.
        destruct (Heqdec x y) as [H_headeq|H_headneq]. {
          destruct H_headeq.
          left; reflexivity.
        } {
          right; congruence.
        }
      } {
        right; congruence.
      }
    }
  }
Qed.

Lemma firstn_one : ∀ {A : Type} (m : nat) (x : A),
  firstn (S m) [x] = [x].
Proof.
  intros A m x.
  simpl.
  rewrite firstn_nil.
  reflexivity.
Qed.

Lemma cons_nil_head_eq : ∀ (A : Type) (x y : A) (ys : list A),
  x :: [] = y :: ys →
    ys = [] ∧ x = y.
Proof.
  intros A x y ys H_eq.
  constructor.
  induction ys as [|z zs]. {
    reflexivity.
  } {
    contradict H_eq.
    discriminate.
  }
  induction ys as [|z zs]. {
    inversion H_eq.
    reflexivity.
  } {
    contradict H_eq.
    discriminate.
  }
Qed.

Lemma head_non_empty : ∀ (A : Type) (xs : list A),
  [] ≠ xs → A.
Proof.
  intros A xs H_neq.
  destruct xs as [|x].
    contradict H_neq.
    reflexivity.
    exact x.
Qed.

Lemma list_in_one_both_eq : ∀ (A : Type) (x y z : A),
  List.In x (z :: []) →
    List.In y (z :: []) →
      x = y.
Proof.
  intros A x y z H_inx H_iny.
  assert ((z = x) ∨ (List.In x [])) as H_inv0
    by (apply (in_inv H_inx)).
  assert ((z = y) ∨ (List.In y [])) as H_inv1
    by (apply (in_inv H_iny)).
  inversion H_inv0. {
    inversion H_inv1. {
      subst x.
      subst y.
      reflexivity.
    } {
      contradiction.
    }
  } {
    contradiction.
  }
Qed.
