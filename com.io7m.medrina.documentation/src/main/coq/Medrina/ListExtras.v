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
