Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import Coq.Logic.Decidable.

Import ListNotations.

Require Import Coq.Unicode.Utf8_core.

Set Mangle Names.

Lemma Forall_lt_trans : ∀ ys x y ,
  Forall (λ z, y < z) ys →
    x < y →
      Forall (λ z, x < z) ys.
Proof.
  intros ys.
  induction ys as [|m ms H_induction]. {
    intros. constructor.
  } {
    intros x y Hfa Hlt.
    inversion Hfa as [|q qs Hym Hfay [Heq0 Heq1]].
    constructor.
    apply (Nat.lt_trans x y m Hlt Hym).
    apply (H_induction x y Hfay Hlt).
  }
Qed.

Lemma Forall_lt_trans_map : ∀ (A : Type) (f : A → nat) ys x y ,
  Forall (λ z, f y < f z) ys →
    f x < f y →
      Forall (λ z, f x < f z) ys.
Proof.
  intros A f ys.
  induction ys as [|m ms H_induction]. {
    intros. constructor.
  } {
    intros x y Hfa Hlt.
    inversion Hfa as [|q qs Hym Hfay [Heq0 Heq1]].
    constructor.
    apply (Nat.lt_trans (f x) (f y) (f m) Hlt Hym).
    apply (H_induction x y Hfay Hlt).
  }
Qed.

Lemma Forall_neq_not_in : ∀ (A : Type) (xs : list A) x,
  Forall (λ y, x ≠ y) xs →
    ¬ In x xs.
Proof.
  intros A xs.
  induction xs as [|y ys H_induction]. {
    intros.
    intro H_contra.
    contradiction.
  } {
    intros x Hfa.
    inversion Hfa as [|z zs Hneq Hfneq [Heq0 Heq1]].
    assert (¬ In x ys) as H_ninx
      by (apply (H_induction _ Hfneq)).

    intro H_contra.
    assert ((y = x) \/ (In x ys)) as H_both_false
      by (apply (in_inv H_contra)).

    destruct H_both_false as [Heq|Hin]. {
      symmetry in Heq.
      contradiction.
    } {
      contradiction.
    }
  }
Qed.

Lemma Forall_list_eq_dec : ∀ {A : Type} (xs ys : list A),
  Forall (λ a : A, (∀ b : A, (decidable (a = b)))) xs →
    Forall (λ a : A, (∀ b : A, (decidable (a = b)))) ys →
      decidable (xs = ys).
Proof.
  intros A xs.
  induction xs as [|x xxs H_xind]. {
    intros ys H_xfa H_yfa.
    destruct ys as [|y yys]. {
      left; reflexivity.
    } {
      right; discriminate.
    }
  } {
    intros ys H_xfa H_yfa.
    destruct ys as [|y yys]. {
      right; discriminate.
    } {
      inversion H_xfa as [|xa xsa H_xdec H_faxs [H_xeq0 H_xeq1]].
      inversion H_yfa as [|ya ysa H_ydec H_fays [H_yeq0 H_yeq1]].
      destruct H_xeq0.
      destruct H_xeq1.
      destruct H_yeq0.
      destruct H_yeq1.
      destruct (H_xdec ya) as [H_headeq|H_headneq]. {
        destruct H_headeq.
        destruct (H_xind _ H_faxs H_fays) as [H_resteq|H_restneq]. {
          destruct H_resteq.
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
