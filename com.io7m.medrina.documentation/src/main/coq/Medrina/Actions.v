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

Inductive action_name_t :=
  ActionName : ∀ s, valid_name s → action_name_t.

Lemma action_name_eq_dec : ∀ (s0 s1 : action_name_t),
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
Instance action_name_textual : textual action_name_t := {
  text_of (s : action_name_t) :=
    match s with
    | ActionName t _ => t
    end
}.

Inductive action_t := Action {
  action_name : action_name_t
}.

Lemma action_eq_dec : ∀ (a0 a1 : action_t),
  decidable (a0 = a1).
Proof.
  intros a0 a1.
  destruct a0 as [a0_name].
  destruct a1 as [a1_name].

  destruct (action_name_eq_dec a0_name a1_name) as [H_eq|H_neq]. {
    left.
    destruct H_eq.
    reflexivity.
  } {
    right.
    intro H_contra.
    inversion H_contra.
    contradiction.
  }
Qed.

Section ActionMatchExpressions.

  Local Unset Elimination Schemes.

  Inductive action_match_expression_t :=
    | AETrue     : action_match_expression_t
    | AEFalse    : action_match_expression_t
    | AEWithName : action_name_t → action_match_expression_t
    | AEAnd      : list action_match_expression_t → action_match_expression_t
    | AEOr       : list action_match_expression_t → action_match_expression_t
    .

  Section rect.
    Variable P              : action_match_expression_t → Type.
    Variable P_list         : list action_match_expression_t → Type.
    Hypothesis P_nil        : P_list [].
    Hypothesis P_cons       : ∀ x xs, P x → P_list xs → P_list (x :: xs).
    Hypothesis P_AETrue     : P AETrue.
    Hypothesis P_AEFalse    : P AEFalse.
    Hypothesis P_AEWithName : ∀ n, P (AEWithName n).
    Hypothesis P_AEAnd      : ∀ es, P_list es → P (AEAnd es).
    Hypothesis P_AEOr       : ∀ es, P_list es → P (AEOr es).

    Fixpoint action_match_expression_t_rect (e : action_match_expression_t) : P e :=
      let
        fix exp_for_all (xs : list action_match_expression_t) : P_list xs :=
          match xs as rxs return (P_list rxs) with
          | []        => @P_nil
          | (y :: ys) => @P_cons y ys (action_match_expression_t_rect y) (exp_for_all ys)
          end
      in
        match e with
        | AETrue       => P_AETrue
        | AEFalse      => P_AEFalse
        | AEWithName n => P_AEWithName n
        | AEAnd es     => P_AEAnd es (exp_for_all es)
        | AEOr es      => P_AEOr es (exp_for_all es)
        end.
  End rect.

  Section ind.
    Variable P              : action_match_expression_t → Prop.
    Hypothesis P_AETrue     : P AETrue.
    Hypothesis P_AEFalse    : P AEFalse.
    Hypothesis P_AEWithName : ∀ n, P (AEWithName n).
    Hypothesis P_AEAnd      : ∀ es, Forall P es → P (AEAnd es).
    Hypothesis P_AEOr       : ∀ es, Forall P es → P (AEOr es).

    Definition action_match_expression_t_ind (e : action_match_expression_t) : P e :=
      action_match_expression_t_rect
        P
        (Forall P)
        (Forall_nil _)
        (λ x xs Px Pxs, Forall_cons _ Px Pxs)
        P_AETrue
        P_AEFalse
        P_AEWithName
        P_AEAnd
        P_AEOr
        e.
  End ind.

End ActionMatchExpressions.

Lemma action_match_expression_eq_dec : forall (e0 e1 : action_match_expression_t),
  decidable (e0 = e1).
Proof.
  intros e0.
  induction e0 as [ | |t|es0 H_fa0|es0 H_fa0]. {
    (* AETrue = ... *)
    intros e1.
    destruct e1.
    left; reflexivity.
    right; discriminate.
    right; discriminate.
    right; discriminate.
    right; discriminate.
  } {
    (* AEFalse = ... *)
    intros e1.
    destruct e1.
    right; discriminate.
    left; reflexivity.
    right; discriminate.
    right; discriminate.
    right; discriminate.
  } {
    (* AEWithName = ... *)
    intros e1.
    destruct e1 as [ | |tr| | ].
    right; discriminate.
    right; discriminate.
    destruct (action_name_eq_dec t tr) as [H_nameeq|H_nameneq]. {
      destruct H_nameeq. left; reflexivity.
    } {
      right; congruence.
    }
    right; discriminate.
    right; discriminate.
  } {
    (* AEAnd = ... *)
    induction es0 as [|x xs H_induction]. {
      intro e1.
      destruct e1 as [ | | |es1|].
      right; discriminate.
      right; discriminate.
      right; discriminate.
      destruct es1 as [|y ys]. {
        left; reflexivity.
      } {
        right; discriminate.
      }
      right; discriminate.
    } {
      intro e1.
      destruct e1 as [ | | |es1|].
      right; discriminate.
      right; discriminate.
      right; discriminate.
      destruct es1 as [|y ys]. {
        right; discriminate.
      } {
        pose proof (Forall_inv H_fa0 y) as H_dec_head.
        pose proof (Forall_inv_tail H_fa0) as H_dec_tail.
        pose proof (H_induction H_dec_tail) as H_dec_xs.
        pose proof (H_dec_xs (AEAnd ys)) as H_dec_ys.

        destruct H_dec_head as [H_head_eq|H_head_neq]. {
          destruct H_dec_ys as [H_tail_eq|H_tail_neq]. {
            left. congruence.
          } {
            right. congruence.
          }
        } {
          destruct H_dec_ys as [H_tail_eq|H_tail_neq]. {
            right. congruence.
          } {
            right. congruence.
          }
        }
      }
      right; discriminate.
    }
  } {
    (* AEOr = ... *)
    induction es0 as [|x xs H_induction]. {
      intro e1.
      destruct e1 as [ | | | |es1].
      right; discriminate.
      right; discriminate.
      right; discriminate.
      right; discriminate.
      destruct es1 as [|y ys]. {
        left; reflexivity.
      } {
        right; discriminate.
      }
    } {
      intro e1.
      destruct e1 as [ | | | |es1].
      right; discriminate.
      right; discriminate.
      right; discriminate.
      right; discriminate.
      destruct es1 as [|y ys]. {
        right; discriminate.
      } {
        pose proof (Forall_inv H_fa0 y) as H_dec_head.
        pose proof (Forall_inv_tail H_fa0) as H_dec_tail.
        pose proof (H_induction H_dec_tail) as H_dec_xs.
        pose proof (H_dec_xs (AEOr ys)) as H_dec_ys.

        destruct H_dec_head as [H_head_eq|H_head_neq]. {
          destruct H_dec_ys as [H_tail_eq|H_tail_neq]. {
            left. congruence.
          } {
            right. congruence.
          }
        } {
          destruct H_dec_ys as [H_tail_eq|H_tail_neq]. {
            right. congruence.
          } {
            right. congruence.
          }
        }
      }
    }
  }
Qed.

Fixpoint action_match_evaluate
  (a : action_t)
  (e : action_match_expression_t)
: bool :=
  match e with
  | AETrue        => true
  | AEFalse       => false
  | AEWithName n  => eqb (text_of n) (text_of (action_name a))
  | AEAnd es      => List.fold_right (λ e acc, andb acc (action_match_evaluate a e)) true es
  | AEOr es       => List.fold_right (λ e acc, orb acc (action_match_evaluate a e)) false es
  end.
