Require Import Coq.Lists.List.
Require Import Coq.Unicode.Utf8_core.
Require Import Coq.Strings.String.
Require Import Coq.Logic.Decidable.

Require Import Medrina.Attributes.
Require Import Medrina.Names.
Require Import Medrina.ListExtras.
Require Import Medrina.Types.

Import ListNotations.

Open Scope string_scope.
Open Scope char_scope.

(* Many types carry proofs of their properties, and we want to be able
   to treat equality of values of these types as decidable. *)
Require Import Coq.Logic.ProofIrrelevance.

Set Mangle Names.

Inductive object_t := Object {
  object_type             : type_name_t;
  object_attributes       : list (attribute_name_t * attribute_value_t);
  object_attributes_names : NoDup (map fst object_attributes);
}.

Lemma object_eq_dec : ∀ (o0 o1 : object_t),
  decidable (o0 = o1).
Proof.
  intros o0 o1.
  destruct o0 as [o0_type o0_attr o0_p].
  destruct o1 as [o1_type o1_attr o1_p].

  destruct (type_name_eq_dec o0_type o1_type) as [H_oeq|H_oneq]. {
    destruct (list_eq_dec attribute_eq_dec o0_attr o1_attr) as [H_aeq|H_aneq]. {
      left.
      destruct H_oeq.
      destruct H_aeq.
      rewrite (proof_irrelevance _ o0_p o1_p).
      reflexivity.
    } {
      right.
      intro H_contra.
      inversion H_contra.
      contradiction.
    }
  } {
    destruct (list_eq_dec attribute_eq_dec o0_attr o1_attr) as [H_aeq|H_aneq]. {
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

Section ObjectMatchExpressions.

  Local Unset Elimination Schemes.

  Inductive object_match_expression_t :=
    | OETrue     : object_match_expression_t
    | OEFalse    : object_match_expression_t
    | OEWithType : type_name_t → object_match_expression_t
    | OEAnd      : list object_match_expression_t → object_match_expression_t
    | OEOr       : list object_match_expression_t → object_match_expression_t
    .

  Section rect.
    Variable P              : object_match_expression_t → Type.
    Variable P_list         : list object_match_expression_t → Type.
    Hypothesis P_nil        : P_list [].
    Hypothesis P_cons       : ∀ x xs, P x → P_list xs → P_list (x :: xs).
    Hypothesis P_OETrue     : P OETrue.
    Hypothesis P_OEFalse    : P OEFalse.
    Hypothesis P_OEWithType : ∀ t, P (OEWithType t).
    Hypothesis P_OEAnd      : ∀ es, P_list es → P (OEAnd es).
    Hypothesis P_OEOr       : ∀ es, P_list es → P (OEOr es).

    Fixpoint object_match_expression_t_rect (e : object_match_expression_t) : P e :=
      let
        fix exp_for_all (xs : list object_match_expression_t) : P_list xs :=
          match xs as rxs return (P_list rxs) with
          | []        => @P_nil
          | (y :: ys) => @P_cons y ys (object_match_expression_t_rect y) (exp_for_all ys)
          end
      in
        match e with
        | OETrue       => P_OETrue
        | OEFalse      => P_OEFalse
        | OEWithType t => P_OEWithType t
        | OEAnd es     => P_OEAnd es (exp_for_all es)
        | OEOr es      => P_OEOr es (exp_for_all es)
        end.
  End rect.

  Section ind.
    Variable P              : object_match_expression_t → Prop.
    Hypothesis P_OETrue     : P OETrue.
    Hypothesis P_OEFalse    : P OEFalse.
    Hypothesis P_OEWithType : ∀ t, P (OEWithType t).
    Hypothesis P_OEAnd      : ∀ es, Forall P es → P (OEAnd es).
    Hypothesis P_OEOr       : ∀ es, Forall P es → P (OEOr es).

    Definition object_match_expression_t_ind (e : object_match_expression_t) : P e :=
      object_match_expression_t_rect
        P
        (Forall P)
        (Forall_nil _)
        (λ x xs Px Pxs, Forall_cons _ Px Pxs)
        P_OETrue
        P_OEFalse
        P_OEWithType
        P_OEAnd
        P_OEOr
        e.
  End ind.

End ObjectMatchExpressions.

Lemma object_match_expression_eq_dec : forall (e0 e1 : object_match_expression_t),
  decidable (e0 = e1).
Proof.
  intros e0.
  induction e0 as [ | |t0|es0 H_fa0|es0 H_fa0]. {
    intros e1.
    destruct e1.
    left; reflexivity.
    right; discriminate.
    right; discriminate.
    right; discriminate.
    right; discriminate.
  } {
    intros e1.
    destruct e1.
    right; discriminate.
    left; reflexivity.
    right; discriminate.
    right; discriminate.
    right; discriminate.
  } {
    intros e1.
    destruct e1 as [ | |t1|es1|es1].
    right; discriminate.
    right; discriminate.
    destruct (type_name_eq_dec t0 t1) as [H_teq|H_tneq]. {
      destruct H_teq.
      left; reflexivity.
    } {
      right. intro H_contra. inversion H_contra. contradiction.
    }
    right; discriminate.
    right; discriminate.
  } {
    induction es0 as [|x xs H_induction]. {
      intro e1.
      destruct e1 as [ | |t1|es1|es1].
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
      destruct e1 as [ | |t1|es1|es1].
      right; discriminate.
      right; discriminate.
      right; discriminate.
      destruct es1 as [|y ys]. {
        right; discriminate.
      } {
        pose proof (Forall_inv H_fa0 y) as H_dec_head.
        pose proof (Forall_inv_tail H_fa0) as H_dec_tail.
        pose proof (H_induction H_dec_tail) as H_dec_xs.
        pose proof (H_dec_xs (OEAnd ys)) as H_dec_ys.

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
    induction es0 as [|x xs H_induction]. {
      intro e1.
      destruct e1 as [ | |t1|es1|es1].
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
      destruct e1 as [ | |t1|es1|es1].
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
        pose proof (H_dec_xs (OEOr ys)) as H_dec_ys.

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

Fixpoint object_match_evaluate
  (o : object_t)
  (e : object_match_expression_t)
: bool :=
  match e with
  | OETrue                    => true
  | OEFalse                   => false
  | OEWithType (TypeName t _) => eqb t (text_of (object_type o))
  | OEAnd es                  => List.fold_right (λ e acc, andb acc (object_match_evaluate o e)) true es
  | OEOr es                   => List.fold_right (λ e acc, orb acc (object_match_evaluate o e)) false es
  end.
