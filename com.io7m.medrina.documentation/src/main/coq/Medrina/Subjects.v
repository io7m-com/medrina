Require Import Coq.Lists.List.
Require Import Coq.Unicode.Utf8_core.
Require Import Coq.Strings.String.
Require Import Coq.Logic.Decidable.

Require Import Medrina.Names.
Require Import Medrina.Roles.
Require Import Medrina.ListExtras.

Import ListNotations.

Open Scope string_scope.
Open Scope char_scope.

(* Many types carry proofs of their properties, and we want to be able
   to treat equality of values of these types as decidable. *)
Require Import Coq.Logic.ProofIrrelevance.

Set Mangle Names.

Inductive subject_t := Subject {
  subject_roles : list role_name_t
}.

Lemma subject_eq_dec : ∀ (s0 s1 : subject_t),
  decidable (s0 = s1).
Proof.
  intros s0 s1.
  destruct s0 as [s0_roles].
  destruct s1 as [s1_roles].
  destruct (list_eq_dec role_name_eq_dec s0_roles s1_roles) as [H_eq|H_neq]. {
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

Section SubjectMatchExpressions.

  Local Unset Elimination Schemes.

  Inductive subject_match_expression_t :=
    | SETrue         : subject_match_expression_t
    | SEFalse        : subject_match_expression_t
    | SEWithRolesAll : list role_name_t → subject_match_expression_t
    | SEWithRolesAny : list role_name_t → subject_match_expression_t
    | SEAnd          : list subject_match_expression_t → subject_match_expression_t
    | SEOr           : list subject_match_expression_t → subject_match_expression_t
    .

  Section rect.
    Variable P                  : subject_match_expression_t → Type.
    Variable P_list             : list subject_match_expression_t → Type.
    Hypothesis P_nil            : P_list [].
    Hypothesis P_cons           : ∀ x xs, P x → P_list xs → P_list (x :: xs).
    Hypothesis P_SETrue         : P SETrue.
    Hypothesis P_SEFalse        : P SEFalse.
    Hypothesis P_SEWithRolesAll : ∀ rs, P (SEWithRolesAll rs).
    Hypothesis P_SEWithRolesAny : ∀ rs, P (SEWithRolesAny rs).
    Hypothesis P_SEAnd          : ∀ es, P_list es → P (SEAnd es).
    Hypothesis P_SEOr           : ∀ es, P_list es → P (SEOr es).

    Fixpoint subject_match_expression_t_rect (e : subject_match_expression_t) : P e :=
      let
        fix exp_for_all (xs : list subject_match_expression_t) : P_list xs :=
          match xs as rxs return (P_list rxs) with
          | []        => @P_nil
          | (y :: ys) => @P_cons y ys (subject_match_expression_t_rect y) (exp_for_all ys)
          end
      in
        match e with
        | SETrue            => P_SETrue
        | SEFalse           => P_SEFalse
        | SEWithRolesAll ts => P_SEWithRolesAll ts
        | SEWithRolesAny ts => P_SEWithRolesAny ts
        | SEAnd es          => P_SEAnd es (exp_for_all es)
        | SEOr es           => P_SEOr es (exp_for_all es)
        end.
  End rect.

  Section ind.
    Variable P                  : subject_match_expression_t → Prop.
    Hypothesis P_SETrue         : P SETrue.
    Hypothesis P_SEFalse        : P SEFalse.
    Hypothesis P_SEWithRolesAll : ∀ ts, P (SEWithRolesAll ts).
    Hypothesis P_SEWithRolesAny : ∀ ts, P (SEWithRolesAny ts).
    Hypothesis P_SEAnd          : ∀ es, Forall P es → P (SEAnd es).
    Hypothesis P_SEOr           : ∀ es, Forall P es → P (SEOr es).

    Definition subject_match_expression_t_ind (e : subject_match_expression_t) : P e :=
      subject_match_expression_t_rect
        P
        (Forall P)
        (Forall_nil _)
        (λ x xs Px Pxs, Forall_cons _ Px Pxs)
        P_SETrue
        P_SEFalse
        P_SEWithRolesAll
        P_SEWithRolesAny
        P_SEAnd
        P_SEOr
        e.
  End ind.

End SubjectMatchExpressions.

Lemma subject_match_expression_eq_dec : forall (e0 e1 : subject_match_expression_t),
  decidable (e0 = e1).
Proof.
  intros e0.
  induction e0 as [ | |ts|ts|es0 H_fa0|es0 H_fa0]. {
    (* SETrue = ... *)
    intros e1.
    destruct e1.
    left; reflexivity.
    right; discriminate.
    right; discriminate.
    right; discriminate.
    right; discriminate.
    right; discriminate.
  } {
    (* SEFalse = ... *)
    intros e1.
    destruct e1.
    right; discriminate.
    left; reflexivity.
    right; discriminate.
    right; discriminate.
    right; discriminate.
    right; discriminate.
  } {
    (* SEWithRolesAll = ... *)
    intros e1.
    destruct e1 as [ | |ss|ss|es1|es1].
    right; discriminate.
    right; discriminate.
    destruct (list_eq_dec role_name_eq_dec ts ss) as [H_teq|H_tneq]. {
      destruct H_teq.
      left; reflexivity.
    } {
      right. intro H_contra. inversion H_contra. contradiction.
    }
    right; discriminate.
    right; discriminate.
    right; discriminate.
  } {
    (* SEWithRolesAny = ... *)
    intros e1.
    destruct e1 as [ | |ss|ss|es1|es1].
    right; discriminate.
    right; discriminate.
    right; discriminate.
    destruct (list_eq_dec role_name_eq_dec ts ss) as [H_teq|H_tneq]. {
      destruct H_teq.
      left; reflexivity.
    } {
      right. intro H_contra. inversion H_contra. contradiction.
    }
    right; discriminate.
    right; discriminate.
  } {
    (* SEAnd = ... *)
    induction es0 as [|x xs H_induction]. {
      intro e1.
      destruct e1 as [ | |ts1|ts1|es1|es1].
      right; discriminate.
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
      destruct e1 as [ | |ts1|ts1|es1|es1].
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
        pose proof (H_dec_xs (SEAnd ys)) as H_dec_ys.

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
    (* SEOr = ... *)
    induction es0 as [|x xs H_induction]. {
      intro e1.
      destruct e1 as [ | |ts1|ts1|es1|es1].
      right; discriminate.
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
      destruct e1 as [ | |ts1|ts1|es1|es1].
      right; discriminate.
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
        pose proof (H_dec_xs (SEOr ys)) as H_dec_ys.

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

Definition subject_has_roleb
  (s : subject_t)
  (r : role_name_t)
: bool :=
  List.existsb (λ sr, eqb (text_of sr) (text_of r)) (subject_roles s).

Fixpoint subject_match_evaluate
  (s : subject_t)
  (e : subject_match_expression_t)
: bool :=
  match e with
  | SETrue            => true
  | SEFalse           => false
  | SEWithRolesAll rs => List.forallb (λ r, subject_has_roleb s r) rs
  | SEWithRolesAny rs => List.fold_right (λ sr acc, orb acc (subject_has_roleb s sr)) false rs
  | SEAnd es          => List.fold_right (λ e acc, andb acc (subject_match_evaluate s e)) true es
  | SEOr es           => List.fold_right (λ e acc, orb acc (subject_match_evaluate s e)) false es
  end.
