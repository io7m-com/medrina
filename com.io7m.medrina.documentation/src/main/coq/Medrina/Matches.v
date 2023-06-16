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
Require Import Coq.Lists.List.
Require Import Coq.Lists.SetoidList.

Import ListNotations.

Require Import Medrina.Actions.
Require Import Medrina.Attributes.
Require Import Medrina.Names.
Require Import Medrina.Subjects.
Require Import Medrina.Roles.
Require Import Medrina.Objects.

(** An expression that matches a subject. *)
Inductive exprMatchSubject : Type :=
  | EMS_False        : exprMatchSubject
  | EMS_True         : exprMatchSubject
  | EMS_WithRolesAll : RoleSets.t -> exprMatchSubject
  | EMS_WithRolesAny : RoleSets.t -> exprMatchSubject
  | EMS_And          : list exprMatchSubject -> exprMatchSubject
  | EMS_Or           : list exprMatchSubject -> exprMatchSubject
  .

Section ExprMatchSubjects_ind.
  Variable P : exprMatchSubject -> Prop.
  Hypothesis P_False        : P EMS_False.
  Hypothesis P_True         : P EMS_True.
  Hypothesis P_WithRolesAll : forall r, P (EMS_WithRolesAll r).
  Hypothesis P_WithRolesAny : forall r, P (EMS_WithRolesAny r).
  Hypothesis P_And          : forall es, Forall P es -> P (EMS_And es).
  Hypothesis P_Or           : forall es, Forall P es -> P (EMS_Or es).

  Fixpoint exprMatchSubject_extendedInd (e : exprMatchSubject) : P e :=
    let
      fix e_list (xs : list exprMatchSubject) : Forall P xs :=
        match xs as rxs return (Forall P rxs) with
        | []        => Forall_nil _
        | (y :: ys) => @Forall_cons _ _ y ys (exprMatchSubject_extendedInd y) (e_list ys)
        end
    in
      match e with
      | EMS_False          => P_False
      | EMS_True           => P_True
      | EMS_WithRolesAll r => P_WithRolesAll r
      | EMS_WithRolesAny r => P_WithRolesAny r
      | EMS_And es         => P_And es (e_list es)
      | EMS_Or es          => P_Or es (e_list es)
      end.

End ExprMatchSubjects_ind.

(** An evaluation function for subject match expressions. *)
Fixpoint exprMatchSubjectEvalF
  (s : subject)
  (e : exprMatchSubject)
: bool :=
  match e with
  | EMS_False          => false
  | EMS_True           => true
  | EMS_WithRolesAll r => RoleSets.subset r (sRoles s)
  | EMS_WithRolesAny r => RoleSets.exists_ (fun x => RoleSets.mem x (sRoles s)) r
  | EMS_And es         => forallb (exprMatchSubjectEvalF s) es
  | EMS_Or es          => existsb (exprMatchSubjectEvalF s) es
  end.

(** The evaluation function for subject match expressions as a relation. *)
Inductive exprMatchSubjectEvalR (s : subject) : exprMatchSubject -> Prop :=
  | EMSR_True :
      exprMatchSubjectEvalR s EMS_True
  | EMSR_WithRolesAll :
    forall (r : RoleSets.t),
      RoleSets.Subset r (sRoles s) ->
        exprMatchSubjectEvalR s (EMS_WithRolesAll r)
  | EMSR_WithRolesAny :
    forall (r : RoleSets.t),
      (exists x, RoleSets.In x r /\ RoleSets.In x (sRoles s)) ->
        exprMatchSubjectEvalR s (EMS_WithRolesAny r)
  | EMSR_And :
    forall (es : list exprMatchSubject),
      Forall (exprMatchSubjectEvalR s) es ->
        exprMatchSubjectEvalR s (EMS_And es)
  | EMSR_Or :
    forall (es : list exprMatchSubject),
      Exists (exprMatchSubjectEvalR s) es ->
        exprMatchSubjectEvalR s (EMS_Or es)
  .

(** Implication lifted into the Forall structure. *)
Lemma Forall_impl_lifted : forall
  (A  : Type)
  (P  : A -> Prop)
  (Q  : A -> Prop)
  (xs : list A),
  Forall (fun x => P x) xs ->
    Forall (fun x => P x -> Q x) xs ->
      Forall (fun x => Q x) xs.
Proof.
  induction xs as [|y ys IH]. {
    intros F0 H1.
    constructor.
  } {
    intros F0 F1.
    constructor. {
      apply (Forall_inv F1).
      apply (Forall_inv F0).
    } {
      apply IH.
      apply (Forall_inv_tail F0).
      apply (Forall_inv_tail F1).
    }
  }
Qed.

Lemma exprMatchSubjectEvalEquivalent_FR_T : forall s e,
  true = exprMatchSubjectEvalF s e -> exprMatchSubjectEvalR s e.
Proof.
  intros s e.
  induction e as [
    |
    |
    |
    |es Hes
    |es Hes
  ] using exprMatchSubject_extendedInd. {
    (* EMS_False *)
    intros Ht.
    inversion Ht.
  } {
    (* EMS_True *)
    intros Ht.
    constructor.
  } {
    (* EMS_WithRolesAll *)
    intros Ht.
    unfold exprMatchSubjectEvalF in Ht.
    constructor.
    apply RoleSets.subset_2.
    intuition.
  } {
    (* EMS_WithRolesAny *)
    intros Ht.
    unfold exprMatchSubjectEvalF in Ht.
    constructor.
    symmetry in Ht.

    assert (
      SetoidList.compat_bool
        RoleSets.E.eq (fun x : RoleSets.elt => RoleSets.mem x (sRoles s))
    ) as Hsetcomp. {
      unfold SetoidList.compat_bool.
      unfold Morphisms.Proper.
      unfold Morphisms.respectful.
      intros x y Heq.
      rewrite Heq.
      reflexivity.
    }

    pose proof (RoleSets.exists_2 Hsetcomp Ht) as [x [H0 H1]].
    exists x.
    intuition.
  } {
    (* EMS_And *)
    destruct es as [|y ys]. {
      intros Ht.
      constructor.
      constructor.
    } {
      simpl.
      intros Ht.

      (* We need to show that the relation holds for all (y :: ys). *)
      assert (Forall (exprMatchSubjectEvalR s) (y :: ys)) as H0. {
        (* We do this by showing it holds for y... *)
        assert (exprMatchSubjectEvalR s y) as H1. {
          symmetry in Ht.
          rewrite Bool.andb_true_iff in Ht.
          rewrite forallb_forall in Ht.
          destruct Ht as [HT0 HT1].
          rewrite <- (@Forall_forall exprMatchSubject _ ys) in HT1.

          apply (Forall_inv Hes).
          symmetry.
          exact HT0.
        }

        (* ... And for all ys. *)
        assert (Forall (exprMatchSubjectEvalR s) ys) as H2. {
          symmetry in Ht.
          rewrite Bool.andb_true_iff in Ht.
          rewrite forallb_forall in Ht.
          destruct Ht as [HT0 HT1].
          rewrite <- (@Forall_forall exprMatchSubject _ ys) in HT1.

          assert (Forall (fun x : exprMatchSubject => true = exprMatchSubjectEvalF s x) ys) as H2. {
            rewrite Forall_forall.
            symmetry.
            generalize dependent x.
            rewrite <- Forall_forall.
            exact HT1.
          }

          pose proof (Forall_inv_tail Hes) as HesT.
          apply (Forall_impl_lifted _ _ _ ys H2 HesT).
        }

        (* ... And then composing the two. *)
        constructor.
        exact H1.
        exact H2.
      }

      constructor.
      exact H0.
    }
  } {
    (* EMS_Or *)
    destruct es as [|y ys]. {
      intros Ht.
      contradict Ht. simpl. discriminate.
    } {
      intros Ht.

      (* We need to show that the relation holds for y or something in ys. *)
      constructor.

      simpl in Ht.
      symmetry in Ht.
      destruct (Bool.orb_true_elim _ _ Ht) as [HtL|HtR]. {
        constructor.
        apply (Forall_inv Hes).
        auto.
      } {
        assert (Exists (exprMatchSubjectEvalR s) (y :: ys)) as H0. {
          rewrite existsb_exists in HtR.
          destruct HtR as [k [Htk0 Htk1]].
          rewrite Forall_forall in Hes.
          pose proof (in_cons y k ys Htk0) as H0.
          pose proof (Hes k H0 (eq_sym Htk1)) as H1.
          apply Exists_cons_tl.
          rewrite Exists_exists.
          exists k.
          auto.
        }
        exact H0.
      }
    }
  }
Qed.

Lemma  exprMatchSubjectEvalEquivalent_RF_T : forall s e,
  exprMatchSubjectEvalR s e -> true = exprMatchSubjectEvalF s e.
Proof.
  intros s e.
  induction e as [
    |
    |
    |
    |es Hes
    |es Hes
  ] using exprMatchSubject_extendedInd. {
    (* EMS_False *)
    intros Ht.
    inversion Ht.
  } {
    (* EMS_True *)
    intros Ht.
    reflexivity.
  } {
    (* EMS_WithRolesAll *)
    intros Ht.
    symmetry.
    apply RoleSets.subset_1.
    inversion Ht.
    intuition.
  } {
    (* EMS_WithRolesAny *)
    intros Ht.
    symmetry.
    inversion Ht as [ | |s0 Hexist Heq| | ].
    subst s0.
    simpl.
    assert (
      RoleSets.Exists
        (fun x : RoleSets.elt => RoleSets.mem x (sRoles s) = true) r
    ) as Hex. {
      unfold RoleSets.Exists.
      destruct Hexist as [y [Hy0 Hy1]].
      exists y.
      intuition.
    }

    assert (
      SetoidList.compat_bool
        RoleSets.E.eq (fun x : RoleSets.elt => RoleSets.mem x (sRoles s))
    ) as Hsetcomp. {
      unfold SetoidList.compat_bool.
      unfold Morphisms.Proper.
      unfold Morphisms.respectful.
      intros x y Heq.
      rewrite Heq.
      reflexivity.
    }

    apply (RoleSets.exists_1 Hsetcomp Hex).
  } {
    (* EMS_And *)
    intros Ht.
    inversion Ht as [ | | |es0 Hfa Heq|].
    subst es0.
    simpl.
    symmetry.
    rewrite forallb_forall.
    intros x Hin.
    symmetry.
    generalize dependent x.
    rewrite <- Forall_forall.
    apply (Forall_impl_lifted exprMatchSubject _ _ es Hfa Hes).
  } {
    (* EMS_Or *)
    intros Ht.
    symmetry.
    simpl.
    rewrite existsb_exists.

    inversion Ht as [ | | | |es0 Hex Heq].
    subst es.
    destruct Hex as [k ks Hk|k ks Hk]. {
      exists k.
      constructor.
      constructor; reflexivity.
      apply (eq_sym (Forall_inv Hes Hk)).
    } {
      rewrite Exists_exists in Hk.
      destruct Hk as [q [Hq0 Hq1]].
      exists q.
      constructor.
      apply (in_cons k q ks Hq0).
      pose proof (Forall_inv_tail Hes) as HesT.
      rewrite Forall_forall in HesT.
      apply (eq_sym (HesT q Hq0 Hq1)).
    }
  }
Qed.

(** The evaluation function and the evaluation relation are equivalent. *)
Theorem exprMatchSubjectEvalEquivalentT : forall s e,
  true = exprMatchSubjectEvalF s e <-> exprMatchSubjectEvalR s e.
Proof.
  split.
  apply exprMatchSubjectEvalEquivalent_FR_T.
  apply exprMatchSubjectEvalEquivalent_RF_T.
Qed.

Lemma exprMatchSubjectEvalEquivalent_FR_F : forall s e,
  false = exprMatchSubjectEvalF s e -> ~exprMatchSubjectEvalR s e.
Proof.
  intros s e.
  induction e as [
    |
    |
    |
    |es Hes
    |es Hes
  ] using exprMatchSubject_extendedInd. {
    (* EMS_False *)
    intros Ht.
    intro Hcontra.
    inversion Hcontra.
  } {
    (* EMS_True *)
    intros Ht.
    contradict Ht.
    discriminate.
  } {
    (* EMS_WithRolesAll *)
    intros Ht.
    intros Hcontra.
    rewrite <- (exprMatchSubjectEvalEquivalent_RF_T _ _ Hcontra) in Ht.
    contradict Ht; discriminate.
  } {
    (* EMS_WithRolesAny *)
    intros Ht.
    intros Hcontra.
    rewrite <- (exprMatchSubjectEvalEquivalent_RF_T _ _ Hcontra) in Ht.
    contradict Ht; discriminate.
  } {
    (* EMS_And *)
    intros Ht.
    intros Hcontra.
    rewrite <- (exprMatchSubjectEvalEquivalent_RF_T _ _ Hcontra) in Ht.
    contradict Ht; discriminate.
  } {
    (* EMS_Or *)
    intros Ht.
    intros Hcontra.
    rewrite <- (exprMatchSubjectEvalEquivalent_RF_T _ _ Hcontra) in Ht.
    contradict Ht; discriminate.
  }
Qed.

Lemma exprMatchSubjectEvalEquivalent_RF_F : forall s e,
  ~exprMatchSubjectEvalR s e -> false = exprMatchSubjectEvalF s e.
Proof.
  intros s e.
  induction e as [
    |
    |
    |
    |es Hes
    |es Hes
  ] using exprMatchSubject_extendedInd. {
    (* EMS_False *)
    intros Ht.
    reflexivity.
  } {
    (* EMS_True *)
    intros Ht.
    contradict Ht.
    constructor.
  } {
    (* EMS_WithRolesAll *)
    intros Ht.
    simpl.
    assert (~RoleSets.Subset r (sRoles s)) as Hns. {
      intros Hcontra.
      apply Ht.
      constructor.
      exact Hcontra.
    }
    symmetry.
    rewrite <- roleSubsetFalse.
    intuition.
  } {
    (* EMS_WithRolesAny *)
    intros Ht.
    symmetry.
    intuition.
    simpl.

    assert (
      SetoidList.compat_bool
        RoleSets.E.eq (fun x : RoleSets.elt => RoleSets.mem x (sRoles s))
    ) as Hsetcomp. {
      unfold SetoidList.compat_bool.
      unfold Morphisms.Proper.
      unfold Morphisms.respectful.
      intros x y Heq.
      rewrite Heq.
      reflexivity.
    }

    rewrite <- (roleExistsFalse r _ Hsetcomp).
    intro Hcontra.
    apply Ht.
    constructor.
    inversion Hcontra as [z [Hz0 Hz1]].
    exists z.
    intuition.
  } {
    (* EMS_And *)
    intros Ht.
    destruct (exprMatchSubjectEvalF s (EMS_And es)) eqn:H. {
      symmetry in H.
      rewrite exprMatchSubjectEvalEquivalentT in H.
      contradiction.
    } {
      reflexivity.
    }
  } {
    (* EMS_Or *)
    intros Ht.
    destruct (exprMatchSubjectEvalF s (EMS_Or es)) eqn:H. {
      symmetry in H.
      rewrite exprMatchSubjectEvalEquivalentT in H.
      contradiction.
    } {
      reflexivity.
    }
  }
Qed.

(** The evaluation function and the evaluation relation are equivalent. *)
Theorem exprMatchSubjectEvalEquivalentF : forall s e,
  false = exprMatchSubjectEvalF s e <-> ~exprMatchSubjectEvalR s e.
Proof.
  split.
  apply exprMatchSubjectEvalEquivalent_FR_F.
  apply exprMatchSubjectEvalEquivalent_RF_F.
Qed.

(** The evaluation relation is decidable. *)
Theorem exprMatchSubjectEvalRDec : forall s e,
  {exprMatchSubjectEvalR s e}+{~exprMatchSubjectEvalR s e}.
Proof.
  intros s e.
  destruct (exprMatchSubjectEvalF s e) eqn:Hev. {
    symmetry in Hev.
    rewrite exprMatchSubjectEvalEquivalentT in Hev.
    left; intuition.
  } {
    symmetry in Hev.
    rewrite exprMatchSubjectEvalEquivalentF in Hev.
    right; intuition.
  }
Qed.

(** An expression that matches an action. *)
Inductive exprMatchAction : Type :=
  | EMA_False    : exprMatchAction
  | EMA_True     : exprMatchAction
  | EMA_WithName : actionName -> exprMatchAction
  | EMA_And      : list exprMatchAction -> exprMatchAction
  | EMA_Or       : list exprMatchAction -> exprMatchAction
  .

(** An evaluation function for action match expressions. *)
Fixpoint exprMatchActionEvalF
  (a : action)
  (e : exprMatchAction)
: bool :=
  match e with
  | EMA_False      => false
  | EMA_True       => true
  | EMA_WithName n => eqb (ivName (aName a)) (ivName n)
  | EMA_And xs     => forallb (exprMatchActionEvalF a) xs
  | EMA_Or xs      => existsb (exprMatchActionEvalF a) xs
  end.

(** The evaluation function for action match expressions as a relation. *)
Inductive exprMatchActionEvalR (a : action) : exprMatchAction -> Prop :=
  | EMAR_True : exprMatchActionEvalR a EMA_True
  | EMAR_WithName :
    forall (x : actionName),
      ivName (aName a) = ivName x ->
        exprMatchActionEvalR a (EMA_WithName x)
  | EMAR_And :
    forall (es : list exprMatchAction),
      Forall (exprMatchActionEvalR a) es ->
        exprMatchActionEvalR a (EMA_And es)
  | EMAR_Or :
    forall (es : list exprMatchAction),
      Exists (exprMatchActionEvalR a) es ->
        exprMatchActionEvalR a (EMA_Or es)
  .

Section ExprMatchAction_ind.
  Variable P : exprMatchAction -> Prop.
  Hypothesis P_False    : P EMA_False.
  Hypothesis P_True     : P EMA_True.
  Hypothesis P_WithName : forall n, P (EMA_WithName n).
  Hypothesis P_And      : forall es, Forall P es -> P (EMA_And es).
  Hypothesis P_Or       : forall es, Forall P es -> P (EMA_Or es).

  Fixpoint exprMatchAction_extendedInd (e : exprMatchAction) : P e :=
    let
      fix e_list (xs : list exprMatchAction) : Forall P xs :=
        match xs as rxs return (Forall P rxs) with
        | []        => Forall_nil _
        | (y :: ys) => @Forall_cons _ _ y ys (exprMatchAction_extendedInd y) (e_list ys)
        end
    in
      match e with
      | EMA_False      => P_False
      | EMA_True       => P_True
      | EMA_WithName a => P_WithName a
      | EMA_And es     => P_And es (e_list es)
      | EMA_Or es      => P_Or es (e_list es)
      end.

End ExprMatchAction_ind.

Lemma exprMatchActionEvalEquivalent_FR_T : forall s e,
  true = exprMatchActionEvalF s e -> exprMatchActionEvalR s e.
Proof.
  intros s e.
  induction e as [
    |
    |
    |es Hes
    |es Hes
  ] using exprMatchAction_extendedInd. {
    (* EMA_False *)
    intros Ht.
    inversion Ht.
  } {
    (* EMA_True *)
    intros Ht.
    constructor.
  } {
    (* EMA_WithName *)
    intros Ht.
    unfold exprMatchActionEvalF in Ht.
    symmetry in Ht.
    rewrite eqb_eq in Ht.
    pose proof (ivIrrelevantEqual _ _ Ht) as H.
    subst n.
    constructor.
    reflexivity.
  } {
    (* EMA_And *)
    destruct es as [|y ys]. {
      intros Ht.
      constructor.
      constructor.
    } {
      simpl.
      intros Ht.

      (* We need to show that the relation holds for all (y :: ys). *)
      assert (Forall (exprMatchActionEvalR s) (y :: ys)) as H0. {
        (* We do this by showing it holds for y... *)
        assert (exprMatchActionEvalR s y) as H1. {
          symmetry in Ht.
          rewrite Bool.andb_true_iff in Ht.
          rewrite forallb_forall in Ht.
          destruct Ht as [HT0 HT1].
          rewrite <- (@Forall_forall exprMatchAction _ ys) in HT1.

          apply (Forall_inv Hes).
          symmetry.
          exact HT0.
        }

        (* ... And for all ys. *)
        assert (Forall (exprMatchActionEvalR s) ys) as H2. {
          symmetry in Ht.
          rewrite Bool.andb_true_iff in Ht.
          rewrite forallb_forall in Ht.
          destruct Ht as [HT0 HT1].
          rewrite <- (@Forall_forall exprMatchAction _ ys) in HT1.

          assert (Forall (fun x => true = exprMatchActionEvalF s x) ys) as H2. {
            rewrite Forall_forall.
            symmetry.
            generalize dependent x.
            rewrite <- Forall_forall.
            exact HT1.
          }

          pose proof (Forall_inv_tail Hes) as HesT.
          apply (Forall_impl_lifted _ _ _ ys H2 HesT).
        }

        (* ... And then composing the two. *)
        constructor.
        exact H1.
        exact H2.
      }

      constructor.
      exact H0.
    }
  } {
    (* EMA_Or *)
    destruct es as [|y ys]. {
      intros Ht.
      contradict Ht. simpl. discriminate.
    } {
      intros Ht.

      (* We need to show that the relation holds for y or something in ys. *)
      constructor.

      simpl in Ht.
      symmetry in Ht.
      destruct (Bool.orb_true_elim _ _ Ht) as [HtL|HtR]. {
        constructor.
        apply (Forall_inv Hes).
        auto.
      } {
        assert (Exists (exprMatchActionEvalR s) (y :: ys)) as H0. {
          rewrite existsb_exists in HtR.
          destruct HtR as [k [Htk0 Htk1]].
          rewrite Forall_forall in Hes.
          pose proof (in_cons y k ys Htk0) as H0.
          pose proof (Hes k H0 (eq_sym Htk1)) as H1.
          apply Exists_cons_tl.
          rewrite Exists_exists.
          exists k.
          auto.
        }
        exact H0.
      }
    }
  }
Qed.

Lemma exprMatchActionEvalEquivalent_RF_T : forall s e,
  exprMatchActionEvalR s e -> true = exprMatchActionEvalF s e.
Proof.
  intros s e.
  induction e as [
    |
    |
    |es Hes
    |es Hes
  ] using exprMatchAction_extendedInd. {
    (* EMA_False *)
    intros Ht.
    inversion Ht.
  } {
    (* EMA_True *)
    intros Ht.
    reflexivity.
  } {
    (* EMA_WithName *)
    intros Ht.
    simpl.
    inversion Ht as [ |y Hyz| | ].
    subst y.
    pose proof (ivIrrelevantEqual _ _ Hyz) as H0.
    rewrite H0.
    symmetry.
    apply eqb_refl.
  } {
    (* EMA_And *)
    intros Ht.
    inversion Ht as [ | |es0 Hfa Heq|].
    subst es0.
    simpl.
    symmetry.
    rewrite forallb_forall.
    intros x Hin.
    symmetry.
    generalize dependent x.
    rewrite <- Forall_forall.
    apply (Forall_impl_lifted exprMatchAction _ _ es Hfa Hes).
  } {
    (* EMA_Or *)
    intros Ht.
    symmetry.
    simpl.
    rewrite existsb_exists.

    inversion Ht as [ | | |es0 Hex Heq].
    subst es.
    destruct Hex as [k ks Hk|k ks Hk]. {
      exists k.
      constructor.
      constructor; reflexivity.
      apply (eq_sym (Forall_inv Hes Hk)).
    } {
      rewrite Exists_exists in Hk.
      destruct Hk as [q [Hq0 Hq1]].
      exists q.
      constructor.
      apply (in_cons k q ks Hq0).
      pose proof (Forall_inv_tail Hes) as HesT.
      rewrite Forall_forall in HesT.
      apply (eq_sym (HesT q Hq0 Hq1)).
    }
  }
Qed.

(** The evaluation function and the evaluation relation are equivalent. *)
Theorem exprMatchActionEvalEquivalentT : forall s e,
  true = exprMatchActionEvalF s e <-> exprMatchActionEvalR s e.
Proof.
  split.
  apply exprMatchActionEvalEquivalent_FR_T.
  apply exprMatchActionEvalEquivalent_RF_T.
Qed.

Lemma exprMatchActionEvalEquivalent_FR_F : forall a e,
  false = exprMatchActionEvalF a e -> ~exprMatchActionEvalR a e.
Proof.
  intros s e.
  induction e as [
    |
    |
    |es Hes
    |es Hes
  ] using exprMatchAction_extendedInd. {
    (* EMA_False *)
    intros Ht.
    intro Hcontra.
    inversion Hcontra.
  } {
    (* EMA_True *)
    intros Ht.
    contradict Ht.
    discriminate.
  } {
    (* EMA_WithName *)
    intros Ht.
    intros Hcontra.
    rewrite <- (exprMatchActionEvalEquivalent_RF_T _ _ Hcontra) in Ht.
    contradict Ht; discriminate.
  } {
    (* EMS_And *)
    intros Ht.
    intros Hcontra.
    rewrite <- (exprMatchActionEvalEquivalent_RF_T _ _ Hcontra) in Ht.
    contradict Ht; discriminate.
  } {
    (* EMS_Or *)
    intros Ht.
    intros Hcontra.
    rewrite <- (exprMatchActionEvalEquivalent_RF_T _ _ Hcontra) in Ht.
    contradict Ht; discriminate.
  }
Qed.

Lemma exprMatchActionEvalEquivalent_RF_F : forall a e,
  ~exprMatchActionEvalR a e -> false = exprMatchActionEvalF a e.
Proof.
  intros s e.
  induction e as [
    |
    |
    |es Hes
    |es Hes
  ] using exprMatchAction_extendedInd. {
    (* EMA_False *)
    intros Ht.
    reflexivity.
  } {
    (* EMA_True *)
    intros Ht.
    contradict Ht.
    constructor.
  } {
    (* EMS_WithName *)
    intros Ht.
    destruct (exprMatchActionEvalF s (EMA_WithName n)) eqn:H. {
      symmetry in H.
      rewrite exprMatchActionEvalEquivalentT in H.
      contradiction.
    } {
      reflexivity.
    }
  } {
    (* EMS_And *)
    intros Ht.
    destruct (exprMatchActionEvalF s (EMA_And es)) eqn:H. {
      symmetry in H.
      rewrite exprMatchActionEvalEquivalentT in H.
      contradiction.
    } {
      reflexivity.
    }
  } {
    (* EMS_Or *)
    intros Ht.
    destruct (exprMatchActionEvalF s (EMA_Or es)) eqn:H. {
      symmetry in H.
      rewrite exprMatchActionEvalEquivalentT in H.
      contradiction.
    } {
      reflexivity.
    }
  }
Qed.

(** The evaluation function and the evaluation relation are equivalent. *)
Theorem exprMatchActionEvalEquivalentF : forall a e,
  false = exprMatchActionEvalF a e <-> ~exprMatchActionEvalR a e.
Proof.
  split.
  apply exprMatchActionEvalEquivalent_FR_F.
  apply exprMatchActionEvalEquivalent_RF_F.
Qed.

(** The evaluation relation is decidable. *)
Theorem exprMatchActionEvalRDec : forall a e,
  {exprMatchActionEvalR a e}+{~exprMatchActionEvalR a e}.
Proof.
  intros a e.
  destruct (exprMatchActionEvalF a e) eqn:Hev. {
    symmetry in Hev.
    rewrite exprMatchActionEvalEquivalentT in Hev.
    left; intuition.
  } {
    symmetry in Hev.
    rewrite exprMatchActionEvalEquivalentF in Hev.
    right; intuition.
  }
Qed.

(** An expression that matches an object. *)
Inductive exprMatchObject : Type :=
  | EMO_False             : exprMatchObject
  | EMO_True              : exprMatchObject
  | EMO_WithType          : typeName -> exprMatchObject
  | EMO_WithAttributesAll : AttributeNameMaps.t attributeValue -> exprMatchObject
  | EMO_WithAttributesAny : AttributeNameMaps.t attributeValue -> exprMatchObject
  | EMO_And               : list exprMatchObject -> exprMatchObject
  | EMO_Or                : list exprMatchObject -> exprMatchObject
  .

Section ExprMatchObject_ind.
  Variable P : exprMatchObject -> Prop.
  Hypothesis P_False             : P EMO_False.
  Hypothesis P_True              : P EMO_True.
  Hypothesis P_WithType          : forall n, P (EMO_WithType n).
  Hypothesis P_WithAttributesAll : forall n, P (EMO_WithAttributesAll n).
  Hypothesis P_WithAttributesAny : forall n, P (EMO_WithAttributesAny n).
  Hypothesis P_And               : forall es, Forall P es -> P (EMO_And es).
  Hypothesis P_Or                : forall es, Forall P es -> P (EMO_Or es).

  Fixpoint exprMatchObject_extendedInd (e : exprMatchObject) : P e :=
    let
      fix e_list (xs : list exprMatchObject) : Forall P xs :=
        match xs as rxs return (Forall P rxs) with
        | []        => Forall_nil _
        | (y :: ys) => @Forall_cons _ _ y ys (exprMatchObject_extendedInd y) (e_list ys)
        end
    in
      match e with
      | EMO_False               => P_False
      | EMO_True                => P_True
      | EMO_WithType a          => P_WithType a
      | EMO_WithAttributesAll a => P_WithAttributesAll a
      | EMO_WithAttributesAny a => P_WithAttributesAny a
      | EMO_And es              => P_And es (e_list es)
      | EMO_Or es               => P_Or es (e_list es)
      end.

End ExprMatchObject_ind.

Definition mapsB
  (m : AttributeNameMaps.t attributeValue)
  (k : attributeName)
  (v : attributeValue)
: bool :=
  match AttributeNameMaps.find k m with
  | Some w => attributeValueBool v w
  | None   => false
  end.

Lemma mapsB_MapsToL : forall m k v,
  mapsB m k v = true -> AttributeNameMaps.MapsTo k v m.
Proof.
  unfold mapsB.
  intros m k v Hf.
  destruct (AttributeNameMaps.find k m) eqn:Hfind. {
    rewrite <- attributeValueBoolDecT in Hf.
    subst v.
    apply (AttributeNameMaps.find_2 Hfind).
  } {
    contradict Hf.
    discriminate.
  }
Qed.

Lemma mapsB_MapsToR : forall m k v,
  AttributeNameMaps.MapsTo k v m -> mapsB m k v = true.
Proof.
  intros m k v Hmaps.
  unfold mapsB.
  destruct (AttributeNameMaps.find k m) eqn:Hfind. {
    rewrite <- attributeValueBoolDecT.
    rewrite <- AttributeNameMapsFacts.find_mapsto_iff in Hfind.
    apply (AttributeNameMapsFacts.MapsTo_fun Hmaps Hfind).
  } {
    rewrite AttributeNameMapsFacts.find_mapsto_iff in Hmaps.
    rewrite Hmaps in Hfind.
    contradict Hfind.
    discriminate.
  }
Qed.

Lemma mapsB_MapsTo_iff : forall m k v,
  AttributeNameMaps.MapsTo k v m <-> mapsB m k v = true.
Proof.
  split.
  apply mapsB_MapsToR.
  apply mapsB_MapsToL.
Qed.

(** An evaluation function for object match expressions. *)
Fixpoint exprMatchObjectEvalF
  (o : object)
  (e : exprMatchObject)
: bool :=
  match e with
  | EMO_False => false
  | EMO_True => true
  | EMO_WithType n =>
    eqb (ivName (oType o)) (ivName n)
  | EMO_WithAttributesAll attributesRequired =>
    let attributesHeld := oAttributes o in
      forallb (fun p => mapsB attributesHeld (fst p) (snd p))
        (AttributeNameMaps.elements attributesRequired)
  | EMO_WithAttributesAny attributesRequired =>
    let attributesHeld := oAttributes o in
      existsb (fun p => mapsB attributesHeld (fst p) (snd p))
        (AttributeNameMaps.elements attributesRequired)
  | EMO_And xs =>
    forallb (exprMatchObjectEvalF o) xs
  | EMO_Or xs =>
    existsb (exprMatchObjectEvalF o) xs
  end.

(** The evaluation function for object match expressions as a relation. *)
Inductive exprMatchObjectEvalR (o : object) : exprMatchObject -> Prop :=
  | EMOR_True : exprMatchObjectEvalR o EMO_True
  | EMOR_WithName :
    forall (t : typeName),
      ivName (oType o) = ivName t ->
        exprMatchObjectEvalR o (EMO_WithType t)
  | EMOR_WithAttributesAll :
    forall (required : AttributeNameMaps.t attributeValue),
      (forall (k : attributeName) (v : attributeValue),
        AttributeNameMaps.MapsTo k v required -> AttributeNameMaps.MapsTo k v (oAttributes o)) ->
          exprMatchObjectEvalR o (EMO_WithAttributesAll required)
  | EMOR_WithAttributesAny :
    forall (required : AttributeNameMaps.t attributeValue),
      (exists k : attributeName,
        (exists v : attributeValue,
          AttributeNameMaps.MapsTo k v required /\ AttributeNameMaps.MapsTo k v (oAttributes o))) ->
            exprMatchObjectEvalR o (EMO_WithAttributesAny required)
  | EMOR_And :
    forall (es : list exprMatchObject),
      Forall (exprMatchObjectEvalR o) es ->
        exprMatchObjectEvalR o (EMO_And es)
  | EMOR_Or :
    forall (es : list exprMatchObject),
      Exists (exprMatchObjectEvalR o) es ->
        exprMatchObjectEvalR o (EMO_Or es)
  .

Lemma exprMatchObjectEvalEquivalent_FR_T_EMO_False : forall s,
  true = exprMatchObjectEvalF s EMO_False -> exprMatchObjectEvalR s EMO_False.
Proof.
  intros s Ht.
  inversion Ht.
Qed.

Lemma exprMatchObjectEvalEquivalent_FR_T_EMO_True : forall s,
  true = exprMatchObjectEvalF s EMO_True -> exprMatchObjectEvalR s EMO_True.
Proof.
  intros s Ht.
  constructor.
Qed.

Lemma exprMatchObjectEvalEquivalent_FR_T_EMO_WithType : forall s n,
  true = exprMatchObjectEvalF s (EMO_WithType n) ->
    exprMatchObjectEvalR s (EMO_WithType n).
Proof.
  intros s n Ht.
  unfold exprMatchObjectEvalF in Ht.
  symmetry in Ht.
  rewrite eqb_eq in Ht.
  pose proof (ivIrrelevantEqual _ _ Ht) as H.
  subst n.
  constructor.
  reflexivity.
Qed.

Lemma exprMatchObjectEvalEquivalent_FR_T_EMO_WithAttributesAll : forall s required,
  true = exprMatchObjectEvalF s (EMO_WithAttributesAll required) ->
    exprMatchObjectEvalR s (EMO_WithAttributesAll required).
Proof.
  intros s required Ht.
  constructor.

  simpl in Ht.
  symmetry in Ht.
  rewrite forallb_forall in Ht.

  intros k v Hmaps.
  pose proof (Ht (k, v)) as Hp0.
  clear Ht.
  simpl in Hp0.
  rewrite <- mapsB_MapsTo_iff in Hp0.
  apply Hp0.
  clear Hp0.
  rewrite AttributeNameMapsFacts.elements_mapsto_iff in Hmaps.
  induction Hmaps as [x xs [H01 H02]|y ys H1]. {
    simpl.
    left.
    destruct x as [fx sx].
    assert (fx = k) as Hp0. { simpl in H01. symmetry. exact H01. }
    assert (sx = v) as Hp1. { simpl in H02. symmetry. exact H02. }
    subst fx.
    subst sx.
    reflexivity.
  } {
    simpl.
    right; auto.
  }
Qed.

Lemma exprMatchObjectEvalEquivalent_FR_T_EMO_WithAttributesAny : forall s required,
  true = exprMatchObjectEvalF s (EMO_WithAttributesAny required) ->
    exprMatchObjectEvalR s (EMO_WithAttributesAny required).
Proof.
  intros s required Ht.
  constructor.

  simpl in Ht.
  symmetry in Ht.
  rewrite existsb_exists in Ht.
  destruct Ht as [[k0 v0] [Ht0 Ht1]].

  exists k0.
  exists v0.
  rewrite <- mapsB_MapsTo_iff in Ht1.
  simpl in Ht1.
  intros.
  split. {
    rewrite AttributeNameMapsFacts.elements_mapsto_iff.
    apply In_InA.
    exact AttributeNameMapsEqEquiv.
    exact Ht0.
  } {
    exact Ht1.
  }
Qed.

Lemma exprMatchObjectEvalEquivalent_FR_T : forall s e,
  true = exprMatchObjectEvalF s e -> exprMatchObjectEvalR s e.
Proof.
  intros s e.
  induction e as [
    |
    |
    |required
    |required
    |es Hes
    |es Hes
  ] using exprMatchObject_extendedInd. {
    apply exprMatchObjectEvalEquivalent_FR_T_EMO_False.
  } {
    apply exprMatchObjectEvalEquivalent_FR_T_EMO_True.
  } {
    apply exprMatchObjectEvalEquivalent_FR_T_EMO_WithType.
  } {
    apply exprMatchObjectEvalEquivalent_FR_T_EMO_WithAttributesAll.
  } {
    apply exprMatchObjectEvalEquivalent_FR_T_EMO_WithAttributesAny.
  } {
    (* EMO_And *)
    destruct es as [|y ys]. {
      intros Ht.
      constructor.
      constructor.
    } {
      simpl.
      intros Ht.

      (* We need to show that the relation holds for all (y :: ys). *)
      assert (Forall (exprMatchObjectEvalR s) (y :: ys)) as H0. {
        (* We do this by showing it holds for y... *)
        assert (exprMatchObjectEvalR s y) as H1. {
          symmetry in Ht.
          rewrite Bool.andb_true_iff in Ht.
          rewrite forallb_forall in Ht.
          destruct Ht as [HT0 HT1].
          rewrite <- (@Forall_forall exprMatchObject _ ys) in HT1.

          apply (Forall_inv Hes).
          symmetry.
          exact HT0.
        }

        (* ... And for all ys. *)
        assert (Forall (exprMatchObjectEvalR s) ys) as H2. {
          symmetry in Ht.
          rewrite Bool.andb_true_iff in Ht.
          rewrite forallb_forall in Ht.
          destruct Ht as [HT0 HT1].
          rewrite <- (@Forall_forall exprMatchObject _ ys) in HT1.

          assert (Forall (fun x => true = exprMatchObjectEvalF s x) ys) as H2. {
            rewrite Forall_forall.
            symmetry.
            generalize dependent x.
            rewrite <- Forall_forall.
            exact HT1.
          }

          pose proof (Forall_inv_tail Hes) as HesT.
          apply (Forall_impl_lifted _ _ _ ys H2 HesT).
        }

        (* ... And then composing the two. *)
        constructor.
        exact H1.
        exact H2.
      }

      constructor.
      exact H0.
    }
  } {
    (* EMO_Or *)
    destruct es as [|y ys]. {
      intros Ht.
      contradict Ht. simpl. discriminate.
    } {
      intros Ht.

      (* We need to show that the relation holds for y or something in ys. *)
      constructor.

      simpl in Ht.
      symmetry in Ht.
      destruct (Bool.orb_true_elim _ _ Ht) as [HtL|HtR]. {
        constructor.
        apply (Forall_inv Hes).
        auto.
      } {
        assert (Exists (exprMatchObjectEvalR s) (y :: ys)) as H0. {
          rewrite existsb_exists in HtR.
          destruct HtR as [k [Htk0 Htk1]].
          rewrite Forall_forall in Hes.
          pose proof (in_cons y k ys Htk0) as H0.
          pose proof (Hes k H0 (eq_sym Htk1)) as H1.
          apply Exists_cons_tl.
          rewrite Exists_exists.
          exists k.
          auto.
        }
        exact H0.
      }
    }
  }
Qed.

Lemma exprMatchObjectEvalEquivalent_RF_T_False : forall s,
  exprMatchObjectEvalR s EMO_False -> true = exprMatchObjectEvalF s EMO_False.
Proof.
  intros s Ht.
  inversion Ht.
Qed.

Lemma exprMatchObjectEvalEquivalent_RF_T_True : forall s,
  exprMatchObjectEvalR s EMO_True -> true = exprMatchObjectEvalF s EMO_True.
Proof.
  intros s Ht.
  reflexivity.
Qed.

Lemma exprMatchObjectEvalEquivalent_RF_T_WithType : forall s n,
  exprMatchObjectEvalR s (EMO_WithType n) ->
    true = exprMatchObjectEvalF s (EMO_WithType n).
Proof.
  intros s n Ht.
  simpl.
  inversion Ht as [ |y Hyz| | | |].
  subst y.
  pose proof (ivIrrelevantEqual _ _ Hyz) as H0.
  rewrite H0.
  symmetry.
  apply eqb_refl.
Qed.

Lemma exprMatchObjectEvalEquivalent_RF_T_WithAttributesAll : forall s n,
  exprMatchObjectEvalR s (EMO_WithAttributesAll n) ->
    true = exprMatchObjectEvalF s (EMO_WithAttributesAll n).
Proof.
  intros s n Hem.
  inversion Hem as [ | |required H0 H1| | |].
  subst n.
  simpl.
  symmetry.
  rewrite forallb_forall.
  intros [k v] Hin.
  simpl.
  rewrite <- mapsB_MapsTo_iff.
  apply H0.
  rewrite AttributeNameMapsFacts.elements_mapsto_iff.
  apply In_InA.
  unfold AttributeNameMaps.eq_key_elt.
  constructor. {
    constructor; reflexivity.
  } {
    constructor.
    intuition.
    symmetry.
    intuition.
  } {
    intros x y z [Heq0 Heq1] [Heq2 Heq3].
    rewrite Heq1.
    rewrite Heq3.
    rewrite <- Heq2.
    rewrite Heq0.
    constructor; reflexivity.
  }
  trivial.
Qed.

Lemma exprMatchObjectEvalEquivalent_RF_T_WithAttributesAny : forall s n,
  exprMatchObjectEvalR s (EMO_WithAttributesAny n) ->
    true = exprMatchObjectEvalF s (EMO_WithAttributesAny n).
Proof.
  intros s n Hem.
  inversion Hem as [ | | |required H0 H1| |].
  subst n.
  destruct H0 as [k [v [Hpm0 Hpm1]]].
  simpl.
  symmetry.
  rewrite existsb_exists.
  exists (k, v).
  rewrite <- mapsB_MapsTo_iff.
  simpl.
  split. {
    rewrite AttributeNameMapsFacts.elements_mapsto_iff in Hpm0.
    rewrite InA_alt in Hpm0.
    destruct Hpm0 as [y [Hy0 Hy1]].
    rewrite AttributeNameMapsEqLeibniz in Hy0.
    subst y.
    exact Hy1.
  } {
    exact Hpm1.
  }
Qed.

Lemma exprMatchObjectEvalEquivalent_RF_T : forall s e,
  exprMatchObjectEvalR s e -> true = exprMatchObjectEvalF s e.
Proof.
  intros s e.
  induction e as [
    |
    |
    |
    |
    |es Hes
    |es Hes
  ] using exprMatchObject_extendedInd. {
    apply exprMatchObjectEvalEquivalent_RF_T_False.
  } {
    apply exprMatchObjectEvalEquivalent_RF_T_True.
  } {
    apply exprMatchObjectEvalEquivalent_RF_T_WithType.
  } {
    apply exprMatchObjectEvalEquivalent_RF_T_WithAttributesAll.
  } {
    apply exprMatchObjectEvalEquivalent_RF_T_WithAttributesAny.
  } {
    (* EMO_And *)
    intros Ht.
    inversion Ht as [ | | | |es0 Hfa Heq|].
    subst es0.
    simpl.
    symmetry.
    rewrite forallb_forall.
    intros x Hin.
    symmetry.
    generalize dependent x.
    rewrite <- Forall_forall.
    apply (Forall_impl_lifted exprMatchObject _ _ es Hfa Hes).
  } {
    (* EMO_Or *)
    intros Ht.
    symmetry.
    simpl.
    rewrite existsb_exists.

    inversion Ht as [ | | | | |es0 Hex Heq].
    subst es.
    destruct Hex as [k ks Hk|k ks Hk]. {
      exists k.
      constructor.
      constructor; reflexivity.
      apply (eq_sym (Forall_inv Hes Hk)).
    } {
      rewrite Exists_exists in Hk.
      destruct Hk as [q [Hq0 Hq1]].
      exists q.
      constructor.
      apply (in_cons k q ks Hq0).
      pose proof (Forall_inv_tail Hes) as HesT.
      rewrite Forall_forall in HesT.
      apply (eq_sym (HesT q Hq0 Hq1)).
    }
  }
Qed.

(** The evaluation function and the evaluation relation are equivalent. *)
Theorem exprMatchObjectEvalEquivalentT : forall s e,
  true = exprMatchObjectEvalF s e <-> exprMatchObjectEvalR s e.
Proof.
  split.
  apply exprMatchObjectEvalEquivalent_FR_T.
  apply exprMatchObjectEvalEquivalent_RF_T.
Qed.

Lemma exprMatchObjectEvalEquivalent_FR_F : forall a e,
  false = exprMatchObjectEvalF a e -> ~exprMatchObjectEvalR a e.
Proof.
  intros s e.
  induction e as [
    |
    |
    |
    |
    |es Hes
    |es Hes
  ] using exprMatchObject_extendedInd. {
    (* EMO_False *)
    intros Ht.
    intro Hcontra.
    inversion Hcontra.
  } {
    (* EMO_True *)
    intros Ht.
    contradict Ht.
    discriminate.
  } {
    (* EMO_WithType *)
    intros Ht.
    intros Hcontra.
    rewrite <- (exprMatchObjectEvalEquivalent_RF_T _ _ Hcontra) in Ht.
    contradict Ht; discriminate.
  } {
    (* EMO_WithAttributesAll *)
    intros Ht.
    intros Hcontra.
    rewrite <- (exprMatchObjectEvalEquivalent_RF_T _ _ Hcontra) in Ht.
    contradict Ht; discriminate.
  } {
    (* EMO_WithAttributesAny *)
    intros Ht.
    intros Hcontra.
    rewrite <- (exprMatchObjectEvalEquivalent_RF_T _ _ Hcontra) in Ht.
    contradict Ht; discriminate.
  } {
    (* EMS_And *)
    intros Ht.
    intros Hcontra.
    rewrite <- (exprMatchObjectEvalEquivalent_RF_T _ _ Hcontra) in Ht.
    contradict Ht; discriminate.
  } {
    (* EMS_Or *)
    intros Ht.
    intros Hcontra.
    rewrite <- (exprMatchObjectEvalEquivalent_RF_T _ _ Hcontra) in Ht.
    contradict Ht; discriminate.
  }
Qed.

Lemma exprMatchObjectEvalEquivalent_RF_F : forall a e,
  ~exprMatchObjectEvalR a e -> false = exprMatchObjectEvalF a e.
Proof.
  intros s e.
  induction e as [
    |
    |
    |
    |
    |es Hes
    |es Hes
  ] using exprMatchObject_extendedInd. {
    (* EMO_False *)
    intros Ht.
    reflexivity.
  } {
    (* EMO_True *)
    intros Ht.
    contradict Ht.
    constructor.
  } {
    (* EMS_WithType *)
    intros Ht.
    destruct (exprMatchObjectEvalF s (EMO_WithType n)) eqn:H. {
      symmetry in H.
      rewrite exprMatchObjectEvalEquivalentT in H.
      contradiction.
    } {
      reflexivity.
    }
  } {
    (* EMO_WithAttributesAll *)
    intros Ht.
    destruct (exprMatchObjectEvalF s (EMO_WithAttributesAll n)) eqn:H. {
      symmetry in H.
      rewrite exprMatchObjectEvalEquivalentT in H.
      contradiction.
    } {
      reflexivity.
    }
  } {
    (* EMO_WithAttributesAny *)
    intros Ht.
    destruct (exprMatchObjectEvalF s (EMO_WithAttributesAny n)) eqn:H. {
      symmetry in H.
      rewrite exprMatchObjectEvalEquivalentT in H.
      contradiction.
    } {
      reflexivity.
    }
  } {
    (* EMS_And *)
    intros Ht.
    destruct (exprMatchObjectEvalF s (EMO_And es)) eqn:H. {
      symmetry in H.
      rewrite exprMatchObjectEvalEquivalentT in H.
      contradiction.
    } {
      reflexivity.
    }
  } {
    (* EMS_Or *)
    intros Ht.
    destruct (exprMatchObjectEvalF s (EMO_Or es)) eqn:H. {
      symmetry in H.
      rewrite exprMatchObjectEvalEquivalentT in H.
      contradiction.
    } {
      reflexivity.
    }
  }
Qed.

(** The evaluation function and the evaluation relation are equivalent. *)
Theorem exprMatchObjectEvalEquivalentF : forall a e,
  false = exprMatchObjectEvalF a e <-> ~exprMatchObjectEvalR a e.
Proof.
  split.
  apply exprMatchObjectEvalEquivalent_FR_F.
  apply exprMatchObjectEvalEquivalent_RF_F.
Qed.

(** The evaluation relation is decidable. *)
Theorem exprMatchObjectEvalRDec : forall o e,
  {exprMatchObjectEvalR o e}+{~exprMatchObjectEvalR o e}.
Proof.
  intros o e.
  destruct (exprMatchObjectEvalF o e) eqn:Hev. {
    symmetry in Hev.
    rewrite exprMatchObjectEvalEquivalentT in Hev.
    left; intuition.
  } {
    symmetry in Hev.
    rewrite exprMatchObjectEvalEquivalentF in Hev.
    right; intuition.
  }
Qed.
