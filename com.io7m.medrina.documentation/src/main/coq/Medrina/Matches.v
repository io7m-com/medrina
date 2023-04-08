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

Require Import Medrina.Actions.
Require Import Medrina.Names.
Require Import Medrina.Subjects.
Require Import Medrina.Roles.
Require Import Medrina.Objects.

(** An expression that matches a subject. *)
Inductive exprMatchSubject : Type :=
  | EMS_False : exprMatchSubject
  | EMS_True : exprMatchSubject
  | EMS_WithRolesAll :
    forall (r : RoleSets.t),
      exprMatchSubject
  | EMS_WithRolesAny :
    forall (r : RoleSets.t),
      exprMatchSubject
  | EMS_And :
    exprMatchSubject ->
      exprMatchSubject ->
        exprMatchSubject
  | EMS_Or :
    exprMatchSubject ->
      exprMatchSubject ->
        exprMatchSubject
  .

(** An evaluation function for subject match expressions. *)
Fixpoint exprMatchSubjectEvalF
  (s : subject)
  (e : exprMatchSubject)
: bool :=
  match e with
  | EMS_False => false
  | EMS_True => true
  | EMS_WithRolesAll r =>
    RoleSets.subset r (sRoles s)
  | EMS_WithRolesAny r =>
    RoleSets.exists_ (fun x => RoleSets.mem x (sRoles s)) r
  | EMS_And x y =>
    andb (exprMatchSubjectEvalF s x) (exprMatchSubjectEvalF s y)
  | EMS_Or x y =>
    orb (exprMatchSubjectEvalF s x) (exprMatchSubjectEvalF s y)
  end.

(** The evaluation function for subject match expressions as a relation. *)
Inductive exprMatchSubjectEvalR : subject -> exprMatchSubject -> Prop :=
  | EMSR_True :
    forall (s : subject),
      exprMatchSubjectEvalR s EMS_True
  | EMSR_WithRolesAll :
    forall (s : subject) (r : RoleSets.t),
      RoleSets.Subset r (sRoles s) ->
        exprMatchSubjectEvalR s (EMS_WithRolesAll r)
  | EMSR_WithRolesAny :
    forall (s : subject) (r : RoleSets.t),
      (exists x, RoleSets.In x r /\ RoleSets.In x (sRoles s)) ->
        exprMatchSubjectEvalR s (EMS_WithRolesAny r)
  | EMSR_And :
    forall (s : subject) (e0 e1 : exprMatchSubject),
      exprMatchSubjectEvalR s e0 /\ exprMatchSubjectEvalR s e1 ->
        exprMatchSubjectEvalR s (EMS_And e0 e1)
  | EMSR_Or :
    forall (s : subject) (e0 e1 : exprMatchSubject),
      exprMatchSubjectEvalR s e0 \/ exprMatchSubjectEvalR s e1 ->
        exprMatchSubjectEvalR s (EMS_Or e0 e1)
  .

(** The evaluation function and the evaluation relation are equivalent. *)
Theorem exprMatchSubjectEvalEquivalentT : forall s e,
  true = exprMatchSubjectEvalF s e <-> exprMatchSubjectEvalR s e.
Proof.
  intros s e.
  induction e as [
    |
    |r
    |r
    |e0 He0 e1 He1
    |e0 He0 e1 He1
  ]. {
    (* EMS_False *)
    split. {
      intros Ht.
      inversion Ht.
    } {
      intros Ht.
      inversion Ht.
    }
  } {
    (* EMS_True *)
    split. {
      intros Ht; constructor.
    } {
      intros Ht; reflexivity.
    }
  } {
    (* EMS_WithRolesAll *)
    split. {
      intros Ht.
      unfold exprMatchSubjectEvalF in Ht.
      constructor.
      apply RoleSets.subset_2.
      intuition.
    } {
      intros Ht.
      symmetry.
      apply RoleSets.subset_1.
      inversion Ht.
      intuition.
    }
  } {
    (* EMS_WithRolesAny *)
    split. {
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
      intros Ht.
      symmetry.
      inversion Ht as [ | |s0 r0 HHt| | ].
      subst s0.
      subst r0.
      simpl.
      assert (
        RoleSets.Exists 
          (fun x : RoleSets.elt => RoleSets.mem x (sRoles s) = true) r
      ) as Hex. {
        unfold RoleSets.Exists.
        destruct HHt as [y [Hy0 Hy1]].
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
    }
  } {
    (* EMS_And *)
    split. {
      intros Ht.
      constructor.
      simpl in Ht.
      pose proof (Bool.andb_true_eq _ _ Ht) as [HT0 HT1].
      intuition.
    } {
      intros Ht.
      inversion Ht as [ | | |s0 e2 e3 He| ].
      subst s0.
      subst e2.
      subst e3.
      rewrite <- He0 in He.
      rewrite <- He1 in He.
      symmetry.
      simpl.
      rewrite Bool.andb_true_iff.
      intuition.
    }
  } {
    (* EMS_Or *)
    split. {
      intros Ht.
      constructor.
      simpl in Ht.
      symmetry in Ht.
      pose proof (Bool.orb_prop _ _ Ht) as Hb.
      destruct Hb as [Hb0|Hb1]. {
        symmetry in Hb0.
        rewrite He0 in Hb0.
        intuition.
      } {
        symmetry in Hb1.
        rewrite He1 in Hb1.
        intuition.
      }
    } {
      intros Ht.
      simpl.
      symmetry.
      rewrite Bool.orb_true_iff.
      inversion Ht as [ | | |  |s0 e2 e3 He].
      subst s0.
      subst e2.
      subst e3.
      intuition.
    }
  }
Qed.

(** The evaluation function and the evaluation relation are equivalent. *)
Theorem exprMatchSubjectEvalEquivalentF : forall s e,
  false = exprMatchSubjectEvalF s e <-> ~exprMatchSubjectEvalR s e.
Proof.
  intros s e.
  induction e as [
    |
    |r
    |r
    |e0 He0 e1 He1
    |e0 He0 e1 He1
  ]. {
    (* EMS_False *)
    split. {
      intros Ht H; inversion H.
    } {
      intros Ht; reflexivity.
    }
  } {
    (* EMS_True *)
    split. {
      intros Ht; inversion Ht.
    } {
      intros Ht.
      intuition.
      assert (exprMatchSubjectEvalR s EMS_True) by constructor.
      contradiction.
    }
  } {
    (* EMS_WithRolesAll *)
    split. {
      intros Ht.
      unfold exprMatchSubjectEvalF in Ht.
      intros H.
      inversion H as [ |s0 r0 Hsub| | | ].
      subst s0.
      subst r0.
      pose proof (RoleSets.subset_1 Hsub) as Hsub2.
      rewrite <- Ht in Hsub2.
      contradict Hsub2; discriminate.
    } {
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
    }
  } {
    (* EMS_WithRolesAny *)
    split. {
      intros Ht.
      unfold exprMatchSubjectEvalF in Ht.

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

      symmetry in Ht.
      rewrite <- (roleExistsFalse r _ Hsetcomp) in Ht.
      unfold RoleSets.Exists in Ht.

      intros H.
      inversion H as [ | |s0 r0 Hsub| | ].
      subst s0.
      subst r0.

      inversion Hsub as [y [Hy0 Hy1]].
      rewrite RoleSetsFacts.mem_iff in Hy1.
      intuition.
      apply Ht.
      exists y.
      intuition.
    } {
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
    }
  } {
    (* EMS_And *)
    split. {
      intros Ht.
      intros Hcontra.
      inversion Hcontra as [ | | |s0 e2 e3 [Hf0 Hf1]| ].
      subst s0.
      subst e2.
      subst e3.
      simpl in Ht.
      destruct (Bool.andb_false_elim _ _ (eq_sym Ht)); intuition.
    } {
      intros Ht.
      destruct (exprMatchSubjectEvalF s (EMS_And e0 e1)) eqn:H. {
        symmetry in H.
        rewrite exprMatchSubjectEvalEquivalentT in H.
        contradiction.
      } {
        reflexivity.
      }
    }
  } {
    (* EMS_Or *)
    split. {
      intros Ht.
      intros Hcontra.
      inversion Hcontra as [ | | |s0 e2 e3 [Hf0 Hf1]| ].
      subst s0.
      subst e2.
      subst e3.
      simpl in Ht.
      destruct (Bool.orb_false_elim _ _ (eq_sym Ht)); intuition.
    } {
      intros Ht.
      destruct (exprMatchSubjectEvalF s (EMS_Or e0 e1)) eqn:H. {
        symmetry in H.
        rewrite exprMatchSubjectEvalEquivalentT in H.
        contradiction.
      } {
        reflexivity.
      }
    }
  }
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
  | EMA_False : exprMatchAction
  | EMA_True : exprMatchAction
  | EMA_WithName :
    forall (n : actionName),
      exprMatchAction
  | EMA_And :
    exprMatchAction ->
      exprMatchAction ->
        exprMatchAction
  | EMA_Or :
    exprMatchAction ->
      exprMatchAction ->
        exprMatchAction
  .

(** An evaluation function for action match expressions. *)
Fixpoint exprMatchActionEvalF
  (a : action)
  (e : exprMatchAction)
: bool :=
  match e with
  | EMA_False => false
  | EMA_True => true
  | EMA_WithName n =>
    eqb (ivName (aName a)) (ivName n)
  | EMA_And x y =>
    andb (exprMatchActionEvalF a x) (exprMatchActionEvalF a y)
  | EMA_Or x y =>
    orb (exprMatchActionEvalF a x) (exprMatchActionEvalF a y)
  end.

(** The evaluation function for action match expressions as a relation. *)
Inductive exprMatchActionEvalR : action -> exprMatchAction -> Prop :=
  | EMAR_True :
    forall (a : action),
      exprMatchActionEvalR a EMA_True
  | EMAR_WithName :
    forall (a : action) (x : actionName),
      ivName (aName a) = ivName x ->
        exprMatchActionEvalR a (EMA_WithName x)
  | EMAR_And :
    forall (a : action) (e0 e1 : exprMatchAction),
      exprMatchActionEvalR a e0 /\ exprMatchActionEvalR a e1 ->
        exprMatchActionEvalR a (EMA_And e0 e1)
  | EMAR_Or :
    forall (a : action) (e0 e1 : exprMatchAction),
      exprMatchActionEvalR a e0 \/ exprMatchActionEvalR a e1 ->
        exprMatchActionEvalR a (EMA_Or e0 e1)
  .

(** The evaluation function and the evaluation relation are equivalent. *)
Theorem exprMatchActionEvalEquivalentT : forall s e,
  true = exprMatchActionEvalF s e <-> exprMatchActionEvalR s e.
Proof.
  intros a e.
  induction e as [
    |
    |r
    |e0 He0 e1 He1
    |e0 He0 e1 He1
  ]. {
    (* EMA_False *)
    split. {
      intros Ht.
      inversion Ht.
    } {
      intros Ht.
      inversion Ht.
    }
  } {
    (* EMA_True *)
    split. {
      intros Ht; constructor.
    } {
      intros Ht; reflexivity.
    }
  } {
    (* EMA_WithName *)
    split. {
      intros Ht.
      unfold exprMatchActionEvalF in Ht.
      symmetry in Ht.
      rewrite eqb_eq in Ht.
      pose proof (ivIrrelevantEqual _ _ Ht).
      subst r.
      constructor.
      intuition.
    } {
      intros Ht.
      simpl.
      inversion Ht as [ |y z Hyz| | ].
      subst y.
      subst z.
      pose proof (ivIrrelevantEqual _ _ Hyz) as H0.
      rewrite H0.
      symmetry.
      apply eqb_refl.
    }
  } {
    (* EMA_And *)
    split. {
      intros Ht.
      simpl in Ht.
      pose proof (Bool.andb_true_eq _ _ Ht) as [HT0 HT1].
      constructor.
      intuition.
    } {
      intros Ht.
      inversion Ht as [ | |a0 e2 e3 He| ].
      subst a0.
      subst e2.
      subst e3.
      rewrite <- He0 in He.
      rewrite <- He1 in He.
      symmetry.
      simpl.
      rewrite Bool.andb_true_iff.
      intuition.
    }
  } {
    (* EMA_Or *)
    split. {
      intros Ht.
      constructor.
      simpl in Ht.
      symmetry in Ht.
      pose proof (Bool.orb_prop _ _ Ht) as Hb.
      destruct Hb as [Hb0|Hb1]. {
        symmetry in Hb0.
        rewrite He0 in Hb0.
        intuition.
      } {
        symmetry in Hb1.
        rewrite He1 in Hb1.
        intuition.
      }
    } {
      intros Ht.
      simpl.
      symmetry.
      rewrite Bool.orb_true_iff.
      inversion Ht as [ | | |a0 e2 e3 He].
      subst a0.
      subst e2.
      subst e3.
      intuition.
    }
  }
Qed.

(** The evaluation function and the evaluation relation are equivalent. *)
Theorem exprMatchActionEvalEquivalentF : forall a e,
  false = exprMatchActionEvalF a e <-> ~exprMatchActionEvalR a e.
Proof.
  intros a e.
  induction e as [
    |
    |r
    |e0 He0 e1 He1
    |e0 He0 e1 He1
  ]. {
    (* EMA_False *)
    split. {
      intros H Ht; inversion Ht.
    } {
      intros H; reflexivity.
    }
  } {
    (* EMA_True *)
    split. {
      intros H Ht.
      contradict H; discriminate.
    } {
      intros H.
      contradict H; constructor.
    }
  } {
    (* EMA_WithName *)
    split. {
      intros H Ht.
      inversion Ht as [ |o1 t1 Heq| | ].
      subst o1.
      subst t1.
      pose proof (ivIrrelevantEqual _ _ Heq) as Hir.
      subst r.
      contradict H.
      simpl.
      rewrite eqb_refl.
      discriminate.
    } {
      intros H.
      destruct (exprMatchActionEvalF a (EMA_WithName r)) eqn:Hd. {
        simpl in Hd.
        rewrite eqb_eq in Hd.
        pose proof (@ivIrrelevantEqual actionName _ _ _ Hd) as Heq.
        subst r.
        assert (
          exprMatchActionEvalR a (EMA_WithName (aName a))
        ) as Hcontra. {
          constructor.
          reflexivity.
        }
        contradiction.
      } {
        reflexivity.
      }
    }
  } {
    (* EMA_And *)
    split. {
      intros Ht.
      intros Hcontra.
      inversion Hcontra as [ | |a1 e2 e3 [Hf0 Hf1]| ].
      subst a1.
      subst e2.
      subst e3.
      simpl in Ht.
      destruct (Bool.andb_false_elim _ _ (eq_sym Ht)); intuition.
    } {
      intros Ht.
      destruct (exprMatchActionEvalF a (EMA_And e0 e1)) eqn:H. {
        symmetry in H.
        rewrite exprMatchActionEvalEquivalentT in H.
        contradiction.
      } {
        reflexivity.
      }
    }
  } {
    (* EMA_Or *)
    split. {
      intros Ht.
      intros Hcontra.
      inversion Hcontra as [ | | |a1 e2 e3 [Hf0|Hf1]].
      subst a1.
      subst e2.
      subst e3.
      simpl in Ht.
      destruct (Bool.orb_false_elim _ _ (eq_sym Ht)) as [Hk0 Hk1]. {
        symmetry in Hk0.
        rewrite He0 in Hk0.
        contradiction.
      }
      subst a1.
      subst e2.
      subst e3.
      simpl in Ht.
      destruct (Bool.orb_false_elim _ _ (eq_sym Ht)) as [Hk0 Hk1]. {
        symmetry in Hk1.
        rewrite He1 in Hk1.
        contradiction.
      }
    } {
      intros Ht.
      destruct (exprMatchActionEvalF a (EMA_Or e0 e1)) eqn:H. {
        symmetry in H.
        rewrite exprMatchActionEvalEquivalentT in H.
        contradiction.
      } {
        reflexivity.
      }
    }
  }
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
  | EMO_False : exprMatchObject
  | EMO_True : exprMatchObject
  | EMO_WithType :
    forall (n : typeName),
      exprMatchObject
  | EMO_And :
    exprMatchObject ->
      exprMatchObject ->
        exprMatchObject
  | EMO_Or :
    exprMatchObject ->
      exprMatchObject ->
        exprMatchObject
  .

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
  | EMO_And x y =>
    andb (exprMatchObjectEvalF o x) (exprMatchObjectEvalF o y)
  | EMO_Or x y =>
    orb (exprMatchObjectEvalF o x) (exprMatchObjectEvalF o y)
  end.

(** The evaluation function for object match expressions as a relation. *)
Inductive exprMatchObjectEvalR : object -> exprMatchObject -> Prop :=
  | EMOR_True :
    forall (o : object),
      exprMatchObjectEvalR o EMO_True
  | EMOR_WithName :
    forall (o : object) (t : typeName),
      ivName (oType o) = ivName t ->
        exprMatchObjectEvalR o (EMO_WithType t)
  | EMOR_And :
    forall (o : object) (e0 e1 : exprMatchObject),
      exprMatchObjectEvalR o e0 /\ exprMatchObjectEvalR o e1 ->
        exprMatchObjectEvalR o (EMO_And e0 e1)
  | EMOR_Or :
    forall (o : object) (e0 e1 : exprMatchObject),
      exprMatchObjectEvalR o e0 \/ exprMatchObjectEvalR o e1 ->
        exprMatchObjectEvalR o (EMO_Or e0 e1)
  .

(** The evaluation function and the evaluation relation are equivalent. *)
Theorem exprMatchObjectEvalEquivalentT : forall s e,
  true = exprMatchObjectEvalF s e <-> exprMatchObjectEvalR s e.
Proof.
  intros o e.
  induction e as [
    |
    |r
    |e0 He0 e1 He1
    |e0 He0 e1 He1
  ]. {
    (* EMO_False *)
    split. {
      intros Ht.
      inversion Ht.
    } {
      intros Ht.
      inversion Ht.
    }
  } {
    (* EMO_True *)
    split. {
      intros Ht; constructor.
    } {
      intros Ht; reflexivity.
    }
  } {
    (* EMO_WithType *)
    split. {
      intros Ht.
      unfold exprMatchObjectEvalF in Ht.
      symmetry in Ht.
      rewrite eqb_eq in Ht.
      pose proof (ivIrrelevantEqual _ _ Ht).
      subst r.
      constructor.
      intuition.
    } {
      intros Ht.
      simpl.
      inversion Ht as [ |y z Hyz| | ].
      subst y.
      subst z.
      pose proof (ivIrrelevantEqual _ _ Hyz) as H0.
      rewrite H0.
      symmetry.
      apply eqb_refl.
    }
  } {
    (* EMO_And *)
    split. {
      intros Ht.
      simpl in Ht.
      pose proof (Bool.andb_true_eq _ _ Ht) as [HT0 HT1].
      constructor.
      intuition.
    } {
      intros Ht.
      inversion Ht as [ | |a0 e2 e3 He| ].
      subst a0.
      subst e2.
      subst e3.
      rewrite <- He0 in He.
      rewrite <- He1 in He.
      symmetry.
      simpl.
      rewrite Bool.andb_true_iff.
      intuition.
    }
  } {
    (* EMO_Or *)
    split. {
      intros Ht.
      constructor.
      simpl in Ht.
      symmetry in Ht.
      pose proof (Bool.orb_prop _ _ Ht) as Hb.
      destruct Hb as [Hb0|Hb1]. {
        symmetry in Hb0.
        rewrite He0 in Hb0.
        intuition.
      } {
        symmetry in Hb1.
        rewrite He1 in Hb1.
        intuition.
      }
    } {
      intros Ht.
      simpl.
      symmetry.
      rewrite Bool.orb_true_iff.
      inversion Ht as [ | | |a0 e2 e3 He].
      subst a0.
      subst e2.
      subst e3.
      intuition.
    }
  }
Qed.

(** The evaluation function and the evaluation relation are equivalent. *)
Theorem exprMatchObjectEvalEquivalentF : forall s e,
  false = exprMatchObjectEvalF s e <-> ~exprMatchObjectEvalR s e.
Proof.
  intros o e.
  induction e as [
    |
    |r
    |e0 He0 e1 He1
    |e0 He0 e1 He1
  ]. {
    (* EMO_False *)
    split. {
      intros H Ht; inversion Ht.
    } {
      intros H; reflexivity.
    }
  } {
    (* EMO_True *)
    split. {
      intros H Ht.
      contradict H; discriminate.
    } {
      intros H.
      contradict H; constructor.
    }
  } {
    (* EMO_WithType *)
    split. {
      intros H Ht.
      inversion Ht as [ |o1 t1 Heq| | ].
      subst o1.
      subst t1.
      pose proof (ivIrrelevantEqual _ _ Heq) as Hir.
      subst r.
      contradict H.
      simpl.
      rewrite eqb_refl.
      discriminate.
    } {
      intros H.
      destruct (exprMatchObjectEvalF o (EMO_WithType r)) eqn:Hd. {
        simpl in Hd.
        rewrite eqb_eq in Hd.
        pose proof (ivIrrelevantEqual _ _ Hd) as Heq.
        subst r.
        assert (
          exprMatchObjectEvalR o (EMO_WithType (oType o))
        ) as Hcontra. {
          constructor.
          reflexivity.
        }
        contradiction.
      } {
        reflexivity.
      }
    }
  } {
    (* EMO_And *)
    split. {
      intros Ht.
      intros Hcontra.
      inversion Hcontra as [ | |o1 e2 e3 [Hf0 Hf1]| ].
      subst o1.
      subst e2.
      subst e3.
      simpl in Ht.
      destruct (Bool.andb_false_elim _ _ (eq_sym Ht)); intuition.
    } {
      intros Ht.
      destruct (exprMatchObjectEvalF o (EMO_And e0 e1)) eqn:H. {
        symmetry in H.
        rewrite exprMatchObjectEvalEquivalentT in H.
        contradiction.
      } {
        reflexivity.
      }
    }
  } {
    (* EMO_Or *)
    split. {
      intros Ht.
      intros Hcontra.
      inversion Hcontra as [ | | |o1 e2 e3 [Hf0|Hf1]].
      subst o1.
      subst e2.
      subst e3.
      simpl in Ht.
      destruct (Bool.orb_false_elim _ _ (eq_sym Ht)) as [Hk0 Hk1]. {
        symmetry in Hk0.
        rewrite He0 in Hk0.
        contradiction.
      }
      subst o1.
      subst e2.
      subst e3.
      simpl in Ht.
      destruct (Bool.orb_false_elim _ _ (eq_sym Ht)) as [Hk0 Hk1]. {
        symmetry in Hk1.
        rewrite He1 in Hk1.
        contradiction.
      }
    } {
      intros Ht.
      destruct (exprMatchObjectEvalF o (EMO_Or e0 e1)) eqn:H. {
        symmetry in H.
        rewrite exprMatchObjectEvalEquivalentT in H.
        contradiction.
      } {
        reflexivity.
      }
    }
  }
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
