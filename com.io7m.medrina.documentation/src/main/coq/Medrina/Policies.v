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

Require Import Medrina.Subjects.
Require Import Medrina.Objects.
Require Import Medrina.Actions.
Require Import Medrina.Rules.
Require Import Medrina.ListEx.

Require Import Coq.Lists.List.
Require Import Psatz.

Import ListNotations.

Definition policy :=
  list rule.

Inductive access : Set :=
  | AccessAllowed
  | AccessDenied
  .

Definition ruleConclusionAccess (c : ruleConclusion) : access :=
  match c with
  | RC_Allow            => AccessAllowed
  | RC_AllowImmediately => AccessAllowed
  | RC_Deny             => AccessDenied
  | RC_DenyImmediately  => AccessDenied
  end.

Inductive halt : Set :=
  | Halt
  | HContinue
  .

Inductive evaluationOfRule : Set :=
  | ERuleMatched     : halt -> access -> evaluationOfRule
  | ERuleDidNotMatch : evaluationOfRule
  .

Definition evaluateRule
  (r : rule)
  (s : subject)
  (o : object)
  (a : action)
: evaluationOfRule :=
  match ruleMatchesF s o a r with
  | true =>
    match (rConclusion r) with
    | RC_Allow =>
      ERuleMatched HContinue AccessAllowed
    | RC_AllowImmediately =>
      ERuleMatched Halt AccessAllowed
    | RC_Deny =>
      ERuleMatched HContinue AccessDenied
    | RC_DenyImmediately =>
      ERuleMatched Halt AccessDenied
    end
  | false =>
    ERuleDidNotMatch
  end.

Fixpoint evaluateRulesInF
  (acc : access)
  (rs  : list rule)
  (s   : subject)
  (o   : object)
  (a   : action)
: access :=
  match rs with
  | []      => acc
  | x :: xs =>
    match evaluateRule x s o a with
    | ERuleMatched h acc_new =>
      match h with
      | Halt      => acc_new
      | HContinue => evaluateRulesInF acc_new xs s o a
      end
    | ERuleDidNotMatch =>
        evaluateRulesInF acc xs s o a
    end
  end.

Definition evaluateRules
  (rs  : list rule)
  (s   : subject)
  (o   : object)
  (a   : action)
: access :=
  evaluateRulesInF AccessDenied rs s o a.

Definition evaluatePolicy
  (p : policy)
  (s : subject)
  (o : object)
  (a : action)
: access :=
  evaluateRules p s o a.

Definition ruleMatchesWithConclusion
  (s : subject)
  (o : object)
  (a : action)
  (r : rule)
  (c : ruleConclusion)
: Prop :=
  ruleMatchesF s o a r = true /\ (rConclusion r) = c.

Definition ruleDoesNotHaltOnMatch
  (r : rule)
: Prop :=
  ((rConclusion r) = RC_Allow \/ (rConclusion r) = RC_Deny).

Definition ruleHaltsOnMatch
  (r : rule)
: Prop :=
  ((rConclusion r) = RC_AllowImmediately \/ (rConclusion r) = RC_DenyImmediately).

Theorem evaluateRulesInFSplit :
  forall (s : subject)
         (o : object)
         (a : action),
  forall (r : rule), ruleMatchesF s o a r = true ->
    forall r_pre : list rule, Forall (fun q => ruleDoesNotHaltOnMatch q) r_pre ->
      forall acc, evaluateRulesInF acc (r_pre ++ [r]) s o a = evaluateRulesInF acc [r] s o a.
Proof.
  intros s o a r Hm r_pre.
  induction r_pre as [|z zs].
  {
    reflexivity.
  } {
    simpl.
    unfold evaluateRule.
    rewrite Hm.
    destruct (ruleMatchesF s o a z) eqn:Hzmat. {
      intros Hfa acc.
      pose proof (Forall_inv Hfa) as H0. simpl in H0.
      unfold ruleDoesNotHaltOnMatch in H0.

      destruct (rConclusion z) eqn:Hrcz. {
        destruct H0 as [H0L|H0R].
          - destruct (rConclusion r) eqn:Hrcr;
            (pose proof (IHzs (Forall_inv_tail Hfa) AccessAllowed) as IH0;
             rewrite IH0;
             simpl;
             unfold evaluateRule;
             rewrite Hm;
             rewrite Hrcr;
             reflexivity).
          - contradict H0R; discriminate.
      } {
        destruct H0 as [H0L|H0R].
          - destruct (rConclusion r) eqn:Hrcr; (try reflexivity; try (contradict H0L; discriminate)).
          - contradict H0R; discriminate.
      } {
        destruct H0 as [H0L|H0R].
          - contradict H0L; discriminate.
          - destruct (rConclusion r) eqn:Hrcr;
            (pose proof (IHzs (Forall_inv_tail Hfa) AccessDenied) as IH0;
             rewrite IH0;
             simpl;
             unfold evaluateRule;
             rewrite Hm;
             rewrite Hrcr;
             reflexivity).
      } {
        destruct H0 as [H|H]; (contradict H; discriminate).
      }
    } {
      intros Hfa acc.
      rewrite (IHzs (Forall_inv_tail Hfa) acc).
      simpl.
      unfold evaluateRule.
      rewrite Hm.
      reflexivity.
    }
  }
Qed.

Theorem evaluateRulesInFSplitHalt :
  forall (s : subject)
         (o : object)
         (a : action),
  forall (r : rule), ruleMatchesF s o a r = true /\ ruleHaltsOnMatch r ->
    forall r_pre : list rule, Forall (fun q => ruleDoesNotHaltOnMatch q) r_pre ->
      forall r_post : list rule,
        forall acc0 acc1, evaluateRulesInF acc0 (r_pre ++ [r] ++ r_post) s o a = evaluateRulesInF acc1 [r] s o a.
Proof.
  intros s o a r [Hm0 Hm1] r_pre.
  induction r_pre as [|z zs]. {
    simpl.
    unfold evaluateRule.
    rewrite Hm0.
    destruct Hm1 as [H|H]; (rewrite H; reflexivity).
  } {
    intros Hfa.
    intros r_post acc0.
    simpl (evaluateRulesInF acc0 ((z :: zs) ++ [r] ++ r_post) s o a) at 1.
    unfold evaluateRule.
    destruct (ruleMatchesF s o a z) eqn:Hzmat. {
      pose proof (Forall_inv Hfa) as [H|H];
        (rewrite H;
         apply IHzs;
         apply (Forall_inv_tail Hfa)).
    } {
      apply IHzs.
      apply (Forall_inv_tail Hfa).
    }
  }
Qed.

Definition ruleAllows (r : rule) : Prop :=
  ((rConclusion r) = RC_AllowImmediately \/ (rConclusion r) = RC_Allow).

Theorem evaluateRulesInFHaltAllow :
  forall (s : subject)
         (o : object)
         (a : action),
  forall (r : rule), ruleMatchesF s o a r = true /\ ruleHaltsOnMatch r /\ ruleAllows r ->
    forall r_pre : list rule, Forall (fun q => ruleDoesNotHaltOnMatch q) r_pre ->
      forall r_post : list rule,
        forall acc, evaluateRulesInF acc (r_pre ++ [r] ++ r_post) s o a = AccessAllowed.
Proof.
  intros s o a r [Hm0 [Hm1L Hm1R]] r_pre.
  intros Hfa.
  intros r_post acc.
  rewrite (evaluateRulesInFSplitHalt s o a r (conj Hm0 Hm1L) r_pre Hfa r_post acc acc).
  simpl.
  unfold evaluateRule.
  rewrite Hm0.
  destruct Hm1R as [H|H]; (rewrite H; reflexivity).
Qed.

Definition ruleDenies (r : rule) : Prop :=
  ((rConclusion r) = RC_DenyImmediately \/ (rConclusion r) = RC_Deny).

Theorem evaluateRulesInFHaltDeny :
  forall (s : subject)
         (o : object)
         (a : action),
  forall (r : rule), ruleMatchesF s o a r = true /\ ruleHaltsOnMatch r /\ ruleDenies r ->
    forall r_pre : list rule, Forall (fun q => ruleDoesNotHaltOnMatch q) r_pre ->
      forall r_post : list rule,
        forall acc, evaluateRulesInF acc (r_pre ++ [r] ++ r_post) s o a = AccessDenied.
Proof.
  intros s o a r [Hm0 [Hm1L Hm1R]] r_pre.
  intros Hfa.
  intros r_post acc.
  rewrite (evaluateRulesInFSplitHalt s o a r (conj Hm0 Hm1L) r_pre Hfa r_post acc acc).
  simpl.
  unfold evaluateRule.
  rewrite Hm0.
  destruct Hm1R as [H|H]; (rewrite H; reflexivity).
Qed.

Definition ruleDoesNotMatch
  (s : subject)
  (o : object)
  (a : action)
  (r : rule)
: Prop :=
  ruleMatchesF s o a r = false.

Theorem evaluateRulesInFPreNotMatching :
  forall (s : subject)
         (o : object)
         (a : action),
  forall r_pre : list rule,
    Forall (fun q => ruleDoesNotMatch s o a q) r_pre ->
      forall r_post : list rule,
        forall acc, evaluateRulesInF acc (r_pre ++ r_post) s o a = evaluateRulesInF acc r_post s o a.
Proof.
  intros s o a.
  induction r_pre as [|z zs IH]. {
    intros.
    rewrite app_nil_l.
    reflexivity.
  } {
    intros Hfa r_post acc.
    simpl (evaluateRulesInF acc ((z :: zs) ++ r_post) s o a) at 1.
    unfold evaluateRule.
    rewrite (Forall_inv Hfa).
    apply IH.
    apply (Forall_inv_tail Hfa).
  }
Qed.

Theorem evaluateRulesInFPostNotMatching :
  forall (s : subject)
         (o : object)
         (a : action),
  forall r_post : list rule,
    Forall (fun q => ruleDoesNotMatch s o a q) r_post ->
      forall r_pre : list rule,
        forall acc, evaluateRulesInF acc (r_pre ++ r_post) s o a = evaluateRulesInF acc r_pre s o a.
Proof.
  intros s o a r_post Hfa.
  induction r_post as [|z zs IH]. {
    intros r_pre.
    rewrite app_nil_r.
    reflexivity.
  } {
    induction r_pre as [|w ws IHp]. {
      intros acc.
      rewrite <- (IH (Forall_inv_tail Hfa) [] acc).
      rewrite app_nil_l.
      rewrite app_nil_l.
      simpl.
      unfold evaluateRule.
      rewrite (Forall_inv Hfa).
      reflexivity.
    } {
      intros acc.
      simpl (evaluateRulesInF acc ((w :: ws) ++ z :: zs) s o a) at 1.
      unfold evaluateRule.
      destruct (ruleMatchesF s o a w) eqn:Hrwm. {
        destruct (rConclusion w) eqn:Hwc. {
          simpl (evaluateRulesInF acc (w :: ws) s o a) at 1.
          unfold evaluateRule.
          rewrite Hrwm.
          rewrite Hwc.
          apply IHp.
        } {
          simpl (evaluateRulesInF acc (w :: ws) s o a) at 1.
          unfold evaluateRule.
          rewrite Hrwm.
          rewrite Hwc.
          reflexivity.
        } {
          simpl (evaluateRulesInF acc (w :: ws) s o a) at 1.
          unfold evaluateRule.
          rewrite Hrwm.
          rewrite Hwc.
          apply IHp.
        } {
          simpl (evaluateRulesInF acc (w :: ws) s o a) at 1.
          unfold evaluateRule.
          rewrite Hrwm.
          rewrite Hwc.
          reflexivity.
        }
      } {
        simpl (evaluateRulesInF acc (w :: ws) s o a) at 1.
        unfold evaluateRule.
        rewrite Hrwm.
        apply IHp.
      }
    }
  }
Qed.

Theorem evaluateRulesInFPreNotHalting :
  forall (s : subject)
         (o : object)
         (a : action),
  forall (r : rule), ruleMatchesF s o a r = true ->
    forall r_pre : list rule,
      Forall (fun q => ruleDoesNotHaltOnMatch q) r_pre ->
        forall acc, evaluateRulesInF acc (r_pre ++ [r]) s o a = ruleConclusionAccess (rConclusion r).
Proof.
  intros s o a r Hrm.
  induction r_pre as [|z zs]. {
    simpl.
    unfold evaluateRule.
    rewrite Hrm.
    intros Hfa acc.
    destruct (rConclusion r); reflexivity.
  } {
    intros Hfa.
    intros acc.
    simpl (evaluateRulesInF acc ((z :: zs) ++ [r]) s o a) at 1.
    unfold evaluateRule.
    destruct (ruleMatchesF s o a z) eqn:Hzm. {
      destruct (Forall_inv Hfa) as [H|H];
        (rewrite H; apply IHzs; apply (Forall_inv_tail Hfa)).
    } {
      apply IHzs.
      apply (Forall_inv_tail Hfa).
    }
  }
Qed.

Theorem evaluateRulesInFLastMatching :
  forall (s : subject)
         (o : object)
         (a : action),
  forall (r : rule), ruleMatchesF s o a r = true ->
    forall r_pre : list rule,
      Forall (fun q => ruleDoesNotHaltOnMatch q) r_pre ->
        forall r_post : list rule,
          Forall (fun q => ruleDoesNotMatch s o a q) r_post ->
            forall acc, evaluateRulesInF acc (r_pre ++ [r] ++ r_post) s o a = ruleConclusionAccess (rConclusion r).
Proof.
  intros s o a r Hrm.
  induction r_pre as [|z zs]. {
    intros Hfa r_post.
    rewrite app_nil_l.
    simpl.
    unfold evaluateRule.
    rewrite Hrm.
    destruct (rConclusion r) eqn:Hrcr. {
      induction r_post as [|w ws IH]. {
        reflexivity.
      } {
        intros Hfaw acc.
        simpl.
        unfold evaluateRule.
        rewrite (Forall_inv Hfaw).
        rewrite IH.
        reflexivity.
        apply (Forall_inv_tail Hfaw).
        exact acc.
      }
    } {
      induction r_post; reflexivity.
    } {
      induction r_post as [|w ws IH]. {
        reflexivity.
      } {
        intros Hfaw acc.
        simpl.
        unfold evaluateRule.
        rewrite (Forall_inv Hfaw).
        rewrite IH.
        reflexivity.
        apply (Forall_inv_tail Hfaw).
        exact acc.
      }
    } {
      induction r_post; reflexivity.
    }
  } {
    intros Hfaz.
    simpl.
    destruct (Forall_inv Hfaz) as [H|H]. {
      unfold evaluateRule.
      rewrite H.
      destruct (ruleMatchesF s o a z) eqn:Hmz. {
        intros r_post Hfap acc.
        apply (IHzs (Forall_inv_tail Hfaz) r_post Hfap AccessAllowed).
      } {
        intros r_post Hfap acc.
        apply (IHzs (Forall_inv_tail Hfaz) r_post Hfap acc).
      }
    } {
      unfold evaluateRule.
      rewrite H.
      destruct (ruleMatchesF s o a z) eqn:Hmz. {
        intros r_post Hfap acc.
        apply (IHzs (Forall_inv_tail Hfaz) r_post Hfap AccessDenied).
      } {
        intros r_post Hfap acc.
        apply (IHzs (Forall_inv_tail Hfaz) r_post Hfap acc).
      }
    }
  }
Qed.

Theorem evaluateRulesInFLastMatchingPreNoHalt :
  forall (s : subject)
         (o : object)
         (a : action),
  forall (r : rule), ruleMatchesF s o a r = true ->
    forall r_pre : list rule,
      Forall (fun q => ruleDoesNotHaltOnMatch q) r_pre ->
        forall r_post : list rule,
          Forall (fun q => ruleDoesNotMatch s o a q) r_post ->
            forall acc, evaluateRulesInF acc (r_pre ++ [r] ++ r_post) s o a = evaluateRulesInF acc [r] s o a.
Proof.
  intros s o a r Hrm.
  assert (forall acc q, ruleMatchesF s o a q = true ->
    evaluateRulesInF acc [q] s o a = ruleConclusionAccess (rConclusion q)) as H0. {
    intros acc q Hq.
    simpl.
    unfold evaluateRule.
    rewrite Hq.
    destruct (rConclusion q); reflexivity.
  }

  intros.
  rewrite (H0 acc r Hrm).
  apply evaluateRulesInFLastMatching; trivial.
Qed.

(*
 * Externally visible proofs.
 *)

(** If no rules in a policy match, the default is to deny access. *)
Theorem evaluateRulesDefaultDenyNoMatches : forall rs s o a,
  Forall (fun r => ruleMatchesF s o a r = false) rs ->
    evaluateRules rs s o a = AccessDenied.
Proof.
  unfold evaluateRules.
  induction rs as [|y ys IH]. {
    reflexivity.
  } {
    intros s o a Hfa.
    pose proof (IH s o a (Forall_inv_tail Hfa)) as Hfa0.
    pose proof (Forall_inv Hfa) as Hfa1.
    simpl in Hfa1.
    simpl.
    unfold evaluateRule.
    rewrite Hfa1.
    exact Hfa0.
  }
Qed.

(** If a policy consists of a sequence of rules _r_pre_ that do not halt on
    matching, followed by a rule _r_ that does match, followed by a
    possibly-empty sequence of rules _r_post_ that do not match, then
    evaluation is equivalent to evaluating _r_ on its own. *)

Theorem evaluateRulesLastMatchingPreNoHalt :
  forall (s      : subject)
         (o      : object)
         (a      : action)
         (r      : rule)
         (r_pre  : list rule)
         (r_post : list rule),
  ruleMatchesF s o a r = true ->
    Forall (fun q => ruleDoesNotHaltOnMatch q) r_pre ->
      Forall (fun q => ruleDoesNotMatch s o a q) r_post ->
        evaluateRules (r_pre ++ [r] ++ r_post) s o a = evaluateRules [r] s o a.
Proof.
  unfold evaluateRules.
  intros.
  apply evaluateRulesInFLastMatchingPreNoHalt; trivial.
Qed.

(** If a policy consists of a sequence or rules _r_pre_, followed
    by a sequence of rules _r_post_ that do not match, then the result
    is equivalent to evaluating _r_pre_. *)

Theorem evaluateRulesPostNotMatching :
  forall (s      : subject)
         (o      : object)
         (a      : action)
         (r_pre  : list rule)
         (r_post : list rule),
  Forall (fun q => ruleDoesNotMatch s o a q) r_post ->
    evaluateRules (r_pre ++ r_post) s o a = evaluateRules r_pre s o a.
Proof.
  unfold evaluateRules.
  intros.
  apply evaluateRulesInFPostNotMatching; trivial.
Qed.

(** If a policy consists of a sequence or rules _r_pre_ that do not match,
    followed by a sequence of rules _r_post_, then the result is equivalent 
    to evaluating _r_post_. *)

Theorem evaluateRulesPreNotMatching :
  forall (s      : subject)
         (o      : object)
         (a      : action)
         (r_pre  : list rule)
         (r_post : list rule),
  Forall (fun q => ruleDoesNotMatch s o a q) r_pre ->
    evaluateRules (r_pre ++ r_post) s o a = evaluateRules r_post s o a.
Proof.
  unfold evaluateRules.
  intros.
  apply evaluateRulesInFPreNotMatching; trivial.
Qed.
