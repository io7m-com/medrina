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

Require Import Coq.Lists.List.
Require Import Psatz.

Import ListNotations.

Local Set Implicit Arguments.

Section ListExes.
  Variable A : Type.

  Fixpoint listAt
    (n  : nat)
    (xs : list A) 
    {struct xs} 
  : option A :=
    match n, xs with
      | O,   y :: ys => Some y
      | O,   []      => None
      | S m, []      => None
      | S m, y :: ys => listAt m ys
    end.

  Theorem listAtNone : forall (n : nat) (s : list A),
    n >= length s -> listAt n s = None.
  Proof.
    induction n as [|m IH]. {
      intros s Hs.
      destruct s as [|y ys]. {
        reflexivity.
      } {
        assert (length (y :: ys) >= 1) as Hge. {
          simpl. lia.
        }
        contradict Hs.
        lia.
      }
    } {
      intros s Heq.
      destruct s as [|x xs]. {
        reflexivity.
      } {
        simpl.
        apply IH.
        simpl in Heq.
        lia.
      }
    }
  Qed.

  Theorem listAtSome : forall (n : nat) (s : list A),
    n < length s -> exists k, listAt n s = Some k.
  Proof.
    induction n as [|m IH]. {
      intros s Hs.
      destruct s as [|y ys]. {
        simpl in Hs.
        contradict Hs.
        intuition.
      } {
        exists y.
        reflexivity.
      }
    } {
      intros s Heq.
      destruct s as [|x xs]. {
        simpl in Heq.
        contradict Heq.
        lia.
      } {
        simpl.
        apply IH.
        simpl in Heq.
        lia.
      }
    }
  Qed.

  Theorem listAtIn : forall (s : list A) (x : A) (n : nat) ,
    listAt n s = Some x -> In x s.
  Proof.
    induction s as [|y ys IH]. {
      intros x n Hsome.
      contradict Hsome.
      simpl.
      destruct n; discriminate.
    } {
      intros x n Hsome.
      simpl in *.
      destruct n as [|m]. {
        left.
        assert (y = x) by congruence.
        trivial.
      } {
        right.
        apply (IH _ _ Hsome).
      }
    }
  Qed.

  Definition listSplit (xs : list A) (x : A) (n : nat) : Prop :=
    exists p q, (
         (xs = p ++ (x :: q))
      /\ (length p = n)
      /\ (forall m, m < n -> listAt m xs = listAt m p)
    ).

  Theorem listAtSplit : forall (n : nat) (xs : list A) (x : A),
    listAt n xs = Some x ->
      listSplit xs x n.
  Proof.
    induction n as [|m IH]. {
      destruct xs as [|y ys]. {
        intros x Hcontra.
        contradict Hcontra; discriminate.
      } {
        intros x Hsome.
        simpl in Hsome.
        assert (y = x) by congruence.
        subst y.
        exists [].
        exists ys.
        split. reflexivity.
        split. reflexivity.
        intros m Hfalse.
        contradict Hfalse.
        lia.
      }
    } {
      intros xs x Hsome.
      destruct xs as [|y ys]. {
        contradict Hsome; discriminate.
      } {
        simpl in Hsome.
        pose proof (IH _ _ Hsome) as [r [s [Hf0 [Hf1 Hf2]]]].
        rewrite <- Hf1.
        exists (y :: r).
        exists s.
        rewrite Hf0.
        split. reflexivity.
        split. reflexivity.
        intros z Hat.
        destruct z. {
          reflexivity.
        } {
          simpl.
          rewrite <- (Hf2 z).
          rewrite <- Hf0.
          reflexivity.
          lia.
        }
      }
    }
  Qed.

  Section ForAll.
    Variable P : A -> Prop.

    Definition listSplitForAll
      (xs : list A)
      (x  : A)
      (f  : Forall P xs)
      (n  : nat) 
    : Prop :=
      exists p q, ((xs = p ++ (x :: q)) /\ (Forall P (p ++ (x :: q)))).

    Theorem listAtSplitFA : forall (n : nat) (xs : list A) (x : A),
      forall (H : Forall P xs),
        (listAt n xs = Some x) ->
          @listSplitForAll xs x H n.
    Proof.
      induction n as [|m IH]. {
        destruct xs as [|y ys]. {
          intros x Hfa Hcontra.
          contradict Hcontra; discriminate.
        } {
          intros x Hfa Hsome.
          simpl in Hsome.
          assert (y = x) by congruence.
          subst y.
          exists [].
          exists ys.
          split. reflexivity.
          rewrite app_nil_l.
          exact Hfa.
        }
      } {
        intros xs x Hfa Hsome.
        destruct xs as [|y ys]. {
          contradict Hsome; discriminate.
        } {
          simpl in Hsome.
          pose proof (IH _ _ (Forall_inv_tail Hfa) Hsome) as [r [s [Hf0 Hf1]]].
          unfold listSplitForAll.
          rewrite Hf0.
          exists (y :: r).
          exists s.
          split. reflexivity.
          rewrite <- app_comm_cons.
          apply Forall_cons.
          apply (Forall_inv Hfa).
          exact Hf1.
        }
      }
    Qed.
  End ForAll.

End ListExes.
