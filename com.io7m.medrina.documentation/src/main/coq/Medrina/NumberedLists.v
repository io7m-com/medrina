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

Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.

Inductive numbered (A : Type) := MkN {
  nIndex : nat;
  nItem  : A
}.

Import ListNotations.

Inductive numberedListSorted (A : Type) : list (numbered A) -> Prop :=
  | NL_Empty : 
    numberedListSorted _ []
  | NL_One : forall x,
    numberedListSorted _ [x]
  | NL_Cons : forall x0 x1 xs,
    nIndex A x1 = S (nIndex A x0) ->
      numberedListSorted _ (x1 :: xs) ->
        numberedListSorted A (x0 :: x1 :: xs)
  .

Fixpoint numberList
  {A  : Type}
  (xs : list A)
  (n  : nat)
: list (numbered A) :=
  match xs with
  | []      => []
  | y :: ys => (MkN _ n y) :: (numberList ys (S n))
  end.

Lemma numberListEmpty : forall (A : Type) (xs : list A) (n : nat),
  numberList xs n = [] <-> xs = [].
Proof.
  split. {
    intros Heq.
    destruct xs as [|y ys]. {
      reflexivity.
    } {
      contradict Heq; discriminate.
    }
  } {
    intros Heq.
    destruct xs as [|y ys]. {
      reflexivity.
    } {
      contradict Heq; discriminate.
    }
  }
Qed.

Lemma numberListSortedCons : 
  forall (A  : Type) 
         (xs : list (numbered A))
         (x  : numbered A),
  numberedListSorted _ (x :: xs) ->
    numberedListSorted _ xs.
Proof.
  intros A xs x Hsort.
  inversion Hsort. {
    constructor.
  } {
    intuition.
  }
Qed.

Theorem numberListSorts : forall (A : Type) (xs : list A) (n : nat),
  numberedListSorted _ (numberList xs n).
Proof.
  induction xs as [|y ys IH]. {
    constructor.
  } {
    destruct ys as [|z zs]. {
      constructor.
    } {
      intros m.
      pose proof (IH (S m)) as H1.
      simpl.
      apply NL_Cons.
      reflexivity.
      simpl in H1.
      exact H1.
    }
  }
Qed.

Theorem numberListInv : forall (A : Type) (xs : list A) (n : nat),
  map (nItem A) (numberList xs n) = xs.
Proof.
  induction xs as [|y ys IH]. {
    reflexivity.
  } {
    simpl.
    intros m.
    rewrite (IH (S m)).
    reflexivity.
  }
Qed.
