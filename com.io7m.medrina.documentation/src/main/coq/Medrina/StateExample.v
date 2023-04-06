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

Require Import Medrina.State.

Import ListNotations.

Module St := State.
Module StI := StateIteration State.

Definition under3 (n : nat) : St.t (list nat) StI.halt :=
  St.bind St.get (fun rs =>
    match (Nat.ltb n 3) with
    | true  => St.bind (St.put (rs ++ [n])) (fun _ => St.ret StI.HContinue)
    | false => St.ret StI.HHalt
    end
  ).

Example under3Example :
  St.evalState [] (StI.iterate [1;2;3;4;5] under3) = [1;2].
Proof.
  compute.
  reflexivity.
Qed.
