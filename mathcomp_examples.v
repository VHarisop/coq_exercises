(* Set of examples using the Mathematical Components library. *)
From mathcomp Require Import all_ssreflect.

(* Definition of a toy function *)
Fixpoint f n := if n is n'.+1 then (f n').+2 else 0.

Lemma tut_foo: forall n, f (2 * n) = f (n) + f (n).
Proof.
  elim => [| n IHn].
  - (* f ( 2 * 0 ) = f 0 + f 0 *)
    by rewrite muln0 //=.
  - (* f ( 2 * (n.+1) ) = f n.+1 + f n.+1 *)
    (* !addnS !addSn -> (f n + f n).+4 *)
    rewrite !addnS !addSn.
    (* mulnS => 2 * (n + 1) -> 2 + 2 n
       IHn => f n + f n -> f (2 * n) *)
    rewrite mulnS -IHn //=.
Qed.

(* Every natural number is >= 0, therefore the lemma below
   follows naturally. *)
Lemma tut_aandb_gt_a: forall a b, b <= a + b.
Proof.
  move => a b.
  elim b => [// | bb Ibb].
    - rewrite addnS.
      rewrite ltnS.
      by rewrite Ibb.
Qed.

(* Lemma about multiplication by a natural number. *)
Lemma tut_leq_mul: forall n1 n2 n, n1 <= n2 -> n1 * n <= n2 * n.
Proof.
  move => n1 n2 n.
  elim: n => [// | n IHn n1_leq_n2].
    - by rewrite !muln0.
    - rewrite !mulnS leq_add //=.
      apply IHn; apply n1_leq_n2.
Qed.
