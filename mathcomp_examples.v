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

(* Trivial lemma about exponentiation. *)
Lemma tut_expn_leq: forall a b n, a ^ n <= (a + b) ^ n.
Proof.
  (* Sublemma in case a is positive *)
  have expn_leq: forall a b n, a > 0 -> a ^ n <= (a + b) ^ n.
    move => a b n a_gt_0.
    elim: n => [// | n IHn].
    rewrite !expnS mulnDl.
    rewrite (leq_trans (_ : _ <= (a * (a + b) ^ n))) //=.
    - rewrite leq_pmul2l.
        + apply: IHn.
        + apply: a_gt_0.
    - rewrite leq_addr //=.
  move => a b n.
  elim: a => [//= | a IHa].
    - rewrite add0n.
      elim: n => [// | n IHn].
        + rewrite exp0n.
          rewrite expnS leq0n //=.
        + by [].
        + by rewrite expn_leq.
Qed.

(* Toy Lemma about sum of terms. *)
Lemma tut_sum_2_power_4: forall a b, a ^ 4 + b ^ 4 <= (a + b)^4.
Proof.
  have lemma_1: forall a b n, a * a ^ n <= a * (a + b) ^ n.
    move => a b n.
    rewrite leq_mul2l.
    elim: a => [// | a IHa].
    by simpl; rewrite tut_expn_leq.
  have expn_convex: forall a b n, a^(n.+1) + b^(n.+1) <= (a + b)^(n.+1).
    move => a b n.
    (* expnS: a^{n+1} -> a * a ^ n
       mulnDl: 'break' (a + b) * something
       leq_add: use lemma_1 for both a and b *)
      rewrite !expnS. rewrite mulnDl. rewrite leq_add //=.
      rewrite addnC //=.
  (* Use expn_convex to prove trivial goal. *)
  move => a b.
  apply expn_convex.
Qed.


(* -------------------------------
   Examples using reflection views
   ------------------------------- *)

(* Use this lemma to prove next, to show a usage scenario
   of the 'case' tactic. *)
Lemma tut_leq_total m n: (m <= n) || (n <= m).
Proof.
  rewrite -implyNb -ltnNge.
  apply /implyP.
  apply ltnW.
Qed.

(* Show that when m is less than max(n1, n2), it must be smaller than
   at least one of n1, n2. *)
Lemma tut_leq_max m n1 n2 : m <= (maxn n1 n2) = (m <= n1) || (m <= n2).
Proof.
  (* Below line is equivalent to:
     - case: (leq_total n1 n2)
       move => /orP [leq_n12 | leq_n21].
     leq_total n1 n2 results in a || hypothesis that can be
     changed to a \/ using the orP view, applied by /orP. The
     \/ hypothesis is then able to be split using => [ha | hb]. *)
  case/orP: (leq_total n1 n2) => [leq_n12 | leq_n21].
      (* maxn_idPr: reflect (maxn m n = n) (m <= n).
         Here, we provide the second premise as leq_n12 (n1 <= n2) *)
    - rewrite (maxn_idPr leq_n12).
      rewrite orb_idl // => le_mn1.
      rewrite (leq_trans (_ : _ <= n1)) //.
    - rewrite (maxn_idPl leq_n21).
      rewrite orb_idr // => le_mn2.
      rewrite (leq_trans (_ : _ <= n2)) //.
Qed.
