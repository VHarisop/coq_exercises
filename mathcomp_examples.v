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


(* 3-way split based on order of numbers *)
Inductive tut_compare_nat (m n: nat) : bool -> bool -> bool -> Set :=
    Ltn : m < n -> tut_compare_nat m n true false false
  | Gtn : n < m -> tut_compare_nat m n false true false
  | Eql : m == n -> tut_compare_nat m n false false true.


(* Proof for totality of naturals. *)
Lemma tuto_ltngtP: forall m n, tut_compare_nat m n (m < n) (n < m) (m == n).
Proof.
  (* Equal is inequality on both sides *)
  have eq_total m n: (m == n) = (m <= n) && (n <= m).
    - by rewrite eqn_leq.
  (* Less than implies not-greater-equal *)
  have neqlt m n: ~~ (n < m) = (m <= n).
    - by rewrite ltnNge negbK.
  (* Main Proof *)
  move => m n.
  (* use case hyp_name: (hypothesis) to explicitly refer to hypothesis later. *)
  case m_lt_n : (m < n).
    (* simplify (m < n) = true to (m < n) *)
    - move: {m_lt_n} (idP m_lt_n) => mlt_n.
      rewrite [m == n]ltn_eqF. rewrite ltnNge ltnW /=; last first. exact mlt_n.
      by constructor. exact mlt_n.
    case n_lt_m: (n < m).
      - move: {m_lt_n n_lt_m} (idP n_lt_m) => nlt_m.
        rewrite tut_eqb. rewrite [n == m]ltn_eqF //=. by constructor.
    move: {n_lt_m m_lt_n} (negbT n_lt_m) (negbT m_lt_n) => H1 H2.
    case m_eq_n: (m == n).
      - move: {m_eq_n} (idP m_eq_n) => m_eq_n.
        by constructor.
      - (* This case is proven by absurdity *)
        move: H1 H2 m_eq_n.
        rewrite !neqlt => h1 h2.
        move/negbT.
        rewrite eq_total.
        rewrite h1 h2 //.
Qed.
