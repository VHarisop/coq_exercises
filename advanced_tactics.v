From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Rework your last proof using the full syntax of ssreflect. *)

(* Solve the following equations. Search is your best friend. *)
Lemma ex5_arit1 n m : n + (m * n + 0) = n * m.+1.
Proof.
  by rewrite addn0 [in RHS]mulnC mulSn.
Qed.

(* Required for ex5_arit2 *)
Lemma muln2_div2 n : n * 2 %/ 2 = n.
Proof.
  rewrite -muln_divA. rewrite divnn //= muln1 //=. rewrite //=.
Qed.

(* Note: %/ is integer division! *)
Lemma ex5_arit2 n m : n %/ 2 + m = (2 * m + n) %/ 2.
Proof.
  rewrite addnC. rewrite mulnC //=.
  rewrite divnDl.
    - by rewrite muln2_div2.
    - by rewrite dvdn_mull.
Qed.

Lemma ex5_arit3 n m p : 0 < p ->  p %| n -> n %/ p + m = (p * m + n) %/ p.
Proof.
  move => p_gt_0 p_divn.
  rewrite addnC.
  rewrite divnDl.
  - (* (p * m) %/ p *)
    rewrite [in RHS]mulnC -muln_divA. rewrite divnn; rewrite p_gt_0 //= muln1 //=.
  - (* p %| p *)
    by rewrite dvdnn.
  - (* p %| p * m *)
    by rewrite dvdn_mulr.
Qed.


(* Prove this by induction. *)
Lemma size_iota_sumn l : sumn (map (addn 1) l) = size l + sumn l.
Proof.
  elim: l => //= x xs IHx.
  rewrite !addSn. rewrite [x + _]addnC IHx. rewrite [in RHS]addnA add0n.
  by rewrite [x + _]addnC.
Qed.

Lemma addnn_subn m n: m + n - n = m.
Proof.
  rewrite -[n in (_ - n)]add0n.
  by rewrite subnDr subn0.
Qed.

(* Prove the following Theorem by induction. *)
Theorem ex5_gauss n : (n * n.-1) %/ 2 = sumn (iota 0 n).
Proof.
  elim: n => //= n IHn; rewrite (iota_addl 1 0).
  rewrite size_iota_sumn add0n.
  rewrite size_iota.
  rewrite -IHn{IHn} mulSn -divnMDl //= -subn1 mulnBr addnBA.
  rewrite [in RHS]addnC.
  rewrite [in RHS] muln2 -addnn muln1.
  rewrite addnA.
  - by rewrite addnn_subn addnC.
    (* Leftover case by application of addnBA *)
  - case: n => //= n.
    set q := n.+1.
    by rewrite muln1 leq_pmull.
Qed.

(* Advanced exercise. *)
Lemma ex5_dvdn : forall m n k, k > 0 -> (m ^ k %| n ^ k) -> (m %| n).
Proof.
  move => m n k k_pos dv_mn_k.
  (* Without loss of generality n is positive, since any number divides 0 *)
  wlog n_gt0 : / (n > 0).
    - case: n {dv_mn_k}.
      + by [].
      + move => n0. rewrite ltn0Sn //=. move => m_div_n0S. by apply m_div_n0S.
  (* Given d := gcdn m n, n can be written as n' * d and m as m' * d *)
  set d := gcdn m n.
  (* IMPORTANT: Use 'have' to assert the existence of n', s.t.
     n = n' * (gcdn m n) *)
  have /dvdnP[n' def_n]: (d %| n).
  - by apply: dvdn_gcdr.
  have /dvdnP[m' def_m]: (d %| m).
  - by apply: dvdn_gcdl.
  (* We also have d > 0 *)
  have : d > 0.
  - by rewrite /d gcdn_gt0 n_gt0 orb_idl.
  (* We can now refine our assumption to m' ^ k %| n' ^ k
   since for b positive, a * b %| c * b -> a %| c     *)
  move => d_gt0.
  have {dv_mn_k} dv_mn_k: m' ^ k %| n' ^ k.
  - move: dv_mn_k. rewrite !def_m !def_n. rewrite !expnMn.
    rewrite dvdn_pmul2r.
      + by [].
      + rewrite expn_gt0 d_gt0 //.
  (* We can also prove that (m' ^ k) and (n' ^ k) are coprime since
     the gcdn of m' and n' is 1, or equivalently (gcdn m' n') * d = d *)
  have cop_mnk: coprime (m' ^ k) (n' ^ k).
    + rewrite coprime_expl //.
    + rewrite coprime_expr //.
    + rewrite /coprime.
    + have: (gcdn m' n') * d == d.
      - rewrite muln_gcdl. rewrite -def_n -def_m. by rewrite /d.
    + rewrite -eqn_div // divnn d_gt0 //=.
  (* From this coprimality and the refined hypothesis follows that
     m' ^ k = 1 = gcdn (m' ^ k) (n' ^ k). Hint: gcdn a (a %% b) = gcdn a b *)
  have : m' ^ k == 1.
    + rewrite -(eqP cop_mnk). by rewrite -gcdn_modr (eqP dv_mn_k) gcdn0.
    + rewrite -(exp1n k) eqn_exp2r. move => /eqP m_eq_1.
      rewrite def_m m_eq_1 mul1n def_n.
      by rewrite dvdn_mull.
      apply k_pos.
Qed.
