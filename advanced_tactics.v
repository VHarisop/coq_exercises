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