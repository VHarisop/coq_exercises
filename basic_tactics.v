From mathcomp Require Import all_ssreflect.

(* Magic settings *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section simpleEx.
(* Some variables *)
Variables P Q R S : Prop.

(* Identity *)
Lemma id_P: P -> P.
Proof.
  move => p; apply p.
Qed.

(* Almost identity *)
Lemma id_PP: (P -> P) -> P -> P.
Proof.
  move => pp; apply pp.
Qed.

(* Transitive identity *)
Lemma imp_trans : (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  move => pq qr p.
  by apply qr; apply pq.
Qed.

Lemma imp_perm : (P -> Q -> R) -> Q -> P -> R.
Proof.
  move => pqr q p.
  apply pqr.
    - by apply p.
    - by apply q.
Qed.

Lemma ignore_Q : (P -> R) -> P -> Q -> R.
Proof.
  move => pr p _.
  apply pr; apply p.
Qed.

Lemma delta_imp : (P -> P -> Q) -> P -> Q.
Proof.
  move => ppq pq.
  apply ppq; apply pq.
Qed.

Lemma delta_impR : (P -> Q) -> P -> P -> Q.
Proof.
  move => pq _; apply pq.
Qed.

Lemma diamond : (P -> Q) -> (P -> R) -> (Q -> R -> S) -> P -> S.
Proof.
  move => pq pr qrs p.
  apply: qrs.
    - apply pq; apply p.
    - apply pr; apply p.
Qed.

Lemma weak_peirce : ((((P -> Q) -> P) -> P) -> Q) -> Q.
Proof.
  move => pqpp.
  apply pqpp.
  move => pqp.
  apply pqp.
  move => p.
  apply pqpp.
  (* I already have the next premise. *)
  move => _; apply p.
Qed.

End simpleEx.

Section haveEx.

(* Hypotheses for Lemma Q0 *)
Variables P Q R T : Prop.
Hypothesis H : P -> Q.
Hypothesis H0 : Q -> R.
Hypothesis H1 : (P -> R) -> T -> Q.
Hypothesis H2 : (P -> R) -> T.

Lemma Q0 : Q.
Proof.
  have p_to_r: P -> R.
     move => p; apply H0; apply H; apply p.
  apply H1.
    - apply p_to_r.
    - apply H2; apply p_to_r.
Qed.

End haveEx.
