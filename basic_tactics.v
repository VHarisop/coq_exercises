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

(* Boolean propositions, mostly proofs by elimination
   over cases. *)

Section bool_prop.

Check (forall (a b : bool), a -> b).
Notation "x 'is_true'" := (is_true x) (at level 8).
Check (forall (a b : bool), a is_true ->  b is_true).

Lemma Andb_idl (a b : bool) : (b is_true -> a is_true ) -> a && b = b.
Proof.
  case: a; case: b; rewrite //=.
  by move => H; apply H.
Qed.

Lemma Andb_idr (a b :bool) : (a is_true-> b is_true) -> a && b = a.
Proof.
  case: a; case: b; rewrite //=.
  by move => H; apply H.
Qed.

(* Note that this is symmetric with Andb_idl -> use andbC *)
Lemma Andb_idr_smart (a b : bool) : (a is_true -> b is_true) -> a && b = a.
Proof.
  move => a_to_b.
  rewrite andbC.
  apply Andb_idl; apply a_to_b.
Qed.

Lemma Andb_id2l (a b c : bool) : (a -> b = c) -> a && b = a && c.
Proof.
  case: a; case: b; rewrite !//=.
  by move => ppt; apply ppt.
  by move => ppf; apply ppf.
Qed.

Lemma andbA : forall x y z, andb x (andb y z) = andb (andb x y) z.
Proof.
  move => x y z.
  rewrite /andb.
  case: x; rewrite //=.
Qed.

(* Prove that logical AND of an OR splits. *)
Lemma andb_orr :
  forall x y z, andb x (orb y z) = orb (andb x y) (andb x z).
Proof.
  move => x y z.
  rewrite /andb.
  case: x; rewrite //=.
Qed.

(* a -> b == (~a) OR b *)
Lemma impbE : forall x y, implb x y = orb (negb x) y.
Proof.
  move => x y.
  by case: x.
Qed.

Lemma xorbE : forall x y, xorb x y = andb (orb x y) (negb (andb x y)).
Proof.
  move => x y.
  by case: x.
Qed.

End bool_prop.

(* Definitions and lemmas about sequences *)
Section sequences.

Definition at_least_two (T: Type) (x : seq T) :=
	if x is h :: t :: _ then true else false.

Definition exactly_two (T: Type) (x : seq T) :=
	if x is h :: t :: [ :: ] then true else false.

(* == 2 -> >= 2 *)
Lemma two_is_enough (T: Type) (x: seq T): exactly_two x -> at_least_two x.
Proof.
  case: x => [// | a Rest].
  by case: Rest => [// | b RRest].
Qed.

(* If one of two lists has at least 2 elements, their concatenation
   will also have at least two elements *)
Lemma concat_has_more (T: Type) (x: seq T) (y: seq T):
  (at_least_two x || at_least_two y) -> at_least_two (x ++ y).
Proof.
  (* Prove the left side *)
  have concat_l_has_more (z w : seq T): at_least_two z -> at_least_two (z ++ w).
    (* Cases on x *)
    rewrite {1}/at_least_two.
    by case: z => [// | _T L]; case: L.
  (* Prove the right side *)
  have concat_r_has_more (z w : seq T): at_least_two w -> at_least_two (z ++ w).
    move : z. case.
      - by [].
      - move => a; case; rewrite //=.
      - move : w; case; rewrite //=.
  (* Use left and right cases to prove the whole thing. *)
  case/orP.
    - apply concat_l_has_more.
    - apply concat_r_has_more.
Qed.

End sequences.
