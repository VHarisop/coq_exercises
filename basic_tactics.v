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

(* Prove that the reverse has at least two if and only if
   the original has at leas two *)
Lemma rev_least (T: Type) (l: seq T):
  at_least_two l = at_least_two (rev l).
Proof.
  have at_least_two_rcons (A: Type) a b (ql: seq A) :
    at_least_two (rcons (rcons ql a) b).
    move: ql; case => // a1. case; rewrite //=.
  case: l => [// | h1 l] //=.
  case: l => [// | h2 l] //=.
    rewrite !rev_cons.
    by rewrite at_least_two_rcons.
Qed.

End sequences.


(* Section playing around with applying and proving views *)
Section views.

Goal forall (P Q : Prop), (P <-> Q) -> P -> Q.
Proof.
  move => P Q p_equiv_q.
  by move/iffLR: p_equiv_q => p_equiv_q.
Qed.

Goal forall (P : nat -> Prop) (Q : Prop),
     (P 0 -> Q)
  -> (forall n, P n.+1 -> P n)
  -> P 4 -> Q.
Proof.
  move => P Q.
  move => p0q pSn_impl_n p4.
  move/pSn_impl_n: p4 => p3.
  move/pSn_impl_n: p3 => p2.
  move/pSn_impl_n: p2 => p1.
  move/pSn_impl_n: p1 => p0; apply p0q; apply p0.
Qed.

(* Using case/orP with b1 || b2 as hypothesis in goal *)
Goal forall (b b1 b2 : bool), (b1 -> b) -> (b2 -> b) -> b1 || b2 -> b.
Proof. (* No case analysis on b, b1, b2 allowed *)
  move => b b1 b2.
  move => b1_b b2_b.
  (* Goal left: b1 || b2 -> b.
     Using case/orP reduces to two trivial goals:
       - b1 -> b
       - b2 -> b *)
  by case/orP.
Qed.

(* Using specialization in move: move => /(_ x). *)
Goal forall (Q : nat -> Prop) (p1 p2 : nat -> bool) x,
  ((forall y, Q y -> p1 y /\ p2 y) /\ Q x) -> p1 x && p2 x.
Proof.
  move => Q p1 p2 x H.
  case: H.
    (* Specialize [Qy -> p1 y /\ py 2] by putting x as y *)
    move => /(_ x).
    move => QH Qx.
    apply /andP; apply QH; apply Qx.
Qed.

(* Same goal with above, using orP. *)
Goal forall (Q : nat -> Prop) (p1 p2 : nat -> bool) x,
  ((forall y, Q y -> p1 y \/ p2 y) /\ Q x) -> p1 x || p2 x.
Proof.
  move => Q p1 p2 x H.
  case: H.
    move => /(_ x).
    move => QH Qx.
    apply/orP.
    apply QH; apply Qx.
Qed.

End views.

Section no_xxxP_lemmas.

(* Prove identity without other xxxP lemmas *)
Lemma myidP: forall (b : bool), reflect b b.
Proof.
  move => b.
  case: b.
  (* ReflectT: P -> reflect P true
     ReflectF: ~P -> reflect P false *)
    - by apply ReflectT.
    - by apply ReflectF.
Qed.

(* Symmetric with idP *)
Lemma mynegP: forall (b : bool), reflect (~ b) (~~ b).
Proof.
  move => b //=.
  case: b.
    - by apply ReflectF.
    - by apply ReflectT.
Qed.

Lemma myandP: forall (b1 b2 : bool), reflect (b1 /\ b2) (b1 && b2).
Proof.
  move => b1 b2.
  case: b1; rewrite //=.
    case b2; rewrite //=.
    (* reflect (true /\ true) true *)
    - by apply ReflectT.
    (* reflect (true /\ false) false *)
    - apply ReflectF. by move => h; case: h.
    (* reflect (false /\ b2) false *)
    - apply ReflectF. by move => h; case: h.
Qed.

(* Logical equivalence stated by booleans *)
Lemma myiffP:
  forall (P Q : Prop) (b : bool),
    reflect P b -> (P -> Q) -> (Q -> P) -> reflect Q b. 
Proof.
  move => P Q b.
  move => Pb PQ QP.
  move: Pb.
    - case: b.
      (* Following parts are tricky! *)
      * move => h. case: h. move/PQ => h. apply/ReflectT; apply h.
      * move => h. apply/ReflectF. move/QP => p. apply h; apply p.
      * move => h. case: h.
        - move/PQ => p. apply ReflectT; apply p.
        - move => NP. apply/ReflectF. move/QP => p. apply NP. apply p.
Qed.

End no_xxxP_lemmas.

Section nats.

Lemma snat_ind : forall (P : nat -> Prop),
  (forall x, (forall y, y < x -> P y) -> P x)
  -> forall x, P x.
Proof.
  (* Hint: strengthen P x into (forall y, y <= x -> P x) and then
   *       perform the induction on x. *)
  move => P Px x.
  (* The following line works as explained here:
     - the ":" tactic works left to right, so at first,
       (leqnn x) is added to the goal stack
     - the second move generalizes the first occurence of "x" in
       (leqnn x) to another nat, x0. *)
  move: {-2}x (leqnn x).
  elim: x.
    - move => x. rewrite leqn0. move/eqP => x_eq_0.
      rewrite x_eq_0. by apply: Px.
    - move => n IHn x. rewrite leq_eqVlt => /orP.
      case.
        + move => x_eq_sn. rewrite (eqP x_eq_sn). apply Px.
          move => y. apply IHn.
        + move => x_lt_sn. apply IHn. apply x_lt_sn.
Qed.

(* Variation of induction on naturals *)
Lemma tut_odd_ind : forall (P : nat -> Prop),
  P 0 -> P 1 -> (forall x, P x  -> P x.+2)
  -> forall x, P x.
Proof.
  move => P P0 P1 Pind.
  elim/snat_ind.
  - move => x. case: x => //= x.
  - case: x.
    + move => _; apply P1.
    + move => x Hind. by apply Pind; apply Hind.
Qed.


(* Variation of strong induction on naturals *)
Lemma tut_nat_ind2: forall (P : nat -> Prop),
  P 0 -> P 1 -> (forall p, P p -> P p.+1 -> P p.+2)
  -> forall n, P n.
Proof.
  move => P P0 P1 ind.
  elim/snat_ind.
  - move => x. case: x => //= x.
  - case: x.
    + move => _; apply P1.
    + move => x HInd. by apply ind; apply HInd.
Qed.

End nats.

End nats.
