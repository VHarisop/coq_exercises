(* These exercises come from Lab Session 6 of the MAP Spring School *)
(* on formalization of mathematics. *)

From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition onext_id n (x: 'I_n): 'I_n.
pose v := nat_of_ord x.
pose H := ltn_ord x.
pose H1 := leq_trans H (leqnn n).
exact: Ordinal H1.
Defined.

(* {x | x < 0} is an empty type *)
Lemma empty_i0 (x: 'I_0): false.
Proof.
  case x. by [].
Qed.

(* Toy structure from examples *)
Structure semiGroup := SemiGroup {
  toy_dom : Type;
  binop : toy_dom -> toy_dom -> toy_dom;
  binopA : forall x y z : toy_dom,
    binop x (binop y z) = binop (binop x y) z
}.

(* Canonical semigroup: register a semigroup to be available for type
   inference - see next Lemma *)
Canonical nat_semiGroup : semiGroup := @SemiGroup nat addn addnA.

Lemma semigroup_canonical (x y z : nat) : x + (y + z) = x + y + z.
Proof.
  apply: binopA.
Qed.


(* We define here an interface for types equipped with a binary boolean *)
(* relation and a unary operation monotonic wrt the previous relation*)
(* Specification projections are unnamed to avoid introducing *)
(* projections that do not play a role for the inference of canonical *)
(* instances *)
Structure rel_s := Rel_s {
   dom : Type;
   cmp : rel dom;
   f : dom -> dom;
   _ : transitive cmp;
   _ : forall x, cmp x (f x)
}.

(* Now we prove that the relation associated with an instance of rel_s *)
(* is transitive.*)
Lemma cmp_trans (s : rel_s) : transitive (@cmp s).
Proof.
  by case: s.
Qed.

(* Ex1 - Prove the following lemma *)
Lemma cmp_f (s : rel_s) : forall x : dom s, cmp x (f x).
Proof.
  by case: s.
Qed.

Section thms.

(* We a assume a parameter type and all the material needed in order *)
(* to build an instance of rel_s*)
Variables (T : Type) (cmpT : rel T) (fT : T -> T).

Hypothesis cmp_trans : transitive cmpT.

Hypothesis f_mon : forall x, cmpT x (fT x).

(* Define a canonical instance of rel_s for cmpT and fT *)
(* Warning: the effect of canonical declarations do not survive *)
(* to the end of sections *)
Canonical res_st : rel_s := Rel_s cmp_trans f_mon.

(* This is a notation local to the section thms for the relation *)
(* associated with the instance s *)

End thms.

(* Prove the following theorem *)
Lemma f3 : forall (s : rel_s) (n : dom s), cmp n (f (f (f n))).
Proof.
  move => s n.
  apply (@cmp_trans _ (f (f n))).
    - apply (@cmp_trans _ (f n)); by rewrite cmp_f.
    - by rewrite cmp_f.
Qed.

(* Define a canonical instance of rel_s on type nat equipped with the *)
(* relation leq and the successor operation *)
Canonical res_snat : rel_s := Rel_s leq_trans leqnSn.

(* This result comes for free using the more generic f3 *)
Lemma fnat3 n : n <= n.+3.
Proof.
  apply f3.
Qed.

Section pairs.

(* We assume two parameter types, and two binary boolean relations *)
(* respectively on these types, and two unary functions *)

Variables (T1 T2 : Type)(r1 : rel T1)(r2 : rel T2).
Variables (f1 : T1 -> T1)(f2 : T2 -> T2).

Hypothesis r1_trans : transitive r1.
Hypothesis r2_trans : transitive r2.

Hypothesis f1_mon : forall x, r1 x (f1 x).
Hypothesis f2_mon : forall x, r2 x (f2 x).

Definition pair_rel (u v : T1 * T2) := (r1 u.1 v.1) && (r2 u.2 v.2).

(* Complete the following definition to define a function on pairs *)
(* which associates (x, y) with the pair (f1 x, f2 y) *)
Definition pair_fun (u : T1 * T2) := (*D *) (f1 u.1, f2 u.2).

(* State and prove that pair_rel is transitive *)
Lemma pair_rel_trans : transitive pair_rel.
Proof.
  case => x1 x2 [y1 y2] [z1 z2].
  move => /andP. rewrite /=. move => [Hxy1 Hxy2].
  move => /andP /= [Hxz1 Hxz2].
  (* Unfold pair_rel definition *)
  rewrite/pair_rel. apply /andP. rewrite /=.
  rewrite (r1_trans Hxy1).
    + by rewrite (r2_trans Hxy2).
    + by apply Hxz1.
Qed.

(* State and prove that pair_fun is monotonic wrt pair_rel *)
Lemma pair_fun_mon : forall x, pair_rel x (pair_fun x).
Proof.
  case => x1 x2.
  rewrite /pair_rel /=. apply /andP.
  by rewrite f1_mon f2_mon.
Qed.

End pairs.

Section instances.
(* Write a canonical declaration which builds a new instance of rel_s *)
(* from two existing ones using the lemmas prouved in section Pairs. *)

Definition test_fun := pair_fun S S.
Definition test_comp := pair_rel leq leq.

(* An instance of rel_s which satisfies the Rel_s definition for pairs *)
Canonical rel_s_pair (s1 s2: rel_s) :=
  Rel_s (pair_rel_trans (@cmp_trans s1) (@cmp_trans s2))
  (pair_fun_mon (@cmp_f s1) (@cmp_f s2)).

(* Find the shortest possible proof for this test lemma *)
Lemma test_rels_pair : forall u : nat * nat, test_comp u (test_fun u).
Proof.
  apply cmp_f.
Qed.

(* Now instanciate rel_s for divisibility and doubling on nat and test *)
(* your approach *)

Lemma doubling_mon_dvdn : forall x, dvdn x (x.*2).
Proof.
  move => x.
  apply /dvdnP.
  by exists 2; rewrite mulnC muln2.
Qed.

Canonical rel_s_div : rel_s := Rel_s dvdn_trans doubling_mon_dvdn.

(* Test the benchmark to see if our approach was correct *)
Lemma dvdn_times_8 : forall x, dvdn x (x.*2.*2.*2).
Proof.
  move => x. apply f3.
Qed.

End instances.
