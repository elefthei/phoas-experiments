(** Thierry Coquand - the computational content of classical logic *)
From Coq Require Import Program.Equality.
From Coq Require Import Unicode.Utf8.
From Coq Require Import Arith.

Set Implicit Arguments.

Inductive M(F: Type -> Type): Type -> Type :=
| K: forall t: Type, F t -> M F t
| ret: forall t: Type, t -> M F t
| bind: forall a b, M F a -> (a -> M F b) -> M F b.


Section CoquandCompContext.
  Hypothesis f: nat -> nat.
  Context (x0: nat).
  Hypothesis H1: forall x, exists y, x < f y.
  Hypothesis H2: f 0 <= x0.

  Definition P := exists n, f n <= x0 /\ x0 < f (S n).
  Definition F: Type -> Type := fun _ => P.


  Definition Δ := M F.
  
  Lemma lem1: forall n X, f n <= x0 -> x0 < f (S n) -> Δ X.
  Proof.
    intros.
    apply K.
    unfold F, P.
    exists n. split; auto.
  Defined.

  Lemma lem: forall n, Δ (f n <= x0).
  Proof.
    induction n.
    - apply ret. apply H2.
    - eapply bind. eapply IHn.
      intro H.
      destruct (le_gt_dec (f (S n)) x0).
      + apply ret. apply l.
      + eapply lem1. apply H.
        apply g.
  Defined.
  
  Lemma lem2': forall X, Δ X -> P + X.
  Proof.
    intros.
    induction X0.
    - unfold F in *. left. apply f0.
    - right. apply t0.
    - destruct IHX0.
      + left. apply p.
      + apply X. apply a0.
  Defined.

  Lemma lem2: forall X, ~ X -> Δ X -> P.
  Proof.
    intros.
    apply lem2' in X0.
    destruct X0.
    + apply p.
    + contradiction.
  Defined.

  Lemma final: P.
  Proof.
    destruct (H1 x0).
    rename x into y0.      
    eapply (@lem2 (f y0 <= x0)).
    - intros Hcontra.
      apply (le_not_lt (f y0) x0).
      apply Hcontra.
      apply H.
    - apply lem.
  Defined.
End CoquandCompContext.
