From Coq Require Import Nat.
From Coq Require Import Program.Equality.

Module Stlc.

  (** Use the same reified type for the whole development *)
  Inductive type : Type :=
  | TNum: type
  | TArrow : type -> type -> type.

  Declare Custom Entry stlc_ty.
  Notation "<{{ e }}>" := e (e custom stlc_ty at level 99).
  Notation "( x )" := x (in custom stlc_ty, x at level 99).
  Notation "x" := x (in custom stlc_ty at level 0, x constr at level 0).
  Notation "S -> T" := (TArrow S T) (in custom stlc_ty at level 2, right associativity).
  Notation "'Num'" := TNum (in custom stlc_ty at level 0).

  Fixpoint typeDenote (t : type) : Set :=
    match t with
    | <{{ Num }}> => nat
    | <{{ t1 -> t2 }}> => typeDenote t1 -> typeDenote t2
    end.

  Section vars.
    Variable var : type -> Type.

    Inductive Term: type -> Type :=
    | NUM: nat -> Term <{{ Num }}>
    | APP: forall a b, Term <{{ a -> b }}> -> Term a -> Term b
    | VAR: forall a, var a -> Term a
    | LAM: forall a b, (var a -> Term b) -> Term <{{ a ->  b }}>.
  End vars.

  Arguments VAR [var a].
  Arguments NUM {var}.
  Arguments APP [var a b].
  Arguments LAM [var a b].
  (** Maximally insert types in class *)

  Declare Custom Entry stlc.

  Notation "<{ e }>" := e (e custom stlc at level 99).
  Notation "( x )" := x (in custom stlc, x at level 99).
  Notation "x" := x (in custom stlc at level 0, x constr at level 0).
  Notation "x y" := (APP x y) (in custom stlc at level 2, left associativity).
  Notation "\ x , y" :=
    (LAM (fun x => y)) (in custom stlc at level 90,
                        x constr,
                        y custom stlc at level 80,
                        left associativity).
  Notation "\_ , y" :=
    (LAM (fun _ => y)) (in custom stlc at level 90,
                        y custom stlc at level 80,
                        left associativity).
  Definition NUM_coerce(n: nat): Term typeDenote <{{ Num }}> := NUM n.
  Coercion NUM_coerce: nat >-> Term.
  Notation "# n" := (VAR n) (in custom stlc at level 0).
  Notation "{ x }" := x (in custom stlc at level 1, x constr).

  Fixpoint termDenote {t: type} (e : Term typeDenote t) {struct e} : typeDenote t :=
    match e in (Term _ t) return (typeDenote t) with
    | VAR v => v
    | NUM f => f
    | APP e1 e2 => (termDenote e1) (termDenote e2)
    | LAM e' => fun x => termDenote (e' x)
    end.

  (* Normalization via reify/reflect Danvy et al. *)
  Class Nbe (t: type) := {
    reify: typeDenote t -> Term typeDenote t;
    reflect: Term typeDenote t -> typeDenote t
                        }.
  
  Instance Nbe_lam {a b: type} `{Nbe a} `{Nbe b}: Nbe <{{ a -> b }}> := {
    reify v :=
      LAM (fun x => reify (v (reflect (VAR x))));
    reflect e :=
      fun x => reflect (APP e (reify x))
                                                                      }.
  Instance Nbe_int : Nbe <{{ Num }}> := {
    reify v := NUM v;
    reflect v := termDenote v;
                                       }.

  Fixpoint resolver(t: type): Nbe t :=
    match t with
    | <{{ Num }}> => Nbe_int
    | <{{ a -> b }}> => Nbe_lam
    end.

  Arguments Nbe {t}.
  Arguments Nbe_lam [a b].

  Definition normalize {t: type} (e: Term typeDenote t): Term typeDenote t :=
    @reify t (resolver t) (@reflect t (resolver t) e).

  Compute normalize <{ 1 }>.

  Compute normalize <{ \ x, (\ y, # y) 1 }>.

  Inductive fof: type -> Prop :=
  | fo_num: fof <{{ Num }}>
  | fof_num: forall a,
      fof <{{ a }}> ->
      fof <{{ Num -> a }}>.

  Inductive value: forall {t: type}, Term typeDenote t -> Prop :=
  | Value_var: forall x, @value <{{ Num }}> (@VAR typeDenote <{{ Num }}> x)
  | Value_const: forall (x: nat), @value <{{ Num }}> (NUM x).

  Inductive hnff: forall (t: type), Term typeDenote t -> Prop :=
  | HNF_num_ar: forall a f,
      (forall (arg: typeDenote <{{ Num }}>), hnff <{{ a }}> (f arg)) ->
      hnff <{{ Num -> a }}> (LAM f)
  | HNF_num: forall e,
      value e ->
      hnff <{{ Num }}> e.

  Hint Constructors hnff: core.
  Hint Constructors value: core.
  Hint Constructors fof: core.
  
  Theorem normalize_correct: forall (t: type) (e: Term typeDenote t),
      fof t  ->
      hnff t (normalize e).
  Proof with eauto.
    intros; induction H; dependent destruction e; cbn...
  Defined.

End Stlc.
