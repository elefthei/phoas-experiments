From Coq Require Import Nat.
From Coq Require Import Program.Equality.

Set Maximal Implicit Insertion.

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
    | ADD: Term <{{ Num }}> -> Term <{{ Num }}> -> Term <{{ Num }}>
    | APP: forall a b, Term <{{ a -> b }}> -> Term a -> Term b
    | RET: forall a, var a -> Term a
    | LAM: forall a b, (var a -> Term b) -> Term <{{ a ->  b }}>.
  End vars.

  Arguments RET {var a}.
  Arguments NUM {var}.
  Arguments ADD {var}.
  Arguments APP {var a b}.
  Arguments LAM {var a b}.

  (* Syntax *)
  Declare Custom Entry stlc.
  Notation "<{ e }>" := e (e custom stlc at level 99).
  Notation "( x )" := x (in custom stlc, x at level 99).
  Notation "x" := x (in custom stlc at level 0, x constr at level 0).
  Notation "x y" := (APP x y) (in custom stlc at level 2, left associativity).
  Notation "x + y" := (ADD x y) (in custom stlc at level 2, left associativity).
  Notation "\ x , y" :=
    (LAM (fun x => y)) (in custom stlc at level 90,
                        x constr,
                        y custom stlc at level 80,
                        left associativity).
  Notation "\_ , y" :=
    (LAM (fun _ => y)) (in custom stlc at level 90,
                        y custom stlc at level 80,
                        left associativity).

  Notation "# n" := (NUM n) (in custom stlc at level 0).
  Notation "@ n" := (RET n) (in custom stlc at level 0, n custom stlc at level 1).
  Notation "{ x }" := x (in custom stlc at level 1, x constr).

  (* Normalization via reify/reflect Danvy et al. and denotation for metaprogramming *)
  Class Nbe (v: type->Type) (t: type) := {
      reify: v t -> Term v t;
      reflect: Term v t -> v t;
      normalize: Term v t -> Term v t := fun x => reify (reflect x);
    }.
  
  Fixpoint termDenote {t: type} (e : Term typeDenote t) : typeDenote t :=
    match e in (Term _ t) return (typeDenote t) with
    | RET v => v
    | ADD l r => (termDenote l) + (termDenote r)                                   
    | NUM f => f
    | APP e1 e2 => (termDenote e1) (termDenote e2)
    | LAM e' => fun x => termDenote (e' x)
    end.
  
  Fixpoint termFlatten {t: type} {v: type -> Type} (e: Term (Term v) t): Term v t :=
    match e with
    | RET v => v
    | NUM f => NUM f
    | ADD l r => ADD (termFlatten l) (termFlatten r)
    | APP e1 e2 => APP (termFlatten e1) (termFlatten e2)
    | LAM e' => LAM (fun x => termFlatten (e' (RET x)))
    end.

  (** Demo *)
  Fixpoint add1 {t: type} {v: type -> Type} (e: Term v t): Term v t :=
    match e with
    | NUM f => NUM (f+1)
    | APP e1 e2 => APP (add1 e1) (add1 e2)
    | ADD e1 e2 => ADD (add1 e1) (add1 e2)
    | LAM e' => LAM (fun x => add1 (e' x))
    | RET v => RET v
    end.

  (** Two orthogonal structural recursions via instances.
      1. On v: type -> Type (metaprogramming induction)
      2. On t: type (induction on type)
   *)
  Instance Nbe_lam a b `{Nbe typeDenote a} `{Nbe typeDenote b}: Nbe typeDenote <{{ a -> b }}> := {
      reify v := LAM (fun x => reify (v (reflect (RET x))));
      reflect e := fun x => reflect (APP e (reify x))
    }.
  
  Instance Nbe_num : Nbe typeDenote <{{ Num }}> := {
    reify v := NUM v;
    reflect v := termDenote v;
                                       }.

  Instance NStep_lam v a b `{Nbe v <{{ a -> b }}>}: Nbe (Term v) <{{ a -> b }}> := {
      reify v := RET v; 
      reflect e := termFlatten e
    }.
  
  Instance NStep_num v `{Nbe v <{{ Num }}>}: Nbe (Term v) <{{ Num }}> := {
      reify v := RET v;
      reflect e := termFlatten e
    }.
  
  Tactic Notation "meta" uconstr(x) := refine x; exact typeDenote.
  
  Definition l3 :=
    ltac:(meta <{ \x, @x + #1 + (@ (#3 + (@( #1)))) }>).
  Check l3.

  Compute add1 l3.          (* = <{ \ x, @ x + #2 + @ (#3) + @ (#1) }> *)
  Compute reflect (add1 l3). (* = <{ \ x, @ x + #2 + (#3 + @ (#1)) }> *)
  Eval cbv in reify (reify (normalize (add1 (reflect (reflect l3))))).
                            (* = <{ \ x, @ x + #3 + #4 + #1 }> *)
  Compute reflect (reflect (add1 (reflect (add1 l3)))).
                            (* = <{ \x, 5 }> *)
  Compute reflect (reflect (add1 l3)).
  Compute reflect (reflect (reflect (add1 l3))).

  Definition l4 :=
    ltac:(meta <{ \x, @x + #1 + (@ (#3 + (#1))) }>).

   
  Compute l4.
  Compute normalize l4.
  Goal True.
    pose proof l4.
    pose proof @lift <{{ Num -> Num }}> (Term typeDenote).
    pose proof (lift (@normalize' (Term typeDenote) (<{{ Num -> Num }}>)
                            (NStep_lam' typeDenote <{{ Num }}> <{{ Num }}>))).
    pose proof (lift normalize' l4).

  Arguments Nbe {t}.
  Arguments Nbe_lam [a b].

  Definition normalize {t: type} (e: Term typeDenote t): Term typeDenote t :=
    @reify t (resolver t) (@reflect t (resolver t) e).

  Compute normalize <{ ((\x, @x + #1) #2) + #1 }>.
  
  Inductive fof: type -> Prop :=
  | fo_num: fof <{{ Num }}>
  | fof_num: forall a,
      fof <{{ a }}> ->
      fof <{{ Num -> a }}>.

  Hint Constructors fof: core.

  Inductive value: forall {t: type}, Term typeDenote t -> Prop :=
  | Value_var: forall x, @value <{{ Num }}> (@RET typeDenote <{{ Num }}> x)
  | Value_const: forall (x: nat), @value <{{ Num }}> (NUM x).

  Hint Constructors value: core.
  
  Inductive hnff: forall (t: type), Term typeDenote t -> Prop :=
  | HNF_num_ar: forall a f,
      (forall (arg: typeDenote <{{ Num }}>), hnff <{{ a }}> (f arg)) ->
      hnff <{{ Num -> a }}> (LAM f)
  | HNF_num: forall e,
      value e ->
      hnff <{{ Num }}> e.
  
  Hint Constructors hnff: core.
  
  Theorem normalize_correct: forall (t: type) (e: Term typeDenote t),
      fof t  ->
      hnff t (normalize e).
  Proof with eauto.
    induction t; intros e H; dependent destruction e; inversion H; subst; cbn...
  Defined.

End Stlc.
