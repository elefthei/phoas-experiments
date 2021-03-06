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

  (* begin typeDenote *)
  Fixpoint typeDenote (t : type) : Set :=
    match t with
    | <{{ Num }}> => nat
    | <{{ t1 -> t2 }}> => typeDenote t1 -> typeDenote t2
    end.
  (* end typeDenote *)
  
  (* begin syntax *)
  Section vars.
    Variable var : type -> Type.

    Inductive Term: type -> Type :=
    | NUM: nat -> Term <{{ Num }}>
    | ADD: Term <{{ Num }}> -> Term <{{ Num }}> -> Term <{{ Num }}>
    | APP: forall a b, Term <{{ a -> b }}> -> Term a -> Term b
    | RET: forall a, var a -> Term a
    | LAM: forall a b, (var a -> Term b) -> Term <{{ a ->  b }}>.
  End vars.
  (* end syntax *)
  
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

  Class Denotation (v: type -> Type) := {
      denote{t}(e: Term v t): v t;
                                      }.

  (* begin termDenote *)
  Fixpoint termDenote {t: type} (e : Term typeDenote t) : typeDenote t :=
    match e in (Term _ t) return (typeDenote t) with
    | RET v => v
    | ADD l r => (termDenote l) + (termDenote r)                                   
    | NUM f => f
    | APP e1 e2 => (termDenote e1) (termDenote e2)
    | LAM e' => fun x => termDenote (e' x)
    end.
  (* end termDenote *)
  
  Fixpoint termFlatten {t: type} {v: type -> Type} (e: Term (Term v) t): Term v t :=
    match e with
    | RET v => v
    | NUM f => NUM f
    | ADD l r => ADD (termFlatten l) (termFlatten r)
    | APP e1 e2 => APP (termFlatten e1) (termFlatten e2)
    | LAM e' => LAM (fun x => termFlatten (e' (RET x)))
    end.

  Instance baseDenotation: Denotation typeDenote := {
      denote t e := termDenote e
    }.
  
  Instance stepDenotation v `{Denotation v}: Denotation (Term v) := {
      denote t e := termFlatten e
    }.


  (** Demo *)
  Fixpoint add1 {t: type} {v: type -> Type} (e: Term v t): Term v t :=
    match e with
    | NUM f => NUM (f+1)
    | APP e1 e2 => APP (add1 e1) (add1 e2)
    | ADD e1 e2 => ADD (add1 e1) (add1 e2)
    | LAM e' => LAM (fun x => add1 (e' x))
    | RET v => RET v
    end.
  
  Tactic Notation "meta" uconstr(x) := refine x; exact typeDenote.
  
  Definition l3 :=
    ltac:(meta <{ \x, @x + #1 + (@ (#3 + (@( #1)))) }>).

  Check l3.

  Compute add1 l3.          (* = <{ \ x, @ x + #2 + @ (#3) + @ (#1) }> *)
  Compute denote (add1 l3). (* = <{ \ x, @ x + #2 + (#3 + @ (#1)) }> *)
  Compute denote (add1 (denote (add1 l3))).
                            (* = <{ \ x, @ x + #3 + #4 + #1 }> *)
  Compute denote (denote (add1 (denote (add1 l3)))).
                            (* = <{ \x, 5 }> *)
  Compute denote (denote (add1 l3)).
  Compute denote (denote (denote (add1 l3))).

  (* Normalization via reify/reflect Danvy et al. *)
  (* begin nbe *)
  Class Nbe (t: type) := {
    reify: typeDenote t -> Term typeDenote t;
    reflect: Term typeDenote t -> typeDenote t
    }.
  
  Instance Nbe_lam {a b: type} `{Nbe a} `{Nbe b}: Nbe <{{ a -> b }}> := {
    reify v :=
      LAM (fun x => reify (v (reflect (RET x))));
    reflect e :=
      fun x => reflect (APP e (reify x))
    }.
  
  Instance Nbe_int : Nbe <{{ Num }}> := {
    reify v := NUM v;
    reflect v := termDenote v;
    }.
  (* end nbe *)
  
  Fixpoint resolver(t: type): Nbe t :=
    match t with
    | <{{ Num }}> => Nbe_int
    | <{{ a -> b }}> => Nbe_lam
    end.

  Arguments Nbe {t}.
  Arguments Nbe_lam [a b].

  Definition normalize {t: type} (e: Term typeDenote t): Term typeDenote t :=
    @reify t (resolver t) (@reflect t (resolver t) e).

  Compute normalize <{ ((\x, @x + #1) #2) + #1 }>.

  (* begin fof *)
  Inductive fof: type -> Prop :=
  | fo_num: fof <{{ Num }}>
  | fof_num: forall a,
      fof <{{ a }}> ->
      fof <{{ Num -> a }}>.

  Hint Constructors fof: core.
  (* end fof *)
  
  Inductive value: forall {t: type}, Term typeDenote t -> Prop :=
  | Value_var: forall x, @value <{{ Num }}> (@RET typeDenote <{{ Num }}> x)
  | Value_const: forall (x: nat), @value <{{ Num }}> (NUM x).

  Hint Constructors value: core.

  (* begin hnff *)
  Inductive hnff: forall (t: type), Term typeDenote t -> Prop :=
  | HNF_num_ar: forall a f,
      (forall (arg: typeDenote <{{ Num }}>), hnff <{{ a }}> (f arg)) ->
      hnff <{{ Num -> a }}> (LAM f)
  | HNF_num: forall e,
      value e ->
      hnff <{{ Num }}> e.
  
  Hint Constructors hnff: core.
  (* end hnff *)

  (* begin correct *)
  Theorem normalize_correct: forall (t: type) (e: Term typeDenote t),
      fof t  ->
      hnff t (normalize e).
  Proof with eauto.
    induction t; dependent destruction e; inversion 1; subst; cbn...
  Defined.
  (* end correct *)
  
End Stlc.
