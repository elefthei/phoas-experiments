From Coq Require Import Init.Nat.
From Coq  Require Import Program.Equality.

Set Implicit Arguments.
Set Maximal Implicit Insertion.

Module Stlc.

  (** Use the same reified type for the whole development *)
  Inductive type : Type :=
  | TBool: type
  | TNum: type
  | TArrow : type -> type -> type.

  Declare Custom Entry stlc_ty.
  Notation "<{{ e }}>" := e (e custom stlc_ty at level 99).
  Notation "( x )" := x (in custom stlc_ty, x at level 99).
  Notation "x" := x (in custom stlc_ty at level 0, x constr at level 0).  
  Notation "S -> T" := (TArrow S T) (in custom stlc_ty at level 2, right associativity).
  Notation "'Num'" := TNum (in custom stlc_ty at level 0).
  Notation "'Bool'" := TBool (in custom stlc_ty at level 0).

  (** This is STLC PHOAS syntax [Term] without control flow,
      it includes normalization by evaluation using reify/reflect as seen in Oliver Danvy et al.
      As reification of Coq terms [if _ then _ else _] is impossible without
      meta-programming, we develop a meta-language [IM] that reifies control-flow, then
      commute with reify/reflect on STLC with our meta-language.
      
      We get the following commutative square for *reflect*


                                  ireflect
      IM (Term typeDenote) t ----------------> IM typeDenote t
             |                                       | 
             |                                       |
             |                                       |
             v                    reflect            v
          Term typeDenote t  -----------------> typeDenote t


      And the following for *reify*
      
                        reify
      typeDenote t  -------------> Term typeDenote t
             |                             | 
             | RET                         | RET
             |                             |
             v            ireify           v
      IM typeDenote t  ----------------> IM (Term typeDenote) t
   *)
  Section vars.
    (** This is how to get reflected Coq terms *)
    Variable var : type -> Type.

    Inductive Term: type -> Type :=
    (* Constants *)
    | NUM: nat -> Term <{{ Num }}>
    | BOOL: bool -> Term <{{ Bool }}>
    (* Finite field arithmetic *)
    | ADD: Term <{{ Num }}> -> Term <{{ Num }}> -> Term <{{ Num }}>
    | SUB: Term <{{ Num }}> -> Term <{{ Num }}> -> Term <{{ Num }}>
    | MUL: Term <{{ Num }}> -> Term <{{ Num }}> -> Term <{{ Num }}>
    | DIV: Term <{{ Num }}> -> Term <{{ Num }}> -> Term <{{ Num }}>
    (* Logical formulas *)
    | EQ: Term <{{ Num }}> -> Term <{{ Num }}> -> Term <{{ Bool }}>
    | AND: Term <{{ Bool }}> -> Term <{{ Bool }}> -> Term <{{ Bool }}>
    | OR: Term <{{ Bool }}> -> Term <{{ Bool }}> -> Term <{{ Bool }}>
    | NOT: Term <{{ Bool }}> -> Term <{{ Bool }}>
    (* Lambda *)
    | APP: forall a b, Term <{{ a -> b }}> -> Term a -> Term b
    | VAR: forall a, var a -> Term a
    | LAM: forall a b, (var a -> Term b) -> Term <{{ a ->  b }}>.

    Fixpoint typeDenote (t : type) : Set :=
      match t with
      | <{{ Bool }}> => bool
      | <{{ Num }}> => nat
      | <{{ t1 -> t2 }}> => typeDenote t1 -> typeDenote t2
      end.

    (* Normalization via reify/reflect Danvy et al. *)
    Class Nbe (t: type) := {
      reify: typeDenote t -> Term t;
      reflect: Term t -> typeDenote t
                          }.

    Instance Nbe_lam {a b: type} `{Nbe a} `{Nbe b}: Nbe <{{ a -> b }}> := {
      reify v := LAM (fun x => reify (v (reflect (VAR x))));        
      reflect e :=  fun x => reflect (APP e (reify x))
                                                                        }.
  End vars.

  (** This is the metalanguage with if-then-else. I am defining another
      [T: type -> Type] because I want to be able to reflect terms in stages,
      first in Terms and then in IM.

      This allows us to have both Terms and IM Terms reified,
      using [IM (Term typeDenote) t] and object terms reflected while
      meta-terms remain reified using [IM typeDenote t]. This is a handy
      trick for staged compilation of meta-languages! *)
  Section mvars.

    Variable T: type -> Type.
    Inductive IM: type -> Type :=
    | ITE: forall t, Term typeDenote <{{ Bool }}> ->
                IM t ->
                IM t ->
                IM t
    | RET: forall t, T t -> IM t.
  End mvars.

  Arguments VAR [var a].
  Arguments NUM {var}.
  Arguments BOOL {var}.
  Arguments ADD {var}.
  Arguments SUB {var}.
  Arguments MUL {var}.
  Arguments DIV {var}.
  Arguments EQ {var}.
  Arguments AND {var}.
  Arguments OR {var}.
  Arguments APP [var a b].
  Arguments LAM [var a b].
  (** Maximally insert types in class *)
  Arguments Nbe {var}.
  Arguments Nbe_lam {var} {a} {b}.
  Arguments reify {var} {t}.
  Arguments reflect {var} {t}.
  (** Meta terms *)
  Arguments ITE {T t}.
  Arguments RET {T t}.
  
  Declare Custom Entry stlc.
  Notation "'fp' n" := (NUM n) (in custom stlc at level 0).
  Notation "'true'"  := true (at level 1).
  Notation "'true'" := (BOOL true) (in custom stlc at level 0).
  Notation "'false'"  := false (at level 1).
  Notation "'false'" := (BOOL false) (in custom stlc at level 0).
  Notation "<{ e }>" := e (e custom stlc at level 99).
  Notation "( x )" := x (in custom stlc, x at level 99).
  Notation "x" := x (in custom stlc at level 0, x constr at level 0).
  Notation "x y" := (APP x y) (in custom stlc at level 1, left associativity).
  Notation "\ x , y" :=
    (LAM (fun x => y)) (in custom stlc at level 90,
                        x constr,
                        y custom stlc at level 80,
                        left associativity).
  Notation "\_ , y" :=
    (LAM (fun _ => y)) (in custom stlc at level 90,
                        y custom stlc at level 80,
                        left associativity).
  Notation "# n" := (VAR n) (in custom stlc at level 0).
  Notation "{ x }" := x (in custom stlc at level 1, x constr).  
  Notation "x + y" := (ADD x y) (in custom stlc at level 2,
                                            left associativity).
  Notation "x - y" := (SUB x y) (in custom stlc at level 2,
                                            left associativity).
  Notation "x * y" := (MUL x y) (in custom stlc at level 1,
                                            left associativity).
  Notation "x && y" := (AND x y) (in custom stlc at level 4,
                                             left associativity).
  Notation "x || y" := (OR x y) (in custom stlc at level 4,
                                             left associativity).
  Notation "x == y" := (EQ x y) (in custom stlc at level 3,
                                      left associativity).
  Notation "! x " := (NOT x) (in custom stlc at level 3).
  Notation "'if' x 'then' y 'else' z" :=
    (ITE x y z) (in custom stlc at level 89,
                    x custom stlc at level 99,
                    y custom stlc at level 99,
                    z custom stlc at level 99,
                    left associativity).  
  
  Fixpoint termDenote t (e : Term typeDenote t) {struct e} : typeDenote t :=
    match e in (Term _ t) return (typeDenote t) with
    | VAR v => v
    | NUM f => f
    | BOOL v => v
    | ADD f1 f2 => (termDenote f1) + (termDenote f2)
    | SUB f1 f2 => (termDenote f1) - (termDenote f2)
    | MUL f1 f2 => (termDenote f1) * (termDenote f2)
    | DIV f1 f2 => (termDenote f1) / (termDenote f2)
    | EQ f1 f2 => eqb (termDenote f1) (termDenote f2)
    (** Commuting conversion if/app *)
    (* | @ITE _ <{{ a -> b }}> c t e =>
      fun y => if (termDenote c) then (termDenote t) y else (termDenote e) y
    | ITE c t e => if (termDenote c) then termDenote t else termDenote e *)
    | AND b1 b2 => andb (termDenote b1) (termDenote b2)
    | OR b1 b2 => orb (termDenote b1) (termDenote b2)
    | NOT b => negb (termDenote b)
    | APP e1 e2 => (termDenote e1) (termDenote e2)
    | LAM e' => fun x => termDenote (e' x)
    end.

  Fixpoint mtermDenote t (e: IM (Term typeDenote) t) : typeDenote t :=
    match e with
    | ITE c e1 e2 => if (termDenote c) then (mtermDenote e1) else mtermDenote e2
    | RET e => termDenote e
    end.  
  
  Instance Nbe_int : Nbe <{{ Num }}> := {
    reify v := NUM v;
    reflect v := termDenote v;
                                }.

  Instance Nbe_bool : Nbe <{{ Bool }}> := {
    reify v := BOOL v;
    reflect v := termDenote v;
                                  }.

  Fixpoint resolver(t: type): Nbe t :=
    match t with
    | <{{ Bool }}> => Nbe_bool
    | <{{ Num }}> => Nbe_int
    | <{{ a -> b }}> => Nbe_lam (resolver a) (resolver b)
    end.

  Fixpoint mreflect t (e: IM (Term typeDenote) t): IM typeDenote t :=
    match e with
    | ITE c e1 e2 =>
      ITE (BOOL (reflect (resolver <{{ Bool }}>) c))
          (mreflect e1) (mreflect e2)
    | RET e => RET (reflect (resolver _) e)
    end.

  (** Conversely, this function is dumb and uninteresting. Since we cannot
      reify if-then-else statements from Gallina to IM *)
  Definition mreify{t: type} (e: typeDenote t): IM (Term typeDenote) t :=
    RET (reify (resolver t) e).

  Definition normalize {t: type} (e: Term typeDenote t) : Term typeDenote t :=
    reify (resolver t) (reflect (resolver t) e).
                                       
  Inductive fof: type -> Prop :=
  | fo_bool: fof <{{ Bool }}>
  | fo_num: fof <{{ Num }}>
  | fof_bool: forall a,
      fof <{{ a }}> ->
      fof <{{ Bool -> a }}>
  | fof_num: forall a,
      fof <{{ a }}> ->
      fof <{{ Num -> a }}>.

  Set Implicit Arguments.
  Inductive value: forall {t: type}, Term typeDenote t -> Prop :=
  | Value_bool: forall x, @value <{{ Bool }}> (@VAR typeDenote <{{ Bool }}> x)
  | Value_btrue: @value <{{ Bool }}> <{ true }>
  | Value_bfalse: @value <{{ Bool }}> <{ false }>
  | Value_const: forall (x: nat), value (NUM x).
  
  Inductive hnff: forall (t: type), Term typeDenote t -> Prop :=
  | HNF_bool_ar: forall a f,
      (forall (arg: typeDenote <{{ Bool }}>), @hnff <{{ a }}> (f arg)) ->
      @hnff <{{ Bool -> a }}> (LAM f)
  | HNF_num_ar: forall a f,
      (forall (arg: typeDenote <{{ Num }}>), @hnff <{{ a }}> (f arg)) ->
      @hnff <{{ Num -> a }}> (LAM f)
  | HNF_bool: forall e,
      value e ->
      @hnff <{{ Bool }}> e
  | HNF_num: forall e,
      value e ->
      @hnff <{{ Num }}> e.

  (** Provide default witnesses for hnff *)
  (* Hint Extern 3 (typeDenote <{{ Bool }}>) => exact (true).
  Hint Extern 3 (typeDenote <{{ Num }}>) => exact (0:%p).
  *)
  Theorem normalize_correct: forall (t: type) (e: Term typeDenote t),
      fof t  -> 
      @hnff t (@normalize t e).
  Proof with eauto.
    intros.
    generalize dependent e.
    generalize dependent H.
    induction t; intros; dependent destruction e; cbn; try constructor;
      invert H; cbn; try constructor...
    - destruct b; constructor.
    - destruct (eq_field (termDenote e1) (termDenote e2)); constructor.
    - destruct (termDenote e1); destruct (termDenote e2); constructor.
    - destruct (termDenote e1); destruct (termDenote e2); constructor.
    - destruct (termDenote e); constructor.
    - destruct (termDenote e1); destruct (termDenote e2); destruct (termDenote e3); constructor.
    - destruct ((termDenote e1 (termDenote e2))); constructor.
    - destruct t; constructor.
  Defined.


  Definition t: Term typeDenote <{{ Bool -> Bool }}> :=
    <{ \x, (if # x then \y, # y else \z, ! # z) # x }>.
  
  Eval cbv in normalize t.

  Eval cbv in reflect (resolver _) (reify (resolver <{{ Bool -> Bool }}>) f).
  Eval cbv in reflect (resolver _) (normalize t) true.

  Example notnormal: @hnff <{{ Bool -> Bool }}> (normalize t).
  Proof.
    constructor.
    intros.
    constructor.
    unfold t; simpl.
    destruct arg.
    - constructor.
    - constructor.
  Qed.

End Stlc.
