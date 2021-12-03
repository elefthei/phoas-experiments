Require Import Coqprime.elliptic.ZEll.
Require Import Coqprime.elliptic.ZEll.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.ZArith.BinInt.

From STLCZK Require Import GaloisField.
From STLCZK Require Import Ltac.
From Coq Require Import Vectors.VectorDef.
From Coq Require Import Init.Nat.
From Coq  Require Import Program.Equality.

Set Implicit Arguments.
Set Maximal Implicit Insertion.

Module Stlc(Import PF: GaloisField.GaloisField).
  Import PF.

  (** Use the same reified type for the whole development *)
  Inductive type : Type :=
  | TBool: type
  | TNum: type
  | TArrow : type -> type -> type.

  Declare Custom Entry stlc_ty.
  Notation "<{{ e }}>" := e (e custom stlc_ty at level 99).
  Notation "( x )" := x (in custom stlc_ty, x at level 99).
  Notation "x" := x (in custom stlc_ty at level 0, x constr at level 0).  
  Notation "S -> T" := (TArrow S T)
                         (in custom stlc_ty at level 2, right associativity).
  Notation "'Num'" := TNum (in custom stlc_ty at level 0).
  Notation "'Bool'" := TBool (in custom stlc_ty at level 0).

  (** This is STLC PHOAS syntax with strong normalization *)
  Fixpoint typeDenote(t: type): Type :=
    match t with
    | <{{ Bool }}> => bool
    | <{{ Num }}> => Fp
    | <{{ a -> b }}> => (typeDenote a) -> (typeDenote b)
    end.

  Section pterms.
    Variable var: type -> Type.

    Inductive PTerm : type -> Type :=
    (* Pure *)
    (* Finite field arithmetic *)
    | ADD: PTerm <{{ Num }}> -> PTerm <{{ Num }}> -> PTerm <{{ Num }}>
    | SUB: PTerm <{{ Num }}> -> PTerm <{{ Num }}> -> PTerm <{{ Num }}>
    | MUL: PTerm <{{ Num }}> -> PTerm <{{ Num }}> -> PTerm <{{ Num }}>
    | DIV: PTerm <{{ Num }}> -> PTerm <{{ Num }}> -> PTerm <{{ Num }}>
    | ITE: forall t, PTerm <{{ Bool }}> -> PTerm t -> PTerm t -> PTerm t
    (* Logical formulas *)
    | EQ: PTerm <{{ Num }}> -> PTerm <{{ Num }}> -> PTerm <{{ Bool }}>
    | AND: PTerm <{{ Bool }}> -> PTerm <{{ Bool }}> -> PTerm <{{ Bool }}>
    | OR: PTerm <{{ Bool }}> -> PTerm <{{ Bool }}> -> PTerm <{{ Bool }}>
    | NOT: PTerm <{{ Bool }}> -> PTerm <{{ Bool }}>
    | L: forall a, LTerm a -> PTerm a
    with LTerm: type -> Type :=
    (* Constants *)
    | NUM: Fp -> LTerm <{{ Num }}>
    | BOOL: bool -> LTerm <{{ Bool }}>
    (* Lambda *)
    | APP: forall a b, LTerm <{{ a -> b }}> -> LTerm a -> LTerm b
    | VAR: forall a, var a -> LTerm a
    | LAM: forall a b, (var a -> LTerm b) -> LTerm <{{ a ->  b }}>
    | P: forall a, PTerm a -> LTerm a.

    (**
PTerm_LTerm_rec
     : forall (P0 : forall t : type, PTerm t -> Type) (P1 : forall t : type, LTerm t -> Type),
       (forall p : PTerm <{{ Num }}>,
        P0 <{{ Num }}> p ->
        forall p0 : PTerm <{{ Num }}>, P0 <{{ Num }}> p0 -> P0 <{{ Num }}> (ADD p p0)) ->
       (forall p : PTerm <{{ Num }}>,
        P0 <{{ Num }}> p ->
        forall p0 : PTerm <{{ Num }}>, P0 <{{ Num }}> p0 -> P0 <{{ Num }}> (SUB p p0)) ->
       (forall p : PTerm <{{ Num }}>,
        P0 <{{ Num }}> p ->
        forall p0 : PTerm <{{ Num }}>, P0 <{{ Num }}> p0 -> P0 <{{ Num }}> (MUL p p0)) ->
       (forall p : PTerm <{{ Num }}>,
        P0 <{{ Num }}> p ->
        forall p0 : PTerm <{{ Num }}>, P0 <{{ Num }}> p0 -> P0 <{{ Num }}> (DIV p p0)) ->
       (forall (t : type) (p : PTerm <{{ Bool }}>),
        P0 <{{ Bool }}> p ->
        forall p0 : PTerm t, P0 t p0 -> forall p1 : PTerm t, P0 t p1 -> P0 t (ITE p p0 p1)) ->
       (forall p : PTerm <{{ Num }}>,
        P0 <{{ Num }}> p ->
        forall p0 : PTerm <{{ Num }}>, P0 <{{ Num }}> p0 -> P0 <{{ Bool }}> (EQ p p0)) ->
       (forall p : PTerm <{{ Bool }}>,
        P0 <{{ Bool }}> p ->
        forall p0 : PTerm <{{ Bool }}>, P0 <{{ Bool }}> p0 -> P0 <{{ Bool }}> (AND p p0)) ->
       (forall p : PTerm <{{ Bool }}>,
        P0 <{{ Bool }}> p ->
        forall p0 : PTerm <{{ Bool }}>, P0 <{{ Bool }}> p0 -> P0 <{{ Bool }}> (OR p p0)) ->
       (forall p : PTerm <{{ Bool }}>, P0 <{{ Bool }}> p -> P0 <{{ Bool }}> (NOT p)) ->
       (forall (a : type) (l : LTerm a), P1 a l -> P0 a (L l)) ->
       (forall f9 : Fp, P1 <{{ Num }}> (NUM f9)) ->
       (forall b : bool, P1 <{{ Bool }}> (BOOL b)) ->
       (forall (a b : type) (l : LTerm <{{ a -> b }}>),
        P1 <{{ a -> b }}> l -> forall l0 : LTerm a, P1 a l0 -> P1 b (APP l l0)) ->
       (forall (a : type) (v : var a), P1 a (VAR v)) ->
       (forall (a b : type) (l : var a -> LTerm b),
        (forall v : var a, P1 b (l v)) -> P1 <{{ a -> b }}> (LAM l)) ->
       (forall (a : type) (p : PTerm a), P0 a p -> P1 a (P p)) ->
       forall (t : type) (p : PTerm t), P0 t p
*)
    Scheme PTerm_LTerm_rec := Induction for PTerm Sort Type
      with LTerm_PTerm_rec := Induction for LTerm Sort Type.
  End pterms.

  Arguments VAR [var a].
  Arguments NUM {var}.
  Arguments BOOL {var}.
  Arguments APP [var a b].
  Arguments LAM [var a b].
  Arguments L {var a}.
  
  Arguments ADD {var}.
  Arguments SUB {var}.
  Arguments MUL {var}.
  Arguments DIV {var}.
  Arguments ITE {var t}.
  Arguments EQ {var}.
  Arguments AND {var}.
  Arguments OR {var}.
  Arguments NOT {var}.
  Arguments P {var a}.

  Fixpoint ptermDenote t (e: PTerm typeDenote t): typeDenote t :=
    match e in (PTerm _ t) return (typeDenote t) with
    | ADD a b => pkplus (ptermDenote a) (ptermDenote b)
    | SUB a b => pksub (ptermDenote a) (ptermDenote b)
    | MUL a b => pkmul (ptermDenote a) (ptermDenote b)
    | DIV a b => pkdiv (ptermDenote a) (ptermDenote b)
    | ITE c a b => if (ptermDenote c) then (ptermDenote a) else (ptermDenote b)
    | EQ a b => if eq_field (ptermDenote a) (ptermDenote b) then true else false
    | AND a b => andb (ptermDenote a) (ptermDenote b)
    | OR a b => orb (ptermDenote a) (ptermDenote b)
    | NOT a => negb (ptermDenote a)
    | L a => ltermDenote a
    end
  with ltermDenote t (e : LTerm typeDenote t) {struct e} : typeDenote t :=
    match e in (LTerm _ t) return (typeDenote t) with
    | VAR v => v
    | NUM f => f
    | BOOL v => v
    | APP e1 e2 => (ltermDenote e1) (ltermDenote e2)
    | LAM e' => fun x => ltermDenote (e' x)
    | P e => ptermDenote e
    end.
  
  (* Normalization via reify/reflect Danvy et al. for LTerms *)
  Class LNbe (t: type) := {
    reify: typeDenote t -> LTerm typeDenote t;
    reflect: LTerm typeDenote t -> typeDenote t;
                         }.
                                                    
  Instance LNbe_lam {a b: type} `(LNbe a) `(LNbe b) : LNbe <{{ a -> b }}> := {
    reify v := LAM (fun x => reify (v (reflect (VAR x))));   
    reflect e := fun x => reflect (APP e (reify x));
                                                                           }.

  Instance LNbe_num : LNbe <{{ Num }}> := {
    reify v := NUM v;
    reflect v := ltermDenote v;
                                        }.
  
  Instance LNbe_bool : LNbe <{{ Bool }}> := {
    reify v := BOOL v;
    reflect v := ltermDenote v;
                                          }.
  
  (* Fine-grained normalization co-recursively in PrimaryOps terms (PTerms) and
     Lambda Calculus terms (LTerms) *)
  Class Nbe (t: type) := {
    pnorm: PTerm typeDenote t -> PTerm typeDenote t;
    lnorm: LTerm typeDenote t -> LTerm typeDenote t
                        }.
  
  (* This is needed so instance resolution succeeds *)
  Hint Extern 5 (Nbe ?X) =>
  match goal with
  | [ H : ?a =  <{{ ?b }}> |- ?g ] => idtac a b g; inversion H; subst; clear H; eauto
  end: typeclass_instances.

  Hint Extern 5 (LNbe ?X) =>
  match goal with
  | [ H : ?a =  <{{ ?b }}> |- ?g ] => idtac a b g; inversion H; subst; clear H; eauto
  end: typeclass_instances.


  Program Fixpoint pnorm_num(e: PTerm typeDenote <{{ Num }}>): PTerm typeDenote <{{ Num }}> :=
      match e with
      | ADD e1 e2 =>
        let p1 := pnorm_num e1 in
        let p2 := pnorm_num e2 in
        match p1, p2 return (PTerm typeDenote <{{ Num }}>) with
        | L (NUM n1), L (NUM n2) => L (NUM (pkplus n1 n2))
        | _, _ => ADD p1 p2
        end
      | SUB e1 e2 =>
        let p1 := pnorm_num e1 in
        let p2 := pnorm_num e2 in
        match p1, p2 return (PTerm typeDenote <{{ Num }}>) with
        | L (NUM n1), L (NUM n2) => L (NUM (pksub n1 n2))
        | _, _ => SUB p1 p2
        end         
      | MUL e1 e2 =>
        let p1 := pnorm_num e1 in
        let p2 := pnorm_num e2 in
        match p1, p2 return (PTerm typeDenote <{{ Num }}>) with
        | L (NUM n1), L (NUM n2) => L (NUM (pkmul n1 n2))
        | _, _ => MUL p1 p2
        end
      | DIV e1 e2 =>
        let p1 := pnorm_num e1 in
        let p2 := pnorm_num e2 in
        match p1, p2 return (PTerm typeDenote <{{ Num }}>) with
        | L (NUM n1), L (NUM n2) => L (NUM (pkdiv n1 n2))
        | _, _ => DIV p1 p2
        end
      | ITE c a b =>
        let pc := pnorm_bool c in
        match pc return (PTerm typeDenote <{{ Num }}>) with
        | L (BOOL true) => pnorm_num a
        | L (BOOL false) => pnorm_num b
        | _ => ITE pc (pnorm_num a) (pnorm_num b)
        end
      | L a => L (lnorm_num a)
      (* Bogus cases *)
      | EQ a b => EQ a b
      | AND e1 e2 => AND e1 e2
      | OR e1 e2 => OR e1 e2
      | NOT a => NOT a
      end
  with lnorm_num (e: LTerm typeDenote <{{ Num }}>): LTerm typeDenote <{{ Num }}> :=
         match e with
         | P p => P (pnorm_num p)
         | APP e1 e2 => reify (reflect e)
         | LAM _ => reify (reflect e)
         | VAR _ => reify (reflect e)
         | NUM f => NUM f
         (* Bogus terms *)
         | BOOL v => BOOL v
         end
  with pnorm_bool(e: PTerm typeDenote <{{ Bool }}>): PTerm typeDenote <{{ Bool }}> :=
         match e with
         | EQ e1 e2 =>
           let p1 := pnorm_num e1 in
           let p2 := pnorm_num e2 in
           match p1, p2 return (PTerm typeDenote <{{ Bool }}>) with
           | L (NUM n1), L (NUM n2) => L (BOOL (if eq_field n1 n2 then true else false))
           | _, _ => EQ p1 p2
           end
         | AND e1 e2 => 
           let p1 := pnorm_bool e1 in
           let p2 := pnorm_bool e2 in
           match p1, p2 return (PTerm typeDenote <{{ Bool }}>) with
           | L (BOOL b1), L (BOOL b2) => L (BOOL (andb b1 b2))
           | _, _ => AND p1 p2
           end
         | OR e1 e2 =>
           let p1 := pnorm_bool e1 in
           let p2 := pnorm_bool e2 in
           match p1, p2 return (PTerm typeDenote <{{ Bool }}>) with
           | L (BOOL b1), L (BOOL b2) => L (BOOL (orb b1 b2))
           | _, _ => OR p1 p2
           end
         | NOT a =>
           let p1 := pnorm_bool a in
           match p1 return (PTerm typeDenote <{{ Bool }}>) with
           | L (BOOL b1) => L (BOOL (negb b1))
           | _ => NOT p1
           end
         | L a => L (lnorm_bool a)
         | ITE c a b =>
           let pc := pnorm_bool c in
           match pc return (PTerm typeDenote <{{ Bool }}>) with
           | L (BOOL true) => pnorm_bool a
           | L (BOOL false) => pnorm_bool b
           | _ => ITE pc (pnorm_bool a) (pnorm_bool b)
           end
         (* Bogus patterns *)
         | ADD a b => ADD a b
         | SUB a b => SUB a b
         | MUL a b => MUL a b
         | DIV a b => DIV a b
         end
  with lnorm_bool (e: LTerm typeDenote <{{ Bool }}>): LTerm typeDenote <{{ Bool }}> :=
         match e with
         | P p => P (pnorm_bool p)
         | APP e1 e2 => reify (reflect e)
         | LAM _ => reify (reflect e)
         | VAR _ => reify (reflect e)
         | BOOL v => BOOL v
         (* Bogus terms *)
         | NUM f => NUM f
         end.
    
  Instance Nbe_num : Nbe <{{ Num }}> := {
    pnorm := pnorm_num;
    lnorm := lnorm_num;
    }.

  Instance Nbe_bool: Nbe <{{ Bool }}> := {
    pnorm := pnorm_bool;
    lnorm := lnorm_bool
                                        }.

  
  Program Fixpoint lnorm_arr{a b: type} `{Nbe <{{ Bool }}>}
          `{LNbe a} `{LNbe b} `{Nbe a} `{Nbe b} `{Nbe <{{Bool}}>}
          (e: LTerm typeDenote <{{a -> b }}>) : LTerm typeDenote <{{ a -> b }}> :=
    match e with
    | P p => P (pnorm_arr p)
    | APP e1 e2 => reify (reflect e)
    | LAM e' => LAM (fun x => lnorm (e' x))
    | VAR _ => reify (reflect e)
    (* Bogus terms *)
    | NUM f => NUM f
    | BOOL v => BOOL v
    end
  with pnorm_arr{a b: type}
          `{LNbe a} `{LNbe b} `{Nbe <{{Bool}}>} `{Nbe a} `{Nbe b}
          (e: PTerm typeDenote <{{a -> b }}>) : PTerm typeDenote <{{ a -> b }}> :=
    match e with
    | ITE c e1 e2 =>
      L (LAM (fun x => P (ITE (pnorm c)
                           (L (lnorm (APP (P (pnorm_arr e1)) (VAR x))))
                           (L (lnorm (APP (P (pnorm_arr e2)) (VAR x)))))))
    | L p => L (lnorm_arr p)
    (* Bogus terms *)
    | ADD a b => ADD a b
    | SUB a b => SUB a b
    | MUL a b => MUL a b
    | DIV a b => DIV a b
    | EQ a b => EQ a b
    | AND a b => AND a b
    | OR a b => OR a b
    | NOT a => NOT a
    end.
                                                     
  Instance Nbe_lam {a b: type} `(Nbe a) `(Nbe b) `(LNbe a) `(LNbe b): Nbe <{{ a -> b }}> := {
    pnorm := pnorm_arr;
    lnorm := lnorm_arr
                                                                                            }.
  
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
  Notation "'ifi' x 'then' y 'else' z" :=
    (ITE x y z) (in custom stlc at level 89,
                    x custom stlc at level 99,
                    y custom stlc at level 99,
                    z custom stlc at level 99,
                    left associativity).  

  Coercion P: PTerm >-> LTerm.
  Coercion L: LTerm >-> PTerm.

  Definition t: LTerm typeDenote <{{ Bool -> Bool }}> :=
    <{ \x, (ifi # x then \y, # y else \z, ! # z) # x }>.

  Print t.
  Eval cbv in lnorm_arr t.
  
  Inductive fof: type -> Prop :=
  | fo_bool: fof <{{ Bool }}>
  | fo_num: fof <{{ Num }}>
  | fof_bool: forall a,
      fof <{{ a }}> ->
      fof <{{ Bool -> a }}>
  | fof_num: forall a,
      fof <{{ a }}> ->
      fof <{{ Num -> a }}>.

  Inductive value: forall (t: type), LTerm typeDenote t -> Prop :=
  | Value_bool: forall x, @value <{{ Bool }}> (@VAR typeDenote <{{ Bool }}> x)
  | Value_btrue: @value <{{ Bool }}> <{ true }>
  | Value_bfalse: @value <{{ Bool }}> <{ false }>
  | Value_var: forall x, @value <{{ Num }}> (@VAR typeDenote <{{ Num }}> x)
  | Value_const: forall (x: Fp), @value <{{ Num }}> (NUM x).
  
  Inductive hnff: forall (t: type), LTerm typeDenote t -> Prop :=
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
  Theorem normalize_correct: forall (t: type) (e: LTerm typeDenote t),
      fof t  -> 
      @hnff t (normalize e).
  Proof with eauto.
    intros.
    generalize dependent e.
    generalize dependent H.
    induction t; intros; dependent destruction e; cbn; try constructor;
      invert H; cbn; try constructor...
    - destruct b; constructor.
    - destruct (ltermDenote e1); constructor. 
    - destruct t; constructor.
    - admit.  
    - admit. 
  Admitted.



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
