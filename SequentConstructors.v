Require Import Lists.List.
Require Import Sorting.Permutation.
Require Import Fin.
Require Import Vector.
Require Import Logic.Eqdep_dec.
Require Import Arith.PeanoNat.
Require Import Arith.Peano_dec.

Class ConstructorSpec (Ctor: Set) :=
  { contraVariantArity : Ctor -> nat;
    coVariantArity : Ctor -> nat;
    epsilon: Ctor -> Prop }.

Class ConstructorRelation (Ctor: Set) `{ConstructorSpec Ctor}
      (R : forall C D,
          (Fin.t (contraVariantArity C) -> Fin.t (contraVariantArity D)) ->
          (Fin.t (coVariantArity D) -> Fin.t (coVariantArity C)) -> Prop) :=
  { reflexivity: forall C f g,
      (forall k, f k = k) ->
      (forall k, g k = k) ->
      R C C f g;
    transitivity:
      forall C D E f g f' g' f'f gg',
        (forall k, f'f k = f' (f k)) ->
        (forall k, gg' k = g (g' k)) ->
        R C D f g -> R D E f' g' -> R C E f'f gg';
    contraMap_unique:
      forall C D f f' g g',
        R C D f g -> R C D f' g' -> forall x, g x = g' x;
    epsilon_monotonicity:
      forall C D f g, R C D f g -> epsilon C -> epsilon D }.

Module Type ConstructorSpecification.
  Parameter Ctor: Set.
  Parameter CtorSpec: ConstructorSpec Ctor.
  Parameter R: forall C D,
      (Fin.t (contraVariantArity C) -> Fin.t (contraVariantArity D)) ->
      (Fin.t (coVariantArity D) -> Fin.t (coVariantArity C)) -> Prop.
  Parameter CtorRel: ConstructorRelation Ctor R.

  Parameter Ctor_eq_dec: forall (C D: Ctor), { C = D } + { C <> D }.
End ConstructorSpecification.

Module Type SubtypeSystem(Import Spec: ConstructorSpecification).

  Unset Elimination Schemes.
  Inductive IntersectionType: Set :=
  | Constr : forall C,
      t (IntersectionType) (contraVariantArity C) ->
      t (IntersectionType) (coVariantArity C) ->
      IntersectionType
  | Inter: IntersectionType -> IntersectionType -> IntersectionType. 

  (* Boilerplate for induction/recursion on nested vectors *)
  Fixpoint IntersectionType_rect
           (P: IntersectionType -> Type)
           (constr_case:
              forall C
                (contraArgs: t (IntersectionType) (contraVariantArity C))
                (coArgs: t (IntersectionType) (coVariantArity C)),
                (forall k, P (nth contraArgs k)) ->
                (forall k, P (nth coArgs k)) ->
                P (Constr C contraArgs coArgs))
           (inter_case: forall sigma tau, P sigma -> P tau -> P (Inter sigma tau))
           (sigma: IntersectionType) {struct sigma}: P (sigma) :=
    match sigma with
    | Constr C contraArgs coArgs =>
      constr_case C contraArgs coArgs
                  ((fix contra_prf n (xs: t IntersectionType n) {struct xs}: forall k, P (nth xs k) :=
                      match xs as xs' in t _ n' return (forall (k : Fin.t n'), P (nth xs' k)) with
                      | nil _ => fun k => Fin.case0 (fun k => P (nth (nil _) k)) k
                      | cons _ x _ xs =>
                        fun k =>
                          Fin.caseS' k (fun k => P (nth (cons _ x _ xs) k))
                                     (IntersectionType_rect P constr_case inter_case x)
                                     (contra_prf _ xs)
                      end) _ contraArgs)
                  ((fix co_prf n (xs: t IntersectionType n) {struct xs}: forall k, P (nth xs k) :=
                      match xs as xs' in t _ n' return (forall (k : Fin.t n'), P (nth xs' k)) with
                      | nil _ => fun k => Fin.case0 (fun k => P (nth (nil _) k)) k
                      | cons _ x _ xs =>
                        fun k =>
                          Fin.caseS' k (fun k => P (nth (cons _ x _ xs) k))
                                     (IntersectionType_rect P constr_case inter_case x)
                                     (co_prf _ xs)
                      end) _ coArgs)
    | Inter sigma tau =>
      inter_case sigma tau
                 (IntersectionType_rect P constr_case inter_case sigma)
                 (IntersectionType_rect P constr_case inter_case tau)
    end.
  Definition IntersectionType_ind
             (P : IntersectionType -> Prop)
             (constr_case:
                forall C
                  (contraArgs: t (IntersectionType) (contraVariantArity C))
                  (coArgs: t (IntersectionType) (coVariantArity C)),
                  (forall k, P (nth contraArgs k)) ->
                  (forall k, P (nth coArgs k)) ->
                  P (Constr C contraArgs coArgs))
             (inter_case: forall sigma tau, P sigma -> P tau -> P (Inter sigma tau))
             (sigma: IntersectionType): P (sigma) :=
    IntersectionType_rect P constr_case inter_case sigma.

  Definition IntersectionType_rec
             (P : IntersectionType -> Set)
             (constr_case:
                forall C
                  (contraArgs: t (IntersectionType) (contraVariantArity C))
                  (coArgs: t (IntersectionType) (coVariantArity C)),
                  (forall k, P (nth contraArgs k)) ->
                  (forall k, P (nth coArgs k)) ->
                  P (Constr C contraArgs coArgs))
             (inter_case: forall sigma tau, P sigma -> P tau -> P (Inter sigma tau))
             (sigma: IntersectionType): P (sigma) :=
    IntersectionType_rect P constr_case inter_case sigma.

  (* Helper lemmas *)
  Lemma Vector_tl_ineq:
    forall {T} (x : T) {n} xs ys, xs <> ys -> cons T x n xs <> cons T x n ys.
  Proof.
    intros T x n xs ys ineq.
    intro devil.
    injection devil as devil.
    contradict ineq.
    apply inj_pair2_eq_dec.
    - apply Nat.eq_dec.
    - exact devil.
  Qed.
  Definition Vector_eq_dec:
    forall {T} {n}
      (t_eq_dec: forall (x y: T), {x = y} + {x <> y}) (xs ys: t T n), {xs = ys} + {xs <> ys}.
  Proof.
    intros T n t_eq_dec xs.
    induction xs as [ | x n xs IH ]; intros ys.
    - apply (fun P prf => case0 P prf ys).
      left; reflexivity.
    - apply (caseS' ys).
      clear ys; intros y ys.
      destruct (t_eq_dec x y) as [ x_eq | x_ineq ].
      + rewrite x_eq.
        destruct (IH ys) as [ xs_eq | ].
        * rewrite xs_eq.
          left; reflexivity.
        * right; apply Vector_tl_ineq; assumption.
      + right; intro devil; inversion devil.
        contradiction x_ineq.
  Defined.

  (* Decidable syntactic equality on types (helpful e.g. for pattern matching) *)
  Fixpoint IntersectionType_eq_dec (sigma: IntersectionType): forall tau, { sigma = tau } + { sigma <> tau }.
  Proof.
    intro tau.
    destruct sigma as [ C contraArgs coArgs | sigma1 sigma2 ];
      destruct tau as [ D contraArgs' coArgs' | tau1 tau2 ];
      try solve [ right; intro devil; inversion devil ].
    - destruct (Ctor_eq_dec C D) as [ prf | disprf ];
        [ | right; intro devil; inversion devil; contradiction ].
      revert contraArgs' coArgs'.
      rewrite <- prf.
      clear D prf.
      intros contraArgs' coArgs'.
      destruct (Vector_eq_dec IntersectionType_eq_dec contraArgs contraArgs') as [ eq | ineq ];
        [ | right; intro devil; inversion devil as [ contraArgs_eq ] ].
      + destruct (Vector_eq_dec IntersectionType_eq_dec coArgs coArgs') as [ eq' | ineq' ];
          [ rewrite eq; rewrite eq'; left; reflexivity
          | right; intro devil; inversion devil as [ [ contraArgs_eq coArgs_eq ] ] ].
        * apply ineq'.
          revert coArgs_eq.
          clear ...
          intro coArgs_eq.
          assert (coArgs_eq': existT (fun n => t IntersectionType n) (coVariantArity C) coArgs =
                existT (fun n => t IntersectionType n) (coVariantArity C) coArgs').
          { remember (existT (fun n => t IntersectionType n) (coVariantArity C) coArgs) as lhs eqn:lhs_eq.
            dependent rewrite coArgs_eq in lhs_eq.
            rewrite lhs_eq.
            reflexivity. }
          clear coArgs_eq.
          revert coArgs coArgs' coArgs_eq'.
          generalize (coVariantArity C).
          intros n coArgs coArgs' coArgs_eq.
          induction coArgs.
          { apply (fun r => case0 _ r coArgs').
            reflexivity. }
          { revert coArgs_eq.
            apply (caseS' coArgs'); clear coArgs'; intros arg' coArgs' coArgs_eq.
            inversion coArgs_eq as [ [ arg'_eq coArgs_eq' ] ].
            apply f_equal.
            auto.  }          
      + apply ineq.
        assert (contraArgs_eq': existT (fun n => t IntersectionType n) (contraVariantArity C) contraArgs =
                existT (fun n => t IntersectionType n) (contraVariantArity C) contraArgs').
        { remember (existT (fun n => t IntersectionType n) (contraVariantArity C) contraArgs) as lhs eqn:lhs_eq.
          dependent rewrite contraArgs_eq in lhs_eq.
          rewrite lhs_eq.
          reflexivity. }
        clear ineq devil contraArgs_eq.
        revert contraArgs contraArgs' contraArgs_eq'.
        clear ...
        generalize (contraVariantArity C).
        intros n contraArgs contraArgs' contraArgs_eq.
        induction contraArgs.
        * apply (fun r => case0 _ r contraArgs').
          reflexivity.
        * revert contraArgs_eq.
          apply (caseS' contraArgs'); clear contraArgs'; intros arg' contraArgs' contraArgs_eq.
          inversion contraArgs_eq as [ [ arg'_eq contraArgs_eq' ] ].
          apply f_equal.
          auto.       
    - destruct (IntersectionType_eq_dec sigma1 tau1) as [ prf1 | disprf1 ];
        [ rewrite prf1 | right; intro devil; inversion devil; contradiction ];
        destruct (IntersectionType_eq_dec sigma2 tau2) as [ prf2 | disprf2 ];
        [ rewrite prf2 | right; intro devil; inversion devil; contradiction ];
        left; reflexivity.
  Defined.

  Set Elimination Schemes.


  (* Helper stuff to unclutter definitions *)
  Import ListNotations.
  Import EqNotations.

  Definition fixContraArity
             {contraArity: nat}
             {k: nat} {ctors: t Ctor (S k)}
             (arityOk: forall i, contraArity = contraVariantArity (nth ctors i))
             {i: Fin.t k}
             (f: Fin.t contraArity -> Fin.t contraArity):
    Fin.t (contraVariantArity (nth ctors (FS i))) -> Fin.t (contraVariantArity (nth ctors F1)) :=
    rew [fun n => Fin.t n -> _ ] arityOk (FS i) in
      rew [fun n => _ -> Fin.t n] arityOk F1 in f.

  Definition fixCoArity
             {coArity: nat}
             {k: nat} {ctors: t Ctor (S k)}
             (arityOk: forall i, coArity = coVariantArity (nth ctors i))
             {i: Fin.t k}
             (f: Fin.t coArity -> Fin.t coArity):
    Fin.t (coVariantArity (nth ctors F1)) -> Fin.t (coVariantArity (nth ctors (FS i))) :=
    rew [fun n => Fin.t n -> _ ] arityOk F1 in
      rew [fun n => _ -> Fin.t n] arityOk (FS i) in f.
  
  Fixpoint positions (n : nat): t (Fin.t n) n :=
    match n with
    | O => nil _
    | S n => cons _ F1 _ (map FS (positions n))
    end.

  Lemma positions_spec: forall n k, nth (positions n) k = k.
  Proof.
    intro n.
    induction n as [ | n IHn ]; intro k.
    - inversion k.
    - remember (S n) as n' eqn:n'_eq.
      destruct k.
      + reflexivity.
      + simpl.
        injection n'_eq as n_eq.
        revert k.
        rewrite n_eq.
        intro k.
        rewrite (nth_map _ _ _ _ (eq_refl k)).
        rewrite (IHn k).
        reflexivity.
  Qed.

  Definition makeConstructor
             {k : nat} {coArity contraArity: nat}
             (ctors: t Ctor k)
             (contraArgs: t (t IntersectionType contraArity) k)
             (coArgs: t (t IntersectionType coArity) k)
             (contraArityOk: forall i, contraArity = contraVariantArity (nth ctors i))
             (coArityOk: forall i, coArity = coVariantArity (nth ctors i))
             (i: Fin.t k): IntersectionType :=
    Constr (nth ctors i)
           (rew (contraArityOk i) in nth contraArgs i)
           (rew (coArityOk i) in nth coArgs i).


  (* The subtype system *)  
  Inductive LEQ: list IntersectionType -> IntersectionType -> Prop :=
  | CtorLeft: forall C contraArgs coArgs rho Gamma Gamma',
      Permutation Gamma' ((Constr C contraArgs coArgs) :: Gamma) ->
      LEQ Gamma rho  ->      
      LEQ Gamma' rho
  | InterRight: forall Gamma sigma tau, LEQ Gamma sigma -> LEQ Gamma tau -> LEQ Gamma (Inter sigma tau)
  | InterLeft: forall Gamma sigma tau rho Gamma' Gamma'',
      Permutation Gamma' (sigma :: tau :: Gamma) ->
      Permutation Gamma'' (Inter sigma tau :: Gamma) ->
      LEQ Gamma' rho ->
      LEQ Gamma'' rho
  | CtorRight:
      forall k contraArity coArity
        (ctors: t Ctor (S k))
        (contraArgs: t (t IntersectionType contraArity) (S k))
        (coArgs: t (t IntersectionType coArity) (S k))
        (fs: t (Fin.t contraArity -> Fin.t contraArity) k)
        (gs: t (Fin.t coArity -> Fin.t coArity) k)
        (contraArityOk: forall i, contraArity = contraVariantArity (nth ctors i))
        (coArityOk: forall i, coArity = coVariantArity (nth ctors i))
        (Gamma: list IntersectionType),
        (k = 0 -> epsilon (hd ctors)) ->
        (forall (i: Fin.t k),
            R (nth ctors (FS i)) (nth ctors F1)
              (fixContraArity contraArityOk (nth fs i))
              (fixCoArity coArityOk (nth gs i))) ->
        (forall i j,
            LEQ (nth (nth contraArgs F1) j :: []) (nth (nth contraArgs (FS i)) ((nth fs i) j))) ->
        (forall i, exists Gamma,
              Permutation (to_list (map (fun j => nth (nth coArgs (FS j)) ((nth gs j) i)) (positions k))) Gamma /\
              LEQ Gamma (nth (nth coArgs F1) i)) ->
        Permutation
          Gamma
          (to_list (map (fun i => makeConstructor ctors contraArgs coArgs contraArityOk coArityOk (FS i))
                        (positions k))) ->        
        LEQ Gamma (makeConstructor ctors contraArgs coArgs contraArityOk coArityOk F1).

  (* Derived rules *)
  
  Lemma sigmaLeft:
    forall Gamma Gamma' sigma rho,
      Permutation Gamma' (sigma :: Gamma) ->
      LEQ Gamma rho -> LEQ Gamma' rho.
  Proof.
    intros Gamma Gamma' sigma.
    revert Gamma Gamma'.
    induction sigma as [ C contraArgs coArgs IHcontra IHco | sigma1 sigma2  IHsigma1 IHsigma2 ];
      intros Gamma Gamma' rho permPrf rhoPrf.
    - apply (CtorLeft C contraArgs coArgs rho Gamma); assumption.
    - apply (InterLeft Gamma sigma1 sigma2 rho (sigma1::sigma2::Gamma) Gamma').
      + apply Permutation_refl.
      + assumption.
      + eapply IHsigma1; [ apply Permutation_refl | ].
        eapply IHsigma2; [ apply Permutation_refl | ].
        assumption.
  Qed.

  Lemma sigmaRefl: forall sigma, LEQ [sigma] sigma.
  Proof.
    intro sigma.
    induction sigma as [ C contraArgs coArgs IHcontra IHco | sigma1 sigma2 IHsigma1 IHsigma2].
    - set (ctors := cons _ C _ (cons _ C _ (nil _))).
      assert (contraArityOk : forall i, contraVariantArity C = contraVariantArity (nth ctors i)).
      { intro i.
        apply (Fin.caseS' i); [ reflexivity | clear i; intro i ].
        apply (Fin.caseS' i); [ reflexivity | clear i; intro i ].
        inversion i. }
      assert (coArityOk : forall i, coVariantArity C = coVariantArity (nth ctors i)).
      { intro i.
        apply (Fin.caseS' i); [ reflexivity | clear i; intro i ].
        apply (Fin.caseS' i); [ reflexivity | clear i; intro i ].
        inversion i. }        
      generalize (CtorRight 1 (contraVariantArity C) (coVariantArity C)
                            (cons _ C _ (cons _ C _ (nil _)))
                            (cons _ contraArgs _ (cons _ contraArgs _ (nil _)))
                            (cons _ coArgs _ (cons _ coArgs _ (nil _)))
                            (cons _ (fun x => x) _ (nil _))
                            (cons _ (fun x => x) _ (nil _))
                            contraArityOk coArityOk
                            [Constr C contraArgs coArgs]
                            (fun k_eq =>
                               False_ind _ (match k_eq in _ = n return match n with | 1 => True | _ => False end with
                                            | eq_refl => I
                                            end))).
      unfold makeConstructor.
      rewrite (UIP_dec (Nat.eq_dec) (contraArityOk F1) eq_refl).
      rewrite (UIP_dec (Nat.eq_dec) (coArityOk F1) eq_refl).
      simpl.
      intro result; apply result; clear result.
      + intro i.
        apply (Fin.caseS' i); [ clear i | intro devil; inversion devil ].
        simpl.
        apply reflexivity.
        * intro k.
          unfold fixContraArity.
          simpl.
          match goal with
          | [|- (rew [fun n => _] ?p1 in _) k = _ ] =>
            set (eq1 := p1); simpl in eq1;
              rewrite (UIP_dec (Nat.eq_dec) eq1 eq_refl);
              simpl
          end.          
          match goal with
          | [|- (rew [fun n => _] ?p1 in _) k = _ ] =>
            set (eq2 := p1); simpl in eq2;
              rewrite (UIP_dec (Nat.eq_dec) eq2 eq_refl);
              simpl
          end.
          reflexivity.
        * intro k.
          unfold fixCoArity.
          simpl.
          match goal with
          | [|- (rew [fun n => _] ?p1 in _) k = _ ] =>
            set (eq1 := p1); simpl in eq1;
              rewrite (UIP_dec (Nat.eq_dec) eq1 eq_refl);
              simpl
          end.          
          match goal with
          | [|- (rew [fun n => _] ?p1 in _) k = _ ] =>
            set (eq2 := p1); simpl in eq2;
              rewrite (UIP_dec (Nat.eq_dec) eq2 eq_refl);
              simpl
          end.
          reflexivity.
      + intro i.
        apply (Fin.caseS' i); [ clear i | intro devil; inversion devil ].
        simpl.
        exact IHcontra.
      + intro i.
        eexists; split; [ apply Permutation_refl | ].
        apply IHco.
      + rewrite (UIP_dec (Nat.eq_dec) (contraArityOk (FS F1)) eq_refl).
        rewrite (UIP_dec (Nat.eq_dec) (coArityOk (FS F1)) eq_refl).
        reflexivity.
    - apply (InterLeft List.nil sigma1 sigma2 _ _ _ (Permutation_refl _) (Permutation_refl _)).
      apply InterRight.
      + apply (sigmaLeft _ (sigma1 :: sigma2 :: []) sigma2 sigma1 (perm_swap _ _ _) IHsigma1).
      + apply (sigmaLeft _ (sigma1 :: sigma2 :: []) sigma1 sigma2 (Permutation_refl _) IHsigma2).
  Qed.  
    
End SubtypeSystem.  
        
        
        

      
      
      
  
    
    
  
                