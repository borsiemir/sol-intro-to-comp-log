(** * Chapter 3: Definitional Equality and Propositional Equality *)

Require Import Base.
Require Import Omega.
Set Implicit Arguments.
Unset Strict Implicit.

(** * 3.1 Conversion Principle *)

Goal ~~True.
Proof.
  change (~True -> False).
  change (~(True -> False)).
  change (~~True).
  hnf.
  change (~~True).
  cbv.
  change (~~True).
  simpl.
  pattern True.
  pattern not at 2.
  hnf.
  exact (fun f => f I).
  Show Proof.
Qed.

Inductive demo (X : Type) (x : X) : Prop :=
  | demoI : demo x.

Goal demo plus.
Proof.
  unfold plus.
  unfold plus.
  fold plus.
  apply demoI.
Qed.

Goal demo (fun x : nat => x).
Proof.
  change (demo (fun y : nat => y)).
  change (demo (fun myname : nat => myname)).
  apply demoI.
Qed.

Section Demo.
  Variable n : nat.

  Goal demo (5+n+n).
  Proof.
    change (demo (2+3+n+n)).
    simpl.
    change (demo (10+n-5+n)).
    pattern n at 1.
    hnf.
    simpl.
    apply demoI.
  Qed.

  Variable X : Type.
  Variable f : X -> X -> X.

  Goal demo f.
  Proof.
    change (demo (fun x => f x)).
    cbv.
    change (demo (fun x y => f x y)).
    cbv.
    apply demoI.
  Qed.
  
End Demo.
  
(** * 3.2 Disjointness and Injectivity of Constructors *)

Goal false <> true.
Proof.
  intros A.
  change (if false then True else False).
  rewrite A.
  exact I.
Qed.

Lemma disjoint_O_S n :
  0 <> S n.
Proof.
  intros A.
  change (match 0 with 0 => False | _ => True end).
  rewrite A.
  exact I.
Qed.

Lemma injective_S x y :
  S x = S y -> x = y.
Proof.
  intros A.
  change (pred (S x) = pred (S y)).
  rewrite A.
  reflexivity.
Qed.

Goal forall x, S x <> 0.
Proof. intros x A. discriminate A. Qed.

Goal forall x y, S x = S y -> x = y.
Proof. intros x y A. injection A. auto. Qed.

(* Exercise 3.2.1 *)

Goal forall (X: Type) (x:X),
       Some x <> None.
Proof.
  intros X x H. change (match Some x with None => True | Some _ => False end).
  rewrite H. exact I. Qed.

Goal forall (X: Type) (x:X),
       Some x <> None.
Proof.
  intros X x H. discriminate H. Qed.  

Goal forall (X: Type) (x:X),
       Some x <> None.
Proof.
  intros X x. congruence. Qed.
  
Goal forall (X: Type) (x: X) (A: list X),
       x :: A <> nil.
Proof.
  intros X x A H. change (match x :: A with [] => True | _ :: _ => False end).
  rewrite H. exact I. Qed.

Goal forall (X: Type) (x: X) (A: list X),
       x :: A <> nil.
Proof.
  intros X x A H. discriminate H. Qed.

Goal forall (X: Type) (x: X) (A: list X),
       x :: A <> nil.
Proof.
  intros X x A. congruence. Qed.

(* Exercise 3.2.2 *)
Goal forall (X Y: Type) (x x' : X) (y y' : Y),
       (x,y) = (x',y') -> x=x' /\ y = y'.
Proof.
  intros X Y x x' y y' H. split.
  - injection H. auto.
  - injection H. auto.
Qed.

Goal forall (X Y: Type) (x x' : X) (y y' : Y),
       (x,y) = (x',y') -> x=x' /\ y = y'.
Proof.
  intros X Y x x' y y' H. split.
  - congruence.
  - congruence.
Qed.

Goal forall (X Y: Type) (x x' : X) (y y' : Y),
       (x,y) = (x',y') -> x=x' /\ y = y'.
Proof.
  intros X Y x x' y y' H. split.
  - change ( fst (x, y) = fst (x', y')). rewrite H. reflexivity.
  - change ( snd (x, y) = snd (x', y')). rewrite H. reflexivity.
Qed.

Goal forall (X : Type) (x x' : X) (A A' : list X),
       x::A = x'::A' -> x=x' /\ A = A'.
Proof.
  intros  X x x' A A' H. split.
  - injection H. auto.
  - injection H. auto.
Qed.
    
Goal forall (X : Type) (x x' : X) (A A' : list X),
       x::A = x'::A' -> x=x' /\ A = A'.
Proof.
  intros X x x' A A' H. split.
  - congruence.
  - congruence.
Qed.

Goal forall (X : Type) (x x' : X) (A A' : list X),
       x::A = x'::A' -> x=x' /\ A = A'.
Proof.
  intros X x x' A A' H; split.
  - change (hd x (x :: A) = hd x (x' :: A')). rewrite H. reflexivity.
  - change ( tl (x :: A) = tl (x :: A')). rewrite H. reflexivity.
Qed.  

(* Exercise 3.2.3 *)
Goal forall x, negb x <> x.
Proof.
  intros x. destruct x.
  - simpl. congruence.
  - simpl. congruence. Qed.

Goal forall x, S x <> x.
Proof.
  intros x. induction x.
  - congruence.
  - intros H. injection H. apply IHx. Qed.

Goal forall x y z, x + y = x + z -> y = z.
Proof.
  intros x y z H. induction x.
  - assumption.
  - apply IHx. simpl in H. congruence. Qed.

Goal forall x y : nat, x = y \/ x <> y.
Proof.
  induction x.
  - induction y.
    + left; reflexivity.
    + right; congruence.
  - induction y.
    + right; congruence.
    + destruct IHy.
      * right. rewrite H. induction y.
        { congruence. }
        { intros H1.  injection H1.  apply IHy. rewrite H. injection H1.
          intros H2. symmetry. assumption. } (* Basta con un auto *)
      * specialize (IHx y). destruct IHx.
        { left. f_equal. assumption. }
        { right. intro H1. injection H1. assumption. }
Qed.
        
(* Exercise 3.2.4 *)

Inductive Ls : Type :=
| ls : list Ls -> Ls.

Check ls [].

Check  ls [ls [ls []; ls []]; ls []]. (* [ [ [] ; [] ]; [] ] *)

Goal exists (X : Type) (f : list X -> X), forall A B, f A = f B -> A = B.
Proof.
  exists Ls. exists ls. intros A B H. injection H. auto. Qed.

(* Exercise 3.2.5 *)

Goal False <> True.
Proof.
  intros H. rewrite H. exact I. Qed.
    
(* Exercise 3.2.6 *)
Goal exists (f : nat -> nat -> nat) x,
       (fun x => f x x) <> f x.
Proof.
  exists plus. exists O. intro H. simpl in H. assert (2 = 1).
  {change ( (fun x : nat => x + x ) 1 = (fun m : nat => m) 1).
   rewrite H. reflexivity. }
  discriminate H0. Qed.
  
(** * 3.3 Leibniz Equality *)

Definition leibniz_eq (X : Type) (x y : X) : Prop :=
  forall p : X -> Prop, p x -> p y.

Notation "x == y" := (leibniz_eq x y) (at level 70, no associativity).

Lemma leibniz_refl X (x : X) :
  x == x.
Proof. hnf. auto. Qed.

Lemma leibniz_sym X (x y : X) :
  x == y -> y == x.
Proof.
  unfold leibniz_eq. intros A p.
  apply (A (fun z => p z -> p x)).
  auto.
Qed.

Lemma leibniz_agrees X (x y : X) :
  x == y <-> x = y.
Proof.
  split ; intros A.
  - apply (A (fun z => x=z)). reflexivity.
  - rewrite A. apply leibniz_refl.
Qed.

Lemma leibniz_rewrite X (x y : X) (p : X -> Prop) :
  x == y -> p y -> p x.
Proof. intros A. apply (leibniz_sym A). Qed.

Lemma leibniz_plus_assoc x y z :
  (x + y) + z == x + (y + z).
Proof.
  induction x ; simpl.
  - apply leibniz_refl.
  - pattern (x+y+z). apply (leibniz_rewrite IHx). apply leibniz_refl.
Qed.

(* Exercise 3.3.1 *)

Goal forall x, x + O == x. (* Unnamed_thm25 *)
Proof.
  induction x.
  - simpl. apply leibniz_refl.
  - simpl. pattern (x + O). apply (leibniz_rewrite IHx). apply leibniz_refl.
Qed.

Goal forall x y, x + S y == S (x + y). (* Unnamed_thm26 *)
Proof.
  intros x y; induction x.
  - simpl. apply leibniz_refl.
  - simpl. pattern (x + S y). apply (leibniz_rewrite IHx). apply leibniz_refl.
Qed.

Goal forall x y, x + y == y + x.
Proof.
  intros x y; induction x.
  - assert (y + O == y) as yO.
    { apply Unnamed_thm26. }
    simpl. pattern (y + O). apply (leibniz_rewrite yO). apply leibniz_refl.    
  - assert (y + S x == S (y + x)) as Sx.
    { apply Unnamed_thm27. }
    simpl. pattern (x + y). apply (leibniz_rewrite IHx). pattern (y + S x).
    apply (leibniz_rewrite Sx). apply leibniz_refl.
Qed.
    
(* Exercise 3.3.2 *)
Lemma leibniz_rewrite_lr X (x y : X) (p : X -> Prop) :
  x == y -> p y -> p x.
Proof.
  intros A. apply (A (fun z => p z -> p x)). auto. Qed.

Lemma leibniz_rewrite_rl X (x y : X) (p : X -> Prop) :
       x == y -> p x -> p y.
Proof.
  intros A. apply (A (fun z => p x -> p z)). auto. Qed.

(* Exercise 3.3.3 *)

Goal forall x y, demo (x + y + x = y).
Proof.
  intros x y.
  change (demo ((fun xO => (fun z => x + y + z = y) xO)x)).
  change (demo ((fun yO => (fun z => x + z + x = yO)yO)y)).
  change (demo ((fun z => x + z + x = z)y)).
  change (demo ((fun z => z + x = y)(x + y))).
  apply demoI.
Qed.

(* No se puede hacer con y + x porque realmente tenemos (x + y) + x, que 
no es convertible con x + (y + x), aunque se pueda probar que son iguales *)

(** * 3.4 By Name Specification of Implicit Arguments *)

About leibniz_sym.

Goal forall X (x y : X) (p : X -> Prop),
       x == y -> p y -> p x.
Proof.
  intros X x y p A.
  Check leibniz_sym A.
  Check leibniz_sym A (p:=p).
  Check @leibniz_sym X x y A p.
  Check @leibniz_sym _ _ _ A p.
  exact (leibniz_sym A (p:=p)).
  Show Proof.
Qed.

(** * 3.5 Local Definitions *)

Compute let x := 2 in x + x.
(* = 4 : nat *)

Compute let x := 2 in let x := x + x in x.
(* = 4 : nat *)

Compute let f := plus 3 in f 7.
(* = 10 : nat *)

Check let X := nat in (fun x : X => x) 2.
(* let X := nat in (fun x : X => x) 2
   : nat *)

(* This check is supposed to result in an error:
Check (fun X => (fun x : X => x) 2) nat.
*)

(** * 3.6 Proof of nat <> bool *)

Goal bool <> nat.
Proof.
  pose (p X := forall x y z : X, x=y \/ x=z \/ y=z).
  assert (H: ~p nat).
  { intros B. specialize (B 0 1 2). destruct B as [B|[B|B]] ; discriminate B. }
  intros A. apply H. rewrite <- A.
  intros [|] [|] [|] ; auto.
Qed.

(* Exercise 3.6.1 *)
Goal bool <> option bool.
Proof.
  pose (p X := forall x y z : X, x=y \/ x=z \/ y=z).
  assert (H: ~p (option bool)).
  { intros B. specialize (B (Some false) (Some true) None).
  destruct B as [B|[B|B]]; discriminate B. }
  intros A. apply H. rewrite <- A.
  intros [|] [|] [|] ; auto.
Qed.

Goal option bool <> prod bool bool.
Proof.
  pose (p X := forall x y z x': X, x=y \/ x=z \/ y=z \/ x=x' \/ y=x' \/ z=x' ).
  assert (H: ~p (prod bool bool)).
  { intros B. specialize (B (true, true) (true, false) (false, true) (false, false)).
  destruct B as [B|[B|[B|[B|[B|B]]]]]; discriminate B. }
  intros A. apply H. rewrite <- A.
  intros [[|]|] [[|]|] [[|]|] [[|]|]; tauto. Qed.
    
Goal bool <> False.
Proof.
  pose (p X := exists x : X, True).
  assert (~ p False) as B.
  { intro H. destruct H. assumption. }
  intro A. apply B. rewrite <- A. exists true. exact I.
Qed.

(** * 3.7 Cantor's Theorem *)

Definition surjective (X Y : Type) (f : X -> Y) : Prop := forall y, exists x, f x = y.

Lemma Cantor X :
  ~ exists f : X -> X -> Prop, surjective f.
Proof.
  intros [f A].
  pose (g x := ~ f x x).
  specialize (A g).
  destruct A as [x A].
  assert (H: ~ (g x <-> ~ g x)) by tauto.
  apply H. unfold g at 1. rewrite A. tauto.
Qed.

(* Exercise 3.7.1 *)

Goal ~ exists f : nat -> nat -> nat, surjective f.
Proof.
  intros [f A]. pose ( g x := S (f x x)). specialize (A g). destruct A as [x A].
  assert (forall y, y <> S y).
  { induction y.
    - congruence.
    - intro H. injection H. apply IHy. }
  assert (f x x <> g x).
  { unfold g. apply H. }
  apply H0. rewrite A. reflexivity. Qed.

Goal ~ exists f : bool -> bool -> bool, surjective f.
Proof.
  intros [f A]. pose (g x := negb (f x x)). specialize (A g). destruct A as [x A].
  assert ( forall y, y <> negb y).
  { intros [|]; intro H; discriminate H. }
  assert (f x x <> g x).
  { unfold g. apply H. }
  apply H0. rewrite A. reflexivity. Qed.
  
(* Exercise 3.7.2 *)

Lemma Cantor_generalized X Y :
  (exists N : Y -> Y, forall y, N y <> y) ->
  ~ exists f : X -> X -> Y, surjective f.
Proof.
  intros [N H] [f A]. pose (g x := N (f x x)). specialize (A g). destruct A as [x A].
  assert ( g x <> f x x) as H1.
  { unfold g. apply H. }
  apply H1. rewrite A. reflexivity. Qed.
  
(* Exercise 3.7.3 *)

Lemma Cantor_neq X Y (f : X -> X -> Y) (N : Y -> Y) :
 (forall y, N y <> y) -> exists h, forall x, f x <> h.
Proof.
  intros H. pose (g := fun x => N (f x x)). exists g. intros x H1.
  assert ( g x <> f x x).
  { unfold g. apply H. }
  apply H0. rewrite H1. reflexivity. Qed.

(* Exercise 3.7.4 *)

Definition injective (X Y : Type) (f : X -> Y) : Prop := forall x x' : X, f x = f x' -> x = x'.

Goal forall X Y : Type, forall f : X -> Y, (exists g : Y -> X, forall y, f (g y) = y) -> surjective f.
Proof.
  intros X Y f H. destruct H as [g H]. unfold surjective.
  intros y. exists (g y). apply H. Qed.

Goal forall X Y : Type, forall f : X -> Y, (exists g : Y -> X, forall x, g (f x) = x) -> injective f.
Proof.
  intros X Y f H. destruct H as [g H]. unfold injective.
  intros x x' H1. assert (g (f x) = x) as gfx. {apply H. }
  specialize (H x'). rewrite <- H; rewrite <- gfx. f_equal. assumption. Qed.

(* Exercise 3.7.5 *)

Goal forall X, ~ exists f : (X -> Prop) -> X, injective f.
Proof.
  intros X [f A].
  pose (p x := exists h, f h = x /\ ~ h x).
  assert (~ p (f p)) as npfp.
  { intros [h [H1 H2]]. apply H2. apply A in H1 as H3. rewrite H3. exists h. split;
    assumption. }
  assert (p (f p)) as pfp.
  { exists p. split; auto. }
  exact (npfp pfp).
Qed. 

(** * 3.8 Kaminski's Equation *)

Goal forall (f : bool -> bool) (x : bool), f (f (f x)) = f x.
Proof.
  intros f x.
  destruct x, (f true) eqn:A, (f false) eqn:B ; congruence.
Qed.

Lemma destruct_eqn_bool (p : bool -> Prop) (x : bool) :
  (x = true -> p true) -> (x = false -> p false) -> p x.
Proof. destruct x ; auto. Qed.

Goal forall (f : bool -> bool) (x : bool), f (f (f x)) = f x.
Proof.
  destruct x ;
  pattern (f true) ; apply destruct_eqn_bool ;
  pattern (f false) ; apply destruct_eqn_bool ;
  congruence.
Qed.

(* Exercise 3.8.1 *)

Goal forall (f g : bool -> bool) (x : bool), f (f (f (g x))) = f (g (g (g x))).
Proof.
  destruct x; destruct (g true) eqn: A1, (g false) eqn: A2,
  (f true) eqn: B1, (f false) eqn: B2; congruence. Qed.

(** * 3.9 Boolean Equality Tests *)

Fixpoint nat_eqb (x y : nat) : bool :=
  match x, y with
    | O, O => true
    | S x', S y' => nat_eqb x' y'
    | _, _ => false
  end.

Lemma nat_eqb_agrees x y :
  nat_eqb x y = true <-> x = y.
Proof.
  revert y.
  induction x ; intros [|y] ; split ; simpl ; intros A ; try congruence.
  - f_equal. apply IHx, A.
  - apply IHx. congruence.
Qed.

(* Exercise 3.9.1 *)

(* Definition bool_eqb (x y: bool) : bool :=
 (* ... *) *)

Definition bool_eqb (x y: bool) : bool :=
  match x, y with
    | true, true => true
    | false, false => true
    | _, _ => false
   end.

Lemma bool_eqb_agress x y :
  bool_eqb x y = true <-> x = y.
Proof.
  destruct x, y; split; try congruence. (* Auto lo soluciona directamente pero *)
  - reflexivity.                        (* no da informacion sobre la demostracion*)
  - intro H; destruct H. reflexivity.
  - intro H; destruct H. reflexivity.
  - reflexivity.
Qed.  
  
(* Exercise 3.9.2 *)

(* Fixpoint list_eqb (X: Type) (X_eqb: X -> X -> bool) (A B: list X) :=
 (* ... *)

Lemma list_eqb_agrees X (X_eqb : X -> X -> bool) (A B : list X) :
  (forall x y, X_eqb x y = true <-> x = y) ->
  (list_eqb X_eqb A B = true <-> A = B). *)

Fixpoint list_eqb (X: Type) (X_eqb: X -> X -> bool) (A B : list X) : bool :=
  match A, B with
    | [], [] => true
    | x :: A', y :: B' => andb (X_eqb x y) (list_eqb X_eqb A' B')
    | _, _ => false
end.

Lemma andb_desc :
  forall x y, andb x y = true -> x = true /\ y = true.
Proof.
  intros [|] [|]; tauto.
Qed.

Lemma list_eqb_agrees X (X_eqb : X -> X -> bool) (A B : list X) :
  (forall x y, X_eqb x y = true <-> x = y) ->
  (list_eqb X_eqb A B = true <-> A = B).
Proof.
  intro H. split.
  - revert B. induction A as [|a A']; destruct B as [|b B']; intro eqB;
    try reflexivity; try discriminate eqB. simpl in eqB.
    apply andb_desc in eqB as [eqBX eqBlist].
    apply H in eqBX. rewrite eqBX. f_equal. apply IHA'. assumption.
  - revert B. induction A as [|a A']; destruct B as [|b B']; intro AeqB;
    try reflexivity; try discriminate AeqB. simpl.
    assert (a = b) as aeqb.
    { change (hd a (a :: A') = hd a (b :: B')). rewrite AeqB.
    reflexivity. }
    apply H in aeqb. rewrite aeqb. simpl. apply IHA'.
    change ( tl (a :: A') = tl (b :: B')). rewrite AeqB. reflexivity.
Qed.    