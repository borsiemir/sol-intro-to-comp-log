(** * Chapter 2: Propositions and proofs *)

Require Import Base.

(** * 2.2 Implication and Universal Quantification *)

Goal forall (X : Type) (x y : X), x=y -> y=x.
Proof. intros X x y A. rewrite A. reflexivity. Qed.

(* Exercise 2.2.1 *)

Goal forall x y, andb x y = true -> x = true.
Proof.
  intros x y H; destruct x.
  - reflexivity.
  - apply H.
Qed.

Goal forall X Y : Prop, X -> (X -> Y) -> Y.
Proof. intros X Y x A. exact (A x). Qed.

Goal forall X Y Z : Prop, (X -> Y) -> (Y -> Z) -> X -> Z.
Proof. intros X Y Z A B x. exact (B (A x)). Qed.

(* Exercise 2.2.2 *)
Goal forall (X: Prop) (x y z: X),
       x = y -> y = z -> x = z.
Proof.
  intros X x y z H1 H2. rewrite H1. rewrite H2. reflexivity.
Qed.

(** * 2.3 Predicates *)

Goal forall p q : nat -> Prop, p 7 -> (forall x, p x -> q x) -> q 7.
Proof. intros p q A B. exact (B 7 A). Qed.

(** * 2.4 The Apply Tactic *)

Goal forall X Y Z : Prop, (X -> Y) -> (Y -> Z) -> X -> Z.
Proof. intros X Y Z A B x. apply B. apply A. exact x. Qed.

Goal forall p q : nat -> Prop, p 7 -> (forall x, p x -> q x) -> q 7.
Proof. intros p q A B. apply B. exact A. Qed.

(* Exercise 2.4.1 *)

Goal forall X Y, (forall Z, (X -> Y -> Z) -> Z) -> X.
Proof.
  intros X Y H. apply H. intros x y. exact x.
Qed.

Goal forall X Y, (forall Z, (X -> Y -> Z) -> Z) -> Y.
Proof.
  intros X Y H. apply H. intros x y. exact y.
Qed.

(* Exercise 2.4.2 *)

Goal forall (p : bool -> Prop) (x : bool),
p true -> p false -> p x.
Proof.
  intros p x HT HF. destruct x.
  - exact HT.
  - exact HF.
Qed.

Goal forall (p : nat -> Prop) (x : nat),
p O -> (forall n, p n -> p (S n)) -> p x.
Proof.
  intros p x H0 HInd. induction x.
  - exact H0.
  - apply HInd. exact IHx. (* Se puede hacer solo con exact 
pero me parece menos legible *)
Qed.
  
Goal forall (X : Type) (p : list X -> Prop) (xs : list X),
p nil -> (forall x xs, p xs -> p (cons x xs)) -> p xs.
Proof.
  intros X p xs BH IndH. induction xs as [|x xs].
  - exact BH.
  - apply IndH. exact IHxs.
Qed.   

(** * Leibniz Characterization of Equality *)

Goal forall (X : Type) (x y : X),
(forall p : X -> Prop, p x -> p y) -> x=y.
Proof. intros X x y A. apply (A (fun z => x=z)). reflexivity. Qed.

(* Exercise 2.5.1 *)

Goal forall (X : Type) (x y : X),
x=y -> forall p : X -> Prop, p x -> p y.
Proof.
  intros X x y Heq p Hx. rewrite <- Heq. exact Hx. Qed.

Goal forall (X : Type) (x y : X),
(forall p : X -> Prop, p x -> p y) ->
forall p : X -> Prop, p y -> p x.
Proof.
  intros X x y HLeib p Hy. rewrite (HLeib (fun z => x = z )).
  - exact Hy.
  - reflexivity.
Qed.

(** * 2.6 Propositions are Types *)

(* Exercise 2.6.1 *)

Goal forall X : Type,
(fun x : X => x) = (fun y : X => y).
Proof.
  intros X. reflexivity.
Qed.

Goal forall X Y : Prop,
(X -> Y) -> forall x : X, Y.
Proof.
  intros X Y H x. exact (H x).
Qed.

Goal forall X Y : Prop,
(forall x : X, Y) -> X -> Y.
Proof.
  intros X Y H x. exact (H x).
Qed.

Goal forall X Y : Prop,
(X -> Y) = (forall x : X, Y).
Proof.
  intros X Y. reflexivity.
Qed.
  
(** * 2.7 Falsity and Negation *)

Goal False -> 2=3.
Proof. intros A. contradiction A. Qed.

Goal forall X : Prop, X -> ~~ X.
Proof. intros X x A. exact (A x). Qed.

Goal forall X : Prop,
(X -> ~ X) -> (~ X -> X) -> False.
Proof.
  intros X A B. apply A.
  - apply B. intros x. exact (A x x).
  - apply B. intros x. exact (A x x).
Qed.

Goal forall X : Prop,
~~ X -> (X -> ~ X) -> X.
Proof.
  intros X A B. exfalso. apply A. intros x. exact (B x x).
Qed.

(* Exercise 2.7.1 *)

Goal forall X : Prop, ~~~ X -> ~ X.
Proof.
  intros X H HX. apply H. intros HnX. exact (HnX HX). 
Qed.

Goal forall X Y : Prop, (X -> Y) -> ~ Y -> ~ X.
Proof.
  intros X Y HXY HnY HX. apply HnY. exact (HXY HX).
Qed.

(* Exercise 2.7.2 *)

Goal forall X : Prop, ~~ (~~ X -> X).
Proof.
  intros X H. apply H. intros nnx. exfalso. apply nnx. intro x.
  apply H. intro H1; exact x.
Qed.

Goal forall X Y : Prop, ~~ (((X -> Y) -> X) -> X).
Proof.
  intros X Y H. apply H. intros xyx. apply xyx. intros x. exfalso. apply H.
  intros H1; exact x.
Qed.

(* Exercise 2.7.3 *)

Goal forall X:Prop,
(X -> False) -> (~ X -> False) -> False.
Proof.
   exact (fun (X:Prop) (p: X -> False) (q: ~ X -> False) => q p).
Qed.

(** * 2.8 Conjunction and Disjunction *)

Goal forall X Y : Prop, X /\ Y -> Y /\ X.
Proof.
  intros X Y A. destruct A as [x y]. split.
  - exact y.
  - exact x.
Qed.

Goal forall X Y : Prop, X \/ Y -> Y \/ X.
Proof.
  intros X Y A. destruct A as [x|y].
  - right. exact x.
  - left. exact y.
Qed.

Goal forall X Y : Prop, X /\ Y -> Y /\ X.
Proof.
  intros X Y [x y]. split.
  - exact y.
  - exact x.
Qed.

Goal forall X Y : Prop, X \/ Y -> Y \/ X.
Proof.
  intros X Y [x|y].
  - right. exact x.
  - left. exact y.
Qed.

Goal forall X Y Z : Prop,
X \/ (Y /\ Z) -> (X \/ Y) /\ (X \/ Z).
Proof.
  intros X Y Z [x|[y z]].
  - split; left; exact x.
  - split; right.
    + exact y.
    + exact z.
Qed.

(* Exercise 2.8.1 *)

Goal forall X : Prop,
~ (X \/ ~ X) -> X \/ ~ X.
Proof.
  intros X H. right. intro x. apply H. left. exact x.
Qed.

Goal forall X : Prop,
(X \/ ~ X -> ~ (X \/ ~ X)) -> X \/ ~ X.
Proof.
  intros X H. right. intro x. apply H.
  - left; exact x.
  - left; exact x.
Qed.

Goal forall X Y Z W : Prop,
(X -> Y) \/ (X -> Z) -> (Y -> W) /\ (Z -> W) -> X -> W.
Proof.
  intros X Y Z W [xy | xz] [yw zw] x.
  - exact (yw (xy x)).
  - exact (zw (xz x)).
Qed.

(* Exercise 2.8.2 *)

Goal forall X : Prop, ~~ (X \/ ~ X).
Proof.
  intros X nExM. apply nExM. right. (* ExM = excluded middle *)
  intros x. apply nExM. left; exact x. 
Qed.

Goal forall X Y : Prop, ~~ ((X -> Y) -> ~ X \/ Y).
Proof.
  intros X Y H. apply H. intros xy. left. intros x.
  apply H. intro xy'; right. exact (xy x).
Qed.

(** * 2.9 Equivalence and Rewriting *)

Lemma and_com : forall X Y : Prop, X /\ Y <-> Y /\ X.
Proof.
  intros X Y. split.
  - intros [x y]. split.
    + exact y.
    + exact x.
  - intros [y x]. split.
    + exact x.
    + exact y.
Qed.

Lemma deMorgan : forall X Y : Prop, ~ (X \/ Y) <-> ~ X /\ ~ Y.
Proof.
  intros X Y. split.
  - intros A. split.
    + intros x. apply A. left. exact x.
    + intros y. apply A. right. exact y.
  - intros [A B] [x|y].
    + exact (A x).
    + exact (B y).
Qed.

Goal forall X Y Z W : Prop, (X <-> Y) -> (Z <-> W) -> (X /\ Z <-> Y /\ W).
Proof.
  intros X Y Z W xy zw; split.
  - intros [x z]; split.
    + apply xy. exact x.
    + apply zw. exact z.
  - intros [y w]; split.
    + apply xy. exact y.
    + apply zw. exact w.
Qed.

(* Allows us to use setoid-rewriting *)
Require Import Setoid.

Goal forall X Y Z : Prop, ~ (X \/ Y) /\ Z <-> Z /\ ~ X /\ ~ Y.
Proof.
 intros X Y Z.
 setoid_rewrite deMorgan.
 apply and_com.
Qed.

Goal forall X : Type, forall p q : X -> Prop, (forall x, ~ (p x \/ q x)) -> forall x, ~ p x /\ ~ q x.
Proof.
 intros X p q A.
 setoid_rewrite <- deMorgan.
 exact A.
Qed.

Goal forall X : Prop, X <-> X.
Proof. reflexivity. Qed.

Goal forall X Y : Prop, (X <-> Y) -> (Y <-> X).
Proof. intros X Y A. symmetry. exact A. Qed.

Goal forall X Y Z : Prop, (X <-> Y) -> (Y <-> Z) -> (X <-> Z).
Proof.
 intros X Y Z A B. transitivity Y.
 - exact A.
 - exact B.
Qed.

(* Exercise 2.9.1 *)

Goal forall X : Prop, X <-> X.
Proof.
  intros X; split.
  - intros x. exact x.
  - intros x. exact x.
Qed.

Goal forall X Y : Prop, (X <-> Y) -> (Y <-> X).
Proof.
  intros X Y xy; split.
  - intros y. apply xy. exact y.
  - intros x. apply xy. exact x.
Qed.

Goal forall X Y Z : Prop, (X <-> Y) -> (Y <-> Z) -> (X <-> Z).
Proof.
  intros X Y Z xy yz; split.
  - intros x. apply yz. apply xy. exact x.
  - intros z. apply xy. apply yz. exact z.
Qed.

(* Exercise 2.9.2 *)

Goal forall (X Y Z W : Prop), (X <-> Y) -> (Z <-> W) -> (X /\ Z <-> Y /\ W).
Proof.
  intros X Y Z W xy zw; split.
  - intros [x z]; split.
    + apply xy. exact x.
    + apply zw. exact z.
  - intros [y w]; split.
    + apply xy. exact y.
    + apply zw. exact w.
Qed.

Goal forall (X:Type) (p q:X -> Prop), (forall x:X, p x <-> q x) -> ((forall x:X, p x) <-> forall x:X, q x).
Proof.
  intros X p q pq; split.
  - intros Hp x. apply pq. apply Hp.
  - intros Hq x. apply pq. apply Hq.
Qed.

(* Exercise 2.9.3 *)

Goal forall X Y Z : Prop, X /\ ~ (Y \/ Z) <-> (~ Y /\ ~ Z) /\ X.
Proof.
  intros X Y Z. setoid_rewrite deMorgan. setoid_rewrite and_com at 2. reflexivity.
Qed.

Goal forall X : Type, forall p q : X -> Prop, (forall x, ~ (p x \/ q x)) <-> forall x, ~ p x /\ ~ q x.
Proof.
  intros X p q. setoid_rewrite deMorgan. reflexivity.
Qed.

(* Exercise 2.9.4 *)

Goal forall X Y : Prop, X /\ (X \/ Y) <-> X.
Proof.
  intros X Y; split.
  - intros [x xy]. exact x.
  - intro x; split.
    + exact x.
    + left; exact x.
Qed.

Goal forall X Y : Prop, X \/ (X /\ Y) <-> X.
Proof.
  intros X Y; split.
  - intros [x | [x y]].
    + exact x.
    + exact x.
  - intros x. left. exact x.
Qed.

Goal forall X:Prop, (X -> ~ X) -> X <-> ~~ X.
Proof.
  intros X xnx. split. (* Se puede con exfalso directamente? *)
  - intros x nx. exact (xnx x x).
  - intro nnx. exfalso. apply nnx. intro x. exact ((xnx x) x).
Qed.

(* Exercise 2.9.5 *)

Goal False <-> forall Z : Prop, Z.
Proof.
  split.
  - intro F. contradiction F.
  - intro Z. apply Z.
Qed.
    
Goal forall X : Prop,
~ X <-> forall Z : Prop, X -> Z.
Proof.
  split.
  - intros nx Z x. exfalso. apply nx. exact x.
  - intros Z x. apply Z. exact x.
Qed.

Goal forall X Y : Prop, X /\ Y <-> forall Z : Prop, (X -> Y -> Z) -> Z.
Proof.
  intros X Y. split.
  - intros [x y] Z xyz. exact (xyz x y).
  - intros Z; split.
    + apply Z. intros x y. exact x.
    + apply Z. intros x y. exact y.
Qed.

Goal forall X Y : Prop, X \/ Y <-> forall Z : Prop, (X -> Z) -> (Y -> Z) -> Z.
Proof.
  intros X Y. split.
  - intros [x | y].
    + intros Z xz yz. exact (xz x).
    + intros Z xz yz. exact (yz y).
  - intros H. apply H.
    + intros x. left. exact x.
    + intros y. right. exact y.
Qed.

Goal forall (X : Type) (x y : X), x=y <-> forall p : X -> Prop, p x -> p y.
Proof.
  intros X x y. split. (* This is thanks to Leibniz equality *)
  - intros xeqy p px. rewrite <- xeqy. exact px.
  - intros HLeib. apply (HLeib (fun z => x = z)). reflexivity.
Qed.

(** * 2.10 Automation Tactics *)

Goal forall X Y : Prop, X /\ Y -> Y /\ X.
Proof. intros X Y [x y]. split ; assumption. Qed.

Goal forall (X : Type) (p : list X -> Prop) (xs : list X),
p nil -> (forall x xs, p xs -> p (cons x xs)) -> p xs.
Proof. induction xs ; auto. Qed.

Goal forall X : Prop, ~ (X <-> ~ X).
Proof. tauto. Qed.

(** * 2.11 Existential Quantification *)

Goal forall (X : Type) (p q : X -> Prop),
    (exists x, p x /\ q x) -> exists x, p x.
Proof.
  intros X p q A. destruct A as [x B]. destruct B as [C _].
  exists x. exact C.
Qed.

Definition diagonal : Prop := forall (X : Type) (p : X -> X -> Prop),
~ exists x, forall y, p x y <-> ~ p y y.

Lemma circuit (X : Prop) : ~ (X <-> ~ X).
Proof. tauto. Qed.

Goal diagonal.
Proof. intros X p [x A]. apply (@circuit (p x x)). exact (A x). Qed.

Goal diagonal.
Proof. intros X p [x A]. specialize (A x). tauto. Qed.

Goal forall (X : Type) (x y : X),
    x <> y <-> exists p : X -> Prop, p x /\ ~ p y.
Proof.
  split.
  - intros A. exists (fun z => x = z). auto.
  - intros [p [A B]] C. apply B. rewrite <- C. apply A.
Qed.

(* Exercise 2.11.1 *)

Goal forall (X : Type) (p : X -> Prop),
~ (exists x, p x) <-> forall x, ~ p x.
Proof.
  intros X p; split.
  - intros H x px. apply H. exists x; exact px.
  - intros Hnp [x px]. specialize (Hnp x). exact (Hnp px).
Qed.

(* Exercise 2.11.2 *)

Goal forall (X Y : Type) (p : X -> Y -> Prop),
(exists x, exists y, p x y) <-> exists y, exists x, p x y.
Proof.
  intros X Y p. split.
  - intros [x [y pxy]]. exists y. exists x. exact pxy.
  - intros [y [x pxy]]. exists x. exists y. exact pxy.
Qed.

(* Exercise 2.11.3 *)

Goal forall (X : Type) (p : X -> Prop),
(exists x, p x) <-> forall Z : Prop, (forall x, p x -> Z) -> Z.
Proof.
  intros X p; split.
  - intros [x px] Z H. specialize (H x). exact (H px).
  - intros H. apply H. intros x px. exists x; exact px.
Qed.

(* Exercise 2.11.4 *)

Goal forall (X : Type) (x y : X),
x = y <-> forall r : X -> X -> Prop, (forall z : X, r z z) -> r x y.
Proof.
  intros X x y; split.
  - intros xeqy r H. rewrite xeqy. apply H.
  - intros H. apply H. intro z. reflexivity.
Qed.

Goal forall (X : Type) (x y : X),
x <> y <-> exists r : X -> X -> Prop, (forall z : X, r z z) /\ ~ r x y.
Proof.
  intros X x y; split.
  - intros xneqy. exists eq. auto.
  - intros [r [H1 H2]]. intros xeqy. apply H2. rewrite xeqy. apply H1.
Qed.
    
(* Exercise 2.11.5 *)

Goal forall (X: Type) (x : X) (p : X -> Prop), exists q : X -> Prop,
q x /\ (forall y, p y -> q y) /\ forall y, q y -> p y \/ x = y.
Proof.
  intros X x p. exists (fun z => (eq x z) \/ p z). split.
  - left. reflexivity.
  - split.
    + intros y py. right. exact py.
    + intros y. intros [H1 | H2].
      * right. apply H1.
      * left. apply H2.
Qed.  

(* Exercise 2.11.6 *)

Goal forall (X : Type) (Y : Prop) ,
X -> Y <-> (exists x : X, True) -> Y.
Proof.
  intros X Y. intros x H. apply H. exists x. reflexivity.
Qed.

(* Falta apartado b *)

(* Falta ejercicio 2.12.1 *)

(** * 2.13 Proof Rules as Lemmas *)

Lemma AndI (X Y : Prop) :
  X -> Y -> X /\ Y.
Proof. tauto. Qed.

Lemma AndE (X Y U : Prop) :
  X /\ Y -> (X -> Y -> U) -> U.
Proof. tauto. Qed.

Goal forall X Y : Prop, X /\ Y -> Y /\ X.
Proof.
  intros X Y A. apply (AndE A).
  intros x y. apply AndI.
  - exact y.
  - exact x.
Qed.

Lemma ExI (X : Type) (p : X -> Prop) :
  forall x : X, p x -> exists x, p x.
Proof. intros x A. exists x. exact A. Qed.

Lemma ExE (X : Type) (p : X -> Prop) (U : Prop) :
  (exists x, p x) -> (forall x, p x -> U) -> U.
Proof. intros [x A] B. exact (B x A). Qed.

Goal forall (X : Type) (p q : X -> Prop),
    (exists x, p x /\ q x) -> exists x, p x.
Proof.
  intros X p q A. apply (ExE A).
  intros x B. apply (AndE B). intros C _.
  exact (ExI C).
Qed.

(* Exercise 2.13.1 *)

(* Lemma OrI_L (* ... *)

Lemma OrI_R (* ... *)

Lemma OrE (* ... *) *)

Lemma OrI_L (X Y : Prop) :
  X -> X \/ Y.
Proof.
  intro x. left. exact x.
Qed.

Lemma OrI_R (X Y : Prop) :
  Y -> X \/ Y.
Proof.
  intro y. right. exact y.
Qed.

Lemma OrE (X Y : Prop) :
  forall Z : Prop,
    (X \/ Y) -> (X -> Z) -> (Y -> Z) -> Z.
Proof.
  intros Z [x | y] H1 H2.
  - exact (H1 x).
  - exact (H2 y).
Qed.
    
Goal forall X Y: Prop, X \/ Y <-> Y \/ X.
Proof.
  intros X Y; split.
  - intro xy. apply (OrE xy).
    + intro x. apply OrI_R. exact x.
    + intro y. apply OrI_L. exact y.
  - intro yx. apply (OrE yx).
    + intro y. apply OrI_R. exact y.
    + intro x. apply OrI_L. exact x.
Qed.

(** * 2.14 Inductive Propositions *)

Inductive True : Prop :=
  | I : True.

Inductive False : Prop := .

Goal forall x y : True, x=y.
Proof. intros x y. destruct x. destruct y. reflexivity. Qed.

Goal forall X : Prop, False -> X.
Proof. intros X A. destruct A. Qed.

(* Esto ya esta definido, tenerlo sobrescribe y da problemas
Inductive and (X Y : Prop) : Prop :=
  | conj : X -> Y -> and X Y.

Inductive or (X Y : Prop) : Prop :=
  | or_introl : X -> or X Y
  | or_intror : Y -> or X Y.

Inductive ex (X : Type) (p : X -> Prop) : Prop :=
  | ex_intro : forall x : X, p x -> ex p.

Definition not (X : Prop) : Prop := X -> False.

Definition iff (X Y : Prop) : Prop := (X -> Y) /\ (Y -> X).
*)

(* Exercise 2.14.1 *)
Goal forall X Y: Prop, X \/ Y <-> Y \/ X.
Proof.
  intros X Y; split.
  - intros [x | y].
    + exact (or_intror x).
    + exact (or_introl y).
  - intros [y | x].
    + exact (or_intror y).
    + exact (or_introl x).
Qed.

(* Faltan ejercicios 2.14.2, 2.14.3 *)

(** * 2.15 An Observation *)

Definition AND (X Y : Prop) : Prop :=
  forall Z : Prop, (X -> Y -> Z) -> Z.

Lemma ANDI (X Y : Prop) :
  X -> Y -> AND X Y.
Proof. intros x y Z. auto. Qed.

Lemma ANDE (X Y Z: Prop) :
  AND X Y -> (X -> Y -> Z) -> Z.
Proof. intros A. exact (A Z). Qed.

Lemma AND_agree (X Y : Prop) :
  AND X Y <-> X /\ Y.
Proof.
  split.
  - intros A. apply A. auto.
  - intros [x y] Z A. apply A ; assumption.
Qed.

(** * 2.16 Excluded Middle *)

Definition XM : Prop := forall X : Prop, X \/ ~ X.

(* Exercise 2.16.1 *)

Goal forall X Y : Prop,
       XM -> ~ (X /\ Y) -> ~ X \/ ~ Y.
Abort.

Goal forall (X : Type) (p : X -> Prop),
XM -> ~ (forall x, p x) -> exists x, ~ p x.
Abort.

(* Exercise 2.16.2 *)

Definition DN : Prop := forall X : Prop, ~~ X -> X. (* double negation *)
Definition CP : Prop := forall X Y : Prop, (~ Y -> ~ X) -> X -> Y. (* contraposition *)
Definition Peirce : Prop := forall X Y : Prop, ((X -> Y) -> X) -> X. (* Peirce's Law *)

Goal XM -> DN.
Abort.

Goal DN -> CP.
Abort.

Goal CP -> Peirce.
Abort.

(* Exercise 2.16.3 *)

Lemma drinker (X : Type) (d : X -> Prop) :
XM -> (exists x : X, True) -> exists x, d x -> forall x, d x.
Abort.

(* Exercise 2.16.4 *)

Goal forall X : Prop,
~~ (X \/ ~ X).
Abort.

Goal forall X Y : Prop,
~~ (((X -> Y) -> X) -> X).
Abort.

Goal forall X Y : Prop,
~~ (~ (X /\ Y) <-> ~ X \/ ~ Y).
Abort.

Goal forall X Y : Prop,
~~ ((X -> Y) <-> (~ Y -> ~ X)).
Abort.

(* Exercise 2.16.5 *)

Definition pdec (s: Prop) := s \/ ~ s.

Goal pdec (forall X: Prop, ~ (X \/ ~ X)).
Abort.

Goal pdec (exists X: Prop, ~ (X \/ ~X)).
Abort.

Goal pdec (forall P: Prop, exists f: Prop -> Prop, forall X Y: Prop,
                                 (X /\ P -> Y) <-> (X -> f Y)).
Abort.

Goal pdec (forall P:Prop, exists f: Prop -> Prop, forall X Y: Prop,
                                (X -> Y /\ P) <-> (f X -> Y)).
Abort.

