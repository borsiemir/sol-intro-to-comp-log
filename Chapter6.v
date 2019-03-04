(** * Chapter 6: Sum and Sigma Types *)

Require Import Base.

(** * 6.1 Boolean Sums and Certifying Test *)

(* We must not override the Base definitions of this stuff,
   because otherwise Coq will complain when we use it!

Inductive sumbool (X Y : Prop) : Type :=
| left : X -> sumbool X Y
| right : Y -> sumbool X Y.


Arguments left {X} {Y} _.
Arguments right {X} {Y} _.


Notation "{ X } + { Y }" := (sumbool X Y).
*)

Definition min (x y : nat) : nat :=
  if le_dec x y then x else y.

Compute min 7 3.

Set Printing All.
Print min.
Unset Printing All.

Goal forall x y, (x <= y -> min x y = x) /\ (y <= x -> min x y = y).
Proof.
  intros x y. split ; intros A.
  - unfold min. destruct (le_dec x y) as [B|B].
    + reflexivity.
    + omega.
  - unfold min. destruct (le_dec x y) as [B|B].
    + omega.
    + reflexivity.
Qed.

Goal forall x y, (x <= y -> min x y = x) /\ (y <= x -> min x y = y).
Proof.
    intros x y. split ; intros A ; unfold min ; destruct (le_dec x y) ; omega.
Qed.

Check le_lt_dec.
Check le_ge_dec.
Check le_gt_dec.
Check lt_eq_lt_dec.

Set Printing All.
Check {True} + {False} + {False}.
Unset Printing All.

(* We must not override the Base definitions of this stuff,
   because otherwise Coq will complain when we use it!

Inductive sumor (X : Type) (Y : Prop) : Type :=
| inleft : X -> sumor X Y 
| inright : Y -> sumor X Y.

Notation "X + { Y }" := (sumor X Y). *)

(* Exercise 6.1.1 *)
Goal forall X Y : Prop, {X} + {Y} -> X \/ Y.
Proof.
  intros X Y [A|A].
  - left; assumption.
  - right; assumption.
Qed.



Goal forall X Y : Prop, X \/ Y -> {X} + {Y}.
  intros X Y H. (* destruct H. *) (* Para hacer el destruct estamos haciendo un match
de X \/ Y que es Prop a  {X} + {Y} que es Type. Eso no es posible por la elim restr.
*) Abort.

(* Exercise 6.1.2 *)
Goal forall x y, if le_dec x y then x <= y else ~ x <= y.
Proof.
  intros x y. destruct (le_dec x y) as [A|A]; assumption.
Qed.

Goal forall x y, if le_dec x y then x <= y else x > y.
Proof.
  intros x y. destruct (le_dec x y) as [A|A]; try assumption; try omega.
Qed.

(** * 6.2 - Inhabitation and Decidability *)

Inductive inhabited (X : Type) : Prop :=
| inhabits : X -> inhabited X.

Goal forall X : Prop, inhabited X <-> X.
Proof.
  split.
  - intros [A] ; exact A.
  - intros A. constructor. exact A.
Qed.

(* We must not override the Base definition of dec,
   because otherwise Coq will complain when we use it.

Definition dec (X : Prop) : Type := {X} + {~ X}.
*)

Check le_dec.

Definition dec2bool (X : Prop) (d : dec X) : bool :=
  if d then true else false.

Compute (dec2bool (le_dec 2 3)).

Definition True_dec : dec True := left I.

Definition False_dec : dec False := right (fun A => A).

(* Exercise 6.2.1 *)
Goal forall X : Type, X -> inhabited X.
Proof.
  intros X x. constructor. assumption. Qed.

Goal forall X : Type, inhabited X -> X.
  intros X A. (* destruct A. *) (* destruct A es un match de inhabited X que es una
prop, a X que es un type, por lo tanto no se puede hacer por elim restriction *)
  Abort.

(* Exercise 6.2.2 *)
Goal forall X Y: Prop, X \/ Y <-> inhabited ({X} + {Y}).
Proof.
  intros X Y; split.
  - intros [A|A]; constructor; auto. (* Ahora si se puede hacer el analisis de casos
sobre A \/ B porque inhabited ({X} + {Y} si es un Prop y no un Type *)
  - intros [[A|A]]; auto.
Qed.

(* Exercise 6.2.3 *)
Goal forall X: Prop, dec X -> X \/ ~ X.
Proof.
  intros X [A|A]; auto. Qed. (* dec X = {X} + {~X} *)

(** * 6.3 Writing Certifying Test *)

Definition impl_dec (X Y : Prop) : dec X -> dec Y -> dec (X -> Y).
  intros A [B|B].
  - left. auto.
  - destruct A as [A|A].
    + right. auto.
    + left. tauto.
Defined.

Check impl_dec (le_dec 3 2) False_dec.

Compute (dec2bool (impl_dec (le_dec 3 2) False_dec)).

Definition nat_eq_dec (x y : nat) : dec (x=y).
  revert y. induction x ; simpl ; intros [|y].
  - left. auto.
  - right. auto.
  - right. auto.
  - destruct (IHx y).
    + left. congruence.
    + right. congruence.
Defined.

Compute dec2bool (nat_eq_dec 3 3).

Goal forall x y : nat, dec (x=y).
Proof. unfold dec. decide equality. Qed.

Definition le_dec (x y : nat) : dec (x <= y).
  destruct (leb x y) eqn:A.
  - left. apply leb_iff. exact A.
  - right. intros B. apply leb_iff in B. congruence.
Defined.

Definition dec_prop_iff (X Y : Prop) : (X <-> Y) -> dec X -> dec Y.
  intros A [B|B].
  - left. tauto.
  - right. tauto.
Defined.

(* Exercise 6.3.1 *)
Goal forall X : Prop, inhabited X -> dec X.
Proof.
  intros X A. (* No se puede aplicar analisis por casos todavia porque inhabited X
es Prop y dec X es Type *) left. (* Ya si podemos *) destruct A. assumption. Qed.

Goal forall X : Prop, dec X -> dec (inhabited X).
Proof.
  intros X [A|A].
  - left. constructor. assumption.
  - right. intro H. destruct H. auto. Qed.

Goal forall X : Prop, dec (inhabited X) -> dec X.
Proof.
  intros X [A|A].
  - left. destruct A. assumption.
  - right. intro x. apply A. constructor. assumption. Qed.

(* Exercise 6.3.2 *)
Definition and_dec (X Y : Prop) : dec X -> dec Y -> dec (X /\ Y).
Proof.
  intros [A|A].
  - intros [B|B].
    + left. auto.
    + right. tauto.
  - intros _. right. tauto.
Qed.

Definition or_dec (X Y : Prop) : dec X -> dec Y -> dec (X \/ Y).
Proof.
  intros [A|A].
  - intros _. left. auto.
  - intros [B|B].
    + left. auto.
    + right. tauto.
Qed.

(* Exercise 6.3.3 *)
Goal forall x y: nat, {x < y} + {x = y} + {y < x}.
Proof.
  induction x; intros [|y].
  - left; right. reflexivity.
  - left; left. omega.
  - right. omega.
  - destruct (IHx y).
    + destruct s.
      * left; left. omega.
      * left; right.  f_equal. assumption.
    + right. omega.
Qed.

(* Exercise 6.3.4- Do it twice: Once with "decide equality", once without. *)
Goal forall x y: bool, {x = y} + {x <> y}.
Proof.
   decide equality. Qed.
  
Goal forall x y: bool, {x = y} + {x <> y}.
Proof.
  intros [|] [|].
  - left; reflexivity.
  - right; congruence.
  - right; congruence.
  - left; reflexivity.
Qed.

(* Exercise 6.3.5 *)
(* In Coq 8.5 the names are Nat.eqb for nat_eqb and Nat.eqb_eq for nat_eqb_agrees. *)
Print Nat.eqb.
Check Nat.eqb_eq.

(* Definition nat_eqb' (x y: nat) : bool :=
 (* ... *)


Lemma nat_eqb_agrees (x y: nat) :
  x = y <-> nat_eqb' x y = true.
Abort. *)

Definition nat_eqb' (x y: nat) : bool :=
  match nat_eq_dec x y with
    | left _ => true
    | right _ => false
  end.                  

Lemma nat_eqb_agrees (x y: nat) :
  x = y <-> nat_eqb' x y = true.
Proof.
  split; unfold nat_eqb'; intros H; destruct (nat_eq_dec x y) eqn:A.
  - reflexivity.
  - congruence.
  - exact e.
  - discriminate H.
Qed.

Definition nat_eq_dec' (x y: nat):
  dec (x = y).
  destruct (Nat.eqb x y) eqn:A.
  - left. apply Nat.eqb_eq in A.  exact A.
  - right. intros B. apply Nat.eqb_eq in B. congruence.
Defined.

(* Exercise 6.3.6 *)

Lemma leb_iff x y : leb x y = true <-> x <= y.
Proof.
  revert y; induction x; simpl; intros [|y]; split; try omega; try congruence.
  - intros H. apply IHx in H. omega.
  - intros H. apply IHx. omega.
Qed.

Definition le_dec' (x y: nat):
  dec (x <= y).
  revert y. induction x; simpl; intros [|y].
  - left. omega.
  - left. omega.
  - right. intro H. omega.
  - destruct (IHx y).
    + left. omega.
    + right. intro H. omega.
Qed.

(* Comparar *)

(* Exercise 6.3.7 *)
Definition listdec (X: Type) (eqX: forall x y: X, dec (x = y)):
  forall xs ys: list X, dec (xs = ys).
Proof.
  unfold dec. decide equality. apply eqX. Qed.

Definition listdec' (X: Type) (eqX: forall x y: X, dec (x = y)):
  forall xs ys: list X, dec (xs = ys).
  unfold dec. induction xs; intros [|b ys].
    - left; reflexivity.
    - right. intros H. discriminate H.
    - right. intros H. discriminate H.
    - destruct (IHxs ys); destruct (eqX a b).
      + left. congruence.
      + right. congruence.
      + right. congruence.
      + right. congruence.
Qed.

(* Exercise 6.3.8 *)
Definition bool2dec (X : Prop) (b : bool) : (X <-> b = true) -> dec X.
  intros [A B]. destruct b.
  - left. auto.
  - right. intros x. cut (false = true). { intro H; discriminate H. } exact (A x).
Defined.

(* Exercise 6.3.9 *)
Definition cas (X Y Z : Type) : (X * Y -> Z) -> X -> Y -> Z.
  intros f x y. Show Proof. exact (f (x,y)). Show Proof.
Defined.

Definition car (X Y Z : Type) : (X -> Y -> Z) -> X * Y -> Z.
  intros f [x y]. Show Proof. exact (f x y). Show Proof.
Defined.

Definition add : nat -> nat -> nat.
  fix f 1. Show Proof. intros x y. Show Proof. destruct x as [|x']. Show Proof.
  - exact y. Show Proof.
  - exact (S (f x' y)). Show Proof.
Defined.

(** * 6.5 Decidable Predicates *)

Definition decidable (X : Type) (p : X -> Prop) : Type := forall x, dec (p x).

Definition XM := forall (X : Prop), X \/ ~X.

Goal decidable (fun X : Prop => X \/ ~X) -> XM.
Proof. intros A X. destruct (A X) as [B|B] ; tauto. Qed.

(* Exercise 6.5.1 *)
Goal forall (X : Type) (p : X -> Prop) (f : X -> bool), (forall x, p x <-> f x = true) -> decidable p.
Proof.
  intros X p test A x. specialize (A x). destruct (test x).
  - left. tauto.
  - right. intro H. apply A in H. discriminate H. Qed.

(** * 6.6 Sigma Types *)

(* This overrides already defined names (from the Base library)
   which we shouldn't do, because if we do, we have two different things
   with the same name.

Inductive sig (X : Type) (p : X -> Prop) : Type :=
  exist : forall x : X, p x -> sig p.

 
Notation "{ x  |  p }" := (sig (fun x => p)).
Notation "{ x : X  |  p }" := (sig (fun x : X => p)).
*)

Definition double (x : nat) : { y | y = 2*x}.
  exists (2*x). reflexivity.
Defined.

Compute let (y,_) := double 4 in y.

Definition div2_cert (n : nat) : {k | n = 2*k} + {k | n = 2*k + 1}.
  induction n.
  - left. exists 0. reflexivity.
  - destruct IHn as [[k A]|[k A]].
    + right. exists k. omega.
    + left. exists (S k). omega.
Defined.

(* This overrides already defined names (from the Base library)
   which we shouldn't do, because if we do, we have two different things
   with the same name, which confuses Coq
Inductive sum (X Y : Type) :=
| inl : X -> sum X Y
| inr : Y -> sum X Y.

 
Notation "x + y" := (sum x y) : type_scope.
*)

Definition mod2 x := if div2_cert x then 0 else 1.

Definition div2 x := match div2_cert x with
                        | inl (exist _ k _) => k
                        | inr (exist _ k _) => k
                      end.

Goal forall x, x = 2 * div2 x + mod2 x.
Proof.
  intros x. unfold div2, mod2.
  destruct (div2_cert x) as [[k A]|[k A]] ; omega.
Qed.

(* Exercise 6.6.1 *)
Goal forall x, mod2 x <= 1.
Proof.
  intro x. unfold mod2. destruct (div2_cert x); simpl; omega. Qed.

(* Exercise 6.6.2 *)

Lemma Sigma_Skolem (X Y : Type) (p : X -> Y -> Prop) :
 (forall x, {y | p x y}) -> { f | forall x, p x (f x) }.
Proof.
  intros A. exists (fun x => let (k, proof) := A x in k). intro x.
  destruct (A x) as [y pxy]. exact pxy.
Qed.

(* Exercise 6.6.3 *)
Goal forall X (p : X -> Prop), {x | p x} -> exists x, p x.
Proof.
  intros X p [x px]. exists x. assumption. Qed.

(* No podemos hacer la otra direccion porque dependeria de un match de exists x, px
que es una prop a {x | p x} que es un type y no se pude por la elim restriction *)

(* Exercise 6.6.4 *)
Goal forall X: Type, forall (p: X -> Prop), (exists x, p x) <-> inhabited {x | p x}.
Proof.
  intros X p; split.
  - intros [x px]. constructor. exists x. assumption.
  - intros [[x px]]. exists x. assumption.
Qed.

(* Exercise 6.6.5 *)
Goal forall (X : Type) (p : X -> Prop), decidable p -> {f : X -> bool | forall x, p x <-> f x = true}.
Proof.
  intros X p A. unfold decidable in A. exists (fun x => dec2bool (A x)). intro x.
  split; intro H.
  -  unfold dec2bool. destruct (A x).
     + reflexivity.
     + congruence.
  - unfold dec2bool in H. destruct (A x).
    + assumption.
    + discriminate H.
Qed.

(* Exercise 6.6.6 *)
Definition div3_cert (n : nat) : {k | n = 3*k} + {k | n = 3*k + 1} + {k | n = 3*k + 2}.
  induction n.
  - left; left. exists O. omega.
  - destruct IHn as [A|[x A]]. destruct A as [[x A]|[x A]].
    + left; right. exists x. omega.
    + right. exists x. omega.
    + left; left. exists (S x). omega.
Qed.

(** * 6.7 Strong Truth Value Semantics *)

Definition b2P (x : bool) : Prop := if x then True else False.

Definition STVS : Type := forall X : Prop, {X=True} + {X=False}.

Definition TVS := forall X : Prop, X=True \/ X=False.

Goal STVS -> TVS.
Proof. intros stvs X. destruct (stvs X) ; subst X ; auto. Qed.

Section STVS.
Variable stvs : STVS.
Definition P2b (X : Prop) : bool := if stvs X then true else false.

Lemma P2bTrue : P2b True = true.
Proof.
    unfold P2b. destruct (stvs True) as [A|A].
    + reflexivity.
    + exfalso. rewrite <- A. exact I.
Qed.

Lemma P2bFalse : P2b False = false.
Proof.
  unfold P2b. destruct (stvs False) as [A|A].
  + exfalso. rewrite A. exact I.
  + reflexivity.
Qed.

Goal forall x : bool, P2b (b2P x) = x.
Proof. intros [|] ; simpl. exact P2bTrue. exact P2bFalse. Qed.

Goal forall X : Prop, b2P (P2b X) = X.
Proof.
  intros X. destruct (stvs X) ; subst X.
  - rewrite P2bTrue. reflexivity.
  - rewrite P2bFalse. reflexivity.
Qed.

End STVS.

Print P2b.

(* Exercise 6.7.1 *)
Goal forall x y: bool, b2P x = b2P y -> x = y.
Proof.
  intros [|] [|]; simpl; intro H; try congruence.
  - exfalso. rewrite <- H. exact I.
  - exfalso. rewrite H. exact I.
Qed.

(* Exercise 6.7.2 *)
Definition surjective (X Y: Type) (f: X -> Y):=
  forall y:Y, exists x: X, f x = y.
  
Goal TVS -> surjective b2P.
Proof.
  intros tvs y. specialize (tvs y) as [A|A].
  - exists true. auto.
  - exists false. auto.
Qed.

(* Exercise 6.7.3 *)
Goal forall A : STVS, forall X Y : Prop, P2b A X = P2b A Y -> X = Y.
Proof.
  intros stvs X Y. unfold P2b. destruct (stvs X), (stvs Y); subst.
  - auto.
  - intro H. discriminate H.
  - intro H. discriminate H.
  - auto.
Qed.

(* Exercise 6.7.4 *)
Goal STVS -> forall X : Prop, dec X.
Proof.
  intros stvs X. specialize (stvs X) as [A|A]; subst.
  - left. exact I.
  - right. intro x. destruct x. Qed.

(* Exercise 6.7.5 *)
Goal STVS -> forall (X : Type) (p : X -> Prop), decidable p.
Proof.
  intros stvs X p x. specialize (stvs (p x)) as [A|A].
  - rewrite A. left. exact I.
  - rewrite A. right. intro H. destruct H.
Qed.