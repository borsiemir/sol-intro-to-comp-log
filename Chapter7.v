(** * Chapter 7:  Inductive Predicates *)

Require Import Base.

(** * 7.1 Nonparametric Arguments and Linerization *)

Inductive zero : nat -> Prop :=
| zeroI : zero 0.

Lemma zero_iff x :
  zero x <-> x = 0.
Proof.
  split ; intros A.
  - destruct A. reflexivity.
  - subst x. constructor.
Qed.

Goal ~ zero 2.
Proof. intros A. remember 2 as x. destruct A. discriminate Heqx. Qed.

(* Exercise 7.1.1 *)
Goal zero 0.
Proof.
  exact zeroI.
Qed.

Goal ~ zero 7.
Proof.
  intros H. remember 7 as x. destruct H. discriminate Heqx. Qed.

Goal forall x, ~ zero (S x).
Proof.
  intros x H. remember (S x) as y. destruct H. discriminate Heqy. Qed.

(* Exercise 7.1.2 *)
Goal forall x, (zero x) + (~ zero x).
Proof.
  intros [|x].
  - left. constructor.
  - right. intro H. remember (S x) as y. destruct H. discriminate Heqy. Qed.

(* Exercise 7.1.3 *)
Lemma remember (X: Type) (p: X -> Type) (x: X):
  (forall y, y = x -> p y) -> p x.
Proof.
  intros H. apply H. reflexivity. Qed. (* Pensar *)

(* Justifica la tactica remember porque te permite cambiar un x ya conocido por un 
forall y, y = x donde al introducir ese y estaras igualando x ya conocido a una 
variable nueva desconocida llamada y, y ademas cambia las x del goal por y *)

Goal forall x, ~ zero (S x).
Proof.
  intros x. pattern (S x). apply remember. intros y H. intros zy. destruct zy.
  discriminate H. Qed.

(* Exercise 7.1.4 *)
Goal forall x, zero x <-> forall p: nat -> Prop, p 0 -> p x.
Proof.
  intros x; split; intro H.
  - destruct H. auto.
  - apply H. constructor. Qed.

(* Exericse 7.1.5 *)
(* Fixpoint zerob : nat -> bool :=
  (* ... *)

Goal forall x, zero x <-> zerob x = true. 
*)

Fixpoint zerob (n : nat) : bool :=
  match n with
    | O => true
    | _ => false
  end. (* No es necesario usar una funcion recursiva *)

Goal forall x, zero x <-> zerob x = true. 
Proof.
  intros x; split.
  - intros []. reflexivity.
  - destruct x.
    + intros _; constructor.
    + simpl. intro H. discriminate H. Qed.

(* Exercise 7.1.6 *)
(* Define leo.

Goal forall x, leo x <-> x <= 1. 

Characterize leo impredicatively and prove the correctness. 

Characterize leo with a boolean test leob: nat -> bool and prove the correctness of the characterization *)

Inductive leo : nat -> Prop :=
|  leo0 : leo O
|  leo1 : leo 1.

Goal forall x, leo x <-> x <= 1.
Proof.
  intros x; split.
  - intros []; omega.
  - intros H. cut (x = O \/ x = 1). { intros [A|A]; rewrite A; constructor. }
    omega.
Qed.    

(** * 7.2 Even *)

Inductive even : nat -> Prop :=
| evenO : even 0
| evenS x : even x -> even (S (S x)).

Lemma even_iff x :
  even x <-> exists k, x = 2*k.
Proof.
  split ; intros A.
  - induction A.
    + exists 0. reflexivity.
    + destruct IHA as [k IHA]. subst x. exists (S k). simpl. omega.
  - destruct A as [k A]. subst x. induction k ; simpl.
    + constructor.
    + replace (S(k+S(k+0))) with (S (S (2*k))) by omega.
      constructor. exact IHk.
Qed.

Goal ~ even 3.
Proof.
  intros A. remember 3 as x. destruct A.
  - discriminate Heqx.
  - destruct A ; discriminate Heqx.
Qed.

Lemma even_descent x :
  even (S (S x)) -> even x.
Proof.
  intros A. remember (S (S x)) as y.
  destruct A as [|y A].
  - discriminate Heqy.
  - congruence.
Qed.

(* Exericse 7.2.1 *)
Goal even 6.
Proof.
  apply evenS. apply evenS. apply evenS. apply evenO. Qed.

Goal ~ even 5.
Proof.
  intros H. remember 5 as x. destruct H.
  - discriminate Heqx.
  - destruct H.
    + discriminate Heqx.
    + destruct H; discriminate Heqx.
Qed.

(* Exercise 7.2.2 *)
Goal forall x y, even x -> even y -> even (x+y).
Proof.
  intros x y evx. induction evx; simpl.
  -  auto.
  - intro evy. apply evenS. apply IHevx. assumption.
Qed.
  
Goal forall x y, even x -> even (x+y) -> even y.
Proof.
  intros x y evx evxy. induction evx.
  - simpl in evxy. assumption.
  - apply IHevx. simpl in evxy. remember (S (S (x + y))) as z. destruct evxy.
    + discriminate Heqz.
    +  congruence. Qed.
Goal forall x, even x -> even (S x) -> False.
Proof.
  intros x evx evSx. induction evx.
  - remember 1 as x. destruct evSx; discriminate Heqx.
  - apply IHevx. remember (S (S (S x))) as y. destruct evSx.
    + discriminate Heqy.
    + congruence. Qed.

(* Exercise 7.2.3 *)
Lemma even_inv x : even x -> x = 0 \/ exists x', x = S (S x') /\ even x'.
Proof.
  intros evx; destruct evx.
  - left; reflexivity.
  - right. exists x. auto. Qed.

(* Exercise 7.2.4 *)
Goal forall x, even x <-> forall p : nat -> Prop, p 0 -> (forall y, p y -> p (S (S y))) -> p x.
Proof.
  intros x; split.
  - intros evx p pO H. induction evx.
    + assumption.
    + apply H. assumption.
  - intros H. apply H.
    + constructor.
    + intros y evy. exact (evenS evy).
Qed.

(* Exercise 7.2.5 *)
Lemma even_succ x : (~ even x -> even (S x)) /\ (~ even (S x) -> even x).
Proof.
  induction x; split.
  - intro H. exfalso. apply H. constructor.
  - intro H; constructor.
  - intros H. constructor. apply IHx. assumption.
  - intros H. apply IHx. intro H'. apply H. constructor. assumption. Qed.
    
(* Exercise 7.2.6 *)

(* Usando even_succ *)


Goal forall x, even x -> ~ even (S x).
Proof.
  induction x.
  - intros evO ev1. remember 1 as y. destruct ev1; discriminate Heqy.
  - intros H H'. apply IHx.
    + remember (S (S x)) as y. destruct H'.
      * discriminate Heqy.
      * congruence.
    + exact H.
Qed.

(* Exercise 7.2.7 *)
Goal forall x, {even x} + {~ even x}.
Proof.
  induction x.
  - left; constructor.
  - destruct IHx.
    + right. (* este es el teorema anterio, el cual no usa even_succ *)
      apply Unnamed_thm15; assumption.
    + left. apply even_succ in n. assumption. Qed.

(* Exercise 7.2.8 *)
Inductive even' (x : nat) : Prop :=
| even'O : x=0 -> even' x
| even'S y : even' y -> x = S (S y) -> even' x.

Goal ~ even' 3.
Proof.
  intros H. remember 3 as x. destruct H; subst.
  - discriminate H.
  - destruct H; subst; discriminate H0.
Qed.

Goal forall x, even' x <-> even x.
Proof.
  split; intros A; induction A; subst.
  - constructor.
  - constructor. assumption.
  - constructor. reflexivity.
  - remember (S (S x)) as y. revert Heqy. apply even'S. assumption. Qed.
     
(* Exercise 7.2.9 *)
Fixpoint evenb (x : nat) : bool :=
  match x with
    | 0 => true
    | S (S x') => evenb x'
    | _ => false
  end.

Lemma evenb_even x : (evenb x = true -> even x) /\ (evenb (S x) = true -> even (S x)).
Proof.
  induction x; split.
  - intros _. constructor.
  - simpl. intros H. discriminate H.
  - intros H. apply IHx. assumption.
  - simpl. intros H. constructor. apply IHx. assumption. Qed.


Goal forall x, even x <-> evenb x = true.
  split; intros A.
  - induction A.
    + reflexivity.
    + simpl. assumption.
  - apply evenb_even. assumption.
Qed.

(** * 7.3 Less or Equal *)

(* These definitions lead to name collisions with the Base library and thus have been commented: *)
(*Inductive le (x : nat) : nat -> Prop :=
| le_n : le x x
| le_S y : le x y -> le x (S y).


Notation "x <= y" := (le x y) (at level 70).
*)

Lemma le_iff x y :
  x <= y <-> exists k, k + x = y.
Proof.
  split.
  - intros A. induction A as [|y A].
    + exists 0. reflexivity.
    + destruct IHA as [k B]. exists (S k). simpl. congruence.
  - intros [k A]. subst y. induction k ; simpl.
    + constructor.
    + constructor. exact IHk.
Qed.

Lemma le_O x : 0 <= x.
Proof.
  induction x.
  - constructor.
  - constructor. exact IHx.
Qed.

Lemma le_SS x y : x <= y -> S x <= S y.
Proof.
  intros xy. induction xy.
  - constructor.
  - constructor. exact IHxy.
Qed.

Lemma le_Strans x y : S x <= y -> x <= y.
Proof.
  intros H. induction H.
  - constructor. constructor.
  - constructor. exact IHle.
Qed.

Lemma le_zero x :
  x <= 0 -> x = 0.
Proof.
  intros A. remember 0 as y. destruct A as [|y A].
  - reflexivity.
  - discriminate Heqy.
Qed.

Lemma le_SS' x y :
  S x <= S y -> x <= y.
Proof.
  intros A. remember (S y) as y'. induction A as [|y' A].
  - injection Heqy'. intros A. subst y. constructor.
  - injection Heqy'. intros B. subst y'. apply le_Strans, A.
Qed.

Definition le_dec x y : dec (x <= y).
  revert y. induction x ; intros y.
  - left. apply le_O.
  - destruct y.
    + right. intros A. apply le_zero in A. discriminate A.
    + destruct (IHx y) as [A|A].
      * left. apply le_SS, A.
      * right. intros B. apply A, le_SS', B.
Defined.

(* Exercise 7.3.2 *)
Lemma le_inv x y : x <= y -> x = y \/ exists y', y = S y' /\ x <= y'.
Proof.
  intros A. destruct A as [|k A].
  - left; reflexivity.
  - right. exists k. auto.
Qed.

(* Exercise 7.3.3 - Do not use omega. *)
Lemma le_trans x y z : x <= y -> y <= z -> x <= z.
Proof.
  intros A B. induction A.
  - exact B.
  - apply IHA, le_Strans, B.
Qed.

Lemma le_trans' x y z : x <= y -> y <= z -> x <= z.
Proof.
  intros A B. induction B.
  - exact A.
  - apply le_S, IHB. Qed.

(* Induciendo sobre y <= z no es necesario el lema le_Strans *)

(* Exericse 7.3.4 - Do not use omega. *)
Goal forall x y, S x <= y -> x <> y.
Proof.
  intros x y; revert x; induction y; intros x A.
  - intros B. apply le_zero in A. congruence.
  - intros B. apply le_SS' in A. rewrite B in A. apply IHy in A. congruence. Qed.

(* Exercise 7.3.5 - Do not use omega. *)
Goal forall x y, x <= y -> y <= x -> x=y.
Proof.
  induction x; intros y A B.
  - apply le_zero in B. congruence.
  - destruct y as [|y].
    + exfalso. apply le_zero in A. discriminate A.
    + f_equal. apply IHx.
      * apply le_SS' in A. exact A.
      * apply le_SS' in B. exact B.
Qed.

(* Exercise 7.3.6 - Do not use omega. *)
Goal forall x y, x <= y <-> leb x y = true.
Proof.
  induction x; split.
  - auto.
  - intros _. apply le_O.
  - intros A. destruct y as [|y].
    + exfalso. apply le_zero in A. discriminate A.
    + simpl. apply le_SS' in A. apply IHx, A.
  - intros A. destruct y.
    + discriminate A.
    + simpl in A. apply le_SS. apply IHx, A.
Qed.


(** * 7.4 Equality *)
(* We need to disable these definitions because of conflicts with Base definitions *)
(*
Inductive eq (X : Type) (x : X) : X -> Prop :=
| eq_refl : eq x x.


Notation "x = y" := (eq x y) (at level 70).
*)

Lemma Leibniz (X : Type) (x y : X) :
  x = y <-> forall p : X -> Prop, p x -> p y.
Proof.
  split ; intros A.
  - destruct A. auto.
  - apply (A (fun z => x = z)). constructor.
Qed.

(** * 7.5 Exceptions from the Elim Restriction *)

Definition cast (X : Type) (x y : X) (f : X -> Type) : x = y -> f x -> f y.
  intros A B. destruct A. exact B.
Defined.

Definition fin (n : nat) : Type := Nat.iter n option False.

Goal forall n, fin n -> fin (n+0).
Proof. intros n. apply cast. omega. Qed.

(* Exercise 7.5.1 *)
Goal forall X Y : Prop, X /\ Y -> prod X Y.
Proof.
  intros X Y [x y]. split; assumption. Qed.

(* El unico constructor de /\ es conj : X → Y → and X Y, donde los argumentos  son 
no-parametricos pero son demostraciones, asi que cumple las condiciones *)  

(* Exercise 7.5.2 *)

(* Inductive inhabited (X : Type) : Prop :=
| inhabits : X → inhabited X. Donde el primer argumento de inhabits es 
no-parametrico y no tiene porque ser una demostracion *)

(* Exercise 7.5.3 *)
Definition exfalso : False -> forall X: Type, X.
intro H. destruct H. Show Proof. Qed. (* Hace un match sobre false que cumple las
condiciones porque no tiene constructores *)

(* Exercise 7.5.4 *)
Goal forall (X : Type) (x y : X), (forall p : X -> Prop, p x -> p y) -> forall p : X -> Type, p x -> p y.
Proof.
  intros X x y A B. apply cast. apply (A (fun y =>  x = y)). reflexivity. Qed.

(** * 7.6 Safe and Nonuniform Parameters *)

Inductive safe (p : nat -> Prop) (n : nat) : Prop :=
| safeB : p n -> safe p n
| safeS : safe p (S n) -> safe p n.

Lemma safe_dclosed k n p :
  k <= n -> safe p n -> safe p k.
Proof.
  intros A B. induction A as [|n A].
  - exact B.
  - apply IHA. right. exact B.
Qed.

Lemma safe_iff p n :
  safe p n <-> exists k, n <= k /\ p k.
Proof.
  split ; intros A.
  - induction A as [n B|n A].
    + exists n. auto.
    + destruct IHA as [k [B C]].
      exists k. split. omega. exact C.
  - destruct A as [k [A B]].
    apply (safe_dclosed A). left. exact B.
Qed.

(* Exercise 7.6.1 *)
Inductive least (p : nat -> Prop) (n : nat) : nat -> Prop :=
| leastB : p n -> least p n n
| leastS k : ~ p n -> least p (S n) k -> least p n k.

Lemma least_correct1 p n k : least p n k -> p k.
Proof.
  intro A. induction A as [n A |n k A].
  - exact A.
  - exact IHA. Qed.

Lemma least_correct2 p n k : least p n k -> n <= k.
Proof.
  intro A. induction A as [n A|n k A].
  - constructor.
  - apply le_S, le_SS' in IHA. exact IHA. Qed.
  

Lemma least_correct3 p n k : least p n k -> forall k', n <= k' -> p k' -> k <= k'.
Proof.
  intros A m B C. induction A as [n A|n k A].
  -  exact B.
  - apply IHA. apply le_lt_eq_dec in B. destruct B.
    + auto.
    + rewrite <- e in C. exfalso. exact (A C). Qed.
 
Lemma least_correct4 p n k : (forall x, dec (p x)) -> p (n+k) -> exists k', least p n k'.
Proof.
  intro A; revert n; induction k; intros n B.
  - exists n. replace (n + 0) with n in B by auto. constructor. exact B.
  - replace (n + S k) with (S n + k) in B by omega. apply IHk in B as [x B].
    specialize (A n). destruct A as [A|A].
    + exists n. constructor. exact A.
    + exists x. constructor.
      * exact A.
      * exact B.
Qed.

Lemma least_correct p n k (p_dec : forall x, dec (p x)) :
  least p n k <-> p k /\ n <= k /\ forall k', n <= k' -> p k' -> k <= k'.
Proof.
  split.
  - intros H. split.
    + exact (least_correct1 H).
    + split.
      * exact (least_correct2 H).
      * exact (least_correct3 H).
  - intros [A [B C]]. apply le_iff in B as [x B]; rewrite plus_comm in B. subst.
    assert (exists k', least p n k') as [y H]. { apply (least_correct4 p_dec A). }
    cut (y = n + x). { intro B. rewrite <- B. exact H. }
    assert (p y) as py. apply least_correct1 in H; exact H.
    assert (n <= y) as leny. apply least_correct2 in H; exact H.
    specialize (C y). apply (C leny) in py.
    assert (y <= n + x) as B.
    { apply (least_correct3 H).
      - omega.
      - auto. }
    omega.
Qed.

(** * 7.7 Constructive Choice for Nat *)
Section First.
Variable p : nat -> Prop.
Variable p_dec : forall n, dec (p n).

Fixpoint first (n : nat) (A : safe p n) : {k | p k} :=
  match p_dec n with
    | left B => exist p n B
    | right B => first match A with
                        | safeB C => match B C with end
                        | safeS A' => A'
                      end
  end.

Lemma cc_nat : (exists x, p x) -> {x | p x}.
Proof.
  intros A. apply first with (n:=0).
  destruct A as [n A].
  apply safe_dclosed with (n:=n). omega. left. exact A.
Qed.

End First.

(* Exercise 7.7.1 Write a constructive choice function for bool. *)
Definition cc_bool (p : bool -> Prop) (p_dec : forall x, dec (p x)) : (exists x, p x) -> {x | p x}.
Proof.
  intros A. assert (dec (p true)) as B. apply p_dec. assert (dec (p false)) as C.
  apply p_dec. destruct B, C.
  + exists true; exact p0.
  + exists true; exact p0.
  + exists false; exact p0.
  + cut (forall x, ~ p x). { intro B. exfalso. destruct A as [x A]. specialize (B x).
    exact (B A). }
    intros x; destruct x; assumption.
Qed.

(* Exercise 7.7.2 *)
Section Second.

Variable p : nat -> Prop.
Variable p_dec : forall n, dec (p n).

Fixpoint first1 (n : nat) (A : safe p n) : {k | p k /\ k >= n}.
  destruct (p_dec n) as [B|B].
  - exists n. auto.
  - assert ({k : nat | p k /\ k >= S n}).
    { apply (first1 (S n)). destruct A as [A|A].
    + destruct (B A).
    +  exact A. }
    destruct H as [x [px C]]. exists x. split; auto. omega.
Defined.

Fixpoint first2 (n : nat) (A : safe p n) : {k | p k /\ k >= n /\ forall k', n <= k' -> p k' -> k <= k'}.
  destruct (p_dec n) as [B|B].
  - exists n. auto.
  - assert ({k : nat | p k /\ k >= S n /\ (forall k' : nat, S n <= k' -> p k' -> k <= k')}).
    { apply (first2 (S n)). destruct A as [A|A].
      + destruct (B A).
      + exact A. }
    destruct H as [x [C [D E]]]. exists x. split; auto; split; try omega.
    intros k H1 H2. destruct H1.
    + exfalso. exact (B H2).
    + apply E.
      * exact (le_SS H1).
      * exact H2.
Qed.
    
    
End Second.

(* Exercise 7.7.3 *)
Definition cc_fin (n : nat) (p : fin n -> Prop) (p_dec : forall x, dec (p x))
  : (exists x, p x) -> {x | p x}.
  induction n; intros A.
  - exfalso. destruct A. destruct x.
  - assert (dec(p None)) as [pNone|pNone] by auto.
    + exists None. exact pNone.
    + specialize (IHn (fun z => p (Some z))). simpl in IHn.
      assert (forall x, dec (p (Some x))) as decpSome by auto. apply IHn in decpSome.
      * destruct decpSome as [x pSomex]. exists (Some x). exact pSomex.
      * destruct A as [x A]. destruct x as [x|].
        { exists x. exact A. }
        { exfalso. exact (pNone A). }
Qed.

    
(** * 7.8 Technical Summary *)
Print least.

Check least.
Check leastB.
Check leastS.

(** * 7.9 Induction Lemmas *)
Print even.
Check even_ind.

Print le.
Check le_ind.

(* Exercise 7.9.1  Complete the following definitions of the induction lemmas for even and le.*)
(* Definition even_ind' (p : nat -> Prop) (r1 : p 0) (r2 : forall x, even x -> p x -> p (S (S x))) 
  : forall x, even x -> p x := (* ... *).

Definition le_ind' (x : nat) (p : nat -> Prop) (r1 : p x) (r2 : forall y, le x y -> p y -> p (S y))
  : forall y, le x y -> p y :=  (* ... *). *)

Definition even_ind' (p : nat -> Prop) (r1 : p 0) (r2 : forall x, even x -> p x -> p (S (S x))) 
  : forall x, even x -> p x := fix f x evx := match evx in (even x) return p x with
                                        | evenO => r1        
                                        | @evenS y evy => r2 y evy (f y evy)
                                        end.

Definition le_ind' (x : nat) (p : nat -> Prop) (r1 : p x) (r2 : forall y, le x y -> p y -> p (S y))
  : forall y, le x y -> p y := fix f y lexy := match lexy in (le _ y) return p y with
                                       | le_n _ => r1
                                       | @le_S _ z lexz => r2 z lexz (f z lexz)
                                       end.
