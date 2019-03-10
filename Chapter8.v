(** * Chapter 8 - Lists *)

Require Export Base.

(** * 8.1 Constructors and Notation *)

(* Commented because of naming conflicts with the Base library: 
 
Inductive list (X : Type) : Type :=
| nil : list X
| cons : X -> list X -> list X.

Notation "x '::' A" := (cons x A) (at level 60).
*)

Check list.
Check nil.
Check cons.

Goal forall (X: Type) (x: X) (A: list X), cons x A = x :: A.
Proof. reflexivity. Qed.

Goal forall (X: Type) (x y: X) (A: list X), cons x (cons y A) = x :: y :: A.
Proof. reflexivity. Qed.

(** * 8.2 Recursion and Induction *)

(* Commented because of naming conflicts with the Base library:
Fixpoint length (X: Type) (A: list X) :=
  match A with
    | => 0
    |x :: A => S (length A)
  end.
    
Notation "| A |" := (length A) (at level 65). 

Fixpoint app (X: Type) (A B: list X) :=
  match A with
    | => B
    |x :: A => x :: (app A B)
  end.

Notation "| A ++ B |" := (app A B) (at level 70). 

Fixpoint rev (X: Type) (A: list X) :=
  match A with
    | => 
    |x :: A => rev A ++ x
  end.

Fixpoint map (X Y: Type) (f: X -> Y) (A: list X) :=
  match A with
    | => 
    |x :: A => f x :: map f A
  end.

Fixpoint list_prod (X Y: Type) (A: list X) (B: list Y) :=
  match A with
    | => 
    |a :: A => map (pair a) B ++ (list_prod A B)
  end. *)

Compute (list_prod [1;2] [5;6;7]).

Goal forall (X: Type) (A B: list X), |A ++ B| = |A| + |B|.
Proof.
  intros X A B. induction A as [|x A IHA].
  - reflexivity.
  - simpl. rewrite IHA. reflexivity.
Qed.

(* Exercise 8.2.2 *)

Lemma list_cycle (X : Type) (A : list X) x :
  x::A <> A.
Proof.
  intros H. induction A as [|a A].
  - discriminate H.
  - apply IHA. injection H. intros H1 H2. subst. exact H1.
Qed.

(* Exercise 8.2.3 *)

Section Ex23.
  Variable X Y: Type.
  Variable x: X.
  Variable A B C: list X.
  Variable f: X -> Y.

  Lemma app_nil_r:
    A ++ nil = A.
  Proof.
    induction A.
    - reflexivity.
    - simpl. f_equal. exact IHl. Qed.

  Lemma app_assoc:
    A ++ (B ++ C) = (A ++ B) ++ C.
  Proof.
    induction A.
    - reflexivity.
    - simpl. f_equal. exact IHl. Qed.

  Lemma rev_app_distr:
    rev (A ++ B) = rev B ++ rev A.
  Proof.
  Abort.
  
  
  Lemma map_app:
    map f (A ++ B) = (map f A) ++ (map f B).
  Proof.
    induction A.
    - reflexivity.
    - simpl. f_equal. exact IHl. Qed.

  Lemma app_length:
  |A ++ B| = |A| + |B|.
  Proof.
    induction A.
    - reflexivity.
    - simpl. f_equal. exact IHl. Qed.

  Lemma rev_length:
  |rev A| = |A|.
  Proof.
    induction A.
    - reflexivity.
    - simpl. Abort.
      

  Lemma map_length:
  |map f A| = |A|.
  Proof.
    induction A.
    - reflexivity.
    - simpl. f_equal. exact IHl. Qed.

  Lemma prod_length:
  |list_prod A B| = |A| * |B|.
  Proof.
    induction A.
    - reflexivity.
    - simpl. Abort.
  
  Lemma rev_involutive:
    rev (rev A) = A.
  Proof.
    induction A.
    - reflexivity.
    - simpl. Abort.

  
  Lemma rev_unit:
    rev (A ++ [x]) = x :: rev A.
  Proof.
    induction A.
    - reflexivity.
    - simpl. Abort.

End Ex23.

(* Exercise 8.2.4 *)
Fixpoint revi (X: Type) (A B: list X) :=
  match A with
    |[] => B
    |x :: A => revi A (x :: B)
  end.

Goal forall (X: Type) (A B: list X),
       revi A B = rev A ++ B.
Proof.
  induction A.
  - reflexivity.
  - intros B. simpl. simpl_list. apply IHA. Qed.

Goal forall (X: Type) (A: list X),
       rev A = revi A nil.
Proof.
  intros X A. rewrite (Unnamed_thm2 A []). simpl_list. reflexivity.
Qed.

(* Exercise 8.2.5 *)

(* Definition lengthi (X: Type) : list X -> nat -> nat :=

Goal forall (X: Type) (A:list X),
         length A = lengthi A. *)

Definition lengthi (X: Type) : list X -> nat -> nat :=
  fix f A n := match A with
               | [] => n
               | a :: A => f A (S n)
               end.

Goal forall (X: Type) (A:list X) (n:nat),
    length A + n = lengthi A n.
Proof.
  induction A.
  - reflexivity.
  - intros n. simpl. specialize (IHA (S n)). rewrite <- IHA. omega. Qed.

Goal forall (X : Type) (A:list X),
    length A = lengthi A 0.
Proof.
  intros X A. rewrite <- (Unnamed_thm4 A 0). omega. Qed.

(** * 8.3 Membership *)

(* Commented because of naming conflicts with the Base library: 
 
Fixpoint In (X: Type) (a: X) (A: list X) :=
  match A with
    | => False
    |x :: A => x = a \/ In a A
  end.

Notation "x 'el' A" := (In x A) (at level 70).
*)

(* Exercise 8.3.1 *)

Goal forall (A B C: list nat), ~ (3 el []) /\ 2 el A ++ (1 :: 2 :: B) ++ C.
Proof.
  intros A B C. split.
  - apply in_nil.
  - apply in_or_app. right. apply in_or_app. left. apply in_cons. apply in_eq. Qed.
    

(* Exercise 8.3.2 *)

Section Ex32.
  Variable X: Type.
  Variable x y: X.
  Variable A B: list X.

  Lemma in_eq:
    x el x :: A.
  Proof.
  unfold In. left. reflexivity. Qed.

  Lemma in_cons:
    x el A -> x el y :: A.
  Proof.
    intros H. unfold In. right. apply H. Qed.

  Lemma in_or_app:
    x el A \/ x el B -> x el A ++ B.
  Proof.
    intros [H|H]. (* con auto se resuelve automaticamente *)
    - induction A; simpl; destruct H.
      + left. exact H.
      + right. apply IHl, H.
    - induction A.
      + simpl. exact H.
      + simpl. right. exact IHl. Qed.
      

  Lemma in_nil:
    ~ (x el []).
  Proof.
    intros H. destruct H. Qed.

  Lemma in_sing:
    x el [y] -> x = y.
  Proof.
    intros H. destruct H.
    - auto.
    - destruct H.
Qed.                       

  Lemma in_cons_neq:
    x el y::A -> x <> y -> x el A.
  Proof.
    intros H1 H2. destruct H1.
    - exfalso. congruence.
    - exact H.
  Qed.
  
  Lemma not_in_cons:
    ~ x el y :: A -> x <> y /\ ~ x el A.
  Proof.
    intro H1. split; intros H2.
    - apply H1. left. symmetry. exact H2.
    - apply H1. right. exact H2. Qed.

End Ex32.

(* Exercise 8.3.3 *)

Section Ex33.

  Lemma in_app_iff (X : Type) (A B: list X) (x :X):
    x el A ++ B <-> x el A \/ x el B.
  Proof.
    split; intros H.
    - induction A; simpl in H.
      + right. exact H.
      + destruct H.
        * left. left. exact H.
        * simpl. apply or_assoc. right. apply IHA, H.
    - induction A; destruct H; simpl.
      + destruct H.
      + exact H.
      + destruct H.
        * left. exact H.
        * right. apply IHA. left. exact H.
      + right. apply IHA. right. exact H. Qed.

  Lemma in_rev_iff (X: Type) (x: X) (A: list X):
    x el rev A <-> x el A.
  Proof.
    induction A; split; simpl; intro H.
    - exact H.
    - exact H.
    - apply in_app_iff in H. destruct H.
      + right. apply IHA, H.
      + left. destruct H; auto; destruct H.
    - apply in_app_iff. destruct H.
      + right. left. exact H.
      + left. apply IHA, H.
Qed.    

  Lemma in_map_iff (X Y: Type) (f: X -> Y) (x: Y) (A: list X):
    x el map f A <-> exists y, f y = x /\ y el A.
  Proof.
    induction A; split; simpl; intro H.
    - destruct H.
    - destruct H as [y [H1 H2]]; destruct H2.
    - destruct H.
      + exists a. auto.
      + apply IHA in H. destruct H as [y [H1 H2]]. exists y. auto.
    - destruct H as [y [H1 [H2|H2]]].
      + left. congruence.
      + right. apply IHA. exists y. auto.
  Qed.
  
  Lemma in_prod_iff (X Y: Type) (A: list X) (B: list Y) (a: X) (b: Y):
    (a, b) el list_prod A B <-> a el A /\ b el B.
  Proof.
    induction A as [|x A]; split; simpl; intro H.
    - destruct H.
    - tauto.
    - apply in_app_iff in H. destruct H.
      + apply in_map_iff in H. destruct H as [y [H1 H2]]. split.
        * left. change (fst (x,y) = fst (a,b)). rewrite H1. reflexivity.
        * change ((snd (a,b)) el B). rewrite <- H1.  exact H2.
      + apply IHA in H as [H1 H2]. auto.
    - destruct H as [[H1|H1] H2]; apply in_app_iff.
      + left. apply in_map_iff. exists b. split; congruence.
      + right. apply IHA. auto.
  Qed.
  
End Ex33.

(* Exercise 8.3.4 *)

(* Inductive con (* ... *)

Definition con_ind (* ... *)
          
Goal forall (X: Type) (A B C: list X),
      con A B C <-> A ++ B = C.
*)

Inductive con (X : Type) : list X -> list X -> list X -> Prop :=
| conEq A : con [] A A
| conAdd a A B C : con A B C -> con (a :: A) B (a :: C).

Goal forall (X: Type) (A B C: list X),
    con A B C <-> A ++ B = C.
Proof.
  intros X A B C; split; intros H.
  - induction H.
    + reflexivity.
    + simpl. congruence.
  - revert H; revert C; induction A; intros C H.
    + simpl in H. rewrite H. constructor.
    + simpl in H. destruct C as [|c C].
      * discriminate H.
      * assert (a = c). { congruence. } rewrite H0. constructor. apply IHA.
        congruence. Qed.

(** * 8.4 Inclusion and Equivalence *)

(* Commented because of naming conflicts with the Base library:   
Definition incl (X: Type) (xs ys: list X) :=
  forall a, a el xs -> a el ys.

Notation "A <<= B" := (incl A B) (at level 70).


Definition equi (X: Type) (xs ys: list X) :=
  xs <<= ys /\ ys <<= xs.

Notation "A === B" := (equi A B) (at level 70).
*)

Goal forall A B C, A <<= B -> 2 :: A ++ 3 :: A <<= C ++ 3 :: 2 :: B.
Proof.
  auto 7.
Qed.

Goal forall X (x y : X) A B, x::A ++ [y] ++ A ++ B === A ++ [y;x] ++ A ++ B.
Proof.
  intros X x y A B. simpl. rewrite equi_swap. rewrite equi_shift at 1. reflexivity.
Qed.

Goal forall (A B C D : list nat), A <<= B -> B <<= C -> C <<= D -> A <<= D.
Proof.
  intros A B C D F G H. rewrite F. rewrite G. exact H.
Qed.

(* Exercise 8.4.2  *)

Section Ex42.
  Variable X: Type.
  Implicit Types A B C: list X.

  Lemma incl_refl A:
    A <<= A.
  Proof.
    intros x H. exact H. Qed.

  Lemma incl_tl x A B:
    A <<= B -> A <<= x::B.
  Proof.
    intros H1 a H2. specialize (H1 a). apply H1 in H2. right. exact H2. Qed.

  Lemma incl_cons x A B:
    x el B -> A <<= B -> x :: A <<= B.
  Proof.
    intros H1 H2 a H3. destruct H3.
    - rewrite <- H. exact H1.
    - specialize (H2 a). exact (H2 H). Qed.
      
  Lemma incl_appl A B C:
    A <<= B -> A <<= B ++ C.
  Proof.
    intros H1 x H2. apply (H1 x) in H2. apply in_app_iff. left. exact H2. Qed.

  Lemma incl_appr A B C:
    A <<= C -> A <<= B ++ C.
  Proof.
    intros H1 x H2. apply (H1 x) in H2. apply in_app_iff. right. exact H2. Qed.

  Lemma incl_app A B C:
    A <<= C -> B <<= C -> A ++ B <<= C.
  Proof.
    intros H1 H2 x H3. apply in_app_iff in H3 as [H3|H3].
    - apply ((H1 x) H3).
    - apply ((H2 x) H3). Qed.

  Lemma incl_nil A:
    nil <<= A.
  Proof.
    intros x H. destruct H. Qed.
  
  Lemma incl_nil_eq A :
    A <<= nil -> A=nil.
  Proof.
    intros H1. destruct A.
    - reflexivity.
    - specialize (H1 x). assert (x el x :: A). { left. auto. }
      apply H1 in H. destruct H. Qed.

  Lemma incl_shift x A B :
    A <<= B -> x::A <<= x::B.
  Proof.
    intros H1 a H2. destruct H2 as [H2|H2].
    - subst. left. auto.
    - right. apply ((H1 a) H2). Qed.

  Lemma incl_lcons x A B :
    x::A <<= B <-> x el B /\ A <<= B.
  Proof.
    split; intro H1.
    - split.
      + specialize (H1 x). apply H1. left. reflexivity.
      + intros a H2. specialize (H1 a). assert (a el x :: A) as H3.
        { right. exact H2. } apply H1, H3.
    - destruct H1 as [H1 H2]. intros a H3. destruct H3 as [H3|H3].
      + subst. exact H1.
      + apply ((H2 a) H3). Qed.

  Lemma incl_sing x A y :
    x::A <<= [y] -> x = y /\ A <<= [y].
  Proof.
    intros H1. split.
    - specialize (H1 x). assert (x el x :: A) as H2. { left. reflexivity. }
      apply H1 in H2. destruct H2.
      + auto.
      + destruct H.
    - intros a H2. auto. Qed.
    

  Lemma incl_rcons x A B :
    A <<= x::B -> ~ x el A -> A <<= B.
  Proof.
    intros H1 H2 a H3. specialize (H1 a). assert (a el A) as H4 by assumption.
    apply H1 in H3. destruct H3.
    - subst. exfalso. auto.
    - exact H. Qed.

  Lemma incl_lrcons x A B :
    x::A <<= x::B -> ~ x el A -> A <<= B.
  Proof.
    intros H1 H2 a H3. specialize (H1 a). assert (a el x :: A) as H4.
    { right. exact H3. } apply H1 in H4. destruct H4.
    - subst. exfalso. auto.
    - exact H. Qed.

  Lemma incl_app_left A B C :
    A ++ B <<= C -> A <<= C /\ B <<= C.
  Proof.
    intros H1; split; intros x H2; specialize (H1 x).
    - apply H1. apply in_app_iff. left. exact H2.
    - apply H1. apply in_app_iff. right. exact H2.
Qed.

  Lemma incl_map A B Y (f: X -> Y):
    A <<= B -> map f A <<= map f B.
  Proof.
    intros H1 y H2. apply in_map_iff in H2 as [x [H2 H3]]. apply in_map_iff.
    exists x. auto. Qed.

  Lemma equi_push x A :
    x el A -> A === x::A.
  Proof.
    intros H1. split; intros a H2.
    - right. exact H2.
    - destruct H2.
      + subst. exact H1.
      + exact H. Qed.

  Lemma equi_dup x A :
    x::A === x::x::A.
  Proof.
    split; intros a H1.
    - destruct H1.
      + left. exact H.
      + right. right. exact H.
    - destruct H1.
      + left. auto.
      + exact H. Qed.

  Lemma equi_swap x y A:
    x::y::A === y::x::A.
  Proof.
    split; intros a H1.
    - destruct H1 as [H1|H1].
      + right. left. exact H1.
      + destruct H1 as [H1|H1].
        * left. exact H1.
        * right; right. exact H1.
    - destruct H1 as [H1|H1].
      + right. left. exact H1.
      + destruct H1 as [H1|H1].
        * left. exact H1.
        * right; right. exact H1. Qed.

  Lemma equi_shift x A B :
    x::A++B === A++x::B.
  Proof.
    split; intros a H1.
    - destruct H1 as [H1|H1]; apply in_app_iff.
      + right. left. exact H1.
      + apply in_app_iff in H1. destruct H1 as [H1|H1]; try auto.
    - apply in_app_iff in H1. destruct H1 as [H1|H1].
      + right. apply in_app_iff. left. exact H1.
      + destruct H1 as [H1|H1]; try auto. subst. left. reflexivity. Qed.

  Lemma equi_rotate x A :
    x::A === A++[x].
  Proof.
    split; intros a H1.
    - apply in_app_iff. destruct H1.
      + right. subst. auto.
      + auto.
    - apply in_app_iff in H1. destruct H1; auto. left. destruct H.
      + exact H.
      + destruct H. Qed.

End Ex42.

(* Exercise 8.4.3 Don't be confused by the syntax of instances. The proofs just work as usual lemmas! *)
Instance incl_preorder X :
  PreOrder (@incl X).
Proof.
  constructor.
  - intros A x H1. exact H1.
  - intros A B C H1 H2 x H3. specialize (H1 x). specialize (H2 x). apply H2, H1, H3.
Qed.

Instance equi_Equivalence X :
  Equivalence (@equi X).
Proof.
  constructor.
  - intros A. auto.
  - intros A B H1. split; intros x H2.
    + destruct H1 as [_ H1]. specialize (H1 x). apply H1, H2.
    + destruct H1 as [H1 _]. specialize (H1 x). apply H1, H2.
  - intros A B C H1 H2. split; intros x H3.
    + destruct H1 as [H1 _], H2 as [H2 _]. auto.
    + destruct H1 as [_ H1], H2 as [_ H2]. auto. Qed.

(* Exercise 8.4.4 *)

Instance incl_equi_proper X :
  Proper (@equi X ==> @equi X ==> iff) (@incl X).
Proof.
  hnf. intros A B H1 C D H2 ; split; intros H3; intros x H4.
  - destruct H2 as [H2 _], H1 as [_ H1]. auto.
  - destruct H1 as [H1 _], H2 as [_ H2]. auto. Qed.

Instance cons_incl_proper X x :
  Proper (@incl X ==> @incl X) (@cons X x).
Proof.
  hnf. intros A B H1 a H2. destruct H2 as [H2|H2].
  - left. assumption.
  - right. auto. Qed.

Instance cons_equi_proper X x :
  Proper (@equi X ==> @equi X) (@cons X x).
Proof.
  hnf. intros A B H1; split; intros a H2.
  - destruct H2.
    + left. assumption.
    + right. destruct H1 as [H1 _]. auto.
  - destruct H2.
    + left. assumption.
    + right. destruct H1 as [_ H1]. auto. Qed.

(* Exercise 8.4.5 *)

(* Inductive mem (X: Type) (x : X) : list X -> Prop := (* ... *)

Goal forall (X: Type) (x: X) (A: list X), mem x A <-> x el A. *)

Inductive mem (X: Type) (x : X) : list X -> Prop :=
| memF A : mem x (x :: A)
| memS y A : mem x A -> mem x (y :: A).                 

Check mem_ind.

Goal forall (X: Type) (x: X) (A: list X), mem x A <-> x el A.
Proof.
  intros X x A; split; intros H1.
  - induction H1.
    + left. reflexivity.
    + right. auto.
  - induction A.
    + destruct H1.
    + destruct H1.
      * subst. constructor.
      * constructor. auto. Qed.

(** * 8.5 Disjointness *)

(* Commented because of naming conflicts with the Base library:   

Definition disjoint A B :=
  ~ exists x, x el A /\ x el B. 
*)

(* Exercise 8.5.1 *)

Section Disjoint.
  Variable X: Type.
  Implicit Types A B: list X.

  Lemma disjoint_forall A B :
    disjoint A B <-> forall x, x el A -> ~ x el B.
  Proof.
    split; intros H1.
    - intros x H2 H3. apply H1. exists x. auto.
    - intros [x [H2 H3]]. apply (H1 x); auto. Qed.

  Lemma disjoint_symm A B :
    disjoint A B -> disjoint B A.
  Proof.
    intros H1 [x [H2 H3]]. apply H1. exists x. auto. Qed.

  Lemma disjoint_incl A B B' :
    B' <<= B -> disjoint A B -> disjoint A B'.
  Proof.
    intros H1 H2 [x [H3 H4]]. apply H2. exists x. auto. Qed.

  Lemma disjoint_nil B :
    disjoint nil B.
  Proof.
    intros [x [H1 _]]. destruct H1. Qed.

  Lemma disjoint_nil' A :
    disjoint A nil.
  Proof.
    intros [x [_ H2]]. destruct H2. Qed.

  Lemma disjoint_cons x A B :
    disjoint (x::A) B <-> ~ x el B /\ disjoint A B.
  Proof.
    split; intros H1.
    - split.
      + intros H2. apply H1. exists x. auto.
      + intros [y [H2 H3]]. apply H1. exists y. auto.
    - destruct H1 as [H1 H2]. intros [y [H3 H4]]. apply H2. exists y. split.
      + destruct H3.
        * subst. exfalso. auto.
        * assumption.
      + assumption.
Qed.

  Lemma disjoint_app A B C :
    disjoint (A ++ B) C <-> disjoint A C /\ disjoint B C.
  Proof.
    split; intros H1.
    - split; intros [x [H2 H3]]; apply H1; exists x; auto.
    - destruct H1 as [H1 H2]. intros [x [H3 H4]].
      apply in_app_iff in H3; destruct H3 as [H3|H3].
      + apply H1. exists x. auto.
      + apply H2. exists x. auto.
Qed.

End Disjoint.

(** * 8.6 Decidability *)

Print list_eq_dec.
Print list_in_dec.
Print list_forall_dec.
Print list_exists_dec.

Goal forall X A B (p : X -> Prop),
  eq_dec X -> (forall x, dec (p x)) -> dec (A=B \/ forall x, x el A -> exists y, y el B /\ (y el A \/ ~ p x)).
Proof. auto. Qed.

Instance iff_dec (X Y : Prop) :
  dec X -> dec Y -> dec (X <-> Y).
Proof. unfold dec; tauto. Qed.

(* Exercise 8.6.1 *)

(* Since === is defined with <<= and /\ *)

Goal forall X (A B : list X), eq_dec X -> dec (A === B).
Proof.
  cut (forall X (A B: list X), eq_dec X -> dec (A <<= B)).
  { intros H X A B eq. apply and_dec; apply H, eq. }
  intros X A B eq. induction A.
    + left. auto.
    + decide (a el B); destruct IHA as [IHA|IHA].
      * left. auto.
      * right. intros H1. apply incl_lcons in H1 as [_ H1]. auto.
      * right. intros H1. auto.
      * right. intros H1. auto.
Qed.    
          
  
(* Exercise 8.6.2 *)

Goal forall X A B (p : X -> Prop),
       eq_dec X -> (forall x, dec (p x)) -> dec (A=B \/ forall x, x el A -> exists y, y el B /\ (y el A \/ ~ p x)).
Proof.
  intros X A B p eqDec pxDec. apply or_dec.
  - apply list_eq_dec, eqDec.
  - apply list_forall_dec. intro x. apply list_exists_dec. intro y. apply or_dec.
    + apply list_in_dec, eqDec.
    + apply impl_dec.
      * apply pxDec.
      * right. intros H; apply H.
Qed.

(* Exercise 8.6.3 *)


Instance list_eq_dec X :
  eq_dec X -> eq_dec (list X).
Proof.
  intros H1 A; induction A; intros B.
  - destruct B.
    + left. reflexivity.
    + right. congruence.
  - destruct B.
    + right. congruence.
    + specialize (H1 x a). destruct H1.
      * specialize (IHA B). destruct IHA.
        { left. congruence. }
        { right. congruence. }
      * right. congruence.
Qed.

Instance list_in_dec (X : Type) (x : X) (A : list X) :
  eq_dec X -> dec (x el A).
Proof.
  intros eqDec; induction A.
  - right. intros H. destruct H.
  - destruct IHA as [H|H].
    + left. right. assumption.
    + specialize (eqDec x a). destruct eqDec.
      * left. left. auto.
      * right. intros H1. apply H. destruct H1; try assumption. exfalso. auto. 
Qed.
    

Instance list_forall_dec X A (p : X -> Prop) :
  (forall x, dec (p x)) -> dec (forall x, x el A -> p x).
Proof.
  intros pDec. induction A.
  - left. intros x H. destruct H.
  - specialize (pDec a). destruct pDec; destruct IHA.
    + left. intros x H. destruct H; auto. subst. assumption.
    + right. intros H1. apply n. intros x H2. apply H1. right. assumption.
    + right. auto.
    + right. auto. Qed.
      
Instance list_exists_dec X A (p : X -> Prop) :
  (forall x, dec (p x)) -> dec (exists x, x el A /\ p x).
Proof.
  intros H1. induction A.
  - right. intros [x [H2 H3]].  destruct H2.
  - destruct IHA as [H2|H2].
    + left. destruct H2 as [x [H2 H3]]. exists x. auto.
    + specialize (H1 a). destruct H1 as [H1|H1].
      * left. exists a. auto.
      * right. intros [x [H3 H4]]. apply H2. exists x. destruct H3; auto. subst. 
        exfalso; auto.
Qed.   

(* Exercise 8.6.4 *)
Lemma list_sigma_forall X A (p : X -> Prop) (p_dec : forall x, dec (p x)) :
  {x | x el A /\ p x} + {forall x, x el A -> ~ p x}.
Proof.
  induction A.
  - right. auto.
  - destruct IHA.
    + left. destruct s as [x [H1 H2]]. exists x. auto.
    + specialize (p_dec a). destruct p_dec.
      * left. exists a. auto.
      * right. intros x H1. destruct H1; auto. subst. assumption. Qed.

Lemma list_exists_DM X A (p : X -> Prop) :
  (forall x, dec (p x)) ->
  ~ (forall x, x el A -> ~ p x) -> exists x, x el A /\ p x.
Proof.
  intros H1 H2. assert ({x | x el A /\ p x} + {forall x, x el A -> ~ p x}) as H3.
  { apply list_sigma_forall. exact H1. }
  destruct H3.
  - destruct s as [x H3]. exists x. apply H3.
  - exfalso. auto.
Qed.

Lemma list_exists_not_incl X (A B : list X) :
  eq_dec X ->
  ~ A <<= B -> exists x, x el A /\ ~ x el B.
Proof.
  intros H1 H2. apply list_exists_DM.
  - intros x. auto.
  - intros H3. apply H2. intros x H4. Abort.

Lemma list_cc X (p : X -> Prop) A :
  (forall x, dec (p x)) ->
  (exists x, x el A /\ p x) -> {x | x el A /\ p x}.
Proof.
  intros H1 H2. assert ({x | x el A /\ p x} + {forall x, x el A -> ~ p x}) as H3.
  { apply list_sigma_forall. exact H1. }  destruct H3 as [H3|H3].
  - exact H3.
  - exfalso. destruct H2 as [x [H2 H4]]. specialize (H1 x). destruct H1 as [H1|H1].
    + specialize (H3 x). apply H3; assumption.
    + auto.
Qed.

(** * 8.7 Filtering *)

(* Commented because of naming conflicts with the Base library:   

Definition filter (X : Type) (p : X -> Prop) (p_dec : forall x, dec (p x)) : list X -> list X :=
  fix f A := match A with
              | nil => nil
              | x::A' => if decision (p x) then x :: f A' else f A'
             end.

Arguments filter {X} p {p_dec} A.

Definition decision (X : Prop) (D : dec X) : dec X := D.
Arguments decision X {D}.
 *)

Compute filter (fun x => 3 <= x <= 7) [1;2;3;4;5;6;7;8;9].

Lemma in_filter_iff X (p : X -> Prop) {p_dec : forall x, dec (p x)} x A :
  x el filter p A <-> x el A /\ p x.
Proof.
  induction A as [|y A]; simpl.
  - tauto.
  - decide (p y) as [B|B]; simpl; rewrite IHA; intuition; subst; tauto.
Qed.

(* Exercise 8.7.1 *)

Section FilterLemmas.
  Variable X : Type.
  Variable p q: X -> Prop.
  Context {p_dec : forall x, dec (p x)}.
  Context {q_dec : forall x, dec (q x)}.

  Goal forall x A,
    x el filter p A <-> x el A /\ p x.
  Proof.
    induction A as [|a A]; simpl.
    - tauto.
    - decide (p a) as [H1|H1]; simpl.
      +  rewrite IHA. split; intros H2.
         * destruct H2 as [H2|[H2 H3]]; auto. subst. auto.
         * destruct H2 as [H2 H3]. tauto.
      + rewrite IHA. split; intros H2.
        * tauto.
        * destruct H2 as [[H2|H2] H3]; auto. subst. exfalso. auto.
  Qed.
  
  Lemma filter_incl A :
    filter p A <<= A.
  Proof.
    intros x. apply in_filter_iff. Qed.

  Lemma filter_mono A B :
    A <<= B -> filter p A <<= filter p B.
  Proof.
    intros H1 x H2. apply in_filter_iff. apply in_filter_iff in H2 as [H2 H3]. auto.
  Qed.
  
  Lemma filter_pq_mono A :
    (forall x, x el A -> p x -> q x) -> filter p A <<= filter q A.
  Proof.
    intros H1 x H2. apply in_filter_iff. apply in_filter_iff in H2 as [H2 H3]. auto.
  Qed.
  
  Lemma filter_pq_eq A :
    (forall x, x el A -> (p x <-> q x)) -> filter p A = filter q A.
  Proof.
    intros H. induction A.
    - reflexivity.
    - simpl. decide (p a); decide (q a).
      + f_equal. apply IHA. auto.
      + exfalso. apply n. apply H; auto.
      + exfalso. apply n. apply H; auto.
      + auto.
  Qed.
  
  Lemma filter_id A :
    (forall x, x el A -> p x) -> filter p A = A.
  Proof.
    intros H1. induction A; auto. simpl. decide (p a) as [H2|H2].
    - f_equal. auto.
    - exfalso. auto.
  Qed.
  
  Lemma filter_app A B :
    filter p (A ++ B) = filter p A ++ filter p B.
  Proof.
    induction A; try reflexivity.
    simpl. decide (p a).
    - simpl. f_equal. auto.
    - apply IHA.
  Qed.
  
  Lemma filter_fst x A :
    p x -> filter p (x::A) = x::filter p A.
  Proof.
    intros H1. simpl. decide (p x); auto. exfalso. auto. Qed.

  Lemma filter_fst' x A :
    ~ p x -> filter p (x::A) = filter p A.
  Proof.
    intros H1. simpl. decide (p x); auto. exfalso; auto. Qed.

End FilterLemmas.


(* Exercise 8.7.2 *)

(* Fixpoint inter (X: Type) (A B: list X) : list X :=
  (* ... *)

Goal forall (X: Type) (x: X) (A B: list X),
       x el inter A B <-> x el A /\ x el B.
Abort. *)

(* He puesto la hipotesis de que la igualdad sobre el tipo sea decidible, si no no
se me ocurre como hacerlo *)

Fixpoint inter (X: Type) {p : eq_dec X} (A B: list X) : list X :=
  match A with
  | [] => []
  | a :: A => if decision (a el B) then a :: inter A B else inter A B
  end.

Goal forall (X: Type) (eq : eq_dec X) (x: X) (A B: list X),
    x el inter A B <-> x el A /\ x el B.
Proof.
  induction A; intros B; simpl; split; intros H1; try tauto.
  -  decide (a el B).
     + destruct H1; subst; auto. apply IHA in H; tauto.
     + apply IHA in H1; tauto.
  - destruct H1 as [[H1|H1] H2]; decide (a el B).
    + subst. left; reflexivity.
    + subst. exfalso; auto.
    + right. apply IHA; auto.
    + apply IHA; auto.
Qed.

(** * 8.8 Element Removal *)

(* Commented because of naming conflicts with the Base library:   

Variable X : Type.
Context {eq_X_dec : eq_dec X}.

Definition rem (A : list X) (x : X) : list X :=
 filter (fun z => z <> x) A. 
*)

(* Exercise 8.8.1 *)

Section Removal.
  Variable X : Type.
  Context {eq_X_dec : eq_dec X}.

  Lemma in_rem_iff x A y :
    x el rem A y <-> x el A /\ x <> y.
  Proof.
    induction A; simpl; try tauto; split; intros H1.
    - decide (a <> y).
      + destruct H1; subst; tauto.
      + apply IHA in H1. tauto.
    - destruct H1 as [[H1|H1] H2]; decide (a <> y); subst.
      + left; reflexivity.
      + tauto.
      + right. apply IHA; auto.
      + auto. 
  Qed.
  
  Lemma rem_not_in x y A :
    x = y \/ ~ x el A -> ~ x el rem A y.
  Proof.
    intros [H1|H1] H2.
    - subst. apply in_rem_iff in H2. tauto.
    - apply in_rem_iff in H2. tauto.
  Qed.

  Lemma rem_incl A x :
    rem A x <<= A.
  Proof.
    intros a H. apply in_rem_iff in H. tauto. Qed.
    
  Lemma rem_mono A B x :
    A <<= B -> rem A x <<= rem B x.
  Proof.
    intros H1 a H2. apply in_rem_iff in H2 as [H2 H3]. apply in_rem_iff. auto. Qed.

  Lemma rem_inclr A B x :
    A <<= B -> ~ x el A -> A <<= rem B x.
  Proof.
    intros H1 H2 a H3. apply in_rem_iff. decide (a = x); subst; auto. Qed.

  Lemma rem_cons A B x :
    A <<= B -> rem (x::A) x <<= B.
  Proof.
    intros H1 a H2. apply in_rem_iff in H2 as [H2 H3]. destruct H2; auto.
    exfalso; auto. Qed.

  Lemma rem_cons' A B x y :
    x el B -> rem A y <<= B -> rem (x::A) y <<= B.
  Proof.
    intros H1 H2 a H3. apply in_rem_iff in H3 as [H3 H4]. destruct H3; subst; auto.
    Qed.

  Lemma rem_app x A B :
    x el A -> B <<= A ++ rem B x.
  Proof.
    intros H1 a H2. apply in_app_iff. decide (a = x).
    - left. subst. assumption.
    - right. apply in_rem_iff. auto. Qed.

  Lemma rem_app' x A B C :
    rem A x <<= C -> rem B x <<= C -> rem (A ++ B) x <<= C.
  Proof.
    intros H1 H2 a H3. apply in_rem_iff in H3 as [H3 H4].
    apply in_app_iff in H3 as [H3|H3].
    - apply H1. apply in_rem_iff; auto.
    - apply H2. apply in_rem_iff; auto.
  Qed.
  
  Lemma rem_in x y A :
    x el rem A y -> x el A.
  Proof.
    intros H1. apply in_rem_iff in H1. tauto. Qed.

  Lemma rem_neq x y A :
    x <> y -> x el A -> x el rem A y.
  Proof.
    intros H1 H2; apply in_rem_iff; auto. Qed.

  Lemma rem_equi x A :
    x::A === x::rem A x.
  Proof.
    split; intros a H1; decide (a = x); subst.
    - left; reflexivity.
    - right. apply in_rem_iff. destruct H1; auto. exfalso; auto.
    - left; reflexivity.
    - right. destruct H1.
      + exfalso; auto.
      + apply in_rem_iff in H as [H1 H2]; auto.
  Qed.
  
  Lemma rem_reorder x A :
    x el A -> A === x :: rem A x.
  Proof.
    intros H1. apply equi_push in H1. (* no funciona rewrite asi que la prueba 
va a ser mas larga *) assert (x::A === x::rem A x) as H2 by apply rem_equi;
    split; intro a; destruct H1, H2;  auto. Qed.
    
  Lemma rem_comm A x y :
    rem (rem A x) y = rem (rem A y) x.
  Proof.
    induction A; auto.
    simpl. decide (a <> x); decide (a <> y).
    - simpl. decide (a <> x); decide (a <> y); try tauto. (* Casos absurdos *)
      f_equal; apply IHA.
    - simpl. decide (a <> y); tauto.
    - simpl. decide (a <> x); tauto.
    - assumption.
  Qed.
  
  Lemma rem_fst x A :
    rem (x::A) x = rem A x.
  Proof.
    induction A; simpl; decide (x <> x); tauto. Qed.

  Lemma rem_fst' x y A :
    x <> y -> rem (x::A) y = x::rem A y.
  Proof.
    intros H1. simpl; decide (x <> y); tauto. Qed.

  Lemma rem_id x A :
    ~ x el A -> rem A x = A.
  Proof.
    intros H1. induction A; auto.
    simpl; decide (a <> x).
    - f_equal. auto.
    - exfalso. apply n. intros H2. apply H1. left. assumption. Qed.

End Removal.

(** * 8.9 Cardinality *)

(* Commented because of naming conflicts with the Base library:   

  Variable X : Type.
  Context { eq_X_dec : eq_dec X }.
  Implicit Types A B : list X.

  Fixpoint card A :=
    match A with
      | nil => 0
      | x::A => if decision (x el A) then card A else 1 + card A
    end.
*)

Print card.

(* Exercise 8.9.1 *)

  (* Fixpoint cardNo A :=
    match A with
      | nil => 0
      | x::A' => cardNo ( rem A' x)
    end. *)
(* Como vemos si intetamos definirla el problema es que la llamada recursiva
es rem A' x y no A', con lo que coq no puede probar que decrezca *)

(* Exercise 8.9.2 *)

Section Ex92.
  Variable X : Type.
  Context { eq_X_dec : eq_dec X }.
  Implicit Types A : list X.

  Lemma card_in_rem x A :
    x el A -> card A = 1 + card (rem A x).
  Proof.
    intros H1; induction A. destruct H1. simpl. destruct H1 as [H1|H1]; decide (a el A); decide (a <> x); subst; try tauto.
    - f_equal. assert (rem A x = A) by (apply rem_id; assumption). congruence.
    - assert (a el rem A x) by (apply in_rem_iff; auto). simpl.
      decide (a el rem A x); tauto.
    - f_equal. assert (~ a el rem A x). { intros H2. apply n. apply in_rem_iff in H2.
      tauto. } simpl. decide (a el rem A x); tauto.
    - exfalso. apply n0. intros H2. subst. auto.
  Qed.  
End Ex92.

(* Exercise 8.9.3 *)

Section Ex93.
  Variable X : Type.
  Context { eq_X_dec : eq_dec X }.
  Implicit Types A : list X.
  
 Lemma card_le A B :
    A <<= B -> card A <= card B.
 Proof.
   revert B; induction A; intros B H; simpl.
   - omega.
   - apply incl_lcons in H as [H1 H2]. decide (a el A).
     + auto.
     + assert (card B = S (card (rem B a))) by (apply card_in_rem; assumption).
       rewrite H. assert (A <<= (rem B a)) as H3 by auto. apply IHA in H3; omega.
 Qed.
 
End Ex93.

(** * 8.10 Duplicate-Freeness *)

(* Commented because of naming conflicts with the Base library:   
Inductive dupfree (X : Type) : list X -> Prop :=
| dupfreeN : dupfree nil
| dupfreeC x A : ~ x el A -> dupfree A -> dupfree (x::A).

Fixpoint undup (X: Type) (H: eq_dec X) (A : list X) : list X :=
  match A with
    | nil => nil
    | x::A' => if decision (x el A') then undup H A' else  x :: undup H A'
  end.

*)

(* Exercise 8.10.1 *)

Section Dupfree.
  Variable X: Type.
  Context {eq_X_dec : eq_dec X}.
  Implicit Type A: list X.

  Lemma dupfree_card A:
    dupfree A -> card A = |A|.
  Proof.
    intros H1. induction H1.
    - reflexivity.
    - simpl. decide (x el A); try tauto; clear n. auto.
  Qed.
  
  Lemma dupfree_dec A :
    dec (dupfree A).
  Proof.
    induction A.
    - left. constructor.
    - decide (a el A).
      + right. intros H1. remember (a :: A) as B. destruct H1.
        * discriminate HeqB.
        * apply H. congruence.
      + destruct IHA.
        * left. constructor; assumption.
        * right. intro H1. remember (a :: A) as B. destruct H1;
          try discriminate HeqB.
          apply H; congruence.
  Qed.   

  Lemma dupfree_undup A :
    dupfree (undup A).
  Proof.
    induction A; simpl; try constructor.
    decide (a el A).
    - assumption.
    - constructor; try assumption. intros H1. apply n.
      assert (forall B, undup B <<= B).
      { intros B x H2.  induction B as [|b B].
        - destruct H2.
        - unfold undup in H2. decide (b el B).
          + right. auto.
          + destruct H2; subst; auto. }
      apply H. assumption. Qed.

  Lemma undup_id_equi A :
    undup A === A.
  Proof.
    split; induction A; intros x H.
    - destruct H.
    - unfold undup in H. decide (a el A).
      + right. auto.
      + destruct H; subst; auto.
    - destruct H.
    - destruct H; unfold undup; decide (a el A); subst; auto. Qed.
End Dupfree.

(* Exercise 8.10.2 *)

Section Dupfree2.
  Variable X: Type.
  Context {eq_X_dec : eq_dec X}.
  Implicit Type A: list X.

  Lemma dupfree_app A B :
    disjoint A B -> dupfree A -> dupfree B -> dupfree (A++B).
  Proof.
    intros H1 H2 H3. induction H2 as [|a A H2]; simpl.
    - assumption.
    - constructor.
      + intros H4. apply in_app_iff in H4. destruct H4 as [H4|H4].
        * auto.
        * apply H1. exists a. auto.
      + apply IHdupfree. intros [x [H4 H5]]. apply H1. exists x.  auto.
  Qed.
  
  Lemma dupfree_map Y A (f : X -> Y) :
    (forall x y, x el A -> y el A -> f x = f y -> x=y) ->
    dupfree A -> dupfree (map f A).
  Proof.
    intros H1 H2. induction H2 as [|a A H2 H3]; simpl.
    - constructor.
    - constructor.
      + intros H4. apply H2. apply in_map_iff in H4 as [y [H4 H5]]. cut (y = a).
        { intro H6; subst. assumption. }
        apply H1; auto.
      + apply IHH3. auto.
  Qed.
  
  Lemma dupfree_filter p (p_dec : forall x, dec (p x)) A :
    dupfree A -> dupfree (filter p A).
  Proof.
    intros H1. induction H1 as [|a A H1 H2]; simpl.
    - constructor.
    - decide (p a).
      + constructor; auto. intros H3. apply in_filter_iff in H3. tauto.
      + assumption.
  Qed.
  

End Dupfree2.

(** * 8.11 Power Lists *)

(* Commented because of naming conflicts with the Base library:   

Fixpoint power (X: Type) (U : list X ) : list (list X) :=
  match U with
    | nil => nil
    | x :: U' => power U' ++ map (cons x) (power U')
  end.

Definition rep (X: Type) (H: eq_dec X) (A U : list X) : list X :=
  filter (fun x => x el A) U.
*)

(* Exercise 8.11.1 *)

Section PowerRep.
  Variable X : Type.
  Context {eq_X_dec : eq_dec X}.
  Implicit Types A U: list X.

  Lemma power_incl A U :
    A el power U -> A <<= U.
  Proof.
    revert A; induction U; intros A; simpl.
    - intros [H1|H1]; destruct H1; auto.
    - intros H1. apply in_app_iff in H1. destruct H1 as [H1|H1].
      + auto.
      + apply in_map_iff in H1 as [B [H1 H2]]. subst. apply incl_shift. auto. Qed.

  Lemma power_nil U :
    nil el power U.
  Proof.
    induction U; simpl; try tauto. apply in_app_iff. auto. Qed.

  Lemma rep_power A U :
    rep A U el power U.
  Proof.
    induction U as [|u U]; simpl.
    - auto.
    - apply in_app_iff. decide (u el A).
      + right. apply in_map_iff. exists (rep A U). auto.
      + left. assumption.
  Qed.

  Lemma rep_incl A U :
    rep A U <<= A.
  Proof.
    induction U as [|u U]; simpl; intros x H1.
    - destruct H1.
    - decide (u el A).
      + destruct H1; subst; try assumption. apply IHU. assumption.
      + apply IHU. assumption.
  Qed.

  Lemma rep_in x A U :
    A <<= U -> x el A -> x el rep A U.
  Proof.
    induction A; simpl; intros H1 H2.
    - destruct H2.
    - destruct H2.
      + subst. apply in_filter_iff. auto.
      + apply in_filter_iff. auto. Qed.

    
  Lemma rep_equi A U :
    A <<= U -> rep A U === A.
  Proof.
    destruct A as [|a A]; simpl; intros H1.
    - cut (rep [] U = []). intros H2. rewrite H2. reflexivity.
      { induction U; simpl; auto. }
    - split; intros x H2.
      + unfold rep in H2. apply in_filter_iff in H2 as [H2 H3]. assumption.
      + destruct H2; apply in_filter_iff.
        * subst. auto.
        * auto. Qed.

  Lemma rep_mono A B U :
    A <<= B -> rep A U <<= rep B U.
  Proof.
    intros H1 x H2. apply in_filter_iff. unfold rep in H2.
    apply in_filter_iff in H2 as [H2 H3]. auto. Qed.

  Lemma rep_eq A B U :
    A === B -> rep A U = rep B U.
  Proof.
    intros H1. induction U. simpl.
    - reflexivity.
    - unfold rep. unfold filter. decide (a el A); decide (a el B); auto.
      + f_equal. apply IHU.
      + exfalso. apply n, H1, i.
      + exfalso. apply n, H1, i.
  Qed.
  
  Lemma rep_injective A B U :
    A <<= U -> B <<= U -> rep A U = rep B U -> A === B.
  Proof.
    intros H1 H2 H3. assert (rep A U === A /\ rep B U === B) as [H4 H5].
    { split; apply rep_equi; assumption. }
    rewrite <- H4. rewrite <- H5. split; intros x H6; apply rep_in; auto.
    - rewrite H3 in H6. destruct H5 as [H5 _]. auto.
    - rewrite <- H3 in H6. destruct H4 as [H4 _]. auto.
  Qed.

  Lemma rep_idempotent A U :
    rep (rep A U) U = rep A U.
  Proof.
    assert (forall x : X, In x U -> (x el (rep A U) <-> x el U /\ x el A)).
    { intros x _. apply in_filter_iff. }
    assert (rep (rep A U) U = filter (fun x => x el U /\ x el A) U).
    { apply filter_pq_eq. auto. }
    rewrite H0. unfold rep. apply filter_pq_eq.
    intros x H1. tauto. Qed.
  
  Lemma dupfree_power U :
    dupfree U -> dupfree (power U).
  Proof.
    intros H1. induction H1 as [|u U H1 H2].
    - simpl. constructor; auto. constructor.
    - simpl. apply dupfree_app.
      + intros [x [H3 H4]]. apply H1. apply in_map_iff in H4 as [B [H4 H5]]. subst.
        apply power_incl in H3. auto.
      + assumption.
      + apply dupfree_map.
        * intros A B _ _ H3. congruence.
        * assumption.
  Qed.
  
  Lemma dupfree_in_power U A :
    A el power U -> dupfree U -> dupfree A.
  Proof.
    intros H1 H2. induction A.
    - constructor.
    - constructor.
      + intros H3. induction U as [|u U].
        * simpl in H1. destruct H1; auto. discriminate H.
        * remember (u :: U) as C. destruct H2 as [|]. simpl in H1. destruct H1;
          auto. discriminate H.
          assert (x = u /\ A0 = U) as [e1 e2] by (split;congruence); subst.
          clear HeqC. apply IHU; auto.
          { simpl in H1. apply in_app_iff in H1 as [H1|H1].
            - auto.
            - apply in_map_iff in H1 as [B [H1 H4]].
              assert (u = a /\ B = A) as [e1 e2] by (split;congruence); subst.
              exfalso.  apply H. apply power_incl in H4. apply H4, H3. }
          { clear IHU. intros H4. apply IHA. simpl. apply in_app_iff. left.
            assumption. }
      + apply IHA. cut (forall b B, b :: B el power U -> B el power U).
        { intros H3. apply (H3 a). assumption. }
        clear IHA; clear H2; clear H1; clear A; clear a. intros a A H1.
        induction U as [|u U].
        * simpl in H1. destruct H1; try tauto. discriminate H.
        * simpl in H1. apply in_app_iff in H1 as [H1|H1].
          { simpl. apply in_app_iff. left. auto. }
          { apply in_map_iff in H1 as [B [H2 H3]].
            assert (u = a /\ B = A) as [e1 e2] by (split;congruence); subst;
              clear H2. simpl. apply in_app_iff. left. assumption. }
Qed.
                    
  Lemma rep_dupfree A U :
    dupfree U -> A el power U -> rep A U = A.
  Proof.
    revert A; induction U as [|u U]; intros A H1 H2.
    - simpl in H2; destruct H2; subst; auto; destruct H.
    - remember (u :: U) as B. destruct H1. discriminate HeqB.
      assert (x = u /\ A0 = U) as [e1 e2] by (split; congruence); subst;
        clear HeqB. simpl in H2. apply in_app_iff in H2. simpl.
      decide (u el A); destruct H2 as [H2|H2].
      + apply power_incl in H2. exfalso. auto.
      + apply in_map_iff in H2 as [B [H2 H3]].
        destruct A as [|a A]. destruct i.
        assert (u = a /\ B = A) as [e1 e2] by (split;congruence); subst. clear i.
        clear H2.  f_equal. assert (~ a el A) as H2.
        { cut (dupfree (a :: A)). intros H4. remember (a :: A) as B. destruct H4.
          discriminate HeqB.
          assert (x = a /\ A0 = A) as [e1 e2] by (split;congruence); subst; auto.
          assert (dupfree (a :: U)) as H2 by (constructor; auto).
          assert (a :: A el power (a :: U)). { simpl. apply in_app_iff. right.
          apply in_map_iff. exists A; auto. } apply (dupfree_in_power H0 H2). }
        replace (rep (a :: A) U) with (rep A U).
        { apply IHU; auto. }
        unfold rep. apply filter_pq_eq. intros x H4. split;auto; intros H5.
        destruct H5; auto. subst. tauto.
      + apply IHU; auto.
      + apply IHU; auto. apply in_map_iff in H2 as [B [H2 H3]]. assert (u el A).
        { rewrite <- H2. left. reflexivity. } tauto. Qed.
          
    

  Lemma power_extensional A B U :
    dupfree U -> A el power U -> B el power U -> A === B -> A = B.
  Proof.
    intros H1 H2 H3 H4. assert (rep A U = A /\ rep B U = B) as [H5 H6].
    { split; apply rep_dupfree; auto. } rewrite <- H5. rewrite <- H6.
    apply rep_eq. assumption. Qed.

End PowerRep.
