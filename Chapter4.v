(** * Chapter 4: Induction and recursion *)

Require Import Base.

(** * 4.1 Induction Lemmas *)

Check nat_ind.
(* nat_ind
   : forall P : nat -> Prop, 
      P 0 -> 
      (forall n : nat, P n -> P (S n)) -> 
      forall n : nat, P n *)

Goal forall n, n + 0 = n.
Proof.
  apply (nat_ind (fun n => n + 0 = n)).
  - reflexivity.
  - intros n IHn. simpl. f_equal. exact IHn.
Qed.

Goal forall n m, n + S m = S (n + m).
Proof.
  intros n m. revert n.
  apply (nat_ind (fun n => n + S m = S (n + m))) ; simpl.
  - reflexivity.
  - intros n IHn. f_equal. exact IHn.
Qed.

(* Comentado porque ya definido (si no da problemas )
Definition nat_ind (p : nat -> Prop) (basis : p 0) (step : forall n, p n -> p (S n))
  : forall n, p n := fix f n := match n return p n with
                                  | 0 => basis
                                  | S n' => step n' (f n')
                                end.
*)
(* Exercise 4.1 *)

Goal forall n m, n + S m = S (n + m).
Proof.  
  apply (nat_ind ( fun n => forall m, n + S m = S (n + m) )) ; simpl.
  - reflexivity.
  - intros n IHn m. f_equal. apply IHn. Qed.
  
(* Exercise 4.2 *)

(* Definition list_ind (X: Type) (p: list X -> Prop) (basis: p nil) 
(step: forall (x:X) (A: list X), p A -> p (x ::A)): forall A: list X, p A := 
  fix f A := match A return p A with
                     | [] => basis
                     | a :: A' => step a A' (f A')
                   end.
*)

Goal forall (X: Type) (x y z: list X), x ++ (y ++ z) = (x ++ y) ++ z.
Proof.
  intros X x y z. revert x.
  apply (list_ind (fun x => x ++ (y ++ z) = (x ++ y) ++ z)).
  - reflexivity.
  - intros a l IndH. simpl. f_equal. exact IndH. Qed.

Check list_ind.
(* list_ind
   : forall (A : Type) (P : list A -> Prop),
       P [] ->
       (forall (a : A) (l : list A), P l -> P (a :: l)) ->
       forall l : list A, P  *)

(** * 4.2 Primitive Recursion *)

Definition prec (p : nat -> Type) (x : p 0) (f : forall n, p n -> p (S n))
  : forall n, p n := fix F n := match n return p n with
                                  | 0 => x
                                  | S n' => f n' (F n')
                                end.

Check fun p : nat -> Prop => prec (p:= p).
(* fun p : nat -> Prop => prec (p:=p)
   : forall p : nat -> Prop,
     p 0 ->
     (forall n : nat, p n -> p (S n)) ->
     forall n : nat, p n *)

Lemma nat_ind' (p : nat -> Prop) :
  p 0 -> (forall n, p n -> p (S n)) -> forall n, p n.
Proof. exact (prec (p:=p)). Qed.

Definition add := prec (fun y => y) (fun _ r y => S (r y)).



Compute add 3 7.
(* = 10 : nat *)

Goal forall x y, add x y = x + y.
Proof. intros x y. induction x ; simpl ; congruence. Qed.

Goal forall X f x n ,
       Nat.iter n f x = prec (p:= fun _ => X) x (fun _ => f) n.
Proof. induction n ; simpl ; congruence. Qed.

Print nat_rec.

(* Exercise 4.2.1 *)
Goal prec = nat_rect.
Proof.
  unfold prec; unfold nat_rect. reflexivity. Qed.

(* Exercise 4.2.2 *)
Goal forall (p: nat -> Prop) (x: p 0) (f: forall n, p n -> p (S n)),
       prec x f 0 = x.
Proof.
  intros p x f. reflexivity. Qed.
  
Goal forall (p: nat -> Prop) (x: p 0) (f: forall n, p n -> p (S n)) (n: nat),
       prec x f (S n) = f n (prec x f n).
Proof.
  intros p x f n. reflexivity. Qed.

(* Exercise 4.2.3 *)
(*Definition mult' : nat -> nat -> nat := fun n m => prec (* ... *)

Goal forall n m, mult n m = mult' n m.
Abort. *)

Definition mult' : nat -> nat -> nat := fun n m => prec
  (fun y => O) (fun _ r m => add m (r m)) n m.

Goal forall n m, mult n m = mult' n m.
Proof.
  induction n; intros m; simpl.
  - reflexivity.
  - symmetry. rewrite IHn. apply Unnamed_thm3.
Qed.

(* Hemos usado que add definido por prec es lo mismo que +, asi hemos definido
mult' unicamente con prec. Alternativamente, como ya sabemos que add y + son iguales
podriamos haber puesto + en lugar de add en la definicion de mult' y la demostracion
hubiera sido mas corta *)

(* Definition fact' : nat -> nat := prec (* ... *).

Goal forall n, fact n = fact' n.
Abort. *)

Definition fact' : nat -> nat := prec (1) (fun n r => mult' (S n) r). 

Goal forall n, fact n = fact' n.
Proof.
  induction n; simpl.
  - reflexivity.
  - assert (add (fact' n) (mult' n (fact' n)) = fact' n + mult' n (fact' n)) as H.
    apply Unnamed_thm3. rewrite H.
    assert (mult' n (fact' n) = n * (fact' n)) as H1. symmetry. apply Unnamed_thm8.
    rewrite H1. rewrite IHn. reflexivity.
Qed.

(* Otra vez hubieramos podido obtener una demostracion mas corta con otra definicion
de fact' *)

(* Exercise 4.2.4 *)
(* Definition pred' : nat -> nat := (* ... *) *)

Definition pred' : nat -> nat := prec O (fun n _ => n).

(* Goal forall n, pred n = pred' n.
Abort. *)

Goal forall n, pred n = pred' n.
Proof.
  induction n; auto. Qed.

(* Exercise 4.2.5 *)
(* Goal forall X x f n,
       match n with O => x |S n' => f n' end = prec (* ... *). *)

Goal forall (X : Type) (x : X) (f : nat -> X) (n : nat), (* No inferia bien los tipos *)
    match n with O => x |S n' => f n' end = prec x (fun n _ => f n) n.
Proof.
  intros X x f; induction n; reflexivity. Qed.

(** * 4.3 Size Induction *)

Lemma size_induction X (f : X -> nat) (p : X -> Prop) :
  (forall x, (forall y, f y < f x -> p y) -> p x) ->
  forall x, p x.
Proof.
  intros step x. apply step.
  assert (G: forall n y, f y < n -> p y).
  { intros n. induction n.
    - intros y B. exfalso. omega.
    - intros y B. apply step. intros z C. apply IHn. omega. }
  apply G.
Qed.

(* Exercise 4.3.1 *)
Lemma complete_induction (p : nat -> Prop) :
  (forall x, (forall y, y < x -> p y) -> p x) -> forall x, p x.
Proof.
  apply size_induction. Qed. (* Es un caso particular de la induccion por size, donde
X es nat y f es la identidad *)

Lemma complete_induction' (p : nat -> Prop) :
  (forall x, (forall y, y < x -> p y) -> p x) -> forall x, p x.
Proof.
  intros step x. apply step. induction x.
  - intros y abs. exfalso. omega.
  - intros y ySx. apply step. intros z zy. apply IHx. omega.
Qed.

(* Exercise 4.3.2 *)
(* Definition lt : nat -> nat -> Prop := *)

Definition lt : nat -> nat -> Prop :=
  fun x y => leb (S x) y = true.

Lemma lt_tran x y z : lt x y -> lt y (S z) -> lt x z. 
Proof.
  revert y z; induction x; intros y z A B.
  - destruct y, z; try discriminate A; try discriminate B. (* Casos abs por hip *)
    unfold lt. simpl. reflexivity.
  - destruct y, z; try discriminate A; try discriminate B. (* Casos abs por hip *)
    assert (lt x z) as  C. { apply (IHx y).
                             - unfold lt in A. simpl in A. exact A. 
                             - unfold lt in B. simpl in B. exact B. }
    unfold lt. simpl. exact C.
Qed.

Lemma size_induction_lt X (f : X -> nat) (p : X -> Prop) :
  (forall x, (forall y, lt (f y) (f x) -> p y) -> p x) ->
  forall x, p x.
Proof.
  intros step x. apply step.
  assert (forall n y, lt (f y) n -> p y) as A.
  { induction n; intros y A.
    - unfold lt in A. simpl in A. discriminate A. (* Basta con discriminate A, pero 
asi se ve mas claro *)
    - apply step. intros z B. apply IHn. exact (lt_tran B A). }
  apply A. Qed.

(** * 4.4 Equational Specifcation of Functions *)

Definition addition (f : nat -> nat -> nat) : Prop :=
  forall x y,
    f x 0 = x /\
    f x (S y) = f (S x) y.

Lemma addition_existence :
  addition plus.
Proof. intros x y. omega. Qed.

Lemma addition_uniqueness f g :
  addition f -> addition g -> forall x y, f x y = g x y.
Proof.
  intros A B x y. revert x. induction y ; intros x.
  - destruct (A x 0) as [A' _]. destruct (B x 0) as [B' _]. congruence.
  - destruct (A x y) as [_ A']. destruct (B x y) as [_ B']. specialize (IHy (S x)). congruence.
Qed.

Definition ackermann (f : nat -> nat -> nat) : Prop :=
  forall m n,
    f O n = S n /\
    f (S m) O = f m 1 /\
    f (S m) (S n) = f m (f (S m) n).

Definition ack : nat -> nat -> nat :=
  fix f m := match m with
               | O => S
               | S m' => fix g n := match n with
                                      | O => f m' 1
                                      | S n' => f m' (g n')
                                    end
             end.

Goal ackermann ack.
Proof. unfold ackermann. auto. Qed.

Goal forall f g x y, ackermann f -> ackermann g -> f x y = g x y.
Proof.
  intros f g x y A B. revert y. induction x ; intros y.
  - destruct (A 0 y) as [C _]. destruct (B 0 y) as [D _]. congruence.
  - induction y.
    + destruct (A x 0) as [_ [C _]]. destruct (B x 0) as [_ [D _]]. congruence.
    + destruct (A x y) as [_ [_ C]]. destruct (B x y) as [_ [_ D]]. congruence.
Qed.

(* Exercise 4.4.1 *)

(* Definition multiplication (f : nat -> nat -> nat) : Prop := (* ... *)

Goal multiplication mult.
Abort. *)

Definition multiplication (f : nat -> nat -> nat) : Prop :=
  forall x y,
    f O y = O /\
    f (S x) y = y + f x y.

Goal multiplication mult.
Proof.
  intros x y. auto. Qed.

Goal forall f g x y, multiplication f -> multiplication g -> f x y = g x y.
Proof.
  intros f g x y A B; induction x.
  - destruct (A O y) as [A' _]. destruct (B O y) as [B' _]. congruence.
  - destruct (A x y) as [_ A']. destruct (B x y) as [_ B']. congruence.
Qed.

(* Definition subtraction (f: nat -> nat -> nat): Prop := (* ... *)

Goal subtraction minus. 
Abort. *)

Definition subtraction (f: nat -> nat -> nat): Prop :=
  forall x y,
    f O y = O /\
    f (S x) O = S x /\
    f (S x) (S y) = f x y.

Goal subtraction minus.
Proof.
  intros x y; omega. Qed.

Goal forall f g x y, subtraction f -> subtraction g -> f x y = g x y.
Proof.
  intros f g x y A B; revert y; induction x; intro y.
  - destruct (A O y) as [A' _]. destruct (B O y) as [B' _]. congruence.
  - induction y.
    + destruct (A x O) as [_ [A' _]]. destruct (B x O) as [_ [B' _]].
      congruence.
    + destruct (A x y) as [_ [_ A']]. destruct (B x y) as [_ [_ B']]. congruence.
Qed.

(* Exercise 4.4.2 *)

(*Definition ack' : nat -> nat -> nat := prec (* ... *)

Goal ackermann ack'. 
*)

Definition ack' : nat -> nat -> nat := prec S (fun _ fm => fun Sn => prec (fm 1)
                  (fun _ gn => fm gn) Sn).

Goal ackermann ack'.
Proof.
  intros x y; auto. Qed.

(* Exercise 4.4.3 *)

Definition primitive_recursion
(r : forall p : nat -> Type, p 0 -> (forall n, p n -> p (S n)) -> forall n, p n)
: Prop :=
  forall p x f n,
    let r := r p x f in
    r 0 = x /\
    r (S n) = f n (r n).

Goal primitive_recursion prec.
Proof.
  intros r x step n r0; auto. Qed.

Goal forall f g r x step n, primitive_recursion f -> primitive_recursion g ->
                       f r x step n = g r x step n.
  intros f g r x step; induction n; intros A B.
  - destruct (A r x step O) as [A' _]. destruct (B r x step O) as [B' _]. congruence.
  - destruct (A r x step n) as [_ A']. destruct (B r x step n) as [_ B']. rewrite A'.
    rewrite B'. f_equal. apply IHn; assumption.
Qed.

(* Exercise 4.4.4 *)
(* Definition nat_iteration (* ... *)

Goal nat_iteration Nat.iter.

(* Show uniqueness of the above specfication. *)
 *)

Check Nat.iter.

Definition nat_iteration (it : nat -> forall A : Type, (A -> A) -> A -> A) : Prop :=
  forall n A f x,
    it 0 A f x = x /\
    it (S n) A f x = f (it n A f x).

Goal nat_iteration Nat.iter.
  intros n A f x; auto. Qed.

Goal forall it it' n A f x, nat_iteration it -> nat_iteration it' ->
                       it n A f x = it' n A f x.
Proof.
  intros it it' n A f x H1 H2; induction n.
  - destruct (H1 O A f x) as [H1' _]. destruct (H2 O A f x) as [H2' _]. congruence.
  - destruct (H1 n A f x) as [_ H1']. destruct (H2 n A f x) as [_ H2']. congruence.
Qed.