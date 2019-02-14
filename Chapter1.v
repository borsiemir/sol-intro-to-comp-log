(** * Chapter 1: Types and Functions *)

(** * 1.1 Booleans *)

(* Commented because of naming conflicts with the Standard library: 
Inductive bool : Type :=
| true : bool
| false : bool.

Definition negb (x : bool) : bool :=
  match x with
    | true => false
    | false => true
  end. *)

Check negb.
(* negb : bool -> bool *)

Check negb (negb true).
(* negb (negb true) : bool *)

Compute negb (negb true).
(* = true : bool *)

Lemma L1 :
  negb true = false.
Proof.
  simpl. reflexivity.
Qed.

Lemma negb_negb (x : bool) :
  negb (negb x) = x.
Proof.
  destruct x.
  - reflexivity.
  - reflexivity.
Qed.

(* La demostración se puede simplificar: *)
Goal forall (x : bool), negb (negb x) = x.
Proof.
  destruct x ;  reflexivity.
Qed.

(* Commented because of naming conflicts with the Standard library: 
Definition andb (x y : bool) : bool :=
  match x with
    | true => y
    | false => false
  end. *)

Print andb.
(* andb = fun b1 b2 : bool => if b1 then b2 else false
        : bool -> bool -> bool*)

Lemma andb_com x y :
  andb x y = andb y x.
Proof.
  destruct x.
  - destruct y ; reflexivity.
  - destruct y ; reflexivity.
Qed.

Goal forall x y: bool,
       andb x y = andb y x.
Proof. destruct x, y; reflexivity. Qed.

(* Exercise 1.1.1 *)

(* 
Definition orb (x y: bool) :=
  match x with
    | true => true
    | false => y
  end. *)

Goal forall x y: bool,
       orb x y = orb y x.
Proof. destruct x, y; reflexivity. Qed. (* Es decir, distinguiendo todos los posibles casos *)

(* Formulate and prove the De Morgan Law. *)

Lemma DeMorgan x y:
  negb(orb x y) = andb (negb x) (negb y).
Proof. destruct x, y; reflexivity. Qed. (* Es decir, distiguiendo todos los posibles casos *)

(** * 1.2 Cascaded Functions *)

Check andb.
(* andb : bool -> bool -> bool *)

Check fun x : bool => x.
(* fun x : bool => x
     : bool -> bool *)

Compute (fun x : bool => x) true.
(* = true : bool *)

Check andb true.
(* andb true : bool -> bool *)

Compute andb true.
(* = fun b2 : bool => b2
     : bool -> bool *)

(* Commented because of naming conflicts with the Standard library: 
Definition andb : bool -> bool -> bool :=
  fun x : bool =>
    fun y : bool =>
      match x with
         | true => y
         | false => false
      end.
*)

Print negb.
(* negb = fun b : bool => if b then false else true
        : bool -> bool *)

Print andb.
(* andb = fun b1 b2 : bool => if b1 then b2 else false
        : bool -> bool -> bool *)

(** * 1.3 Natural Numbers *)

(* Commented because of naming conflicts with the Standard library: 
Inductive nat : Type :=
| O : nat
| S : nat -> nat.

Definition pred (x : nat) : nat :=
  match x with
    | O => O
    | S x' => x'
  end.
 *)

Print nat.
(* Inductive nat : Set :=  O : nat | S : nat -> nat *)

Print Nat.pred.
(* Nat.pred = fun n : nat => match n with
                                  | 0 => n
                                  | S u => u
                                  end
            : nat -> nat *)

Compute pred (S (S O)).
(* = 1 : nat *)

Set Printing All.

Compute pred (S (S O)).
(* = S O : nat *)

Unset Printing All.

(* Commented because of naming conflicts with the Standard library: 
Fixpoint plus (x y : nat) : nat :=
  match x with
    | O => y
    | S x' => S (plus x' y)
  end.
 *)

Print plus.
(* Notation plus := Nat.add *)

Print Nat.add.
(* Nat.add = fix add (n m : nat) {struct n} : nat := 
               match n with
                   | 0 => m
                   | S p => S (add p m)
                   end
           : nat -> nat -> nat *)

Compute plus (S O) (S O).
(* = 2 : nat *)

Fixpoint leb (x y: nat) : bool :=
  match x with
    | O => true
    | S x' => match y with
                | O => false
                | S y' => leb x' y'
              end
  end.

Fixpoint leb' (x y: nat) : bool :=
  match x, y with
    | O, _ => true
    | _, O => false
    | S x', S y' => leb' x' y'
  end.

(* Exercise 1.3.1 *)

(* 
Fixpoint mult (x y: nat) : nat := 
 match x with
  | O => O
  | S x' => plus y (mult x' y)
 end. *)

(* Definition of power *)
Fixpoint power (x y: nat) : nat :=
  match y with
    | O => S O (* Notemos que power 0 0 no esta definido, aqui le daremos el valor 1 *)
    | S y' => mult x (power x y')
  end.

Compute power 0 0.

Compute power 2 10.

(* Definition of fac *)

Fixpoint fac (x:nat) : nat :=
  match x with
    | O => S O
    | S x' => mult x (fac x')
  end.

Compute fac 3.

Compute fac 6.

(* Definition of evenb *)

Fixpoint evenb (x:nat) : bool :=
  match x with
    | O => true
    | S O => false
    | S (S x') => evenb x'
  end.

Compute evenb 7.

Compute evenb 346.

(* Definition of mod2 *)

Fixpoint mod2 (x:nat) : nat :=
  match x with
    | O => O
    | S O => S O
    | S (S x') => mod2 x'
  end.

Compute mod2 7.

Compute mod2 346. 

(* Definition of minus *)

Fixpoint minus (x y: nat) : nat :=
  match x, y with
    | _, O => x
    | O, _ => O
    | S x', S y' => minus x' y'
  end.

Compute minus 4 2.

Compute minus 2 4.

(* Definition of gtb *)

Fixpoint gtb (x y: nat) : bool :=
  match x, y with
    | O, _ => false
    | _, O => true
    | S x', S y' => gtb x' y'
  end.

Compute gtb 5 7.

Compute gtb 5 2.

Compute gtb 0 1.

(* Definition of eqb *)

Fixpoint eqb (x y:nat) : bool :=
  match x, y with
    | O, O => true
    | S x', S y' => eqb x' y'
    | _, _ => false
  end.

Compute eqb 0 0.

Compute eqb 42 24.

Compute eqb 30 30.

(** * 1.4 Structural Induction and Rewriting *)

Lemma plus_O x :
  plus x O = x.
Proof.
  induction x ; simpl.
  - reflexivity.
  - rewrite IHx. reflexivity.
Qed.

Lemma plus_S x y :
  plus x (S y) = S (plus x y).
Proof.
  induction x ; simpl.
  - reflexivity.
  - rewrite IHx. reflexivity.
Qed.

Lemma plus_com x y :
  plus x y = plus y x.
Proof.
  induction x ; simpl.
  - rewrite plus_O. reflexivity.
  - rewrite plus_S. rewrite IHx. reflexivity.
Qed.

Lemma plus_asso x y z :
  plus (plus x y) z = plus x (plus y z).
Proof.
  induction x ; simpl.
  - reflexivity.
  - rewrite IHx. reflexivity.
Qed.

(* Exercise 1.4.1 *)

Goal forall x y, plus x y = plus y x.
Proof.
  induction y.
  - rewrite plus_O. reflexivity.
  - rewrite plus_S. rewrite IHy. reflexivity.
Qed.

(** * 1.5 More on Rewriting *)

Require Import Omega.

Lemma plus_AC x y z :
  plus y (plus x z) = plus (plus z y) x.
Proof.
  setoid_rewrite plus_com at 3.
  setoid_rewrite plus_com at 1.
  apply plus_asso.
Qed.

(* Commented because of naming conflicts with the Standard library: 
Fixpoint mult (x y : nat) : nat :=
    match x with
    O => O
   | S x' => plus y (mult x' y)
    end. *)

Lemma plus_AC' x y z :
  plus (plus (mult x y) (mult x z)) (plus y z) =
  plus (plus (mult x y) y) (plus (mult x z) z).
Proof.
  rewrite plus_asso. rewrite plus_asso. f_equal.
  setoid_rewrite plus_com at 1. rewrite plus_asso. f_equal.
  apply plus_com.
Qed.

Example Ex1 x y z :
  S (plus x (plus y z)) = S (plus (plus x y) z).
Proof.
  rewrite <- plus_asso. reflexivity.
Qed.

(* Exercise 1.5.1 *)

Lemma mult_S' x y :
  mult x (S y) = plus (mult x y) x.
Proof.
  induction x.
  - reflexivity.
  - rewrite plus_S. simpl. f_equal. rewrite plus_asso. rewrite <- IHx. f_equal.
Qed.  (* Revisar para usar apply directamente sobre hipotesis *)

(* Exercise 1.5.2 *)
Lemma mult_O (x : nat) :
  mult x O = O.
Proof.
  induction x.
  - reflexivity.
  - simpl. apply IHx.
Qed.    

Lemma mult_S (x y : nat) :
  mult x (S y) = plus (mult x y) x.
Proof.
  induction x.
  - reflexivity.
  - rewrite plus_com. simpl. f_equal. 
    setoid_rewrite plus_com at 2. rewrite <- plus_assoc. f_equal.
    apply IHx.
Qed.

Lemma mult_com (x y : nat) :
  mult x y = mult y x.
Proof.
  induction x.
  - simpl; rewrite mult_O. reflexivity.
  - simpl. rewrite mult_S. setoid_rewrite plus_com at 2. f_equal. apply IHx.
Qed.

Lemma mult_dist (x y z: nat) :
  mult (plus x y) z = plus (mult x z) (mult y z).
Proof.
  induction x.
  - reflexivity.
  - simpl. rewrite plus_asso. f_equal. apply IHx.
Qed.

Lemma mult_asso (x y z: nat) :
  mult (mult x y) z = mult x (mult y z).
Proof.
  induction x.
  - reflexivity.
  - simpl. rewrite <- IHx. rewrite <- mult_dist. f_equal.
Qed.

(** * 1.6 Recursive Abstractions *)

Print plus.
(* Notation plus := Init.Nat.add *)

Print Init.Nat.add.
(* Init.Nat.add = 
   fix add (n m : nat) {struct n} : nat :=
     match n with
     | 0 => m
     | S p => S (add p m)
     end
        : nat -> nat -> nat *)

Compute plus O.
(* = fun m : nat => m
   : nat -> nat *)

Compute plus (S (S O)).
(* = fun m : nat => S (S m)
   : nat -> nat *)

Compute fun x => plus (S x).
(* = fun x m : nat =>
     S ((fix Ffix (x0 x1 : nat) {struct x0} : nat := 
       match x0 with
           | 0 => x1
           | S x2 => S (Ffix x2 x1)
           end) x m)
   : nat -> nat -> nat *)

Goal plus O = fun x => x.
Proof.
  compute. reflexivity.
Qed.

Goal (fun x => plus (S x)) = fun x y => S (plus x y).
Proof.
  compute. reflexivity.
Qed.

(** * 1.7 Defined Notations *)

(* Commented because of naming conflicts with the Standard library: 
Notation "x + y" := (plus x y)  (at level 50, left associativity).
Notation "x * y" := (mult x y) (at level 40, left associativity).
*)

Lemma mult_dist' x y z :
  x * (y + z) = x*y + x*z.
Proof.
  induction x ; simpl.
  - reflexivity.
  - rewrite IHx. rewrite plus_asso. rewrite plus_asso. f_equal.
    setoid_rewrite <- plus_asso at 2.
    setoid_rewrite plus_com at 4.
    symmetry. apply plus_asso.
Qed.

Set Printing All.

Check O + O * S O.
(* Init.Nat.add O (Init.Nat.mul O (S O)) : nat *)

Unset Printing All.

(* Exercise 1.7.1 *) (* Hacer despues copiar y pegar *)

Goal forall (x : nat),
  x * O = O.
Abort.

Goal forall x y: nat,
  x * (S y) = (x * y) + x.
Abort.

Goal forall x y: nat,
  x * y = y * x.
Abort.

Goal forall x y z: nat,
  (x + y) * z = (x * z) + (y * z).
Abort.

Goal forall x y z: nat,
  (x * y) * z = x * (y * z).
Abort.

(* Exercise 1.7.2 *)

Goal forall x y z: nat,
       x * (y * z) = x * y * z.
Proof.
  induction x.
  - reflexivity.
  - intros y z. simpl. rewrite IHx. setoid_rewrite mult_com at 4.
    rewrite mult_dist'. setoid_rewrite mult_com at 4. f_equal.
    setoid_rewrite mult_com at 3. reflexivity.
Qed.

(* Exercise 1.7.3 *)

Goal forall x,
       (x + x) + x = x + (x + x).
Proof.
  induction x.
  - reflexivity.
  - rewrite plus_S. rewrite plus_com. rewrite plus_S. rewrite plus_S.
    setoid_rewrite plus_com at 2. rewrite plus_S. rewrite plus_S. rewrite plus_S.
    setoid_rewrite plus_com at 4. rewrite plus_S. rewrite plus_S.
    setoid_rewrite plus_com at 3. rewrite plus_S. f_equal. f_equal. f_equal.
    symmetry. apply IHx.
Qed.

(** * 1.8 Standard Library *)

Set Printing All.

Check 2 + 3*2.
(* Init.Nat.add (S (S O)) (Init.Nat.mul (S (S (S O))) (S (S O)))
   : nat*)

Unset Printing All.

Locate "*".
(* Notation
   "x * y" := N.mul x y : N_scope
   "x * y" := Z.mul x y : Z_scope
   "x * y" := Init.Nat.mul x y : nat_scope (default interpretation)
   "x * y" := Pos.mul x y : positive_scope"x * y" := prod x y : type_scope
 *)

Set Printing All.

Check if false then 0 else 1.
(* match false return nat with
   | true => O
   | false => S O
   end
   : nat *)

Unset Printing All.

Goal forall x y z, (x + y) + z = x + (y + z).
Proof. intros x y z. omega. Qed.

Goal forall x y, 2 * (x + y) = (y + x) * 2.
Proof. intros x y. omega. Qed.

(** * 1.9 Pairs and Implicit Arguments *)

(* Commented because of naming conflicts with the Standard library: 
Inductive prod (X Y : Type) : Type :=
| pair : X -> Y -> prod X Y. 

Arguments pair {X} {Y} _ _. *)

Check pair 0 true.
(* (0, true) : nat * bool*)

Check @pair nat.
(* @pair nat : forall B : Type, nat -> B -> nat * B *)

Check @pair nat bool 0.
(* pair 0 : bool -> nat * bool *)

Set Printing All.

Check pair 0 true.
(* @pair nat bool O true : prod nat bool *)

Unset Printing All.

About pair.
(* pair : forall A B : Type, A -> B -> A * B
   
   pair is template universe polymorphic
   Arguments A, B are implicit and maximally inserted
   Argument scopes are [type_scope type_scope _ _]
   Expands to: Constructor Coq.Init.Datatypes.pair *)

Set Implicit Arguments.
Unset Strict Implicit.

(* Commented because of naming conflicts with the Standard library: 
Definition fst (X Y : Type) (p : prod X Y) : X :=
  match p with pair x _ => x end.

Definition snd (X Y : Type) (p : prod X Y) : Y :=
  match p with pair _ y => y end. *)

Compute fst (pair O true).
(* = 0 : nat *)

Compute snd (pair O true).
(* = true : bool*)

Lemma pair_eta (X Y : Type) (p : prod X Y) :
  pair (fst p) (snd p) = p.
Proof. destruct p as [x y]. simpl. reflexivity. Qed.

Definition swap (X Y : Type) (p : X * Y) : Y * X :=
  (snd p, fst p).

Compute swap (0, true).
(* = (true, 0) : bool * nat *)

Lemma swap_swap (X Y : Type) (p : X * Y) :
  swap (swap p) = p.
Proof.
  destruct p as [x y]. unfold swap. simpl. reflexivity.
Qed.

(* Se puede simplificar la demostración:*)
Goal forall (X Y : Type) (p : X * Y),
  swap (swap p) = p.
Proof.
  destruct p as [x y]. reflexivity.
Qed.

Check (fun x : nat * nat * nat => fst x) (1, 2, 3).
(* (fun x : nat * nat * nat => fst x) (1, 2, 3)
   : nat * nat *)

(* Exercise 1.9.1 *)

(* Definition car (* ... *)

Definition cas (* ... *)

Lemma car_spec X Y Z (f: X -> Y -> Z) x y:
  car f (x,y) = f x y.
Abort.

Lemma cas_spec X Y Z (f: X * Y -> Z) x y:
  cas f x y = f (x, y).
Abort. *)

Definition cas (X Y Z : Type) (f : (X * Y) -> Z) : X -> Y -> Z :=
  fun x: X =>
    fun y: Y =>
      f (x,y).

Definition car (X Y Z : Type) (f : X -> Y -> Z) : (X * Y) -> Z :=
  fun p: X * Y =>
    f (fst p) (snd p).

Lemma car_spec X Y Z (f: X -> Y -> Z) x y:
  car f (x,y) = f x y.
Proof.
  reflexivity.
Qed.

Lemma cas_spec X Y Z (f: X * Y -> Z) x y:
  cas f x y = f (x, y).
Proof.
  reflexivity.
Qed.

(** * 1.10 Lists *)
 
(* Commented because of naming conflicts with the Standard library: 
Inductive list (X : Type) : Type :=
| nil : list X
| cons : X -> list X -> list X. 

Arguments nil {X}. *)

Set Printing All.

Check cons 1 nil.
(* (fun x : nat * nat * nat => fst x) (1, 2, 3)
   : nat * nat *)

Unset Printing All.

Notation "x :: y" := (cons x y) (at level 60, right associativity).

Set Printing All.

Check 1 :: 2 :: nil.
(* @cons nat (S O) (@cons nat (S (S O)) (@nil nat))
   : list nat *)

Unset Printing All.

Notation "[]" := nil.
Notation "[ x ]" := (cons x nil).
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Set Printing All.

Check [1;2].
(* @cons nat (S O) (@cons nat (S (S O)) (@nil nat))
   : list nat *)

Unset Printing All.

(* The following tends to crash CoqIDE.
   Toggle View -> Display all low-level contents instead! *)
(* Unset Printing All. *)

(* Comentado ya que ya esta definido
Fixpoint length (X : Type) (A : list X) : nat :=
  match A with
    | nil     => O
    | _ :: A' => S (length A')
  end.
*)

Notation "| A |" := (length A) (at level 70).

(* Comentado ya que ya esta definido
Fixpoint app (X : Type) (A B : list X) : list X :=
  match A with
    | nil     => B
    | x :: A' => x :: app A' B
  end.
 *)

Notation "x ++ y" := (app x y) (at level 60, right associativity).

Fixpoint rev (X : Type) (A : list X) : list X :=
  match A with
    | nil     => nil
    | x :: A' => rev A' ++ [x]
  end.


Compute rev [1;2;3].
(* = [3; 2; 1] : list nat *)

Lemma app_nil (X : Type) (A : list X) :
  A ++ nil = A.
Proof.
  induction A as [|x A] ; simpl.
  - reflexivity.
  - rewrite IHA. reflexivity.
Qed.

(* Enabling these lines will mess things up in this file, 
   because we've defined many of the names that it imports.
   In order to avoid confusion, don't enable them. *)
(*
Require Import List.
Import ListNotations.
*)

(* Exercise 1.10.1 *)

(* Needed for section 1.11 *)
Lemma app_assoc (X : Type) (A B C : list X) :
  (A ++ B) ++ C = A ++ (B ++ C).
Proof.
  induction A as [|x A]; simpl.
  - reflexivity. 
  - f_equal. apply IHA.
Qed.
  
Lemma length_app (X : Type) (A B : list X) :
  |A ++ B| = |A| + |B|.
Proof.
  induction A as [|x A].
  - reflexivity.
  - simpl. f_equal. apply IHA.
Qed.

Lemma rev_app (X : Type) (A B : list X) :
  rev (A ++ B) = rev B ++ rev A.
Proof.
  induction A as [|x A]; simpl.
  - symmetry. apply app_nil.
  - rewrite IHA. apply app_assoc.
Qed.
    
Lemma rev_rev (X : Type) (A : list X) :
  rev (rev A) = A.
Proof.
  induction A as [|x A]; simpl.
  - reflexivity.
  - rewrite rev_app. simpl. f_equal. apply IHA.
Qed.

(** * 1.11 Quantified Inductive Hypotheses *)

Fixpoint revi (X : Type) (A B : list X) : list X :=
  match A with
    | nil     => B
    | x :: A' => revi A' (x :: B)
  end.

Lemma revi_rev (X : Type) (A B : list X) :
  revi A B = rev A ++ B.
Proof.
  revert B. induction A as [|x A] ; simpl.
  - reflexivity.
  - intros B. rewrite IHA. rewrite app_assoc. simpl. reflexivity.
Qed.

(* Exercise 1.11.1 *)

Lemma rev_revi (X : Type) (A : list X) :
  rev A = revi A nil.
Proof.
  induction A as [|x A]; simpl.
  - reflexivity.
  - symmetry. apply revi_rev.
Qed.

(* Exercise 1.11.2 *)

Fixpoint lengthi (X : Type) (A : list X) (n : nat) :=
  match A with
    | nil => n
    | _ :: A' => lengthi A' (S n)
  end.

Lemma lengthi_length X (A : list X) n :
  lengthi A n = |A| + n.
Proof.
  revert n; induction A as [|x A]; simpl.
  - reflexivity.
  - intro n. rewrite IHA. simpl. apply plus_S.
Qed.  

Lemma length_lengthi X (A : list X) :
  |A| = lengthi A 0.
Proof.
  symmetry. rewrite <- plus_O. apply lengthi_length.
Qed.

(* Exercise 1.11.3 *)

(* Fixpoint fact (n : nat) : nat :=
(* ... *)

Fixpoint facti (n a: nat) : nat := 
(* ... *)

Goal forall n, fact n = facti n 1. *)

(* fact ya esta definido *)

Compute fact 5. 

Fixpoint facti (n a: nat) : nat :=
  match n with
    | O => a
    | S n' => facti n' (a * S n')
end.

Lemma mult_1 (n :nat) :
  1 * n = n.
Proof.
  destruct n; simpl.
  - reflexivity.
  - f_equal. apply plus_O.
Qed.

Lemma mult_plus (n m:nat) :
  m + n * m = S n * m.
Proof.
  destruct m; simpl; f_equal; reflexivity.
Qed.
   
Lemma facti_fact (n m:nat) :
  facti n m  = m * fact n.
Proof.
  revert m; induction n; simpl.
  - intro m. rewrite mult_com. symmetry. apply mult_1.
  - intro m. setoid_rewrite mult_com at 2. rewrite mult_dist. rewrite IHn.
    rewrite mult_com. rewrite  mult_assoc. rewrite mult_S. rewrite plus_com.
    f_equal. rewrite mult_com. rewrite mult_assoc. reflexivity.
Qed.

(** * 1.12 Iteration as Polymorphic Higher-Order Function *)

Fixpoint iter (n : nat) (X : Type) (f : X -> X) (x : X) : X :=
  match n with
    | 0    => x
    | S n' => f (iter n' f x)
  end.

Lemma iter_plus x y :
  x + y = iter x S y.
Proof. induction x;  simpl; congruence. Qed.

Lemma iter_minus x y :
  x-y = iter y pred x.
Proof. induction y ; simpl ; omega. Qed.

(* Exercise 1.12.1 *)

Lemma iter_mult x y :
  x * y = iter x (plus y) 0.
Proof.
  induction x; simpl; congruence.
Qed.

(* Exercise 1.12.2 *)

Lemma iter_shift X (f : X -> X) x n :
  iter (S n) f x = iter n f (f x).
Proof.
  induction n; simpl.
  - reflexivity.
  - f_equal. rewrite <- IHn. simpl. reflexivity.
Qed.

(* Exercise 1.12.3 *)

(* Fixpoint power (x n: nat) := 
(* ... *) Definido atras.

Lemma iter_power x n:
  power x n = iter n (mult x) 1. *)

Lemma iter_power x n:
  power x n = iter n (mult x) 1.
Proof.
  induction n; simpl; congruence.
Qed.
  
(* Exercise 1.12.4 *)

(* Definition*)

Definition step (p : nat * nat) : nat * nat :=
  match p with
    | (n, x) => (S n, S n * x)
end. 

  
Lemma it_fac_step n :
  step (n, fac n) = (S n, fac (S n)).
Proof.
  induction n; reflexivity. 
Qed.

Lemma it_fac' n : 
  iter n step (O, S O) = (n, fac n).
Proof.
  induction n.
  - reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.
    
Lemma it_fac n :  
  fac n = snd (iter n step (O, S O)).
Proof.
  rewrite it_fac'. reflexivity.
Qed.


(* Exercise 1.12.5 *)
Definition Nat := forall X: Type, (X -> X) -> X -> X.

Definition encode (n: nat) : Nat :=
  iter n.

Definition decode (N: Nat) : nat :=
  N nat S 0.

Goal forall n: nat,
         decode (encode n) = n.
Proof.
  induction n.
  - reflexivity.
  - unfold encode. unfold decode. simpl. f_equal. apply IHn.
Qed.
    
(** * 1.13 Options and Finite Types *)

Inductive Empty_set : Type := .

Lemma vacuous_truth (x : Empty_set) :
  1 = 2.
Proof. destruct x. Qed.

Inductive option (X : Type) : Type :=
| Some : X -> option X
| None : option X.

Arguments None {X}.

Definition fin (n : nat) : Type :=
  Nat.iter n option Empty_set.

Definition a11 : fin 1 := @None Empty_set.
Definition a21 : fin 2 := Some a11.
Definition a22 : fin 2 := @None (fin 1).
Definition a31 : fin 3 := Some a21.
Definition a32 : fin 3 := Some a22.
Definition a33 : fin 3 := @None (fin 2).

Goal forall n, fin (2+n) = option (fin (S n)).
Proof. intros n. reflexivity. Qed.

Goal forall m n, fin (m+n) = fin (n+m).
Proof.
  intros m n. f_equal. omega.
Qed.

(* For Coq to get typing right, we had to replace None by a11 in this lemma: *)
Lemma fin1 (x : fin 1):
  x = a11.
Proof.
  destruct x as [x|].
  - simpl in x. destruct x.
  - reflexivity.
Qed.

(* Exercise 1.13.1 *)

Definition fromBool (b: bool) : fin 2 :=
  match b with
    | true => a21
    | false => a22
end.
    
Definition toBool (x: fin 2) : bool :=
  match x with
    | Some _ => true
    | _ => false            
end.

Lemma bool_fin b: toBool (fromBool b) = b.
Proof.
  destruct b; reflexivity.
Qed.

Lemma fin_bool x: fromBool (toBool x) = x.
Proof.
  destruct x.
  - simpl. unfold a21. f_equal. rewrite fin1. reflexivity.
  - simpl. unfold a22. f_equal.
Qed.

(* Exercise 1.13.2 *)

Definition fromNat (n: nat) : option nat :=
  match n with
    | O => None
    | S n => Some n
end.

Definition toNat (n: option nat) : nat :=
  match n with
    | None => O
    | Some n' => S n'
end.

    
Goal forall n, toNat (fromNat n) = n.
Proof.
  induction n; reflexivity.
Qed.

Goal forall n, fromNat (toNat n) = n.
 induction n; reflexivity.
Qed.

(* Exercise 1.13.3*)

Fixpoint find (X: Type) (p: X -> bool) (A: list X) : option X :=
  match A with
    | [] => None
    | x :: A' => if p x then Some x else find p A'
end.

Fixpoint  minus_opt (x y: nat) : option nat :=
  match  x, y with
    | _, O => Some x
    | O, _ => None
    | S x', S y' => minus_opt x' y'
end.

(** * 1.14 More about Functions *)
Check forall x : nat, nat.
(* nat -> nat : Set *)
