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
  - destruct y.
    + simpl. reflexivity.
    + reflexivity.
  - destruct y ; reflexivity.
Qed.

Goal forall x y: bool,
       andb x y = andb y x.
Proof. destruct x, y; reflexivity. Qed.

(* Exercise 1.1.1 *)

(* Definition orb (x y: bool) :=
  match x with
     | true => true
     | false => y
   end. *)

Goal forall x y: bool,
    orb x y = orb y x.
Proof.
  destruct x.
  - destruct y; reflexivity.
  - destruct y; reflexivity.
Qed.
(* Formulate and prove the De Morgan Law. *)
Lemma DMor_1 (x y: bool) :
    negb (orb x y) = andb (negb x) (negb y).
Proof.
  destruct x.
  - destruct y.
    + simpl. reflexivity.
    + simpl. reflexivity.
  - destruct y.
    + simpl. reflexivity.
    + simpl. reflexivity.
Qed.

(* Más compacto:

   destruct x
   - destruct y; reflexivity.
   - destruct y; reflexivity.
Qed. *)


Lemma DMor_2 (x y: bool) :
  negb (andb x y) = orb (negb x) (negb y).
Proof.
  destruct x.
  - destruct y; reflexivity.
  - destruct y; reflexivity.
Qed.
         


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
Definition mult (x y: nat) : nat := 
 match x with
| 0 => 0
| S x' => plus y (mult x' y)
end.
  *)  

(* Exercise 1.3.2 *)

(* Definition of power*)
Fixpoint power (x n: nat) : nat :=
   match n with
   | 0 => S 0
   | S n' => mult x (power x n')
   end.             

(*Definition of fac*)
Fixpoint fac (n: nat) : nat :=
  match n with
  | 0 => S 0
  | S n' => mult n (fac n')
  end.

(*Definition of evenb*)
Fixpoint evenb (n: nat) : bool :=
  match n with
  | 0 => true
  | S 0 => false
  | S (S n') => evenb n'
  end.

(*Definition of mod2*)
Fixpoint mod2 (n: nat) : nat :=
  match n with
  | 0 => 0
  | S 0 => S 0
  | S (S n') => mod2 n'
    end.

(*Definition of minus*)
Fixpoint minus (x y : nat) : nat :=
  match y with
  | 0 => x
  | S y' => match x with
            | 0 => 0
            | S x' => minus x' y' 
            end  
  end.

(*Si y>x entonces definimos la resta como 0*)

(*Definition of gtb*)
Fixpoint gtb (x y: nat) : bool :=
  match x with
  | 0  => false
  | S x' => match y with
            | 0 => true
            | S y' => gtb x' y'
            end
  end.

(*Definition of eqb*)
Fixpoint eqb (x y: nat) : bool :=
  match x with
  | 0 => match y with
         | 0 => true
         | _ => false
         end
  | S x' => match y with
            | 0 => false
            | S y' => eqb x' y'
            end
  end.


(** * 1.4 Structural Induction and Rewriting *)

Lemma plus_O x :
  plus x O = x.
Proof.
  induction x.
  - reflexivity.
  - simpl. rewrite IHx. reflexivity.
Qed.
     
 (* induction x ; simpl.
  - reflexivity.
  - rewrite IHx. reflexivity.
Qed.*)

Lemma plus_S x y :
  plus x (S y) = S (plus x y).
Proof.
  induction x. simpl.
  - reflexivity.
  - simpl. rewrite <- IHx. reflexivity.
    Qed.

  (*induction x ; simpl.
  - reflexivity.
  - rewrite IHx. reflexivity.
Qed.
   *)


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
  induction y; simpl.
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
  induction x. simpl.
  - reflexivity.
  - rewrite plus_com. simpl. f_equal. rewrite plus_com. rewrite IHx. setoid_rewrite plus_com at 4.
    setoid_rewrite plus_com at 1. rewrite <- plus_asso. setoid_rewrite plus_com at 4. apply plus_com.
Qed.

(****Reducir más****)
                          
(* Exercise 1.5.2 *)
Lemma mult_O (x : nat) :
  mult x O = O.
Proof.
  induction x. simpl.
  - reflexivity.
  - simpl. rewrite IHx. reflexivity.
Qed.


  Lemma mult_S (x y : nat) :
  mult x (S y) = plus (mult x y) x.
  Proof.
    induction x. simpl. 
    - reflexivity.
    - rewrite plus_com. simpl. f_equal. rewrite plus_com. rewrite IHx. setoid_rewrite plus_com at 4.
    setoid_rewrite plus_com at 1. rewrite <- plus_asso. setoid_rewrite plus_com at 4. apply plus_com.
Qed.
  (****Reducir más****)

  
Lemma mult_com (x y : nat) :
  mult x y = mult y x.
Proof.
  induction x. simpl.
  - rewrite mult_O. reflexivity.
  - simpl. rewrite mult_S. rewrite IHx. apply plus_com.
Qed.

    
Lemma mult_dist (x y z: nat) :
  mult (plus x y) z = plus (mult x z) (mult y z).
Proof.
  induction x. simpl.
  - rewrite mult_com. reflexivity.
  - simpl. rewrite IHx. rewrite plus_asso. reflexivity.
Qed.


Lemma mult_asso (x y z: nat) :
  mult (mult x y) z = mult x (mult y z).
Proof.
  induction x. simpl.
  - reflexivity.
  - simpl. rewrite <- IHx. rewrite <- mult_dist. reflexivity.
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

(* Exercise 1.7.1 *)

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
Abort.

(* Exercise 1.7.3 *)

Goal forall x,
       (x + x) + x = x + (x + x).
Proof.
  induction x.
  Restart.
Abort.

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

Fixpoint length (X : Type) (A : list X) : nat :=
  match A with
    | nil     => O
    | _ :: A' => S (length A')
  end.

Notation "| A |" := (length A) (at level 70).

Fixpoint app (X : Type) (A B : list X) : list X :=
  match A with
    | nil     => B
    | x :: A' => x :: app A' B
  end.

Notation "x ++ y" := (app x y) (at level 60, right associativity).

Fixpoint rev (X : Type) (A : list X) : list X :=
  match A with
    | nil     => nil
    | x :: A' => rev A' ++ [x]
  end.

Compute rev [1;2;3].
(* = [3; 2; 1] : list nat *)



(* Enabling these lines will mess things up in this file, 
   because we've defined many of the names that it imports.
   In order to avoid confusion, don't enable them. *)

Require Import List.
Import ListNotations.


Lemma app_nil (X : Type) (A : list X) :
  A ++ nil = A.
Proof.
  induction A as [|x A] ; simpl.
  - reflexivity.
  - rewrite IHA. reflexivity.
Qed.

(* Inserto aquí este lema para que 
no entre en conflicto con las 
definiciones anteriores y la librería *)



(* Exercise 1.10.1 *)

(* Needed for section 1.11 *)
Lemma app_assoc (X : Type) (A B C : list X) :
  (A ++ B) ++ C = A ++ (B ++ C).
Proof.
  induction A as [| x A]. simpl.
  - reflexivity.
  - simpl. rewrite <- IHA. reflexivity.
Qed.

Lemma length_app (X : Type) (A B : list X) :
  |A ++ B| = |A| + |B|.
Proof.
  induction A as [| x A]. simpl.
  - reflexivity.
  - simpl. f_equal. rewrite IHA. reflexivity.
    Qed.



Lemma rev_app (X : Type) (A B : list X) :
  rev (A ++ B) = rev B ++ rev A.
Proof.
  induction A as [| x A]. simpl.
  - rewrite app_nil. reflexivity.
  - simpl. rewrite IHA. rewrite app_assoc. reflexivity.
    Qed.

Lemma rev_rev (X : Type) (A : list X) :
  rev (rev A) = A.
Proof.
  induction A as [| x A]. simpl.
  - reflexivity.
  - simpl. rewrite rev_app. simpl. rewrite IHA. reflexivity.
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
 revert B.  induction A as [|x A] ; simpl.
  - reflexivity.
  - intros B. rewrite IHA. rewrite app_assoc. simpl. reflexivity.
Qed.

(* Exercise 1.11.1 *)

Lemma rev_revi (X : Type) (A : list X) :
  rev A = revi A nil.
Proof. rewrite revi_rev. rewrite app_nil. reflexivity.
       Qed.

(* Exercise 1.11.2 *)

Fixpoint lengthi (X : Type) (A : list X) (n : nat) :=
  match A with
    | nil => n
    | _ :: A' => lengthi A' (S n)
  end.

Lemma lengthi_length X (A : list X) n :
  lengthi A n = |A| + n.
Proof. revert n. induction A as [| x A]; simpl.
       - reflexivity.
       - intros n. rewrite IHA. omega.
         Qed.
  
Lemma length_lengthi X (A : list X) :
  |A| = lengthi A 0.
Proof. rewrite lengthi_length. rewrite plus_O. reflexivity.
       Qed.
       
(* Exercise 1.11.3 *)

(* Fixpoint fact (n : nat) : nat :=
(* ... *)

Fixpoint facti (n a: nat) : nat := 
(* ... *)

Goal forall n, fact n = facti n 1. *)

(** * 1.12 Iteration as Polymorphic Higher-Order Function *)

Fixpoint iter (n : nat) (X : Type) (f : X -> X) (x : X) : X :=
  match n with
    | 0    => x
    | S n' => f (iter n' f x)
  end.

Lemma iter_plus x y :
  x + y = iter x S y.
Proof. induction x ; simpl ; congruence. Qed.

Lemma iter_minus x y :
  x-y = iter y pred x.
Proof. induction y ; simpl ; omega. Qed.

(* Exercise 1.12.1 *)

Lemma iter_mult x y :
  x * y = iter x (plus y) 0.
Proof.
  induction x; simpl.
  - reflexivity.
  - rewrite IHx. reflexivity. 
Qed.



(* Exercise 1.12.2 *)

Lemma iter_shift X (f : X -> X) x n :
  iter (S n) f x = iter n f (f x).
Proof.
  induction n; simpl.
  - reflexivity.
  - rewrite <- IHn. reflexivity.
Qed.

  
(* Exercise 1.12.3 *)
(*
Fixpoint power (x n: nat) := 
 match n with
 | 0 => S 0
 | S n' => mult x (power x n')
end.
 *)


Lemma iter_power (x n: nat) :
  power x n = iter n (mult x) 1.
Proof.
  induction n; simpl.
  - reflexivity.
  - f_equal. rewrite IHn. reflexivity.
Qed. 


(* Exercise 1.12.4 *)

Definition step (p : nat * nat) : nat * nat :=
  match p with (x, y) => (S x, S x * y)
end.

Compute step (2,2).

Lemma it_fac_step n :
  step (n, fac n) = (S n, fac (S n)).
Proof.
  induction n; simpl.
  - reflexivity.
  - reflexivity.
Qed.


Lemma it_fac' n : 
  iter n step (O, S O) = (n, fac n).
Proof.
  induction n; simpl.
  - reflexivity.
  - rewrite IHn. reflexivity.
Qed.

Lemma it_fac n :  
  fac n = snd (iter n step (O, S O)).
Proof.
  induction n; simpl.
  - reflexivity.
  - rewrite it_fac'. simpl. reflexivity.
    Qed.


    
(* Exercise 1.12.5 *)
Definition Nat := forall X: Type, (X -> X) -> X -> X.

(* Fixpoint encode (n: nat) : Nat :=
  (* ... *)

Definition decode (N: Nat) : nat :=
  (* ... *)

Goal forall n: nat,
         decode (encode n) = n.
Abort. *)

(** * 1.13 Options and Finite Types *)

Inductive Empty_set : Type := .

Lemma vacuous_truth (x : Empty_set) :
  1 = 2.
Proof. destruct x. Qed.

Inductive option (X : Type) : Type :=
| Some : X -> option X
| None : option X.


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
  | false => a22
  | true => a21
end.

Definition toBool (x: fin 2) : bool :=
  match x with
  | None _ => false
  | _ => true
  end.

Lemma bool_fin b: toBool (fromBool b) = b.
Proof.
  destruct b; reflexivity.
Qed.

Lemma fin_bool x: fromBool (toBool x) = x.
Proof.
  destruct x.
  - simpl in f. simpl. unfold a21. f_equal. rewrite fin1. reflexivity.
  - (*simpl. y por definición*) reflexivity.
Qed.
  
(* Exercise 1.13.2 *)

Check @None nat.
About None.

Arguments None {X}.
About None.

Definition fromNat (n: nat) : option nat :=
  match n with
  | 0 => None
  | S n => Some n
  end.
                 

Definition toNat (n: option nat) : nat :=
  match n with
  | None => 0
  | Some n => S n
  end.

Goal forall n, toNat (fromNat n) = n.
Proof. 
  destruct n; simpl.
  - reflexivity.
  - reflexivity.
    Qed.
  
Goal forall n, fromNat (toNat n) = n.
Proof.
  destruct n; reflexivity.
Qed.


(* Exercise 1.13.3*)


Fixpoint find (X: Type) (p: X -> bool) (A: list X) : option X :=
  match A with
  | nil => None
  | x :: A' => if p x then Some x
               else find p A'
  end.


Fixpoint minus_opt (x y: nat) : option nat :=
  match x, y with
  | _, 0 => Some x
  | 0, _  => None
  | S x', S y' => minus_opt x' y'
  end.



(** * 1.14 More about Functions *)
Check forall x : nat, nat.
(* nat -> nat : Set *)
