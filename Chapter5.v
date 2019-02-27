(** * Chapter 5: Truth value semantics and elim restriction *)

Require Import Base.

(* Definitions from earlier chapters: *)

Definition XM : Prop := forall X : Prop, X \/ ~X.
Definition surjective (X Y : Type) (f : X -> Y) : Prop := forall y, exists x, f x = y.

(** * 5.1 Truth Value Semantics *)

Definition TVS : Prop := forall X : Prop, X=True \/ X=False.

Goal TVS -> XM.
Proof.
  intros A X. destruct (A X) as [B|B]; rewrite B ; auto.
Qed.

Definition PI : Prop := forall (X : Prop) (A B : X), A=B.

Goal TVS -> PI.
Proof.
  intros A X B C. destruct (A X) ; subst X.
  - destruct B, C. reflexivity.
  - contradiction B.
Qed.

Definition PE : Prop := forall X Y : Prop, (X <-> Y) -> X=Y.

Goal TVS -> PE.
Proof.
  intros A X Y B. destruct (A X), (A Y) ; subst X Y ; tauto.
Qed.

Goal XM -> PE -> TVS.
Proof.
  intros xm pe X. destruct (xm X) as [A|A].
  - left. apply pe. tauto.
  - right. apply pe. tauto.
Qed.

(* Exercise 5.1.1 *)
Goal TVS <-> XM /\ PE.
Proof.
  split.
  - split.
    + intros X. destruct (H X) as [B|B]; rewrite B; tauto.
    + intros X Y H1. destruct (H X) as [B|B], (H Y) as [C|C]; subst X Y; tauto.
  - intros [xm pe] X. destruct (xm X) as [H|H].
    + left. apply pe. tauto.
    + right. apply pe. tauto.
Qed.

(* Exercise 5.1.2 *)
Goal TVS -> PE.
Proof.
  intros tvs X Y xy. destruct (tvs X) as [A|A], (tvs Y) as [B|B];
  rewrite A; rewrite B; rewrite A in xy; rewrite B in xy; tauto.
Qed.

(** *  5.2 Elim Restriction *)

Goal forall X (f : X -> bool), surjective f -> exists x y : X, x <> y.
Proof.
  intros X f A. destruct (A true) as [x B]. destruct (A false) as [y C].
  exists x, y. congruence.
Qed.

Inductive bp : Prop := P1 : bp | P2 : bp.

(* This Check produced an "Incorrect elimination" error, because the function violates the elim restriction:
Check fun x : bp => match x with P1 => true | P2 => false end. *)

Lemma Prop_Skolem (X : Type) (Y : Prop) (p : X -> Y -> Prop) :
  (forall x, exists y, p x y) -> exists f, forall x, p x (f x).
Proof.
 intros A.
 exists (fun x => let (y,_) := A x in y).
 intros x.
 destruct (A x) as [y B].
 exact B.
Qed.

(* Exercise 5.2.1 *)
Goal (forall X: Type, X = True \/ X = False) -> False.
Proof.
  intros H. specialize (H bool). (* Aqui falla para TVS *) destruct H.
  - pose (p X := forall x y : X, x = y).
    assert (A: ~ (p bool)). { intros B. specialize (B false true). discriminate B. }
    apply A. rewrite H. intros x y. destruct x, y. reflexivity.
  - pose (p X := forall x : X, x <> x).
    assert (A: ~ p bool). { intros B. specialize (B true). apply B. reflexivity. }
    apply A. rewrite H. intros x. destruct x. Qed.

(** * 5.3 Propositional Extensionality Entails Proof Irrelevance *)

Lemma sur_fixpoint X Y (f : X -> X -> Y) (g : Y -> Y) :
  surjective f -> exists y, g y = y.
Proof.
  intros A.
  pose (h x := g (f x x)).
  destruct (A h) as [x B].
  exists (h x). unfold h at 2. rewrite <- B. reflexivity.
Qed.

Goal PE -> PI.
Proof.
  intros pe.
  cut (P1=P2).
  { intros A X B C.
    change (B = match P1 with P1 => C | P2 => B end).
    rewrite A. reflexivity. }
  pose (neg x := match x with P1 => P2 | P2 => P1 end).
  cut (exists P, neg P = P).
  { unfold neg. intros [[|] C].
    - symmetry. exact C.
    - exact C. }
  cut (exists f : bp -> bp -> bp, surjective f).
  { intros [f A]. apply (sur_fixpoint (f:=f)). exact A. }
  cut (bp = (bp -> bp)).
  { intros A. rewrite <- A. exists (fun x => x). intros x. exists x. reflexivity. }
  apply pe. split ; auto using P1.
Qed.

(* Exercise 5.3.1 *)
Lemma Cantor X :
  ~ exists f : X -> X -> Prop, surjective f.
Proof.
  intros [f sur]. cut (exists y : Prop, (~ y) = y).
  { intros [y abs]. assert (~ y <-> y). { split; rewrite abs; auto. } tauto. }
  apply (@sur_fixpoint X Prop f). assumption.
Qed.

(* Exercise 5.3.2 *)
Definition iso (X Y : Type) : Prop :=
  exists f : X -> Y, exists g : Y -> X, forall x y, g (f x) = x /\ f (g y) = y.

Definition PU : Prop := forall X Y : Prop, iso X Y -> X = Y.

Goal PE <-> PU /\ PI.
Proof.
  split.
  - intros pe; split.
    + intros X Y [f [g H]]. apply pe. split.
      * intros x. exact (f x).
      * intros y. exact (g y).
    + apply Unnamed_thm7; assumption.
  - intros [pu pi].    intros X Y [f g]. apply pu. exists f; exists g.
    intros x y. split; apply pi. Qed.

(** * 5.4 A Simpler Proof *)
Goal PE -> PI.
intros D X E F.
assert (C: X=True) by (apply D; tauto).
subst. destruct E, F. reflexivity.
Qed.

(* Exercise 5.4.1 *)
Goal PE -> forall X:Prop, X -> X = True.
Proof.
  intros pe x H. apply pe; tauto. Qed.

Goal (forall X:Prop, X -> X = True) -> P1 = P2.
Proof.
  intros H. assert (A: bp = True) by (apply H; exact P1).
  assert (B: forall x y : bp, x = y).
  { rewrite A. destruct x, y; reflexivity. }
  apply B. Qed.
  
  
  

