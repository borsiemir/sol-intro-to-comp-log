(** * Chapter 9 - Syntactic Unification *)

Require Export Base.

(** * 9.1 Terms, substitution and unifiers *)

Definition var := nat.

Inductive ter : Type :=
| V : var -> ter
| T : ter -> ter -> ter.

Definition eqn := prod ter ter.

Implicit Types x y z : var.
Implicit Types s t u v : ter.
Implicit Types e : eqn.
Implicit Types A B C : list eqn.
Implicit Types sigma tau : ter -> ter.
Implicit Types m n k : nat.

Definition subst sigma : Prop :=
  forall s t, sigma (T s t) = T (sigma s) (sigma t).

Definition unif sigma A : Prop :=
  subst sigma /\ forall s t, (s, t) el A ->  sigma s = sigma t.

Definition unifiable A : Prop :=
  exists sigma, unif sigma A.

Definition principal_unifier sigma A : Prop :=
  unif sigma A /\ forall tau, unif tau A -> forall s, tau (sigma s) = tau s.

(* Excercise 9.1.1 *)

Lemma subst_var sigma tau :
  subst sigma -> subst tau ->
  (forall n, sigma (V n) = tau (V n)) ->
  forall s, sigma s = tau s.
Proof.
  intros H1 H2 H3. induction s as [n |s IHs t IHt].
  - apply H3.
  - specialize (H1 s); specialize (H1 t); specialize (H2 s); specialize (H2 t).
    rewrite H1; rewrite H2. rewrite IHs; rewrite IHt. reflexivity. Qed.

(* Exercise 9.1.2 *)

Lemma princ_uni_idem sigma :
  (exists A,  principal_unifier sigma A) -> forall s, sigma (sigma s) = sigma s.
Proof.
  intros [A [H1 H3]] s. apply H3. assumption. Qed.

(* Exercise 9.1.3 *)

Lemma unif_cons sigma :
  forall s t A, unif sigma ((s, t) :: A) <-> (sigma s = sigma t /\ unif sigma A).
Proof.
  intros s t A; split; intros [H1 H2].
  - split.
    + auto. 
    + split; auto.
  - split.
    + destruct H2 as [H2 _]. assumption.
    + intros u v [H3|H3].
      * congruence.
      * destruct H1 as [_ H1]. destruct H2 as [_ H2]. auto.
Qed.

Lemma unif_app sigma :
  forall A B, unif sigma (A ++ B) <-> unif sigma A /\ unif sigma B.
Proof.
  induction A; simpl; intros B; split; intros [H1 H2].
  - split; split; auto. intros s t H3; destruct H3.
  - exact H2.
  - split.
    + destruct a as (s, t). apply unif_cons. split; auto.
      specialize (IHA B); destruct IHA as [IHA _]. apply IHA. split; auto.
    + apply IHA. split; auto.
  - destruct H1 as [_ H1]; destruct H2 as [H2 H3]. split; try assumption.
    intros s t H4. destruct H4; subst.
    + apply H1. auto.
    + apply in_app_iff in H as [H|H]; auto.
Qed.

(* Exercise 9.1.4 *)

Lemma non_unif_sub A :
  ~ unifiable A -> exists B, B <<= A /\ ~ unifiable A.
Proof.
  intros H1. exists A. auto. Qed.

(** 9.2 Solved Equation Lists *)

Fixpoint FV_term s : list var :=
  match s with
  | V x => [x]
  | T s t => FV_term s ++ FV_term t
  end.

Fixpoint FV_eqn A : list var :=
  match A with
  | [] => []
  | (s, t) :: A => FV_term s ++ FV_term t ++ FV_eqn A
  end.

Fixpoint Dom_eqn A : list var :=
  match A with
  | [] => []
  | (s, t) :: A => match s with
                 | V x => x :: Dom_eqn A
                 | _ => []
                 end
  end.

Inductive solved : list eqn -> Prop :=
| solv_nil : solved []
| solv_S x s A : ~ x el (FV_term s) -> ~ x el (Dom_eqn A) ->
                 disjoint (FV_term s) (Dom_eqn A) -> solved A ->
                 solved ((V x, s) :: A).

Fixpoint vrep_t s x t : ter :=
  match s with
  | V y => if decision (y = x) then t else V y
  | T s1 s2 => T (vrep_t s1 x t) (vrep_t s2 x t)
  end.

Fixpoint vrep_e A x t : list eqn :=
  match A with
  | [] => []
  | (s1, s2) :: A => (vrep_t s1 x t, vrep_t s2 x t) :: (vrep_e A x t)
  end.

Fixpoint phi A s : ter :=
  match A with
  | [] => s
  | (V x, t) :: A => vrep_t (phi A s) x t
  | (T _ _, _) :: A => s
  end.

(* Exercise 9.2.3 *)

Lemma noFV_vrep_t s x t :
  ~ x el FV_term s -> vrep_t s x t = s.
Proof.
  intros H1. induction s as [y|s1 IHs1 s2 IHs2]; simpl; simpl in H1.
  - decide (y = x); auto; tauto.
  -  assert (~ x el FV_term s1 /\ ~ x el FV_term s2) as [H2 H3].
     { split; intros H2; auto. }
     apply IHs1 in H2; apply IHs2 in H3. congruence.
Qed.

Lemma noFV_vrep_e A x t :
  ~ x el (FV_eqn A) -> vrep_e A x t = A.
Proof.
  intros H1; induction A.
  - reflexivity.
  - destruct a as [s1 s2]. simpl. simpl in H1.
 assert ((~ x el FV_term s1 /\ ~ x el FV_term s2) /\ ~ x el FV_eqn A) as [[H2 H3] H4].
 { split. split; intros H2; apply H1; auto. intros H2; apply H1; auto. }
 apply (noFV_vrep_t t) in H2; apply (noFV_vrep_t t) in H3.
 rewrite H2; rewrite H3. f_equal. auto.
Qed.

Lemma dom_vrep_e A x t :
  ~ x el (Dom_eqn A) -> Dom_eqn (vrep_e A x t) = Dom_eqn A.
Proof.
  intros H1. induction A as [|(s1, s2) A].
  - reflexivity.
  - destruct s1 as [y |t1 t2]; auto. simpl. decide (y = x).
    + subst. simpl in H1. exfalso. auto.
    + f_equal. simpl in H1. auto.
Qed.

Lemma subs_vrep_t sigma x t :
  subst sigma -> sigma (V x) = sigma t -> forall s, sigma (vrep_t s x t) = sigma s.
Proof.
  intros H1 H2; induction s as [y|s1 IHs1 s2 IHs2].
  - simpl. decide (y = x); congruence.
  - simpl. replace (sigma (T s1 s2)) with (T (sigma s1) (sigma s2)).
    { specialize (H1 (vrep_t s1 x t)); specialize (H1 (vrep_t s2 x t)).
      congruence. } symmetry. apply H1.
Qed.

Lemma vrep_t_is_subs x t :
  subst (fun s => vrep_t s x t).
Proof.  
  intros s1 s2. reflexivity. Qed.

(* Exercise 9.2.4 *)

Lemma phi_is_subs A:
  subst (phi A).
Proof.
  intros s1 s2. induction A as [|(t1, t2)  A].
  - reflexivity.
  - destruct t1 as [x|u1 u2]; simpl.
    + rewrite IHA. reflexivity.
    + reflexivity.
Qed.

Lemma phi_FV A s:
  disjoint (Dom_eqn A) (FV_term s) -> phi A s = s.
  intros H1. induction s as [x|s1 IHs1 s2 IHs2].
  - induction A as [|(t1, t2) A]; auto. destruct t1 as [y|u1 u2]; auto.
    simpl. simpl in H1. simpl in IHA. replace (phi A (V x)) with (V x).
    { simpl. decide (x = y); auto. subst. exfalso. destruct H1. exists y; auto. }
    symmetry; apply IHA. apply disjoint_cons in H1 as [_ H1]. assumption.
  - replace (phi A (T s1 s2)) with (T (phi A s1) (phi A s2))
      by (symmetry; apply phi_is_subs).
    simpl in H1. apply disjoint_symm in H1; apply disjoint_app in H1.
    destruct H1 as [H1 H2]; apply disjoint_symm in H1; apply disjoint_symm in H2.
    apply IHs1 in H1; apply IHs2 in H2. congruence.
Qed.

Lemma solv_phi_unif A :
  solved A -> unif (phi A) A.
Proof.
  intros H1. induction H1 as [|x t A H1 H2 H3 H4].
  - split; intros s t; auto. intros H1; destruct H1.
  - destruct IHH4 as [H5  H6]; split.
    + intros s1 s2. simpl. replace (phi A (T s1 s2)) with (T (phi A s1) (phi A s2))
      by (symmetry; apply H5). reflexivity.
    + intros s1 s2 H7. simpl. destruct H7.
    * assert (s1 = V x /\ s2 = t) as [e1 e2] by (split; congruence); subst; clear H.
      replace (phi A (V x)) with (V x).
      { simpl. decide (x = x); try tauto. clear e. apply disjoint_symm in H3.
        apply phi_FV in H3. rewrite H3. apply (noFV_vrep_t t) in H1. auto. }
      symmetry; apply phi_FV. simpl. intros [y [H7 H8]]. destruct H8; subst; auto.
    * f_equal. auto.
Qed.

Lemma unif_phi A sigma :
  unif sigma A -> forall s, sigma (phi A s) = sigma s.
Proof.
  intros H1 s. induction A as [|(t1,t) A].
  - auto.
  - destruct t1 as [x|]; auto. simpl. destruct H1 as [H1 H2].
    assert (forall u, sigma (vrep_t u x t) = sigma u).
    { intros u. induction u as [y|u1 IHu1 u2 IHu2]; simpl.
      - decide (y = x); auto. subst. symmetry. auto.
      - replace (sigma (T u1 u2)) with (T (sigma u1) (sigma u2)) by auto.
        specialize (H1 (vrep_t u1 x t)); specialize (H1 (vrep_t u2 x t)).
        congruence. }
    specialize (H (phi A s)). rewrite H. apply IHA. split; auto.
Qed.

Lemma solv_phi_princ A :
  solved A -> principal_unifier (phi A) A.
Proof.
  intros H1. assert (unif (phi A) A) as H2
      by (apply solv_phi_unif; assumption). split.
  - assumption.
  - apply unif_phi.
Qed.

(* Exercise 9.2.5 *)

Fixpoint size s : nat :=
  match s with
  | V _ => 1
  |T s t => size s + size t
  end.

Lemma FV_size x s sigma :
  x el FV_term s -> subst sigma -> size (sigma (V x)) <= size (sigma s).
  intros H1 H2. induction s as [y|s1 IHs1 s2 IHs2]; simpl in H1.
  - destruct H1; try tauto. subst. constructor.
  - specialize (H2 s1); specialize (H2 s2); rewrite H2. simpl.
    apply in_app_iff in H1. destruct H1 as [H1|H1].
    + apply IHs1 in H1. omega.
    + apply IHs2 in H1. omega.
Qed.

Lemma bad_eq_noUni x s :
  V x <> s -> x el FV_term s -> forall sigma, ~ unif sigma [(V x, s)].
Proof.
  intros H1 H2 sigma H3. destruct H3 as [H3 H4]. induction s as [y|s1 _ s2 _].
  - destruct H2; subst; auto.
  - assert (forall u, size u <> 0) as H0.
    { induction u; simpl; omega. }
    assert (size (sigma (V x)) = size (sigma (T s1 s2))) as H5
        by (f_equal; apply H4;auto). simpl in H2. apply in_app_iff in H2 as [H2|H2];
    replace (sigma (T s1 s2)) with (T (sigma s1) (sigma s2)) in H5 by congruence;
    simpl in H5.
    + assert (size (sigma (V x)) <= size (sigma s1)).
      { apply FV_size; auto. }  rewrite H5 in H.
      assert (size (sigma s2) = 0) as Abs by omega. specialize (H0 (sigma s2)); auto.
    + assert (size (sigma (V x)) <= size (sigma s2)).
      { apply FV_size; auto. }  rewrite H5 in H.
      assert (size (sigma s1) = 0) as Abs by omega. specialize (H0 (sigma s1)); auto.
Qed.

Lemma bad_list_noUni A :
  (exists x s, (V x, s) el A /\ V x <> s /\ x el FV_term s) ->
  forall sigma, ~ unif sigma A.
Proof.
  intros [x [s [H1 [H2 H3]]]] sigma [H4 H5].
  specialize (H5 (V x)); specialize (H5 s). apply H5 in H1.
  assert (~ unif sigma [(V x, s)]) by (apply bad_eq_noUni; auto). apply H.
  split; auto. intros u v [H6|H6]. congruence. destruct H6.
Qed.

(* Exercise 9.2.6 *)

Lemma dom_FV A :
  Dom_eqn A <<= FV_eqn A.
Proof.
  induction A as [|(s,t) A]; auto.
  destruct s as [x|s1 s2]; destruct t as [y|t1 t2]; simpl; auto.
Qed.

Lemma FV_app A B :
  FV_eqn (A ++ B) = FV_eqn A ++ FV_eqn B.
Proof.
  induction A as [|(s, t) A]; auto; simpl.
  rewrite IHA. simpl_list. auto.
Qed.

Lemma FV_cons_incl A s t:
  (s, t) el A -> FV_term s <<= FV_eqn A /\ FV_term t <<= FV_eqn A.
Proof.
  intros H1. induction A as [|(u, v) A]. destruct H1. simpl.
  destruct H1; split.
  - assert (u = s) by congruence; subst. auto.
  - assert (v = t) by congruence; subst. auto.
  - apply IHA in H. destruct H as [H _]. auto.
  - apply IHA in H. destruct H as [_ H]. auto.
Qed.

Lemma FV_incl A B:
  A <<= B -> FV_eqn A <<= FV_eqn B.
Proof.
  intros H; induction A as [|(s,t) A]; simpl; auto. apply incl_lcons in H as [H1 H2].
  apply IHA in H2; clear IHA. apply FV_cons_incl in H1 as [H1 H3].
  auto.
Qed.

(* Exercise 9.2.7 *)

Fixpoint gen n : ter :=
  match n with
  | 0 => V 0
  | S n => T (gen n) (V (S n))
  end.

Lemma eqn_lc s t u :
  forall sigma, unif sigma [(T s t, T s u)] <-> unif sigma [(t, u)].
Proof.
  intros sigma; split; intros [H1 H2]; split; auto.
  - intros s1 s2 H3. destruct H3; auto.
    assert (s1 = t /\ s2 = u) as [e1 e2] by (split; congruence); subst; clear H.
    specialize (H2 (T s t)); specialize (H2 (T s u)).
    cut (T (sigma s) (sigma t) = T (sigma s) (sigma u)).
    { intros H3. injection H3. auto. }
    replace (T (sigma s) (sigma t)) with (sigma (T s t)) by auto.
    replace (T (sigma s) (sigma u)) with (sigma (T s u)) by auto.
    auto.
  - intros s1 s2 H3. destruct H3; auto.
    assert (T s t = s1 /\ T s u = s2) as [e1 e2] by (split; congruence);
      subst; clear H.
    replace (sigma (T s t)) with (T (sigma s) (sigma t)) by auto;
    replace (sigma (T s u)) with (T (sigma s) (sigma u)) by auto.
    f_equal. auto.
Qed.

Goal forall n m, n <> m -> forall sigma, ~ unif sigma [(gen n, gen m)].
Abort.

(* Exercise 9.2.8 *)

Goal forall x A B,
    x el Dom_eqn (A ++ B) -> x el Dom_eqn A \/ x el Dom_eqn B.
Proof.
  intros x; induction A as [|(s,t) A]; intros B; auto; simpl; intros H1.
  destruct s as [y|s1 s2]; auto. destruct H1 as [H1| H1]; subst; auto.
  apply IHA in H1. destruct H1; auto. Qed.

Lemma solved_app  A B :
  solved A -> solved B -> disjoint (FV_eqn A) (Dom_eqn B) -> solved (A ++ B).
Proof.
Abort.

(** 9.3 Unification Rules *)

Definition sim A B := forall sigma, unif sigma A <-> unif sigma B.

Notation "A ~=~ B" := (sim A B) (at level 80).

Definition sim_ord A B := FV_eqn B <<= FV_eqn A /\ A ~=~ B.

Notation "A |> B" := (sim_ord A B) (at level 80).

(* Exercise 9.3.3 *)

Lemma sim_ord_refl A :
  A |> A.
Proof.
  split; auto. intros H; tauto.
Qed.

Lemma sim_ord_trans A B C :
  A |> B -> B |> C -> A |> C.
  intros [H1 H2] [H3 H4]. split.
  - intros x H; auto.
  - intros sigma. specialize (H2 sigma); specialize (H4 sigma). tauto.
Qed.

Lemma sim_ord_cons A B :
  A |> B -> forall x : ter * ter, x :: A |> x :: B.
Proof.
  intros [H1 H2] [s t]. split.
  - simpl. auto.
  - intros sigma. split; intros H3; specialize (H2 sigma); apply unif_cons;
                    apply unif_cons in H3; tauto.
Qed.

Lemma sim_ord_app A A' B B' :
  A |> A' -> B |> B' -> A ++ B |> A' ++ B'.
Proof.
  intros [H1 H2] [H3 H4]. split.
  - intros x H. rewrite FV_app; rewrite FV_app in H.
    apply in_app_iff; apply in_app_iff in H as [H|H]; auto.
  - (* Buscar forma mas rapida *) Abort.

Lemma sim_ord_unif A B:
  A |> B -> forall sigma, unif sigma A <-> unif sigma B.
Proof.
  intros [_ H]. apply H.
Qed.

