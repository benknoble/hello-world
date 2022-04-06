Require Import Coq.Unicode.Utf8.
Require Import Arith List Permutation.
Import ListNotations.

Theorem forall_dist_conj X P Q:
  (∀ x: X, P x ∧ Q x) →
  (∀ x, P x) ∧ (∀ x, Q x).
Proof.
  exact (λ H, (conj (λ x, proj1 (H x)) (λ x, proj2 (H x)))).
Qed.

Theorem le_Sn_le n m:
  S n ≤ m → n ≤ m.
Proof.
  transitivity (S n); auto.
Qed.

Theorem le_S_n n m:
  S n ≤ S m → n ≤ m.
Proof.
  generalize dependent m; induction n; intros.
  - apply le_0_n.
  - inversion H; subst; auto.
    transitivity (S (S n)); auto.
Qed.

Theorem le_Sn_n n:
  ¬(S n ≤ n).
Proof.
  induction n; intros H.
  - inversion H.
  - apply IHn.
    now apply le_S_n.
Qed.

Theorem le_antisym n m:
  n ≤ m → m ≤ n → n = m.
Proof.
  intros [] MN; auto.
  destruct (le_Sn_n m0).
  now transitivity n.
Qed.

(* Phew!
 * Q: how does agda do the case elimination in the latter step?
 * A: with the following: *)

Inductive le_agda: nat → nat → Prop :=
  | le_z: ∀ n, le_agda 0 n
  | le_s: ∀ m n, le_agda m n → le_agda (S m) (S n).

(* I've written this proof "Agda style" *)
Theorem le_agda_antisym n m:
  le_agda n m → le_agda m n → n = m.
Proof.
  intros p; induction p; intros q; inversion q as [| k j q']; subst.
  - exact eq_refl.
  - f_equal. exact (IHp q').
Qed.

Module Sorting.

  Theorem nle_flip x y:
    ¬(x ≤ y) → y ≤ x.
  Proof.
    intros H.
    now destruct (Nat.le_ge_cases x y).
  Qed.

  Ltac find_nle_flip :=
    try match goal with
    | H: ¬(_ ≤ _) |- _ => apply nle_flip in H
    end.

  Inductive le_all (x: nat): list nat → Prop :=
    | le_all_vac: le_all x []
    | le_all_cons: ∀ {y: nat} {ys: list nat}, x ≤ y → le_all x ys → le_all x (y :: ys).

  Local Hint Constructors le_all : core.

  Theorem le_all_trans x y ys:
    x ≤ y → le_all y ys → le_all x ys.
  Proof with auto.
    intros L LA. generalize dependent L.
    induction LA... constructor...
    now transitivity y.
  Qed.

  (* Alternate definition *)
  Definition le_all' (x: nat) := Forall (λ y, x ≤ y).
  Theorem le_all'_trans x y ys:
    x ≤ y → le_all' y ys → le_all x ys.
  Proof.
    intros L LA. generalize dependent L.
    induction LA; constructor; auto.
    now transitivity y.
  Qed.

  Theorem le_all_equiv x xs:
    le_all x xs ↔ le_all' x xs.
  Proof.
    split; intros H;
    induction H; constructor; auto.
  Qed.

  Inductive sorted: list nat → Prop :=
    | sorted_nil: sorted []
    | sorted_cons: ∀ {x: nat} {xs: list nat}, le_all x xs → sorted xs → sorted (x :: xs).

  Local Hint Constructors sorted : core.

  Inductive sorted': list nat → Prop :=
    | sorted'_nil: sorted' []
    | sorted'_cons: ∀ {x: nat} {xs: list nat}, le_all' x xs → sorted' xs → sorted' (x :: xs).

  (* Corollary of le_all_equiv … *)
  Theorem sorted_equiv xs:
    sorted xs ↔ sorted' xs.
  Proof.
    split; intros H;
    induction H; constructor; auto;
    apply le_all_equiv; auto.
  Qed.

  Fixpoint insert x xs :=
    match xs with
    | [] => [x]
    | (y :: xs) => if x <=? y then x :: y :: xs else y :: (insert x xs)
    end.

  Ltac use_le_spec x y := destruct (Nat.leb_spec0 x y); find_nle_flip.

  Ltac destruct_insert_cons :=
    match goal with
    | |- _ (if ?x <=? ?y then ?x :: ?y :: ?xs else ?y :: (insert ?x ?xs))
        => use_le_spec x y; repeat (constructor; auto)
    end.

  Fixpoint isort xs := match xs with
                       | [] => []
                       | x :: xs => insert x (isort xs)
                       end.

  Lemma le_all_insert x y xs:
    x ≤ y → le_all x xs → le_all x (insert y xs).
  Proof with auto.
    induction xs as [| z xs]; intros Hxy Hxxs; simpl...
    inversion Hxxs; subst.
    (* by induction hypothesis *)
    destruct_insert_cons.
  Qed.

  Lemma insert_pres_sorted x xs:
    sorted xs → sorted (insert x xs).
  Proof with eauto.
    induction xs as [| y xs]; intros Hsorted; simpl...
    inversion Hsorted; subst.
    destruct_insert_cons.
    * eapply le_all_trans...
    * apply le_all_insert...
  Qed.

  Theorem isort_correct xs:
    sorted (isort xs).
  Proof with eauto.
    induction xs as [| y xs]; simpl; try constructor...
    destruct (isort xs) as [| z xs']; simpl...
    inversion IHxs; subst.
    destruct_insert_cons.
    * eapply le_all_trans...
    * apply le_all_insert...
    * apply insert_pres_sorted...
  Qed.

  Local Hint Constructors Permutation : core.

  (* for fun *)
  Theorem _perm_refl X (xs: list X): Permutation xs xs.
  Proof with auto.
    induction xs...
  Qed.
  Theorem _perm_sym X (xs ys: list X):
    Permutation xs ys → Permutation ys xs.
  Proof with eauto.
    intros HP. induction HP...
  Qed.
  Theorem _perm_trans X (xs ys zs: list X):
    Permutation xs ys → Permutation ys zs → Permutation xs zs.
  Proof. econstructor; eauto. Qed.

  Theorem insert_perm x xs:
    Permutation (x :: xs) (insert x xs).
  Proof with auto.
    induction xs as [| y xs]...
    simpl.
    destruct_insert_cons.
    transitivity (y :: x :: xs)...
  Qed.

  Theorem insert_pres_perm x xs ys:
    Permutation xs ys →
    Permutation (x :: xs) (insert x ys).
  Proof with auto using insert_perm.
    intros Hxy;
      induction Hxy as [| z xs' ys' Hxy | x' y' xs' | xs' xs'' xs''' Hxs1 IHH1 Hxs2 IHH2]...
    - simpl. destruct_insert_cons.
      transitivity (z :: x :: xs')...
    - simpl.
      use_le_spec x x'...
      use_le_spec x y'.
      * transitivity (x :: x' :: y' :: xs')...
      * transitivity (y' :: x' :: insert x xs')...
        transitivity (y' :: x :: x' :: xs')... constructor.
        transitivity (x' :: x :: xs')...
    - rewrite IHH1, <- IHH2.
      symmetry...
  Qed.

  Theorem isort_complete xs:
    Permutation xs (isort xs).
  Proof with (cbv; auto using insert_pres_perm).
    (* inductive case needed [[insert_pres_perm]] *)
    induction xs as [| y xs]...
    (* - constructor. *)
    (* - cbv -[insert]; fold isort. *)
    (*   apply insert_pres_perm. assumption. *)
  Qed.

End Sorting.
