Require Import Coq.Unicode.Utf8.

Definition not_exists_all_not_manual:
  ∀ (X: Type) (P: X → Prop),
  ¬(∃ x: X, P x) → ∀ (x: X), ¬ P x
  :=
  λ X P nexPx x Px,
  nexPx (@ex_intro X P x Px)
  .

Theorem not_exists_all_not_normal:
  ∀ (X: Type) (P: X → Prop),
  ¬(∃ x: X, P x) → ∀ (x: X), ¬ P x.
Proof.
  (* eauto. *)
  intros ** Px.
  apply H.
  (* now *) exists x (*; auto *).
  exact Px.
Qed.

Definition exists_not_not_all_manual:
  ∀ (X: Type) (P: X → Prop),
  (∃ x: X, ¬ P x) → ¬ ∀ (x: X), P x
  :=
  λ X P exNPx fPx,
  @ex_ind X (λ x, ¬ P x) False (λ x NPx, NPx (fPx x)) exNPx
  .

Theorem exists_not_not_all_normal:
  ∀ (X: Type) (P: X → Prop),
  (∃ x: X, ¬ P x) → ¬ ∀ (x: X), P x.
Proof.
  intros ** H.
  induction H0. (* proof object uses 'match' if proof uses destruct *)
  (* now *) apply H0.
  apply H.
Qed.

Definition not_pointwise_not_equal_manual:
  ∀ (A B: Type) (f g: A → B),
  (∃ a : A, ¬(f a = g a)) → ¬(f = g)
  :=
  λ A B f g exNFeG FeG,
  @ex_ind A (λ a, ¬(f a = g a)) False
  (λ a Pa, Pa (@eq_ind (A → B) f (λ h, f a = h a) (eq_refl (f a)) g FeG))
  exNFeG
  .

Theorem not_pointwise_not_equal_normal:
  ∀ (A B: Type) (f g: A → B),
  (∃ a : A, ¬(f a = g a)) → ¬(f = g).
Proof.
  intros ** FeG.
  induction H.
  apply H.
  (* now *) induction FeG (*; auto *).
  reflexivity.
Qed.
