Require Import Utf8.
(* Finite or infinite sets, constructive or classical (?) *)
Require Import Ensembles.

Section Mockingbirds.

  (* Types *)
  Variable bird: Type.
  Definition forest := Ensemble bird.

  (* Relations *)
  Definition In u e := Ensembles.In bird e u.
  Variable responds_to: bird → bird → bird.

  Local Notation "( x , y )" := (responds_to x y).

  (* Correctness hypothesis: the forest is a closed system of birds *)
  Hypothesis responds_to_clos: ∀ (f: forest) a b,
    In a f → In b f → In (a, b) f.

  (* Problem definitions *)
  Definition fond_of y x := (y, x) = x.
  Definition compositional (f: forest) := ∀ a b,
    In a f →
    In b f →
    ∃ (c: bird), In c f ∧ ∀ x, (c, x) = (b, (a, x)).
  Definition mockingbird M := ∀ x, (M, x) = (x, x).

  Example MM m: mockingbird m → (m, m) = (m, m).
  Proof. now unfold mockingbird. Qed.

  Theorem compositional_all_fond f m:
    compositional f →
    mockingbird m →
    In m f →
    ∀ p, In p f → ∃ b, In b f ∧ fond_of p b.
  Proof.
    intros f_comp m_mock m_in_f p a_in_f.
    destruct (f_comp m p) as (c & c_in_f & c_comp_ma); auto.
    specialize (c_comp_ma c); rewrite m_mock in c_comp_ma.
    now exists (c, c); intuition; symmetry.
  Qed.

  Definition no_fixpoint (b: bird) (f: forest) :=
    ∀ x, In x f → ¬ fond_of b x.

  Theorem compositional_all_fond_contrap (f: forest):
    (∃ b, In b f ∧ no_fixpoint b f) →
    ¬ (compositional f ∧ (∃ m, In m f ∧ mockingbird m)).
  Proof.
    intros (b & b_in_f & b_no_fix) [f_comp (m & m_in_f & m_mock)].
    destruct (compositional_all_fond f m) with (p := b) as [d contra]; auto.
    now contradiction (b_no_fix d).
  Qed.

  (* Read [fixated_on x y f] as "x is fixated on y in f." *)
  Definition fixated_on x y (f: forest) := ∀ z, In z f → (x, z) = y.
  (* Similarly, "K is a kestrel in f." *)
  Definition kestrel K f := ∀ x, fixated_on (K, x) x f.

  Theorem fond_kestrel_fixated f k:
    (* Notice the kestrel need not be in the forest with birds it responds to *)
    kestrel k f →
    fond_of k k →
    fixated_on k k f.
  Proof.
    intros k_kestrel k_fond_k x x_in_f.
    rewrite <- k_fond_k.
    now rewrite (k_kestrel k).
  Qed.

  (* Minimum premises: notice it is not necessary to be a kestrel yet. *)
  Lemma fond_fixation_gives_equality f k b:
    In k f →
    fond_of k k →
    fixated_on k b f →
    b = k.
  Proof.
    intros k_in_f k_fond_k k_fix_b.
    transitivity (k, k); [ symmetry | ]; auto.
  Qed.

  Theorem fond_kestrel_lonely f k:
    kestrel k f →
    In k f →
    fond_of k k →
    (∀ b, In b f → b = k).
  Proof.
    intros k_kestrel k_in_f k_fond_k b b_in_f.
    apply (fond_fixation_gives_equality f); auto; clear k_in_f.
    (* [fond_kestrel_fixated] with our two k hypotheses gives that k = (k, b);
     * so therefore fixated_on (k,b) b ↔ fixated_on k b. But the former is the
     * definition of a kestrel k. *)
    now rewrite <- (fond_kestrel_fixated f k) with (z := b).
  Qed.

End Mockingbirds.
