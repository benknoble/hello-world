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
    exists (c, c); intuition; now symmetry.
  Qed.

End Mockingbirds.
