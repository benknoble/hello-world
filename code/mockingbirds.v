Require Import Utf8.
Require Import Relations Setoid.
(* ??? *)
(* Start with only finite forests; convert to Stream for possibly-infinite
 * forests *)
Require Import List.

Section Mockingbirds.

  Variable bird: Type.
  Hypothesis responds_to: bird → bird → bird.

  (* make this a Stream later *)
  Definition forest := list bird.
  Hypothesis responds_to_clos: ∀ (f: forest) a b,
    In a f → In b f → In (responds_to a b) f.

  Definition fond_of y x :=
    (responds_to y x) = x.

  Definition compositional (f: forest) := ∀ a b,
    In a f →
    In b f →
    ∃ (c: bird), In c f ∧ ∀ x, (responds_to c x) = (responds_to b (responds_to a x)).

  Definition mockingbird M := ∀ x, (responds_to M x) = (responds_to x x).

  Example MM m: mockingbird m → (responds_to m m) = (responds_to m m).
  Proof.
    now unfold mockingbird.
  Qed.

  Theorem compositional_all_fond f m:
    compositional f →
    mockingbird m →
    In m f →
    ∀ a, In a f → ∃ b, In b f ∧ fond_of a b.
  Proof.
    intros f_comp m_mock m_in_f a a_in_f.
    destruct (f_comp m a m_in_f a_in_f) as (c & c_in_f & c_comp_ma).
    exists (responds_to c c); intuition.
    symmetry.
    rewrite <- (m_mock c) at 2.
    apply c_comp_ma.
  Qed.

End Mockingbirds.
