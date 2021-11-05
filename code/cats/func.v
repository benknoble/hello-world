Require Import Coq.Unicode.Utf8.
Require Import List.
Import ListNotations.
Require Export Coq.Program.Program.

Fixpoint replicate' {A: Type} (xs: list A) (n: nat) (a: A): list A :=
  match n with
  | 0 => xs
  | S n => replicate' (a :: xs) n a
  end.

Definition replicate {A: Type} : nat → A → list A := @replicate' A [].

Definition compose2 {A B C D: Type}: (C → D) → (A → B → C) → A → B → D :=
  compose ∘ compose.

Lemma compose2_nat:
  ∀ {A B C D: Type}, @compose2 A B C D = λ f g x, f ∘ g x.
Proof. easy. Qed.

Definition apply2 {A B} (f: A → A → B) x := f x x.
