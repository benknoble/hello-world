Require Import Coq.Unicode.Utf8.
Require Setoid.
Require Arith.

Fixpoint B n p :=
  match n with
  | 0 => True
  | 1 => p
  | S n => p ↔ B n p
  end.

Lemma B2 n p: B (2 * n) p.
Proof.
  induction n; [ easy | ].

  rewrite (PeanoNat.Nat.mul_add_distr_l _ 1 n).
  simpl (2 * 1) in *.
  destruct n; [ easy | ].

  (* because for some reason rewrite in * isn't working *)
  replace (2 * S n) with (2 * 1 + 2 * n)
    in IHn |- *
    by now rewrite <- (PeanoNat.Nat.mul_add_distr_l 2 1 n).
  simpl (2 * 1) in *.

  split; [ split | intros [_ ?] ]; auto.
Qed.

Lemma B2_Even n p: PeanoNat.Nat.Even n → B n p.
Proof.
  intros [k Hk]; subst.
  apply B2.
Qed.

Inductive ev: nat → Prop :=
  | ev_0: ev 0
  | ev_SS n: ev n → ev (S (S n)).

(* spec *)
Theorem ev_Even n: ev n ↔ PeanoNat.Nat.Even n.
Proof.
  split; intros Hevn.
  - induction Hevn; [ now exists 0 | ].
    destruct IHHevn as [k Hevk]; subst.
    exists (S k).
    now replace (2 * S k) with (2 * 1 + 2 * k)
      by now rewrite <- (PeanoNat.Nat.mul_add_distr_l 2 1 k).
  - destruct Hevn as [k Hevk]; subst.
    generalize dependent k.
    induction k; [ exact ev_0 | ].
    replace (2 * S k) with (2 * 1 + 2 * k)
      by now rewrite <- (PeanoNat.Nat.mul_add_distr_l 2 1 k).
    exact (ev_SS _ IHk).
Qed.

Lemma B2_ev n p: ev n → B n p.
Proof.
  intros H; induction H; [ exact I | ].
  simpl; split.
  - now destruct n.
  - destruct n; intuition.
Qed.

Require Import Even.

Definition even_ind_odd (P: nat → Prop)
  (P0: P 0)
  (PSS: ∀ n, P n → P (S (S n)))
  : ∀ n, even n → P n.
Proof.
  fix f 2; intros n Evn.
  destruct_with_eqn Evn; [ exact P0 | ].
  match goal with
    H: odd n |- _ => destruct_with_eqn H
  end.
  match goal with
    H: even n |- _ => exact (PSS _ (f _ H))
  end.
Qed.

Lemma B2_even n p: even n → B n p.
Proof.
  intros Heven; induction Heven using even_ind_odd; [ exact I | ].
  simpl; split.
  - now destruct n.
  - destruct n; intuition.
Qed.

Lemma tauto1 p: p ↔ (p ↔ (p ↔ (p ↔ (p ↔ (p ↔ (p ↔ (p ↔ (p ↔ p)))))))).
Proof.
  (* tauto. *)

  (* repeat (split; easy || intros ->). *)
  (* repeat (repeat split; assumption || (intros; assumption) || intros ->). *)

  change (B 10 p). (* not strictly necessary, but makes it all more obvious *)

  (* apply B2_Even; now exists 5. *)
  apply B2_even; repeat constructor. (* preferred proof *)
  (* apply B2_ev; repeat constructor. *)
  (* exact (B2 5 p). *)
Qed.
