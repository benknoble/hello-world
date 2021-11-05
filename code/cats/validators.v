Require Import Coq.Unicode.Utf8.
Require Import List.
Import ListNotations.
Require Import Lia.

Require Export Cats.cats.
Require Cats.cats_examples.

Section validators.

  Variable Error: Type.
  Definition validator A := A → Error + A.

  Definition run {A} (v: validator A) (a: A): Error + A := v a.
  Definition runOn {A}: A → validator A → Error + A := flip run.

  Definition succeeding {A}: validator A := inr.
  Definition failing {A} (e: Error): validator A := const (inl e).

  Definition success_of {A}: A → validator A := const ∘ succeeding.

  Definition combine {A} (x y: validator A): validator A :=
    (* λ a, (x a) >>= y. *)
    (* λ a, y =<< (x a). *)
    dnib y ∘ x.

  Definition dispatch {A} (f: A → validator A): validator A :=
    (* λ a, run (f a) a. *)
    (* cats_examples.ar_bind f run. *)
    @bind (arrow A) _ _ _ _ _ f run.

  Definition v_bind_endo {A} (f: A → validator A) (v: validator A): validator A :=
    (* λ a, match run v a with *)
    (*      | inl e => inl e *)
    (*      | inr a => run (f a) a *)
    (*      end. *)
    (* λ a, run v a >>= dispatch f. *)
    dnib (dispatch f) ∘ run v.

  Definition v_bind_co
    {A B} (f: A → validator B) (v: validator A): A → validator B :=
    (* λ a b, run v a >>= (λ a, run (f a) b). *)
    λ a b, run v a >>= runOn b ∘ f.

  Definition rejecting_none_as {A} (e: Error) (v: validator A): validator (option A) :=
    λ a,
    match (option_map (run v) a) with
    | None => inl e
    | Some a => match a with
                | inr a => inr (Some a)
                | inl e => inl e
                end
    end.

  Instance validatorS: ∀ A, Semigroup (validator A).
  Proof.
    intros.
    refine {| mappend := combine |}; intros; cbv.
    apply functional_extensionality; intros; simpl.
    now destruct (x _).
  Defined.

  Instance validatorMd: ∀ A, Monoid (validator A).
  Proof.
    intros.
    refine {| mempty := succeeding |}; intros; cbv;
    try easy.
    apply functional_extensionality; intros.
    now destruct (x _).
  Defined.

  Definition sequence {A}: list (validator A) → validator A := mconcat.

  Definition map {A B} (f: A → B) (g: B → A) (x: validator A): validator B
    :=
    (* λ b, f <$> x (g b). *)
    fmap f ∘ x ∘ g.

  Instance validatorF: InvariantFunctor validator.
  Proof.
    refine {| invmap := @map |}; intros; cbv;
    repeat (apply functional_extensionality; intros);
      now destruct (_ _).
  Defined.

  Definition lift {A B} (f: A → B) (v: validator B): validator A :=
    (* λ a, const a <$> run v (f a). *)
    (* λ a, (map (const a) f v) a. *)
    let map_f_on_v := flip (flip map f) v
    in apply2 (map_f_on_v ∘ const).

End validators.

Section examples.

  Let Error: Type := ().
  Let v := validator Error.

  Example gt_5: v nat := λ x, if Nat.ltb 5 x then inr x else inl ().
  Example zeroth {A}: list A → option A := @hd_error A.
  Example zeroth_gt_5: v (list nat) :=
    lift Error zeroth (rejecting_none_as _ () gt_5).

  Example zgt_1: (zeroth_gt_5 []) = inl (). easy. Qed.
  Example zgt_2: (zeroth_gt_5 [1]) = inl (). easy. Qed.
  Example zgt_3: (zeroth_gt_5 [6]) = inr [6]. easy. Qed.
  Example zgt_4: (zeroth_gt_5 [6; 7]) = inr [6; 7]. easy. Qed.

  Theorem zgt_valid: ∀ (xs: list nat) (n: nat),
    hd_error xs = Some n
    ∧ n > 5
    →
    zeroth_gt_5 xs = inr xs.
  Proof.
    intros xs n [Hh Hn].
    cbv - [Nat.ltb].
    destruct xs; inversion Hh; subst; clear Hh.
    destruct_with_eqn (Nat.ltb 5 n); easy || exfalso.
    rewrite PeanoNat.Nat.ltb_nlt in *.
    lia.
  Qed.

  Theorem zgt_empty_invalid: zeroth_gt_5 [] = inl ().
  Proof. easy. Qed.

  Theorem zgt_invalid: ∀ (xs: list nat) (n: nat),
    hd_error xs = Some n
    ∧ n ≤ 5
    →
    zeroth_gt_5 xs = inl ().
  Proof.
    intros xs n [Hh Hn].
    cbv - [Nat.ltb].
    destruct xs; inversion Hh; subst; clear Hh.
    destruct_with_eqn (Nat.ltb 5 n); easy || exfalso.
    rewrite PeanoNat.Nat.ltb_lt in Heqb.
    enough (5 < 5); lia.
  Qed.

End examples.
