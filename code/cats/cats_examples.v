Require Import Coq.Unicode.Utf8.
Require Import List.
Import ListNotations.

Require Import Cats.cats.

Instance nat_add_sg: Semigroup nat :=
  {
    mappend := Nat.add ;
    mappend_associative := Plus.plus_assoc ;
  }.

Example nat_add_1: 1 +_+ 2 = 3. easy. Qed.

Instance nat_add_monoid: Monoid nat.
Proof.
  now refine {| mempty := 0 |}.
  (* econstructor. unshelve (instantiate (1 := ?[n])). exact 0. all: easy. *)
  (* econstructor; now eauto. *)
  (* now apply Build_Monoid with (mempty := 0). *)
  (* now constructor 1 with (mempty := 0). *)
  (* now unshelve eapply {| mempty := 0 |}. *)
Defined.

Instance nat_mul_sg: Semigroup nat :=
  {
    mappend := Nat.mul ;
    mappend_associative := PeanoNat.Nat.mul_assoc ;
  }.
Instance nat_mul_monoid: Monoid nat.
Proof.
  econstructor; [ apply PeanoNat.Nat.mul_1_l | apply PeanoNat.Nat.mul_1_r ].
Defined.

Example nat_mul_1: (1 +_+ 2) = 2. easy. Qed.
Example nat_add_2: (@mappend _ nat_add_sg 1 2) = 3. easy. Qed.

Instance listS: ∀ (A: Type), Semigroup (list A) :=
  {
    mappend := @app A ;
    mappend_associative := @app_assoc A ;
  }.

Instance listMd: ∀ (A: Type), Monoid (list A) :=
  {
    mempty := [] ;
    mempty_left_unit := @app_nil_l A ;
    mempty_right_unit := @app_nil_r A ;
  }.

Instance listF: Functor list.
Proof.
  refine {| fmap := List.map |}; intros;
    apply functional_extensionality; induction x; try easy;
    simpl; now rewrite IHx.
Defined.

Instance listIF: InvariantFunctor list := inv_func list listF.

Definition list_ap {A B} (fs: list (A → B)) (xs: list A): list B :=
  flat_map (λ f, map f xs) fs.

Theorem flat_map_compose:
  ∀ {A B C} (a: B → C) (v: list (A → B)) (w: list A),
  map a (flat_map (λ f : A → B, map f w) v)
  =
  flat_map (λ f : A → C, map f w) (map (compose a) v).
Proof.
  intros A B C a. induction v; try easy; intros.
  (* unfold compose in *. *)
  simpl. rewrite map_app. rewrite IHv; clear IHv.
  apply app_inv_tail_iff; clear v.
  induction w; try easy.
  simpl. now rewrite IHw.
Qed.

Instance listA: Applicative list.
Proof.
  refine {| pure := λ A x, [x]; ap := @list_ap |};
  intros; unfold list_ap.
  - induction v; try easy.
    simpl in *. now rewrite IHv.
  - now simpl.
  - generalize dependent y. induction u; try easy; intros.
    simpl in *. now rewrite IHu.
  - generalize dependent w. generalize dependent v.
    induction u; try easy; intros.
    simpl in *. rewrite app_nil_r in *.
    rewrite IHu; clear IHu.
    remember (flat_map (λ f : (A → B) → A → C, map f v) (map compose u)).
    (* unfold compose in *. *)
    rewrite flat_map_app.
    apply app_inv_tail_iff; clear Heql; clear l; clear u.
    apply flat_map_compose.
Defined.

Instance listM: Monad list.
Proof.
  refine {| bind := λ A B, flip (@flat_map A B) |}; intros; unfold flip.
  - simpl. now rewrite app_nil_r.
  - induction a; try easy.
    simpl in *. now rewrite IHa.
  - generalize dependent k.
    generalize dependent h.
    induction a; try easy; intros.
    simpl. rewrite flat_map_app.
    apply app_inv_head_iff.
    apply IHa.
Defined.

Definition option_mappend {A} `{Semigroup A} (x: option A) (y: option A): option A :=
  match (x, y) with
  | (None, None) => None
  | (Some x, None) => Some x
  | (None, Some y) => Some y
  | (Some x, Some y) => Some (x +_+ y)
  end.

Instance optionS: ∀ (A: Type) `{Semigroup A}, Semigroup (option A).
Proof.
  intros.
  refine {| mappend := option_mappend |}; intros.
  destruct x; destruct y; destruct z;
  simpl; try easy.
  unfold option_mappend.
  now rewrite mappend_associative.
Defined.

Instance optionMd: ∀ (A: Type) `{Semigroup A}, Monoid (option A).
Proof.
  intros.
  refine {| mempty := None |}; intros;
  now destruct x.
Defined.

Instance optionF: Functor option.
Proof.
  refine {| fmap := option_map |}; intros;
  apply functional_extensionality; now intros [].
Defined.

Definition option_flat_map {A B} (f: A → option B) (x: option A): option B :=
  match x with
  | None => None
  | Some x => f x
  end.

Definition option_ap {A B} (f: option (A → B)) (x: option A): option B :=
  option_flat_map (λ f, option_map f x) f.

Instance optionA: Applicative option.
Proof.
  refine {| pure := @Some; ap := @option_ap |};
  intros; try easy.
  - now destruct v.
  - destruct u; try easy;
    destruct v; try easy;
    now destruct w.
Defined.

Instance optionM: Monad option.
Proof.
  refine {| bind := λ A B, flip (@option_flat_map A B) |};
  intros; try easy; now destruct a.
Defined.

Instance ArS: ∀ (A: Type), Semigroup (A → A).
Proof.
  intros.
  now refine {| mappend := @compose A A A |}.
Defined.

Instance ArMd: ∀ (A: Type), Monoid (A → A).
Proof.
  intros.
  now refine {| mempty := @id A |}.
Defined.

Instance ArOutS: ∀ (A B: Type) `{Semigroup B}, Semigroup (A → B).
Proof.
  intros.
  refine {| mappend := λ x y a, (x a) +_+ (y a) |}; intros; simpl.
  apply functional_extensionality; intros a.
  apply mappend_associative.
Defined.

Instance ArOutMd: ∀ (A B: Type) `{Monoid B}, Monoid (A → B).
Proof.
  intros.
  refine {| mempty := const mempty |}; intros; simpl;
  apply functional_extensionality; intros a; unfold const;
  [ apply mempty_left_unit | apply mempty_right_unit ].
Defined.

Instance ArF: ∀ (A: Type), Functor (arrow A).
Proof.
  intros.
  now refine {| fmap := @compose A |}.
Defined.

Definition ar_ap {A B C} (f: A → B → C) (g: A → B): A → C :=
  λ a, f a (g a).

Instance ArA: ∀ (A: Type), Applicative (arrow A).
Proof.
  intros.
  now refine {| pure := λ B, const; ap := @ar_ap A |}.
  (* intros B v. *)
  (* Set Printing Implicit. *)
  (* Check const: B → (A → B). *)
  (* Check ar_ap (@const (arrow B B) A id) v. *)
Defined.

Definition ar_bind {A B C} (f: A → B) (g: B → A → C): A → C :=
  (* λ a, g (f a) a. *)
  apply2 (g ∘ f).

Lemma ar_bind_nat: ∀ {A B C: Type} (f: A → B) (g: B → A → C),
  apply2 (g ∘ f) = λ x, g (f x) x.
Proof. easy. Qed.

Lemma ar_bind_ap:
  ∀ {A B C: Type} (f: A → B) (g: B → A → C),
  ar_bind f g = ar_ap (flip g) f.
Proof. easy. Qed.

Lemma ar_ap_bind:
  ∀ {A B C: Type} (f: A → B → C) (g: A → B),
  ar_ap f g = ar_bind g (flip f).
Proof. easy. Qed.

Instance ArM: ∀ (A: Type), Monad (arrow A).
Proof.
  intros.
  now refine {| bind := @ar_bind A |}.
Defined.

Compute (((λ x, x + 1): arrow _ _) >>= ((λ x y, x + y): arrow _ _)) 3.

Definition prod_mappend {A B} `{Semigroup A} `{Semigroup B}
  (ab: A * B) (xy: A * B): (A * B)
  := (fst ab +_+ fst xy, snd ab +_+ snd xy).

Instance productS: ∀ (A B: Type) `{Semigroup A} `{Semigroup B}, Semigroup (A * B).
Proof.
  intros.
  refine {| mappend := prod_mappend |}.
  intros [] [] []; unfold prod_mappend; simpl.
  now repeat rewrite mappend_associative.
Defined.

Instance productMd: ∀ (A B: Type) `{Monoid A} `{Monoid B}, Monoid (A * B).
Proof.
  intros.
  refine {| mempty := (mempty, mempty) |};
  intros []; simpl; unfold prod_mappend; simpl;
  now repeat (rewrite mempty_left_unit || rewrite mempty_right_unit).
Defined.

Definition prod_fmap {F G} `{Functor F} `{Functor G}
  {A B} (f: A → B) (x: (F A * G A)): (F B * G B)
  := (f <$> fst x, f <$> snd x).

Instance productF: ∀ (F G: Type → Type) `{Functor F} `{Functor G},
  Functor (λ A, (F A * G A)%type).
Proof.
  intros.
  refine {| fmap := @prod_fmap F G _ _ |}; intros;
  unfold prod_fmap;
  apply functional_extensionality; intros [].
  - now repeat rewrite fmap_id.
  - repeat rewrite fmap_compose.
    now unfold compose.
Defined.

Definition prod_pure {F G} `{Applicative F} `{Applicative G} {A} (x: A): F A * G A
  := (pure x, pure x).

Definition prod_ap {F G} `{Applicative F} `{Applicative G}
  {A B} (f: F (A → B) * G (A → B)) (x: F A * G A): F B * G B
  :=
  (fst f <*> fst x, snd f <*> snd x).

Instance productA: ∀ (F G: Type → Type) `{Applicative F} `{Applicative G},
  Applicative (λ A, (F A * G A)%type).
Proof.
  intros.
  refine {| pure := @prod_pure F G _ _ _ _; ap := @prod_ap F G _ _ _ _ |};
  intros;
  unfold prod_ap, prod_pure; cbn.
  - destruct v.
    now repeat rewrite pure_id.
  - now repeat rewrite pure_ap.
  - destruct u.
    now repeat rewrite <- ap_pure.
  - destruct u; destruct v; destruct w.
    now repeat rewrite <- ap_assoc.
Defined.

Definition prod_bind {F G} `{Monad F} `{Monad G}
  {A B} (x: F A * G A) (f: A → F B * G B): F B * G B
  := (fst x >>= fst ∘ f, snd x >>= snd ∘ f).

Instance productM: ∀ (F G: Type → Type) `{Monad F} `{Monad G},
  Monad (λ A, (F A * G A)%type).
Proof.
  intros.
  refine {| bind := @prod_bind F G _ _ _ _ _ _ |};
  intros;
  unfold prod_bind.
  - simpl.
    replace pure with (@mreturn F _ _ _ A) by reflexivity.
    replace pure with (@mreturn G _ _ _ A) by reflexivity.
    repeat rewrite mreturn_bind.
    unfold compose.
    now destruct (k a).
  - destruct a. unfold compose; simpl.
    replace pure with (@mreturn F _ _ _ A) by reflexivity.
    replace pure with (@mreturn G _ _ _ A) by reflexivity.
    now repeat rewrite mreturn_id.
  - destruct a; simpl.
    unfold compose. simpl.
    now repeat rewrite mbind_assoc.
Defined.

Definition sum_fmap {E A B} (f: A → B) (x: E + A): E + B :=
  match x with
  | inl x => inl x
  | inr x => inr (f x)
  end.

Instance sumF: ∀ E, Functor (sum E).
Proof.
  intros.
  refine {| fmap := @sum_fmap E |}; intros;
  unfold sum_fmap; unfold compose;
  apply functional_extensionality;
  now intros [].
Defined.

Definition sum_ap {E A B} (f: E + (A → B)) (x: E + A): E + B :=
  match f with
  | inl f => inl f
  | inr f => f <$> x
  end.

Instance sumA: ∀ E, Applicative (sum E).
Proof.
  intros.
  refine {| pure := @inr E; ap := @sum_ap E |}; intros; simpl;
  try easy.
  - unfold sum_fmap. now destruct v.
  - unfold sum_ap; unfold compose.
    destruct u; try easy.
    destruct v; try easy.
    simpl; unfold sum_fmap.
    now destruct w.
Defined.

Definition sum_bind {E A B} (x: E + A) (f: A → E + B): E + B :=
  match x with
  | inl x => inl x
  | inr x => f x
  end.

Instance sumM: ∀ E, Monad (sum E).
Proof.
  intros.
  refine {| bind := @sum_bind E |}; intros; simpl;
  unfold sum_bind; try easy;
  now destruct a.
Defined.
