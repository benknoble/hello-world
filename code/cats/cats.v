Require Import Coq.Unicode.Utf8.
Require Import List.
Import ListNotations.

Require Export Cats.func.

Class Semigroup (A: Type): Type :=
  {
    mappend: A → A → A ;
    mappend_associative: ∀ x y z, mappend x (mappend y z) = mappend (mappend x y) z ;

    sconcat: A → list A → A := λ a xs, fold_left mappend xs a ;
    stimes: nat → A → A := λ n a, sconcat a (replicate (n-1) a) ;
  }.

Notation "x +_+ y" := (mappend x y) (at level 50).

Class Monoid (A: Type) `{Semigroup A}: Type :=
  {
    mempty: A ;
    mempty_left_unit: ∀ x, mappend mempty x = x ;
    mempty_right_unit: ∀ x, mappend x mempty = x ;

    mconcat: list A → A := λ xs, fold_left mappend xs mempty ;
  }.

Class Functor (f: Type → Type): Type :=
  {
    fmap: ∀ {A B}, (A → B) → f A → f B;
    fmap_id: ∀ {A}, fmap (@id A) = id;
    fmap_compose: ∀ {A B C} (f: A → B) (g: B → C),
      fmap (g ∘ f) = fmap g ∘ fmap f;

    replaceLeft: ∀ {A B}, A → f B → f A := λ A B, fmap ∘ const;
    replaceRight: ∀ {A B}, f A → B → f B := λ A B, flip replaceLeft;
    void: ∀ {A}, f A → f unit := λ A, replaceLeft tt;
  }.

Notation "a <$ fb" := (replaceLeft a fb) (at level 50).
Notation "fa $> b" := (replaceRight fa b) (at level 50).
Notation "f <$> fa" := (fmap f fa) (at level 50).

Class ContraFunctor (f: Type → Type): Type :=
  {
    contramap: ∀ {A B}, (B → A) → f A → f B;
    contramap_id: ∀ {A}, contramap (@id A) = id;
    contramap_compose: ∀ {A B C} (f: A → B) (g: B → C),
      contramap (g ∘ f) = contramap f ∘ contramap g;
  }.

Class InvariantFunctor (f: Type → Type): Type :=
  {
    invmap: ∀ {A B}, (A → B) → (B → A) → f A → f B;
    invmap_id: ∀ {A}, invmap (@id A) (@id A) = id;
    invmap_compose: ∀ {A B C} (f: B → C) (g: C → B) (h: A → B) (k: B → A),
      invmap (f ∘ h) (k ∘ g) = (invmap f g) ∘ (invmap h k);
  }.

Definition functor_invariant f `{Functor f} {A B}: (A → B) → (B → A) → f A → f B
  := const ∘ fmap.

Theorem inv_func: ∀ f, Functor f → InvariantFunctor f.
Proof.
  intros.
  refine {| invmap := @functor_invariant f X |};
  unfold functor_invariant, const, compose; intros.
  - apply fmap_id.
  - apply fmap_compose.
Defined.

Definition contra_invariant f `{ContraFunctor f} {A B}: (A → B)  → (B → A) → f A → f B
  :=  const contramap.

Theorem inv_contra: ∀ f, ContraFunctor f → InvariantFunctor f.
Proof.
  intros.
  refine {| invmap := @contra_invariant f X |};
  unfold contra_invariant, const; intros.
  - apply contramap_id.
  - apply contramap_compose.
Defined.

Class Applicative (f: Type → Type) `{Functor f}: Type :=
  {
    pure: ∀ {A}, A → f A;
    ap: ∀ {A B}, f (A → B) → f A → f B;
    pure_id: ∀ {A} (v: f A), ap (pure id) v = v;
    pure_ap: ∀ {A B} (f: A → B) (x: A), ap (pure f) (pure x) = pure (f x);
    ap_pure: ∀ {A B} (u: f (A → B)) (y: A), ap u (pure y) = ap (pure (λ f, f y)) u;
    ap_assoc: ∀ {A B C} (u: f (B → C)) (v: f (A → B)) (w: f A),
      ap u (ap v w) = ap (ap (ap (pure compose) u) v) w;

    fmap2: ∀ {A B C}, (A → B → C) → f A → f B → f C :=
      λ A B C f a b, ap (ap (pure f) a) b;
  }.

Notation "f <*> x" := (ap f x) (at level 50).

Class Monad (m: Type → Type) `{Applicative m}: Type :=
  {
    mreturn: ∀ {A}, A → m A := @pure m H H0;
    bind: ∀ {A B}, m A → (A → m B) → m B;
    mreturn_bind: ∀ {A B} (a: A) (k: A → m B), bind (mreturn a) k = k a;
    mreturn_id: ∀ {A} (a: m A), bind a mreturn = a;
    mbind_assoc: ∀ {A B C} (a: m A) (k: A → m B) (h: B → m C),
      bind a (λ x, bind (k x) h) = bind (bind a k) h;

    dnib: ∀ {A B}, (A → m B) → m A → m B := λ A B, flip bind;
    map2: ∀ {A B C}, (A → B → C) → m A → m B → m C :=
      λ A B C f a b, bind a (flip fmap b ∘ f);
    product: ∀ {A B}, m A → m B → m (A * B)%type :=
      λ A B, map2 (λ a b, (a, b));

    traverse: ∀ {A B}, (A → m B) → list A → m (list B) :=
      λ A B f, List.fold_right (map2 cons) (mreturn []) ∘ map f;
    sequence: ∀ {A}, list (m A) → m (list A) := λ A, traverse id;

    replicateM: ∀ {A}, nat → m A → m (list A) :=
      λ A, compose2 sequence replicate;
    filterM: ∀ {A}, (A → m bool) → list A → m (list A) :=
      (* λ A f, fix filterM (xs: list A): m (list A) := *)
      (* match xs with *)
      (* | [] => mreturn [] *)
      (* | h::t => bind (f h) (λ keep, (λ t, if keep then h::t else t) <$> (filterM t)) *)
      (* end; *)
      λ A f,
      List.fold_right
      (λ h t, bind (f h) (λ keep, if keep then map2 cons (mreturn h) t else t))
      (mreturn []);
  }.

Notation "x >>= f" := (bind x f) (at level 50).
Notation "f =<< x" := (dnib f x) (at level 50).

Lemma ap_fmap: ∀ {A B: Type} m `{Monad m} (f: A → B) (x: m A),
  pure f <*> x = f <$> x.
Proof.
Admitted.

Lemma ap_bind: ∀ {A B: Type} m `{Monad m} (f: A → B) (x: m A),
  pure f <*> x = (mreturn ∘ f) =<< x.
Proof.
  intros. unfold dnib, flip, compose.
Admitted.

Lemma ap_bind_fmap: ∀ {A B: Type} m `{Monad m} (f: m (A → B)) (x: m A),
  f <*> x = f >>= (λ ff, ff <$> x).
Proof.
Admitted.

Theorem fmap2_map2: ∀ {A B C: Type} m `{Monad m},
  fmap2 (A:=A) (B:=B) (C:=C) = map2.
Proof.
  intros; repeat (apply functional_extensionality; intros).
  unfold fmap2, map2, flip, compose.
  rewrite (@ap_bind A (B → C) m _ _ _).
  unfold dnib, flip, compose.
  rewrite (@ap_bind_fmap _ _ m _ _ _).
  rewrite <- mbind_assoc.
  f_equal; clear x0. apply functional_extensionality; intros.
  now rewrite mreturn_bind.
Qed.
