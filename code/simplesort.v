(* https://arxiv.org/pdf/2110.01111.pdf *)
(* https://fzn.fr/teaching/coq/ecole11/summer/lectures/lec9.pdf *)
(* https://coq.inria.fr/doc/V8.18.0/stdlib/Coq.Lists.List.html *)
(* https://coq.inria.fr/doc/V8.18.0/refman/proof-engine/tactics.html#example-apply-pattern *)

Require Import Utf8.
Require Import List.
Import ListNotations.
Require Import PeanoNat.
Require Import Lia.

Require Import Sorted.
Require Import Permutation.

Require Import Recdef.

Lemma in_or_out {A: Type} (xs ys: list A) i j:
  length xs = length ys →
  nth_error xs i = nth_error ys j →
  nth_error xs j = nth_error ys i →
  ((i < length xs ∧ j < length ys)
   ∨ (length xs ≤ i ∧ length ys ≤ j)).
Proof.
  intros length_eq ij ji.
  destruct (nth_error xs i) eqn: xs_i;
  destruct (nth_error xs j) eqn: xs_j;
  destruct (nth_error ys i) eqn: ys_i;
  destruct (nth_error ys j) eqn: ys_j; try easy.
  - left; repeat rewrite <- nth_error_Some; now rewrite xs_i, ys_j.
  - contradict xs_j.
    now rewrite nth_error_Some, length_eq, <- nth_error_Some, ys_j.
  - contradict xs_i.
    now rewrite nth_error_Some, length_eq, <- nth_error_Some, ys_i.
  - right; now repeat rewrite <- nth_error_None.
Qed.

Section Naturals.

  Lemma nat_wlog (P: nat → nat → Prop):
    (∀ x y, P x y ↔ P y x) →
    (∀ x y, x ≤ y → P x y) →
    (∀ x y, P x y).
  Proof.
    intros Hsym Hle x y.
    destruct (Nat.le_gt_cases x y) as [Hxy | Hyx]; auto.
    rewrite Hsym; apply Hle; lia.
  Qed.

  Lemma nat_cut (P: nat → Prop) n:
    (∀ k, k < n → P k) →
    P n →
    (∀ k, n < k → P k) →
    (∀ k, P k).
  Proof.
    intros kn nk N k.
    destruct (Compare_dec.lt_eq_lt_dec k n) as [[A | B] | C]; subst; auto.
  Qed.

  Lemma nat_cut_lt (P: nat → Prop) n k:
    k < n →
    (∀ i, i < k → P i) →
    P k →
    (∀ i, k < i → i < n → P i) →
    (∀ i, i < n → P i).
  Proof.
    intros kn ik K ki i i_n.
    destruct (Compare_dec.lt_eq_lt_dec k i) as [[A | B] | C]; subst; auto.
  Qed.

  Lemma nat_cut_gt (P: nat → Prop) n k:
    k > n →
    (∀ i, k > i → i > n → P i) →
    P k →
    (∀ i, i > k → P i) →
    (∀ i, i > n → P i).
  Proof.
    intros kn ik K ki i i_n.
    destruct (Compare_dec.lt_eq_lt_dec k i) as [[A | B] | C]; subst; auto.
  Qed.

  Lemma limited_ind (P: nat → Prop) n:
    P 0 →
    (∀ i, i < n → P i → P (S i)) →
    P n.
  Proof.
    induction n as [| n IHn]; try easy.
    intros P0 Pind; apply Pind; auto.
  Qed.

End Naturals.

Section Sublists.

  Definition sublist_excl (xs: list nat) (i j: nat): list nat :=
    map (λ k, nth k xs 0) (seq i (j - i)).

  Lemma sublist_excl_length xs i j: length (sublist_excl xs i j) = j - i.
  Proof.
    unfold sublist_excl.
    now rewrite map_length, seq_length.
  Qed.

  Lemma nth_error_sublist_excl xs i j k:
    k < length xs → i ≤ k → k < j →
    nth_error xs k = nth_error (sublist_excl xs i j) (k - i).
  Proof.
    intros klen ij kj.
    unfold sublist_excl.
    rewrite nth_error_map.
    rewrite (nth_error_nth' (seq _ _) 0), seq_nth; simpl; try rewrite seq_length; try lia.
    replace (i + _) with k by lia.
    now apply nth_error_nth'.
  Qed.

  Definition sublist_incl xs i j := sublist_excl xs i (S j).

  Lemma firstn_all' {A: Type} (xs ys: list A):
    length xs = length ys →
    firstn (length xs) ys = ys.
  Proof.
    intros ->; now rewrite firstn_all.
  Qed.

End Sublists.

Ltac solve_len := repeat rewrite app_length; repeat rewrite sublist_excl_length; simpl; try lia.

Section SwapSpec.

  Definition swaps f := ∀ (xs: list nat) i j,
    i < length xs → j < length xs →
    length xs = length (f xs i j)
    ∧ nth_error xs i = nth_error (f xs i j) j
    ∧ nth_error xs j = nth_error (f xs i j) i
    ∧ (∀ k, k ≠ i → k ≠ j → nth_error xs k = nth_error (f xs i j) k).

  Lemma permute_swap_suff {A: Type} (xs ys: list A) i j:
    length xs = length ys →
    nth_error xs i = nth_error ys j →
    nth_error xs j = nth_error ys i →
    (∀ k, k ≠ i → k ≠ j → nth_error xs k = nth_error ys k) →
    Permutation xs ys.
  Proof.
    revert i j; apply (nat_wlog (λ i j, _ → _ → _ → _ → Permutation _ _)); intros i j; [intuition |].
    intros i_le_j length_eq ij ji at_k.
    apply Permutation_nth_error; split; auto.
    exists (λ n, if n =? i then j else if n =? j then i else n); split.
    - clear; intros x y fxy.
      destruct (Nat.eqb_spec x i);
      destruct (Nat.eqb_spec x j);
      destruct (Nat.eqb_spec y i);
      destruct (Nat.eqb_spec y j); now subst.
    - intros n.
      destruct (Nat.eqb_spec n i);
      destruct (Nat.eqb_spec n j); subst; symmetry; auto.
  Qed.

  Corollary swaps_permutes f:
    swaps f → ∀ xs i j,
    i < length xs → j < length xs →
    Permutation xs (f xs i j).
  Proof.
    intros f_swaps xs i j Hi Hj; destruct (f_swaps xs i j Hi Hj) as (length_eq & ij & ji & at_k).
    now apply (permute_swap_suff _ _ i j).
  Qed.

End SwapSpec.

Section Swap.

  Definition swap_inner (xs: list nat) (i j: nat): list nat :=
    (* xs[0..=i-1] *)
    (sublist_excl xs 0 i) ++
    (* xs[j] *)
    [nth j xs 0] ++
    (* xs[i+1..=j-1] with length j - i - 1 *)
    (sublist_excl xs (S i) j) ++
    (* xs[i] *)
    [nth i xs 0] ++
    (* xs[j+1..|xs|] with length |xs| - j - 1 *)
    (sublist_excl xs (S j) (length xs)).

  Definition swap (xs: list nat) (i j: nat): list nat :=
    if i =? j
    then xs
    else if i <? j
    then swap_inner xs i j
    else swap_inner xs j i.

  Lemma swap_eq xs i: swap xs i i = xs.
  Proof.
    unfold swap; now rewrite Nat.eqb_refl.
  Qed.

  Lemma swap_sym xs i j: swap xs i j = swap xs j i.
  Proof.
    revert i j; apply nat_wlog; [intuition |]; intros i j i_le_j.
    inversion i_le_j as [| m i_le_m]; subst; [now rewrite swap_eq | unfold swap].
    assert (i_lt: i < S m) by lia; clear i_le_m.
    rewrite <- Nat.ltb_lt in i_lt; rewrite i_lt; clear i_lt.
    now rewrite <- Nat.ltb_ge in i_le_j; rewrite i_le_j, Nat.eqb_sym.
  Qed.

  Lemma swap_wlog xs (P: nat → nat → list nat → Prop):
    (∀ i j, i ≤ j → P i j (swap xs i j)) →
    (∀ i j xs, P i j xs → P j i xs) →
    (∀ i j, P i j (swap xs i j)).
  Proof.
    intros Hs HP.
    apply nat_wlog; try easy; clear Hs.
    intros i j; rewrite swap_sym; intuition.
  Qed.

  Lemma swap_wlog' xs (P: list nat → Prop):
    (∀ i j, i ≤ j → P (swap xs i j)) →
    (∀ i j, P (swap xs i j)).
  Proof.
    intros H.
    apply nat_wlog; try easy; intros i j.
    now rewrite swap_sym.
  Qed.

  Lemma swap_wlog_lt xs (P: nat → nat → list nat → Prop):
    (∀ i j, i < j → P i j (swap_inner xs i j)) →
    (∀ i, P i i xs) →
    (∀ i j xs, P i j xs → P j i xs) →
    (∀ i j, P i j (swap xs i j)).
  Proof.
    intros i_lt_j ii iji.
    apply swap_wlog; auto; intros i j ij.
    inversion ij as [|m im]; subst; [now rewrite swap_eq | unfold swap].
    assert (iSm: i ≠ S m) by lia; rewrite <- Nat.eqb_neq in iSm; rewrite iSm; clear iSm.
    assert (iSm: i < S m) by lia; rewrite <- Nat.ltb_lt in iSm; rewrite iSm; clear iSm.
    clear ij; set (j := S m) in *.
    apply i_lt_j; lia.
  Qed.

  Ltac swap_wlog_lt :=
    match goal with
    | [ i: nat, j: nat |- _ ] =>
        apply swap_wlog_lt; auto; clear i j; intros i j;
        match goal with
        | [ |- i < j → _ ] => intros ij
        | _ => idtac
        end
    end.

  Lemma swap_agree_ij xs i j:
    i < length xs → j < length xs →
    nth_error xs i = nth_error (swap xs i j) j.
  Proof.
    (* no swap_wlog, because the property is not exactly symmetric; it matters
     * which of i and j is used where *)
    intros Hi Hj.
    destruct (Compare_dec.lt_eq_lt_dec i j) as [[i_lt_j | ii] | j_lt_i]; subst; [ | now rewrite swap_eq | ];
        unfold swap; (destruct (i =? j) eqn:ij; [rewrite Nat.eqb_eq in ij; lia | clear ij]).
    - (* i < j *) rewrite <- Nat.ltb_lt in i_lt_j; rewrite i_lt_j; rewrite Nat.ltb_lt in i_lt_j.
      unfold swap_inner.
      repeat rewrite app_assoc; rewrite <- app_assoc.
      rewrite nth_error_app2; solve_len.
      replace (j - _) with 0 by lia; simpl.
      now apply nth_error_nth'.
    - (* j < i *) assert (i_nlt_j: ¬ i < j) by lia; rewrite <- Nat.ltb_nlt in i_nlt_j; rewrite i_nlt_j; clear i_nlt_j.
      unfold swap_inner.
      rewrite app_assoc.
      rewrite nth_error_app1; solve_len.
      rewrite nth_error_app2; solve_len.
      replace (j - _) with 0 by lia; simpl.
      now apply nth_error_nth'.
  Qed.

  Lemma swap_length xs i j:
    i < length xs → j < length xs →
    length xs = length (swap xs i j).
  Proof. swap_wlog_lt; unfold swap_inner; solve_len. Qed.

  Lemma swap_preserves_outside xs i j:
    i < length xs → j < length xs →
    ∀ k, k >= length xs → nth_error xs k = nth_error (swap xs i j) k.
  Proof.
    intros Hi Hj k Hk.
    transitivity (None: option nat); [| symmetry]; apply nth_error_None; try lia.
    now rewrite <- swap_length.
  Qed.

  Lemma swap_preserves xs i j:
    i < length xs → j < length xs →
    ∀ k, k ≠ i → k ≠ j → nth_error xs k = nth_error (swap xs i j) k.
  Proof.
    (* reduce to 0 < k < |xs|, since swap_preserves_outside handles |xs| ≤ k *)
    intros Hi Hj k; revert k Hi Hj.
    apply (nat_cut (λ k, _ → _ → _ → _ → _ = _) (length xs)); try (intros; apply swap_preserves_outside; lia).
    intros k Hk Hi Hj; revert Hi Hj k Hk.
    swap_wlog_lt; unfold swap_inner; intros Hi Hj.
    (* split up the remaining domain at i, j *)
    apply (nat_cut_lt (λ k, _ → _ → _ = _) (length xs) i); try easy.
    - (* 0 < k < i *) intros k ki _ _.
      rewrite nth_error_app1; [| solve_len].
      replace (nth_error (sublist_excl _ _ _) k) with (nth_error (sublist_excl xs 0 i) (k - 0))
      by (now rewrite Nat.sub_0_r).
      apply nth_error_sublist_excl; lia.
    - (* i < k < |xs| *) intros k ik kl; revert k kl ik.
      apply (nat_cut_lt (λ k, _ → _ → _ → _ = _) (length xs) j); try easy.
      * (* i < k < j *) intros k kj ik _ _.
        rewrite app_assoc, nth_error_app2; solve_len.
        rewrite nth_error_app1; [| solve_len].
        replace (i - 0 + 1) with (S i) by lia; apply nth_error_sublist_excl; lia.
      * (* j < k < |xs| *) intros k jk kl _ _ _.
        repeat rewrite app_assoc; rewrite nth_error_app2; solve_len.
        replace (k - _) with (k - (S j)) by lia.
        apply nth_error_sublist_excl; lia.
  Qed.

  Theorem swap_swaps: swaps swap.
  Proof.
    intros xs i j Hi Hj; intuition auto using swap_length, swap_agree_ij, swap_preserves.
    now rewrite swap_sym; apply swap_agree_ij.
  Qed.

End Swap.

Section SimpleSort.

  Function simplesort_inner xs n i j {measure (λ j, n - j) j} :=
    if n <=? j then xs
    else if (nth i xs 0) <? (nth j xs 0)
    then simplesort_inner (swap xs i j) n i (S j)
    else simplesort_inner       xs      n i (S j).
  Proof.
    all: intros; rewrite Nat.leb_gt in *; lia.
  Defined.

  Function simplesort_outer xs n i {measure (λ i, n - i) i} :=
    if n <=? i then xs
    else simplesort_outer (simplesort_inner xs n i 0) n (S i).
  Proof.
    intros; rewrite Nat.leb_gt in *; lia.
  Defined.

  Definition simplesort xs: list nat :=
    simplesort_outer xs (length xs) 0.

  Definition simplesort_outer_P xs i : Prop :=
    let after_ith_iteration := simplesort_outer xs i 0
    in (Sorted le (firstn (S i) after_ith_iteration)
        ∧ nth i after_ith_iteration 0 = list_max xs).

  Lemma simplesort_inner_length xs i j:
    i < length xs → j < length xs →
    length (simplesort_inner xs (length xs) i j) = length xs.
  Proof.
    intros Hi Hj.

    (* apply (simplesort_inner_ind (λ xs n i j ys, length ys = length xs)); try easy. *)
    (* clear; intros xs n i j nj do_swap ->. *)
    (* rewrite <- swap_length; auto. *)
    (* (1* need facts about i, j *1) *)

    (* About simplesort_inner_ind. *)
    (* functional induction (simplesort_inner xs (length xs) i j). *)

    rewrite simplesort_inner_equation.
    destruct (Nat.leb_spec0 (length xs) j); try easy.
    destruct (Nat.ltb_spec0 (nth i xs 0) (nth j xs 0)); try easy.
    (* Need an induction hypothesis *)

    (* induction xs; try easy. *)
    (* rewrite simplesort_inner_equation. *)
    (* destruct (Nat.leb_spec0 (length (a :: xs)) j); try easy. *)
    (* destruct (Nat.ltb_spec0 (nth i (a :: xs) 0) (nth j (a :: xs) 0)); try easy. *)
    (* - Fail rewrite IHxs. *)
  Admitted.

  Lemma simplesort_length xs:
    length (simplesort xs) = length xs.
  Proof.
    apply (simplesort_outer_ind (λ xs n i ys, length ys = length xs)); auto.
    clear; intros xs n i ni ->.
    Fail apply simplesort_inner_length.
    (* need fact about n, then i, j *)
  Admitted.

  Lemma simplesort_outer_Pn_sorts xs:
    simplesort_outer_P xs (length xs) → Sorted le (simplesort xs).
  Proof.
    intros (sorted & max).
    rewrite firstn_all2 in sorted; [apply sorted |].
    fold (simplesort xs); rewrite simplesort_length; lia.
  Qed.

  Theorem simplesort_sorts xs: Sorted le (simplesort xs).
  Proof.
    (* Pick one… *)
    (* apply Sorted_LocallySorted_iff. *)
    (* apply StronglySorted_Sorted. *)
  Admitted.

End SimpleSort.

Section SimpleSort2.

  Fixpoint simplesort2_inner xs i j how_many :=
    match how_many with
    | 0 => xs
    | S how_many_more =>
        if (nth i xs 0) <? (nth j xs 0)
        then simplesort2_inner (swap xs i j) i (S j) how_many_more
        else simplesort2_inner       xs      i (S j) how_many_more
    end.

  Fixpoint simplesort2_outer xs i how_many :=
    match how_many with
    | 0 => xs
    | S how_many_more => simplesort2_outer (simplesort2_inner xs i 0 (length xs)) (S i) how_many_more
    end.

  Definition simplesort2 xs: list nat :=
    simplesort2_outer xs 0 (length xs).

  Definition simplesort2_outer_P xs i : Prop :=
    let after_ith_iteration := simplesort2_outer xs 0 i
    in (Sorted le (firstn i after_ith_iteration)
        ∧ nth (i - 1) after_ith_iteration 0 = list_max xs).

  Lemma simplesort2_inner_length xs i j n:
    i < length xs → j ≤ length xs →
    n ≤ length xs → n + j ≤ length xs →
    length (simplesort2_inner xs i j n) = length xs.
  Proof.
    revert xs i j.
    induction n as [| n IHn]; try easy; intros xs i j iN jN nN njN.
    simpl simplesort2_inner.
    destruct (Nat.ltb_spec0 (nth i xs 0) (nth j xs 0));
    rewrite IHn; try rewrite <- (swap_length _ i j); lia.
  Qed.

  Lemma simplesort2_outer_length xs i n:
    i ≤ length xs →
    n ≤ length xs → n + i ≤ length xs →
    length (simplesort2_outer xs i n) = length xs.
  Proof.
    revert xs i.
    induction n as [| n IHn]; try easy; intros xs i iN nN niN.
    simpl simplesort2_outer.
    remember (simplesort2_inner xs i 0 (length xs)) as inner.
    enough (xlen: length xs = length inner) by (rewrite xlen; apply IHn; lia).
    subst; rewrite simplesort2_inner_length; lia.
  Qed.

  Lemma simplesort2_length xs:
    length (simplesort2 xs) = length xs.
  Proof.
    (* length requirement on simplesort2_outer_length disqualifies empty list *)
    destruct xs; [easy | apply simplesort2_outer_length; simpl; lia].
  Qed.

  Lemma simplesort2_outer_Pn_sorts x xs:
    simplesort2_outer_P (x::xs) (length (x::xs)) → Sorted le (simplesort2 (x::xs)).
  Proof.
    intros (sorted & max).
    (* destruct xs as [| x xs]; try easy; remember (x::xs) as ys. *)
    rewrite firstn_all2 in sorted; [apply sorted |].
    fold (simplesort2 (x::xs)); rewrite simplesort2_length; lia.
  Qed.

  (* (1* inner loop invariant: finding the max *)
  (*  * might need stated better? *1) *)
  (* Lemma simplesort2_inner_max xs k: *)
  (*   1 ≤ k → k ≤ length xs → *)
  (*   nth 0 (simplesort2_inner xs (length xs) (length xs) k) 0 = Init.Nat.max (nth 0 xs 0) (list_max (skipn (length xs - k) xs)). *)
  (* Proof. *)
  (*   revert xs; induction k as [| k IHk]; intros xs Hk kN. *)
  (*   - lia. *)
  (*   - simpl simplesort2_inner. *)
  (*     replace (length xs - length xs) with 0 by lia. *)
  (* Admitted. *)
  (*     (1* destruct xs as [| x xs]; try easy; remember (x::xs) as ys. *1) *)
  (*     (1* destruct (Nat.ltb_spec0 (nth 0 ys 0) (nth (n - S k) ys 0)). *1) *)
  (*     (1* * subst; simpl list_max. *1) *)
  (*     (1*   (2* swapping into 0th position and continuing *2) *1) *)
  (*     (1*   admit. *1) *)
  (*     (1* * subst; simpl list_max. *1) *)
  (*     (1*   (2* not swapping at all; 0th position greater than current examination *2) *1) *)
  (*     (1*   enough (H: nth 0 (simplesort2_inner (x::xs) n n k) 0 = Init.Nat.max x (nth 0 (simplesort2_inner xs n n k) 0)). *1) *)
  (*     (1*   { rewrite H. rewrite IHk; simpl in HN, kN; try easy || lia. *1) *)
  (*     (1*     admit. *1) *)
  (*     (1*     inversion Hk; subst; try easy. *1) *)
  (*     (1*     simpl in H. (2* close! 1 ≤ k still the problem *2) *1) *)
  (*     (1*     admit. } *1) *)
  (*     (1*   (2* no idea; another lemma? *2) *1) *)
  (*     (1*   admit. *1) *)
  (* (1* Admitted. *1) *)

  Theorem simplesort2_sorts xs: Sorted le (simplesort2 xs).
  Proof.

    induction xs as [| x xs IHxs].
    - unfold simplesort2; simpl; easy.
    - apply simplesort2_outer_Pn_sorts.
      (* Paper proceeds by induction on number of outer iterations here *)
      unfold simplesort2_outer_P.
      rewrite firstn_all'; [| rewrite simplesort2_outer_length; lia].
      simpl; rewrite Nat.ltb_irrefl; split.
      * admit.
      * admit.

    (* apply simplesort2_outer_Pn_sorts. *)
    (* unfold simplesort2_outer_P. *)
    (* rewrite firstn_all'; [| rewrite simplesort2_outer_length; lia]. *)

    (* (1* remember (length xs) as n; induction n as [| n IHn]. *1) *)
    (* (1* - destruct xs; simpl; try easy. *1) *)
    (* (1* - split. *1) *)
    (* (1*   * assert (H: firstn (S n) (simplesort2_outer xs 0 (S n)) = simplesort2_outer xs 0 (S n)). *1) *)
    (* (1*     { rewrite Heqn; apply firstn_all'. *1) *)
    (* (1*       rewrite (simplesort2_outer_length _ 0 (length xs)); try lia. } *1) *)
    (* (1*     rewrite H; clear H. *1) *)
    (* (1*     destruct xs as [| x xs]; try easy. *1) *)
    (* (1*     simpl. *1) *)
    (* (1*     rewrite Nat.ltb_irrefl. *1) *)

    (* induction xs as [| x xs (sorted & maxxed)]; simpl; [easy | split; rewrite Nat.ltb_irrefl]. *)
    (* - admit. *)
    (* - replace (length xs - 0) with (length xs) by lia. *)
    (*   (1* rewrite <- maxxed. *1) *)
    (*   admit. *)

    (* remember (length xs) as n. *)
    (* apply limited_ind with (n := n); destruct xs as [| x xs]; try (simpl; easy). *)

    (* destruct xs as [| x xs]; try (simpl; easy). *)
    (* remember (length (x::xs)) as n. *)
    (* (1* induction n; try easy. *1) *)
    (* apply limited_ind with (n := n). *)
    (* - (1* n = 0 *1) admit. *)
    (* - simpl. split. *)
    (*   * destruct (simplesort2_inner _ _ _ _); now constructor. *)
    (*   * destruct xs as [| x xs]; [easy | remember (x::xs) as ys]. *)
    (*     transitivity (list_max (skipn 0 ys)); [| now rewrite skipn_O]. *)
    (*     transitivity (list_max (skipn (length ys - length ys) ys)); [| now rewrite Nat.sub_diag]. *)
    (*     subst; transitivity (Init.Nat.max (nth 0 ys 0) (list_max (skipn (length ys - length ys) ys)). *)
    (*     apply simplesort2_inner_max. subst; simpl; lia. *)
    (* - intros i iN (sorted & max); split. *)

  Admitted.
End SimpleSort2.
