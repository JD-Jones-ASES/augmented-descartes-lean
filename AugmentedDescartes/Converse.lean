module

public import AugmentedDescartes.Main

/-!
# Converse

The converse of the augmented theorem (ARCH.md §4). Lane `converse`.
-/

@[expose] public section

namespace AugmentedDescartes

open Matrix

/-- The rows of a solution have Lorentz norm `1` and distinct rows pair to `−1`. -/
theorem conv_lorentz_of_identity {n : ℕ} (hn : 0 < n) (W : Matrix (Fin (n + 2)) (Fin 2 ⊕ Fin n) ℝ)
    (hW : Wᵀ * descartesQ n * W = augmentedTarget n) :
    (∀ i, lorentz (W i) (W i) = 1) ∧ ∀ i j, i ≠ j → lorentz (W i) (W j) = -1 :=
  (augmented_identity_iff_lorentz_internal hn W).1 hW

/-- Row `i` of `augmentedMatrixOf s` is the row of `s i`. -/
theorem conv_augmentedMatrixOf_apply {n : ℕ} (s : Fin (n + 2) → OrientedSphere n) (i : Fin (n + 2)) :
    augmentedMatrixOf s i = OrientedSphere.row (s i) := rfl

/-- Row `i` of `augmentedMatrix x r` is `sphereRow (x i) (r i)`. -/
theorem conv_augmentedMatrix_apply {n : ℕ} (x : Fin (n + 2) → EuclideanSpace ℝ (Fin n))
    (r : Fin (n + 2) → ℝ) (i : Fin (n + 2)) :
    augmentedMatrix x r i = sphereRow (x i) (r i) := rfl

/-- Decoding a row with nonzero second coordinate gives a sphere. -/
theorem conv_decodeRow_of_ne {n : ℕ} (w : Fin 2 ⊕ Fin n → ℝ) (hw : w (Sum.inl 1) ≠ 0) :
    decodeRow w = Sum.inl (WithLp.toLp 2 (fun k => w (Sum.inr k) / w (Sum.inl 1)), 1 / w (Sum.inl 1)) := by
  unfold decodeRow
  split_ifs with h
  · exact absurd h hw
  · rfl

/-- The converse of LMW Theorem 3.3 (spheres and hyperplanes): every real solution is the augmented matrix
of exactly one family of valid, pairwise tangent oriented spheres and hyperplanes. -/
theorem augmented_descartes_converse_internal {n : ℕ} (hn : 0 < n) (W : Matrix (Fin (n + 2)) (Fin 2 ⊕ Fin n) ℝ)
    (hW : Wᵀ * descartesQ n * W = augmentedTarget n) :
    ∃! s : Fin (n + 2) → OrientedSphere n, (∀ i, OrientedSphere.IsValid (s i)) ∧
      (∀ i j, i ≠ j → OrientedSphere.Tangent (s i) (s j)) ∧ augmentedMatrixOf s = W := by
  obtain ⟨h1, h2⟩ := conv_lorentz_of_identity hn W hW
  have hv : ∀ i, OrientedSphere.IsValid (decodeRow (W i)) := fun i => rows_decodeRow_isValid _ (h1 i)
  have hr : ∀ i, OrientedSphere.row (decodeRow (W i)) = W i := fun i => rows_row_decodeRow _ (h1 i)
  refine ⟨fun i => decodeRow (W i), ⟨hv, fun i j hij => ?_, ?_⟩, ?_⟩
  · rw [← lorentz_row_eq_neg_one_iff_internal _ _ (hv i) (hv j), hr i, hr j]
    exact h2 i j hij
  · funext i
    rw [conv_augmentedMatrixOf_apply]
    exact hr i
  · rintro t ⟨ht, -, htW⟩
    funext i
    apply row_injOn_valid_internal _ _ (ht i) (hv i)
    rw [hr i, ← conv_augmentedMatrixOf_apply, htW]

/-- The converse for spheres: a solution whose second column has no zero is the augmented matrix of
exactly one pairwise tangent family of spheres, `rᵢ = 1/W i 1`, `xᵢ = (W i 2, …) / W i 1`. -/
theorem augmented_descartes_converse_spheres_internal {n : ℕ} (hn : 0 < n)
    (W : Matrix (Fin (n + 2)) (Fin 2 ⊕ Fin n) ℝ) (hW : Wᵀ * descartesQ n * W = augmentedTarget n)
    (hb : ∀ i, W i (Sum.inl 1) ≠ 0) :
    ∃! p : (Fin (n + 2) → EuclideanSpace ℝ (Fin n)) × (Fin (n + 2) → ℝ),
      PairwiseTangent p.1 p.2 ∧ augmentedMatrix p.1 p.2 = W := by
  obtain ⟨h1, h2⟩ := conv_lorentz_of_identity hn W hW
  set x : Fin (n + 2) → EuclideanSpace ℝ (Fin n) :=
    fun i => WithLp.toLp 2 (fun k => W i (Sum.inr k) / W i (Sum.inl 1)) with hx
  set r : Fin (n + 2) → ℝ := fun i => 1 / W i (Sum.inl 1) with hrdef
  have hr0 : ∀ i, r i ≠ 0 := fun i => one_div_ne_zero (hb i)
  have hdec : ∀ i, decodeRow (W i) = Sum.inl (x i, r i) := fun i => conv_decodeRow_of_ne _ (hb i)
  have hrow : ∀ i, sphereRow (x i) (r i) = W i := by
    intro i
    have := rows_row_decodeRow _ (h1 i)
    rw [hdec i] at this
    exact this
  refine ⟨(x, r), ⟨⟨hr0, fun i j hij => ?_⟩, ?_⟩, ?_⟩
  · rw [← lorentz_sphereRow_eq_neg_one_iff_internal _ _ _ _ (hr0 i) (hr0 j), hrow i, hrow j]
    exact h2 i j hij
  · funext i
    rw [conv_augmentedMatrix_apply]
    exact hrow i
  · rintro ⟨y, s⟩ ⟨⟨hs0, -⟩, hyW⟩
    have key : ∀ i, (Sum.inl (y i, s i) : OrientedSphere n) = Sum.inl (x i, r i) := by
      intro i
      apply row_injOn_valid_internal (Sum.inl (y i, s i)) (Sum.inl (x i, r i)) (hs0 i) (hr0 i)
      show sphereRow (y i) (s i) = sphereRow (x i) (r i)
      rw [hrow i, ← conv_augmentedMatrix_apply, hyW]
    have key' : ∀ i, y i = x i ∧ s i = r i := fun i => Prod.mk.inj (Sum.inl_injective (key i))
    exact Prod.ext (funext fun i => (key' i).1) (funext fun i => (key' i).2)

/-- For the `Transitivity` lane: a solution's second column is the curvature vector of a valid, pairwise
tangent family of oriented spheres and hyperplanes (the existence half of the converse, read on curvatures). -/
theorem conv_exists_family_curvature {n : ℕ} (hn : 0 < n) (W : Matrix (Fin (n + 2)) (Fin 2 ⊕ Fin n) ℝ)
    (hW : Wᵀ * descartesQ n * W = augmentedTarget n) :
    ∃ s : Fin (n + 2) → OrientedSphere n, (∀ i, OrientedSphere.IsValid (s i)) ∧
      (∀ i j, i ≠ j → OrientedSphere.Tangent (s i) (s j)) ∧
      ∀ i, OrientedSphere.curvature (s i) = W i (Sum.inl 1) := by
  obtain ⟨s, ⟨hv, ht, hsW⟩, -⟩ := augmented_descartes_converse_internal hn W hW
  refine ⟨s, hv, ht, fun i => ?_⟩
  rw [← rows_row_inl_one, ← conv_augmentedMatrixOf_apply, hsW]

/-- For the `Transitivity` lane: a solution whose second column has no zero gives a pairwise tangent family
of spheres with curvatures `1 / rᵢ = W i 1`. -/
theorem conv_exists_spheres_curvature {n : ℕ} (hn : 0 < n) (W : Matrix (Fin (n + 2)) (Fin 2 ⊕ Fin n) ℝ)
    (hW : Wᵀ * descartesQ n * W = augmentedTarget n) (hb : ∀ i, W i (Sum.inl 1) ≠ 0) :
    ∃ x : Fin (n + 2) → EuclideanSpace ℝ (Fin n), ∃ r : Fin (n + 2) → ℝ,
      PairwiseTangent x r ∧ ∀ i, 1 / r i = W i (Sum.inl 1) := by
  obtain ⟨⟨x, r⟩, ⟨hp, hxW⟩, -⟩ := augmented_descartes_converse_spheres_internal hn W hW hb
  refine ⟨x, r, hp, fun i => ?_⟩
  have h := congrFun (congrFun hxW i) (Sum.inl 1)
  rw [← h]
  simp [augmentedMatrix, sphereRow]

end AugmentedDescartes
