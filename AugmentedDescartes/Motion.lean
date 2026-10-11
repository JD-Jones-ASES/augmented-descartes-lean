module

public import AugmentedDescartes.Rigidity
public import AugmentedDescartes.Orientation

/-!
# Euclidean motions act on configurations; the geometric forms of the orientation theorems

A motion preserves validity, curvature and tangency, so two labelled families of valid, pairwise tangent oriented
spheres and hyperplanes are congruent exactly when their curvature vectors agree; for every such family the total
curvature is never zero and at most two members are hyperplanes, and when the total curvature is positive the open
interiors are pairwise disjoint.
-/

@[expose] public section

namespace AugmentedDescartes

open Matrix

/-- A Euclidean motion preserves the signed curvature. -/
theorem rigidMotionOf_curvature_internal {n : ℕ} (O : Matrix (Fin n) (Fin n) ℝ) (t : Fin n → ℝ)
    (s : OrientedSphere n) :
    OrientedSphere.curvature (rigidMotionOf O t s) = OrientedSphere.curvature s := by
  rcases s with ⟨x, r⟩ | ⟨h, δ⟩ <;> rfl

/-- The augmented matrix of a motion preserves the Lorentz pairing of rows. -/
theorem lorentz_vecMul_rigidMotionMatrix_internal {n : ℕ} (O : Matrix (Fin n) (Fin n) ℝ)
    (hO : Oᵀ * O = 1) (t : Fin n → ℝ) (w w' : Fin 2 ⊕ Fin n → ℝ) :
    lorentz (w ᵥ* rigidMotionMatrix O t) (w' ᵥ* rigidMotionMatrix O t) = lorentz w w' := by
  have hsum : ∑ k, (w ᵥ* rigidMotionMatrix O t) (Sum.inr k) * (w' ᵥ* rigidMotionMatrix O t) (Sum.inr k) =
      ((fun k => w (Sum.inr k)) ᵥ* O) ⬝ᵥ ((fun k => w' (Sum.inr k)) ᵥ* O) +
        w' (Sum.inl 1) * (((fun k => w (Sum.inr k)) ᵥ* O) ⬝ᵥ t) +
        w (Sum.inl 1) * (t ⬝ᵥ ((fun k => w' (Sum.inr k)) ᵥ* O)) +
        w (Sum.inl 1) * w' (Sum.inl 1) * (t ⬝ᵥ t) := by
    simp only [rig_row_mul_spatial, dotProduct, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have h1 : ((fun k => w (Sum.inr k)) ᵥ* O) ⬝ᵥ t = (fun k => w (Sum.inr k)) ⬝ᵥ (O *ᵥ t) :=
    (dotProduct_mulVec _ _ _).symm
  have h2 : t ⬝ᵥ ((fun k => w' (Sum.inr k)) ᵥ* O) = (fun k => w' (Sum.inr k)) ⬝ᵥ (O *ᵥ t) := by
    rw [dotProduct_comm, ← dotProduct_mulVec]
  have h3 : ∑ k, w (Sum.inr k) * w' (Sum.inr k) =
      (fun k => w (Sum.inr k)) ⬝ᵥ (fun k => w' (Sum.inr k)) := rfl
  simp only [lorentz]
  rw [hsum, rig_row_mul_augmented, rig_row_mul_augmented, rig_row_mul_curvature,
    rig_row_mul_curvature, rig_vecMul_dotProduct O hO, h1, h2, h3]
  ring

/-- A Euclidean motion preserves tangency of valid objects. -/
theorem rigidMotionOf_tangent_iff_internal {n : ℕ} (O : Matrix (Fin n) (Fin n) ℝ) (hO : Oᵀ * O = 1)
    (t : Fin n → ℝ) (s u : OrientedSphere n) (hs : OrientedSphere.IsValid s)
    (hu : OrientedSphere.IsValid u) :
    OrientedSphere.Tangent (rigidMotionOf O t s) (rigidMotionOf O t u) ↔ OrientedSphere.Tangent s u := by
  rw [← lorentz_row_eq_neg_one_iff_internal _ _ (rigidMotionOf_isValid_internal O hO t s hs)
      (rigidMotionOf_isValid_internal O hO t u hu), ← lorentz_row_eq_neg_one_iff_internal s u hs hu,
    rig_rigidMotionOf_row O hO t s, rig_rigidMotionOf_row O hO t u,
    lorentz_vecMul_rigidMotionMatrix_internal O hO t]

/-- Two labelled families of valid, pairwise tangent oriented spheres and hyperplanes are congruent exactly
when their curvature vectors agree (LMW Theorem 3.1's congruence half as an equivalence). -/
theorem congruent_iff_same_curvature_internal {n : ℕ} (hn : 0 < n)
    (s s' : Fin (n + 2) → OrientedSphere n)
    (hs : ∀ i, OrientedSphere.IsValid (s i)) (hs' : ∀ i, OrientedSphere.IsValid (s' i))
    (ht : ∀ i j, i ≠ j → OrientedSphere.Tangent (s i) (s j))
    (ht' : ∀ i j, i ≠ j → OrientedSphere.Tangent (s' i) (s' j)) :
    (∃ O : Matrix (Fin n) (Fin n) ℝ, ∃ t : Fin n → ℝ, Oᵀ * O = 1 ∧ ∀ i, rigidMotionOf O t (s i) = s' i) ↔
      ∀ i, OrientedSphere.curvature (s i) = OrientedSphere.curvature (s' i) := by
  constructor
  · rintro ⟨O, t, _, h⟩ i
    rw [← h i, rigidMotionOf_curvature_internal]
  · intro hb
    obtain ⟨⟨O, t⟩, ⟨hO, h⟩, _⟩ := same_curvature_congruence_internal hn s s' hs hs' ht ht' hb
    exact ⟨O, t, hO, h⟩

/-- The total curvature of a family of valid, pairwise tangent oriented spheres and hyperplanes is never zero
(GLMWY III §3.1, p. 6, for configurations). -/
theorem tangent_family_curvature_sum_ne_zero_internal {n : ℕ} (hn : 0 < n)
    (s : Fin (n + 2) → OrientedSphere n) (hs : ∀ i, OrientedSphere.IsValid (s i))
    (ht : ∀ i j, i ≠ j → OrientedSphere.Tangent (s i) (s j)) :
    (∑ i, OrientedSphere.curvature (s i)) ≠ 0 := by
  have h := (augmented_orientation_internal hn _ (augmented_descartes_general_internal hn s hs ht)).1
  simpa only [augmentedMatrixOf, Matrix.of_apply, rows_row_inl_one] using h

/-- A family of valid, pairwise tangent oriented spheres and hyperplanes with positive total curvature has
pairwise disjoint open interiors (LMW §3's compatible orientations, for the family itself): the open ball of a
positive-radius sphere, the open exterior of a negative-radius sphere, the open half-space into which a
hyperplane's normal points (`rowPower_sphereRow_neg_iff_of_pos`, `rowPower_sphereRow_neg_iff_of_neg`,
`rowPower_planeRow_neg_iff`). -/
theorem tangent_family_interiors_disjoint_internal {n : ℕ} (hn : 0 < n)
    (s : Fin (n + 2) → OrientedSphere n) (hs : ∀ i, OrientedSphere.IsValid (s i))
    (ht : ∀ i j, i ≠ j → OrientedSphere.Tangent (s i) (s j))
    (hpos : 0 < ∑ i, OrientedSphere.curvature (s i)) (i j : Fin (n + 2)) (hij : i ≠ j) :
    Disjoint {y : EuclideanSpace ℝ (Fin n) | rowPower (OrientedSphere.row (s i)) y < 0}
      {y : EuclideanSpace ℝ (Fin n) | rowPower (OrientedSphere.row (s j)) y < 0} := by
  have h := augmented_orientation_disjoint_internal hn _
    (augmented_descartes_general_internal hn s hs ht) i j hij
  have hB : (∑ k, augmentedMatrixOf s k (Sum.inl 1)) = ∑ k, OrientedSphere.curvature (s k) := by
    simp only [augmentedMatrixOf, Matrix.of_apply, rows_row_inl_one]
  rw [hB] at h
  have he : ∀ m, {y : EuclideanSpace ℝ (Fin n) |
      (∑ k, OrientedSphere.curvature (s k)) * rowPower (augmentedMatrixOf s m) y < 0} =
      {y : EuclideanSpace ℝ (Fin n) | rowPower (OrientedSphere.row (s m)) y < 0} := by
    intro m
    ext y
    simp only [Set.mem_ofPred_eq, augmentedMatrixOf]
    constructor
    · intro hy
      by_contra hy'
      exact absurd hy (not_lt.mpr (mul_nonneg hpos.le (not_lt.mp hy')))
    · exact mul_neg_of_pos_of_neg hpos
  rwa [he, he] at h

/-- At most two members of a family of valid, pairwise tangent oriented spheres and hyperplanes are hyperplanes. -/
theorem tangent_family_two_hyperplanes_internal {n : ℕ} (hn : 0 < n)
    (s : Fin (n + 2) → OrientedSphere n) (hs : ∀ i, OrientedSphere.IsValid (s i))
    (ht : ∀ i j, i ≠ j → OrientedSphere.Tangent (s i) (s j))
    (i j k : Fin (n + 2)) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ¬ (OrientedSphere.curvature (s i) = 0 ∧ OrientedSphere.curvature (s j) = 0 ∧
      OrientedSphere.curvature (s k) = 0) := by
  have h := augmented_no_three_zero_curvatures_internal hn _
    (augmented_descartes_general_internal hn s hs ht) i j k hij hik hjk
  simpa only [augmentedMatrixOf, Matrix.of_apply, rows_row_inl_one] using h

end AugmentedDescartes
