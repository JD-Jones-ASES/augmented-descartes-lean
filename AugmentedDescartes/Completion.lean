module

public import AugmentedDescartes.Converse

/-!
# Completion

The converse of the curvature–centre theorem (ARCH.md §8). Lane `completion`.
-/

@[expose] public section

namespace AugmentedDescartes

open Matrix

/-- A solution of the curvature–centre equation with a nonzero first column completes to exactly one solution of
the augmented identity with the same second and centre columns. -/
theorem cmp_exists_unique_completion {n : ℕ} (hn : 0 < n) (M : Matrix (Fin (n + 2)) (Fin 1 ⊕ Fin n) ℝ)
    (hM : Mᵀ * descartesQ n * M = curvatureCenterTarget n) (hb : ∃ i, M i (Sum.inl 0) ≠ 0) :
    ∃! W : Matrix (Fin (n + 2)) (Fin 2 ⊕ Fin n) ℝ, Wᵀ * descartesQ n * W = augmentedTarget n ∧
      (∀ i, W i (Sum.inl 1) = M i (Sum.inl 0)) ∧ ∀ i k, W i (Sum.inr k) = M i (Sum.inr k) := sorry

/-- The converse of LMW Theorem 3.2: every real `M` with `Mᵀ Qₙ M = diag(0, 2 Iₙ)` and a nonzero first
column is the curvature–centre matrix of exactly one family of valid, pairwise tangent oriented spheres and
hyperplanes. -/
theorem curvature_center_converse_internal {n : ℕ} (hn : 0 < n) (M : Matrix (Fin (n + 2)) (Fin 1 ⊕ Fin n) ℝ)
    (hM : Mᵀ * descartesQ n * M = curvatureCenterTarget n) (hb : ∃ i, M i (Sum.inl 0) ≠ 0) :
    ∃! s : Fin (n + 2) → OrientedSphere n, (∀ i, OrientedSphere.IsValid (s i)) ∧
      (∀ i j, i ≠ j → OrientedSphere.Tangent (s i) (s j)) ∧ curvatureCenterMatrixOf s = M := sorry

/-- The hypothesis of `curvature_center_converse` is needed: at `n = 2` the matrix with columns
`0, e₀ − e₁, e₂ − e₃` solves the equation and is the curvature–centre matrix of no family. -/
theorem curvature_center_converse_needs_nonzero_internal :
    ∃ M : Matrix (Fin (2 + 2)) (Fin 1 ⊕ Fin 2) ℝ, Mᵀ * descartesQ 2 * M = curvatureCenterTarget 2 ∧
      (∀ i, M i (Sum.inl 0) = 0) ∧
      ¬ ∃ s : Fin (2 + 2) → OrientedSphere 2, (∀ i, OrientedSphere.IsValid (s i)) ∧
        (∀ i j, i ≠ j → OrientedSphere.Tangent (s i) (s j)) ∧ curvatureCenterMatrixOf s = M := sorry

end AugmentedDescartes
