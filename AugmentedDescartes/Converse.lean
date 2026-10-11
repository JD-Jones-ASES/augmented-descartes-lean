module

public import AugmentedDescartes.Main

/-!
# Converse

The converse of the augmented theorem (ARCH.md §4). Lane `converse`.
-/

@[expose] public section

namespace AugmentedDescartes

open Matrix

/-- The converse of LMW Theorem 3.3 (spheres and hyperplanes): every real solution is the augmented matrix
of exactly one family of valid, pairwise tangent oriented spheres and hyperplanes. -/
theorem augmented_descartes_converse_internal {n : ℕ} (hn : 0 < n) (W : Matrix (Fin (n + 2)) (Fin 2 ⊕ Fin n) ℝ)
    (hW : Wᵀ * descartesQ n * W = augmentedTarget n) :
    ∃! s : Fin (n + 2) → OrientedSphere n, (∀ i, OrientedSphere.IsValid (s i)) ∧
      (∀ i j, i ≠ j → OrientedSphere.Tangent (s i) (s j)) ∧ augmentedMatrixOf s = W := sorry

/-- The converse for spheres: a solution whose second column has no zero is the augmented matrix of
exactly one pairwise tangent family of spheres, `rᵢ = 1/W i 1`, `xᵢ = (W i 2, …) / W i 1`. -/
theorem augmented_descartes_converse_spheres_internal {n : ℕ} (hn : 0 < n)
    (W : Matrix (Fin (n + 2)) (Fin 2 ⊕ Fin n) ℝ) (hW : Wᵀ * descartesQ n * W = augmentedTarget n)
    (hb : ∀ i, W i (Sum.inl 1) ≠ 0) :
    ∃! p : (Fin (n + 2) → EuclideanSpace ℝ (Fin n)) × (Fin (n + 2) → ℝ),
      PairwiseTangent p.1 p.2 ∧ augmentedMatrix p.1 p.2 = W := sorry

end AugmentedDescartes
