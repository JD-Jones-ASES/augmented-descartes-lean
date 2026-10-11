module

public import AugmentedDescartes.Lorentz

/-!
# Main

The forward theorems: the identity, Soddy–Gosset, the curvature–centre identity (ARCH.md §3). Lane `main`.
-/

@[expose] public section

namespace AugmentedDescartes

open Matrix

/-- The augmented Euclidean Descartes theorem (LMW Theorem 3.3) for spheres of nonzero curvature:
`Wᵀ Qₙ W = [[0, −4, 0], [−4, 0, 0], [0, 0, 2 Iₙ]]`. -/
theorem augmented_descartes_internal {n : ℕ} (hn : 0 < n) (x : Fin (n + 2) → EuclideanSpace ℝ (Fin n))
    (r : Fin (n + 2) → ℝ) (h : PairwiseTangent x r) :
    (augmentedMatrix x r)ᵀ * descartesQ n * augmentedMatrix x r = augmentedTarget n := sorry

/-- The augmented Euclidean Descartes theorem (LMW Theorem 3.3) for spheres and hyperplanes. -/
theorem augmented_descartes_general_internal {n : ℕ} (hn : 0 < n) (s : Fin (n + 2) → OrientedSphere n)
    (hv : ∀ i, OrientedSphere.IsValid (s i))
    (ht : ∀ i j, i ≠ j → OrientedSphere.Tangent (s i) (s j)) :
    (augmentedMatrixOf s)ᵀ * descartesQ n * augmentedMatrixOf s = augmentedTarget n := sorry

/-- The Soddy–Gosset theorem (LMW Theorem 3.1, (1.2)): `(Σ 1/rᵢ)² = n Σ (1/rᵢ)²`. -/
theorem soddy_gosset_internal {n : ℕ} (hn : 0 < n) (x : Fin (n + 2) → EuclideanSpace ℝ (Fin n))
    (r : Fin (n + 2) → ℝ) (h : PairwiseTangent x r) :
    (∑ i, 1 / r i) ^ 2 = n * ∑ i, (1 / r i) ^ 2 := sorry

/-- The Soddy–Gosset theorem for spheres and hyperplanes (curvature `0` for a hyperplane). -/
theorem soddy_gosset_general_internal {n : ℕ} (hn : 0 < n) (s : Fin (n + 2) → OrientedSphere n)
    (hv : ∀ i, OrientedSphere.IsValid (s i))
    (ht : ∀ i j, i ≠ j → OrientedSphere.Tangent (s i) (s j)) :
    (∑ i, OrientedSphere.curvature (s i)) ^ 2 = n * ∑ i, OrientedSphere.curvature (s i) ^ 2 := sorry

/-- The Euclidean generalized Descartes theorem (LMW Theorem 3.2, (3.5)) for spheres:
`Mᵀ Qₙ M = diag(0, 2 Iₙ)`. -/
theorem curvature_center_internal {n : ℕ} (hn : 0 < n) (x : Fin (n + 2) → EuclideanSpace ℝ (Fin n))
    (r : Fin (n + 2) → ℝ) (h : PairwiseTangent x r) :
    (curvatureCenterMatrix x r)ᵀ * descartesQ n * curvatureCenterMatrix x r =
      curvatureCenterTarget n := sorry

/-- LMW Theorem 3.2 for spheres and hyperplanes. -/
theorem curvature_center_general_internal {n : ℕ} (hn : 0 < n) (s : Fin (n + 2) → OrientedSphere n)
    (hv : ∀ i, OrientedSphere.IsValid (s i))
    (ht : ∀ i j, i ≠ j → OrientedSphere.Tangent (s i) (s j)) :
    (curvatureCenterMatrixOf s)ᵀ * descartesQ n * curvatureCenterMatrixOf s =
      curvatureCenterTarget n := sorry

end AugmentedDescartes
