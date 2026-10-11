module

public import AugmentedDescartes.Main

/-!
# Corollaries

The complex Descartes theorem and Mathlib's spheres (ARCH.md §3). Lane `corollaries`.
-/

@[expose] public section

namespace AugmentedDescartes

open Matrix

/-- The complex Descartes theorem (LMW Theorem 2.1, (2.2)) for four circles of nonzero curvature:
with `zᵢ = xᵢ + i yᵢ`, `(Σ bᵢ zᵢ)² = 2 Σ (bᵢ zᵢ)²`. -/
theorem complex_descartes_internal (x : Fin (2 + 2) → EuclideanSpace ℝ (Fin 2)) (r : Fin (2 + 2) → ℝ)
    (h : PairwiseTangent x r) :
    (∑ i, ((x i 0 : ℂ) + (x i 1 : ℂ) * Complex.I) / r i) ^ 2 =
      2 * ∑ i, (((x i 0 : ℂ) + (x i 1 : ℂ) * Complex.I) / r i) ^ 2 := sorry

/-- LMW (2.3): `Σ bᵢ (bᵢ zᵢ) = ½ (Σ bᵢ)(Σ bᵢ zᵢ)`. -/
theorem complex_descartes_mixed_internal (x : Fin (2 + 2) → EuclideanSpace ℝ (Fin 2)) (r : Fin (2 + 2) → ℝ)
    (h : PairwiseTangent x r) :
    ∑ i, (1 / r i : ℂ) * (((x i 0 : ℂ) + (x i 1 : ℂ) * Complex.I) / r i) =
      (1 / 2) * (∑ i, (1 / r i : ℂ)) * ∑ i, ((x i 0 : ℂ) + (x i 1 : ℂ) * Complex.I) / r i := sorry

/-- Soddy–Gosset for Mathlib's spheres: `n + 2` spheres of positive radius, pairwise externally tangent. -/
theorem sphere_soddy_gosset_internal {n : ℕ} (hn : 0 < n)
    (s : Fin (n + 2) → EuclideanGeometry.Sphere (EuclideanSpace ℝ (Fin n)))
    (hr : ∀ i, 0 < (s i).radius)
    (ht : ∀ i j, i ≠ j → EuclideanGeometry.Sphere.IsExtTangent (s i) (s j)) :
    (∑ i, 1 / (s i).radius) ^ 2 = n * ∑ i, (1 / (s i).radius) ^ 2 := sorry

/-- Soddy–Gosset with one enclosing sphere `e`, to which the others are internally tangent and which
carries the curvature `−1/rₑ`. -/
theorem sphere_soddy_gosset_enclosing_internal {n : ℕ} (hn : 0 < n)
    (s : Fin (n + 2) → EuclideanGeometry.Sphere (EuclideanSpace ℝ (Fin n))) (e : Fin (n + 2))
    (hr : ∀ i, 0 < (s i).radius)
    (hint : ∀ j, j ≠ e → EuclideanGeometry.Sphere.IsIntTangent (s j) (s e))
    (hext : ∀ i j, i ≠ e → j ≠ e → i ≠ j → EuclideanGeometry.Sphere.IsExtTangent (s i) (s j)) :
    (∑ i, (if i = e then -1 else 1) / (s i).radius) ^ 2 =
      n * ∑ i, ((if i = e then -1 else 1) / (s i).radius) ^ 2 := sorry

/-- The augmented identity for Mathlib's spheres, pairwise externally tangent. -/
theorem sphere_augmented_descartes_internal {n : ℕ} (hn : 0 < n)
    (s : Fin (n + 2) → EuclideanGeometry.Sphere (EuclideanSpace ℝ (Fin n)))
    (hr : ∀ i, 0 < (s i).radius)
    (ht : ∀ i j, i ≠ j → EuclideanGeometry.Sphere.IsExtTangent (s i) (s j)) :
    (augmentedMatrix (fun i => (s i).center) (fun i => (s i).radius))ᵀ * descartesQ n *
      augmentedMatrix (fun i => (s i).center) (fun i => (s i).radius) = augmentedTarget n := sorry

end AugmentedDescartes
