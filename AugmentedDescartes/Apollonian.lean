module

public import AugmentedDescartes.Converse

/-!
# Apollonian

The Apollonian generators and Soddy's two spheres (ARCH.md §5). Lane `apollonian`.
-/

@[expose] public section

namespace AugmentedDescartes

open Matrix

/-- The entries of the Apollonian generator: row `k` has `−1` on the diagonal and `2/(n−1)` elsewhere, the other
rows are those of the identity. -/
theorem apo_apollonianGen_apply {n : ℕ} (k i j : Fin (n + 2)) :
    apollonianGen n k i j =
      if i = k then (if j = k then (2 / ((n : ℝ) - 1)) - 2 * n / ((n : ℝ) - 1) + 1 else 2 / ((n : ℝ) - 1))
      else (if i = j then 1 else 0) := sorry

/-- The pairing is linear in a row combination. -/
theorem apo_lorentz_vecMul {n : ℕ} (c : Fin (n + 2) → ℝ) (W : Matrix (Fin (n + 2)) (Fin 2 ⊕ Fin n) ℝ)
    (v : Fin 2 ⊕ Fin n → ℝ) : lorentz (c ᵥ* W) v = ∑ i, c i * lorentz (W i) v := sorry

/-- The Apollonian generators preserve the Descartes form (GLMWY III, after (4.1)): `Sₖᵀ Qₙ Sₖ = Qₙ`. -/
theorem apollonianGen_mem_aut_internal {n : ℕ} (hn : 2 ≤ n) (k : Fin (n + 2)) :
    (apollonianGen n k)ᵀ * descartesQ n * apollonianGen n k = descartesQ n := sorry

/-- Replacing sphere `k` of a configuration by its Apollonian reflection gives a configuration. -/
theorem apollonian_reflection_internal {n : ℕ} (hn : 2 ≤ n) (W : Matrix (Fin (n + 2)) (Fin 2 ⊕ Fin n) ℝ)
    (hW : Wᵀ * descartesQ n * W = augmentedTarget n) (k : Fin (n + 2)) :
    (apollonianGen n k * W)ᵀ * descartesQ n * (apollonianGen n k * W) = augmentedTarget n := sorry

/-- The reflected row is `(2/(n−1)) Σ_{i ≠ k} (row i) − (row k)`; in particular the two curvatures
satisfy `bₖ + bₖ' = (2/(n−1)) Σ_{i ≠ k} bᵢ` (LMW (2.1) at `n = 2`). -/
theorem apollonianGen_mul_apply_internal {n : ℕ} (hn : 2 ≤ n) (W : Matrix (Fin (n + 2)) (Fin 2 ⊕ Fin n) ℝ)
    (k : Fin (n + 2)) (j : Fin 2 ⊕ Fin n) :
    (apollonianGen n k * W) k j = (2 / ((n : ℝ) - 1)) * ∑ i ∈ Finset.univ.erase k, W i j - W k j := sorry

/-- Soddy's two spheres in every dimension (LMW, footnote 3; GLMWY III §4.1): the rows of Lorentz norm
`1` pairing to `−1` with every row of a configuration but the `k`-th are exactly the `k`-th row and its
Apollonian reflection, which are distinct. -/
theorem two_tangent_rows_internal {n : ℕ} (hn : 2 ≤ n) (W : Matrix (Fin (n + 2)) (Fin 2 ⊕ Fin n) ℝ)
    (hW : Wᵀ * descartesQ n * W = augmentedTarget n) (k : Fin (n + 2)) :
    (∀ w : Fin 2 ⊕ Fin n → ℝ, (lorentz w w = 1 ∧ ∀ i, i ≠ k → lorentz w (W i) = -1) ↔
      (w = W k ∨ w = (apollonianGen n k * W) k)) ∧ W k ≠ (apollonianGen n k * W) k := sorry

/-- Soddy's two spheres, geometrically: given `n + 1` members of a configuration, exactly two valid
oriented spheres or hyperplanes are tangent to all of them, the missing member and one other, and their
curvatures sum to `(2/(n−1)) Σ` of the others' curvatures. -/
theorem two_tangent_spheres_internal {n : ℕ} (hn : 2 ≤ n) (s : Fin (n + 2) → OrientedSphere n)
    (hv : ∀ i, OrientedSphere.IsValid (s i))
    (ht : ∀ i j, i ≠ j → OrientedSphere.Tangent (s i) (s j)) (k : Fin (n + 2)) :
    ∃ t : OrientedSphere n, OrientedSphere.IsValid t ∧ t ≠ s k ∧
      (∀ i, i ≠ k → OrientedSphere.Tangent t (s i)) ∧
      OrientedSphere.curvature t + OrientedSphere.curvature (s k) =
        (2 / ((n : ℝ) - 1)) * ∑ i ∈ Finset.univ.erase k, OrientedSphere.curvature (s i) ∧
      ∀ u : OrientedSphere n, OrientedSphere.IsValid u → (∀ i, i ≠ k → OrientedSphere.Tangent u (s i)) →
        u = s k ∨ u = t := sorry

end AugmentedDescartes
