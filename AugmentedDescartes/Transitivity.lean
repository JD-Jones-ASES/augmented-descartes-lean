module

public import AugmentedDescartes.Base
public import AugmentedDescartes.Converse
public import AugmentedDescartes.Apollonian

/-!
# Transitivity

The converse of Soddy–Gosset by a `Qₙ`-reflection (ARCH.md §7). Lane `converse-sg`.
-/

@[expose] public section

namespace AugmentedDescartes

open Matrix

/-- The `Qₙ`-reflection in a vector `v`: `R = 1 − (2/⟨v, v⟩) v (Qₙ v)ᵀ`. -/
noncomputable def qReflection {n : ℕ} (v : Fin (n + 2) → ℝ) : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ :=
  1 - (2 / (v ⬝ᵥ (descartesQ n *ᵥ v))) • Matrix.vecMulVec v (descartesQ n *ᵥ v)

/-- A reflection in a non-isotropic vector preserves `Qₙ`. -/
theorem tr_qReflection_isometry {n : ℕ} (v : Fin (n + 2) → ℝ) (hv : v ⬝ᵥ (descartesQ n *ᵥ v) ≠ 0) :
    (qReflection v)ᵀ * descartesQ n * qReflection v = descartesQ n := sorry

/-- The reflection in `b₀ − b` sends `b₀` to `b` when both are isotropic and pair nontrivially. -/
theorem tr_qReflection_mulVec {n : ℕ} (b₀ b : Fin (n + 2) → ℝ) (h₀ : b₀ ⬝ᵥ (descartesQ n *ᵥ b₀) = 0)
    (h : b ⬝ᵥ (descartesQ n *ᵥ b) = 0) (hp : b₀ ⬝ᵥ (descartesQ n *ᵥ b) ≠ 0) :
    qReflection (b₀ - b) *ᵥ b₀ = b := sorry

/-- The column swap of the two hyperbolic coordinates. -/
noncomputable def hyperbolicSwap (n : ℕ) : Matrix (Fin 2 ⊕ Fin n) (Fin 2 ⊕ Fin n) ℝ :=
  Matrix.fromBlocks !![0, 1; 1, 0] 0 0 1

/-- The swap preserves the target: `σᵀ T σ = T`. -/
theorem tr_hyperbolicSwap_target (n : ℕ) :
    (hyperbolicSwap n)ᵀ * augmentedTarget n * hyperbolicSwap n = augmentedTarget n := sorry

/-- Every solution of the Soddy–Gosset relation with `b ≠ 0` is the second column of a solution of the matrix
identity. -/
theorem tr_exists_solution_of_isotropic {n : ℕ} (hn : 0 < n) (b : Fin (n + 2) → ℝ) (hb : b ≠ 0)
    (h : b ⬝ᵥ (descartesQ n *ᵥ b) = 0) :
    ∃ W : Matrix (Fin (n + 2)) (Fin 2 ⊕ Fin n) ℝ, Wᵀ * descartesQ n * W = augmentedTarget n ∧
      ∀ i, W i (Sum.inl 1) = b i := sorry

/-- The converse of the Soddy–Gosset theorem (LMW Theorem 3.1, existence): every nonzero `b` with
`(Σ bᵢ)² = n Σ bᵢ²` is the curvature vector of a pairwise tangent family of valid oriented spheres
(`bᵢ ≠ 0`) and hyperplanes (`bᵢ = 0`). -/
theorem converse_soddy_gosset_internal {n : ℕ} (hn : 0 < n) (b : Fin (n + 2) → ℝ) (hb : b ≠ 0)
    (h : (∑ i, b i) ^ 2 = n * ∑ i, b i ^ 2) :
    ∃ s : Fin (n + 2) → OrientedSphere n, (∀ i, OrientedSphere.IsValid (s i)) ∧
      (∀ i j, i ≠ j → OrientedSphere.Tangent (s i) (s j)) ∧
      ∀ i, OrientedSphere.curvature (s i) = b i := sorry

/-- The converse of the Soddy–Gosset theorem for spheres: every `b` with no zero entry and
`(Σ bᵢ)² = n Σ bᵢ²` is the curvature vector of a pairwise tangent family of spheres. -/
theorem converse_soddy_gosset_spheres_internal {n : ℕ} (hn : 0 < n) (b : Fin (n + 2) → ℝ) (hb : ∀ i, b i ≠ 0)
    (h : (∑ i, b i) ^ 2 = n * ∑ i, b i ^ 2) :
    ∃ x : Fin (n + 2) → EuclideanSpace ℝ (Fin n), ∃ r : Fin (n + 2) → ℝ,
      PairwiseTangent x r ∧ ∀ i, 1 / r i = b i := sorry

/-- Existence of a pairwise tangent family of spheres in every dimension. -/
theorem exists_pairwiseTangent_internal (n : ℕ) (hn : 0 < n) :
    ∃ x : Fin (n + 2) → EuclideanSpace ℝ (Fin n), ∃ r : Fin (n + 2) → ℝ, PairwiseTangent x r := sorry

end AugmentedDescartes
