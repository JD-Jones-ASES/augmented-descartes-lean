module

public import AugmentedDescartes.Rows

/-!
# Lorentz

The matrix identity in Lorentz form, the inverses, the determinant (ARCH.md §2). Lane `lorentz`.
-/

@[expose] public section

namespace AugmentedDescartes

open Matrix

/-- The pairing is the bilinear form of `G`. -/
theorem lor_lorentz_eq_dotProduct {n : ℕ} (u v : Fin 2 ⊕ Fin n → ℝ) :
    lorentz u v = u ⬝ᵥ (lorentzG n *ᵥ v) := sorry

/-- `W G Wᵀ` is the Gram matrix of the rows. -/
theorem lor_mul_lorentzG_mul_transpose_apply {n : ℕ} (W : Matrix (Fin (n + 2)) (Fin 2 ⊕ Fin n) ℝ)
    (i j : Fin (n + 2)) : (W * lorentzG n * Wᵀ) i j = lorentz (W i) (W j) := sorry

theorem lor_descartesQ_transpose (n : ℕ) : (descartesQ n)ᵀ = descartesQ n := sorry

theorem lor_lorentzG_transpose (n : ℕ) : (lorentzG n)ᵀ = lorentzG n := sorry

/-- `(2I − J)(Qₙ/2) = I`. -/
theorem lor_twoIminusJ_mul_half_descartesQ {n : ℕ} (hn : 0 < n) :
    (2 • (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ) - Matrix.of (fun _ _ => 1)) *
      ((1 / 2 : ℝ) • descartesQ n) = 1 := sorry

/-- `Qₙ (I − J/2) = I`. -/
theorem lor_descartesQ_mul_inv {n : ℕ} (hn : 0 < n) :
    descartesQ n * (1 - (1 / 2 : ℝ) • Matrix.of (fun _ _ => (1 : ℝ))) = 1 := sorry

/-- `G⁻¹ = [[0, −2, 0], [−2, 0, 0], [0, 0, Iₙ]]`. -/
noncomputable def lorentzGinv (n : ℕ) : Matrix (Fin 2 ⊕ Fin n) (Fin 2 ⊕ Fin n) ℝ :=
  Matrix.fromBlocks !![0, -2; -2, 0] 0 0 1

theorem lor_lorentzGinv_mul (n : ℕ) : lorentzGinv n * lorentzG n = 1 := sorry

theorem lor_mul_lorentzGinv (n : ℕ) : lorentzG n * lorentzGinv n = 1 := sorry

theorem lor_augmentedTarget_eq (n : ℕ) : augmentedTarget n = (2 : ℝ) • lorentzGinv n := sorry

theorem lor_augmentedTarget_mul_half_lorentzG (n : ℕ) :
    augmentedTarget n * ((1 / 2 : ℝ) • lorentzG n) = 1 := sorry

theorem lor_half_lorentzG_mul_augmentedTarget (n : ℕ) :
    ((1 / 2 : ℝ) • lorentzG n) * augmentedTarget n = 1 := sorry

/-- Rows of norm `1` pairing to `−1` have Gram matrix `2I − J`. -/
theorem lor_gram_of_lorentz {n : ℕ} (W : Matrix (Fin (n + 2)) (Fin 2 ⊕ Fin n) ℝ)
    (h1 : ∀ i, lorentz (W i) (W i) = 1) (h2 : ∀ i j, i ≠ j → lorentz (W i) (W j) = -1) :
    W * lorentzG n * Wᵀ = 2 • (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ) - Matrix.of (fun _ _ => 1) := sorry

/-- From the Gram form to the identity. -/
theorem lor_augmented_identity_of_gram {n : ℕ} (hn : 0 < n) (W : Matrix (Fin (n + 2)) (Fin 2 ⊕ Fin n) ℝ)
    (hG : W * lorentzG n * Wᵀ = 2 • (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ) - Matrix.of (fun _ _ => 1)) :
    Wᵀ * descartesQ n * W = augmentedTarget n := sorry

/-- A solution is invertible, with the explicit two-sided inverse `(G/2) Wᵀ Qₙ`. -/
theorem lor_inv_of_identity {n : ℕ} (hn : 0 < n) (W : Matrix (Fin (n + 2)) (Fin 2 ⊕ Fin n) ℝ)
    (hW : Wᵀ * descartesQ n * W = augmentedTarget n) :
    (((1 / 2 : ℝ) • lorentzG n) * Wᵀ * descartesQ n) * W = 1 ∧
      W * (((1 / 2 : ℝ) • lorentzG n) * Wᵀ * descartesQ n) = 1 := sorry

/-- An isometry of `Qₙ` on the left keeps the identity. -/
theorem lor_isometry_mul {n : ℕ} (U : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ)
    (hU : Uᵀ * descartesQ n * U = descartesQ n) (W : Matrix (Fin (n + 2)) (Fin 2 ⊕ Fin n) ℝ)
    (hW : Wᵀ * descartesQ n * W = augmentedTarget n) :
    (U * W)ᵀ * descartesQ n * (U * W) = augmentedTarget n := sorry

/-- The Descartes form is symmetric. -/
theorem lor_dotProduct_descartesQ_comm {n : ℕ} (u v : Fin (n + 2) → ℝ) :
    u ⬝ᵥ (descartesQ n *ᵥ v) = v ⬝ᵥ (descartesQ n *ᵥ u) := sorry

/-- The Descartes form in coordinates: `u ⬝ᵥ (Qₙ *ᵥ v) = Σ uᵢ vᵢ − (1/n)(Σ uᵢ)(Σ vᵢ)`. -/
theorem lor_dotProduct_descartesQ {n : ℕ} (u v : Fin (n + 2) → ℝ) :
    u ⬝ᵥ (descartesQ n *ᵥ v) = ∑ i, u i * v i - (n : ℝ)⁻¹ * ((∑ i, u i) * ∑ i, v i) := sorry

/-- `Wᵀ Qₙ W` is the target exactly when the rows of `W` have Lorentz norm `1` and pair to `−1`. -/
theorem augmented_identity_iff_lorentz_internal {n : ℕ} (hn : 0 < n) (W : Matrix (Fin (n + 2)) (Fin 2 ⊕ Fin n) ℝ) :
    Wᵀ * descartesQ n * W = augmentedTarget n ↔
      (∀ i, lorentz (W i) (W i) = 1) ∧ ∀ i j, i ≠ j → lorentz (W i) (W j) = -1 := sorry

/-- The Gram form of the identity: `W G Wᵀ = 2I − J`. -/
theorem gram_eq_of_augmented_identity_internal {n : ℕ} (hn : 0 < n) (W : Matrix (Fin (n + 2)) (Fin 2 ⊕ Fin n) ℝ)
    (hW : Wᵀ * descartesQ n * W = augmentedTarget n) :
    W * lorentzG n * Wᵀ = 2 • (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ) - Matrix.of (fun _ _ => 1) := sorry

/-- `det Qₙ = −2/n` (GLMWY III, Lemma 6.4). -/
theorem det_descartesQ_internal (n : ℕ) (hn : 0 < n) : (descartesQ n).det = -2 / n := sorry

/-- The Soddy–Gosset relation is the vanishing of the Descartes form: `(Σ bᵢ)² = n Σ bᵢ² ↔ bᵀ Qₙ b = 0`. -/
theorem soddy_gosset_iff_isotropic_internal {n : ℕ} (hn : 0 < n) (b : Fin (n + 2) → ℝ) :
    (∑ i, b i) ^ 2 = n * ∑ i, b i ^ 2 ↔ b ⬝ᵥ (descartesQ n *ᵥ b) = 0 := sorry

end AugmentedDescartes
