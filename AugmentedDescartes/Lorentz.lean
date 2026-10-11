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
    lorentz u v = u ⬝ᵥ (lorentzG n *ᵥ v) := by
  simp [lorentz, lorentzG, dotProduct, mulVec, Fintype.sum_sum_type, Fin.sum_univ_two,
    Matrix.one_apply]
  ring

/-- `W G Wᵀ` is the Gram matrix of the rows. -/
theorem lor_mul_lorentzG_mul_transpose_apply {n : ℕ} (W : Matrix (Fin (n + 2)) (Fin 2 ⊕ Fin n) ℝ)
    (i j : Fin (n + 2)) : (W * lorentzG n * Wᵀ) i j = lorentz (W i) (W j) := by
  rw [lor_lorentz_eq_dotProduct, dotProduct_mulVec]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, dotProduct, vecMul]

theorem lor_descartesQ_transpose (n : ℕ) : (descartesQ n)ᵀ = descartesQ n := by
  unfold descartesQ
  rw [transpose_sub, transpose_smul, transpose_one]
  rfl

theorem lor_lorentzG_transpose (n : ℕ) : (lorentzG n)ᵀ = lorentzG n := by
  unfold lorentzG
  rw [fromBlocks_transpose, transpose_zero, transpose_one]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The all-ones matrix on `Fin (n + 2)`. -/
noncomputable def lor_J (n : ℕ) : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ :=
  Matrix.of (fun _ _ => (1 : ℝ))

theorem lor_J_mul_J (n : ℕ) : lor_J n * lor_J n = ((n : ℝ) + 2) • lor_J n := by
  ext i j
  simp [lor_J, Matrix.mul_apply]

theorem lor_combo_mul (n : ℕ) (a b c d : ℝ) :
    (a • (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ) + b • lor_J n) * (c • 1 + d • lor_J n) =
      (a * c) • (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ) +
        (a * d + b * c + b * d * ((n : ℝ) + 2)) • lor_J n := by
  rw [add_mul, mul_add, mul_add, smul_mul_smul_comm, smul_mul_smul_comm, smul_mul_smul_comm,
    smul_mul_smul_comm, one_mul, mul_one, one_mul, lor_J_mul_J, smul_smul]
  module

theorem lor_twoIminusJ_apply (n : ℕ) (i j : Fin (n + 2)) :
    (2 • (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ) - Matrix.of (fun _ _ => (1 : ℝ)) :
      Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ) i j = if i = j then 1 else -1 := by
  rw [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply]
  by_cases h : i = j
  · subst h
    rw [Matrix.one_apply_eq, ite_eq_left rfl]
    norm_num
  · rw [Matrix.one_apply_ne h, ite_eq_right h]
    norm_num

/-- `(2I − J)(Qₙ/2) = I`. -/
theorem lor_twoIminusJ_mul_half_descartesQ {n : ℕ} (hn : 0 < n) :
    (2 • (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ) - Matrix.of (fun _ _ => 1)) *
      ((1 / 2 : ℝ) • descartesQ n) = 1 := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  have e1 : (2 • (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ) - Matrix.of (fun _ _ => 1)) =
      (2 : ℝ) • (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ) + (-1 : ℝ) • lor_J n := by
    ext i j
    rw [lor_twoIminusJ_apply]
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, lor_J, Matrix.of_apply,
      smul_eq_mul]
    split_ifs <;> norm_num
  have e2 : ((1 / 2 : ℝ) • descartesQ n) =
      (1 / 2 : ℝ) • (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ) + (-(1 / 2) * (n : ℝ)⁻¹) • lor_J n := by
    unfold descartesQ lor_J
    module
  rw [e1, e2, lor_combo_mul]
  have hs : (2 : ℝ) * (-(1 / 2) * (n : ℝ)⁻¹) + -1 * (1 / 2) + -1 * (-(1 / 2) * (n : ℝ)⁻¹) * ((n : ℝ) + 2)
      = 0 := by
    field_simp
    ring
  rw [hs]
  norm_num

/-- `Qₙ (I − J/2) = I`. -/
theorem lor_descartesQ_mul_inv {n : ℕ} (hn : 0 < n) :
    descartesQ n * (1 - (1 / 2 : ℝ) • Matrix.of (fun _ _ => (1 : ℝ))) = 1 := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  have e1 : descartesQ n = (1 : ℝ) • (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ) +
      (-(n : ℝ)⁻¹) • lor_J n := by
    unfold descartesQ lor_J
    module
  have e2 : (1 - (1 / 2 : ℝ) • Matrix.of (fun _ _ => (1 : ℝ))) =
      (1 : ℝ) • (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ) + (-(1 / 2) : ℝ) • lor_J n := by
    unfold lor_J
    module
  rw [e1, e2, lor_combo_mul]
  have hs : (1 : ℝ) * (-(1 / 2)) + -(n : ℝ)⁻¹ * 1 + -(n : ℝ)⁻¹ * (-(1 / 2)) * ((n : ℝ) + 2) = 0 := by
    field_simp
    ring
  rw [hs]
  norm_num

/-- `G⁻¹ = [[0, −2, 0], [−2, 0, 0], [0, 0, Iₙ]]`. -/
noncomputable def lorentzGinv (n : ℕ) : Matrix (Fin 2 ⊕ Fin n) (Fin 2 ⊕ Fin n) ℝ :=
  Matrix.fromBlocks !![0, -2; -2, 0] 0 0 1

theorem lor_lorentzGinv_mul (n : ℕ) : lorentzGinv n * lorentzG n = 1 := by
  rw [lorentzGinv, lorentzG, fromBlocks_multiply, ← fromBlocks_one]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]

theorem lor_mul_lorentzGinv (n : ℕ) : lorentzG n * lorentzGinv n = 1 := by
  rw [lorentzGinv, lorentzG, fromBlocks_multiply, ← fromBlocks_one]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]

theorem lor_augmentedTarget_eq (n : ℕ) : augmentedTarget n = (2 : ℝ) • lorentzGinv n := by
  rw [augmentedTarget, lorentzGinv, fromBlocks_smul]
  simp only [smul_zero]
  congr 1
  · ext i j
    fin_cases i <;> fin_cases j <;> norm_num
  · ext i j
    by_cases h : i = j
    · subst h
      rw [diagonal_apply_eq, Matrix.smul_apply, one_apply_eq]
      norm_num
    · rw [diagonal_apply_ne _ h, Matrix.smul_apply, one_apply_ne h, smul_zero]

theorem lor_augmentedTarget_mul_half_lorentzG (n : ℕ) :
    augmentedTarget n * ((1 / 2 : ℝ) • lorentzG n) = 1 := by
  rw [lor_augmentedTarget_eq, smul_mul_smul_comm, lor_lorentzGinv_mul]
  norm_num

theorem lor_half_lorentzG_mul_augmentedTarget (n : ℕ) :
    ((1 / 2 : ℝ) • lorentzG n) * augmentedTarget n = 1 := by
  rw [lor_augmentedTarget_eq, smul_mul_smul_comm, lor_mul_lorentzGinv]
  norm_num

/-- Rows of norm `1` pairing to `−1` have Gram matrix `2I − J`. -/
theorem lor_gram_of_lorentz {n : ℕ} (W : Matrix (Fin (n + 2)) (Fin 2 ⊕ Fin n) ℝ)
    (h1 : ∀ i, lorentz (W i) (W i) = 1) (h2 : ∀ i j, i ≠ j → lorentz (W i) (W j) = -1) :
    W * lorentzG n * Wᵀ = 2 • (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ) - Matrix.of (fun _ _ => 1) := by
  ext i j
  rw [lor_mul_lorentzG_mul_transpose_apply, lor_twoIminusJ_apply]
  by_cases h : i = j
  · subst h
    rw [h1, ite_eq_left rfl]
  · rw [h2 i j h, ite_eq_right h]

/-- The reindexing `Fin (n + 2) ≃ Fin 2 ⊕ Fin n`. -/
def lor_equiv (n : ℕ) : Fin (n + 2) ≃ Fin 2 ⊕ Fin n :=
  (finCongr (Nat.add_comm n 2)).trans finSumFinEquiv.symm

/-- From the Gram form to the identity. -/
theorem lor_augmented_identity_of_gram {n : ℕ} (hn : 0 < n) (W : Matrix (Fin (n + 2)) (Fin 2 ⊕ Fin n) ℝ)
    (hG : W * lorentzG n * Wᵀ = 2 • (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ) - Matrix.of (fun _ _ => 1)) :
    Wᵀ * descartesQ n * W = augmentedTarget n := by
  have h1 : W * (lorentzG n * Wᵀ * ((1 / 2 : ℝ) • descartesQ n)) = 1 := by
    rw [← lor_twoIminusJ_mul_half_descartesQ hn, ← hG]
    simp only [Matrix.mul_assoc]
  have h2 : (lorentzG n * Wᵀ * ((1 / 2 : ℝ) • descartesQ n)) * W = 1 :=
    (Matrix.mul_eq_one_comm_of_equiv (lor_equiv n)).mp h1
  have h3 : lorentzG n * (Wᵀ * descartesQ n * W) =
      (2 : ℝ) • (1 : Matrix (Fin 2 ⊕ Fin n) (Fin 2 ⊕ Fin n) ℝ) := by
    have : lorentzG n * (Wᵀ * descartesQ n * W) =
        (2 : ℝ) • ((lorentzG n * Wᵀ * ((1 / 2 : ℝ) • descartesQ n)) * W) := by
      simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.mul_assoc]
      norm_num
    rw [this, h2]
  calc Wᵀ * descartesQ n * W = (lorentzGinv n * lorentzG n) * (Wᵀ * descartesQ n * W) := by
        rw [lor_lorentzGinv_mul, Matrix.one_mul]
    _ = lorentzGinv n * (lorentzG n * (Wᵀ * descartesQ n * W)) := by rw [Matrix.mul_assoc]
    _ = augmentedTarget n := by rw [h3, Matrix.mul_smul, Matrix.mul_one, lor_augmentedTarget_eq]

/-- A solution is invertible, with the explicit two-sided inverse `(G/2) Wᵀ Qₙ`. -/
theorem lor_inv_of_identity {n : ℕ} (hn : 0 < n) (W : Matrix (Fin (n + 2)) (Fin 2 ⊕ Fin n) ℝ)
    (hW : Wᵀ * descartesQ n * W = augmentedTarget n) :
    (((1 / 2 : ℝ) • lorentzG n) * Wᵀ * descartesQ n) * W = 1 ∧
      W * (((1 / 2 : ℝ) • lorentzG n) * Wᵀ * descartesQ n) = 1 := by
  have h1 : (((1 / 2 : ℝ) • lorentzG n) * Wᵀ * descartesQ n) * W = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Wᵀ, hW,
      lor_half_lorentzG_mul_augmentedTarget]
  exact ⟨h1, (Matrix.mul_eq_one_comm_of_equiv (lor_equiv n).symm).mp h1⟩

/-- An isometry of `Qₙ` on the left keeps the identity. -/
theorem lor_isometry_mul {n : ℕ} (U : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ)
    (hU : Uᵀ * descartesQ n * U = descartesQ n) (W : Matrix (Fin (n + 2)) (Fin 2 ⊕ Fin n) ℝ)
    (hW : Wᵀ * descartesQ n * W = augmentedTarget n) :
    (U * W)ᵀ * descartesQ n * (U * W) = augmentedTarget n := by
  rw [transpose_mul, show Wᵀ * Uᵀ * descartesQ n * (U * W) = Wᵀ * (Uᵀ * descartesQ n * U) * W by
    simp only [Matrix.mul_assoc], hU, hW]

/-- The Descartes form is symmetric. -/
theorem lor_dotProduct_descartesQ_comm {n : ℕ} (u v : Fin (n + 2) → ℝ) :
    u ⬝ᵥ (descartesQ n *ᵥ v) = v ⬝ᵥ (descartesQ n *ᵥ u) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, lor_descartesQ_transpose, dotProduct_comm]

/-- The Descartes form in coordinates: `u ⬝ᵥ (Qₙ *ᵥ v) = Σ uᵢ vᵢ − (1/n)(Σ uᵢ)(Σ vᵢ)`. -/
theorem lor_dotProduct_descartesQ {n : ℕ} (u v : Fin (n + 2) → ℝ) :
    u ⬝ᵥ (descartesQ n *ᵥ v) = ∑ i, u i * v i - (n : ℝ)⁻¹ * ((∑ i, u i) * ∑ i, v i) := by
  have hq : descartesQ n *ᵥ v = fun i => v i - (n : ℝ)⁻¹ * ∑ j, v j := by
    ext i
    simp [descartesQ, mulVec, dotProduct, sub_mul, Finset.sum_sub_distrib, Matrix.one_apply,
      Finset.mul_sum]
  rw [hq]
  simp only [dotProduct, mul_sub, Finset.sum_sub_distrib]
  congr 1
  rw [← Finset.sum_mul]
  ring

/-- The Gram form of the identity (helper, before the iff). -/
theorem lor_gram_of_identity {n : ℕ} (hn : 0 < n) (W : Matrix (Fin (n + 2)) (Fin 2 ⊕ Fin n) ℝ)
    (hW : Wᵀ * descartesQ n * W = augmentedTarget n) :
    W * lorentzG n * Wᵀ = 2 • (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ) - Matrix.of (fun _ _ => 1) := by
  obtain ⟨_, h⟩ := lor_inv_of_identity hn W hW
  have h3 : W * lorentzG n * Wᵀ * descartesQ n =
      (2 : ℝ) • (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ) := by
    have : W * lorentzG n * Wᵀ * descartesQ n =
        (2 : ℝ) • (W * (((1 / 2 : ℝ) • lorentzG n) * Wᵀ * descartesQ n)) := by
      simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.mul_assoc]
      norm_num
    rw [this, h]
  calc W * lorentzG n * Wᵀ
      = W * lorentzG n * Wᵀ * (descartesQ n * (1 - (1 / 2 : ℝ) • Matrix.of (fun _ _ => (1 : ℝ)))) := by
        rw [lor_descartesQ_mul_inv hn, Matrix.mul_one]
    _ = (2 : ℝ) • (1 - (1 / 2 : ℝ) • Matrix.of (fun _ _ => (1 : ℝ))) := by
        rw [← Matrix.mul_assoc, h3, Matrix.smul_mul, Matrix.one_mul]
    _ = 2 • (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ) - Matrix.of (fun _ _ => 1) := by
        ext i j
        rw [lor_twoIminusJ_apply]
        simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.of_apply,
          smul_eq_mul]
        split_ifs <;> norm_num

/-- `Wᵀ Qₙ W` is the target exactly when the rows of `W` have Lorentz norm `1` and pair to `−1`. -/
theorem augmented_identity_iff_lorentz_internal {n : ℕ} (hn : 0 < n) (W : Matrix (Fin (n + 2)) (Fin 2 ⊕ Fin n) ℝ) :
    Wᵀ * descartesQ n * W = augmentedTarget n ↔
      (∀ i, lorentz (W i) (W i) = 1) ∧ ∀ i j, i ≠ j → lorentz (W i) (W j) = -1 := by
  constructor
  · intro hW
    have hG := lor_gram_of_identity hn W hW
    refine ⟨fun i => ?_, fun i j hij => ?_⟩
    · rw [← lor_mul_lorentzG_mul_transpose_apply, hG, lor_twoIminusJ_apply, ite_eq_left rfl]
    · rw [← lor_mul_lorentzG_mul_transpose_apply, hG, lor_twoIminusJ_apply, ite_eq_right hij]
  · rintro ⟨h1, h2⟩
    exact lor_augmented_identity_of_gram hn W (lor_gram_of_lorentz W h1 h2)

/-- The Gram form of the identity: `W G Wᵀ = 2I − J`. -/
theorem gram_eq_of_augmented_identity_internal {n : ℕ} (hn : 0 < n) (W : Matrix (Fin (n + 2)) (Fin 2 ⊕ Fin n) ℝ)
    (hW : Wᵀ * descartesQ n * W = augmentedTarget n) :
    W * lorentzG n * Wᵀ = 2 • (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ) - Matrix.of (fun _ _ => 1) :=
  lor_gram_of_identity hn W hW

/-- `Qₙ = 1 + col(−𝟙/n) row(𝟙)`. -/
theorem lor_descartesQ_eq_replicate (n : ℕ) :
    descartesQ n = 1 + replicateCol Unit (fun _ : Fin (n + 2) => -(n : ℝ)⁻¹) *
      replicateRow Unit (fun _ : Fin (n + 2) => (1 : ℝ)) := by
  ext i j
  simp [descartesQ, Matrix.mul_apply, replicateCol_apply, replicateRow_apply, sub_eq_add_neg]

/-- `det Qₙ = −2/n` (GLMWY III, Lemma 6.4). -/
theorem det_descartesQ_internal (n : ℕ) (hn : 0 < n) : (descartesQ n).det = -2 / n := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  rw [lor_descartesQ_eq_replicate, det_one_add_replicateCol_mul_replicateRow]
  simp [dotProduct]
  field_simp
  ring

/-- The Soddy–Gosset relation is the vanishing of the Descartes form: `(Σ bᵢ)² = n Σ bᵢ² ↔ bᵀ Qₙ b = 0`. -/
theorem soddy_gosset_iff_isotropic_internal {n : ℕ} (hn : 0 < n) (b : Fin (n + 2) → ℝ) :
    (∑ i, b i) ^ 2 = n * ∑ i, b i ^ 2 ↔ b ⬝ᵥ (descartesQ n *ᵥ b) = 0 := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  rw [lor_dotProduct_descartesQ]
  have hsq : ∑ i, b i * b i = ∑ i, b i ^ 2 := Finset.sum_congr rfl fun i _ => (sq (b i)).symm
  rw [hsq]
  constructor
  · intro h
    rw [← sq, h, ← mul_assoc, inv_mul_cancel₀ hn', one_mul, sub_self]
  · intro h
    rw [sub_eq_zero.mp h, ← mul_assoc, mul_inv_cancel₀ hn', one_mul, sq]

end AugmentedDescartes
