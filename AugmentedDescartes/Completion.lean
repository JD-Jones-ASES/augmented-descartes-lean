module

public import AugmentedDescartes.Converse

/-!
# Completion

The converse of the curvature–centre theorem (ARCH.md §8). Lane `completion`.
-/

@[expose] public section

namespace AugmentedDescartes

open Matrix

/-- The Descartes form `⟨u, v⟩ = u ⬝ᵥ (Qₙ *ᵥ v)` as a bilinear map. -/
noncomputable def cmp_B (n : ℕ) : (Fin (n + 2) → ℝ) →ₗ[ℝ] (Fin (n + 2) → ℝ) →ₗ[ℝ] ℝ :=
  Matrix.toLinearMap₂' ℝ (descartesQ n)

theorem cmp_B_apply {n : ℕ} (u v : Fin (n + 2) → ℝ) : cmp_B n u v = u ⬝ᵥ (descartesQ n *ᵥ v) :=
  Matrix.toLinearMap₂'_apply' _ _ _

theorem cmp_B_comm {n : ℕ} (u v : Fin (n + 2) → ℝ) : cmp_B n u v = cmp_B n v u := by
  rw [cmp_B_apply, cmp_B_apply, lor_dotProduct_descartesQ_comm]

/-- An entry of `Aᵀ Qₙ B` is the Descartes pairing of two columns. -/
theorem cmp_entry {n : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ] (A : Matrix (Fin (n + 2)) ι ℝ)
    (B : Matrix (Fin (n + 2)) κ ℝ) (p : ι) (q : κ) :
    (Aᵀ * descartesQ n * B) p q = cmp_B n (fun i => A i p) (fun i => B i q) := by
  rw [cmp_B_apply, Matrix.mul_assoc, Matrix.mul_apply]
  simp only [Matrix.transpose_apply, dotProduct, Matrix.mulVec, Matrix.mul_apply]

/-- A coordinate of `Aᵀ (Qₙ y)` is the Descartes pairing of a column with `y`. -/
theorem cmp_transpose_mulVec {n : ℕ} {ι : Type*} [Fintype ι] (A : Matrix (Fin (n + 2)) ι ℝ)
    (y : Fin (n + 2) → ℝ) (p : ι) :
    (Aᵀ *ᵥ (descartesQ n *ᵥ y)) p = cmp_B n (fun i => A i p) y := by
  rw [cmp_B_apply]
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]

/-- `Qₙ` is injective. -/
theorem cmp_descartesQ_mulVec_eq_zero {n : ℕ} (hn : 0 < n) {b : Fin (n + 2) → ℝ}
    (h : descartesQ n *ᵥ b = 0) : b = 0 := by
  have hinv : (1 - (1 / 2 : ℝ) • Matrix.of (fun _ _ => (1 : ℝ))) * descartesQ n = 1 :=
    mul_eq_one_comm.mp (lor_descartesQ_mul_inv hn)
  calc b = (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ) *ᵥ b := (Matrix.one_mulVec b).symm
    _ = (1 - (1 / 2 : ℝ) • Matrix.of (fun _ _ => (1 : ℝ))) *ᵥ (descartesQ n *ᵥ b) := by
        rw [Matrix.mulVec_mulVec, hinv]
    _ = 0 := by rw [h, Matrix.mulVec_zero]

/-- A solution `W` of the identity makes `y ↦ Wᵀ Qₙ y` injective. -/
theorem cmp_eq_zero_of_transpose_mulVec {n : ℕ} (hn : 0 < n) (W : Matrix (Fin (n + 2)) (Fin 2 ⊕ Fin n) ℝ)
    (hW : Wᵀ * descartesQ n * W = augmentedTarget n) {y : Fin (n + 2) → ℝ}
    (hy : Wᵀ *ᵥ (descartesQ n *ᵥ y) = 0) : y = 0 := by
  have h1 := (lor_inv_of_identity hn W hW).2
  calc y = (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ) *ᵥ y := (Matrix.one_mulVec y).symm
    _ = W *ᵥ (((1 / 2 : ℝ) • lorentzG n) *ᵥ (Wᵀ *ᵥ (descartesQ n *ᵥ y))) := by
        rw [← h1, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    _ = 0 := by rw [hy, Matrix.mulVec_zero, Matrix.mulVec_zero]

/-- Uniqueness: two solutions of the identity with the same second and centre columns are equal. -/
theorem cmp_completion_unique {n : ℕ} (hn : 0 < n) (W₁ W₂ : Matrix (Fin (n + 2)) (Fin 2 ⊕ Fin n) ℝ)
    (hW₁ : W₁ᵀ * descartesQ n * W₁ = augmentedTarget n)
    (hW₂ : W₂ᵀ * descartesQ n * W₂ = augmentedTarget n)
    (h1 : ∀ i, W₂ i (Sum.inl 1) = W₁ i (Sum.inl 1)) (h2 : ∀ i k, W₂ i (Sum.inr k) = W₁ i (Sum.inr k)) :
    W₁ = W₂ := by
  set a₁ : Fin (n + 2) → ℝ := fun i => W₁ i (Sum.inl 0) with ha₁
  set a₂ : Fin (n + 2) → ℝ := fun i => W₂ i (Sum.inl 0) with ha₂
  set b : Fin (n + 2) → ℝ := fun i => W₁ i (Sum.inl 1) with hb
  have hcb : (fun i => W₂ i (Sum.inl 1)) = b := funext h1
  have hcv : ∀ k, (fun i => W₂ i (Sum.inr k)) = fun i => W₁ i (Sum.inr k) := fun k => funext fun i => h2 i k
  have E₁ : ∀ p q, cmp_B n (fun i => W₁ i p) (fun i => W₁ i q) = augmentedTarget n p q := by
    intro p q; rw [← cmp_entry, hW₁]
  have E₂ : ∀ p q, cmp_B n (fun i => W₂ i p) (fun i => W₂ i q) = augmentedTarget n p q := by
    intro p q; rw [← cmp_entry, hW₂]
  have a₁a₁ : cmp_B n a₁ a₁ = 0 := by simpa [augmentedTarget] using E₁ (Sum.inl 0) (Sum.inl 0)
  have a₁b : cmp_B n a₁ b = -4 := by simpa [augmentedTarget] using E₁ (Sum.inl 0) (Sum.inl 1)
  have ba₁ : cmp_B n b a₁ = -4 := by rw [cmp_B_comm]; exact a₁b
  have bb : cmp_B n b b = 0 := by simpa [augmentedTarget] using E₁ (Sum.inl 1) (Sum.inl 1)
  have va₁ : ∀ k, cmp_B n (fun i => W₁ i (Sum.inr k)) a₁ = 0 := by
    intro k; simpa [augmentedTarget] using E₁ (Sum.inr k) (Sum.inl 0)
  have vb : ∀ k, cmp_B n (fun i => W₁ i (Sum.inr k)) b = 0 := by
    intro k; simpa [augmentedTarget] using E₁ (Sum.inr k) (Sum.inl 1)
  have a₂a₂ : cmp_B n a₂ a₂ = 0 := by simpa [augmentedTarget] using E₂ (Sum.inl 0) (Sum.inl 0)
  have ba₂ : cmp_B n b a₂ = -4 := by
    have := E₂ (Sum.inl 1) (Sum.inl 0); rw [hcb] at this; simpa [augmentedTarget] using this
  have va₂ : ∀ k, cmp_B n (fun i => W₁ i (Sum.inr k)) a₂ = 0 := by
    intro k; have := E₂ (Sum.inr k) (Sum.inl 0); rw [hcv k] at this; simpa [augmentedTarget] using this
  set c := cmp_B n a₁ a₂ with hc
  have hy : W₁ᵀ *ᵥ (descartesQ n *ᵥ (a₂ - a₁ + (c / 4) • b)) = 0 := by
    funext p
    rw [cmp_transpose_mulVec]
    rcases p with p | k
    · fin_cases p
      · simp only [Fin.zero_eta, Fin.isValue, map_add, map_sub, map_smul, smul_eq_mul, Pi.zero_apply]
        rw [← ha₁, a₁a₁, a₁b, ← hc]; ring
      · simp only [Fin.mk_one, Fin.isValue, map_add, map_sub, map_smul, smul_eq_mul, Pi.zero_apply]
        rw [← hb, ba₂, ba₁, bb]; ring
    · simp only [map_add, map_sub, map_smul, smul_eq_mul, Pi.zero_apply]
      rw [va₂, va₁, vb]; ring
  have hd := cmp_eq_zero_of_transpose_mulVec hn W₁ hW₁ hy
  have ha₂eq : a₂ = a₁ - (c / 4) • b := by
    rw [← sub_eq_zero, ← hd]; abel
  have hc0 : c = 0 := by
    have h := a₂a₂
    rw [ha₂eq] at h
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul] at h
    rw [a₁a₁, a₁b, ba₁, bb] at h
    linarith
  have ha : a₂ = a₁ := by rw [ha₂eq, hc0]; simp
  ext i p
  rcases p with p | k
  · fin_cases p
    · exact (congrFun ha i).symm
    · exact (h1 i).symm
  · exact (h2 i k).symm

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
