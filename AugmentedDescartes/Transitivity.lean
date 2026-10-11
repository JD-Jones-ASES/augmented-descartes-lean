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
    (qReflection v)ᵀ * descartesQ n * qReflection v = descartesQ n := by
  have h1 : descartesQ n * vecMulVec v (descartesQ n *ᵥ v) =
      vecMulVec (descartesQ n *ᵥ v) (descartesQ n *ᵥ v) := by
    rw [mul_vecMulVec]
  have h2 : vecMulVec (descartesQ n *ᵥ v) v * descartesQ n =
      vecMulVec (descartesQ n *ᵥ v) (descartesQ n *ᵥ v) := by
    rw [vecMulVec_mul, ← mulVec_transpose, lor_descartesQ_transpose]
  have h4 : vecMulVec (descartesQ n *ᵥ v) (descartesQ n *ᵥ v) * vecMulVec v (descartesQ n *ᵥ v) =
      (v ⬝ᵥ (descartesQ n *ᵥ v)) • vecMulVec (descartesQ n *ᵥ v) (descartesQ n *ᵥ v) := by
    rw [vecMulVec_mul_vecMulVec, vecMulVec_smul, dotProduct_comm]
  unfold qReflection
  rw [transpose_sub, transpose_one, transpose_smul, transpose_vecMulVec]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
    Matrix.mul_smul, h1, h2, h4]
  ext i j
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  field_simp
  ring

/-- `⟨b₀ − b, b₀ − b⟩ = −2 ⟨b₀, b⟩` for isotropic `b₀, b`. -/
theorem tr_sub_self {n : ℕ} (b₀ b : Fin (n + 2) → ℝ) (h₀ : b₀ ⬝ᵥ (descartesQ n *ᵥ b₀) = 0)
    (h : b ⬝ᵥ (descartesQ n *ᵥ b) = 0) :
    (b₀ - b) ⬝ᵥ (descartesQ n *ᵥ (b₀ - b)) = -2 * (b₀ ⬝ᵥ (descartesQ n *ᵥ b)) := by
  rw [mulVec_sub, dotProduct_sub, sub_dotProduct, sub_dotProduct, h₀, h,
    lor_dotProduct_descartesQ_comm b b₀]
  ring

/-- The reflection in `b₀ − b` sends `b₀` to `b` when both are isotropic and pair nontrivially. -/
theorem tr_qReflection_mulVec {n : ℕ} (b₀ b : Fin (n + 2) → ℝ) (h₀ : b₀ ⬝ᵥ (descartesQ n *ᵥ b₀) = 0)
    (h : b ⬝ᵥ (descartesQ n *ᵥ b) = 0) (hp : b₀ ⬝ᵥ (descartesQ n *ᵥ b) ≠ 0) :
    qReflection (b₀ - b) *ᵥ b₀ = b := by
  have hd : (descartesQ n *ᵥ (b₀ - b)) ⬝ᵥ b₀ = -(b₀ ⬝ᵥ (descartesQ n *ᵥ b)) := by
    rw [dotProduct_comm, mulVec_sub, dotProduct_sub, h₀]
    ring
  unfold qReflection
  rw [sub_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec, op_smul_eq_smul, smul_smul,
    tr_sub_self b₀ b h₀ h, hd]
  have hk : 2 / (-2 * (b₀ ⬝ᵥ (descartesQ n *ᵥ b))) * -(b₀ ⬝ᵥ (descartesQ n *ᵥ b)) = 1 := by
    field_simp
  rw [hk, one_smul, sub_sub_cancel]

/-- The column swap of the two hyperbolic coordinates. -/
noncomputable def hyperbolicSwap (n : ℕ) : Matrix (Fin 2 ⊕ Fin n) (Fin 2 ⊕ Fin n) ℝ :=
  Matrix.fromBlocks !![0, 1; 1, 0] 0 0 1

/-- The swap preserves the target: `σᵀ T σ = T`. -/
theorem tr_hyperbolicSwap_target (n : ℕ) :
    (hyperbolicSwap n)ᵀ * augmentedTarget n * hyperbolicSwap n = augmentedTarget n := by
  unfold hyperbolicSwap augmentedTarget
  rw [fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply]
  congr 1
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · simp
  · simp
  · simp

/-- The target on a vector. -/
theorem tr_target_mulVec {n : ℕ} (y : Fin 2 ⊕ Fin n → ℝ) :
    augmentedTarget n *ᵥ y =
      Sum.elim ![-4 * y (Sum.inl 1), -4 * y (Sum.inl 0)] (fun k => 2 * y (Sum.inr k)) := by
  funext i
  rcases i with i | k
  · fin_cases i <;>
      simp [augmentedTarget, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two]
  · simp [augmentedTarget, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, diagonal_apply]

/-- Pairing two vectors in the image of a matrix. -/
theorem tr_pair {n : ℕ} (W : Matrix (Fin (n + 2)) (Fin 2 ⊕ Fin n) ℝ) (u y : Fin 2 ⊕ Fin n → ℝ) :
    (W *ᵥ u) ⬝ᵥ (descartesQ n *ᵥ (W *ᵥ y)) = u ⬝ᵥ ((Wᵀ * descartesQ n * W) *ᵥ y) := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec u Wᵀ, vecMul_transpose]

/-- A column as a matrix–vector product. -/
theorem tr_col {n : ℕ} (W : Matrix (Fin (n + 2)) (Fin 2 ⊕ Fin n) ℝ) (j : Fin 2 ⊕ Fin n)
    (b₀ : Fin (n + 2) → ℝ) (hcol : ∀ i, W i j = b₀ i) : W *ᵥ Pi.single j 1 = b₀ := by
  funext i
  rw [mulVec_single_one]
  exact hcol i

/-- Reflecting a solution: if the second column of a solution pairs nontrivially with an isotropic `b`,
some solution has second column `b`. -/
theorem tr_reflect_solution {n : ℕ} (W : Matrix (Fin (n + 2)) (Fin 2 ⊕ Fin n) ℝ)
    (hW : Wᵀ * descartesQ n * W = augmentedTarget n) (b₀ b : Fin (n + 2) → ℝ)
    (hcol : ∀ i, W i (Sum.inl 1) = b₀ i) (h : b ⬝ᵥ (descartesQ n *ᵥ b) = 0)
    (hp : b₀ ⬝ᵥ (descartesQ n *ᵥ b) ≠ 0) :
    ∃ W' : Matrix (Fin (n + 2)) (Fin 2 ⊕ Fin n) ℝ, W'ᵀ * descartesQ n * W' = augmentedTarget n ∧
      ∀ i, W' i (Sum.inl 1) = b i := by
  have hc := tr_col W _ b₀ hcol
  have h₀ : b₀ ⬝ᵥ (descartesQ n *ᵥ b₀) = 0 := by
    rw [← hc, tr_pair, hW, tr_target_mulVec]
    simp
  have hv : (b₀ - b) ⬝ᵥ (descartesQ n *ᵥ (b₀ - b)) ≠ 0 := by
    rw [tr_sub_self b₀ b h₀ h]
    exact mul_ne_zero (by norm_num) hp
  refine ⟨qReflection (b₀ - b) * W, lor_isometry_mul _ (tr_qReflection_isometry _ hv) W hW,
    fun i => ?_⟩
  rw [← congrFun (tr_qReflection_mulVec b₀ b h₀ h hp) i]
  simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, hcol]

/-- Every solution of the Soddy–Gosset relation with `b ≠ 0` is the second column of a solution of the matrix
identity. -/
theorem tr_exists_solution_of_isotropic {n : ℕ} (hn : 0 < n) (b : Fin (n + 2) → ℝ) (hb : b ≠ 0)
    (h : b ⬝ᵥ (descartesQ n *ᵥ b) = 0) :
    ∃ W : Matrix (Fin (n + 2)) (Fin 2 ⊕ Fin n) ℝ, Wᵀ * descartesQ n * W = augmentedTarget n ∧
      ∀ i, W i (Sum.inl 1) = b i := by
  obtain ⟨s, hv, ht⟩ := exists_configuration_internal n hn
  have hW₀ := augmented_descartes_general_internal hn s hv ht
  generalize augmentedMatrixOf s = W₀ at hW₀
  obtain ⟨-, hWV⟩ := lor_inv_of_identity hn W₀ hW₀
  obtain ⟨y, hby⟩ : ∃ y, W₀ *ᵥ y = b :=
    ⟨(((1 / 2 : ℝ) • lorentzG n) * W₀ᵀ * descartesQ n) *ᵥ b, by rw [mulVec_mulVec, hWV, one_mulVec]⟩
  subst hby
  have key : ∀ u, (W₀ *ᵥ u) ⬝ᵥ (descartesQ n *ᵥ (W₀ *ᵥ y)) = u ⬝ᵥ (augmentedTarget n *ᵥ y) := by
    intro u
    rw [tr_pair, hW₀]
  have hyy := key y
  rw [h, tr_target_mulVec] at hyy
  simp only [dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two, Sum.elim_inl, Sum.elim_inr,
    Matrix.cons_val_zero, Matrix.cons_val_one] at hyy
  by_cases hy0 : y (Sum.inl 0) = 0
  · -- reflect the swapped solution, whose second column is the first column of `W₀`
    have hy1 : y (Sum.inl 1) ≠ 0 := by
      intro hy1
      apply hb
      have hsum : ∑ k, y (Sum.inr k) * (2 * y (Sum.inr k)) = 0 := by
        rw [hy0, hy1] at hyy
        linarith
      rw [Finset.sum_eq_zero_iff_of_nonneg (fun k _ => by nlinarith [mul_self_nonneg (y (Sum.inr k))])]
        at hsum
      have hy : y = 0 := by
        funext i
        rcases i with i | k
        · fin_cases i
          · exact hy0
          · exact hy1
        · have := hsum k (Finset.mem_univ _)
          have h2 : y (Sum.inr k) * y (Sum.inr k) = 0 := by linarith
          exact mul_self_eq_zero.mp h2
      rw [hy, mulVec_zero]
    have hW₁ : (W₀ * hyperbolicSwap n)ᵀ * descartesQ n * (W₀ * hyperbolicSwap n) =
        augmentedTarget n := by
      rw [transpose_mul]
      calc (hyperbolicSwap n)ᵀ * W₀ᵀ * descartesQ n * (W₀ * hyperbolicSwap n)
          = (hyperbolicSwap n)ᵀ * (W₀ᵀ * descartesQ n * W₀) * hyperbolicSwap n := by
            simp only [Matrix.mul_assoc]
        _ = augmentedTarget n := by rw [hW₀, tr_hyperbolicSwap_target]
    have hcol₁ : ∀ i, (W₀ * hyperbolicSwap n) i (Sum.inl 1) = W₀ i (Sum.inl 0) := by
      intro i
      simp [Matrix.mul_apply, hyperbolicSwap, Fintype.sum_sum_type, Fin.sum_univ_two]
    refine tr_reflect_solution _ hW₁ (fun i => W₀ i (Sum.inl 0)) _ hcol₁ h ?_
    rw [← tr_col W₀ (Sum.inl 0) _ (fun i => rfl), key, tr_target_mulVec]
    simpa using hy1
  · refine tr_reflect_solution W₀ hW₀ (fun i => W₀ i (Sum.inl 1)) _ (fun i => rfl) h ?_
    rw [← tr_col W₀ (Sum.inl 1) _ (fun i => rfl), key, tr_target_mulVec]
    simpa using hy0

/-- The converse of the Soddy–Gosset theorem (LMW Theorem 3.1, existence): every nonzero `b` with
`(Σ bᵢ)² = n Σ bᵢ²` is the curvature vector of a pairwise tangent family of valid oriented spheres
(`bᵢ ≠ 0`) and hyperplanes (`bᵢ = 0`). -/
theorem converse_soddy_gosset_internal {n : ℕ} (hn : 0 < n) (b : Fin (n + 2) → ℝ) (hb : b ≠ 0)
    (h : (∑ i, b i) ^ 2 = n * ∑ i, b i ^ 2) :
    ∃ s : Fin (n + 2) → OrientedSphere n, (∀ i, OrientedSphere.IsValid (s i)) ∧
      (∀ i j, i ≠ j → OrientedSphere.Tangent (s i) (s j)) ∧
      ∀ i, OrientedSphere.curvature (s i) = b i := by
  have hiso := (soddy_gosset_iff_isotropic_internal hn b).mp h
  obtain ⟨W, hW, hcol⟩ := tr_exists_solution_of_isotropic hn b hb hiso
  obtain ⟨s, ⟨hv, ht, hs⟩, -⟩ := augmented_descartes_converse_internal hn W hW
  refine ⟨s, hv, ht, fun i => ?_⟩
  rw [← rows_row_inl_one, ← hcol i, ← hs]
  rfl

/-- The converse of the Soddy–Gosset theorem for spheres: every `b` with no zero entry and
`(Σ bᵢ)² = n Σ bᵢ²` is the curvature vector of a pairwise tangent family of spheres. -/
theorem converse_soddy_gosset_spheres_internal {n : ℕ} (hn : 0 < n) (b : Fin (n + 2) → ℝ) (hb : ∀ i, b i ≠ 0)
    (h : (∑ i, b i) ^ 2 = n * ∑ i, b i ^ 2) :
    ∃ x : Fin (n + 2) → EuclideanSpace ℝ (Fin n), ∃ r : Fin (n + 2) → ℝ,
      PairwiseTangent x r ∧ ∀ i, 1 / r i = b i := by
  have hb0 : b ≠ 0 := fun h0 => hb 0 (by simp [h0])
  have hiso := (soddy_gosset_iff_isotropic_internal hn b).mp h
  obtain ⟨W, hW, hcol⟩ := tr_exists_solution_of_isotropic hn b hb0 hiso
  obtain ⟨⟨x, r⟩, ⟨hxr, hm⟩, -⟩ :=
    augmented_descartes_converse_spheres_internal hn W hW (fun i => by rw [hcol]; exact hb i)
  refine ⟨x, r, hxr, fun i => ?_⟩
  rw [← hcol i, ← hm]
  simp [augmentedMatrix, sphereRow]

/-- A sum over `Fin (n + 2)` split at `n` and `n + 1`. -/
theorem tr_sum_split (n : ℕ) (f : ℕ → ℝ) :
    ∑ i : Fin (n + 2), f i = ∑ i : Fin n, f i + f n + f (n + 1) := by
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  simp

/-- Existence of a pairwise tangent family of spheres in every dimension. -/
theorem exists_pairwiseTangent_internal (n : ℕ) (hn : 0 < n) :
    ∃ x : Fin (n + 2) → EuclideanSpace ℝ (Fin n), ∃ r : Fin (n + 2) → ℝ, PairwiseTangent x r := by
  rcases Nat.lt_or_ge n 2 with h2 | h2
  · obtain rfl : n = 1 := by omega
    obtain ⟨x, r, hxr, -⟩ := converse_soddy_gosset_spheres_internal (n := 1) one_pos ![1, 1, -1 / 2]
      (by intro i; fin_cases i <;> norm_num) (by simp [Fin.sum_univ_succ]; norm_num)
    exact ⟨x, r, hxr⟩
  · have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast h2
    have hn1 : (0 : ℝ) < n - 1 := by linarith
    have hn1' : (n : ℝ) - 1 ≠ 0 := hn1.ne'
    set F : ℕ → ℝ := fun m => if m < n then 1 else if m = n then 2 * n / (n - 1) else
      2 * n * (n + 1) / (n - 1) ^ 2 with hF
    have hFi : ∀ i : Fin n, F i = 1 := fun i => by simp [hF, i.isLt]
    have hFn : F n = 2 * n / (n - 1) := by simp [hF]
    have hFn1 : F (n + 1) = 2 * n * (n + 1) / (n - 1) ^ 2 := by
      have e1 : ¬ (n + 1 < n) := by omega
      simp [hF, e1]
    have hpos : ∀ i : Fin (n + 2), F i ≠ 0 := by
      intro i
      simp only [hF]
      split_ifs
      · norm_num
      · exact (div_pos (by positivity) hn1).ne'
      · exact (div_pos (by positivity) (pow_pos hn1 2)).ne'
    have hs1 : ∑ i : Fin (n + 2), F i = n + 2 * n / (n - 1) + 2 * n * (n + 1) / (n - 1) ^ 2 := by
      rw [tr_sum_split n F, hFn, hFn1]
      simp [hFi]
    have hs2 : ∑ i : Fin (n + 2), F i ^ 2 =
        n + (2 * n / (n - 1)) ^ 2 + (2 * n * (n + 1) / (n - 1) ^ 2) ^ 2 := by
      rw [tr_sum_split n (fun m => F m ^ 2)]
      simp only [hFn, hFn1, hFi]
      simp
    obtain ⟨x, r, hxr, -⟩ := converse_soddy_gosset_spheres_internal hn (fun i => F i) hpos
      (by
        rw [hs1, hs2]
        field_simp
        ring)
    exact ⟨x, r, hxr⟩

end AugmentedDescartes
