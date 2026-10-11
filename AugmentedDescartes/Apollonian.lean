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
      else (if i = j then 1 else 0) := by
  simp only [apollonianGen, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
    Matrix.vecMulVec_apply, Pi.single_apply, smul_eq_mul]
  split_ifs <;> subst_vars <;> first | ring1 | simp_all

/-- The pairing is linear in a row combination. -/
theorem apo_lorentz_vecMul {n : ℕ} (c : Fin (n + 2) → ℝ) (W : Matrix (Fin (n + 2)) (Fin 2 ⊕ Fin n) ℝ)
    (v : Fin 2 ⊕ Fin n → ℝ) : lorentz (c ᵥ* W) v = ∑ i, c i * lorentz (W i) v := by
  rw [lor_lorentz_eq_dotProduct, ← Matrix.dotProduct_mulVec]
  simp only [dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [lor_lorentz_eq_dotProduct]
  rfl

/-- `n − 1 ≠ 0` in the reals for `n ≥ 2`. -/
theorem apo_sub_one_ne_zero {n : ℕ} (hn : 2 ≤ n) : (n : ℝ) - 1 ≠ 0 := by
  have h1 : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  exact sub_ne_zero.mpr h1.ne'

/-- The diagonal entry of row `k`: `2/(n−1) − 2n/(n−1) + 1 = −1`. -/
theorem apo_diag {n : ℕ} (hn : 2 ≤ n) : 2 / ((n : ℝ) - 1) - 2 * n / ((n : ℝ) - 1) + 1 = -1 := by
  have hne := apo_sub_one_ne_zero hn
  rw [div_sub_div_same, div_add_one hne, div_eq_iff hne]
  ring

/-- The correction vector `u` of `Sₖ = 1 + eₖ uᵀ`: `uₖ = −2`, `uᵢ = 2/(n−1)` otherwise. -/
noncomputable def apo_u (n : ℕ) (k i : Fin (n + 2)) : ℝ := if i = k then -2 else 2 / ((n : ℝ) - 1)

/-- `Sₖ = 1 + eₖ uᵀ` entrywise. -/
theorem apo_apollonianGen_apply' {n : ℕ} (hn : 2 ≤ n) (k m i : Fin (n + 2)) :
    apollonianGen n k m i = (if m = i then 1 else 0) + (if m = k then apo_u n k i else 0) := by
  rw [apo_apollonianGen_apply]
  unfold apo_u
  split_ifs <;> subst_vars <;> first | ring1 | linarith [apo_diag hn] | simp_all

/-- The column sums of `Sₖ`. -/
theorem apo_colsum {n : ℕ} (hn : 2 ≤ n) (k i : Fin (n + 2)) :
    ∑ m, apollonianGen n k m i = 1 + apo_u n k i := by
  simp only [apo_apollonianGen_apply' hn, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ,
    if_true]

/-- The column dot products of `Sₖ`. -/
theorem apo_prodsum {n : ℕ} (hn : 2 ≤ n) (k i j : Fin (n + 2)) :
    ∑ m, apollonianGen n k m i * apollonianGen n k m j =
      (if i = j then 1 else 0) + (if i = k then apo_u n k j else 0) + (if j = k then apo_u n k i else 0) +
        apo_u n k i * apo_u n k j := by
  have h : ∀ m, apollonianGen n k m i * apollonianGen n k m j =
      (if m = i then (if i = j then 1 else 0) else 0) +
        (if m = i then (if i = k then apo_u n k j else 0) else 0) +
        (if m = j then (if j = k then apo_u n k i else 0) else 0) +
        (if m = k then apo_u n k i * apo_u n k j else 0) := by
    intro m
    rw [apo_apollonianGen_apply' hn, apo_apollonianGen_apply' hn]
    split_ifs <;> subst_vars <;> first | ring1 | simp_all
  simp only [h, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- The entries of `Aᵀ Q B` as a dot product of columns. -/
theorem apo_transpose_mul_mul_apply {ι κ ν : Type*} [Fintype ι] (A : Matrix ι κ ℝ) (Q : Matrix ι ι ℝ)
    (B : Matrix ι ν ℝ) (i : κ) (j : ν) :
    (Aᵀ * Q * B) i j = (fun b => A b i) ⬝ᵥ (Q *ᵥ fun b => B b j) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, dotProduct, Matrix.mulVec, Finset.sum_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

/-- The entries of `Qₙ`. -/
theorem apo_descartesQ_apply (n : ℕ) (i j : Fin (n + 2)) :
    descartesQ n i j = (if i = j then 1 else 0) - (n : ℝ)⁻¹ := by
  simp [descartesQ, Matrix.sub_apply, Matrix.one_apply]

/-- The Apollonian generators preserve the Descartes form (GLMWY III, after (4.1)): `Sₖᵀ Qₙ Sₖ = Qₙ`. -/
theorem apollonianGen_mem_aut_internal {n : ℕ} (hn : 2 ≤ n) (k : Fin (n + 2)) :
    (apollonianGen n k)ᵀ * descartesQ n * apollonianGen n k = descartesQ n := by
  ext i j
  rw [apo_transpose_mul_mul_apply, lor_dotProduct_descartesQ, apo_prodsum hn, apo_colsum hn, apo_colsum hn,
    apo_descartesQ_apply]
  have hne := apo_sub_one_ne_zero hn
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  unfold apo_u
  split_ifs <;> subst_vars <;> first | ring1 | (field_simp; ring1) | simp_all | field_simp

/-- Replacing sphere `k` of a configuration by its Apollonian reflection gives a configuration. -/
theorem apollonian_reflection_internal {n : ℕ} (hn : 2 ≤ n) (W : Matrix (Fin (n + 2)) (Fin 2 ⊕ Fin n) ℝ)
    (hW : Wᵀ * descartesQ n * W = augmentedTarget n) (k : Fin (n + 2)) :
    (apollonianGen n k * W)ᵀ * descartesQ n * (apollonianGen n k * W) = augmentedTarget n :=
  lor_isometry_mul _ (apollonianGen_mem_aut_internal hn k) W hW

/-- The reflected row is `(2/(n−1)) Σ_{i ≠ k} (row i) − (row k)`; in particular the two curvatures
satisfy `bₖ + bₖ' = (2/(n−1)) Σ_{i ≠ k} bᵢ` (LMW (2.1) at `n = 2`). -/
theorem apollonianGen_mul_apply_internal {n : ℕ} (hn : 2 ≤ n) (W : Matrix (Fin (n + 2)) (Fin 2 ⊕ Fin n) ℝ)
    (k : Fin (n + 2)) (j : Fin 2 ⊕ Fin n) :
    (apollonianGen n k * W) k j = (2 / ((n : ℝ) - 1)) * ∑ i ∈ Finset.univ.erase k, W i j - W k j := by
  rw [Matrix.mul_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ k)]
  have hk : apollonianGen n k k k = -1 := by
    rw [apo_apollonianGen_apply, if_pos rfl, if_pos rfl, apo_diag hn]
  have hrest : ∑ m ∈ Finset.univ.erase k, apollonianGen n k k m * W m j =
      ∑ m ∈ Finset.univ.erase k, 2 / ((n : ℝ) - 1) * W m j :=
    Finset.sum_congr rfl fun m hm => by
      rw [apo_apollonianGen_apply, if_pos rfl, if_neg (Finset.ne_of_mem_erase hm)]
  rw [hk, hrest, ← Finset.mul_sum]
  ring

/-- Rows of a matrix product are row combinations. -/
theorem apo_mul_row {n : ℕ} (A : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ)
    (W : Matrix (Fin (n + 2)) (Fin 2 ⊕ Fin n) ℝ) (k : Fin (n + 2)) : (A * W) k = A k ᵥ* W := by
  funext l
  rfl

/-- The rows of a solution are independent. -/
theorem apo_vecMul_inj {n : ℕ} (hn : 0 < n) (W : Matrix (Fin (n + 2)) (Fin 2 ⊕ Fin n) ℝ)
    (hW : Wᵀ * descartesQ n * W = augmentedTarget n) (x y : Fin (n + 2) → ℝ) (h : x ᵥ* W = y ᵥ* W) :
    x = y := by
  have hWV := (lor_inv_of_identity hn W hW).2
  calc x = x ᵥ* (W * (((1 / 2 : ℝ) • lorentzG n) * Wᵀ * descartesQ n)) := by rw [hWV, Matrix.vecMul_one]
    _ = (x ᵥ* W) ᵥ* (((1 / 2 : ℝ) • lorentzG n) * Wᵀ * descartesQ n) := by rw [Matrix.vecMul_vecMul]
    _ = (y ᵥ* W) ᵥ* (((1 / 2 : ℝ) • lorentzG n) * Wᵀ * descartesQ n) := by rw [h]
    _ = y := by rw [Matrix.vecMul_vecMul, hWV, Matrix.vecMul_one]

/-- The pairing of a row combination with a row of a configuration: `2 cⱼ − Σ c`. -/
theorem apo_pair_row {n : ℕ} (W : Matrix (Fin (n + 2)) (Fin 2 ⊕ Fin n) ℝ)
    (h1 : ∀ i, lorentz (W i) (W i) = 1) (h2 : ∀ i j, i ≠ j → lorentz (W i) (W j) = -1)
    (c : Fin (n + 2) → ℝ) (j : Fin (n + 2)) :
    lorentz (c ᵥ* W) (W j) = 2 * c j - ∑ i, c i := by
  rw [apo_lorentz_vecMul]
  have h : ∀ i, c i * lorentz (W i) (W j) = 2 * (if i = j then c i else 0) - c i := by
    intro i
    by_cases hij : i = j
    · subst hij; rw [h1, if_pos rfl]; ring
    · rw [h2 i j hij, if_neg hij]; ring
  rw [Finset.sum_congr rfl fun i _ => h i, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_ite_eq']
  simp

/-- The norm of a row combination: `Σ cᵢ (2 cᵢ − Σ c)`. -/
theorem apo_norm_comb {n : ℕ} (W : Matrix (Fin (n + 2)) (Fin 2 ⊕ Fin n) ℝ)
    (h1 : ∀ i, lorentz (W i) (W i) = 1) (h2 : ∀ i j, i ≠ j → lorentz (W i) (W j) = -1)
    (c : Fin (n + 2) → ℝ) :
    lorentz (c ᵥ* W) (c ᵥ* W) = ∑ i, c i * (2 * c i - ∑ l, c l) := by
  rw [apo_lorentz_vecMul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [rows_lorentz_comm, apo_pair_row W h1 h2]

/-- `|Fin (n + 2) ∖ {k}| = n + 1`. -/
theorem apo_card_erase {n : ℕ} (k : Fin (n + 2)) :
    ((Finset.univ.erase k).card : ℝ) = n + 1 := by
  rw [Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ, Fintype.card_fin,
    show n + 2 - 1 = n + 1 by omega, Nat.cast_add, Nat.cast_one]

/-- Soddy's two spheres in every dimension (LMW, footnote 3; GLMWY III §4.1): the rows of Lorentz norm
`1` pairing to `−1` with every row of a configuration but the `k`-th are exactly the `k`-th row and its
Apollonian reflection, which are distinct. -/
theorem two_tangent_rows_internal {n : ℕ} (hn : 2 ≤ n) (W : Matrix (Fin (n + 2)) (Fin 2 ⊕ Fin n) ℝ)
    (hW : Wᵀ * descartesQ n * W = augmentedTarget n) (k : Fin (n + 2)) :
    (∀ w : Fin 2 ⊕ Fin n → ℝ, (lorentz w w = 1 ∧ ∀ i, i ≠ k → lorentz w (W i) = -1) ↔
      (w = W k ∨ w = (apollonianGen n k * W) k)) ∧ W k ≠ (apollonianGen n k * W) k := by
  have hn0 : 0 < n := by omega
  have hne := apo_sub_one_ne_zero hn
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  obtain ⟨h1, h2⟩ := (augmented_identity_iff_lorentz_internal hn0 W).mp hW
  obtain ⟨hVW, _⟩ := lor_inv_of_identity hn0 W hW
  have hW' := apollonian_reflection_internal hn W hW k
  obtain ⟨h1', h2'⟩ := (augmented_identity_iff_lorentz_internal hn0 _).mp hW'
  have hfix : ∀ i, i ≠ k → (apollonianGen n k * W) i = W i := by
    intro i hi
    funext l
    rw [Matrix.mul_apply]
    have : ∀ m, apollonianGen n k i m * W m l = if i = m then W m l else 0 := by
      intro m
      rw [apo_apollonianGen_apply, if_neg hi]
      split_ifs <;> ring
    rw [Finset.sum_congr rfl fun m _ => this m, Finset.sum_ite_eq]
    simp
  refine ⟨fun w => ⟨fun ⟨hww, hwi⟩ => ?_, fun hw => ?_⟩, fun heq => ?_⟩
  · -- the forward direction: solve for the row coefficients `c = w Vᵀ`
    set V := ((1 / 2 : ℝ) • lorentzG n) * Wᵀ * descartesQ n with hV
    set c := w ᵥ* V with hc
    have hcW : c ᵥ* W = w := by rw [hc, Matrix.vecMul_vecMul, hVW, Matrix.vecMul_one]
    rw [← hcW] at hww hwi
    rw [apo_norm_comb W h1 h2] at hww
    obtain ⟨t, ht⟩ : ∃ t : ℝ, t = ((∑ l, c l) - 1) / 2 := ⟨_, rfl⟩
    have hS : ∑ l, c l = 2 * t + 1 := by rw [ht]; ring
    have hcj : ∀ j, j ≠ k → c j = t := by
      intro j hj
      have := hwi j hj
      rw [apo_pair_row W h1 h2] at this
      rw [ht]; linarith
    have e0 : ∑ i ∈ Finset.univ.erase k, c i = ∑ i ∈ Finset.univ.erase k, t :=
      Finset.sum_congr rfl fun j hj => hcj j (Finset.ne_of_mem_erase hj)
    have hsum : ∑ l, c l = c k + (n + 1) * t := by
      rw [← Finset.add_sum_erase Finset.univ c (Finset.mem_univ k), e0, Finset.sum_const, nsmul_eq_mul,
        apo_card_erase]
    have hck : c k = 1 - ((n : ℝ) - 1) * t := by linear_combination hS - hsum
    have e1 : ∑ i ∈ Finset.univ.erase k, c i * (2 * c i - ∑ l, c l) =
        ∑ i ∈ Finset.univ.erase k, t * (2 * t - ∑ l, c l) :=
      Finset.sum_congr rfl fun j hj => by rw [hcj j (Finset.ne_of_mem_erase hj)]
    rw [← Finset.add_sum_erase Finset.univ (fun i => c i * (2 * c i - ∑ l, c l)) (Finset.mem_univ k), e1,
      Finset.sum_const, nsmul_eq_mul, apo_card_erase, hS] at hww
    have hnorm : c k * (2 * c k - (2 * t + 1)) - ((n : ℝ) + 1) * t = 1 := by linear_combination hww
    rw [hck] at hnorm
    have hkey : (2 * (n : ℝ)) * (t * (((n : ℝ) - 1) * t - 2)) = 0 := by linear_combination hnorm
    have hrow : ∀ l, w l = c k * W k l + t * ∑ i ∈ Finset.univ.erase k, W i l := by
      intro l
      have e2 : ∑ i ∈ Finset.univ.erase k, c i * W i l = ∑ i ∈ Finset.univ.erase k, t * W i l :=
        Finset.sum_congr rfl fun j hj => by rw [hcj j (Finset.ne_of_mem_erase hj)]
      rw [← hcW]
      change ∑ i, c i * W i l = _
      rw [← Finset.add_sum_erase Finset.univ (fun i => c i * W i l) (Finset.mem_univ k), e2, Finset.mul_sum]
    rcases mul_eq_zero.mp hkey with h | h
    · exact absurd h (mul_ne_zero two_ne_zero hnR)
    rcases mul_eq_zero.mp h with h0 | ha
    · left
      funext l
      rw [hrow l, hck, h0]
      ring
    · right
      have hta : t = 2 / ((n : ℝ) - 1) := by
        rw [eq_div_iff hne]; linear_combination ha
      have h2' : ((n : ℝ) - 1) * (2 / ((n : ℝ) - 1)) = 2 := by field_simp
      funext l
      rw [hrow l, hck, apollonianGen_mul_apply_internal hn, hta, h2']
      ring
  · rcases hw with rfl | rfl
    · exact ⟨h1 k, fun i hi => h2 k i (Ne.symm hi)⟩
    · refine ⟨h1' k, fun i hi => ?_⟩
      rw [← hfix i hi]
      exact h2' k i (Ne.symm hi)
  · -- distinctness: the row coefficients `eₖ` and `Sₖ k` differ at `k`
    have hrow1 : W k = (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ) k ᵥ* W := by
      rw [← apo_mul_row (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ) W k, Matrix.one_mul]
    rw [hrow1, apo_mul_row] at heq
    have := congrFun (apo_vecMul_inj hn0 W hW _ _ heq) k
    rw [Matrix.one_apply_eq, apo_apollonianGen_apply, if_pos rfl, if_pos rfl, apo_diag hn] at this
    norm_num at this

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
        u = s k ∨ u = t := by
  have hn0 : 0 < n := by omega
  have hW := augmented_descartes_general_internal hn0 s hv ht
  have hrowW : ∀ i, augmentedMatrixOf s i = OrientedSphere.row (s i) := fun i => rfl
  obtain ⟨hiff, hdist⟩ := two_tangent_rows_internal hn (augmentedMatrixOf s) hW k
  set w' := (apollonianGen n k * augmentedMatrixOf s) k with hw'
  obtain ⟨hww, hwi⟩ := (hiff w').mpr (Or.inr rfl)
  have htv := rows_decodeRow_isValid w' hww
  have hrt := rows_row_decodeRow w' hww
  refine ⟨decodeRow w', htv, fun heq => ?_, fun i hi => ?_, ?_, fun u hu hut => ?_⟩
  · apply hdist
    rw [hrowW, ← heq, hrt]
  · rw [← lorentz_row_eq_neg_one_iff_internal _ _ htv (hv i), hrt, ← hrowW]
    exact hwi i hi
  · rw [← rows_row_inl_one (decodeRow w'), hrt, ← rows_row_inl_one (s k), hw',
      apollonianGen_mul_apply_internal hn]
    simp only [hrowW, rows_row_inl_one]
    ring
  · have huu := lorentz_row_self_internal u hu
    have hui : ∀ i, i ≠ k → lorentz (OrientedSphere.row u) (augmentedMatrixOf s i) = -1 := by
      intro i hi
      rw [hrowW, lorentz_row_eq_neg_one_iff_internal _ _ hu (hv i)]
      exact hut i hi
    rcases (hiff _).mp ⟨huu, hui⟩ with h | h
    · left
      exact row_injOn_valid_internal _ _ hu (hv k) (by rw [h, hrowW])
    · right
      exact row_injOn_valid_internal _ _ hu htv (by rw [h, hrt])

end AugmentedDescartes
