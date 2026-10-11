module

public import AugmentedDescartes.Main
public import AugmentedDescartes.Transitivity

/-!
# Compatible orientations

The power polynomial of a row is negative exactly on the row's open interior (a ball, the exterior of a ball, a
half-space); the vector of the powers of a solution of the augmented identity at a point is Descartes-null with a
sum of the sign of the total curvature `B`, which is nonzero, so after multiplication by `B` the interiors are
pairwise disjoint (Cauchy–Schwarz on the other `n` entries), at most two rows are hyperplanes and no three
boundaries share a finite point (Cauchy–Schwarz on the other `n − 1` entries).
-/

@[expose] public section

namespace AugmentedDescartes

open Matrix

/-- The power polynomial of a sphere row is `(dist(y, x)² − r²)/r`. -/
theorem rowPower_sphereRow_internal {n : ℕ} (x y : EuclideanSpace ℝ (Fin n))
    (r : ℝ) (hr : r ≠ 0) :
    rowPower (sphereRow x r) y = (dist y x ^ 2 - r ^ 2) / r := by
  have hxy : ∑ k, x k / r * y k = inner ℝ x y / r := by
    rw [← rows_sum_mul_eq_inner, Finset.sum_div]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hd : dist y x ^ 2 = ‖y‖ ^ 2 - 2 * inner ℝ x y + ‖x‖ ^ 2 := by
    rw [dist_eq_norm, norm_sub_sq_real, real_inner_comm]
  simp only [rowPower, sphereRow, Sum.elim_inl, Sum.elim_inr,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hxy, hd]
  field_simp
  ring

/-- The power polynomial of a hyperplane row is `2(δ − ⟪h, y⟫)`. -/
theorem rowPower_planeRow_internal {n : ℕ} (h y : EuclideanSpace ℝ (Fin n))
    (δ : ℝ) : rowPower (planeRow h δ) y = 2 * (δ - inner ℝ h y) := by
  simp only [rowPower, planeRow, Sum.elim_inl, Sum.elim_inr,
    Matrix.cons_val_zero, Matrix.cons_val_one, zero_mul, zero_sub]
  rw [rows_sum_mul_eq_inner]
  ring

/-- For `r > 0` the power is negative exactly on the open ball `dist(y, x) < r`. -/
theorem rowPower_sphereRow_neg_iff_of_pos_internal {n : ℕ}
    (x y : EuclideanSpace ℝ (Fin n)) (r : ℝ) (hr : 0 < r) :
    rowPower (sphereRow x r) y < 0 ↔ dist y x < r := by
  rw [rowPower_sphereRow_internal x y r hr.ne', div_lt_iff₀ hr, zero_mul, sub_lt_zero]
  exact sq_lt_sq₀ dist_nonneg hr.le

/-- For `r < 0` the power is negative exactly on the open exterior `−r < dist(y, x)`. -/
theorem rowPower_sphereRow_neg_iff_of_neg_internal {n : ℕ}
    (x y : EuclideanSpace ℝ (Fin n)) (r : ℝ) (hr : r < 0) :
    rowPower (sphereRow x r) y < 0 ↔ -r < dist y x := by
  rw [rowPower_sphereRow_internal x y r hr.ne, div_lt_iff_of_neg hr, zero_mul, sub_pos]
  simpa only [neg_sq] using sq_lt_sq₀ (neg_nonneg.mpr hr.le) (dist_nonneg : 0 ≤ dist y x)

/-- The power of a hyperplane row is negative exactly on the open half-space `δ < ⟪h, y⟫` into which `h`
points. -/
theorem rowPower_planeRow_neg_iff_internal {n : ℕ}
    (h y : EuclideanSpace ℝ (Fin n)) (δ : ℝ) :
    rowPower (planeRow h δ) y < 0 ↔ δ < inner ℝ h y := by
  rw [rowPower_planeRow_internal]
  constructor <;> intro hxy <;> linarith

/-- A Descartes-null vector with positive sum cannot have two negative coordinates.
The complement of two coordinates has cardinality `n`, so Cauchy–Schwarz rules this out. -/
theorem orientation_null_no_two_negative {n : ℕ} (b : Fin (n + 2) → ℝ)
    (hb : (∑ k, b k) ^ 2 = n * ∑ k, b k ^ 2) (hpos : 0 < ∑ k, b k)
    (i j : Fin (n + 2)) (hij : i ≠ j) : ¬ (b i < 0 ∧ b j < 0) := by
  classical
  rintro ⟨hi, hj⟩
  let s := (Finset.univ.erase i).erase j
  have hi_mem : i ∈ (Finset.univ : Finset (Fin (n + 2))) := Finset.mem_univ i
  have hj_mem : j ∈ (Finset.univ : Finset (Fin (n + 2))).erase i :=
    Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩
  have hcard : s.card = n := by
    dsimp [s]
    rw [Finset.card_erase_of_mem hj_mem, Finset.card_erase_of_mem hi_mem,
      Finset.card_univ, Fintype.card_fin]
    omega
  have hsum : (∑ k ∈ s, b k) + b j + b i = ∑ k, b k := by
    rw [Finset.sum_erase_add _ _ hj_mem, Finset.sum_erase_add _ _ hi_mem]
  have hsum_sq : (∑ k ∈ s, b k ^ 2) + b j ^ 2 + b i ^ 2 = ∑ k, b k ^ 2 := by
    rw [Finset.sum_erase_add _ _ hj_mem, Finset.sum_erase_add _ _ hi_mem]
  have hrest : (∑ k, b k) < ∑ k ∈ s, b k := by linarith
  have hsq_lt : (∑ k, b k) ^ 2 < (∑ k ∈ s, b k) ^ 2 :=
    (sq_lt_sq₀ hpos.le (by linarith)).mpr hrest
  have hcs := sq_sum_le_card_mul_sum_sq (s := s) (f := b)
  rw [hcard] at hcs
  have htail : (n : ℝ) * (b j ^ 2 + b i ^ 2) ≥ 0 := by positivity
  nlinarith

/-- Scaling all coordinates preserves the homogeneous Descartes relation. -/
theorem orientation_null_scale {n : ℕ} (b : Fin (n + 2) → ℝ) (c : ℝ)
    (hb : (∑ k, b k) ^ 2 = n * ∑ k, b k ^ 2) :
    (∑ k, c * b k) ^ 2 = n * ∑ k, (c * b k) ^ 2 := by
  rw [← Finset.mul_sum, mul_pow, hb]
  simp_rw [mul_pow]
  rw [← Finset.mul_sum]
  ring

/-- A Descartes-null vector with nonzero sum has at most two zero coordinates (Cauchy–Schwarz on the other
`n − 1`). -/
theorem orientation_null_no_three_zero {n : ℕ} (hn : 0 < n) (b : Fin (n + 2) → ℝ)
    (hb : (∑ l, b l) ^ 2 = n * ∑ l, b l ^ 2) (hs : (∑ l, b l) ≠ 0)
    (i j k : Fin (n + 2)) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ¬ (b i = 0 ∧ b j = 0 ∧ b k = 0) := by
  classical
  rintro ⟨hi, hj, hk⟩
  let s := ((Finset.univ.erase i).erase j).erase k
  have hi_mem : i ∈ (Finset.univ : Finset (Fin (n + 2))) := Finset.mem_univ i
  have hj_mem : j ∈ (Finset.univ : Finset (Fin (n + 2))).erase i :=
    Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩
  have hk_mem : k ∈ ((Finset.univ : Finset (Fin (n + 2))).erase i).erase j :=
    Finset.mem_erase.mpr ⟨hjk.symm, Finset.mem_erase.mpr ⟨hik.symm, Finset.mem_univ k⟩⟩
  have hcard : s.card = n - 1 := by
    dsimp [s]
    rw [Finset.card_erase_of_mem hk_mem, Finset.card_erase_of_mem hj_mem,
      Finset.card_erase_of_mem hi_mem, Finset.card_univ, Fintype.card_fin]
    omega
  have hsum : (∑ l ∈ s, b l) + b k + b j + b i = ∑ l, b l := by
    rw [Finset.sum_erase_add _ _ hk_mem, Finset.sum_erase_add _ _ hj_mem,
      Finset.sum_erase_add _ _ hi_mem]
  have hsum_sq : (∑ l ∈ s, b l ^ 2) + b k ^ 2 + b j ^ 2 + b i ^ 2 = ∑ l, b l ^ 2 := by
    rw [Finset.sum_erase_add _ _ hk_mem, Finset.sum_erase_add _ _ hj_mem,
      Finset.sum_erase_add _ _ hi_mem]
  simp only [hi, hj, hk, zero_pow (by decide : 2 ≠ 0), add_zero] at hsum hsum_sq
  have hcs := sq_sum_le_card_mul_sum_sq (s := s) (f := b)
  rw [hcard, Nat.cast_sub (by omega), Nat.cast_one, hsum, hsum_sq] at hcs
  have hnonneg : 0 ≤ ∑ l, b l ^ 2 := Finset.sum_nonneg fun l _ => sq_nonneg _
  have hsq_zero : (∑ l, b l) ^ 2 = 0 := by nlinarith
  exact hs (sq_eq_zero_iff.mp hsq_zero)

/-- The Lorentz norm of the sum of the rows fixes a strictly positive discriminant. -/
theorem orientation_sum_discriminant {n : ℕ} (hn : 0 < n)
    (W : Matrix (Fin (n + 2)) (Fin 2 ⊕ Fin n) ℝ)
    (hW : Wᵀ * descartesQ n * W = augmentedTarget n) :
    (∑ i, W i (Sum.inl 0)) * (∑ i, W i (Sum.inl 1)) -
      (∑ k, (∑ i, W i (Sum.inr k)) ^ 2) = (n : ℝ) * (n + 2) := by
  have h := lor_lorentz_vecMul hn W hW (fun _ => 1) (fun _ => 1)
  simp only [lorentz, Matrix.vecMul, dotProduct, one_mul, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, Nat.cast_add,
    Nat.cast_ofNat] at h
  simp only [sq] at ⊢
  nlinarith

/-- The sum of the row powers, in terms of the column sums. -/
theorem orientation_sum_rowPower {n : ℕ}
    (W : Matrix (Fin (n + 2)) (Fin 2 ⊕ Fin n) ℝ) (y : EuclideanSpace ℝ (Fin n)) :
    (∑ i, rowPower (W i) y) = (∑ i, W i (Sum.inl 1)) * ‖y‖ ^ 2 -
      2 * (∑ k, (∑ i, W i (Sum.inr k)) * y k) + ∑ i, W i (Sum.inl 0) := by
  simp only [rowPower, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.sum_mul, ← Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul]

/-- Multiplying the sum of the powers by the total curvature is everywhere positive.
The difference from `n(n+2)` is an explicit sum of squares. -/
theorem orientation_sum_rowPower_pos {n : ℕ} (hn : 0 < n)
    (W : Matrix (Fin (n + 2)) (Fin 2 ⊕ Fin n) ℝ)
    (hW : Wᵀ * descartesQ n * W = augmentedTarget n) (y : EuclideanSpace ℝ (Fin n)) :
    0 < (∑ i, W i (Sum.inl 1)) * ∑ i, rowPower (W i) y := by
  let B := ∑ i, W i (Sum.inl 1)
  let V := fun k => ∑ i, W i (Sum.inr k)
  have hsq : (∑ k, (B * y k - V k) ^ 2) =
      B ^ 2 * ‖y‖ ^ 2 - 2 * B * (∑ k, V k * y k) + ∑ k, V k ^ 2 := by
    calc
      _ = ∑ k, (B ^ 2 * (y k) ^ 2 - (2 * B) * (V k * y k) + V k ^ 2) := by
        exact Finset.sum_congr rfl fun k _ => by ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
          ← Finset.mul_sum, ← EuclideanSpace.real_norm_sq_eq]
  have hdisc := orientation_sum_discriminant hn W hW
  have hsum := orientation_sum_rowPower W y
  have hsq_nonneg : 0 ≤ ∑ k, (B * y k - V k) ^ 2 :=
    Finset.sum_nonneg fun k _ => sq_nonneg _
  have hdim : 0 < (n : ℝ) * (n + 2) := by positivity
  dsimp [B, V] at hsq hsq_nonneg
  rw [hsum]
  nlinarith

/-- Evaluating all row powers at any point gives a Descartes-null vector. -/
theorem orientation_rowPower_null {n : ℕ} (hn : 0 < n)
    (W : Matrix (Fin (n + 2)) (Fin 2 ⊕ Fin n) ℝ)
    (hW : Wᵀ * descartesQ n * W = augmentedTarget n) (y : EuclideanSpace ℝ (Fin n)) :
    (∑ i, rowPower (W i) y) ^ 2 = n * ∑ i, rowPower (W i) y ^ 2 := by
  let u : Fin 2 ⊕ Fin n → ℝ := Sum.elim ![1, ‖y‖ ^ 2] (fun k => -2 * y k)
  have hu : u ⬝ᵥ (augmentedTarget n *ᵥ u) = 0 := by
    rw [tr_target_mulVec]
    simp only [u, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two,
      Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one]
    have hsp : (∑ k, (-2 * y k) * (2 * (-2 * y k))) = 8 * ∑ k, y k ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [hsp, ← EuclideanSpace.real_norm_sq_eq]
    ring
  have hpower : W *ᵥ u = fun i => rowPower (W i) y := by
    funext i
    simp only [u, rowPower, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
      Fin.sum_univ_two, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one]
    have hsp : (∑ k, W i (Sum.inr k) * (-2 * y k)) = -2 * ∑ k, W i (Sum.inr k) * y k := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [hsp]
    ring
  apply (soddy_gosset_iff_isotropic_internal hn _).mpr
  rw [← hpower, tr_pair W u u, hW, hu]

/-- Compatible orientations (LMW §3, the definition of an oriented Descartes configuration: interiors disjoint with
the given orientations or with all reversed; the total curvature is never zero and its sign fixes the orientation,
GLMWY III §3.1, p. 6): for a solution of the identity the total curvature `B = Σ W k (Sum.inl 1)` is nonzero, and no point
`y` has `B Fᵢ(y) < 0` and `B Fⱼ(y) < 0` for two rows `i ≠ j`, `Fᵢ = rowPower (W i)`. -/
theorem augmented_orientation_internal {n : ℕ} (hn : 0 < n)
    (W : Matrix (Fin (n + 2)) (Fin 2 ⊕ Fin n) ℝ)
    (hW : Wᵀ * descartesQ n * W = augmentedTarget n) :
    (∑ k, W k (Sum.inl 1)) ≠ 0 ∧
      ∀ (i j : Fin (n + 2)), i ≠ j → ∀ y : EuclideanSpace ℝ (Fin n),
        ¬ ((∑ k, W k (Sum.inl 1)) * rowPower (W i) y < 0 ∧
          (∑ k, W k (Sum.inl 1)) * rowPower (W j) y < 0) := by
  refine ⟨?_, ?_⟩
  · intro hB
    have h := orientation_sum_rowPower_pos hn W hW (0 : EuclideanSpace ℝ (Fin n))
    simp only [hB, zero_mul, lt_self_iff_false] at h
  · intro i j hij y
    apply orientation_null_no_two_negative
      (fun k => (∑ l, W l (Sum.inl 1)) * rowPower (W k) y)
      (orientation_null_scale _ _ (orientation_rowPower_null hn W hW y)) _ i j hij
    rw [← Finset.mul_sum]
    exact orientation_sum_rowPower_pos hn W hW y

/-- The same as disjoint sets: `{y | B Fᵢ(y) < 0}` and `{y | B Fⱼ(y) < 0}` are disjoint for `i ≠ j`. -/
theorem augmented_orientation_disjoint_internal {n : ℕ} (hn : 0 < n)
    (W : Matrix (Fin (n + 2)) (Fin 2 ⊕ Fin n) ℝ)
    (hW : Wᵀ * descartesQ n * W = augmentedTarget n)
    (i j : Fin (n + 2)) (hij : i ≠ j) :
    Disjoint {y : EuclideanSpace ℝ (Fin n) |
      (∑ k, W k (Sum.inl 1)) * rowPower (W i) y < 0}
      {y : EuclideanSpace ℝ (Fin n) |
        (∑ k, W k (Sum.inl 1)) * rowPower (W j) y < 0} := by
  apply Set.disjoint_left.mpr
  intro y hi hj
  exact (augmented_orientation_internal hn W hW).2 i j hij y ⟨hi, hj⟩

/-- At most two rows of a solution of the identity have zero curvature, the hyperplane rows (the four cases of the
curvature vector of a positively oriented configuration, GLMWY III §3.1, p. 6; LMW's list after Theorem 3.1), by
Cauchy–Schwarz. -/
theorem augmented_no_three_zero_curvatures_internal {n : ℕ} (hn : 0 < n)
    (W : Matrix (Fin (n + 2)) (Fin 2 ⊕ Fin n) ℝ)
    (hW : Wᵀ * descartesQ n * W = augmentedTarget n)
    (i j k : Fin (n + 2)) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ¬ (W i (Sum.inl 1) = 0 ∧ W j (Sum.inl 1) = 0 ∧ W k (Sum.inl 1) = 0) := by
  exact orientation_null_no_three_zero hn (fun l => W l (Sum.inl 1))
    (main_soddy_gosset_of_identity hn W hW) (augmented_orientation_internal hn W hW).1
    i j k hij hik hjk

/-- No three rows of a solution of the identity have power `0` at one point `y` of `ℝⁿ`: no three boundaries share
a finite point (LMW's distinct tangencies, at finite points). -/
theorem augmented_no_three_boundaries_internal {n : ℕ} (hn : 0 < n)
    (W : Matrix (Fin (n + 2)) (Fin 2 ⊕ Fin n) ℝ)
    (hW : Wᵀ * descartesQ n * W = augmentedTarget n)
    (i j k : Fin (n + 2)) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (y : EuclideanSpace ℝ (Fin n)) :
    ¬ (rowPower (W i) y = 0 ∧ rowPower (W j) y = 0 ∧ rowPower (W k) y = 0) := by
  apply orientation_null_no_three_zero hn (fun l => rowPower (W l) y)
    (orientation_rowPower_null hn W hW y) _ i j k hij hik hjk
  intro hsum
  have h := orientation_sum_rowPower_pos hn W hW y
  simp only [hsum, mul_zero, lt_self_iff_false] at h

end AugmentedDescartes
