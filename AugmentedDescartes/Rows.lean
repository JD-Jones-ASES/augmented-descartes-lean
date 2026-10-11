module

public import AugmentedDescartes.Defs

/-!
# Rows

The encoding: Lorentz pairings of sphere and hyperplane rows (PROOF.md §1).
-/

@[expose] public section

namespace AugmentedDescartes

open Matrix

/-- The coordinate form of the real inner product on `EuclideanSpace`. -/
theorem rows_sum_mul_eq_inner {n : ℕ} (x y : EuclideanSpace ℝ (Fin n)) :
    ∑ k, x k * y k = inner ℝ x y := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct, star_trivial]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

/-- The pairing of two sphere rows: `(r² + s² − dist x y ²) / (2 r s)`. -/
theorem rows_lorentz_sphereRow {n : ℕ} (x y : EuclideanSpace ℝ (Fin n)) (r s : ℝ) (hr : r ≠ 0) (hs : s ≠ 0) :
    lorentz (sphereRow x r) (sphereRow y s) = (r ^ 2 + s ^ 2 - dist x y ^ 2) / (2 * r * s) := by
  have hxy : ∑ k, x k / r * (y k / s) = inner ℝ x y / (r * s) := by
    rw [← rows_sum_mul_eq_inner, Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ => ?_
    field_simp
  have hd : dist x y ^ 2 = ‖x‖ ^ 2 - 2 * inner ℝ x y + ‖y‖ ^ 2 := by
    rw [dist_eq_norm, norm_sub_sq_real]
  simp only [lorentz, sphereRow, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hxy, hd]
  field_simp
  ring

/-- The pairing of a sphere row and a hyperplane row: `(⟪h, x⟫ − δ) / r`. -/
theorem rows_lorentz_sphereRow_planeRow {n : ℕ} (x h : EuclideanSpace ℝ (Fin n)) (r δ : ℝ) (hr : r ≠ 0) :
    lorentz (sphereRow x r) (planeRow h δ) = (inner ℝ h x - δ) / r := by
  have hxh : ∑ k, x k / r * h k = inner ℝ h x / r := by
    rw [real_inner_comm, ← rows_sum_mul_eq_inner, Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  simp only [lorentz, sphereRow, planeRow, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  rw [hxh]
  field_simp
  ring

/-- The pairing of two hyperplane rows: `⟪h, k⟫`. -/
theorem rows_lorentz_planeRow {n : ℕ} (h k : EuclideanSpace ℝ (Fin n)) (δ ε : ℝ) :
    lorentz (planeRow h δ) (planeRow k ε) = inner ℝ h k := by
  simp only [lorentz, planeRow, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [rows_sum_mul_eq_inner]
  ring

/-- The pairing is symmetric. -/
theorem rows_lorentz_comm {n : ℕ} (u v : Fin 2 ⊕ Fin n → ℝ) : lorentz u v = lorentz v u := by
  simp only [lorentz]
  congr 1
  · ring
  · exact Finset.sum_congr rfl fun k _ => mul_comm _ _

/-- The second coordinate of a row is the curvature. -/
theorem rows_row_inl_one {n : ℕ} (s : OrientedSphere n) :
    OrientedSphere.row s (Sum.inl 1) = OrientedSphere.curvature s := by
  rcases s with ⟨x, r⟩ | ⟨h, δ⟩
  · simp [OrientedSphere.row, OrientedSphere.curvature, sphereRow]
  · simp [OrientedSphere.row, OrientedSphere.curvature, planeRow]

/-- Tangency of valid objects is symmetric. -/
theorem rows_tangent_comm {n : ℕ} (s t : OrientedSphere n) (hs : OrientedSphere.IsValid s)
    (ht : OrientedSphere.IsValid t) : OrientedSphere.Tangent s t ↔ OrientedSphere.Tangent t s := by
  rcases s with ⟨x, r⟩ | ⟨h, δ⟩ <;> rcases t with ⟨y, s⟩ | ⟨k, ε⟩
  · simp only [OrientedSphere.Tangent, Sum.elim_inl]
    rw [dist_comm, add_comm r s]
  · exact Iff.rfl
  · exact Iff.rfl
  · simp only [OrientedSphere.Tangent, Sum.elim_inr]
    constructor
    · rintro rfl
      simp
    · rintro rfl
      simp

/-- Decoding a row: a sphere `(v/b, 1/b)` when `b ≠ 0`, the hyperplane `(v, b̄/2)` when `b = 0`. -/
noncomputable def decodeRow {n : ℕ} (w : Fin 2 ⊕ Fin n → ℝ) : OrientedSphere n :=
  if w (Sum.inl 1) = 0 then Sum.inr (WithLp.toLp 2 (fun k => w (Sum.inr k)), w (Sum.inl 0) / 2)
  else Sum.inl (WithLp.toLp 2 (fun k => w (Sum.inr k) / w (Sum.inl 1)), 1 / w (Sum.inl 1))

/-- The Lorentz norm in coordinates. -/
theorem rows_lorentz_self_eq {n : ℕ} (w : Fin 2 ⊕ Fin n → ℝ) :
    lorentz w w = -(w (Sum.inl 0) * w (Sum.inl 1)) + ∑ k, w (Sum.inr k) * w (Sum.inr k) := by
  simp only [lorentz]
  ring

/-- A row of Lorentz norm `1` is the row of its decoding. -/
theorem rows_row_decodeRow {n : ℕ} (w : Fin 2 ⊕ Fin n → ℝ) (hw : lorentz w w = 1) :
    OrientedSphere.row (decodeRow w) = w := by
  rw [rows_lorentz_self_eq] at hw
  by_cases hb : w (Sum.inl 1) = 0
  · simp only [decodeRow, hb, ↓reduceIte, OrientedSphere.row, Sum.elim_inr, planeRow]
    funext i
    rcases i with j | k
    · fin_cases j
      · simp only [Fin.zero_eta, Fin.isValue, Sum.elim_inl, Matrix.cons_val_zero]
        ring
      · simp [hb]
    · simp
  · simp only [decodeRow, hb, ↓reduceIte, OrientedSphere.row, Sum.elim_inl, sphereRow]
    have hS : ‖(WithLp.toLp 2 (fun k => w (Sum.inr k) / w (Sum.inl 1)) : EuclideanSpace ℝ (Fin n))‖ ^ 2 =
        (∑ k, w (Sum.inr k) * w (Sum.inr k)) / w (Sum.inl 1) ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq, Finset.sum_div]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    funext i
    rcases i with j | k
    · fin_cases j
      · simp only [Fin.zero_eta, Fin.isValue, Sum.elim_inl, Matrix.cons_val_zero]
        have hS' : ∑ k, w (Sum.inr k) * w (Sum.inr k) = 1 + w (Sum.inl 0) * w (Sum.inl 1) := by
          linarith
        rw [hS, hS']
        field_simp
        ring
      · simp
    · simp only [Sum.elim_inr]
      field_simp

/-- The decoding of a row of Lorentz norm `1` is valid. -/
theorem rows_decodeRow_isValid {n : ℕ} (w : Fin 2 ⊕ Fin n → ℝ) (hw : lorentz w w = 1) :
    OrientedSphere.IsValid (decodeRow w) := by
  rw [rows_lorentz_self_eq] at hw
  by_cases hb : w (Sum.inl 1) = 0
  · simp only [decodeRow, hb, ↓reduceIte, OrientedSphere.IsValid, Sum.elim_inr]
    rw [← pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero, EuclideanSpace.real_norm_sq_eq]
    have hsq : ∑ k, w (Sum.inr k) ^ 2 = ∑ k, w (Sum.inr k) * w (Sum.inr k) :=
      Finset.sum_congr rfl fun k _ => sq _
    rw [hsq]
    rw [hb] at hw
    linarith
  · simp only [decodeRow, hb, ↓reduceIte, OrientedSphere.IsValid, Sum.elim_inl]
    exact one_div_ne_zero hb

/-- Decoding the row of a valid object gives it back. -/
theorem rows_decodeRow_row {n : ℕ} (s : OrientedSphere n) (hs : OrientedSphere.IsValid s) :
    decodeRow (OrientedSphere.row s) = s := by
  rcases s with ⟨x, r⟩ | ⟨h, δ⟩
  · simp only [OrientedSphere.IsValid, Sum.elim_inl] at hs
    have h1 : OrientedSphere.row (Sum.inl (x, r) : OrientedSphere n) (Sum.inl 1) = 1 / r := by
      simp [OrientedSphere.row, sphereRow]
    have h1' : OrientedSphere.row (Sum.inl (x, r) : OrientedSphere n) (Sum.inl 1) ≠ 0 := by
      rw [h1]; exact one_div_ne_zero hs
    simp only [decodeRow, h1', ↓reduceIte]
    rw [h1]
    congr 1
    refine Prod.ext ?_ ?_
    · refine WithLp.ofLp_injective 2 (funext fun k => ?_)
      simp only [OrientedSphere.row, Sum.elim_inl, sphereRow, Sum.elim_inr]
      field_simp
    · field_simp
  · have h1 : OrientedSphere.row (Sum.inr (h, δ) : OrientedSphere n) (Sum.inl 1) = 0 := by
      simp [OrientedSphere.row, planeRow]
    simp only [decodeRow, h1, ↓reduceIte]
    congr 1
    refine Prod.ext ?_ ?_
    · refine WithLp.ofLp_injective 2 (funext fun k => ?_)
      simp [OrientedSphere.row, planeRow]
    · simp [OrientedSphere.row, planeRow]

/-- A sphere row has Lorentz norm `1`. -/
theorem lorentz_sphereRow_self_internal {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) (r : ℝ) (hr : r ≠ 0) :
    lorentz (sphereRow x r) (sphereRow x r) = 1 := by
  rw [rows_lorentz_sphereRow x x r r hr hr, dist_self]
  field_simp
  ring

/-- Two sphere rows pair to `−1` exactly when the spheres are tangent in the signed sense. -/
theorem lorentz_sphereRow_eq_neg_one_iff_internal {n : ℕ} (x y : EuclideanSpace ℝ (Fin n)) (r s : ℝ)
    (hr : r ≠ 0) (hs : s ≠ 0) :
    lorentz (sphereRow x r) (sphereRow y s) = -1 ↔ dist x y ^ 2 = (r + s) ^ 2 := by
  have hne : 2 * r * s ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero hr) hs
  rw [rows_lorentz_sphereRow x y r s hr hs, div_eq_iff hne]
  constructor <;> intro h <;> linear_combination -h

/-- A sphere row and a hyperplane row pair to `−1` exactly when `⟪h, x⟫ − δ = −r`. -/
theorem lorentz_sphereRow_planeRow_eq_neg_one_iff_internal {n : ℕ} (x h : EuclideanSpace ℝ (Fin n)) (r δ : ℝ)
    (hr : r ≠ 0) :
    lorentz (sphereRow x r) (planeRow h δ) = -1 ↔ inner ℝ h x - δ = -r := by
  rw [rows_lorentz_sphereRow_planeRow x h r δ hr, div_eq_iff hr]
  constructor <;> intro h <;> linear_combination h

/-- Two unit-normal hyperplane rows pair to `−1` exactly when the normals are opposite. -/
theorem lorentz_planeRow_eq_neg_one_iff_internal {n : ℕ} (h k : EuclideanSpace ℝ (Fin n)) (δ ε : ℝ)
    (hh : ‖h‖ = 1) (hk : ‖k‖ = 1) :
    lorentz (planeRow h δ) (planeRow k ε) = -1 ↔ k = -h := by
  rw [rows_lorentz_planeRow]
  constructor
  · intro hi
    have h2 : ‖h + k‖ ^ 2 = 0 := by
      rw [norm_add_sq_real, hh, hk, hi]
      norm_num
    have h3 : h + k = 0 := norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h2)
    rw [add_comm] at h3
    exact add_eq_zero_iff_eq_neg.mp h3
  · rintro rfl
    rw [inner_neg_right, real_inner_self_eq_norm_sq, hh]
    norm_num

/-- A valid oriented sphere or hyperplane has a row of Lorentz norm `1`. -/
theorem lorentz_row_self_internal {n : ℕ} (s : OrientedSphere n) (hs : OrientedSphere.IsValid s) :
    lorentz (OrientedSphere.row s) (OrientedSphere.row s) = 1 := by
  rcases s with ⟨x, r⟩ | ⟨h, δ⟩
  · simp only [OrientedSphere.IsValid, OrientedSphere.row, Sum.elim_inl] at hs ⊢
    exact lorentz_sphereRow_self_internal x r hs
  · simp only [OrientedSphere.IsValid, OrientedSphere.row, Sum.elim_inr] at hs ⊢
    rw [rows_lorentz_planeRow, real_inner_self_eq_norm_sq, hs]
    norm_num

/-- Two valid oriented spheres or hyperplanes pair to `−1` exactly when they are tangent. -/
theorem lorentz_row_eq_neg_one_iff_internal {n : ℕ} (s t : OrientedSphere n) (hs : OrientedSphere.IsValid s)
    (ht : OrientedSphere.IsValid t) :
    lorentz (OrientedSphere.row s) (OrientedSphere.row t) = -1 ↔ OrientedSphere.Tangent s t := by
  rcases s with ⟨x, r⟩ | ⟨h, δ⟩ <;> rcases t with ⟨y, s⟩ | ⟨k, ε⟩ <;>
    simp only [OrientedSphere.IsValid, OrientedSphere.row, OrientedSphere.Tangent, Sum.elim_inl,
      Sum.elim_inr] at hs ht ⊢
  · exact lorentz_sphereRow_eq_neg_one_iff_internal x y r s hs ht
  · exact lorentz_sphereRow_planeRow_eq_neg_one_iff_internal x k r ε hs
  · rw [rows_lorentz_comm]
    exact lorentz_sphereRow_planeRow_eq_neg_one_iff_internal y h s δ ht
  · exact lorentz_planeRow_eq_neg_one_iff_internal h k δ ε hs ht

/-- Augmented coordinates are a global coordinate system (LMW, after (3.9)): valid oriented spheres
and hyperplanes with the same row are equal. -/
theorem row_injOn_valid_internal {n : ℕ} (s t : OrientedSphere n) (hs : OrientedSphere.IsValid s)
    (ht : OrientedSphere.IsValid t) (h : OrientedSphere.row s = OrientedSphere.row t) : s = t := by
  rw [← rows_decodeRow_row s hs, ← rows_decodeRow_row t ht, h]

/-- Every row of Lorentz norm `1` is the row of a valid oriented sphere (second coordinate nonzero) or
hyperplane (second coordinate zero). -/
theorem exists_orientedSphere_of_lorentz_self_internal {n : ℕ} (w : Fin 2 ⊕ Fin n → ℝ) (hw : lorentz w w = 1) :
    ∃ s : OrientedSphere n, OrientedSphere.IsValid s ∧ OrientedSphere.row s = w :=
  ⟨decodeRow w, rows_decodeRow_isValid w hw, rows_row_decodeRow w hw⟩

/-- The pairing is the bilinear form of `lorentzG`: `lorentz u v = u ⬝ᵥ (G *ᵥ v)`. -/
theorem rows_lorentz_eq_dotProduct_mulVec {n : ℕ} (u v : Fin 2 ⊕ Fin n → ℝ) :
    lorentz u v = u ⬝ᵥ (lorentzG n *ᵥ v) := by
  simp [lorentz, lorentzG, dotProduct, mulVec, Fintype.sum_sum_type, Fin.sum_univ_two, Matrix.one_apply]
  ring

/-- The Gram matrix of the rows of `W` under the Lorentz form: `(W G Wᵀ) i j = lorentz (W i) (W j)`. -/
theorem rows_mul_lorentzG_mul_transpose_apply {n m : ℕ} (W : Matrix (Fin m) (Fin 2 ⊕ Fin n) ℝ) (i j : Fin m) :
    (W * lorentzG n * Wᵀ) i j = lorentz (W i) (W j) := by
  rw [rows_lorentz_eq_dotProduct_mulVec, Matrix.mul_assoc]
  simp [Matrix.mul_apply, dotProduct, mulVec]

end AugmentedDescartes
