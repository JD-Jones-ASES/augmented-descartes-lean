module

public import AugmentedDescartes.Defs

/-!
# Rows

The encoding: Lorentz pairings of sphere and hyperplane rows (ARCH.md §1). Lane `rows`.
-/

@[expose] public section

namespace AugmentedDescartes

open Matrix

/-- The pairing of two sphere rows: `(r² + s² − dist x y ²) / (2 r s)`. -/
theorem rows_lorentz_sphereRow {n : ℕ} (x y : EuclideanSpace ℝ (Fin n)) (r s : ℝ) (hr : r ≠ 0) (hs : s ≠ 0) :
    lorentz (sphereRow x r) (sphereRow y s) = (r ^ 2 + s ^ 2 - dist x y ^ 2) / (2 * r * s) := sorry

/-- The pairing of a sphere row and a hyperplane row: `(⟪h, x⟫ − δ) / r`. -/
theorem rows_lorentz_sphereRow_planeRow {n : ℕ} (x h : EuclideanSpace ℝ (Fin n)) (r δ : ℝ) (hr : r ≠ 0) :
    lorentz (sphereRow x r) (planeRow h δ) = (inner ℝ h x - δ) / r := sorry

/-- The pairing of two hyperplane rows: `⟪h, k⟫`. -/
theorem rows_lorentz_planeRow {n : ℕ} (h k : EuclideanSpace ℝ (Fin n)) (δ ε : ℝ) :
    lorentz (planeRow h δ) (planeRow k ε) = inner ℝ h k := sorry

/-- The pairing is symmetric. -/
theorem rows_lorentz_comm {n : ℕ} (u v : Fin 2 ⊕ Fin n → ℝ) : lorentz u v = lorentz v u := sorry

/-- The second coordinate of a row is the curvature. -/
theorem rows_row_inl_one {n : ℕ} (s : OrientedSphere n) :
    OrientedSphere.row s (Sum.inl 1) = OrientedSphere.curvature s := sorry

/-- Tangency of valid objects is symmetric. -/
theorem rows_tangent_comm {n : ℕ} (s t : OrientedSphere n) (hs : OrientedSphere.IsValid s)
    (ht : OrientedSphere.IsValid t) : OrientedSphere.Tangent s t ↔ OrientedSphere.Tangent t s := sorry

/-- Decoding a row: a sphere `(v/b, 1/b)` when `b ≠ 0`, the hyperplane `(v, b̄/2)` when `b = 0`. -/
noncomputable def decodeRow {n : ℕ} (w : Fin 2 ⊕ Fin n → ℝ) : OrientedSphere n :=
  if w (Sum.inl 1) = 0 then Sum.inr (WithLp.toLp 2 (fun k => w (Sum.inr k)), w (Sum.inl 0) / 2)
  else Sum.inl (WithLp.toLp 2 (fun k => w (Sum.inr k) / w (Sum.inl 1)), 1 / w (Sum.inl 1))

/-- A row of Lorentz norm `1` is the row of its decoding. -/
theorem rows_row_decodeRow {n : ℕ} (w : Fin 2 ⊕ Fin n → ℝ) (hw : lorentz w w = 1) :
    OrientedSphere.row (decodeRow w) = w := sorry

/-- The decoding of a row of Lorentz norm `1` is valid. -/
theorem rows_decodeRow_isValid {n : ℕ} (w : Fin 2 ⊕ Fin n → ℝ) (hw : lorentz w w = 1) :
    OrientedSphere.IsValid (decodeRow w) := sorry

/-- Decoding the row of a valid object gives it back. -/
theorem rows_decodeRow_row {n : ℕ} (s : OrientedSphere n) (hs : OrientedSphere.IsValid s) :
    decodeRow (OrientedSphere.row s) = s := sorry

/-- A sphere row has Lorentz norm `1`. -/
theorem lorentz_sphereRow_self_internal {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) (r : ℝ) (hr : r ≠ 0) :
    lorentz (sphereRow x r) (sphereRow x r) = 1 := sorry

/-- Two sphere rows pair to `−1` exactly when the spheres are tangent in the signed sense. -/
theorem lorentz_sphereRow_eq_neg_one_iff_internal {n : ℕ} (x y : EuclideanSpace ℝ (Fin n)) (r s : ℝ)
    (hr : r ≠ 0) (hs : s ≠ 0) :
    lorentz (sphereRow x r) (sphereRow y s) = -1 ↔ dist x y ^ 2 = (r + s) ^ 2 := sorry

/-- A sphere row and a hyperplane row pair to `−1` exactly when `⟪h, x⟫ − δ = −r`. -/
theorem lorentz_sphereRow_planeRow_eq_neg_one_iff_internal {n : ℕ} (x h : EuclideanSpace ℝ (Fin n)) (r δ : ℝ)
    (hr : r ≠ 0) :
    lorentz (sphereRow x r) (planeRow h δ) = -1 ↔ inner ℝ h x - δ = -r := sorry

/-- Two unit-normal hyperplane rows pair to `−1` exactly when the normals are opposite. -/
theorem lorentz_planeRow_eq_neg_one_iff_internal {n : ℕ} (h k : EuclideanSpace ℝ (Fin n)) (δ ε : ℝ)
    (hh : ‖h‖ = 1) (hk : ‖k‖ = 1) :
    lorentz (planeRow h δ) (planeRow k ε) = -1 ↔ k = -h := sorry

/-- A valid oriented sphere or hyperplane has a row of Lorentz norm `1`. -/
theorem lorentz_row_self_internal {n : ℕ} (s : OrientedSphere n) (hs : OrientedSphere.IsValid s) :
    lorentz (OrientedSphere.row s) (OrientedSphere.row s) = 1 := sorry

/-- Two valid oriented spheres or hyperplanes pair to `−1` exactly when they are tangent. -/
theorem lorentz_row_eq_neg_one_iff_internal {n : ℕ} (s t : OrientedSphere n) (hs : OrientedSphere.IsValid s)
    (ht : OrientedSphere.IsValid t) :
    lorentz (OrientedSphere.row s) (OrientedSphere.row t) = -1 ↔ OrientedSphere.Tangent s t := sorry

/-- Augmented coordinates are a global coordinate system (LMW, after (3.9)): valid oriented spheres
and hyperplanes with the same row are equal. -/
theorem row_injOn_valid_internal {n : ℕ} (s t : OrientedSphere n) (hs : OrientedSphere.IsValid s)
    (ht : OrientedSphere.IsValid t) (h : OrientedSphere.row s = OrientedSphere.row t) : s = t := sorry

/-- Every row of Lorentz norm `1` is the row of a valid oriented sphere (second coordinate nonzero) or
hyperplane (second coordinate zero). -/
theorem exists_orientedSphere_of_lorentz_self_internal {n : ℕ} (w : Fin 2 ⊕ Fin n → ℝ) (hw : lorentz w w = 1) :
    ∃ s : OrientedSphere n, OrientedSphere.IsValid s ∧ OrientedSphere.row s = w := sorry

end AugmentedDescartes
