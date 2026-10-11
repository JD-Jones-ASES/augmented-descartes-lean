module

public import AugmentedDescartes.Lorentz

/-!
# Main

The forward theorems: the identity, Soddy–Gosset, the curvature–centre identity (ARCH.md §3). Lane `main`.
-/

@[expose] public section

namespace AugmentedDescartes

open Matrix

/-- An entry of `Mᵀ Qₙ M` in coordinates: the Descartes form of two columns. -/
theorem main_entry {n : ℕ} {α : Type*} (M : Matrix (Fin (n + 2)) α ℝ) (j k : α) :
    (Mᵀ * descartesQ n * M) j k =
      ∑ i, M i j * M i k - (n : ℝ)⁻¹ * ((∑ i, M i j) * ∑ i, M i k) := by
  have h : (Mᵀ * descartesQ n * M) j k =
      (fun i => M i j) ⬝ᵥ (descartesQ n *ᵥ fun i => M i k) := by
    rw [Matrix.mul_assoc]
    rfl
  rw [h, lor_dotProduct_descartesQ]

/-- Deleting columns: `(W.submatrix id f)ᵀ Qₙ (W.submatrix id f)` is `(Wᵀ Qₙ W).submatrix f f`. -/
theorem main_submatrix_entry {n : ℕ} {α β : Type*} (W : Matrix (Fin (n + 2)) α ℝ) (f : β → α)
    (j k : β) :
    ((W.submatrix id f)ᵀ * descartesQ n * W.submatrix id f) j k = (Wᵀ * descartesQ n * W) (f j) (f k) := by
  rw [main_entry, main_entry]
  rfl

/-- The `(b, b)` entry of a solution: `Σ bᵢ² − (1/n)(Σ bᵢ)² = 0`. -/
theorem main_entry_inl_inl {n : ℕ} (W : Matrix (Fin (n + 2)) (Fin 2 ⊕ Fin n) ℝ)
    (hW : Wᵀ * descartesQ n * W = augmentedTarget n) :
    ∑ i, W i (Sum.inl 1) ^ 2 - (n : ℝ)⁻¹ * (∑ i, W i (Sum.inl 1)) ^ 2 = 0 := by
  have h := congrFun (congrFun hW (Sum.inl 1)) (Sum.inl 1)
  rw [main_entry] at h
  simp only [augmentedTarget, Matrix.fromBlocks_apply₁₁, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one] at h
  simpa [sq] using h

/-- The Soddy–Gosset relation from the `(b, b)` entry of a solution. -/
theorem main_soddy_gosset_of_identity {n : ℕ} (hn : 0 < n)
    (W : Matrix (Fin (n + 2)) (Fin 2 ⊕ Fin n) ℝ)
    (hW : Wᵀ * descartesQ n * W = augmentedTarget n) :
    (∑ i, W i (Sum.inl 1)) ^ 2 = n * ∑ i, W i (Sum.inl 1) ^ 2 := by
  have h := main_entry_inl_inl W hW
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have h2 : ∑ i, W i (Sum.inl 1) ^ 2 = (n : ℝ)⁻¹ * (∑ i, W i (Sum.inl 1)) ^ 2 := by linarith
  rw [h2, ← mul_assoc, mul_inv_cancel₀ hn', one_mul]

/-- The curvature–centre identity of a solution: the identity with the first row and column deleted. -/
theorem main_curvature_center_of_identity {n : ℕ} (W : Matrix (Fin (n + 2)) (Fin 2 ⊕ Fin n) ℝ)
    (hW : Wᵀ * descartesQ n * W = augmentedTarget n) :
    (W.submatrix id (Sum.elim (fun _ => Sum.inl 1) Sum.inr))ᵀ * descartesQ n *
      W.submatrix id (Sum.elim (fun _ => Sum.inl 1) Sum.inr) = curvatureCenterTarget n := by
  ext j k
  rw [main_submatrix_entry, hW]
  rcases j with j | j <;> rcases k with k | k <;>
    simp [augmentedTarget, curvatureCenterTarget, Matrix.diagonal_apply]

/-- The augmented Euclidean Descartes theorem (LMW Theorem 3.3) for spheres and hyperplanes. -/
theorem augmented_descartes_general_internal {n : ℕ} (hn : 0 < n) (s : Fin (n + 2) → OrientedSphere n)
    (hv : ∀ i, OrientedSphere.IsValid (s i))
    (ht : ∀ i j, i ≠ j → OrientedSphere.Tangent (s i) (s j)) :
    (augmentedMatrixOf s)ᵀ * descartesQ n * augmentedMatrixOf s = augmentedTarget n := by
  refine (augmented_identity_iff_lorentz_internal hn _).2 ⟨fun i => ?_, fun i j hij => ?_⟩
  · exact lorentz_row_self_internal (s i) (hv i)
  · exact (lorentz_row_eq_neg_one_iff_internal (s i) (s j) (hv i) (hv j)).2 (ht i j hij)

/-- The augmented Euclidean Descartes theorem (LMW Theorem 3.3) for spheres of nonzero curvature:
`Wᵀ Qₙ W = [[0, −4, 0], [−4, 0, 0], [0, 0, 2 Iₙ]]`. -/
theorem augmented_descartes_internal {n : ℕ} (hn : 0 < n) (x : Fin (n + 2) → EuclideanSpace ℝ (Fin n))
    (r : Fin (n + 2) → ℝ) (h : PairwiseTangent x r) :
    (augmentedMatrix x r)ᵀ * descartesQ n * augmentedMatrix x r = augmentedTarget n :=
  augmented_descartes_general_internal hn (fun i => Sum.inl (x i, r i)) (fun i => h.1 i)
    (fun i j hij => h.2 i j hij)

/-- The Soddy–Gosset theorem for spheres and hyperplanes (curvature `0` for a hyperplane). -/
theorem soddy_gosset_general_internal {n : ℕ} (hn : 0 < n) (s : Fin (n + 2) → OrientedSphere n)
    (hv : ∀ i, OrientedSphere.IsValid (s i))
    (ht : ∀ i j, i ≠ j → OrientedSphere.Tangent (s i) (s j)) :
    (∑ i, OrientedSphere.curvature (s i)) ^ 2 = n * ∑ i, OrientedSphere.curvature (s i) ^ 2 := by
  have h := main_soddy_gosset_of_identity hn _ (augmented_descartes_general_internal hn s hv ht)
  simpa only [augmentedMatrixOf, Matrix.of_apply, rows_row_inl_one] using h

/-- The Soddy–Gosset theorem (LMW Theorem 3.1, (1.2)): `(Σ 1/rᵢ)² = n Σ (1/rᵢ)²`. -/
theorem soddy_gosset_internal {n : ℕ} (hn : 0 < n) (x : Fin (n + 2) → EuclideanSpace ℝ (Fin n))
    (r : Fin (n + 2) → ℝ) (h : PairwiseTangent x r) :
    (∑ i, 1 / r i) ^ 2 = n * ∑ i, (1 / r i) ^ 2 :=
  soddy_gosset_general_internal hn (fun i => Sum.inl (x i, r i)) (fun i => h.1 i)
    (fun i j hij => h.2 i j hij)

/-- The curvature–centre matrix of a family is its augmented matrix with the first column deleted. -/
theorem main_curvatureCenterMatrixOf_eq {n : ℕ} (s : Fin (n + 2) → OrientedSphere n) :
    curvatureCenterMatrixOf s =
      (augmentedMatrixOf s).submatrix id (Sum.elim (fun _ => Sum.inl 1) Sum.inr) := by
  ext i c
  rcases c with c | k
  · simp [curvatureCenterMatrixOf, augmentedMatrixOf, Fin.fin_one_eq_zero c]
  · simp [curvatureCenterMatrixOf, augmentedMatrixOf]

/-- The curvature–centre matrix of spheres is that of the family `Sum.inl (xᵢ, rᵢ)`. -/
theorem main_curvatureCenterMatrix_eq {n : ℕ} (x : Fin (n + 2) → EuclideanSpace ℝ (Fin n))
    (r : Fin (n + 2) → ℝ) :
    curvatureCenterMatrix x r = curvatureCenterMatrixOf (fun i => Sum.inl (x i, r i)) := by
  ext i c
  rcases c with c | k
  · simp [curvatureCenterMatrix, curvatureCenterMatrixOf, OrientedSphere.row, sphereRow,
      Fin.fin_one_eq_zero c]
  · simp [curvatureCenterMatrix, curvatureCenterMatrixOf, OrientedSphere.row, sphereRow]

/-- LMW Theorem 3.2 for spheres and hyperplanes. -/
theorem curvature_center_general_internal {n : ℕ} (hn : 0 < n) (s : Fin (n + 2) → OrientedSphere n)
    (hv : ∀ i, OrientedSphere.IsValid (s i))
    (ht : ∀ i j, i ≠ j → OrientedSphere.Tangent (s i) (s j)) :
    (curvatureCenterMatrixOf s)ᵀ * descartesQ n * curvatureCenterMatrixOf s =
      curvatureCenterTarget n := by
  rw [main_curvatureCenterMatrixOf_eq]
  exact main_curvature_center_of_identity _ (augmented_descartes_general_internal hn s hv ht)

/-- The Euclidean generalized Descartes theorem (LMW Theorem 3.2, (3.5)) for spheres:
`Mᵀ Qₙ M = diag(0, 2 Iₙ)`. -/
theorem curvature_center_internal {n : ℕ} (hn : 0 < n) (x : Fin (n + 2) → EuclideanSpace ℝ (Fin n))
    (r : Fin (n + 2) → ℝ) (h : PairwiseTangent x r) :
    (curvatureCenterMatrix x r)ᵀ * descartesQ n * curvatureCenterMatrix x r =
      curvatureCenterTarget n := by
  rw [main_curvatureCenterMatrix_eq]
  exact curvature_center_general_internal hn _ (fun i => h.1 i) (fun i j hij => h.2 i j hij)

/-! ## Extras for `Corollaries`: the centre block in coordinates and the complex Descartes theorem -/

/-- The `(inr k, inr l)` entry for spheres: `Σ (bᵢ xᵢₖ)(bᵢ xᵢₗ) − (1/n)(Σ bᵢ xᵢₖ)(Σ bᵢ xᵢₗ) = 2 δₖₗ`. -/
theorem main_center_entry {n : ℕ} (hn : 0 < n) (x : Fin (n + 2) → EuclideanSpace ℝ (Fin n))
    (r : Fin (n + 2) → ℝ) (h : PairwiseTangent x r) (k l : Fin n) :
    ∑ i, x i k / r i * (x i l / r i) - (n : ℝ)⁻¹ * ((∑ i, x i k / r i) * ∑ i, x i l / r i) =
      if k = l then 2 else 0 := by
  have e := congrFun (congrFun (augmented_descartes_internal hn x r h) (Sum.inr k)) (Sum.inr l)
  rw [main_entry] at e
  simpa [augmentedMatrix, sphereRow, augmentedTarget, Matrix.diagonal_apply] using e

/-- The `(inl 1, inr k)` entry for spheres: `Σ bᵢ (bᵢ xᵢₖ) − (1/n)(Σ bᵢ)(Σ bᵢ xᵢₖ) = 0`. -/
theorem main_mixed_entry {n : ℕ} (hn : 0 < n) (x : Fin (n + 2) → EuclideanSpace ℝ (Fin n))
    (r : Fin (n + 2) → ℝ) (h : PairwiseTangent x r) (k : Fin n) :
    ∑ i, 1 / r i * (x i k / r i) - (n : ℝ)⁻¹ * ((∑ i, 1 / r i) * ∑ i, x i k / r i) = 0 := by
  have e := congrFun (congrFun (augmented_descartes_internal hn x r h) (Sum.inl 1)) (Sum.inr k)
  rw [main_entry] at e
  simpa [augmentedMatrix, sphereRow, augmentedTarget] using e

theorem main_sq_ofReal_add_mul_I (a b : ℝ) :
    ((a : ℂ) + (b : ℂ) * Complex.I) ^ 2 = ((a ^ 2 - b ^ 2 : ℝ) : ℂ) + ((2 * a * b : ℝ) : ℂ) * Complex.I := by
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

theorem main_sum_ofReal_add_mul_I {ι : Type*} (s : Finset ι) (u v : ι → ℝ) :
    ∑ i ∈ s, ((u i : ℂ) + (v i : ℂ) * Complex.I) =
      ((∑ i ∈ s, u i : ℝ) : ℂ) + ((∑ i ∈ s, v i : ℝ) : ℂ) * Complex.I := by
  push_cast
  rw [Finset.sum_add_distrib, Finset.sum_mul]

theorem main_complex_aux (u v : Fin (2 + 2) → ℝ)
    (huu : ∑ i, u i * u i - (2 : ℝ)⁻¹ * ((∑ i, u i) * ∑ i, u i) = 2)
    (hvv : ∑ i, v i * v i - (2 : ℝ)⁻¹ * ((∑ i, v i) * ∑ i, v i) = 2)
    (huv : ∑ i, u i * v i - (2 : ℝ)⁻¹ * ((∑ i, u i) * ∑ i, v i) = 0) :
    (∑ i, ((u i : ℂ) + (v i : ℂ) * Complex.I)) ^ 2 =
      2 * ∑ i, ((u i : ℂ) + (v i : ℂ) * Complex.I) ^ 2 := by
  simp_rw [main_sq_ofReal_add_mul_I]
  rw [main_sum_ofReal_add_mul_I, main_sum_ofReal_add_mul_I, main_sq_ofReal_add_mul_I]
  have hre : (∑ i, u i) ^ 2 - (∑ i, v i) ^ 2 = 2 * ∑ i, (u i ^ 2 - v i ^ 2) := by
    rw [Finset.sum_sub_distrib]
    simp only [sq]
    linear_combination (-2 : ℝ) * huu + 2 * hvv
  have him : 2 * (∑ i, u i) * (∑ i, v i) = 2 * ∑ i, 2 * u i * v i := by
    have : ∑ i, 2 * u i * v i = 2 * ∑ i, u i * v i := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [this]
    linear_combination (-4 : ℝ) * huv
  rw [hre, him]
  push_cast
  ring

theorem main_complex_mixed_aux (b u v : Fin (2 + 2) → ℝ)
    (hu : ∑ i, b i * u i - (2 : ℝ)⁻¹ * ((∑ i, b i) * ∑ i, u i) = 0)
    (hv : ∑ i, b i * v i - (2 : ℝ)⁻¹ * ((∑ i, b i) * ∑ i, v i) = 0) :
    ∑ i, (b i : ℂ) * ((u i : ℂ) + (v i : ℂ) * Complex.I) =
      (1 / 2) * (∑ i, (b i : ℂ)) * ∑ i, ((u i : ℂ) + (v i : ℂ) * Complex.I) := by
  rw [main_sum_ofReal_add_mul_I]
  have e : ∀ i, (b i : ℂ) * ((u i : ℂ) + (v i : ℂ) * Complex.I) =
      ((b i * u i : ℝ) : ℂ) + ((b i * v i : ℝ) : ℂ) * Complex.I := by
    intro i; push_cast; ring
  simp_rw [e]
  rw [main_sum_ofReal_add_mul_I]
  have h1 : ∑ i, b i * u i = (1 / 2) * (∑ i, b i) * ∑ i, u i := by linear_combination hu
  have h2 : ∑ i, b i * v i = (1 / 2) * (∑ i, b i) * ∑ i, v i := by linear_combination hv
  rw [h1, h2]
  push_cast
  ring

theorem main_complex_term (x : Fin (2 + 2) → EuclideanSpace ℝ (Fin 2)) (r : Fin (2 + 2) → ℝ)
    (i : Fin (2 + 2)) :
    ((x i 0 : ℂ) + (x i 1 : ℂ) * Complex.I) / r i =
      ((x i 0 / r i : ℝ) : ℂ) + ((x i 1 / r i : ℝ) : ℂ) * Complex.I := by
  push_cast
  ring

/-- The complex Descartes theorem (LMW Theorem 2.1, (2.2)), for `Corollaries`. -/
theorem main_complex_descartes (x : Fin (2 + 2) → EuclideanSpace ℝ (Fin 2)) (r : Fin (2 + 2) → ℝ)
    (h : PairwiseTangent x r) :
    (∑ i, ((x i 0 : ℂ) + (x i 1 : ℂ) * Complex.I) / r i) ^ 2 =
      2 * ∑ i, (((x i 0 : ℂ) + (x i 1 : ℂ) * Complex.I) / r i) ^ 2 := by
  have e00 := main_center_entry (by norm_num) x r h 0 0
  have e11 := main_center_entry (by norm_num) x r h 1 1
  have e01 := main_center_entry (by norm_num) x r h 0 1
  rw [if_pos rfl] at e00 e11
  rw [if_neg (by decide)] at e01
  simp only [Nat.cast_ofNat] at e00 e11 e01
  simp_rw [main_complex_term x r]
  exact main_complex_aux (fun i => x i 0 / r i) (fun i => x i 1 / r i) e00 e11 e01

/-- LMW (2.3): `Σ bᵢ (bᵢ zᵢ) = ½ (Σ bᵢ)(Σ bᵢ zᵢ)`, for `Corollaries`. -/
theorem main_complex_descartes_mixed (x : Fin (2 + 2) → EuclideanSpace ℝ (Fin 2)) (r : Fin (2 + 2) → ℝ)
    (h : PairwiseTangent x r) :
    ∑ i, (1 / r i : ℂ) * (((x i 0 : ℂ) + (x i 1 : ℂ) * Complex.I) / r i) =
      (1 / 2) * (∑ i, (1 / r i : ℂ)) * ∑ i, ((x i 0 : ℂ) + (x i 1 : ℂ) * Complex.I) / r i := by
  have e0 := main_mixed_entry (by norm_num) x r h 0
  have e1 := main_mixed_entry (by norm_num) x r h 1
  simp only [Nat.cast_ofNat] at e0 e1
  simp_rw [main_complex_term x r]
  have hb : ∀ i, (1 / r i : ℂ) = ((1 / r i : ℝ) : ℂ) := by intro i; push_cast; ring
  simp_rw [hb]
  exact main_complex_mixed_aux (fun i => 1 / r i) (fun i => x i 0 / r i) (fun i => x i 1 / r i) e0 e1

end AugmentedDescartes
