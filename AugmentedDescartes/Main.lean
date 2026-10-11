module

public import AugmentedDescartes.Lorentz

/-!
# Main

The forward theorems: the identity, Soddy–Gosset, the curvature–centre identity (PROOF.md §3).
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

/-- The augmented Euclidean Descartes theorem (LMW Theorem 3.3; (8.4) at `n = 1`) for spheres of nonzero
curvature: `Wᵀ Qₙ W = [[0, −4, 0], [−4, 0, 0], [0, 0, 2 Iₙ]]`. -/
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

/-- The Soddy–Gosset theorem (LMW Theorem 1.2, (1.2); Soddy 1936, Gosset 1937, Lachlan 1886 at `n = 3`):
`(Σ 1/rᵢ)² = n Σ (1/rᵢ)²`. -/
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

end AugmentedDescartes
