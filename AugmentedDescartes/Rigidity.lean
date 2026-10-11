module

public import AugmentedDescartes.Completion

/-!
# The congruence half of the converse of Soddy–Gosset

Two solutions of the augmented identity with the same curvature column differ by right multiplication by exactly
one motion matrix `rigidMotionMatrix O t`, `Oᵀ O = 1` (a matrix that preserves the target form and fixes the
curvature column is a motion matrix); through the rows of valid objects this is LMW Theorem 3.1's congruence half,
with the motion unique for families labelled alike, hyperplanes and reflections included.
-/

@[expose] public section

namespace AugmentedDescartes

open Matrix

/-- The two parameters can be recovered directly from the lower-right block and
the spatial part of the second row. -/
theorem rig_rigidMotionMatrix_injective {n : ℕ} (O P : Matrix (Fin n) (Fin n) ℝ)
    (t u : Fin n → ℝ) (h : rigidMotionMatrix O t = rigidMotionMatrix P u) :
    O = P ∧ t = u := by
  constructor
  · ext i j
    exact congrFun (congrFun h (Sum.inr i)) (Sum.inr j)
  · funext j
    exact congrFun (congrFun h (Sum.inl 1)) (Sum.inr j)

/-- An entry of the target-form Gram matrix, in coordinates. -/
theorem rig_target_entry {n : ℕ}
    (A : Matrix (Fin 2 ⊕ Fin n) (Fin 2 ⊕ Fin n) ℝ) (p q : Fin 2 ⊕ Fin n) :
    (Aᵀ * augmentedTarget n * A) p q =
      -4 * (A (Sum.inl 0) p * A (Sum.inl 1) q +
        A (Sum.inl 1) p * A (Sum.inl 0) q) +
      2 * ∑ k, A (Sum.inr k) p * A (Sum.inr k) q := by
  simp [Matrix.mul_apply, augmentedTarget, Matrix.fromBlocks, Fintype.sum_sum_type, Fin.sum_univ_two,
    Matrix.diagonal_apply, Finset.mul_sum]
  have hs : (∑ k, A (Sum.inr k) p * 2 * A (Sum.inr k) q) =
      ∑ k, 2 * (A (Sum.inr k) p * A (Sum.inr k) q) :=
    Finset.sum_congr rfl fun k _ => by ring
  rw [hs]
  ring

/-- A matrix that preserves the target form and fixes the curvature column is a motion matrix
`rigidMotionMatrix O t` with `Oᵀ O = 1`. -/
theorem rig_stabilizer_normal_form {n : ℕ}
    (A : Matrix (Fin 2 ⊕ Fin n) (Fin 2 ⊕ Fin n) ℝ)
    (hA : Aᵀ * augmentedTarget n * A = augmentedTarget n)
    (hb : ∀ p, A p (Sum.inl 1) = (Pi.single (Sum.inl 1) (1 : ℝ) : Fin 2 ⊕ Fin n → ℝ) p) :
    ∃ O : Matrix (Fin n) (Fin n) ℝ, ∃ t : Fin n → ℝ,
      Oᵀ * O = 1 ∧ A = rigidMotionMatrix O t := by
  have E : ∀ p q,
      -4 * (A (Sum.inl 0) p * A (Sum.inl 1) q +
        A (Sum.inl 1) p * A (Sum.inl 0) q) +
      2 * ∑ k, A (Sum.inr k) p * A (Sum.inr k) q = augmentedTarget n p q := by
    intro p q
    rw [← rig_target_entry, hA]
  have h01 : A (Sum.inl 0) (Sum.inl 1) = 0 := by simpa using hb (Sum.inl 0)
  have h11 : A (Sum.inl 1) (Sum.inl 1) = 1 := by simpa using hb (Sum.inl 1)
  have hv1 : ∀ k, A (Sum.inr k) (Sum.inl 1) = 0 := fun k => by simpa using hb (Sum.inr k)
  have h00 : A (Sum.inl 0) (Sum.inl 0) = 1 := by
    have h := E (Sum.inl 0) (Sum.inl 1)
    simp only [h01, h11, hv1, mul_zero, mul_one, add_zero, Finset.sum_const_zero] at h
    norm_num [augmentedTarget] at h
    linarith
  have h0v : ∀ k, A (Sum.inl 0) (Sum.inr k) = 0 := by
    intro k
    have h := E (Sum.inr k) (Sum.inl 1)
    simp only [h01, h11, hv1, mul_zero, mul_one, add_zero, Finset.sum_const_zero] at h
    norm_num [augmentedTarget] at h
    linarith
  let O : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => A (Sum.inr i) (Sum.inr j)
  let t : Fin n → ℝ := fun k => A (Sum.inl 1) (Sum.inr k)
  let u : Fin n → ℝ := fun k => A (Sum.inr k) (Sum.inl 0)
  have hO : Oᵀ * O = 1 := by
    ext k l
    have h := E (Sum.inr k) (Sum.inr l)
    simp only [h0v, zero_mul, mul_zero, zero_add] at h
    simp only [augmentedTarget, Matrix.fromBlocks_apply₂₂, Matrix.diagonal_apply] at h
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, O, Matrix.of_apply]
    split_ifs at h ⊢ <;> linarith
  have hOu : Oᵀ *ᵥ u = (2 : ℝ) • t := by
    funext k
    have h := E (Sum.inl 0) (Sum.inr k)
    simp only [h00, h0v, one_mul, mul_zero, add_zero] at h
    simp only [augmentedTarget, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply] at h
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Pi.smul_apply, smul_eq_mul, O, t, u,
      Matrix.of_apply]
    have hc : ∑ i, A (Sum.inr i) (Sum.inr k) * A (Sum.inr i) (Sum.inl 0) =
        ∑ i, A (Sum.inr i) (Sum.inl 0) * A (Sum.inr i) (Sum.inr k) :=
      Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [hc]
    linarith
  have hO' : O * Oᵀ = 1 := mul_eq_one_comm.mp hO
  have hu : u = (2 : ℝ) • (O *ᵥ t) := by
    calc
      u = (1 : Matrix (Fin n) (Fin n) ℝ) *ᵥ u := (Matrix.one_mulVec u).symm
      _ = O *ᵥ (Oᵀ *ᵥ u) := by rw [Matrix.mulVec_mulVec, hO']
      _ = (2 : ℝ) • (O *ᵥ t) := by rw [hOu, Matrix.mulVec_smul]
  have hnorm : (O *ᵥ t) ⬝ᵥ (O *ᵥ t) = t ⬝ᵥ t := by
    calc
      (O *ᵥ t) ⬝ᵥ (O *ᵥ t) = t ⬝ᵥ (Oᵀ *ᵥ (O *ᵥ t)) := by
        simpa only [vecMul_transpose] using (dotProduct_mulVec t Oᵀ (O *ᵥ t)).symm
      _ = t ⬝ᵥ t := by rw [Matrix.mulVec_mulVec, hO, Matrix.one_mulVec]
  have huu : u ⬝ᵥ u = 4 * (t ⬝ᵥ t) := by
    simp only [hu, smul_dotProduct, dotProduct_smul, hnorm, smul_eq_mul]
    ring
  have h10 : A (Sum.inl 1) (Sum.inl 0) = t ⬝ᵥ t := by
    have h := E (Sum.inl 0) (Sum.inl 0)
    simp only [h00, one_mul, mul_one] at h
    simp only [augmentedTarget, Matrix.fromBlocks_apply₁₁] at h
    change -4 * (A (Sum.inl 1) (Sum.inl 0) + A (Sum.inl 1) (Sum.inl 0)) +
      2 * (u ⬝ᵥ u) = 0 at h
    rw [huu] at h
    linarith
  refine ⟨O, t, hO, ?_⟩
  ext p q
  rcases p with p | k <;> rcases q with q | l
  · fin_cases p <;> fin_cases q <;> simp [rigidMotionMatrix, h00, h01, h10, h11]
  · fin_cases p <;> simp [rigidMotionMatrix, h0v, t]
  · fin_cases q
    · exact congrFun hu k
    · simpa [rigidMotionMatrix] using hv1 k
  · rfl

/-- The congruence half of the converse of the Soddy–Gosset theorem in matrix form (LMW Theorem 3.1; GLMWY III
arXiv v1–v2, Theorem 2.2 (ii)): two solutions of the identity with the same curvature column satisfy
`W₁ * rigidMotionMatrix O t = W₂` for exactly one pair `(O, t)` with `Oᵀ O = 1`, hyperplanes included
(`same_curvature_congruence` is the geometric form). -/
theorem same_curvature_motion_internal {n : ℕ}
    (W₁ W₂ : Matrix (Fin (n + 2)) (Fin 2 ⊕ Fin n) ℝ)
    (hW₁ : W₁ᵀ * descartesQ n * W₁ = augmentedTarget n)
    (hW₂ : W₂ᵀ * descartesQ n * W₂ = augmentedTarget n)
    (hb : ∀ i, W₁ i (Sum.inl 1) = W₂ i (Sum.inl 1)) :
    ∃! p : Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ),
      p.1ᵀ * p.1 = 1 ∧ W₁ * rigidMotionMatrix p.1 p.2 = W₂ := by
  let V := ((1 / 2 : ℝ) • lorentzG n) * W₁ᵀ * descartesQ n
  have hV : V * W₁ = 1 ∧ W₁ * V = 1 := cmp_inv_of_identity W₁ hW₁
  let A := V * W₂
  have hWA : W₁ * A = W₂ := by
    dsimp only [A]
    rw [← Matrix.mul_assoc, hV.2, Matrix.one_mul]
  have hA : Aᵀ * augmentedTarget n * A = augmentedTarget n := by
    calc
      Aᵀ * augmentedTarget n * A = Aᵀ * (W₁ᵀ * descartesQ n * W₁) * A := by rw [hW₁]
      _ = (W₁ * A)ᵀ * descartesQ n * (W₁ * A) := by
        rw [show (W₁ * A)ᵀ = Aᵀ * W₁ᵀ from Matrix.transpose_mul W₁ A]
        simp only [Matrix.mul_assoc]
      _ = augmentedTarget n := by rw [hWA, hW₂]
  have hbA : ∀ p, A p (Sum.inl 1) = (Pi.single (Sum.inl 1) (1 : ℝ) : Fin 2 ⊕ Fin n → ℝ) p := by
    intro p
    have h : A p (Sum.inl 1) = (V * W₁) p (Sum.inl 1) := by
      simp only [A, Matrix.mul_apply]
      exact Finset.sum_congr rfl fun i _ => by rw [← hb i]
    rw [h, hV.1]
    simp [Matrix.one_apply, Pi.single_apply]
  obtain ⟨O, t, hO, hAt⟩ := rig_stabilizer_normal_form A hA hbA
  have hOt : W₁ * rigidMotionMatrix O t = W₂ := by rw [← hAt, hWA]
  refine ⟨(O, t), ⟨hO, hOt⟩, ?_⟩
  rintro ⟨P, u⟩ ⟨-, hPu⟩
  have heq : rigidMotionMatrix P u = rigidMotionMatrix O t := by
    calc
      rigidMotionMatrix P u = (V * W₁) * rigidMotionMatrix P u := by rw [hV.1, Matrix.one_mul]
      _ = V * W₂ := by rw [Matrix.mul_assoc, hPu]
      _ = V * (W₁ * rigidMotionMatrix O t) := by rw [hOt]
      _ = (V * W₁) * rigidMotionMatrix O t := (Matrix.mul_assoc V W₁ _).symm
      _ = rigidMotionMatrix O t := by rw [hV.1, Matrix.one_mul]
  obtain ⟨rfl, rfl⟩ := rig_rigidMotionMatrix_injective P O u t heq
  rfl

/-- A spatial row of multiplication by the explicit inverse target matrix. -/
theorem rig_halfG_mul_spatial {n : ℕ}
    (B : Matrix (Fin 2 ⊕ Fin n) (Fin 2 ⊕ Fin n) ℝ) (k : Fin n) (q : Fin 2 ⊕ Fin n) :
    (((1 / 2 : ℝ) • lorentzG n) * B) (Sum.inr k) q = (1 / 2 : ℝ) * B (Sum.inr k) q := by
  simp [Matrix.mul_apply, lorentzG, Fintype.sum_sum_type, Matrix.one_apply]

/-- The curvature row of multiplication by the explicit inverse target matrix. -/
theorem rig_halfG_mul_curvature {n : ℕ}
    (B : Matrix (Fin 2 ⊕ Fin n) (Fin 2 ⊕ Fin n) ℝ) (q : Fin 2 ⊕ Fin n) :
    (((1 / 2 : ℝ) • lorentzG n) * B) (Sum.inl 1) q = (-1 / 4 : ℝ) * B (Sum.inl 0) q := by
  norm_num [Matrix.mul_apply, lorentzG, Fintype.sum_sum_type, Fin.sum_univ_two]

/-- The motion's parameters from the two matrices: with `W₁ = [a | b | X]`, `W₂ = [a' | b | X']` and
`W₁ * rigidMotionMatrix O t = W₂`, `O = ½ Xᵀ Qₙ X'` and `t = −¼ aᵀ Qₙ X'` (row-vector convention; read from
`W₁⁻¹ = ½ G W₁ᵀ Qₙ`, so no hypothesis on `O` or on `W₂` is needed). -/
theorem rigidMotion_parameters_internal {n : ℕ}
    (W₁ W₂ : Matrix (Fin (n + 2)) (Fin 2 ⊕ Fin n) ℝ)
    (hW₁ : W₁ᵀ * descartesQ n * W₁ = augmentedTarget n)
    (O : Matrix (Fin n) (Fin n) ℝ) (t : Fin n → ℝ)
    (h : W₁ * rigidMotionMatrix O t = W₂) :
    (∀ k l, O k l = (1 / 2 : ℝ) *
      ((fun i => W₁ i (Sum.inr k)) ⬝ᵥ (descartesQ n *ᵥ (fun i => W₂ i (Sum.inr l))))) ∧
    ∀ l, t l = (-1 / 4 : ℝ) *
      ((fun i => W₁ i (Sum.inl 0)) ⬝ᵥ (descartesQ n *ᵥ (fun i => W₂ i (Sum.inr l)))) := by
  have hV := (cmp_inv_of_identity W₁ hW₁).1
  have hA : ((1 / 2 : ℝ) • lorentzG n) * (W₁ᵀ * descartesQ n * W₂) = rigidMotionMatrix O t := by
    calc
      ((1 / 2 : ℝ) • lorentzG n) * (W₁ᵀ * descartesQ n * W₂) =
          (((1 / 2 : ℝ) • lorentzG n) * W₁ᵀ * descartesQ n) * W₂ := by
            simp only [Matrix.mul_assoc]
      _ = (((1 / 2 : ℝ) • lorentzG n) * W₁ᵀ * descartesQ n) * (W₁ * rigidMotionMatrix O t) := by
        rw [h]
      _ = rigidMotionMatrix O t := by rw [← Matrix.mul_assoc, hV, Matrix.one_mul]
  constructor
  · intro k l
    have e := congrFun (congrFun hA (Sum.inr k)) (Sum.inr l)
    rw [rig_halfG_mul_spatial, cmp_entry, cmp_B_apply] at e
    exact e.symm
  · intro l
    have e := congrFun (congrFun hA (Sum.inl 1)) (Sum.inr l)
    rw [rig_halfG_mul_curvature, cmp_entry, cmp_B_apply] at e
    exact e.symm

/-- Orthogonal right multiplication preserves the Euclidean dot product. -/
theorem rig_vecMul_dotProduct {n : ℕ} (O : Matrix (Fin n) (Fin n) ℝ)
    (hO : Oᵀ * O = 1) (x y : Fin n → ℝ) :
    (x ᵥ* O) ⬝ᵥ (y ᵥ* O) = x ⬝ᵥ y := by
  have hO' : O * Oᵀ = 1 := mul_eq_one_comm.mp hO
  rw [← dotProduct_mulVec, Matrix.mulVec_vecMul, hO', Matrix.one_mulVec]

/-- For `Oᵀ O = 1` the point map `x ↦ x O + t` is an isometry. -/
theorem rigidMotionPoint_isometry_internal {n : ℕ} (O : Matrix (Fin n) (Fin n) ℝ)
    (hO : Oᵀ * O = 1) (t : Fin n → ℝ) : Isometry (rigidMotionPoint O t) := by
  refine isometry_iff_dist_eq.mpr fun x y => ?_
  have hd : (fun k => (rigidMotionPoint O t x - rigidMotionPoint O t y) k) =
      (fun k => (x - y) k) ᵥ* O := by
    change ((fun k => x k) ᵥ* O + t) - ((fun k => y k) ᵥ* O + t) =
      ((fun k => x k) - (fun k => y k)) ᵥ* O
    rw [Matrix.sub_vecMul]
    abel
  have hn : ∀ z : EuclideanSpace ℝ (Fin n),
      ‖z‖ ^ 2 = (fun k => z k) ⬝ᵥ (fun k => z k) := by
    intro z
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [dotProduct, pow_two]
  have hs : dist (rigidMotionPoint O t x) (rigidMotionPoint O t y) ^ 2 = dist x y ^ 2 := by
    rw [dist_eq_norm, dist_eq_norm, hn, hn, hd, rig_vecMul_dotProduct O hO]
  exact (sq_eq_sq₀ dist_nonneg dist_nonneg).mp hs

/-- The norm expansion for the associated point map. -/
theorem rig_rigidMotionPoint_norm_sq {n : ℕ} (O : Matrix (Fin n) (Fin n) ℝ)
    (hO : Oᵀ * O = 1) (t : Fin n → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    ‖rigidMotionPoint O t x‖ ^ 2 = ‖x‖ ^ 2 +
      2 * ((fun k => x k) ⬝ᵥ (O *ᵥ t)) + t ⬝ᵥ t := by
  have hx : (fun k => x k) ⬝ᵥ (fun k => x k) = ‖x‖ ^ 2 := by
    rw [dotProduct, rows_sum_mul_eq_inner, real_inner_self_eq_norm_sq]
  calc
    ‖rigidMotionPoint O t x‖ ^ 2 =
        ((fun k => x k) ᵥ* O + t) ⬝ᵥ ((fun k => x k) ᵥ* O + t) := by
      rw [EuclideanSpace.real_norm_sq_eq]
      simp only [rigidMotionPoint, PiLp.toLp_apply, Pi.add_apply, dotProduct, pow_two]
    _ = ‖x‖ ^ 2 + 2 * ((fun k => x k) ⬝ᵥ (O *ᵥ t)) + t ⬝ᵥ t := by
      rw [add_dotProduct, dotProduct_add, dotProduct_add, rig_vecMul_dotProduct O hO,
        dotProduct_comm t, hx]
      simp only [← dotProduct_mulVec]
      ring

/-- The spatial coordinate of a row after a rigid motion. -/
theorem rig_row_mul_spatial {n : ℕ} (O : Matrix (Fin n) (Fin n) ℝ)
    (t : Fin n → ℝ) (w : Fin 2 ⊕ Fin n → ℝ) (j : Fin n) :
    (w ᵥ* rigidMotionMatrix O t) (Sum.inr j) =
      ((fun k => w (Sum.inr k)) ᵥ* O) j + w (Sum.inl 1) * t j := by
  simp [Matrix.vecMul, dotProduct, rigidMotionMatrix, Matrix.fromBlocks, Fintype.sum_sum_type,
    Fin.sum_univ_two]
  ring

/-- A rigid motion fixes the curvature coordinate of every row. -/
theorem rig_row_mul_curvature {n : ℕ} (O : Matrix (Fin n) (Fin n) ℝ)
    (t : Fin n → ℝ) (w : Fin 2 ⊕ Fin n → ℝ) :
    (w ᵥ* rigidMotionMatrix O t) (Sum.inl 1) = w (Sum.inl 1) := by
  simp [Matrix.vecMul, dotProduct, rigidMotionMatrix, Matrix.fromBlocks, Fintype.sum_sum_type,
    Fin.sum_univ_two]

/-- The augmented coordinate of a row after a rigid motion. -/
theorem rig_row_mul_augmented {n : ℕ} (O : Matrix (Fin n) (Fin n) ℝ)
    (t : Fin n → ℝ) (w : Fin 2 ⊕ Fin n → ℝ) :
    (w ᵥ* rigidMotionMatrix O t) (Sum.inl 0) = w (Sum.inl 0) +
      w (Sum.inl 1) * (t ⬝ᵥ t) + 2 * ((fun k => w (Sum.inr k)) ⬝ᵥ (O *ᵥ t)) := by
  simp only [Matrix.vecMul, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two,
    rigidMotionMatrix, Matrix.fromBlocks, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr,
    Matrix.cons_val_zero, Matrix.cons_val_one, mul_one]
  simp only [Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by ring

/-- On a sphere row the matrix acts as the motion: centre `x ↦ x O + t`, signed radius fixed (`Oᵀ O = 1` is
needed; at `r = 0` both sides are the zero row). -/
theorem rigidMotionMatrix_sphereRow_internal {n : ℕ} (O : Matrix (Fin n) (Fin n) ℝ)
    (hO : Oᵀ * O = 1) (t : Fin n → ℝ) (x : EuclideanSpace ℝ (Fin n)) (r : ℝ) :
    sphereRow x r ᵥ* rigidMotionMatrix O t = sphereRow (rigidMotionPoint O t x) r := by
  by_cases hr : r = 0
  · subst hr
    have h0 : ∀ y : EuclideanSpace ℝ (Fin n), sphereRow y (0 : ℝ) = 0 := by
      intro y
      funext p
      rcases p with p | k
      · fin_cases p <;> simp [sphereRow]
      · simp [sphereRow]
    rw [h0, h0, Matrix.zero_vecMul]
  funext p
  rcases p with p | j
  · fin_cases p <;> simp only [Fin.zero_eta, Fin.mk_one]
    · rw [rig_row_mul_augmented]
      simp only [sphereRow, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [rig_rigidMotionPoint_norm_sq O hO]
      have hd : (fun k => x k / r) ⬝ᵥ (O *ᵥ t) =
          ((fun k => x k) ⬝ᵥ (O *ᵥ t)) / r := by
        simp only [dotProduct, Finset.sum_div]
        exact Finset.sum_congr rfl fun k _ => by ring
      rw [hd]
      field_simp
      ring
    · rw [rig_row_mul_curvature]
      rfl
  · rw [rig_row_mul_spatial]
    simp only [sphereRow, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_one, Matrix.cons_val_zero,
      rigidMotionPoint, PiLp.toLp_apply, Pi.add_apply]
    have hd : ((fun k => x k / r) ᵥ* O) j = ((fun k => x k) ᵥ* O) j / r := by
      simp only [Matrix.vecMul, dotProduct, Finset.sum_div]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [hd]
    ring

/-- On a hyperplane row the matrix multiplies the normal by `O` and moves the offset: `h ↦ h O`,
`δ ↦ δ + (h O) ⬝ᵥ t`; no hypothesis on `O`, since a hyperplane row has curvature `0`. -/
theorem rigidMotionMatrix_planeRow_internal {n : ℕ} (O : Matrix (Fin n) (Fin n) ℝ)
    (t : Fin n → ℝ) (h : EuclideanSpace ℝ (Fin n)) (δ : ℝ) :
    planeRow h δ ᵥ* rigidMotionMatrix O t =
      planeRow (rigidMotionPoint O 0 h) (δ + ((fun k => h k) ᵥ* O) ⬝ᵥ t) := by
  funext p
  rcases p with p | j
  · fin_cases p <;> simp only [Fin.zero_eta, Fin.mk_one]
    · rw [rig_row_mul_augmented]
      simp only [planeRow, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero,
        Matrix.cons_val_one, zero_mul, add_zero]
      rw [← dotProduct_mulVec]
      ring
    · rw [rig_row_mul_curvature]
      rfl
  · rw [rig_row_mul_spatial]
    simp [planeRow, rigidMotionPoint]

/-- A Euclidean motion preserves validity. -/
theorem rigidMotionOf_isValid_internal {n : ℕ} (O : Matrix (Fin n) (Fin n) ℝ)
    (hO : Oᵀ * O = 1) (t : Fin n → ℝ) (s : OrientedSphere n)
    (hs : OrientedSphere.IsValid s) : OrientedSphere.IsValid (rigidMotionOf O t s) := by
  rcases s with ⟨x, r⟩ | ⟨h, δ⟩
  · exact hs
  · have hzero : rigidMotionPoint O 0 (0 : EuclideanSpace ℝ (Fin n)) = 0 := by
      apply WithLp.ofLp_injective 2
      change (0 : Fin n → ℝ) ᵥ* O + 0 = 0
      simp
    have hd := (rigidMotionPoint_isometry_internal O hO 0).dist_eq h 0
    rw [hzero, dist_zero_right, dist_zero_right] at hd
    simpa only [rigidMotionOf, Sum.elim_inr, OrientedSphere.IsValid, hd] using hs

/-- The geometric action agrees with the augmented matrix action. -/
theorem rig_rigidMotionOf_row {n : ℕ} (O : Matrix (Fin n) (Fin n) ℝ)
    (hO : Oᵀ * O = 1) (t : Fin n → ℝ) (s : OrientedSphere n) :
    OrientedSphere.row (rigidMotionOf O t s) =
      OrientedSphere.row s ᵥ* rigidMotionMatrix O t := by
  rcases s with ⟨x, r⟩ | ⟨h, δ⟩
  · exact (rigidMotionMatrix_sphereRow_internal O hO t x r).symm
  · exact (rigidMotionMatrix_planeRow_internal O t h δ).symm

/-- The congruence half of the converse of the Soddy–Gosset theorem (LMW Theorem 3.1; GLMWY III arXiv v1–v2,
Theorem 2.2 (ii)), with uniqueness: two valid, pairwise tangent families with the same curvatures, index by index,
are carried one to the other by exactly one Euclidean motion `x ↦ x O + t`, `Oᵀ O = 1` (reflections and
hyperplanes included; tangency in the signed-distance sense). -/
theorem same_curvature_congruence_internal {n : ℕ} (hn : 0 < n)
    (s s' : Fin (n + 2) → OrientedSphere n)
    (hs : ∀ i, OrientedSphere.IsValid (s i))
    (hs' : ∀ i, OrientedSphere.IsValid (s' i))
    (ht : ∀ i j, i ≠ j → OrientedSphere.Tangent (s i) (s j))
    (ht' : ∀ i j, i ≠ j → OrientedSphere.Tangent (s' i) (s' j))
    (hb : ∀ i, OrientedSphere.curvature (s i) = OrientedSphere.curvature (s' i)) :
    ∃! p : Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ),
      p.1ᵀ * p.1 = 1 ∧ ∀ i, rigidMotionOf p.1 p.2 (s i) = s' i := by
  have hW := augmented_descartes_general_internal hn s hs ht
  have hW' := augmented_descartes_general_internal hn s' hs' ht'
  have hbW : ∀ i, augmentedMatrixOf s i (Sum.inl 1) = augmentedMatrixOf s' i (Sum.inl 1) := by
    intro i
    simpa only [augmentedMatrixOf, Matrix.of_apply, rows_row_inl_one] using hb i
  obtain ⟨⟨O, t⟩, ⟨hO, hOt⟩, hu⟩ :=
    same_curvature_motion_internal (augmentedMatrixOf s) (augmentedMatrixOf s') hW hW' hbW
  refine ⟨(O, t), ⟨hO, fun i => ?_⟩, ?_⟩
  · apply row_injOn_valid_internal _ _ (rigidMotionOf_isValid_internal O hO t (s i) (hs i)) (hs' i)
    rw [rig_rigidMotionOf_row O hO t (s i)]
    exact congrFun hOt i
  · rintro ⟨P, u⟩ ⟨hP, hPu⟩
    apply hu (P, u) ⟨hP, ?_⟩
    ext i j
    have h := congrArg OrientedSphere.row (hPu i)
    rw [rig_rigidMotionOf_row P hP u (s i)] at h
    exact congrFun h j

end AugmentedDescartes
