module

public import AugmentedDescartes.Rows

/-!
# Base

The strip configuration (ARCH.md §6). Lane `base`.
-/

@[expose] public section

namespace AugmentedDescartes

open Matrix

/-- The unit sphere centred at `√2 eᵢ`. -/
noncomputable def base_sphere (n : ℕ) (i : Fin n) : OrientedSphere n :=
  Sum.inl (Real.sqrt 2 • EuclideanSpace.single i 1, 1)

/-- The hyperplane `⟪h, y⟫ = 1 + √2/√n` with `h = 𝟙/√n`. -/
noncomputable def base_planeP (n : ℕ) : OrientedSphere n :=
  Sum.inr (WithLp.toLp 2 (fun _ => 1 / Real.sqrt n), 1 + Real.sqrt 2 / Real.sqrt n)

/-- The hyperplane `⟪h, y⟫ = 1 − √2/√n` with `h = −𝟙/√n`. -/
noncomputable def base_planeM (n : ℕ) : OrientedSphere n :=
  Sum.inr (WithLp.toLp 2 (fun _ => -(1 / Real.sqrt n)), 1 - Real.sqrt 2 / Real.sqrt n)

/-- The strip configuration: `n` unit spheres, then the two hyperplanes. -/
noncomputable def base_config (n : ℕ) (i : Fin (n + 2)) : OrientedSphere n :=
  if h : (i : ℕ) < n then base_sphere n ⟨i, h⟩
  else if (i : ℕ) = n then base_planeP n else base_planeM n

theorem base_norm_const (n : ℕ) (hn : 0 < n) (c : ℝ)
    (hc : c = 1 / Real.sqrt n ∨ c = -(1 / Real.sqrt n)) :
    ‖(WithLp.toLp 2 (fun _ : Fin n => c) : EuclideanSpace ℝ (Fin n))‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hsq : c ^ 2 = 1 / (n : ℝ) := by
    have h1 : (1 / Real.sqrt n) ^ 2 = 1 / (n : ℝ) := by
      rw [div_pow, Real.sq_sqrt hn'.le, one_pow]
    rcases hc with hc | hc
    · rw [hc, h1]
    · rw [hc, neg_sq, h1]
  simp only [Real.norm_eq_abs, sq_abs, hsq, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  rw [mul_one_div_cancel hn'.ne', Real.sqrt_one]

theorem base_isValid_sphere (n : ℕ) (i : Fin n) : OrientedSphere.IsValid (base_sphere n i) := by
  simp [base_sphere, OrientedSphere.IsValid]

theorem base_isValid_planeP (n : ℕ) (hn : 0 < n) : OrientedSphere.IsValid (base_planeP n) := by
  simp only [base_planeP, OrientedSphere.IsValid, Sum.elim_inr]
  exact base_norm_const n hn _ (Or.inl rfl)

theorem base_isValid_planeM (n : ℕ) (hn : 0 < n) : OrientedSphere.IsValid (base_planeM n) := by
  simp only [base_planeM, OrientedSphere.IsValid, Sum.elim_inr]
  exact base_norm_const n hn _ (Or.inr rfl)

theorem base_inner_single (n : ℕ) (i : Fin n) (c : ℝ) :
    inner ℝ (WithLp.toLp 2 (fun _ : Fin n => c) : EuclideanSpace ℝ (Fin n))
      (Real.sqrt 2 • EuclideanSpace.single i (1 : ℝ)) = Real.sqrt 2 * c := by
  rw [real_inner_comm, real_inner_smul_left, EuclideanSpace.inner_single_left]
  simp

theorem base_tangent_sphere_sphere (n : ℕ) (i j : Fin n) (hij : i ≠ j) :
    OrientedSphere.Tangent (base_sphere n i) (base_sphere n j) := by
  simp only [base_sphere, OrientedSphere.Tangent, Sum.elim_inl]
  rw [dist_eq_norm, ← smul_sub, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    Real.sq_sqrt (by norm_num), norm_sub_sq_real, EuclideanSpace.inner_single_left]
  simp [hij]
  norm_num

theorem base_tangent_sphere_planeP (n : ℕ) (i : Fin n) :
    OrientedSphere.Tangent (base_sphere n i) (base_planeP n) := by
  simp only [base_sphere, base_planeP, OrientedSphere.Tangent, Sum.elim_inl, Sum.elim_inr]
  rw [base_inner_single]
  ring

theorem base_tangent_planeP_sphere (n : ℕ) (i : Fin n) :
    OrientedSphere.Tangent (base_planeP n) (base_sphere n i) := by
  simp only [base_sphere, base_planeP, OrientedSphere.Tangent, Sum.elim_inl, Sum.elim_inr]
  rw [base_inner_single]
  ring

theorem base_tangent_sphere_planeM (n : ℕ) (i : Fin n) :
    OrientedSphere.Tangent (base_sphere n i) (base_planeM n) := by
  simp only [base_sphere, base_planeM, OrientedSphere.Tangent, Sum.elim_inl, Sum.elim_inr]
  rw [base_inner_single]
  ring

theorem base_tangent_planeM_sphere (n : ℕ) (i : Fin n) :
    OrientedSphere.Tangent (base_planeM n) (base_sphere n i) := by
  simp only [base_sphere, base_planeM, OrientedSphere.Tangent, Sum.elim_inl, Sum.elim_inr]
  rw [base_inner_single]
  ring

theorem base_tangent_planeP_planeM (n : ℕ) :
    OrientedSphere.Tangent (base_planeP n) (base_planeM n) := by
  simp only [base_planeP, base_planeM, OrientedSphere.Tangent, Sum.elim_inr]
  ext k
  simp

theorem base_tangent_planeM_planeP (n : ℕ) :
    OrientedSphere.Tangent (base_planeM n) (base_planeP n) := by
  simp only [base_planeP, base_planeM, OrientedSphere.Tangent, Sum.elim_inr]
  ext k
  simp

theorem base_config_isValid (n : ℕ) (hn : 0 < n) (i : Fin (n + 2)) :
    OrientedSphere.IsValid (base_config n i) := by
  unfold base_config
  split_ifs
  · exact base_isValid_sphere n _
  · exact base_isValid_planeP n hn
  · exact base_isValid_planeM n hn

theorem base_config_tangent (n : ℕ) (i j : Fin (n + 2)) (hij : i ≠ j) :
    OrientedSphere.Tangent (base_config n i) (base_config n j) := by
  have hv : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
  have hi2 := i.isLt
  have hj2 := j.isLt
  unfold base_config
  split_ifs
  all_goals first
    | exact base_tangent_sphere_sphere n _ _ (fun h => hv (by simpa using congrArg Fin.val h))
    | exact base_tangent_sphere_planeP n _
    | exact base_tangent_sphere_planeM n _
    | exact base_tangent_planeP_sphere n _
    | exact base_tangent_planeM_sphere n _
    | exact base_tangent_planeP_planeM n
    | exact base_tangent_planeM_planeP n
    | (exfalso; omega)

/-- Existence of a configuration in every dimension: two parallel hyperplanes at distance `2` and `n`
unit spheres centred at `√2 eᵢ` (the configuration of GLMWY III, Theorem 6.1). -/
theorem exists_configuration_internal (n : ℕ) (hn : 0 < n) :
    ∃ s : Fin (n + 2) → OrientedSphere n, (∀ i, OrientedSphere.IsValid (s i)) ∧
      ∀ i j, i ≠ j → OrientedSphere.Tangent (s i) (s j) :=
  ⟨base_config n, base_config_isValid n hn, base_config_tangent n⟩

end AugmentedDescartes
