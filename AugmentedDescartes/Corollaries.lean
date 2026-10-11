module

public import AugmentedDescartes.Main

/-!
# Corollaries

The complex Descartes theorem and Mathlib's spheres (ARCH.md §3). Lane `corollaries`.
-/

@[expose] public section

namespace AugmentedDescartes

open Matrix

/-- An entry of `Wᵀ Qₙ W`: `Σ Wᵢₚ Wᵢ_q − (1/n)(Σ Wᵢₚ)(Σ Wᵢ_q)`. -/
theorem cor_entry {n : ℕ} {ι : Type*} (W : Matrix (Fin (n + 2)) ι ℝ) (p q : ι) :
    (Wᵀ * descartesQ n * W) p q =
      ∑ i, W i p * W i q - (n : ℝ)⁻¹ * ((∑ i, W i p) * ∑ i, W i q) := by
  unfold descartesQ
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul]
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
    Matrix.transpose_apply, Matrix.of_apply, mul_one]
  simp only [Finset.mul_sum]

/-- A summand of the complex Descartes theorem in real and imaginary parts. -/
theorem cor_summand (a b r : ℝ) :
    ((a : ℂ) + (b : ℂ) * Complex.I) / (r : ℂ) =
      ((a / r : ℝ) : ℂ) + ((b / r : ℝ) : ℂ) * Complex.I := by
  push_cast
  ring

/-- The three centre entries and the two mixed entries of the identity at `n = 2`. -/
theorem cor_entries (x : Fin (2 + 2) → EuclideanSpace ℝ (Fin 2)) (r : Fin (2 + 2) → ℝ)
    (h : PairwiseTangent x r) :
    (∑ i, x i 0 / r i * (x i 0 / r i) -
        (2 : ℝ)⁻¹ * ((∑ i, x i 0 / r i) * ∑ i, x i 0 / r i) = 2) ∧
    (∑ i, x i 1 / r i * (x i 1 / r i) -
        (2 : ℝ)⁻¹ * ((∑ i, x i 1 / r i) * ∑ i, x i 1 / r i) = 2) ∧
    (∑ i, x i 0 / r i * (x i 1 / r i) -
        (2 : ℝ)⁻¹ * ((∑ i, x i 0 / r i) * ∑ i, x i 1 / r i) = 0) ∧
    (∑ i, 1 / r i * (x i 0 / r i) -
        (2 : ℝ)⁻¹ * ((∑ i, 1 / r i) * ∑ i, x i 0 / r i) = 0) ∧
    (∑ i, 1 / r i * (x i 1 / r i) -
        (2 : ℝ)⁻¹ * ((∑ i, 1 / r i) * ∑ i, x i 1 / r i) = 0) := by
  have hA := augmented_descartes_internal (by norm_num) x r h
  have e : ∀ p q : Fin 2 ⊕ Fin 2,
      (∑ i, augmentedMatrix x r i p * augmentedMatrix x r i q -
        ((2 : ℕ) : ℝ)⁻¹ * ((∑ i, augmentedMatrix x r i p) * ∑ i, augmentedMatrix x r i q)) =
        augmentedTarget 2 p q := by
    intro p q
    rw [← cor_entry, hA]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have := e (Sum.inr 0) (Sum.inr 0)
    simpa [augmentedMatrix, sphereRow, augmentedTarget] using this
  · have := e (Sum.inr 1) (Sum.inr 1)
    simpa [augmentedMatrix, sphereRow, augmentedTarget] using this
  · have := e (Sum.inr 0) (Sum.inr 1)
    simpa [augmentedMatrix, sphereRow, augmentedTarget] using this
  · have := e (Sum.inl 1) (Sum.inr 0)
    simpa [augmentedMatrix, sphereRow, augmentedTarget] using this
  · have := e (Sum.inl 1) (Sum.inr 1)
    simpa [augmentedMatrix, sphereRow, augmentedTarget] using this

/-- The complex Descartes theorem (LMW Theorem 2.1, (2.2)) for four circles of nonzero curvature:
with `zᵢ = xᵢ + i yᵢ`, `(Σ bᵢ zᵢ)² = 2 Σ (bᵢ zᵢ)²`. -/
theorem complex_descartes_internal (x : Fin (2 + 2) → EuclideanSpace ℝ (Fin 2)) (r : Fin (2 + 2) → ℝ)
    (h : PairwiseTangent x r) :
    (∑ i, ((x i 0 : ℂ) + (x i 1 : ℂ) * Complex.I) / r i) ^ 2 =
      2 * ∑ i, (((x i 0 : ℂ) + (x i 1 : ℂ) * Complex.I) / r i) ^ 2 := by
  obtain ⟨h00, h11, h01, -, -⟩ := cor_entries x r h
  simp_rw [cor_summand]
  apply Complex.ext
  · simp only [sq, Complex.mul_re, Complex.re_sum, Complex.im_sum, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.mul_im,
      Complex.re_ofNat, Complex.im_ofNat]
    simp only [mul_zero, mul_one, sub_zero, zero_mul, add_zero, zero_add, Finset.sum_sub_distrib]
    linear_combination (-2 : ℝ) * h00 + 2 * h11
  · simp only [sq, Complex.mul_im, Complex.mul_re, Complex.re_sum, Complex.im_sum, Complex.add_re,
      Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.re_ofNat, Complex.im_ofNat]
    simp only [mul_zero, mul_one, sub_zero, zero_mul, add_zero, zero_add, Finset.sum_add_distrib]
    have hs : ∑ i, x i 1 / r i * (x i 0 / r i) = ∑ i, x i 0 / r i * (x i 1 / r i) :=
      Finset.sum_congr rfl fun i _ => mul_comm _ _
    linear_combination (-4 : ℝ) * h01 - 2 * hs

/-- LMW (2.3): `Σ bᵢ (bᵢ zᵢ) = ½ (Σ bᵢ)(Σ bᵢ zᵢ)`. -/
theorem complex_descartes_mixed_internal (x : Fin (2 + 2) → EuclideanSpace ℝ (Fin 2)) (r : Fin (2 + 2) → ℝ)
    (h : PairwiseTangent x r) :
    ∑ i, (1 / r i : ℂ) * (((x i 0 : ℂ) + (x i 1 : ℂ) * Complex.I) / r i) =
      (1 / 2) * (∑ i, (1 / r i : ℂ)) * ∑ i, ((x i 0 : ℂ) + (x i 1 : ℂ) * Complex.I) / r i := by
  obtain ⟨-, -, -, hm0, hm1⟩ := cor_entries x r h
  have hb : ∀ i, (1 / r i : ℂ) = ((1 / r i : ℝ) : ℂ) := fun i => by push_cast; rfl
  simp_rw [cor_summand, hb]
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.re_sum, Complex.im_sum, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.mul_im,
      Complex.div_ofNat_re, Complex.div_ofNat_im, Complex.one_re, Complex.one_im]
    simp only [mul_zero, mul_one, sub_zero, zero_mul, add_zero, zero_add, zero_div]
    linear_combination hm0
  · simp only [Complex.mul_im, Complex.mul_re, Complex.re_sum, Complex.im_sum, Complex.add_re,
      Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.div_ofNat_re, Complex.div_ofNat_im, Complex.one_re, Complex.one_im]
    simp only [mul_zero, mul_one, sub_zero, zero_mul, add_zero, zero_add, zero_div]
    linear_combination hm1

/-- Pairwise external tangency of Mathlib's spheres of positive radius gives `PairwiseTangent`. -/
theorem cor_pairwiseTangent_of_ext {n : ℕ}
    (s : Fin (n + 2) → EuclideanGeometry.Sphere (EuclideanSpace ℝ (Fin n)))
    (hr : ∀ i, 0 < (s i).radius)
    (ht : ∀ i j, i ≠ j → EuclideanGeometry.Sphere.IsExtTangent (s i) (s j)) :
    PairwiseTangent (fun i => (s i).center) (fun i => (s i).radius) :=
  ⟨fun i => (hr i).ne', fun i j hij => by simp only [(ht i j hij).dist_center]⟩

/-- Soddy–Gosset for Mathlib's spheres: `n + 2` spheres of positive radius, pairwise externally tangent. -/
theorem sphere_soddy_gosset_internal {n : ℕ} (hn : 0 < n)
    (s : Fin (n + 2) → EuclideanGeometry.Sphere (EuclideanSpace ℝ (Fin n)))
    (hr : ∀ i, 0 < (s i).radius)
    (ht : ∀ i j, i ≠ j → EuclideanGeometry.Sphere.IsExtTangent (s i) (s j)) :
    (∑ i, 1 / (s i).radius) ^ 2 = n * ∑ i, (1 / (s i).radius) ^ 2 :=
  soddy_gosset_internal hn _ _ (cor_pairwiseTangent_of_ext s hr ht)

/-- One enclosing sphere `e` (internally tangent to the others) and the others pairwise externally
tangent give `PairwiseTangent` with the signed radius `−rₑ` at `e`. -/
theorem cor_pairwiseTangent_enclosing {n : ℕ}
    (s : Fin (n + 2) → EuclideanGeometry.Sphere (EuclideanSpace ℝ (Fin n))) (e : Fin (n + 2))
    (hr : ∀ i, 0 < (s i).radius)
    (hint : ∀ j, j ≠ e → EuclideanGeometry.Sphere.IsIntTangent (s j) (s e))
    (hext : ∀ i j, i ≠ e → j ≠ e → i ≠ j → EuclideanGeometry.Sphere.IsExtTangent (s i) (s j)) :
    PairwiseTangent (fun i => (s i).center)
      (fun i => if i = e then -(s i).radius else (s i).radius) := by
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · have := (hr i).ne'
    dsimp only
    split_ifs <;> simp [this]
  · by_cases hi : i = e
    · subst hi
      have hj : j ≠ i := fun hji => hij hji.symm
      have hd := (hint j hj).dist_center
      simp only [↓reduceIte, hj]
      rw [dist_comm, hd]
      ring
    · by_cases hj : j = e
      · subst hj
        have hd := (hint i hi).dist_center
        simp only [↓reduceIte, hi]
        rw [hd]
        ring
      · simp only [hi, hj, ↓reduceIte]
        rw [(hext i j hi hj hij).dist_center]

/-- Soddy–Gosset with one enclosing sphere `e`, to which the others are internally tangent and which
carries the curvature `−1/rₑ`. -/
theorem sphere_soddy_gosset_enclosing_internal {n : ℕ} (hn : 0 < n)
    (s : Fin (n + 2) → EuclideanGeometry.Sphere (EuclideanSpace ℝ (Fin n))) (e : Fin (n + 2))
    (hr : ∀ i, 0 < (s i).radius)
    (hint : ∀ j, j ≠ e → EuclideanGeometry.Sphere.IsIntTangent (s j) (s e))
    (hext : ∀ i j, i ≠ e → j ≠ e → i ≠ j → EuclideanGeometry.Sphere.IsExtTangent (s i) (s j)) :
    (∑ i, (if i = e then -1 else 1) / (s i).radius) ^ 2 =
      n * ∑ i, ((if i = e then -1 else 1) / (s i).radius) ^ 2 := by
  have hPT := cor_pairwiseTangent_enclosing s e hr hint hext
  have key := soddy_gosset_internal hn _ _ hPT
  have hc : ∀ i, 1 / (if i = e then -(s i).radius else (s i).radius) =
      (if i = e then -1 else 1) / (s i).radius := by
    intro i
    split_ifs <;> simp [div_neg, neg_div]
  simp only [hc] at key
  exact key

/-- The augmented identity for Mathlib's spheres, pairwise externally tangent. -/
theorem sphere_augmented_descartes_internal {n : ℕ} (hn : 0 < n)
    (s : Fin (n + 2) → EuclideanGeometry.Sphere (EuclideanSpace ℝ (Fin n)))
    (hr : ∀ i, 0 < (s i).radius)
    (ht : ∀ i j, i ≠ j → EuclideanGeometry.Sphere.IsExtTangent (s i) (s j)) :
    (augmentedMatrix (fun i => (s i).center) (fun i => (s i).radius))ᵀ * descartesQ n *
      augmentedMatrix (fun i => (s i).center) (fun i => (s i).radius) = augmentedTarget n :=
  augmented_descartes_internal hn _ _ (cor_pairwiseTangent_of_ext s hr ht)

/-- The augmented identity for Mathlib's spheres with one enclosing sphere `e`, whose row is taken with
the signed radius `−rₑ`. -/
theorem cor_sphere_augmented_descartes_enclosing {n : ℕ} (hn : 0 < n)
    (s : Fin (n + 2) → EuclideanGeometry.Sphere (EuclideanSpace ℝ (Fin n))) (e : Fin (n + 2))
    (hr : ∀ i, 0 < (s i).radius)
    (hint : ∀ j, j ≠ e → EuclideanGeometry.Sphere.IsIntTangent (s j) (s e))
    (hext : ∀ i j, i ≠ e → j ≠ e → i ≠ j → EuclideanGeometry.Sphere.IsExtTangent (s i) (s j)) :
    (augmentedMatrix (fun i => (s i).center)
        (fun i => if i = e then -(s i).radius else (s i).radius))ᵀ * descartesQ n *
      augmentedMatrix (fun i => (s i).center)
        (fun i => if i = e then -(s i).radius else (s i).radius) = augmentedTarget n :=
  augmented_descartes_internal hn _ _ (cor_pairwiseTangent_enclosing s e hr hint hext)

end AugmentedDescartes
