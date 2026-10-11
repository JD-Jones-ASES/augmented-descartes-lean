module

public import AugmentedDescartes

/-!
# Solution

Each statement of `Challenge.lean`, restated verbatim and closed by the internal theorem of the same
name with the suffix `_internal` (the modules of `AugmentedDescartes/`; VERIFICATION.md names the module of
each theorem). This module does not import `Challenge.lean`; the definitions come from
`AugmentedDescartes/Defs.lean`, which restates those of the Challenge character for character.
-/

@[expose] public section

namespace AugmentedDescartes

open Matrix

theorem lorentz_sphereRow_self {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) (r : ℝ) (hr : r ≠ 0) :
    lorentz (sphereRow x r) (sphereRow x r) = 1 :=
  lorentz_sphereRow_self_internal x r hr

theorem lorentz_sphereRow_eq_neg_one_iff {n : ℕ} (x y : EuclideanSpace ℝ (Fin n)) (r s : ℝ)
    (hr : r ≠ 0) (hs : s ≠ 0) :
    lorentz (sphereRow x r) (sphereRow y s) = -1 ↔ dist x y ^ 2 = (r + s) ^ 2 :=
  lorentz_sphereRow_eq_neg_one_iff_internal x y r s hr hs

theorem lorentz_sphereRow_planeRow_eq_neg_one_iff {n : ℕ} (x h : EuclideanSpace ℝ (Fin n)) (r δ : ℝ)
    (hr : r ≠ 0) :
    lorentz (sphereRow x r) (planeRow h δ) = -1 ↔ inner ℝ h x - δ = -r :=
  lorentz_sphereRow_planeRow_eq_neg_one_iff_internal x h r δ hr

theorem lorentz_planeRow_eq_neg_one_iff {n : ℕ} (h k : EuclideanSpace ℝ (Fin n)) (δ ε : ℝ)
    (hh : ‖h‖ = 1) (hk : ‖k‖ = 1) :
    lorentz (planeRow h δ) (planeRow k ε) = -1 ↔ k = -h :=
  lorentz_planeRow_eq_neg_one_iff_internal h k δ ε hh hk

theorem lorentz_row_self {n : ℕ} (s : OrientedSphere n) (hs : OrientedSphere.IsValid s) :
    lorentz (OrientedSphere.row s) (OrientedSphere.row s) = 1 :=
  lorentz_row_self_internal s hs

theorem lorentz_row_eq_neg_one_iff {n : ℕ} (s t : OrientedSphere n) (hs : OrientedSphere.IsValid s)
    (ht : OrientedSphere.IsValid t) :
    lorentz (OrientedSphere.row s) (OrientedSphere.row t) = -1 ↔ OrientedSphere.Tangent s t :=
  lorentz_row_eq_neg_one_iff_internal s t hs ht

theorem row_injOn_valid {n : ℕ} (s t : OrientedSphere n) (hs : OrientedSphere.IsValid s)
    (ht : OrientedSphere.IsValid t) (h : OrientedSphere.row s = OrientedSphere.row t) : s = t :=
  row_injOn_valid_internal s t hs ht h

theorem exists_orientedSphere_of_lorentz_self {n : ℕ} (w : Fin 2 ⊕ Fin n → ℝ) (hw : lorentz w w = 1) :
    ∃ s : OrientedSphere n, OrientedSphere.IsValid s ∧ OrientedSphere.row s = w :=
  exists_orientedSphere_of_lorentz_self_internal w hw

theorem augmented_identity_iff_lorentz {n : ℕ} (hn : 0 < n) (W : Matrix (Fin (n + 2)) (Fin 2 ⊕ Fin n) ℝ) :
    Wᵀ * descartesQ n * W = augmentedTarget n ↔
      (∀ i, lorentz (W i) (W i) = 1) ∧ ∀ i j, i ≠ j → lorentz (W i) (W j) = -1 :=
  augmented_identity_iff_lorentz_internal hn W

theorem gram_eq_of_augmented_identity {n : ℕ} (hn : 0 < n) (W : Matrix (Fin (n + 2)) (Fin 2 ⊕ Fin n) ℝ)
    (hW : Wᵀ * descartesQ n * W = augmentedTarget n) :
    W * lorentzG n * Wᵀ = 2 • (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ) - Matrix.of (fun _ _ => 1) :=
  gram_eq_of_augmented_identity_internal hn W hW

theorem augmented_descartes {n : ℕ} (hn : 0 < n) (x : Fin (n + 2) → EuclideanSpace ℝ (Fin n))
    (r : Fin (n + 2) → ℝ) (h : PairwiseTangent x r) :
    (augmentedMatrix x r)ᵀ * descartesQ n * augmentedMatrix x r = augmentedTarget n :=
  augmented_descartes_internal hn x r h

theorem augmented_descartes_general {n : ℕ} (hn : 0 < n) (s : Fin (n + 2) → OrientedSphere n)
    (hv : ∀ i, OrientedSphere.IsValid (s i))
    (ht : ∀ i j, i ≠ j → OrientedSphere.Tangent (s i) (s j)) :
    (augmentedMatrixOf s)ᵀ * descartesQ n * augmentedMatrixOf s = augmentedTarget n :=
  augmented_descartes_general_internal hn s hv ht

theorem augmented_descartes_converse {n : ℕ} (hn : 0 < n) (W : Matrix (Fin (n + 2)) (Fin 2 ⊕ Fin n) ℝ)
    (hW : Wᵀ * descartesQ n * W = augmentedTarget n) :
    ∃! s : Fin (n + 2) → OrientedSphere n, (∀ i, OrientedSphere.IsValid (s i)) ∧
      (∀ i j, i ≠ j → OrientedSphere.Tangent (s i) (s j)) ∧ augmentedMatrixOf s = W :=
  augmented_descartes_converse_internal hn W hW

theorem augmented_descartes_converse_spheres {n : ℕ} (hn : 0 < n)
    (W : Matrix (Fin (n + 2)) (Fin 2 ⊕ Fin n) ℝ) (hW : Wᵀ * descartesQ n * W = augmentedTarget n)
    (hb : ∀ i, W i (Sum.inl 1) ≠ 0) :
    ∃! p : (Fin (n + 2) → EuclideanSpace ℝ (Fin n)) × (Fin (n + 2) → ℝ),
      PairwiseTangent p.1 p.2 ∧ augmentedMatrix p.1 p.2 = W :=
  augmented_descartes_converse_spheres_internal hn W hW hb

theorem soddy_gosset {n : ℕ} (hn : 0 < n) (x : Fin (n + 2) → EuclideanSpace ℝ (Fin n))
    (r : Fin (n + 2) → ℝ) (h : PairwiseTangent x r) :
    (∑ i, 1 / r i) ^ 2 = n * ∑ i, (1 / r i) ^ 2 :=
  soddy_gosset_internal hn x r h

theorem soddy_gosset_general {n : ℕ} (hn : 0 < n) (s : Fin (n + 2) → OrientedSphere n)
    (hv : ∀ i, OrientedSphere.IsValid (s i))
    (ht : ∀ i j, i ≠ j → OrientedSphere.Tangent (s i) (s j)) :
    (∑ i, OrientedSphere.curvature (s i)) ^ 2 = n * ∑ i, OrientedSphere.curvature (s i) ^ 2 :=
  soddy_gosset_general_internal hn s hv ht

theorem soddy_gosset_iff_isotropic {n : ℕ} (hn : 0 < n) (b : Fin (n + 2) → ℝ) :
    (∑ i, b i) ^ 2 = n * ∑ i, b i ^ 2 ↔ b ⬝ᵥ (descartesQ n *ᵥ b) = 0 :=
  soddy_gosset_iff_isotropic_internal hn b

theorem curvature_center {n : ℕ} (hn : 0 < n) (x : Fin (n + 2) → EuclideanSpace ℝ (Fin n))
    (r : Fin (n + 2) → ℝ) (h : PairwiseTangent x r) :
    (curvatureCenterMatrix x r)ᵀ * descartesQ n * curvatureCenterMatrix x r =
      curvatureCenterTarget n :=
  curvature_center_internal hn x r h

theorem curvature_center_general {n : ℕ} (hn : 0 < n) (s : Fin (n + 2) → OrientedSphere n)
    (hv : ∀ i, OrientedSphere.IsValid (s i))
    (ht : ∀ i j, i ≠ j → OrientedSphere.Tangent (s i) (s j)) :
    (curvatureCenterMatrixOf s)ᵀ * descartesQ n * curvatureCenterMatrixOf s =
      curvatureCenterTarget n :=
  curvature_center_general_internal hn s hv ht

theorem complex_descartes (x : Fin (2 + 2) → EuclideanSpace ℝ (Fin 2)) (r : Fin (2 + 2) → ℝ)
    (h : PairwiseTangent x r) :
    (∑ i, ((x i 0 : ℂ) + (x i 1 : ℂ) * Complex.I) / r i) ^ 2 =
      2 * ∑ i, (((x i 0 : ℂ) + (x i 1 : ℂ) * Complex.I) / r i) ^ 2 :=
  complex_descartes_internal x r h

theorem complex_descartes_mixed (x : Fin (2 + 2) → EuclideanSpace ℝ (Fin 2)) (r : Fin (2 + 2) → ℝ)
    (h : PairwiseTangent x r) :
    ∑ i, (1 / r i : ℂ) * (((x i 0 : ℂ) + (x i 1 : ℂ) * Complex.I) / r i) =
      (1 / 2) * (∑ i, (1 / r i : ℂ)) * ∑ i, ((x i 0 : ℂ) + (x i 1 : ℂ) * Complex.I) / r i :=
  complex_descartes_mixed_internal x r h

theorem det_descartesQ (n : ℕ) (hn : 0 < n) : (descartesQ n).det = -2 / n :=
  det_descartesQ_internal n hn

theorem sphere_soddy_gosset {n : ℕ} (hn : 0 < n)
    (s : Fin (n + 2) → EuclideanGeometry.Sphere (EuclideanSpace ℝ (Fin n)))
    (hr : ∀ i, 0 < (s i).radius)
    (ht : ∀ i j, i ≠ j → EuclideanGeometry.Sphere.IsExtTangent (s i) (s j)) :
    (∑ i, 1 / (s i).radius) ^ 2 = n * ∑ i, (1 / (s i).radius) ^ 2 :=
  sphere_soddy_gosset_internal hn s hr ht

theorem sphere_soddy_gosset_enclosing {n : ℕ} (hn : 0 < n)
    (s : Fin (n + 2) → EuclideanGeometry.Sphere (EuclideanSpace ℝ (Fin n))) (e : Fin (n + 2))
    (hr : ∀ i, 0 < (s i).radius)
    (hint : ∀ j, j ≠ e → EuclideanGeometry.Sphere.IsIntTangent (s j) (s e))
    (hext : ∀ i j, i ≠ e → j ≠ e → i ≠ j → EuclideanGeometry.Sphere.IsExtTangent (s i) (s j)) :
    (∑ i, (if i = e then -1 else 1) / (s i).radius) ^ 2 =
      n * ∑ i, ((if i = e then -1 else 1) / (s i).radius) ^ 2 :=
  sphere_soddy_gosset_enclosing_internal hn s e hr hint hext

theorem sphere_augmented_descartes {n : ℕ} (hn : 0 < n)
    (s : Fin (n + 2) → EuclideanGeometry.Sphere (EuclideanSpace ℝ (Fin n)))
    (hr : ∀ i, 0 < (s i).radius)
    (ht : ∀ i j, i ≠ j → EuclideanGeometry.Sphere.IsExtTangent (s i) (s j)) :
    (augmentedMatrix (fun i => (s i).center) (fun i => (s i).radius))ᵀ * descartesQ n *
      augmentedMatrix (fun i => (s i).center) (fun i => (s i).radius) = augmentedTarget n :=
  sphere_augmented_descartes_internal hn s hr ht

theorem exists_configuration (n : ℕ) (hn : 0 < n) :
    ∃ s : Fin (n + 2) → OrientedSphere n, (∀ i, OrientedSphere.IsValid (s i)) ∧
      ∀ i j, i ≠ j → OrientedSphere.Tangent (s i) (s j) :=
  exists_configuration_internal n hn

theorem exists_pairwiseTangent (n : ℕ) (hn : 0 < n) :
    ∃ x : Fin (n + 2) → EuclideanSpace ℝ (Fin n), ∃ r : Fin (n + 2) → ℝ, PairwiseTangent x r :=
  exists_pairwiseTangent_internal n hn

theorem converse_soddy_gosset {n : ℕ} (hn : 0 < n) (b : Fin (n + 2) → ℝ) (hb : b ≠ 0)
    (h : (∑ i, b i) ^ 2 = n * ∑ i, b i ^ 2) :
    ∃ s : Fin (n + 2) → OrientedSphere n, (∀ i, OrientedSphere.IsValid (s i)) ∧
      (∀ i j, i ≠ j → OrientedSphere.Tangent (s i) (s j)) ∧
      ∀ i, OrientedSphere.curvature (s i) = b i :=
  converse_soddy_gosset_internal hn b hb h

theorem converse_soddy_gosset_spheres {n : ℕ} (hn : 0 < n) (b : Fin (n + 2) → ℝ) (hb : ∀ i, b i ≠ 0)
    (h : (∑ i, b i) ^ 2 = n * ∑ i, b i ^ 2) :
    ∃ x : Fin (n + 2) → EuclideanSpace ℝ (Fin n), ∃ r : Fin (n + 2) → ℝ,
      PairwiseTangent x r ∧ ∀ i, 1 / r i = b i :=
  converse_soddy_gosset_spheres_internal hn b hb h

theorem curvature_center_converse {n : ℕ} (hn : 0 < n) (M : Matrix (Fin (n + 2)) (Fin 1 ⊕ Fin n) ℝ)
    (hM : Mᵀ * descartesQ n * M = curvatureCenterTarget n) (hb : ∃ i, M i (Sum.inl 0) ≠ 0) :
    ∃! s : Fin (n + 2) → OrientedSphere n, (∀ i, OrientedSphere.IsValid (s i)) ∧
      (∀ i j, i ≠ j → OrientedSphere.Tangent (s i) (s j)) ∧ curvatureCenterMatrixOf s = M :=
  curvature_center_converse_internal hn M hM hb

theorem curvature_center_converse_needs_nonzero :
    ∃ M : Matrix (Fin (2 + 2)) (Fin 1 ⊕ Fin 2) ℝ, Mᵀ * descartesQ 2 * M = curvatureCenterTarget 2 ∧
      (∀ i, M i (Sum.inl 0) = 0) ∧
      ¬ ∃ s : Fin (2 + 2) → OrientedSphere 2, (∀ i, OrientedSphere.IsValid (s i)) ∧
        (∀ i j, i ≠ j → OrientedSphere.Tangent (s i) (s j)) ∧ curvatureCenterMatrixOf s = M :=
  curvature_center_converse_needs_nonzero_internal

theorem apollonianGen_mem_aut {n : ℕ} (hn : 2 ≤ n) (k : Fin (n + 2)) :
    (apollonianGen n k)ᵀ * descartesQ n * apollonianGen n k = descartesQ n :=
  apollonianGen_mem_aut_internal hn k

theorem apollonian_reflection {n : ℕ} (hn : 2 ≤ n) (W : Matrix (Fin (n + 2)) (Fin 2 ⊕ Fin n) ℝ)
    (hW : Wᵀ * descartesQ n * W = augmentedTarget n) (k : Fin (n + 2)) :
    (apollonianGen n k * W)ᵀ * descartesQ n * (apollonianGen n k * W) = augmentedTarget n :=
  apollonian_reflection_internal hn W hW k

theorem apollonianGen_mul_apply {n : ℕ} (hn : 2 ≤ n) (W : Matrix (Fin (n + 2)) (Fin 2 ⊕ Fin n) ℝ)
    (k : Fin (n + 2)) (j : Fin 2 ⊕ Fin n) :
    (apollonianGen n k * W) k j = (2 / ((n : ℝ) - 1)) * ∑ i ∈ Finset.univ.erase k, W i j - W k j :=
  apollonianGen_mul_apply_internal hn W k j

theorem two_tangent_rows {n : ℕ} (hn : 2 ≤ n) (W : Matrix (Fin (n + 2)) (Fin 2 ⊕ Fin n) ℝ)
    (hW : Wᵀ * descartesQ n * W = augmentedTarget n) (k : Fin (n + 2)) :
    (∀ w : Fin 2 ⊕ Fin n → ℝ, (lorentz w w = 1 ∧ ∀ i, i ≠ k → lorentz w (W i) = -1) ↔
      (w = W k ∨ w = (apollonianGen n k * W) k)) ∧ W k ≠ (apollonianGen n k * W) k :=
  two_tangent_rows_internal hn W hW k

theorem two_tangent_spheres {n : ℕ} (hn : 2 ≤ n) (s : Fin (n + 2) → OrientedSphere n)
    (hv : ∀ i, OrientedSphere.IsValid (s i))
    (ht : ∀ i j, i ≠ j → OrientedSphere.Tangent (s i) (s j)) (k : Fin (n + 2)) :
    ∃ t : OrientedSphere n, OrientedSphere.IsValid t ∧ t ≠ s k ∧
      (∀ i, i ≠ k → OrientedSphere.Tangent t (s i)) ∧
      OrientedSphere.curvature t + OrientedSphere.curvature (s k) =
        (2 / ((n : ℝ) - 1)) * ∑ i ∈ Finset.univ.erase k, OrientedSphere.curvature (s i) ∧
      ∀ u : OrientedSphere n, OrientedSphere.IsValid u → (∀ i, i ≠ k → OrientedSphere.Tangent u (s i)) →
        u = s k ∨ u = t :=
  two_tangent_spheres_internal hn s hv ht k

theorem same_curvature_motion {n : ℕ}
    (W₁ W₂ : Matrix (Fin (n + 2)) (Fin 2 ⊕ Fin n) ℝ)
    (hW₁ : W₁ᵀ * descartesQ n * W₁ = augmentedTarget n)
    (hW₂ : W₂ᵀ * descartesQ n * W₂ = augmentedTarget n)
    (hb : ∀ i, W₁ i (Sum.inl 1) = W₂ i (Sum.inl 1)) :
    ∃! p : Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ),
      p.1ᵀ * p.1 = 1 ∧ W₁ * rigidMotionMatrix p.1 p.2 = W₂ :=
  same_curvature_motion_internal W₁ W₂ hW₁ hW₂ hb

theorem rigidMotion_parameters {n : ℕ}
    (W₁ W₂ : Matrix (Fin (n + 2)) (Fin 2 ⊕ Fin n) ℝ)
    (hW₁ : W₁ᵀ * descartesQ n * W₁ = augmentedTarget n)
    (O : Matrix (Fin n) (Fin n) ℝ) (t : Fin n → ℝ)
    (h : W₁ * rigidMotionMatrix O t = W₂) :
    (∀ k l, O k l = (1 / 2 : ℝ) *
      ((fun i => W₁ i (Sum.inr k)) ⬝ᵥ (descartesQ n *ᵥ (fun i => W₂ i (Sum.inr l))))) ∧
    ∀ l, t l = (-1 / 4 : ℝ) *
      ((fun i => W₁ i (Sum.inl 0)) ⬝ᵥ (descartesQ n *ᵥ (fun i => W₂ i (Sum.inr l)))) :=
  rigidMotion_parameters_internal W₁ W₂ hW₁ O t h

theorem rigidMotionPoint_isometry {n : ℕ} (O : Matrix (Fin n) (Fin n) ℝ)
    (hO : Oᵀ * O = 1) (t : Fin n → ℝ) : Isometry (rigidMotionPoint O t) :=
  rigidMotionPoint_isometry_internal O hO t

theorem rigidMotionMatrix_sphereRow {n : ℕ} (O : Matrix (Fin n) (Fin n) ℝ)
    (hO : Oᵀ * O = 1) (t : Fin n → ℝ) (x : EuclideanSpace ℝ (Fin n)) (r : ℝ) :
    sphereRow x r ᵥ* rigidMotionMatrix O t = sphereRow (rigidMotionPoint O t x) r :=
  rigidMotionMatrix_sphereRow_internal O hO t x r

theorem rigidMotionMatrix_planeRow {n : ℕ} (O : Matrix (Fin n) (Fin n) ℝ)
    (t : Fin n → ℝ) (h : EuclideanSpace ℝ (Fin n)) (δ : ℝ) :
    planeRow h δ ᵥ* rigidMotionMatrix O t =
      planeRow (rigidMotionPoint O 0 h) (δ + ((fun k => h k) ᵥ* O) ⬝ᵥ t) :=
  rigidMotionMatrix_planeRow_internal O t h δ

theorem same_curvature_congruence {n : ℕ} (hn : 0 < n)
    (s s' : Fin (n + 2) → OrientedSphere n)
    (hs : ∀ i, OrientedSphere.IsValid (s i))
    (hs' : ∀ i, OrientedSphere.IsValid (s' i))
    (ht : ∀ i j, i ≠ j → OrientedSphere.Tangent (s i) (s j))
    (ht' : ∀ i j, i ≠ j → OrientedSphere.Tangent (s' i) (s' j))
    (hb : ∀ i, OrientedSphere.curvature (s i) = OrientedSphere.curvature (s' i)) :
    ∃! p : Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ),
      p.1ᵀ * p.1 = 1 ∧ ∀ i, rigidMotionOf p.1 p.2 (s i) = s' i :=
  same_curvature_congruence_internal hn s s' hs hs' ht ht' hb

theorem rowPower_sphereRow {n : ℕ} (x y : EuclideanSpace ℝ (Fin n))
    (r : ℝ) (hr : r ≠ 0) :
    rowPower (sphereRow x r) y = (dist y x ^ 2 - r ^ 2) / r :=
  rowPower_sphereRow_internal x y r hr

theorem rowPower_planeRow {n : ℕ} (h y : EuclideanSpace ℝ (Fin n))
    (δ : ℝ) : rowPower (planeRow h δ) y = 2 * (δ - inner ℝ h y) :=
  rowPower_planeRow_internal h y δ

theorem rowPower_sphereRow_neg_iff_of_pos {n : ℕ}
    (x y : EuclideanSpace ℝ (Fin n)) (r : ℝ) (hr : 0 < r) :
    rowPower (sphereRow x r) y < 0 ↔ dist y x < r :=
  rowPower_sphereRow_neg_iff_of_pos_internal x y r hr

theorem rowPower_sphereRow_neg_iff_of_neg {n : ℕ}
    (x y : EuclideanSpace ℝ (Fin n)) (r : ℝ) (hr : r < 0) :
    rowPower (sphereRow x r) y < 0 ↔ -r < dist y x :=
  rowPower_sphereRow_neg_iff_of_neg_internal x y r hr

theorem rowPower_planeRow_neg_iff {n : ℕ}
    (h y : EuclideanSpace ℝ (Fin n)) (δ : ℝ) :
    rowPower (planeRow h δ) y < 0 ↔ δ < inner ℝ h y :=
  rowPower_planeRow_neg_iff_internal h y δ

theorem augmented_orientation {n : ℕ} (hn : 0 < n)
    (W : Matrix (Fin (n + 2)) (Fin 2 ⊕ Fin n) ℝ)
    (hW : Wᵀ * descartesQ n * W = augmentedTarget n) :
    (∑ k, W k (Sum.inl 1)) ≠ 0 ∧
      ∀ (i j : Fin (n + 2)), i ≠ j → ∀ y : EuclideanSpace ℝ (Fin n),
        ¬ ((∑ k, W k (Sum.inl 1)) * rowPower (W i) y < 0 ∧
          (∑ k, W k (Sum.inl 1)) * rowPower (W j) y < 0) :=
  augmented_orientation_internal hn W hW

theorem augmented_orientation_disjoint {n : ℕ} (hn : 0 < n)
    (W : Matrix (Fin (n + 2)) (Fin 2 ⊕ Fin n) ℝ)
    (hW : Wᵀ * descartesQ n * W = augmentedTarget n)
    (i j : Fin (n + 2)) (hij : i ≠ j) :
    Disjoint {y : EuclideanSpace ℝ (Fin n) |
      (∑ k, W k (Sum.inl 1)) * rowPower (W i) y < 0}
      {y : EuclideanSpace ℝ (Fin n) |
        (∑ k, W k (Sum.inl 1)) * rowPower (W j) y < 0} :=
  augmented_orientation_disjoint_internal hn W hW i j hij

theorem augmented_no_three_zero_curvatures {n : ℕ} (hn : 0 < n)
    (W : Matrix (Fin (n + 2)) (Fin 2 ⊕ Fin n) ℝ)
    (hW : Wᵀ * descartesQ n * W = augmentedTarget n)
    (i j k : Fin (n + 2)) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ¬ (W i (Sum.inl 1) = 0 ∧ W j (Sum.inl 1) = 0 ∧ W k (Sum.inl 1) = 0) :=
  augmented_no_three_zero_curvatures_internal hn W hW i j k hij hik hjk

theorem augmented_no_three_boundaries {n : ℕ} (hn : 0 < n)
    (W : Matrix (Fin (n + 2)) (Fin 2 ⊕ Fin n) ℝ)
    (hW : Wᵀ * descartesQ n * W = augmentedTarget n)
    (i j k : Fin (n + 2)) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (y : EuclideanSpace ℝ (Fin n)) :
    ¬ (rowPower (W i) y = 0 ∧ rowPower (W j) y = 0 ∧ rowPower (W k) y = 0) :=
  augmented_no_three_boundaries_internal hn W hW i j k hij hik hjk y

theorem rigidMotionOf_isValid {n : ℕ} (O : Matrix (Fin n) (Fin n) ℝ) (hO : Oᵀ * O = 1)
    (t : Fin n → ℝ) (s : OrientedSphere n) (hs : OrientedSphere.IsValid s) :
    OrientedSphere.IsValid (rigidMotionOf O t s) :=
  rigidMotionOf_isValid_internal O hO t s hs

theorem rigidMotionOf_curvature {n : ℕ} (O : Matrix (Fin n) (Fin n) ℝ) (t : Fin n → ℝ)
    (s : OrientedSphere n) :
    OrientedSphere.curvature (rigidMotionOf O t s) = OrientedSphere.curvature s :=
  rigidMotionOf_curvature_internal O t s

theorem lorentz_vecMul_rigidMotionMatrix {n : ℕ} (O : Matrix (Fin n) (Fin n) ℝ)
    (hO : Oᵀ * O = 1) (t : Fin n → ℝ) (w w' : Fin 2 ⊕ Fin n → ℝ) :
    lorentz (w ᵥ* rigidMotionMatrix O t) (w' ᵥ* rigidMotionMatrix O t) = lorentz w w' :=
  lorentz_vecMul_rigidMotionMatrix_internal O hO t w w'

theorem rigidMotionOf_tangent_iff {n : ℕ} (O : Matrix (Fin n) (Fin n) ℝ) (hO : Oᵀ * O = 1)
    (t : Fin n → ℝ) (s u : OrientedSphere n) (hs : OrientedSphere.IsValid s)
    (hu : OrientedSphere.IsValid u) :
    OrientedSphere.Tangent (rigidMotionOf O t s) (rigidMotionOf O t u) ↔ OrientedSphere.Tangent s u :=
  rigidMotionOf_tangent_iff_internal O hO t s u hs hu

theorem congruent_iff_same_curvature {n : ℕ} (hn : 0 < n)
    (s s' : Fin (n + 2) → OrientedSphere n)
    (hs : ∀ i, OrientedSphere.IsValid (s i)) (hs' : ∀ i, OrientedSphere.IsValid (s' i))
    (ht : ∀ i j, i ≠ j → OrientedSphere.Tangent (s i) (s j))
    (ht' : ∀ i j, i ≠ j → OrientedSphere.Tangent (s' i) (s' j)) :
    (∃ O : Matrix (Fin n) (Fin n) ℝ, ∃ t : Fin n → ℝ, Oᵀ * O = 1 ∧ ∀ i, rigidMotionOf O t (s i) = s' i) ↔
      ∀ i, OrientedSphere.curvature (s i) = OrientedSphere.curvature (s' i) :=
  congruent_iff_same_curvature_internal hn s s' hs hs' ht ht'

theorem tangent_family_curvature_sum_ne_zero {n : ℕ} (hn : 0 < n)
    (s : Fin (n + 2) → OrientedSphere n) (hs : ∀ i, OrientedSphere.IsValid (s i))
    (ht : ∀ i j, i ≠ j → OrientedSphere.Tangent (s i) (s j)) :
    (∑ i, OrientedSphere.curvature (s i)) ≠ 0 :=
  tangent_family_curvature_sum_ne_zero_internal hn s hs ht

theorem tangent_family_interiors_disjoint {n : ℕ} (hn : 0 < n)
    (s : Fin (n + 2) → OrientedSphere n) (hs : ∀ i, OrientedSphere.IsValid (s i))
    (ht : ∀ i j, i ≠ j → OrientedSphere.Tangent (s i) (s j))
    (hpos : 0 < ∑ i, OrientedSphere.curvature (s i)) (i j : Fin (n + 2)) (hij : i ≠ j) :
    Disjoint {y : EuclideanSpace ℝ (Fin n) | rowPower (OrientedSphere.row (s i)) y < 0}
      {y : EuclideanSpace ℝ (Fin n) | rowPower (OrientedSphere.row (s j)) y < 0} :=
  tangent_family_interiors_disjoint_internal hn s hs ht hpos i j hij

theorem tangent_family_two_hyperplanes {n : ℕ} (hn : 0 < n)
    (s : Fin (n + 2) → OrientedSphere n) (hs : ∀ i, OrientedSphere.IsValid (s i))
    (ht : ∀ i j, i ≠ j → OrientedSphere.Tangent (s i) (s j))
    (i j k : Fin (n + 2)) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ¬ (OrientedSphere.curvature (s i) = 0 ∧ OrientedSphere.curvature (s j) = 0 ∧
      OrientedSphere.curvature (s k) = 0) :=
  tangent_family_two_hyperplanes_internal hn s hs ht i j k hij hik hjk

end AugmentedDescartes
