module

public import Mathlib

/-!
# Definitions

The definitions of `Challenge.lean`, restated character for character (the registry's comparator judges the
elaborated constants; `scripts/check_definitions.py` compares the text and `scripts/verify.py` the `pp.all`
output). The development's modules import this file; `Solution.lean` restates the Challenge's theorems over it
and never imports `Challenge.lean`.
-/

@[expose] public section

namespace AugmentedDescartes

open Matrix

/-- The Descartes quadratic form's matrix `Qₙ = I − (1/n) 𝟙𝟙ᵀ` on `ℝ^(n+2)` (LMW (3.1)). -/
noncomputable def descartesQ (n : ℕ) : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ :=
  1 - (n : ℝ)⁻¹ • Matrix.of (fun _ _ => (1 : ℝ))

/-- The target `[[0, −4, 0], [−4, 0, 0], [0, 0, 2 Iₙ]]` of LMW (3.11), on the index type `Fin 2 ⊕ Fin n`
(the two hyperbolic coordinates `b̄, b` and the `n` centre coordinates). -/
noncomputable def augmentedTarget (n : ℕ) : Matrix (Fin 2 ⊕ Fin n) (Fin 2 ⊕ Fin n) ℝ :=
  Matrix.fromBlocks !![0, -4; -4, 0] 0 0 (Matrix.diagonal fun _ => 2)

/-- The Lorentz form `G = [[0, −½, 0], [−½, 0, 0], [0, 0, Iₙ]]` on the row space; `2 G⁻¹` is the target. -/
noncomputable def lorentzG (n : ℕ) : Matrix (Fin 2 ⊕ Fin n) (Fin 2 ⊕ Fin n) ℝ :=
  Matrix.fromBlocks !![0, -1 / 2; -1 / 2, 0] 0 0 1

/-- The Lorentz pairing of two augmented rows `u = (ū, u₁, u')`, `v = (v̄, v₁, v')`:
`−(ū v₁ + u₁ v̄)/2 + ⟪u', v'⟫`, that is `u ⬝ᵥ (G *ᵥ v)`. -/
noncomputable def lorentz {n : ℕ} (u v : Fin 2 ⊕ Fin n → ℝ) : ℝ :=
  -(u (Sum.inl 0) * v (Sum.inl 1) + u (Sum.inl 1) * v (Sum.inl 0)) / 2 +
    ∑ k, u (Sum.inr k) * v (Sum.inr k)

/-- LMW Definition 3.2, (3.7)–(3.8): the augmented curvature–centre coordinates `(b̄, b, b x)` of the
oriented sphere with centre `x` and signed radius `r`, where `b = 1/r` and `b̄ = ‖x‖²/r − r`. -/
noncomputable def sphereRow {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) (r : ℝ) : Fin 2 ⊕ Fin n → ℝ :=
  Sum.elim ![‖x‖ ^ 2 / r - r, 1 / r] (fun k => x k / r)

/-- LMW (3.9): the coordinates `(2δ, 0, h)` of the oriented hyperplane `⟪h, y⟫ = δ` with unit normal `h`,
whose interior is the side `⟪h, y⟫ > δ` into which `h` points (the inversion of that half-space in the unit
sphere is a ball or the exterior of a ball of signed curvature `2δ`). -/
noncomputable def planeRow {n : ℕ} (h : EuclideanSpace ℝ (Fin n)) (δ : ℝ) : Fin 2 ⊕ Fin n → ℝ :=
  Sum.elim ![2 * δ, 0] (fun k => h k)

/-- Signed-radius tangency of a family: every radius is nonzero and distinct members satisfy
`dist (xᵢ, xⱼ)² = (rᵢ + rⱼ)²`. -/
def PairwiseTangent {n : ℕ} (x : Fin (n + 2) → EuclideanSpace ℝ (Fin n)) (r : Fin (n + 2) → ℝ) : Prop :=
  (∀ i, r i ≠ 0) ∧ ∀ i j, i ≠ j → dist (x i) (x j) ^ 2 = (r i + r j) ^ 2

/-- The augmented matrix of a family of spheres: row `i` is `sphereRow (x i) (r i)`. -/
noncomputable def augmentedMatrix {n : ℕ} (x : Fin (n + 2) → EuclideanSpace ℝ (Fin n))
    (r : Fin (n + 2) → ℝ) : Matrix (Fin (n + 2)) (Fin 2 ⊕ Fin n) ℝ :=
  Matrix.of fun i => sphereRow (x i) (r i)

/-- LMW Definition 3.1: the curvature–centre matrix with rows `(b, b x)`, on the index type
`Fin 1 ⊕ Fin n`. -/
noncomputable def curvatureCenterMatrix {n : ℕ} (x : Fin (n + 2) → EuclideanSpace ℝ (Fin n))
    (r : Fin (n + 2) → ℝ) : Matrix (Fin (n + 2)) (Fin 1 ⊕ Fin n) ℝ :=
  Matrix.of fun i => Sum.elim ![1 / r i] (fun k => x i k / r i)

/-- The target `diag(0, 2 Iₙ)` of LMW (3.5). -/
noncomputable def curvatureCenterTarget (n : ℕ) : Matrix (Fin 1 ⊕ Fin n) (Fin 1 ⊕ Fin n) ℝ :=
  Matrix.fromBlocks 0 0 0 (Matrix.diagonal fun _ => 2)

/-- An oriented sphere (centre, signed radius; the left summand) or an oriented hyperplane (unit normal
`h`, offset `δ`, the hyperplane `⟪h, y⟫ = δ`; the right summand). -/
abbrev OrientedSphere (n : ℕ) : Type :=
  (EuclideanSpace ℝ (Fin n) × ℝ) ⊕ (EuclideanSpace ℝ (Fin n) × ℝ)

/-- A sphere is valid when its radius is nonzero, a hyperplane when its normal is a unit vector. -/
def OrientedSphere.IsValid {n : ℕ} (s : OrientedSphere n) : Prop :=
  Sum.elim (fun p => p.2 ≠ 0) (fun p => ‖p.1‖ = 1) s

/-- The augmented row of an oriented sphere or hyperplane. -/
noncomputable def OrientedSphere.row {n : ℕ} (s : OrientedSphere n) : Fin 2 ⊕ Fin n → ℝ :=
  Sum.elim (fun p => sphereRow p.1 p.2) (fun p => planeRow p.1 p.2) s

/-- The signed curvature: `1/r` for a sphere, `0` for a hyperplane. -/
noncomputable def OrientedSphere.curvature {n : ℕ} (s : OrientedSphere n) : ℝ :=
  Sum.elim (fun p => 1 / p.2) (fun _ => 0) s

/-- LMW's oriented tangency, by cases: two spheres `dist (x, y)² = (r + s)²`; a sphere `(x, r)` and a
hyperplane `(h, δ)`: `⟪h, x⟫ − δ = −r`; two hyperplanes: opposite unit normals. -/
noncomputable def OrientedSphere.Tangent {n : ℕ} (s t : OrientedSphere n) : Prop :=
  Sum.elim
    (fun p => Sum.elim (fun q => dist p.1 q.1 ^ 2 = (p.2 + q.2) ^ 2)
      (fun q => inner ℝ q.1 p.1 - q.2 = -p.2) t)
    (fun p => Sum.elim (fun q => inner ℝ p.1 q.1 - p.2 = -q.2) (fun q => q.1 = -p.1) t) s

/-- The augmented matrix of a family of oriented spheres and hyperplanes. -/
noncomputable def augmentedMatrixOf {n : ℕ} (s : Fin (n + 2) → OrientedSphere n) :
    Matrix (Fin (n + 2)) (Fin 2 ⊕ Fin n) ℝ :=
  Matrix.of fun i => OrientedSphere.row (s i)

/-- The curvature–centre matrix of a family of oriented spheres and hyperplanes: the augmented matrix
with its first column deleted (LMW (3.3)–(3.4)). -/
noncomputable def curvatureCenterMatrixOf {n : ℕ} (s : Fin (n + 2) → OrientedSphere n) :
    Matrix (Fin (n + 2)) (Fin 1 ⊕ Fin n) ℝ :=
  Matrix.of fun i => Sum.elim ![OrientedSphere.row (s i) (Sum.inl 1)]
    (fun k => OrientedSphere.row (s i) (Sum.inr k))

/-- The `k`-th generator of the `n`-dimensional Apollonian group, GLMWY III (4.1):
`Sₖ = I + (2/(n−1)) eₖ 𝟙ᵀ − (2n/(n−1)) eₖ eₖᵀ`. It replaces row `k` of a matrix by
`(2/(n−1)) Σ_{i ≠ k} (row i) − (row k)` and fixes the other rows. -/
noncomputable def apollonianGen (n : ℕ) (k : Fin (n + 2)) : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ :=
  1 + (2 / ((n : ℝ) - 1)) • Matrix.vecMulVec (Pi.single k 1) (fun _ => 1) -
    (2 * n / ((n : ℝ) - 1)) • Matrix.vecMulVec (Pi.single k 1) (Pi.single k 1)

end AugmentedDescartes
