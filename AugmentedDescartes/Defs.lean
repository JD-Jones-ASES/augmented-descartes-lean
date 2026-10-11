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

/-- LMW (3.9): the coordinates `(b̄, 0, h)` of the oriented hyperplane `⟪h, y⟫ = δ` with unit normal `h`, where
`b̄ = 2δ` is the curvature of its inversion in the unit sphere (GLMWY I, p. 8: twice the distance from the
origin), the interior being the side `⟪h, y⟫ > δ` into which `h` points (GLMWY III, p. 7). -/
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

/-- Oriented tangency pair by pair (the pairwise form of LMW's oriented Descartes configurations; GLMWY III,
arXiv v2, Definition 2.1): two spheres `dist (x, y)² = (r + s)²`; a sphere `(x, r)` and a hyperplane `(h, δ)`:
`⟪h, x⟫ − δ = −r`; two hyperplanes: opposite unit normals. -/
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

/-- The augmented-coordinate matrix of the Euclidean motion `x ↦ x O + t`
in row-vector convention. Its block form is
`[[1, 0, 0], [t·t, 1, t], [2 O t, 0, O]]`.
When `Oᵀ O = I`, this rotates or reflects and translates spheres and hyperplanes. -/
noncomputable def rigidMotionMatrix {n : ℕ} (O : Matrix (Fin n) (Fin n) ℝ)
    (t : Fin n → ℝ) : Matrix (Fin 2 ⊕ Fin n) (Fin 2 ⊕ Fin n) ℝ :=
  Matrix.fromBlocks !![1, 0; t ⬝ᵥ t, 1]
    (Matrix.of fun i k => ![0, t k] i) (Matrix.of fun k j => ![2 * (O *ᵥ t) k, 0] j) O

/-- The Euclidean point map encoded by `rigidMotionMatrix`. -/
noncomputable def rigidMotionPoint {n : ℕ} (O : Matrix (Fin n) (Fin n) ℝ)
    (t : Fin n → ℝ) (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 ((fun k => x k) ᵥ* O + t)

/-- The Euclidean action on oriented objects: the motion moves sphere centres and hyperplane normals, keeps
signed radii, and shifts hyperplane offsets. -/
noncomputable def rigidMotionOf {n : ℕ} (O : Matrix (Fin n) (Fin n) ℝ)
    (t : Fin n → ℝ) : OrientedSphere n → OrientedSphere n :=
  Sum.elim (fun p => Sum.inl (rigidMotionPoint O t p.1, p.2))
    (fun p => Sum.inr (rigidMotionPoint O 0 p.1,
      p.2 + ((fun k => p.1 k) ᵥ* O) ⬝ᵥ t))

/-- The signed power polynomial of an augmented row. Its negative set is the oriented interior: a ball for a
positive-radius sphere, an exterior for a negative-radius sphere, and the half-space into which the unit normal
points for a hyperplane. -/
noncomputable def rowPower {n : ℕ} (w : Fin 2 ⊕ Fin n → ℝ)
    (y : EuclideanSpace ℝ (Fin n)) : ℝ :=
  w (Sum.inl 1) * ‖y‖ ^ 2 - 2 * ∑ k, w (Sum.inr k) * y k + w (Sum.inl 0)

end AugmentedDescartes
