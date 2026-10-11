module

public import Mathlib

/-!
# The augmented Descartes theorem in every dimension: the matrix identity, its converse, the converses
of the Soddy–Gosset and curvature–centre theorems, and Soddy's two spheres, by the Lorentz form

J. C. Lagarias, C. L. Mallows, A. R. Wilks, *Beyond the Descartes circle theorem*, Amer. Math. Monthly 109
(2002) 338–361 (arXiv:math/0101066), Section 3. An oriented sphere in `ℝⁿ` with centre `x` and signed
radius `r ≠ 0` has curvature `b = 1/r`, co-curvature `b̄ = ‖x‖²/r − r` (the curvature of its inversion in the
unit sphere) and augmented curvature–centre coordinates `(b̄, b, b x)` (Definition 3.2); an oriented hyperplane
`⟪h, y⟫ = δ` with unit normal `h` has coordinates `(2δ, 0, h)` ((3.9): the inversion of the hyperplane is a
sphere of curvature `2δ`). For `n + 2` mutually tangent oriented spheres the augmented matrix `W` with these
rows satisfies `Wᵀ Qₙ W = [[0, −4, 0], [−4, 0, 0], [0, 0, 2 Iₙ]]` with `Qₙ = I − (1/n) 𝟙𝟙ᵀ` (Theorem 3.3),
and every real solution `W` is the augmented matrix of a unique configuration (its converse). The
Soddy–Gosset relation `(Σ bᵢ)² = n Σ bᵢ²` is the `(b, b)` entry (Theorem 1.2, (1.2); Theorem 3.1 is its
converse), the curvature–centre identity `Mᵀ Qₙ M = diag(0, 2 Iₙ)` is the identity with the first row and
column deleted (Theorem 3.2), and at `n = 2` the complex Descartes theorem `(Σ bᵢ zᵢ)² = 2 Σ (bᵢ zᵢ)²` is its
centre block (Theorem 2.1).

Tangency is by signed distances, LMW's oriented tangency pair by pair: two spheres `dist (x, y)² = (r + s)²`
(external tangency for two positive radii, internal when one radius is negative); a sphere and a hyperplane
`⟪h, x⟫ − δ = −r` (the hyperplane's interior is the side `⟪h, y⟫ > δ`, into which `h` points); two
hyperplanes `h' = −h` (tangent at infinity). The disjoint-interiors property of an oriented Descartes
configuration is not formalized: the converses deliver tangency in this sense. Everything holds for `n ≥ 1`;
LMW's Section 3 assumes `n ≥ 2`, and their Section 8, (8.4), states the identity on the line with the same
target under its own convention for the infinite interval.

The development runs LMW's Section 4 argument (Lemmas 4.3–4.4, (4.9)–(4.10)) directly in Euclidean
coordinates: with `G = [[0, −½, 0], [−½, 0, 0], [0, 0, Iₙ]]` (the inverse of half the target, not the
change-of-coordinates matrix `G` of their (5.1)), the rows of `W` have Gram matrix `W G Wᵀ = 2I − J` exactly
when each row has Lorentz norm `1` and each pair pairs to `−1`, and the sphere and hyperplane rows pair to
`−1` exactly when they are tangent; `Wᵀ Qₙ W = 2 G⁻¹` is then `(2I − J)(Qₙ/2) = I` read backwards. Also
proved here: the existence half of the converse of the Soddy–Gosset theorem, LMW's Theorem 3.1 (every
nonzero `b` with `(Σ bᵢ)² = n Σ bᵢ²` is the curvature vector of a configuration; LMW: "We do not know an easy
proof of this result; a proof appears in [16]", [16] being Graham–Lagarias–Mallows–Wilks–Yan, *Apollonian
circle packings: geometry and group theory III*, whose arXiv versions 1–2 prove both halves as their Theorem
2.2 from the same base configuration and the transitivity of the Lorentz group, a section the published
version omits), by one `Qₙ`-reflection from that configuration (GLMWY III, Theorem 6.1); the converse of
Theorem 3.2 in every dimension under the hypothesis of a nonzero first column (GLMWY I, Theorem 3.1 and its
Remark, prove it at `n = 2` with that hypothesis; LMW's printed converse and GLMWY III's Theorem 2.3 omit it,
and the matrix at `n = 2` with columns `0, e₀ − e₁, e₂ − e₃`, GLMWY I's configuration (3.15) with its first
column zeroed, solves the equation and is no configuration); Soddy's two spheres in every dimension `n ≥ 2`, in the signed sense (LMW
footnote 3; GLMWY III §4.1): the oriented spheres and hyperplanes tangent to `n + 1` members of a
configuration are exactly the missing one and its Apollonian reflection, with `b + b' = (2/(n − 1)) Σ bᵢ`,
the Apollonian generators of GLMWY III (4.1) preserving `Qₙ`; the existence of a configuration in every
dimension (GLMWY III, Theorem 6.1); `det Qₙ = −2/n` (GLMWY III, (6.4) in the proof of Lemma 6.4); and the three statements in
Mathlib's vocabulary (`EuclideanGeometry.Sphere.IsExtTangent`, `IsIntTangent`). The congruence half of
Theorem 3.1's converse is not formalized.

`Solution.lean` proves every statement, kernel-only. The definitions are fully specified here.
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

/-! ## The encoding: Lorentz pairings of rows -/

/-- A sphere row has Lorentz norm `1`. -/
theorem lorentz_sphereRow_self {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) (r : ℝ) (hr : r ≠ 0) :
    lorentz (sphereRow x r) (sphereRow x r) = 1 := sorry

/-- Two sphere rows pair to `−1` exactly when the spheres are tangent in the signed sense. -/
theorem lorentz_sphereRow_eq_neg_one_iff {n : ℕ} (x y : EuclideanSpace ℝ (Fin n)) (r s : ℝ)
    (hr : r ≠ 0) (hs : s ≠ 0) :
    lorentz (sphereRow x r) (sphereRow y s) = -1 ↔ dist x y ^ 2 = (r + s) ^ 2 := sorry

/-- A sphere row and a hyperplane row pair to `−1` exactly when `⟪h, x⟫ − δ = −r`. -/
theorem lorentz_sphereRow_planeRow_eq_neg_one_iff {n : ℕ} (x h : EuclideanSpace ℝ (Fin n)) (r δ : ℝ)
    (hr : r ≠ 0) :
    lorentz (sphereRow x r) (planeRow h δ) = -1 ↔ inner ℝ h x - δ = -r := sorry

/-- Two unit-normal hyperplane rows pair to `−1` exactly when the normals are opposite. -/
theorem lorentz_planeRow_eq_neg_one_iff {n : ℕ} (h k : EuclideanSpace ℝ (Fin n)) (δ ε : ℝ)
    (hh : ‖h‖ = 1) (hk : ‖k‖ = 1) :
    lorentz (planeRow h δ) (planeRow k ε) = -1 ↔ k = -h := sorry

/-- A valid oriented sphere or hyperplane has a row of Lorentz norm `1`. -/
theorem lorentz_row_self {n : ℕ} (s : OrientedSphere n) (hs : OrientedSphere.IsValid s) :
    lorentz (OrientedSphere.row s) (OrientedSphere.row s) = 1 := sorry

/-- Two valid oriented spheres or hyperplanes pair to `−1` exactly when they are tangent. -/
theorem lorentz_row_eq_neg_one_iff {n : ℕ} (s t : OrientedSphere n) (hs : OrientedSphere.IsValid s)
    (ht : OrientedSphere.IsValid t) :
    lorentz (OrientedSphere.row s) (OrientedSphere.row t) = -1 ↔ OrientedSphere.Tangent s t := sorry

/-- Augmented coordinates are a global coordinate system (LMW, after (3.9)): valid oriented spheres
and hyperplanes with the same row are equal. -/
theorem row_injOn_valid {n : ℕ} (s t : OrientedSphere n) (hs : OrientedSphere.IsValid s)
    (ht : OrientedSphere.IsValid t) (h : OrientedSphere.row s = OrientedSphere.row t) : s = t := sorry

/-- Every row of Lorentz norm `1` is the row of a valid oriented sphere (second coordinate nonzero) or
hyperplane (second coordinate zero). -/
theorem exists_orientedSphere_of_lorentz_self {n : ℕ} (w : Fin 2 ⊕ Fin n → ℝ) (hw : lorentz w w = 1) :
    ∃ s : OrientedSphere n, OrientedSphere.IsValid s ∧ OrientedSphere.row s = w := sorry

/-! ## The matrix identity and its Lorentz form -/

/-- `Wᵀ Qₙ W` is the target exactly when the rows of `W` have Lorentz norm `1` and pair to `−1`. -/
theorem augmented_identity_iff_lorentz {n : ℕ} (hn : 0 < n) (W : Matrix (Fin (n + 2)) (Fin 2 ⊕ Fin n) ℝ) :
    Wᵀ * descartesQ n * W = augmentedTarget n ↔
      (∀ i, lorentz (W i) (W i) = 1) ∧ ∀ i j, i ≠ j → lorentz (W i) (W j) = -1 := sorry

/-- The Gram form of the identity: `W G Wᵀ = 2I − J`. -/
theorem gram_eq_of_augmented_identity {n : ℕ} (hn : 0 < n) (W : Matrix (Fin (n + 2)) (Fin 2 ⊕ Fin n) ℝ)
    (hW : Wᵀ * descartesQ n * W = augmentedTarget n) :
    W * lorentzG n * Wᵀ = 2 • (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ) - Matrix.of (fun _ _ => 1) := sorry

/-- The augmented Euclidean Descartes theorem (LMW Theorem 3.3; (8.4) at `n = 1`) for spheres of nonzero
curvature: `Wᵀ Qₙ W = [[0, −4, 0], [−4, 0, 0], [0, 0, 2 Iₙ]]`. -/
theorem augmented_descartes {n : ℕ} (hn : 0 < n) (x : Fin (n + 2) → EuclideanSpace ℝ (Fin n))
    (r : Fin (n + 2) → ℝ) (h : PairwiseTangent x r) :
    (augmentedMatrix x r)ᵀ * descartesQ n * augmentedMatrix x r = augmentedTarget n := sorry

/-- The augmented Euclidean Descartes theorem (LMW Theorem 3.3) for spheres and hyperplanes. -/
theorem augmented_descartes_general {n : ℕ} (hn : 0 < n) (s : Fin (n + 2) → OrientedSphere n)
    (hv : ∀ i, OrientedSphere.IsValid (s i))
    (ht : ∀ i j, i ≠ j → OrientedSphere.Tangent (s i) (s j)) :
    (augmentedMatrixOf s)ᵀ * descartesQ n * augmentedMatrixOf s = augmentedTarget n := sorry

/-- The converse of LMW Theorem 3.3 (spheres and hyperplanes): every real solution is the augmented matrix
of exactly one family of valid, pairwise tangent oriented spheres and hyperplanes (tangency in the
signed-distance sense; disjoint interiors not asserted). -/
theorem augmented_descartes_converse {n : ℕ} (hn : 0 < n) (W : Matrix (Fin (n + 2)) (Fin 2 ⊕ Fin n) ℝ)
    (hW : Wᵀ * descartesQ n * W = augmentedTarget n) :
    ∃! s : Fin (n + 2) → OrientedSphere n, (∀ i, OrientedSphere.IsValid (s i)) ∧
      (∀ i j, i ≠ j → OrientedSphere.Tangent (s i) (s j)) ∧ augmentedMatrixOf s = W := sorry

/-- The converse for spheres: a solution whose second column has no zero is the augmented matrix of
exactly one pairwise tangent family of spheres, `rᵢ = 1 / W i (Sum.inl 1)` and
`xᵢ k = W i (Sum.inr k) / W i (Sum.inl 1)` (tangency in the signed-distance sense). -/
theorem augmented_descartes_converse_spheres {n : ℕ} (hn : 0 < n)
    (W : Matrix (Fin (n + 2)) (Fin 2 ⊕ Fin n) ℝ) (hW : Wᵀ * descartesQ n * W = augmentedTarget n)
    (hb : ∀ i, W i (Sum.inl 1) ≠ 0) :
    ∃! p : (Fin (n + 2) → EuclideanSpace ℝ (Fin n)) × (Fin (n + 2) → ℝ),
      PairwiseTangent p.1 p.2 ∧ augmentedMatrix p.1 p.2 = W := sorry

/-! ## Corollaries: Soddy–Gosset, the curvature–centre identity, the complex Descartes theorem -/

/-- The Soddy–Gosset theorem (LMW Theorem 1.2, (1.2); Soddy 1936, Gosset 1937, Lachlan 1886 at `n = 3`):
`(Σ 1/rᵢ)² = n Σ (1/rᵢ)²`. -/
theorem soddy_gosset {n : ℕ} (hn : 0 < n) (x : Fin (n + 2) → EuclideanSpace ℝ (Fin n))
    (r : Fin (n + 2) → ℝ) (h : PairwiseTangent x r) :
    (∑ i, 1 / r i) ^ 2 = n * ∑ i, (1 / r i) ^ 2 := sorry

/-- The Soddy–Gosset theorem for spheres and hyperplanes (curvature `0` for a hyperplane). -/
theorem soddy_gosset_general {n : ℕ} (hn : 0 < n) (s : Fin (n + 2) → OrientedSphere n)
    (hv : ∀ i, OrientedSphere.IsValid (s i))
    (ht : ∀ i j, i ≠ j → OrientedSphere.Tangent (s i) (s j)) :
    (∑ i, OrientedSphere.curvature (s i)) ^ 2 = n * ∑ i, OrientedSphere.curvature (s i) ^ 2 := sorry

/-- The Soddy–Gosset relation is the vanishing of the Descartes form: `(Σ bᵢ)² = n Σ bᵢ² ↔ bᵀ Qₙ b = 0`. -/
theorem soddy_gosset_iff_isotropic {n : ℕ} (hn : 0 < n) (b : Fin (n + 2) → ℝ) :
    (∑ i, b i) ^ 2 = n * ∑ i, b i ^ 2 ↔ b ⬝ᵥ (descartesQ n *ᵥ b) = 0 := sorry

/-- The Euclidean generalized Descartes theorem (LMW Theorem 3.2, (3.5)) for spheres:
`Mᵀ Qₙ M = diag(0, 2 Iₙ)`. -/
theorem curvature_center {n : ℕ} (hn : 0 < n) (x : Fin (n + 2) → EuclideanSpace ℝ (Fin n))
    (r : Fin (n + 2) → ℝ) (h : PairwiseTangent x r) :
    (curvatureCenterMatrix x r)ᵀ * descartesQ n * curvatureCenterMatrix x r =
      curvatureCenterTarget n := sorry

/-- LMW Theorem 3.2 for spheres and hyperplanes. -/
theorem curvature_center_general {n : ℕ} (hn : 0 < n) (s : Fin (n + 2) → OrientedSphere n)
    (hv : ∀ i, OrientedSphere.IsValid (s i))
    (ht : ∀ i j, i ≠ j → OrientedSphere.Tangent (s i) (s j)) :
    (curvatureCenterMatrixOf s)ᵀ * descartesQ n * curvatureCenterMatrixOf s =
      curvatureCenterTarget n := sorry

/-- The complex Descartes theorem (LMW Theorem 2.1, (2.2)) for four circles of nonzero curvature:
with `zᵢ = xᵢ + i yᵢ`, `(Σ bᵢ zᵢ)² = 2 Σ (bᵢ zᵢ)²`. -/
theorem complex_descartes (x : Fin (2 + 2) → EuclideanSpace ℝ (Fin 2)) (r : Fin (2 + 2) → ℝ)
    (h : PairwiseTangent x r) :
    (∑ i, ((x i 0 : ℂ) + (x i 1 : ℂ) * Complex.I) / r i) ^ 2 =
      2 * ∑ i, (((x i 0 : ℂ) + (x i 1 : ℂ) * Complex.I) / r i) ^ 2 := sorry

/-- LMW (2.3): `Σ bᵢ (bᵢ zᵢ) = ½ (Σ bᵢ)(Σ bᵢ zᵢ)`. -/
theorem complex_descartes_mixed (x : Fin (2 + 2) → EuclideanSpace ℝ (Fin 2)) (r : Fin (2 + 2) → ℝ)
    (h : PairwiseTangent x r) :
    ∑ i, (1 / r i : ℂ) * (((x i 0 : ℂ) + (x i 1 : ℂ) * Complex.I) / r i) =
      (1 / 2) * (∑ i, (1 / r i : ℂ)) * ∑ i, ((x i 0 : ℂ) + (x i 1 : ℂ) * Complex.I) / r i := sorry

/-- `det Qₙ = −2/n` (GLMWY III, (6.4) in the proof of Lemma 6.4). -/
theorem det_descartesQ (n : ℕ) (hn : 0 < n) : (descartesQ n).det = -2 / n := sorry

/-! ## Mathlib's spheres -/

/-- Soddy–Gosset for Mathlib's spheres: `n + 2` spheres of positive radius, pairwise externally tangent
(LMW's case (i); at `n = 1` the hypotheses cannot be met, three pairwise externally tangent intervals forcing
a zero radius). -/
theorem sphere_soddy_gosset {n : ℕ} (hn : 0 < n)
    (s : Fin (n + 2) → EuclideanGeometry.Sphere (EuclideanSpace ℝ (Fin n)))
    (hr : ∀ i, 0 < (s i).radius)
    (ht : ∀ i j, i ≠ j → EuclideanGeometry.Sphere.IsExtTangent (s i) (s j)) :
    (∑ i, 1 / (s i).radius) ^ 2 = n * ∑ i, (1 / (s i).radius) ^ 2 := sorry

/-- Soddy–Gosset with one enclosing sphere `e`, to which the others are internally tangent
(`IsIntTangent (s j) (s e)`: `s j` lies inside `s e`) and which carries the curvature `−1/rₑ` (LMW's case
(ii)). -/
theorem sphere_soddy_gosset_enclosing {n : ℕ} (hn : 0 < n)
    (s : Fin (n + 2) → EuclideanGeometry.Sphere (EuclideanSpace ℝ (Fin n))) (e : Fin (n + 2))
    (hr : ∀ i, 0 < (s i).radius)
    (hint : ∀ j, j ≠ e → EuclideanGeometry.Sphere.IsIntTangent (s j) (s e))
    (hext : ∀ i j, i ≠ e → j ≠ e → i ≠ j → EuclideanGeometry.Sphere.IsExtTangent (s i) (s j)) :
    (∑ i, (if i = e then -1 else 1) / (s i).radius) ^ 2 =
      n * ∑ i, ((if i = e then -1 else 1) / (s i).radius) ^ 2 := sorry

/-- The augmented identity for Mathlib's spheres, pairwise externally tangent (unsatisfiable at `n = 1`). -/
theorem sphere_augmented_descartes {n : ℕ} (hn : 0 < n)
    (s : Fin (n + 2) → EuclideanGeometry.Sphere (EuclideanSpace ℝ (Fin n)))
    (hr : ∀ i, 0 < (s i).radius)
    (ht : ∀ i j, i ≠ j → EuclideanGeometry.Sphere.IsExtTangent (s i) (s j)) :
    (augmentedMatrix (fun i => (s i).center) (fun i => (s i).radius))ᵀ * descartesQ n *
      augmentedMatrix (fun i => (s i).center) (fun i => (s i).radius) = augmentedTarget n := sorry

/-! ## Beyond LMW: the two converses they leave unproved -/

/-- Existence of a configuration in every dimension: two parallel hyperplanes at distance `2` and `n`
unit spheres centred at `√2 eᵢ` (the configuration of GLMWY III, Theorem 6.1, stated there for `n ≥ 2`; at
`n = 1` the hyperplanes are oriented points). -/
theorem exists_configuration (n : ℕ) (hn : 0 < n) :
    ∃ s : Fin (n + 2) → OrientedSphere n, (∀ i, OrientedSphere.IsValid (s i)) ∧
      ∀ i j, i ≠ j → OrientedSphere.Tangent (s i) (s j) := sorry

/-- Existence of a pairwise tangent family of spheres in every dimension. -/
theorem exists_pairwiseTangent (n : ℕ) (hn : 0 < n) :
    ∃ x : Fin (n + 2) → EuclideanSpace ℝ (Fin n), ∃ r : Fin (n + 2) → ℝ, PairwiseTangent x r := sorry

/-- The existence half of the converse of the Soddy–Gosset theorem (LMW Theorem 3.1, which LMW state with
"We do not know an easy proof of this result; a proof appears in [16]"; GLMWY III's arXiv versions 1–2 prove
it as their Theorem 2.2 by the same route): every nonzero `b` with
`(Σ bᵢ)² = n Σ bᵢ²` is the curvature vector of a pairwise tangent family of valid oriented spheres
(`bᵢ ≠ 0`) and hyperplanes (`bᵢ = 0`), tangency in the signed-distance sense; the congruence half is not
formalized. -/
theorem converse_soddy_gosset {n : ℕ} (hn : 0 < n) (b : Fin (n + 2) → ℝ) (hb : b ≠ 0)
    (h : (∑ i, b i) ^ 2 = n * ∑ i, b i ^ 2) :
    ∃ s : Fin (n + 2) → OrientedSphere n, (∀ i, OrientedSphere.IsValid (s i)) ∧
      (∀ i j, i ≠ j → OrientedSphere.Tangent (s i) (s j)) ∧
      ∀ i, OrientedSphere.curvature (s i) = b i := sorry

/-- The existence half of the converse of the Soddy–Gosset theorem for spheres: every `b` with no zero
entry and `(Σ bᵢ)² = n Σ bᵢ²` is the curvature vector of a pairwise tangent family of spheres (tangency in
the signed-distance sense). -/
theorem converse_soddy_gosset_spheres {n : ℕ} (hn : 0 < n) (b : Fin (n + 2) → ℝ) (hb : ∀ i, b i ≠ 0)
    (h : (∑ i, b i) ^ 2 = n * ∑ i, b i ^ 2) :
    ∃ x : Fin (n + 2) → EuclideanSpace ℝ (Fin n), ∃ r : Fin (n + 2) → ℝ,
      PairwiseTangent x r ∧ ∀ i, 1 / r i = b i := sorry

/-- The converse of LMW Theorem 3.2 in every dimension, under the hypothesis of a nonzero first column
(GLMWY I, Theorem 3.1 and its Remark, state and prove it at `n = 2` with this hypothesis; LMW's printed
converse, "any real solution `M`", omits it): every real `M` with `Mᵀ Qₙ M = diag(0, 2 Iₙ)` and a nonzero
first column is the curvature–centre matrix of exactly one family of valid, pairwise tangent oriented spheres
and hyperplanes (tangency in the signed-distance sense). -/
theorem curvature_center_converse {n : ℕ} (hn : 0 < n) (M : Matrix (Fin (n + 2)) (Fin 1 ⊕ Fin n) ℝ)
    (hM : Mᵀ * descartesQ n * M = curvatureCenterTarget n) (hb : ∃ i, M i (Sum.inl 0) ≠ 0) :
    ∃! s : Fin (n + 2) → OrientedSphere n, (∀ i, OrientedSphere.IsValid (s i)) ∧
      (∀ i j, i ≠ j → OrientedSphere.Tangent (s i) (s j)) ∧ curvatureCenterMatrixOf s = M := sorry

/-- The hypothesis of `curvature_center_converse` is needed (GLMWY I, the Remark after Theorem 3.1): at
`n = 2` the matrix with columns `0, e₀ − e₁, e₂ − e₃` solves the equation and is the curvature–centre matrix
of no family. -/
theorem curvature_center_converse_needs_nonzero :
    ∃ M : Matrix (Fin (2 + 2)) (Fin 1 ⊕ Fin 2) ℝ, Mᵀ * descartesQ 2 * M = curvatureCenterTarget 2 ∧
      (∀ i, M i (Sum.inl 0) = 0) ∧
      ¬ ∃ s : Fin (2 + 2) → OrientedSphere 2, (∀ i, OrientedSphere.IsValid (s i)) ∧
        (∀ i j, i ≠ j → OrientedSphere.Tangent (s i) (s j)) ∧ curvatureCenterMatrixOf s = M := sorry

/-! ## The Apollonian group and Soddy's two spheres -/

/-- The Apollonian generators preserve the Descartes form (GLMWY III, after (4.1)): `Sₖᵀ Qₙ Sₖ = Qₙ`. -/
theorem apollonianGen_mem_aut {n : ℕ} (hn : 2 ≤ n) (k : Fin (n + 2)) :
    (apollonianGen n k)ᵀ * descartesQ n * apollonianGen n k = descartesQ n := sorry

/-- Replacing sphere `k` of a configuration by its Apollonian reflection gives a configuration. -/
theorem apollonian_reflection {n : ℕ} (hn : 2 ≤ n) (W : Matrix (Fin (n + 2)) (Fin 2 ⊕ Fin n) ℝ)
    (hW : Wᵀ * descartesQ n * W = augmentedTarget n) (k : Fin (n + 2)) :
    (apollonianGen n k * W)ᵀ * descartesQ n * (apollonianGen n k * W) = augmentedTarget n := sorry

/-- The reflected row is `(2/(n−1)) Σ_{i ≠ k} (row i) − (row k)`; in particular the two curvatures
satisfy `bₖ + bₖ' = (2/(n−1)) Σ_{i ≠ k} bᵢ` and the centre columns the like relation (LMW (2.1) and (2.4) at
`n = 2`). -/
theorem apollonianGen_mul_apply {n : ℕ} (hn : 2 ≤ n) (W : Matrix (Fin (n + 2)) (Fin 2 ⊕ Fin n) ℝ)
    (k : Fin (n + 2)) (j : Fin 2 ⊕ Fin n) :
    (apollonianGen n k * W) k j = (2 / ((n : ℝ) - 1)) * ∑ i ∈ Finset.univ.erase k, W i j - W k j := sorry

/-- Soddy's two spheres in every dimension (LMW, footnote 3; GLMWY III §4.1), in the signed sense and for
the members of a configuration: the rows of Lorentz norm `1` pairing to `−1` with every row of a
configuration but the `k`-th are exactly the `k`-th row and its Apollonian reflection, which are distinct. -/
theorem two_tangent_rows {n : ℕ} (hn : 2 ≤ n) (W : Matrix (Fin (n + 2)) (Fin 2 ⊕ Fin n) ℝ)
    (hW : Wᵀ * descartesQ n * W = augmentedTarget n) (k : Fin (n + 2)) :
    (∀ w : Fin 2 ⊕ Fin n → ℝ, (lorentz w w = 1 ∧ ∀ i, i ≠ k → lorentz w (W i) = -1) ↔
      (w = W k ∨ w = (apollonianGen n k * W) k)) ∧ W k ≠ (apollonianGen n k * W) k := sorry

/-- Soddy's two spheres, geometrically (the signed count; LMW's footnote 3 counts the real spheres tangent
to any `n + 1` mutually tangent spheres with distinct tangencies): given `n + 1` members of a configuration,
exactly two valid oriented spheres or hyperplanes are tangent to all of them in the signed sense, the missing
member and one other, and their curvatures sum to `(2/(n−1)) Σ` of the others' curvatures. -/
theorem two_tangent_spheres {n : ℕ} (hn : 2 ≤ n) (s : Fin (n + 2) → OrientedSphere n)
    (hv : ∀ i, OrientedSphere.IsValid (s i))
    (ht : ∀ i j, i ≠ j → OrientedSphere.Tangent (s i) (s j)) (k : Fin (n + 2)) :
    ∃ t : OrientedSphere n, OrientedSphere.IsValid t ∧ t ≠ s k ∧
      (∀ i, i ≠ k → OrientedSphere.Tangent t (s i)) ∧
      OrientedSphere.curvature t + OrientedSphere.curvature (s k) =
        (2 / ((n : ℝ) - 1)) * ∑ i ∈ Finset.univ.erase k, OrientedSphere.curvature (s i) ∧
      ∀ u : OrientedSphere n, OrientedSphere.IsValid u → (∀ i, i ≠ k → OrientedSphere.Tangent u (s i)) →
        u = s k ∨ u = t := sorry

end AugmentedDescartes
