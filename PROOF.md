# The proofs

Rows are augmented curvature–centre coordinates on `Fin 2 ⊕ Fin n`: `(b̄, b, b x)` for a sphere of centre `x` and signed
radius `r` (`b = 1/r`, `b̄ = ‖x‖²/r − r`), `(2δ, 0, h)` for the hyperplane `⟪h, y⟫ = δ` with unit normal `h` (Lagarias–
Mallows–Wilks, Definition 3.2 and (3.9)). The Lorentz pairing is `lorentz u v = −(u₀ v₁ + u₁ v₀)/2 + Σ uₖ vₖ = u ⬝ᵥ (G *ᵥ v)`
with `G = [[0, −½, 0], [−½, 0, 0], [0, 0, Iₙ]]`. The proofs run LMW's Section 4 argument (Lemmas 4.3–4.4, (4.9)–(4.10))
directly in Euclidean coordinates.

1. **Encoding** (`AugmentedDescartes/Rows.lean`). `lorentz (sphereRow x r) (sphereRow y s) = (r² + s² − dist x y ²)/(2rs)`:
   norm `1` on the diagonal, `−1` iff `dist² = (r + s)²`. `lorentz (sphereRow x r) (planeRow h δ) = (⟪h, x⟫ − δ)/r`: `−1`
   iff `⟪h, x⟫ − δ = −r`. `lorentz (planeRow h δ) (planeRow k ε) = ⟪h, k⟫`: norm `‖h‖²`, `−1` iff `k = −h` for unit normals
   (`‖h + k‖² = 2 + 2⟪h, k⟫`). A row of norm `1` decodes: `b ≠ 0` gives the sphere `(v/b, 1/b)`, `b = 0` gives `‖v‖ = 1`
   and the hyperplane `(v, b̄/2)`; valid objects with equal rows are equal.
2. **The matrix identity** (`Lorentz.lean`). `(W * G * Wᵀ) i j = lorentz (W i) (W j)`; `(2•1 − J)((1/2) • Qₙ) = 1`;
   `Qₙ (1 − (1/2) • J) = 1`; `G⁻¹ = [[0, −2, 0], [−2, 0, 0], [0, 0, Iₙ]]` and the target is `2 • G⁻¹`. Forward: rows of norm
   `1` pairing to `−1` give `W G Wᵀ = 2•1 − J`, so `W (G Wᵀ ((1/2) • Qₙ)) = 1`; `Matrix.mul_eq_one_comm_of_equiv` (with
   `finSumFinEquiv` and `finCongr`) gives `(G Wᵀ ((1/2) • Qₙ)) W = 1`, so `G Wᵀ Qₙ W = 2•1` and `Wᵀ Qₙ W = 2 • G⁻¹`.
   Backward: `((1/2) • G) Wᵀ Qₙ W = 1`, swap, `W G Wᵀ Qₙ = 2•1`, multiply by `Qₙ⁻¹`. This is
   `augmented_identity_iff_lorentz`; everything else reads entries. `det Qₙ = −2/n` by the matrix determinant lemma
   (`Qₙ = 1 + col(−𝟙/n) row(𝟙)`).
3. **Forward theorems** (`Main.lean`, `Corollaries.lean`). A family's rows are valid and pairwise tangent, so the identity
   holds; Soddy–Gosset is the `(inl 1, inl 1)` entry (`Σ bᵢ² − (1/n)(Σ bᵢ)² = 0`); the curvature–centre identity is the
   identity with the first row and column deleted; the complex Descartes theorem reads the three centre entries at
   `n = 2` through `Complex.ext`. The Mathlib statements use `EuclideanGeometry.Sphere.IsExtTangent.dist_center` and
   `IsIntTangent.dist_center` (`dist s₁ s₂ = s₂.radius − s₁.radius`, `s₁` inside `s₂`).
4. **Converse** (`Converse.lean`). From the identity the rows have norm `1` and pair to `−1`; decode each row; tangency is
   the pairing; uniqueness by the injectivity of rows on valid objects.
5. **Apollonian** (`Apollonian.lean`). `Sₖ = 1 + (2/(n−1)) • vecMulVec (Pi.single k 1) 1 − (2n/(n−1)) • vecMulVec
   (Pi.single k 1) (Pi.single k 1)` (GLMWY III (4.1)); `(Sₖ W) k = (2/(n−1)) Σ_{i ≠ k} W i − W k`, other rows fixed;
   `Sₖᵀ Qₙ Sₖ = Qₙ` entrywise (`n ≥ 2`). Two spheres: with `V := ((1/2) • G) * Wᵀ * Qₙ`, `V * W = 1` and `W * V = 1`, so
   a row `w` is `c ᵥ* W` with `c = w ᵥ* V`; `lorentz (c ᵥ* W) (W j) = 2 cⱼ − Σ c` and `lorentz (c ᵥ* W) (c ᵥ* W) =
   2 Σ cᵢ² − (Σ c)²` by the Gram form; the conditions force `cⱼ = c` for `j ≠ k`, `cₖ = 1 − (n−1) c`, and
   `2 n c ((n−1) c − 2) = 0`; `c = 0` is `W k`, `c = 2/(n−1)` the reflected row. Distinct because the rows are
   independent (`c ᵥ* W = 0 → c = c ᵥ* (W * V) = 0`).
6. **A configuration in every dimension** (`Base.lean`): GLMWY III Theorem 6.1's: `n` unit spheres at
   `√2 • EuclideanSpace.single i 1` and the hyperplanes `(𝟙/√n, 1 + √2/√n)`, `(−𝟙/√n, 1 − √2/√n)`; the tangency conditions
   are `dist² = 4`, `⟪h, x⟫ − δ = −1`, opposite normals; valid since `‖𝟙/√n‖ = 1`.
7. **The converse of Soddy–Gosset** (`Transitivity.lean`). The `Qₙ`-reflection `R v = 1 − (2/⟨v, v⟩) • vecMulVec v (Qₙ *ᵥ v)`
   satisfies `Rᵀ Qₙ R = Qₙ` when `⟨v, v⟩ ≠ 0` and `R *ᵥ v = −v`; for null `b₀, b` with `⟨b₀, b⟩ ≠ 0`,
   `⟨b₀ − b, b₀ − b⟩ = −2⟨b₀, b⟩` and `R (b₀ − b) *ᵥ b₀ = b`. Given null `b ≠ 0` and the base matrix `W₀`: with
   `y := V₀ *ᵥ b`, `b = W₀ *ᵥ y` and `⟨W₀ *ᵥ eⱼ, b⟩ = (T y) j`, so `⟨b₀, b⟩ = −4 y₀` and `⟨b̄₀, b⟩ = −4 y₁`; if `y₀ ≠ 0`
   reflect `W₀`, else `y₁ ≠ 0` (else `⟨b, b⟩ = 2 Σ_{k≥2} yₖ² = 0` forces `y = 0`, `b = 0`) and reflect `W₀ σ`, `σ` the
   swap of the two hyperbolic columns (`σᵀ T σ = T`). An isometry `U` of `Qₙ` keeps the identity. Decode; the curvatures
   are the second column. `exists_pairwiseTangent` at `n ≥ 2` from `b = (1, …, 1, 2n/(n−1), 2n(n+1)/(n−1)²)` (null:
   `(n+1)⁴ − (n−1)⁴ = 8n³ + 8n`); at `n = 1` the intervals with centres `1, 3, 2` and radii `1, 1, −2`.
8. **The converse of the curvature–centre theorem** (`Completion.lean`). `M = [b | V]`, `Mᵀ Qₙ M = diag(0, 2•1)`, `b ≠ 0`:
   `P := 1 − (1/2) • V * Vᵀ * Qₙ` satisfies `Vᵀ Qₙ (P u) = 0`; `⟨P u, b⟩ = ⟨u, b⟩ = (Qₙ b) ⬝ᵥ u`, so some
   `z := P *ᵥ Pi.single ℓ 1` has `⟨z, b⟩ ≠ 0` (`Qₙ b ≠ 0` since `Qₙ` is invertible); `b̄ := (−4/⟨z, b⟩) • (z − (⟨z, z⟩/(2⟨z,
   b⟩)) • b)` is null, `Qₙ`-orthogonal to `V`'s columns, pairs to `−4` with `b`; `W := [b̄ | b | V]` satisfies the identity;
   decode. Uniqueness: two completions `b̄, b̄'` give `d = b̄' − b̄` with `⟨d, b⟩ = 0`, `⟨d, V⟩ = 0`; in the basis of `W`'s
   columns `d = α b + β b̄`, `β = 0`, and `⟨b̄', b⟩ = −4` forces `α = 0`. The counterexample at `n = 2`: columns
   `0, e₀ − e₁, e₂ − e₃`; any family's augmented matrix would have `(inl 0, inl 1)` entry `⟨b̄, 0⟩ = 0 ≠ −4`.
