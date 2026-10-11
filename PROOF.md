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
   swap of the two hyperbolic columns (`σᵀ T σ = T`; `W₀ σ` is the configuration's inversion in the unit sphere). An
   isometry `U` of `Qₙ` keeps the identity. Decode; the curvatures are the second column. `exists_pairwiseTangent` at
   `n ≥ 2` from `b = (1, …, 1, 2n/(n−1), 2n(n+1)/(n−1)²)` (null: `(n+1)⁴ − (n−1)⁴ = 8n³ + 8n`); at `n = 1` from
   `b = (1, 1, −½)`.
8. **The converse of the curvature–centre theorem** (`Completion.lean`). `M = [b | V]`, `Mᵀ Qₙ M = diag(0, 2•1)`, `b ≠ 0`:
   `P := 1 − (1/2) • V * Vᵀ * Qₙ` satisfies `Vᵀ Qₙ (P u) = 0`; `⟨P u, b⟩ = ⟨u, b⟩ = (Qₙ b) ⬝ᵥ u`, so some
   `z := P *ᵥ Pi.single ℓ 1` has `⟨z, b⟩ ≠ 0` (`Qₙ b ≠ 0` since `Qₙ` is invertible); `b̄ := (−4/⟨z, b⟩) • (z − (⟨z, z⟩/(2⟨z,
   b⟩)) • b)` is null, `Qₙ`-orthogonal to `V`'s columns, pairs to `−4` with `b`; `W := [b̄ | b | V]` satisfies the identity;
   decode. Uniqueness: two completions `b̄, b̄'` give `d = b̄' − b̄` with `⟨d, b⟩ = 0`, `⟨d, V⟩ = 0`; in the basis of `W`'s
   columns `d = α b + β b̄`, `⟨d, b⟩ = −4β` forces `β = 0`, and `⟨b̄', b̄'⟩ = −8α = 0` forces `α = 0`. The matrix at
   `n = 2` with columns `0, e₀ − e₁, e₂ − e₃` solves the equation (it is the curvature–centre matrix of four oriented
   lines with normals `±e₀, ±e₁`) and no valid, pairwise tangent family has it: such a family's augmented matrix would
   satisfy the identity with `(inl 0, inl 1)` entry `⟨b̄, 0⟩ = 0 ≠ −4`.
9. **Compatible orientations** (`Orientation.lean`). Write row `i` as `(aᵢ, bᵢ, vᵢ)` and
   `Fᵢ(y) := rowPower (W i) y = bᵢ ‖y‖² − 2 vᵢ ⬝ᵥ y + aᵢ`. On a sphere row `F = (dist y x ² − r²)/r`, on a hyperplane row
   `F = 2(δ − ⟪h, y⟫)`, so `F < 0` is the open ball (`r > 0`), the open exterior of the ball of radius `−r` (`r < 0`)
   or the open half-space `⟪h, y⟫ > δ` (`F(y) = −2 lorentz (W i) (‖y‖², 1, y)`, the power of `y` with respect to the
   sphere divided by `r`; cf. the separation of GLMWY III, Definition 7.1, arXiv v1–v2 Definition 5.1). With
   `u(y) := (1, ‖y‖², −2y)`, `W *ᵥ u(y) = F(y)` and `u(y)ᵀ T u(y) = −8‖y‖² + 2·4‖y‖² = 0` (`T` the target), so
   `F(y)ᵀ Qₙ F(y) = 0`: `(Σ Fᵢ)² = n Σ Fᵢ²`. Let `A = Σ aᵢ`, `B = Σ bᵢ`, `V = Σ vᵢ`; the Gram form `W G Wᵀ = 2•1 − J`
   summed over all entries is `lorentz (Σ wᵢ) (Σ wᵢ) = −AB + ‖V‖² = 2(n + 2) − (n + 2)²`, so `AB − ‖V‖² = n(n + 2)`
   and, completing the square, `B Σ Fᵢ(y) = B²‖y‖² − 2B V ⬝ᵥ y + AB = ‖B y − V‖² + n(n + 2) > 0` (`n > 0`). Hence
   `B ≠ 0` (GLMWY III §3.1, p. 6, state this for configurations) and its sign is the orientation. Two Cauchy–Schwarz lemmas on
   a vector `z` of length `n + 2` with `(Σ z)² = n Σ z²`: (a) if `Σ z > 0` no two entries are negative, for if
   `zᵢ, zⱼ < 0` the other `n` entries sum to `S > Σ z > 0` and `S² ≤ n Σ_{k ≠ i, j} zₖ² ≤ n Σ z² = (Σ z)² < S²`; (b) if
   `Σ z ≠ 0` no three entries vanish, for the other `n − 1` entries give `(Σ z)² ≤ (n − 1) Σ z²`, so `Σ z² ≤ 0`,
   `z = 0`, `Σ z = 0`. The relation is homogeneous, so (a) applies to `z = B • F(y)`, whose sum is `B Σ Fᵢ(y) > 0`:
   the sets `{y | B Fᵢ(y) < 0}` are pairwise disjoint (`augmented_orientation`, `augmented_orientation_disjoint`);
   for `B > 0` they are the given interiors, for `B < 0` the interiors of every reversed row. (b) applied to `b`,
   null by the `(inl 1, inl 1)` entry of the identity and with `Σ b = B ≠ 0`, leaves at most two hyperplane rows
   (the four cases of GLMWY III §3.1, p. 6, and LMW's list after Theorem 3.1); applied to `F(y)`, with `Σ Fᵢ(y) ≠ 0`, it
   leaves no point `y` on three boundaries `{Fᵢ = 0}` (LMW's distinct tangencies, at finite points).
10. **Congruence** (`Rigidity.lean`). Let `W₁, W₂` satisfy the identity with the same curvature column, and let
    `e_b := Pi.single (inl 1) 1`. With `V₁ := ((1/2) • G) * W₁ᵀ * Qₙ` (item 5: `V₁ W₁ = W₁ V₁ = 1`), `H := V₁ W₂`
    satisfies `W₁ H = W₂`, `Hᵀ T H = W₂ᵀ Qₙ W₂ = T` (from `Qₙ = V₁ᵀ T V₁`) and `H e_b = V₁ (W₂ e_b) = V₁ (W₁ e_b) = e_b`.
    A matrix in the group of `T` that fixes `e_b` is a motion matrix (the little group of a null vector in the
    Lorentz group is the Euclidean group; the inclusion is computed here directly): `(Hᵀ T H) e_b = T e_b = −4 e_{b̄}` gives `Hᵀ e_{b̄} = e_{b̄}`, so
    the `inl 0` row of `H` is `(1, 0, 0)`; write the `inl 1` row `(c, 1, t)` and the spatial rows `(u, 0, O)`. Then
    the spatial–spatial entries of `Hᵀ T H = T` give `2 Oᵀ O = 2•1`, the `(inl 0, inr l)` entries
    `−4 tₗ + 2 (Oᵀ u)ₗ = 0`, so `u = 2 O t` (`O Oᵀ = 1` for a square matrix), and the `(inl 0, inl 0)` entry
    `−8c + 2‖u‖² = 0`, so `c = ‖t‖²`: `H = rigidMotionMatrix O t = [[1, 0, 0], [‖t‖², 1, t], [2 O t, 0, O]]`, the
    product of the translation and rotation matrices of GLMWY III's Theorem 9.1 (arXiv v1–v2 Theorem 3.1). Unique,
    since `W₁` is invertible and `(O, t) ↦ rigidMotionMatrix O t` is injective (`same_curvature_motion`). Reading
    `H = ((1/2) • G) W₁ᵀ Qₙ W₂` at the spatial block (`G`'s is `1`) and at the `(inl 1, inr l)` entries (`G`'s
    `inl 1` row is `(−½, 0, 0)`) gives `O = ½ X₁ᵀ Qₙ X₂` and `t = −¼ a₁ᵀ Qₙ X₂` (`rigidMotion_parameters`, from
    `W₁ H = W₂` alone). Rows are row vectors: `sphereRow x r ᵥ* H = sphereRow (x O + t) r`, since
    `‖x O + t‖² = ‖x‖² + 2 x ⬝ᵥ (O t) + ‖t‖²` when `O Oᵀ = 1` (at `r = 0` both sides are the zero row), and
    `planeRow h δ ᵥ* H = planeRow (h O) (δ + (h O) ⬝ᵥ t)` with no hypothesis on `O`; `x ↦ x O + t` is an isometry;
    `rigidMotionOf O t` keeps radii nonzero and unit normals unit, so it maps valid objects to valid objects with
    `row (rigidMotionOf O t s) = row s ᵥ* H`. For two valid, pairwise tangent families with equal curvatures the
    forward theorem gives `W₁, W₂` with one curvature column; `row_injOn_valid` turns `W₁ H = W₂` into
    `rigidMotionOf O t (s i) = s' i` for each `i`, and any motion doing so gives `W₁ (rigidMotionMatrix O' t') = W₂`,
    so `(O', t') = (O, t)` (`same_curvature_congruence`). LMW Theorem 3.1 and GLMWY III's arXiv v1–v2 Theorem 2.2 (ii) state a
    motion; GLMWY III's arXiv v1–v2 prove it by the rigidity of a simplex of centres (pp. 12–14); the uniqueness and
    the formulas are proved here.
11. **Motions on configurations** (`Motion.lean`). `rigidMotionOf` keeps validity (item 10) and curvature (by cases
    on the object); `rigidMotionMatrix O t` preserves the Lorentz pairing when `Oᵀ O = 1`: expand the three
    coordinates of `w ᵥ* H` by the row formulas of item 10 and use `(x ᵥ* O) ⬝ᵥ (y ᵥ* O) = x ⬝ᵥ y` and
    `(x ᵥ* O) ⬝ᵥ t = x ⬝ᵥ (O t)`, after which the terms in `t` cancel. So tangency of valid objects is preserved
    through item 1, and with item 10 two valid, pairwise tangent families are congruent exactly when their
    curvature vectors agree. The geometric orientation statements are item 9 for `augmentedMatrixOf s` through the
    forward theorem (item 3), the curvature column being the curvatures of `s`; for `B > 0` the factor `B` drops out
    of `{y | B F < 0}`.
