# Architecture

The augmented Descartes theorem in every dimension (Lagarias–Mallows–Wilks, *Beyond the Descartes circle theorem*,
AMM 109 (2002), arXiv:math/0101066, §3), its converses, and Soddy's two spheres, on Lean `v4.35.0-rc2` + Mathlib
`v4.35.0-rc2`. `Challenge.lean` pins the definitions and the statements; `AugmentedDescartes/Defs.lean` restates the
definitions character for character; the modules below prove the theorems under the names of the Challenge with the
suffix `_internal`; `Solution.lean` restates each Challenge theorem and closes it by its `_internal` twin. The desk's
exact replay of every step is the bench's `probe.py` (176 checks).

## The mathematics

Rows are augmented curvature–centre coordinates on `Fin 2 ⊕ Fin n`: `(b̄, b, b x)` for a sphere of centre `x` and signed
radius `r` (`b = 1/r`, `b̄ = ‖x‖²/r − r`), `(2δ, 0, h)` for the hyperplane `⟪h, y⟫ = δ`, `‖h‖ = 1`. The Lorentz pairing
`lorentz u v = −(u₀ v₁ + u₁ v₀)/2 + Σ uₖ vₖ = u ⬝ᵥ (G *ᵥ v)` with `G = fromBlocks !![0, -1/2; -1/2, 0] 0 0 1`.

1. **Encoding** (`Rows`). `lorentz (sphereRow x r) (sphereRow y s) = (r² + s² − dist x y ²)/(2 r s)`: norm `1` on the
   diagonal, `−1` iff `dist² = (r + s)²`. `lorentz (sphereRow x r) (planeRow h δ) = (⟪h, x⟫ − δ)/r`: `−1` iff
   `⟪h, x⟫ − δ = −r`. `lorentz (planeRow h δ) (planeRow k ε) = ⟪h, k⟫`: norm `‖h‖²`, `−1` iff `k = −h` for unit normals
   (`‖h + k‖² = 2 + 2⟪h, k⟫`). A row of norm `1` decodes: `b ≠ 0` gives the sphere `(v/b, 1/b)`, `b = 0` gives
   `‖v‖ = 1` and the hyperplane `(v, b̄/2)`; valid objects with equal rows are equal.
2. **The matrix identity** (`Lorentz`). `(W * G * Wᵀ) i j = lorentz (W i) (W j)`. `(2•1 − J)((1/2) • Qₙ) = 1`,
   `Qₙ (1 − (1/2) • J) = 1`, `G⁻¹ = fromBlocks !![0, -2; -2, 0] 0 0 1`, `augmentedTarget n = 2 • G⁻¹`,
   `augmentedTarget n * ((1/2) • G) = 1`. Forward: rows of norm `1` pairing to `−1` give `W G Wᵀ = 2•1 − J`, so
   `W (G Wᵀ ((1/2) • Qₙ)) = 1`; `Matrix.mul_eq_one_comm_of_equiv` (with `finSumFinEquiv` and `finCongr`) gives
   `(G Wᵀ ((1/2) • Qₙ)) W = 1`, so `G Wᵀ Qₙ W = 2•1` and `Wᵀ Qₙ W = 2 • G⁻¹`. Backward: `((1/2) • G) Wᵀ Qₙ W = 1`, swap,
   `W G Wᵀ Qₙ = 2•1`, multiply by `Qₙ⁻¹`. This is `augmented_identity_iff_lorentz`; everything else reads entries.
   `det Qₙ = −2/n` by `Matrix.det_one_add_replicateCol_mul_replicateRow` (`Qₙ = 1 + col(−𝟙/n) row(𝟙)`).
3. **Forward theorems** (`Main`): the family's rows are valid and pairwise tangent, so the identity holds; Soddy–Gosset is
   the `(inl 1, inl 1)` entry (`Σ bᵢ² − (1/n)(Σ bᵢ)² = 0`); the curvature–centre identity is the identity with the first
   row and column deleted; the complex Descartes theorem reads the three centre entries at `n = 2` through `Complex.ext`.
   The Mathlib bridge (`Corollaries`) uses `EuclideanGeometry.Sphere.IsExtTangent.dist_center` and
   `IsIntTangent.dist_center` (`dist s₁ s₂ = s₂.radius − s₁.radius`, `s₁` inside `s₂`).
4. **Converse** (`Converse`): from the identity, the rows have norm `1` and pair to `−1`; decode each row; tangency is the
   pairing; uniqueness by `row_injOn_valid`.
5. **Apollonian** (`Apollonian`): `Sₖ = 1 + (2/(n−1)) • vecMulVec (Pi.single k 1) 1 − (2n/(n−1)) • vecMulVec (Pi.single k 1)
   (Pi.single k 1)`; `(Sₖ W) k = (2/(n−1)) Σ_{i ≠ k} W i − W k`, other rows fixed; `Sₖᵀ Qₙ Sₖ = Qₙ` entrywise
   (`Sₖ` changes only row `k`; `n ≥ 2`). Two spheres: with `V := ((1/2) • G) * Wᵀ * Qₙ`, `V * W = 1` and `W * V = 1`
   (from `Lorentz`), so a row `w` is `c ᵥ* W` with `c = w ᵥ* V`; `lorentz (c ᵥ* W) (W j) = 2 cⱼ − Σ c` and
   `lorentz (c ᵥ* W) (c ᵥ* W) = 2 Σ cᵢ² − (Σ c)²` by the Gram form; the conditions force `cⱼ = c` for `j ≠ k`,
   `cₖ = 1 − (n−1) c`, and `2 n c ((n−1) c − 2) = 0`; `c = 0` is `W k`, `c = 2/(n−1)` the reflected row. Distinct because
   the rows are independent (`c ᵥ* W = 0 → c = c ᵥ* (W * V) = 0`).
6. **Base** (`Base`): the strip configuration of GLMWY III Theorem 6.1: `n` unit spheres at `√2 • EuclideanSpace.single i 1`
   and the hyperplanes `(𝟙/√n, 1 + √2/√n)`, `(−𝟙/√n, 1 − √2/√n)`; the tangency conditions are the three geometric
   identities (`dist² = 4`, `⟪h, x⟫ − δ = −1`, opposite normals); valid since `‖𝟙/√n‖ = 1`.
7. **Transitivity** (`Transitivity`): the `Qₙ`-reflection `R v = 1 − (2/⟨v, v⟩) • vecMulVec v (Qₙ *ᵥ v)` satisfies
   `Rᵀ Qₙ R = Qₙ` when `⟨v, v⟩ ≠ 0` and `R *ᵥ v = −v`; for null `b₀, b` with `⟨b₀, b⟩ ≠ 0`, `⟨b₀ − b, b₀ − b⟩ = −2⟨b₀, b⟩`
   and `R (b₀ − b) *ᵥ b₀ = b`. Given null `b ≠ 0` and the base `W₀` (its identity from `Base` + `Main`): with
   `y := V₀ *ᵥ b` one has `b = W₀ *ᵥ y` and `⟨W₀ *ᵥ eⱼ, b⟩ = (T y) j`, so `⟨b₀, b⟩ = −4 y₀` and `⟨b̄₀, b⟩ = −4 y₁`;
   if `y₀ ≠ 0` reflect `W₀`, else `y₁ ≠ 0` (else `⟨b, b⟩ = 2 Σ_{k≥2} yₖ² = 0` forces `y = 0`, `b = 0`) and reflect
   `W₀ * σ` where `σ` swaps the two hyperbolic columns (`σᵀ T σ = T`). An isometry `U` of `Qₙ` keeps the identity:
   `(U W)ᵀ Qₙ (U W) = T`. Decode by `Converse`; the curvatures are the second column. `exists_pairwiseTangent` at
   `n ≥ 2` from `converse_soddy_gosset_spheres` on `b = (1, …, 1, 2n/(n−1), 2n(n+1)/(n−1)²)` (null: `(n+1)⁴ − (n−1)⁴ =
   8n³ + 8n`); at `n = 1` the family centres `1, 3, 2`, radii `1, 1, −2`.
8. **Completion** (`Completion`): `M = [b | V]` with `Mᵀ Qₙ M = diag(0, 2•1)`, `b ≠ 0`: `P := 1 − (1/2) • V * Vᵀ * Qₙ`
   satisfies `Vᵀ Qₙ (P u) = 0`; `⟨P u, b⟩ = ⟨u, b⟩ = (Qₙ b) ⬝ᵥ u`, so some `z := P *ᵥ Pi.single ℓ 1` has `⟨z, b⟩ ≠ 0`
   (`Qₙ b ≠ 0` since `Qₙ` is invertible); `b̄ := (−4/⟨z, b⟩) • (z − (⟨z, z⟩/(2⟨z, b⟩)) • b)` is null, `Qₙ`-orthogonal to
   `V`'s columns, pairs to `−4` with `b`; `W := [b̄ | b | V]` satisfies the identity; decode. Uniqueness: two completions
   `b̄, b̄'` give `d = b̄' − b̄` with `⟨d, b⟩ = 0`, `⟨d, V⟩ = 0`; write `d` in the basis of `W`'s columns (`W` invertible):
   `d = α b + β b̄`, `β = 0`, then `⟨b̄', b̄'⟩ = 0` forces `α = 0`. The counterexample at `n = 2`: columns
   `0, e₀ − e₁, e₂ − e₃`; any family's augmented matrix would have `(inl 0, inl 1)` entry `⟨b̄, 0⟩ = 0 ≠ −4`.

## Module map and lanes

| Module | Owner lane | Proves (`_internal`) |
| --- | --- | --- |
| `AugmentedDescartes/Defs.lean` | desk (frozen) | the definitions, verbatim |
| `AugmentedDescartes/Rows.lean` | `rows` | the eight encoding theorems; `decodeRow`; `row_inl_one`, `tangent_comm` |
| `AugmentedDescartes/Lorentz.lean` | `lorentz` | `augmented_identity_iff_lorentz`, `gram_eq_of_augmented_identity`, the inverses, `inv_of_identity`, `det_descartesQ`, `soddy_gosset_iff_isotropic` |
| `AugmentedDescartes/Main.lean` | `main` | `augmented_descartes(_general)`, `soddy_gosset(_general)`, `curvature_center(_general)` |
| `AugmentedDescartes/Corollaries.lean` | `corollaries` | `complex_descartes(_mixed)`, `sphere_soddy_gosset(_enclosing)`, `sphere_augmented_descartes` |
| `AugmentedDescartes/Converse.lean` | `converse` | `augmented_descartes_converse(_spheres)` |
| `AugmentedDescartes/Apollonian.lean` | `apollonian` | `apollonianGen_mem_aut`, `apollonian_reflection`, `apollonianGen_mul_apply`, `two_tangent_rows`, `two_tangent_spheres` |
| `AugmentedDescartes/Base.lean` | `base` | `exists_configuration` |
| `AugmentedDescartes/Transitivity.lean` | `converse-sg` | `qReflection`, `converse_soddy_gosset(_spheres)`, `exists_pairwiseTangent` |
| `AugmentedDescartes/Completion.lean` | `completion` | `curvature_center_converse`, `curvature_center_converse_needs_nonzero` |

Imports: `Defs ← Rows ← Lorentz ← Main ← Corollaries`; `Converse ← Main`; `Apollonian ← Converse`;
`Base ← Rows`; `Transitivity ← Base, Converse, Apollonian`; `Completion ← Converse`. A lane uses the other modules'
pinned statements as black boxes (sorried skeletons compile) and never restates them.

## Rules

1. Helpers carry the lane prefix (`rows_`, `lor_`, `main_`, `cor_`, `conv_`, `apo_`, `base_`, `tr_`, `cmp_`).
2. No `native_decide`, `axiom`, `set_option maxHeartbeats`, `mutual`; `decide` on tiny goals only.
3. A wrong pin is proved under a new name and reported, never edited.
4. Build through `scripts/lane-build.sh <Module>`, one module per call.
5. `Challenge.lean`, `Defs.lean`, `Solution.lean` and the other lanes' modules are read-only for a lane.
