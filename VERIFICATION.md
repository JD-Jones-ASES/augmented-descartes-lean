# Verification

All fifty-nine statements of Challenge.lean have proofs. The local build, the axiom audit, the source guard and its
controls, the definition and statement checks, the standard-library replay of every identity behind the compared
statements, the metadata check, the module-resolution check, the elaboration check and Palomar's core-notation audit of
the statements pass; `python scripts/verify.py` runs them all and ends with `VERIFY: PASS`. The checks below were last run
on the tree of the final commit (the counts are printed by verify.py); a build log is evidence for that tree only.
Theorems are numbered as in `comparator.json`, which is also their order in Challenge.lean. `comparator.json` lists no
`definition_names`: a name there is a definition hole whose value the Solution supplies; the twenty-two definitions here
are fully specified in the Challenge, so the comparator checks the Solution's values against them.

## Formal scope

| # | Statement | Proved in |
| --- | --- | --- |
| 1 | `lorentz_sphereRow_self` — A sphere row has Lorentz norm `1` | AugmentedDescartes/Rows.lean |
| 2 | `lorentz_sphereRow_eq_neg_one_iff` — Two sphere rows pair to `−1` exactly when the spheres are tangent in the signed sense | AugmentedDescartes/Rows.lean |
| 3 | `lorentz_sphereRow_planeRow_eq_neg_one_iff` — A sphere row and a hyperplane row pair to `−1` exactly when `⟪h, x⟫ − δ = −r` | AugmentedDescartes/Rows.lean |
| 4 | `lorentz_planeRow_eq_neg_one_iff` — Two unit-normal hyperplane rows pair to `−1` exactly when the normals are opposite | AugmentedDescartes/Rows.lean |
| 5 | `lorentz_row_self` — A valid oriented sphere or hyperplane has a row of Lorentz norm `1` | AugmentedDescartes/Rows.lean |
| 6 | `lorentz_row_eq_neg_one_iff` — Two valid oriented spheres or hyperplanes pair to `−1` exactly when they are tangent | AugmentedDescartes/Rows.lean |
| 7 | `row_injOn_valid` — Augmented coordinates are a global coordinate system (LMW, after (3.9)): valid oriented spheres and hyperplanes with the same row are equal | AugmentedDescartes/Rows.lean |
| 8 | `exists_orientedSphere_of_lorentz_self` — Every row of Lorentz norm `1` is the row of a valid oriented sphere (second coordinate nonzero) or hyperplane (second coordinate zero) | AugmentedDescartes/Rows.lean |
| 9 | `augmented_identity_iff_lorentz` — `Wᵀ Qₙ W` is the target exactly when the rows of `W` have Lorentz norm `1` and pair to `−1` | AugmentedDescartes/Lorentz.lean |
| 10 | `gram_eq_of_augmented_identity` — The Gram form of the identity: `W G Wᵀ = 2I − J` | AugmentedDescartes/Lorentz.lean |
| 11 | `augmented_descartes` — The augmented Euclidean Descartes theorem (LMW Theorem 3.3; (8.4) at `n = 1`) for spheres of nonzero curvature: `Wᵀ Qₙ W = [[0, −4, 0], [−4, 0, 0], [0, 0, 2 Iₙ]]` | AugmentedDescartes/Main.lean |
| 12 | `augmented_descartes_general` — The augmented Euclidean Descartes theorem (LMW Theorem 3.3) for spheres and hyperplanes | AugmentedDescartes/Main.lean |
| 13 | `augmented_descartes_converse` — The converse of LMW Theorem 3.3 (spheres and hyperplanes): every real solution is the augmented matrix of exactly one family of valid, pairwise tangent oriented spheres and hyperplanes (tangency in the signed-distance sense; compatible orientations in `augmented_orientation`) | AugmentedDescartes/Converse.lean |
| 14 | `augmented_descartes_converse_spheres` — The converse for spheres: a solution whose second column has no zero is the augmented matrix of exactly one pairwise tangent family of spheres, `rᵢ = 1 / W i (Sum.inl 1)` and `xᵢ k = W i (Sum.inr k) / W i (Sum.inl 1)` (tangency in the signed-distance sense) | AugmentedDescartes/Converse.lean |
| 15 | `soddy_gosset` — The Soddy–Gosset theorem (LMW Theorem 1.2, (1.2); Soddy 1936, Gosset 1937, Lachlan 1886 at `n = 3`): `(Σ 1/rᵢ)² = n Σ (1/rᵢ)²` | AugmentedDescartes/Main.lean |
| 16 | `soddy_gosset_general` — The Soddy–Gosset theorem for spheres and hyperplanes (curvature `0` for a hyperplane) | AugmentedDescartes/Main.lean |
| 17 | `soddy_gosset_iff_isotropic` — The Soddy–Gosset relation is the vanishing of the Descartes form: `(Σ bᵢ)² = n Σ bᵢ² ↔ bᵀ Qₙ b = 0` | AugmentedDescartes/Lorentz.lean |
| 18 | `curvature_center` — The Euclidean generalized Descartes theorem (LMW Theorem 3.2, (3.5)) for spheres: `Mᵀ Qₙ M = diag(0, 2 Iₙ)` | AugmentedDescartes/Main.lean |
| 19 | `curvature_center_general` — LMW Theorem 3.2 for spheres and hyperplanes | AugmentedDescartes/Main.lean |
| 20 | `complex_descartes` — The complex Descartes theorem (LMW Theorem 2.1, (2.2)) for four circles of nonzero curvature: with `zᵢ = xᵢ + i yᵢ`, `(Σ bᵢ zᵢ)² = 2 Σ (bᵢ zᵢ)²` | AugmentedDescartes/Corollaries.lean |
| 21 | `complex_descartes_mixed` — LMW (2.3): `Σ bᵢ (bᵢ zᵢ) = ½ (Σ bᵢ)(Σ bᵢ zᵢ)` | AugmentedDescartes/Corollaries.lean |
| 22 | `det_descartesQ` — `det Qₙ = −2/n` (GLMWY III, (6.4) in the proof of Lemma 6.4) | AugmentedDescartes/Lorentz.lean |
| 23 | `sphere_soddy_gosset` — Soddy–Gosset for Mathlib's spheres: `n + 2` spheres of positive radius, pairwise externally tangent (LMW's case (i); at `n = 1` the hypotheses cannot be met, three pairwise externally tangent intervals forcing a zero radius) | AugmentedDescartes/Corollaries.lean |
| 24 | `sphere_soddy_gosset_enclosing` — Soddy–Gosset with one enclosing sphere `e`, to which the others are internally tangent (`IsIntTangent (s j) (s e)`: `s j` lies inside `s e`) and which carries the curvature `−1/rₑ` (LMW's case (ii)) | AugmentedDescartes/Corollaries.lean |
| 25 | `sphere_augmented_descartes` — The augmented identity for Mathlib's spheres, pairwise externally tangent (unsatisfiable at `n = 1`) | AugmentedDescartes/Corollaries.lean |
| 26 | `exists_configuration` — Existence of a configuration in every dimension: two parallel hyperplanes at distance `2` and `n` unit spheres centred at `√2 eᵢ` (the configuration in the proof of GLMWY III's Theorem 6.1, given there for `n ≥ 2`; at `n = 1` the hyperplanes are oriented points) | AugmentedDescartes/Base.lean |
| 27 | `exists_pairwiseTangent` — Existence of a pairwise tangent family of spheres in every dimension | AugmentedDescartes/Transitivity.lean |
| 28 | `converse_soddy_gosset` — The existence half of the converse of the Soddy–Gosset theorem (LMW Theorem 3.1, which LMW state with "We do not know an easy proof of this result; a proof appears in [16]"; GLMWY III's arXiv versions 1–2 prove it as their Theorem 2.2 by the same route): every nonzero `b` with `(Σ bᵢ)² = n Σ bᵢ²` is the curvature vector of a pairwise tangent family of valid oriented spheres (`bᵢ ≠ 0`) and hyperplanes (`bᵢ = 0`), tangency in the signed-distance sense; the congruence half is `same_curvature_congruence` | AugmentedDescartes/Transitivity.lean |
| 29 | `converse_soddy_gosset_spheres` — The existence half of the converse of the Soddy–Gosset theorem for spheres: every `b` with no zero entry and `(Σ bᵢ)² = n Σ bᵢ²` is the curvature vector of a pairwise tangent family of spheres (tangency in the signed-distance sense) | AugmentedDescartes/Transitivity.lean |
| 30 | `curvature_center_converse` — The converse of LMW Theorem 3.2 in every dimension, under the hypothesis of a nonzero first column (GLMWY I, Theorem 3.1 and its Remark, state and prove it at `n = 2` with this hypothesis; LMW's printed converse, "any real solution `M`", omits it): every real `M` with `Mᵀ Qₙ M = diag(0, 2 Iₙ)` and a nonzero first column is the curvature–centre matrix of exactly one family of valid, pairwise tangent oriented spheres and hyperplanes (tangency in the signed-distance sense) | AugmentedDescartes/Completion.lean |
| 31 | `curvature_center_converse_needs_nonzero` — The hypothesis of `curvature_center_converse` is needed (GLMWY I, the Remark after Theorem 3.1): at `n = 2` the matrix with columns `0, e₀ − e₁, e₂ − e₃` solves the equation and is the curvature–centre matrix of no valid, pairwise tangent family (it is the matrix of four oriented lines with normals `±e₀, ±e₁`, which are not pairwise tangent) | AugmentedDescartes/Completion.lean |
| 32 | `apollonianGen_mem_aut` — The Apollonian generators preserve the Descartes form (GLMWY III, after (4.1)): `Sₖᵀ Qₙ Sₖ = Qₙ` | AugmentedDescartes/Apollonian.lean |
| 33 | `apollonian_reflection` — Replacing sphere `k` of a configuration by its Apollonian reflection gives a configuration | AugmentedDescartes/Apollonian.lean |
| 34 | `apollonianGen_mul_apply` — The reflected row is `(2/(n−1)) Σ_{i ≠ k} (row i) − (row k)`; in particular the two curvatures satisfy `bₖ + bₖ' = (2/(n−1)) Σ_{i ≠ k} bᵢ` and the centre columns the like relation (LMW (2.1) and (2.4) at `n = 2`) | AugmentedDescartes/Apollonian.lean |
| 35 | `two_tangent_rows` — Soddy's two spheres in every dimension (LMW, footnote 3; GLMWY III §4.1), in the signed sense and for the members of a configuration: the rows of Lorentz norm `1` pairing to `−1` with every row of a configuration but the `k`-th are exactly the `k`-th row and its Apollonian reflection, which are distinct | AugmentedDescartes/Apollonian.lean |
| 36 | `two_tangent_spheres` — Soddy's two spheres, geometrically (the signed count; LMW's footnote 3: the real circles tangent to each of `n + 1` mutually tangent real circles "with distinct tangents" number exactly two): given `n + 1` members of a configuration, exactly two valid oriented spheres or hyperplanes are tangent to all of them in the signed sense, the missing member and one other, and their curvatures sum to `(2/(n−1)) Σ` of the others' curvatures | AugmentedDescartes/Apollonian.lean |
| 37 | `same_curvature_motion` — The congruence half of the converse of the Soddy–Gosset theorem in matrix form (LMW Theorem 3.1; GLMWY III arXiv v1–v2, Theorem 2.2 (ii)): two solutions of the identity with the same curvature column satisfy `W₁ * rigidMotionMatrix O t = W₂` for exactly one pair `(O, t)` with `Oᵀ O = 1`, hyperplanes included (`same_curvature_congruence` is the geometric form) | AugmentedDescartes/Rigidity.lean |
| 38 | `rigidMotion_parameters` — The motion's parameters from the two matrices: with `W₁ = [a | b | X]`, `W₂ = [a' | b | X']` and `W₁ * rigidMotionMatrix O t = W₂`, `O = ½ Xᵀ Qₙ X'` and `t = −¼ aᵀ Qₙ X'` (row-vector convention; read from `W₁⁻¹ = ½ G W₁ᵀ Qₙ`, so no hypothesis on `O` or on `W₂` is needed) | AugmentedDescartes/Rigidity.lean |
| 39 | `rigidMotionPoint_isometry` — For `Oᵀ O = 1` the point map `x ↦ x O + t` is an isometry | AugmentedDescartes/Rigidity.lean |
| 40 | `rigidMotionMatrix_sphereRow` — On a sphere row the matrix acts as the motion: centre `x ↦ x O + t`, signed radius fixed (`Oᵀ O = 1` is needed; at `r = 0` both sides are the zero row) | AugmentedDescartes/Rigidity.lean |
| 41 | `rigidMotionMatrix_planeRow` — On a hyperplane row the matrix multiplies the normal by `O` and moves the offset: `h ↦ h O`, `δ ↦ δ + (h O) ⬝ᵥ t`; no hypothesis on `O`, since a hyperplane row has curvature `0` | AugmentedDescartes/Rigidity.lean |
| 42 | `same_curvature_congruence` — The congruence half of the converse of the Soddy–Gosset theorem (LMW Theorem 3.1; GLMWY III arXiv v1–v2, Theorem 2.2 (ii)), with uniqueness: two valid, pairwise tangent families with the same curvatures, index by index, are carried one to the other by exactly one Euclidean motion `x ↦ x O + t`, `Oᵀ O = 1` (reflections and hyperplanes included; tangency in the signed-distance sense) | AugmentedDescartes/Rigidity.lean |
| 43 | `rowPower_sphereRow` — The power polynomial of a sphere row is `(dist(y, x)² − r²)/r` | AugmentedDescartes/Orientation.lean |
| 44 | `rowPower_planeRow` — The power polynomial of a hyperplane row is `2(δ − ⟪h, y⟫)` | AugmentedDescartes/Orientation.lean |
| 45 | `rowPower_sphereRow_neg_iff_of_pos` — For `r > 0` the power is negative exactly on the open ball `dist(y, x) < r` | AugmentedDescartes/Orientation.lean |
| 46 | `rowPower_sphereRow_neg_iff_of_neg` — For `r < 0` the power is negative exactly on the open exterior `−r < dist(y, x)` | AugmentedDescartes/Orientation.lean |
| 47 | `rowPower_planeRow_neg_iff` — The power of a hyperplane row is negative exactly on the open half-space `δ < ⟪h, y⟫` into which `h` points | AugmentedDescartes/Orientation.lean |
| 48 | `augmented_orientation` — Compatible orientations (LMW §3, the definition of an oriented Descartes configuration: interiors disjoint with the given orientations or with all reversed; the total curvature is never zero and its sign fixes the orientation, GLMWY III §3.1, p. 6): for a solution of the identity the total curvature `B = Σ W k (Sum.inl 1)` is nonzero, and no point `y` has `B Fᵢ(y) < 0` and `B Fⱼ(y) < 0` for two rows `i ≠ j`, `Fᵢ = rowPower (W i)` | AugmentedDescartes/Orientation.lean |
| 49 | `augmented_orientation_disjoint` — The same as disjoint sets: `{y | B Fᵢ(y) < 0}` and `{y | B Fⱼ(y) < 0}` are disjoint for `i ≠ j` | AugmentedDescartes/Orientation.lean |
| 50 | `augmented_no_three_zero_curvatures` — At most two rows of a solution of the identity have zero curvature, the hyperplane rows (the four cases of the curvature vector of a positively oriented configuration, GLMWY III §3.1, p. 6; LMW's list after Theorem 3.1), by Cauchy–Schwarz | AugmentedDescartes/Orientation.lean |
| 51 | `augmented_no_three_boundaries` — No three rows of a solution of the identity have power `0` at one point `y` of `ℝⁿ`: no three boundaries share a finite point (LMW's distinct tangencies, at finite points) | AugmentedDescartes/Orientation.lean |
| 52 | `rigidMotionOf_isValid` — A Euclidean motion preserves validity | AugmentedDescartes/Rigidity.lean |
| 53 | `rigidMotionOf_curvature` — A Euclidean motion preserves the signed curvature | AugmentedDescartes/Motion.lean |
| 54 | `lorentz_vecMul_rigidMotionMatrix` — The augmented matrix of a motion preserves the Lorentz pairing of rows | AugmentedDescartes/Motion.lean |
| 55 | `rigidMotionOf_tangent_iff` — A Euclidean motion preserves tangency of valid objects | AugmentedDescartes/Motion.lean |
| 56 | `congruent_iff_same_curvature` — Two labelled families of valid, pairwise tangent oriented spheres and hyperplanes are congruent exactly when their curvature vectors agree (LMW Theorem 3.1's congruence half as an equivalence) | AugmentedDescartes/Motion.lean |
| 57 | `tangent_family_curvature_sum_ne_zero` — The total curvature of a family of valid, pairwise tangent oriented spheres and hyperplanes is never zero (GLMWY III §3.1, p. 6, for configurations) | AugmentedDescartes/Motion.lean |
| 58 | `tangent_family_interiors_disjoint` — A family of valid, pairwise tangent oriented spheres and hyperplanes with positive total curvature has pairwise disjoint open interiors (LMW §3's compatible orientations, for the family itself): the open ball of a positive-radius sphere, the open exterior of a negative-radius sphere, the open half-space into which a hyperplane's normal points (`rowPower_sphereRow_neg_iff_of_pos`, `rowPower_sphereRow_neg_iff_of_neg`, `rowPower_planeRow_neg_iff`) | AugmentedDescartes/Motion.lean |
| 59 | `tangent_family_two_hyperplanes` — At most two members of a family of valid, pairwise tangent oriented spheres and hyperplanes are hyperplanes | AugmentedDescartes/Motion.lean |

## What is checked

- **Build** — `lake build AugmentedDescartes`, `lake build Challenge`, `lake build Solution`, `lake build Test` on the
  pinned toolchain and Mathlib (`lean-toolchain`, `lake-manifest.json`; `lake update` is never run).
- **Axioms** — `Test/Axioms.lean` walks every constant whose name begins with `AugmentedDescartes.`,
  `_private.AugmentedDescartes.` or `_private.Solution.` (private auxiliaries are not enumerated under the module
  system, but `collectAxioms` reaches every private constant a public proof uses) and fails the build on any axiom
  beyond `propext`, `Classical.choice`, `Quot.sound`; it also fails if fewer than 289 constants are matched
  (320 are) or any compared theorem is missing from the environment.
- **Source guard** — `scripts/check-source.py` rejects `sorry`, `sorryAx`, `admit`, `axiom`, `native_decide`, `unsafe`,
  `partial`, `implemented_by`, `extern`, `opaque`, `mutual`, `csimp`, `ofReduceNat`, `ofReduceBool`, `set_option` and
  every `debug.` option outside comments and strings in `AugmentedDescartes/`, `Solution.lean`, `Test/`, `Test.lean` and
  `AugmentedDescartes.lean` (Challenge.lean is checked for every token except its intentional `sorry` placeholders;
  `scripts/core_notation_audit.lean`, the registry's own audit script, is not a proof file and is outside the guard), any
  `leanOptions`, `moreLeanArgs`, `weakLeanArgs` or `-D` in `lakefile.toml`, and any control character in the Python
  scripts; `scripts/check_source_guard.py` runs the guard on one clean fixture, six prohibited-option fixtures and one
  with a control byte in a script.
- **Definitions and statements** — `scripts/check_definitions.py` compares every definition block of Challenge.lean with
  `AugmentedDescartes/Defs.lean` character for character; `scripts/check_statements.py` compares every theorem header of
  Challenge.lean with Solution.lean; `scripts/verify.py` prints every compared definition, and the type of every compared
  theorem, with `pp.all` from both modules and requires identical output, and runs Palomar's core-notation audit on every
  compared declaration.
- **Replay** — `scripts/check_descartes.py` (584 checks, no `assert`, the same verdict under `python -O`) rebuilds
  the identities in the standard library, exactly (`fractions.Fraction`) where the data are rational, over `ℚ(√3)` at
  `n = 3`, and in floating point with a fixed seed where that is impossible (the base configuration of two hyperplanes
  and `n` unit spheres has `√2` centres at every `n`, and no configuration is rational at `n = 3..7`, since
  `det(W)² = n 2ⁿ⁺³` is not a square there, which the replay checks; the seed also drives the exact random null vectors
  at n = 1, 2): the rational configurations at n = 1 and n = 2 (the Lorentz Gram matrix, the matrix
  identity, Soddy–Gosset, the curvature–centre identity, the complex Descartes theorem and LMW's (2.3) in their real and
  imaginary parts); the inverse identities for n = 1..8 and det Qₙ = −2/n for n = 1..6; the configuration of two
  hyperplanes and n unit spheres for n = 1..7, its rows decoded and every pair, sphere–hyperplane and
  hyperplane–hyperplane included, checked for tangency, Soddy–Gosset on it with the hyperplanes' zero curvatures, and for
  n = 2..7 its two Apollonian reflections (the all-sphere family with curvatures (1, …, 1, 2n/(n−1), 2n(n+1)/(n−1)²),
  decoded and checked for pairwise tangency, the two roots of the norm along the admissible line, the invertibility of
  the base matrix); the Challenge's generator matrix Sₖ built from its formula, SₖᵀQₙSₖ = Qₙ, its row formula and the
  curvature relation on random configurations for n = 2..6; the existence half of the converse of Soddy–Gosset on random
  null vectors made by rational Qₙ-reflections (exact at n = 1, 2; float at n = 3..7); the completion of the converse of
  the curvature–centre theorem recovering the original co-curvature column (n = 1..7) and rebuilding the solution from an
  independently reflected configuration (n = 1, 2); the matrix at n = 2 that solves the equation, whose every candidate
  completion has (0, 1) entry 0 rather than −4 and whose rows are four oriented lines that are not pairwise tangent; the
  decoding round trips and the equivalence of the Soddy–Gosset relation with bᵀQₙb = 0 on random vectors; non-tangent
  pairs (two unit circles at distance 3, a circle and a far line, perpendicular and like-oriented parallel lines) pairing
  to values other than −1; the squared-distance forms of Mathlib's `IsExtTangent` and `IsIntTangent` on the rational
  n = 2 configuration; Euclidean motions (rational rotations, reflections and translations of the rational
  configurations at n = 1, 2 and of two `ℚ(√3)` configurations at n = 3, two hyperplanes included), the motion recovered
  from the two matrices by `O = ½ Xᵀ Qₙ X'`, `t = −¼ aᵀ Qₙ X'` and compared with its action on sphere and hyperplane
  rows, five pairs of families built independently with equal curvatures and the motion between them recovered, and two
  controls (a non-orthogonal stretch keeps the curvatures and breaks the identity; an Apollonian replacement keeps the
  identity and changes a curvature); the power polynomial against ball, exterior and half-space membership, its null
  relation and `B Σ Fᵢ = ‖B y − V‖² + n(n + 2)`, both global orientations, `B ≠ 0` and no three boundaries through a
  finite point on 54 families at n = 1..7 (every tangency point on exactly two boundaries, all contacts distinct), two
  families with `B < 0` whose raw interiors overlap at a point that lies in at most one interior after multiplying by
  `B`, and a tangent pair with overlapping interiors; and a control in which one moved centre breaks the identity. The
  rational matrices, `G` included, are built from `Fraction` entries throughout, so halving them stays exact.

## What is not checked here

The statements' faithfulness to the papers is argued in `formalization.yaml` (fidelity) and PROOF.md, not checked
mechanically. Compatible orientations are stated for the rows of a solution, after multiplying by the total curvature
`B`, and for a family of valid, pairwise tangent objects when `B > 0`; the congruence half is for families labelled
alike. There is no compactification: tangency at infinity is the convention of opposite normals, and boundaries are
compared at finite points only. LMW's Section 8 convention for the line and the spherical and hyperbolic forms are
outside the formal scope. The replay is a second implementation of the identities, not a proof.
