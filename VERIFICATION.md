# Verification

All thirty-six statements of Challenge.lean have proofs. The local build, the axiom audit, the source guard and its
controls, the definition and statement checks, the standard-library replay of every identity behind the compared
statements, the metadata check, the module-resolution check, the elaboration check and Palomar's core-notation audit of
the statements pass; `python scripts/verify.py` runs them all and ends with `VERIFY: PASS`. The checks below were last run
on the tree of the final commit (the counts are printed by verify.py); a build log is evidence for that tree only.
Theorems are numbered as in `comparator.json`, which is also their order in Challenge.lean. `comparator.json` lists no
`definition_names`: a name there is a definition hole whose value the Solution supplies; the eighteen definitions here
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
| 13 | `augmented_descartes_converse` — The converse of LMW Theorem 3.3 (spheres and hyperplanes): every real solution is the augmented matrix of exactly one family of valid, pairwise tangent oriented spheres and hyperplanes (tangency in the signed-distance sense; disjoint interiors not asserted) | AugmentedDescartes/Converse.lean |
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
| 26 | `exists_configuration` — Existence of a configuration in every dimension: two parallel hyperplanes at distance `2` and `n` unit spheres centred at `√2 eᵢ` (the configuration of GLMWY III, Theorem 6.1, stated there for `n ≥ 2`; at `n = 1` the hyperplanes are oriented points) | AugmentedDescartes/Base.lean |
| 27 | `exists_pairwiseTangent` — Existence of a pairwise tangent family of spheres in every dimension | AugmentedDescartes/Transitivity.lean |
| 28 | `converse_soddy_gosset` — The existence half of the converse of the Soddy–Gosset theorem (LMW Theorem 3.1, which LMW state with "We do not know an easy proof of this result; a proof appears in [16]"; GLMWY III's arXiv versions 1–2 prove it as their Theorem 2.2 by the same route): every nonzero `b` with `(Σ bᵢ)² = n Σ bᵢ²` is the curvature vector of a pairwise tangent family of valid oriented spheres (`bᵢ ≠ 0`) and hyperplanes (`bᵢ = 0`), tangency in the signed-distance sense; the congruence half is not formalized | AugmentedDescartes/Transitivity.lean |
| 29 | `converse_soddy_gosset_spheres` — The existence half of the converse of the Soddy–Gosset theorem for spheres: every `b` with no zero entry and `(Σ bᵢ)² = n Σ bᵢ²` is the curvature vector of a pairwise tangent family of spheres (tangency in the signed-distance sense) | AugmentedDescartes/Transitivity.lean |
| 30 | `curvature_center_converse` — The converse of LMW Theorem 3.2 in every dimension, under the hypothesis of a nonzero first column (GLMWY I, Theorem 3.1 and its Remark, state and prove it at `n = 2` with this hypothesis; LMW's printed converse, "any real solution `M`", omits it): every real `M` with `Mᵀ Qₙ M = diag(0, 2 Iₙ)` and a nonzero first column is the curvature–centre matrix of exactly one family of valid, pairwise tangent oriented spheres and hyperplanes (tangency in the signed-distance sense) | AugmentedDescartes/Completion.lean |
| 31 | `curvature_center_converse_needs_nonzero` — The hypothesis of `curvature_center_converse` is needed (GLMWY I, the Remark after Theorem 3.1): at `n = 2` the matrix with columns `0, e₀ − e₁, e₂ − e₃` solves the equation and is the curvature–centre matrix of no family | AugmentedDescartes/Completion.lean |
| 32 | `apollonianGen_mem_aut` — The Apollonian generators preserve the Descartes form (GLMWY III, after (4.1)): `Sₖᵀ Qₙ Sₖ = Qₙ` | AugmentedDescartes/Apollonian.lean |
| 33 | `apollonian_reflection` — Replacing sphere `k` of a configuration by its Apollonian reflection gives a configuration | AugmentedDescartes/Apollonian.lean |
| 34 | `apollonianGen_mul_apply` — The reflected row is `(2/(n−1)) Σ_{i ≠ k} (row i) − (row k)`; in particular the two curvatures satisfy `bₖ + bₖ' = (2/(n−1)) Σ_{i ≠ k} bᵢ` and the centre columns the like relation (LMW (2.1) and (2.4) at `n = 2`) | AugmentedDescartes/Apollonian.lean |
| 35 | `two_tangent_rows` — Soddy's two spheres in every dimension (LMW, footnote 3; GLMWY III §4.1), in the signed sense and for the members of a configuration: the rows of Lorentz norm `1` pairing to `−1` with every row of a configuration but the `k`-th are exactly the `k`-th row and its Apollonian reflection, which are distinct | AugmentedDescartes/Apollonian.lean |
| 36 | `two_tangent_spheres` — Soddy's two spheres, geometrically (the signed count; LMW's footnote 3 counts the real spheres tangent to any `n + 1` mutually tangent spheres with distinct tangencies): given `n + 1` members of a configuration, exactly two valid oriented spheres or hyperplanes are tangent to all of them in the signed sense, the missing member and one other, and their curvatures sum to `(2/(n−1)) Σ` of the others' curvatures | AugmentedDescartes/Apollonian.lean |

## What is checked

- **Build** — `lake build AugmentedDescartes`, `lake build Challenge`, `lake build Solution`, `lake build Test` on the
  pinned toolchain and Mathlib (`lean-toolchain`, `lake-manifest.json`; `lake update` is never run).
- **Axioms** — `Test/Axioms.lean` walks every public constant in `AugmentedDescartes.*` (private auxiliaries are not
  enumerated under the module system, but `collectAxioms` reaches every private constant a public proof uses) and fails
  the build on any axiom beyond `propext`, `Classical.choice`, `Quot.sound`; it also fails if fewer than 250
  constants are matched or any compared theorem is missing from the environment.
- **Source guard** — `scripts/check-source.py` rejects `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`,
  `partial`, `implemented_by`, `extern`, `opaque`, `mutual`, `ofReduceBool`, `set_option` and every `debug.` option
  outside comments and strings in `AugmentedDescartes/`, `Solution.lean` and `Test/` (Challenge.lean's intentional `sorry`
  placeholders excepted), any `leanOptions`, `moreLeanArgs`, `weakLeanArgs` or `-D` in `lakefile.toml`, and any control
  character in the Python scripts; `scripts/check_source_guard.py` runs the guard on one clean fixture, six
  prohibited-option fixtures and one with a control byte in a script.
- **Definitions and statements** — `scripts/check_definitions.py` compares every definition block of Challenge.lean with
  `AugmentedDescartes/Defs.lean` character for character; `scripts/check_statements.py` compares every theorem header of
  Challenge.lean with Solution.lean; `scripts/verify.py` prints every compared definition, and the type of every compared
  theorem, with `pp.all` from both modules and requires identical output, and runs Palomar's core-notation audit on every
  compared declaration.
- **Replay** — `scripts/check_descartes.py` rebuilds every identity in the standard library, exactly where the data are
  rational (`fractions.Fraction`) and in floating point with a fixed seed where a square root enters: the rational
  configurations at n = 1 and n = 2 (the Lorentz Gram matrix, the matrix identity, Soddy–Gosset, the curvature–centre
  identity, the complex Descartes theorem), the inverse identities for n = 1..8, the configuration of two hyperplanes and
  n unit spheres for n = 1..7 with its two Apollonian reflections (the all-sphere family with curvatures
  (1, …, 1, 2n/(n−1), 2n(n+1)/(n−1)²), decoded and checked for pairwise tangency, the two roots of the norm along the
  admissible line, the invertibility of the base matrix), the converse of Soddy–Gosset on random null vectors made by
  rational Qₙ-reflections (exact at n = 1, 2; float at n = 3..7), the completion of the converse of the curvature–centre
  theorem with its uniqueness, the matrix at n = 2 that solves the equation and completes to nothing, the Mathlib
  tangency conventions, and a control in which one moved centre breaks the identity (176 checks).

## What is not checked here

The statements' faithfulness to the papers is argued in `formalization.yaml` (fidelity) and PROOF.md, not checked
mechanically. The disjoint-interiors property of an oriented Descartes configuration, the congruence half of the
converse of the Soddy–Gosset theorem, LMW's Section 8 convention for the line, and the spherical and hyperbolic forms are
outside the formal scope.
