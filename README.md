# The augmented Descartes theorem in every dimension, its converses, and Soddy's two spheres

Lagarias, Mallows and Wilks (*Beyond the Descartes circle theorem*, Amer. Math. Monthly 109 (2002) 338–361,
[arXiv:math/0101066](https://arxiv.org/abs/math/0101066), §3): an oriented sphere in `ℝⁿ` with centre `x` and
signed radius `r` has the augmented curvature–centre row `(‖x‖²/r − r, 1/r, x/r)`, an oriented hyperplane
`⟪h, y⟫ = δ` with unit normal `h` the row `(2δ, 0, h)`; for `n + 2` mutually tangent oriented spheres the matrix
`W` of rows satisfies `Wᵀ Qₙ W = [[0, −4, 0], [−4, 0, 0], [0, 0, 2 Iₙ]]`, `Qₙ = I − (1/n) 𝟙𝟙ᵀ` (Theorem 3.3), and
every real solution is the augmented matrix of a unique configuration. Tangency is taken here pair by pair, by
signed distances (two spheres `dist² = (r + s)²`, a sphere and a hyperplane `⟪h, x⟫ − δ = −r`, two hyperplanes
opposite normals), and the converses deliver tangency in this sense. LMW's configurations also have distinct
tangencies and compatible orientations (disjoint interiors, up to reversing every orientation); for every solution
the orientations are proved compatible separately, after multiplying each row's power polynomial by the total
curvature, and no three boundaries share a finite point.

[Challenge.lean](Challenge.lean) states fifty-nine theorems over twenty-two definitions (namespace
`AugmentedDescartes`); [Solution.lean](Solution.lean) proves them, kernel-only; [VERIFICATION.md](VERIFICATION.md)
names each one and [PROOF.md](PROOF.md) gives the arguments. For every `n ≥ 1` (LMW's §3 assumes `n ≥ 2`; their
§8, (8.4), is the identity on the line under their convention for the infinite interval):

- the identity for spheres of nonzero curvature and for spheres with hyperplanes (`augmented_descartes`,
  `augmented_descartes_general`), as LMW's §4 argument (Lemmas 4.3–4.4) run in Euclidean coordinates: `Wᵀ Qₙ W`
  is the target exactly when the rows of `W` have Lorentz norm `1` and pair to `−1` under
  `G = [[0, −½, 0], [−½, 0, 0], [0, 0, Iₙ]]` (`augmented_identity_iff_lorentz`, `gram_eq_of_augmented_identity`),
  and the pairings of sphere and hyperplane rows are the tangency conditions (eight encoding theorems);
- its converse with uniqueness, for spheres and hyperplanes and for spheres alone when the second column has no
  zero (`augmented_descartes_converse`, `augmented_descartes_converse_spheres`);
- Soddy–Gosset `(Σ 1/rᵢ)² = n Σ (1/rᵢ)²` (LMW's Theorem 1.2) with and without hyperplanes and as `bᵀ Qₙ b = 0`
  (`soddy_gosset`, `soddy_gosset_general`, `soddy_gosset_iff_isotropic`); `Mᵀ Qₙ M = diag(0, 2 Iₙ)` (Theorem 3.2;
  `curvature_center`, `curvature_center_general`); at `n = 2` the complex Descartes theorem and LMW's (2.3)
  (`complex_descartes`, `complex_descartes_mixed`); `det Qₙ = −2/n` (`det_descartesQ`); and the statements for
  Mathlib's `EuclideanGeometry.Sphere`, pairwise `IsExtTangent` or with one enclosing sphere to which the others
  are `IsIntTangent` (`sphere_soddy_gosset`, `sphere_soddy_gosset_enclosing`, `sphere_augmented_descartes`).

Also proved. Both halves of LMW's Theorem 3.1, the converse of Soddy–Gosset ("We do not know an easy proof of this
result; a proof appears in [16]"). Existence: every nonzero `b` with `(Σ bᵢ)² = n Σ bᵢ²` is the curvature vector
of a pairwise tangent family of spheres and hyperplanes, of spheres alone when no `bᵢ` vanishes
(`converse_soddy_gosset`, `converse_soddy_gosset_spheres`), by one `Qₙ`-reflection from the configuration of two
parallel hyperplanes and `n` unit spheres (`exists_configuration`, `exists_pairwiseTangent`) or from its inversion
in the unit sphere. Congruence: two valid, pairwise tangent families with the same labelled curvatures differ by
exactly one Euclidean motion `x ↦ x O + t`, `Oᵀ O = I`, hyperplanes and reflections included
(`same_curvature_congruence`; the matrix form `same_curvature_motion`: `W₂ = W₁ · rigidMotionMatrix O t` for
exactly one `(O, t)`), with `O = ½ Xᵀ Qₙ X'` and `t = −¼ aᵀ Qₙ X'` for `W = [a | b | X]`,
`W' = [a' | b | X']` (`rigidMotion_parameters`) and the motion's action on points, spheres and hyperplanes (three
theorems); LMW state the existence of a motion for `n ≥ 2`. A motion preserves validity, curvature and tangency
(`rigidMotionOf_isValid`, `rigidMotionOf_curvature`, `rigidMotionOf_tangent_iff`; the motion matrix preserves the
Lorentz pairing, `lorentz_vecMul_rigidMotionMatrix`), so two valid, pairwise tangent families are congruent exactly
when their curvature vectors agree (`congruent_iff_same_curvature`). [16] is Graham–Lagarias–Mallows–Wilks–Yan,
[*Apollonian circle packings: geometry and group theory III*](https://arxiv.org/abs/math/0010324), whose arXiv
versions 1–2 prove both halves as their Theorem 2.2 from that configuration (the congruence half by the rigidity of
a simplex of centres), in whose proof of Theorem 6.1 it reappears, and whose §9 gives the translation and rotation
matrices on augmented coordinates. For every solution of the identity (`augmented_orientation`,
`augmented_orientation_disjoint`): the total curvature `B = Σ bᵢ` is nonzero, and the open sets `{y | B Fᵢ(y) < 0}`,
`Fᵢ` the power polynomial of row `i` (negative exactly inside a ball, outside a ball of negative radius, or on the
side of a hyperplane its normal points to; five theorems), are pairwise disjoint; at most two rows are hyperplanes
(`augmented_no_three_zero_curvatures`), and no three boundaries pass through a finite point
(`augmented_no_three_boundaries`); for a valid, pairwise tangent family the total curvature is nonzero
(`tangent_family_curvature_sum_ne_zero`), at most two members are hyperplanes (`tangent_family_two_hyperplanes`),
and when it is positive the open interiors themselves are pairwise disjoint (`tangent_family_interiors_disjoint`).
The converse of LMW's Theorem 3.2 in every dimension under the hypothesis of a nonzero first column
(`curvature_center_converse`): GLMWY [I](https://arxiv.org/abs/math/0010298), Theorem 3.1 and its Remark, prove it
at `n = 2` with that hypothesis, LMW's printed converse and GLMWY III's arXiv v1–v2 Theorem 2.3 omit it, and the
matrix at `n = 2` with columns `0, e₀ − e₁, e₂ − e₃`, GLMWY I's configuration (3.15) with its first column zeroed,
solves the equation and is the curvature–centre matrix of no valid, pairwise tangent family
(`curvature_center_converse_needs_nonzero`). For `n ≥ 2`, the Apollonian generators
`Sₖ = I + (2/(n−1)) eₖ 𝟙ᵀ − (2n/(n−1)) eₖ eₖᵀ` of GLMWY III, (4.1), preserve `Qₙ` and carry configurations to
configurations (`apollonianGen_mem_aut`, `apollonian_reflection`, `apollonianGen_mul_apply`), and Soddy's two
spheres (LMW, footnote 3; GLMWY III, §4.1) in the signed sense: the oriented spheres and hyperplanes tangent to
`n + 1` members of a configuration are exactly the missing member and its Apollonian reflection, two distinct
objects with `b + b' = (2/(n−1)) Σ bᵢ` (`two_tangent_rows`, `two_tangent_spheres`).

The spelling is Gosset (Thorold Gosset, author of "The Hexlet", Nature 139 (1937) 251–252); LMW print "Gossett"
in Theorem 1.2 and "Gosset" in Theorem 3.1. `scripts/check_descartes.py` replays the identities in the standard
library, exactly where the data are rational (and over `ℚ(√3)` at `n = 3`; at `n = 3..7` no configuration is
rational, since `det(W)² = n 2ⁿ⁺³` is not a square there); `python scripts/verify.py` runs every local check and
ends with `VERIFY: PASS`. As of the searches of 2026-10-09 to 2026-10-11 (UTC) no Palomar entry, ATLAS file,
Mathlib declaration (1000.yaml lists Q1196538 with none), formal-conjectures, openai/math, LeanPool,
anthropics/formal-math, Isabelle AFP, Rocq, HOL Light, GitHub code search or arXiv result formalizes these
statements; the planar Soddy–Gosset relation for four circles of positive radius, pairwise externally tangent or
with one enclosing circle, is proved in
[facebookresearch/atlas-lean](https://github.com/facebookresearch/atlas-lean/blob/27a38cfdcea9e80a11c49ff8e2ce17650e264552/MathlibExt/Geometry/Euclidean/DescartesCircleTheorem.lean)
(`descartes_circle_theorem`, unregistered);
[rjwalters/lean-genius](https://github.com/rjwalters/lean-genius/blob/8e7085869ea0f90f1a5e1f8348affc97f75bb9a2/proofs/Proofs/DescartesCircleTheorem.lean)
(four files) and [carlok/LeanFrontier](https://github.com/carlok/LeanFrontier/blob/bb432f13a234e682dec83ba94e427d684d9825c5/LeanFrontier/NumberTheory/DescartesCircle.lean)
treat `(Σ kᵢ)² = 2 Σ kᵢ²` as a definition (its two roots in `k₄`, the same over `ℂ`, integer reflections and parity),
LeanFrontier checking it for one family of Ford circles and their tangent line, neither deriving it from tangency;
a DIMACS REU 2022 project toward Soddy–Gosset in Lean is unfinished, and the integral Descartes quadruples of
tadamcz/annals-results, ImperialCollegeLondon/AnnalsChallenge and brandonrdug/holonics carry no centres or
tangency; nothing is derived from any of them.
Lean v4.35.0-rc2, Mathlib v4.35.0-rc2; MIT ([LICENSE](LICENSE)); AI assistance in [DISCLOSURE.md](DISCLOSURE.md).
