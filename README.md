# The augmented Descartes theorem in every dimension, its converses, and Soddy's two spheres

Lagarias, Mallows and Wilks (*Beyond the Descartes circle theorem*, Amer. Math. Monthly 109 (2002) 338–361,
[arXiv:math/0101066](https://arxiv.org/abs/math/0101066), §3): an oriented sphere in `ℝⁿ` with centre `x` and
signed radius `r` has the augmented curvature–centre row `(‖x‖²/r − r, 1/r, x/r)`, an oriented hyperplane
`⟪h, y⟫ = δ` with unit normal `h` the row `(2δ, 0, h)`; for `n + 2` mutually tangent oriented spheres the matrix
`W` of rows satisfies `Wᵀ Qₙ W = [[0, −4, 0], [−4, 0, 0], [0, 0, 2 Iₙ]]`, `Qₙ = I − (1/n) 𝟙𝟙ᵀ` (Theorem 3.3), and
every real solution is the augmented matrix of a unique configuration. Tangency here is distance-encoded in their
oriented sense: two spheres `dist² = (r + s)²`, a sphere and a hyperplane `⟪h, x⟫ − δ = −r`, two hyperplanes
opposite normals; nothing is claimed about disjoint interiors.

[Challenge.lean](Challenge.lean) states thirty-six theorems over eighteen definitions (namespace
`AugmentedDescartes`); [Solution.lean](Solution.lean) proves them, kernel-only; the table in
[VERIFICATION.md](VERIFICATION.md) names each one. For every `n ≥ 1`:

- the matrix identity for spheres of nonzero curvature and for spheres with hyperplanes
  (`augmented_descartes`, `augmented_descartes_general`), proved as an equivalence: `Wᵀ Qₙ W` is the target
  exactly when the rows of `W` have Lorentz norm `1` and pair to `−1` under
  `G = [[0, −½, 0], [−½, 0, 0], [0, 0, Iₙ]]` (`augmented_identity_iff_lorentz`; `W G Wᵀ = 2I − J`,
  `gram_eq_of_augmented_identity`), the pairings of sphere and hyperplane rows being the tangency conditions
  (the eight encoding theorems);
- its converse with uniqueness: every solution is the augmented matrix of exactly one family of valid, pairwise
  tangent oriented spheres and hyperplanes, and of exactly one family of spheres when its second column has no
  zero (`augmented_descartes_converse`, `augmented_descartes_converse_spheres`);
- the corollaries: Soddy–Gosset `(Σ 1/rᵢ)² = n Σ (1/rᵢ)²` with and without hyperplanes and as `bᵀ Qₙ b = 0`
  (`soddy_gosset`, `soddy_gosset_general`, `soddy_gosset_iff_isotropic`), the curvature–centre identity
  `Mᵀ Qₙ M = diag(0, 2 Iₙ)` (`curvature_center`, `curvature_center_general`), at `n = 2` the complex Descartes
  theorem `(Σ bᵢ zᵢ)² = 2 Σ (bᵢ zᵢ)²` and `Σ bᵢ (bᵢ zᵢ) = ½ (Σ bᵢ)(Σ bᵢ zᵢ)` (`complex_descartes`,
  `complex_descartes_mixed`), `det Qₙ = −2/n` (`det_descartesQ`), and the statements for Mathlib's
  `EuclideanGeometry.Sphere`, pairwise `IsExtTangent` or with one enclosing sphere to which the others are
  `IsIntTangent` (`sphere_soddy_gosset`, `sphere_soddy_gosset_enclosing`, `sphere_augmented_descartes`).

Beyond the paper: the converse of the Soddy–Gosset theorem, which LMW state as the second half of their Theorem
3.1 with "We do not know an easy proof of this result" — every nonzero `b` with `(Σ bᵢ)² = n Σ bᵢ²` is the
curvature vector of a pairwise tangent family of spheres and hyperplanes, of spheres alone when no `bᵢ` vanishes
(`converse_soddy_gosset`, `converse_soddy_gosset_spheres`), by one `Qₙ`-reflection from the configuration of two
parallel hyperplanes and `n` unit spheres (`exists_configuration`; `exists_pairwiseTangent`); the converse of
their Theorem 3.2, which they leave unproved — every real `M` with `Mᵀ Qₙ M = diag(0, 2 Iₙ)` and a nonzero first
column is the curvature–centre matrix of exactly one family (`curvature_center_converse`), and the matrix at
`n = 2` with columns `0, e₀ − e₁, e₂ − e₃` shows that the printed statement needs the hypothesis
(`curvature_center_converse_needs_nonzero`); and, for `n ≥ 2`, the Apollonian generators
`Sₖ = I + (2/(n−1)) eₖ 𝟙ᵀ − (2n/(n−1)) eₖ eₖᵀ` of Graham–Lagarias–Mallows–Wilks–Yan
([*Apollonian circle packings: geometry and group theory III*](https://arxiv.org/abs/math/0010324), (4.1))
preserve `Qₙ` and carry configurations to configurations (`apollonianGen_mem_aut`, `apollonian_reflection`,
`apollonianGen_mul_apply`), and Soddy's two spheres in every dimension: the oriented spheres and hyperplanes
tangent to `n + 1` members of a configuration are exactly the missing member and its Apollonian reflection, two
distinct objects with `b + b' = (2/(n−1)) Σ bᵢ` (`two_tangent_rows`, `two_tangent_spheres`).

LMW's §3 assumes `n ≥ 2` and their §8 treats the line with another convention; here `n = 1` is the same algebra
with signed radii. The spelling is Gosset (Thorold Gosset, Nature 139 (1937) 62); LMW print "Gossett".
`scripts/check_descartes.py` replays every identity in the standard library, exactly where the data are
rational; `python scripts/verify.py` runs every local check and ends with `VERIFY: PASS`. As of 2026-10-10, no
search of the Palomar registry, ATLAS, Mathlib, formal-conjectures, openai/math, LeanPool, the Isabelle AFP,
Rocq's opam index, HOL Light, GitHub code search or arXiv found a formalization of these statements; the planar
Soddy–Gosset relation with positive radii and one enclosing circle is proved in
[facebookresearch/atlas-lean](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/DescartesCircleTheorem.lean)
(`descartes_circle_theorem`, unregistered), and a DIMACS REU 2022 project toward Soddy–Gosset in Lean is
unfinished; nothing is derived from either.
Lean v4.35.0-rc2, Mathlib v4.35.0-rc2; MIT ([LICENSE](LICENSE)); AI assistance in [DISCLOSURE.md](DISCLOSURE.md).
