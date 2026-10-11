module

import Solution
import Lean.Util.CollectAxioms

/-!
# Axiom audit

A module file importing `Solution` (not `Challenge.lean`). Walks every constant of the environment
whose name begins with `AugmentedDescartes.`, `_private.AugmentedDescartes.` or `_private.Solution.` (the public declarations of
this development; the private auxiliaries that Lean generates are not enumerated under the module
system, but `collectAxioms` reaches every private constant a public proof refers to, including a
private `axiom`), and collects the axioms each depends on. Anything outside `propext`,
`Classical.choice`, `Quot.sound` is reported with `logError`, which fails `lake build`. The audit
also fails if it matched fewer constants than the floor below (so a renamed namespace cannot make it
pass vacuously) or if any of the compared theorems is missing from the environment.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut checked : Nat := 0
  let mut rejected : Nat := 0
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for (name, _) in env.constants.toList do
    let label := name.toString
    if label.startsWith "AugmentedDescartes." || label.startsWith "_private.AugmentedDescartes." ||
        label.startsWith "_private.Solution." then
      checked := checked + 1
      let axs ← collectAxioms name
      for ax in axs do
        unless allowed.contains ax do
          rejected := rejected + 1
          logError m!"Unexpected axiom dependency: {name} -> {ax}"
  unless checked ≥ 80 do
    logError m!"Axiom audit matched only {checked} project constants; expected at least 80"
  for n in [`AugmentedDescartes.lorentz_sphereRow_self,
      `AugmentedDescartes.lorentz_sphereRow_eq_neg_one_iff,
      `AugmentedDescartes.lorentz_sphereRow_planeRow_eq_neg_one_iff,
      `AugmentedDescartes.lorentz_planeRow_eq_neg_one_iff,
      `AugmentedDescartes.lorentz_row_self, `AugmentedDescartes.lorentz_row_eq_neg_one_iff,
      `AugmentedDescartes.row_injOn_valid,
      `AugmentedDescartes.exists_orientedSphere_of_lorentz_self,
      `AugmentedDescartes.augmented_identity_iff_lorentz,
      `AugmentedDescartes.gram_eq_of_augmented_identity,
      `AugmentedDescartes.augmented_descartes, `AugmentedDescartes.augmented_descartes_general,
      `AugmentedDescartes.augmented_descartes_converse,
      `AugmentedDescartes.augmented_descartes_converse_spheres,
      `AugmentedDescartes.soddy_gosset, `AugmentedDescartes.soddy_gosset_general,
      `AugmentedDescartes.soddy_gosset_iff_isotropic, `AugmentedDescartes.curvature_center,
      `AugmentedDescartes.curvature_center_general, `AugmentedDescartes.complex_descartes,
      `AugmentedDescartes.complex_descartes_mixed, `AugmentedDescartes.det_descartesQ,
      `AugmentedDescartes.sphere_soddy_gosset,
      `AugmentedDescartes.sphere_soddy_gosset_enclosing,
      `AugmentedDescartes.sphere_augmented_descartes, `AugmentedDescartes.exists_configuration,
      `AugmentedDescartes.exists_pairwiseTangent, `AugmentedDescartes.converse_soddy_gosset,
      `AugmentedDescartes.converse_soddy_gosset_spheres,
      `AugmentedDescartes.curvature_center_converse,
      `AugmentedDescartes.curvature_center_converse_needs_nonzero,
      `AugmentedDescartes.apollonianGen_mem_aut, `AugmentedDescartes.apollonian_reflection,
      `AugmentedDescartes.apollonianGen_mul_apply, `AugmentedDescartes.two_tangent_rows,
      `AugmentedDescartes.two_tangent_spheres] do
    unless env.contains n do
      logError m!"Compared theorem is missing from the environment: {n}"
  logInfo m!"Audited {checked} project constants; unexpected axiom dependencies: {rejected}."
