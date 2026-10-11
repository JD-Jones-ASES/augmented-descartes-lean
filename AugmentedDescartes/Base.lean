module

public import AugmentedDescartes.Rows

/-!
# Base

The strip configuration (ARCH.md §6). Lane `base`.
-/

@[expose] public section

namespace AugmentedDescartes

open Matrix

/-- Existence of a configuration in every dimension: two parallel hyperplanes at distance `2` and `n`
unit spheres centred at `√2 eᵢ` (the configuration of GLMWY III, Theorem 6.1). -/
theorem exists_configuration_internal (n : ℕ) (hn : 0 < n) :
    ∃ s : Fin (n + 2) → OrientedSphere n, (∀ i, OrientedSphere.IsValid (s i)) ∧
      ∀ i j, i ≠ j → OrientedSphere.Tangent (s i) (s j) := sorry

end AugmentedDescartes
