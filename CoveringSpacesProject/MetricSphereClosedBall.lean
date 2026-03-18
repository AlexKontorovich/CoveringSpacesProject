import Mathlib

/-!
# Inclusions from spheres to closed balls

This file packages the canonical inclusion `Metric.sphere x r → Metric.closedBall x r`
as a named map.
-/

open Set

namespace Metric

/-- The canonical inclusion of a sphere into the corresponding closed ball. -/
def sphereToClosedBall {α : Type*} [PseudoMetricSpace α] (x : α) (r : ℝ) :
    sphere x r → closedBall x r :=
  Set.inclusion sphere_subset_closedBall

@[simp] theorem coe_sphereToClosedBall {α : Type*} [PseudoMetricSpace α] (x : α) (r : ℝ)
    (y : sphere x r) : ((sphereToClosedBall x r y : closedBall x r) : α) = y := rfl

end Metric
