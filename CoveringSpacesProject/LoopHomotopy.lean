import Mathlib

/-!
# Homotopies through loops

This file packages the condition that a homotopy `I × I → X` stays within loops, in the sense that
each slice has the same start and end point.
-/

open scoped unitInterval

namespace ContinuousMap

/-- A homotopy through loops on `I`. -/
def IsLoopHomotopy {X : Type*} [TopologicalSpace X] (H : C(I × I, X)) : Prop :=
  ∀ s, H (s, 0) = H (s, 1)

end ContinuousMap
