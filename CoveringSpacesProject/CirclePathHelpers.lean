import Mathlib
import «CoveringSpacesProject».LoopHomotopy
import «CoveringSpacesProject».MetricSphereClosedBall

open Complex TopologicalSpace

open scoped unitInterval

noncomputable section

namespace Circle

/-- The canonical inclusion of the circle into the closed unit disk. -/
abbrev toClosedUnitDisk : Circle → Metric.closedBall (0 : ℂ) 1 :=
  Metric.sphereToClosedBall (0 : ℂ) 1

@[simp] theorem coe_toClosedUnitDisk (z : Circle) :
    ((toClosedUnitDisk z : Metric.closedBall (0 : ℂ) 1) : ℂ) = z := rfl

end Circle

namespace ContinuousMap

/-- Precompose a circle map with the standard loop `t ↦ Circle.exp (2πt)` on `I`. -/
def circleLoop {X : Type*} [TopologicalSpace X] (f : C(Circle, X)) : Path (f 1) (f 1) where
  toFun t := f (Circle.exp (2 * Real.pi * (t : ℝ)))
  continuous_toFun := f.continuous.comp <| Circle.exp.continuous.comp <| by fun_prop
  source' := by simp
  target' := by simp [Circle.exp_two_pi]

@[simp] theorem circleLoop_apply {X : Type*} [TopologicalSpace X] (f : C(Circle, X)) (t : I) :
    f.circleLoop t = f (Circle.exp (2 * Real.pi * (t : ℝ))) := rfl

/-- Precompose a homotopy of circle maps with the standard loop `t ↦ Circle.exp (2πt)`. -/
def circleLoopHomotopy {X : Type*} [TopologicalSpace X] {f g : C(Circle, X)}
    (H : ContinuousMap.Homotopy f g) : C(I × I, X) :=
  ⟨fun x => H (x.1, Circle.exp (2 * Real.pi * (x.2 : ℝ))),
    H.continuous_toFun.comp
      (continuous_fst.prodMk
        (Circle.exp.continuous.comp <| by fun_prop))⟩

@[simp] theorem circleLoopHomotopy_apply {X : Type*} [TopologicalSpace X] {f g : C(Circle, X)}
    (H : ContinuousMap.Homotopy f g) (x : I × I) :
    circleLoopHomotopy H x = H (x.1, Circle.exp (2 * Real.pi * (x.2 : ℝ))) := rfl

theorem circleLoopHomotopy_isLoopHomotopy {X : Type*} [TopologicalSpace X] {f g : C(Circle, X)}
    (H : ContinuousMap.Homotopy f g) : ContinuousMap.IsLoopHomotopy (circleLoopHomotopy H) := by
  intro s
  change H (s, Circle.exp (2 * Real.pi * (0 : ℝ))) =
    H (s, Circle.exp (2 * Real.pi * (1 : ℝ)))
  simp [Circle.exp_two_pi]

@[simp] theorem circleLoopHomotopy_zero_left {X : Type*} [TopologicalSpace X]
    {f g : C(Circle, X)} (H : ContinuousMap.Homotopy f g) (t : I) :
    circleLoopHomotopy H (0, t) = f.circleLoop t := by
  change H (0, Circle.exp (2 * Real.pi * (t : ℝ))) = f (Circle.exp (2 * Real.pi * (t : ℝ)))
  exact H.map_zero_left (Circle.exp (2 * Real.pi * (t : ℝ)))

@[simp] theorem circleLoopHomotopy_one_left {X : Type*} [TopologicalSpace X]
    {f g : C(Circle, X)} (H : ContinuousMap.Homotopy f g) (t : I) :
    circleLoopHomotopy H (1, t) = g.circleLoop t := by
  change H (1, Circle.exp (2 * Real.pi * (t : ℝ))) = g (Circle.exp (2 * Real.pi * (t : ℝ)))
  exact H.map_one_left (Circle.exp (2 * Real.pi * (t : ℝ)))

end ContinuousMap
