import Mathlib
import «CoveringSpacesProject».RootsComplexPolynomials

open Complex TopologicalSpace

open scoped unitInterval

noncomputable section

/-- The closed unit disk in `ℂ`, using the existing project model. -/
abbrev ClosedUnitDisk := D2

namespace Circle

/-- The canonical inclusion of the circle into the closed unit disk. -/
abbrev toClosedUnitDisk : Circle → ClosedUnitDisk := circleToD2

end Circle

/-- The center of the closed unit disk. -/
abbrev closedUnitDiskZero : ClosedUnitDisk := zeroD2

namespace ContinuousMap

/-- Precompose a circle map with the standard parametrization `Circle.exp`. -/
def circlePath {X : Type*} [TopologicalSpace X]
    (f : C(Circle, X)) : C(Set.Icc (0 : ℝ) (2 * Real.pi), X) :=
  ⟨fun t => f (Circle.exp t), f.continuous.comp (Circle.exp.continuous.comp continuous_subtype_val)⟩

@[simp] theorem circlePath_apply {X : Type*} [TopologicalSpace X] (f : C(Circle, X))
    (t : Set.Icc (0 : ℝ) (2 * Real.pi)) : f.circlePath t = f (Circle.exp t) := rfl

theorem circlePath_source_eq_target {X : Type*} [TopologicalSpace X] (f : C(Circle, X)) :
    f.circlePath ⟨0, ⟨le_rfl, Real.two_pi_pos.le⟩⟩ =
      f.circlePath ⟨2 * Real.pi, ⟨Real.two_pi_pos.le, le_rfl⟩⟩ := by
  simp [circlePath, Circle.exp_two_pi]

/-- View a units-valued continuous map as a map to the subtype of nonzero complex numbers. -/
def toNonzeroSubtype {α : Type*} [TopologicalSpace α] (f : C(α, ℂˣ)) : C(α, Cstar) :=
  ⟨fun x => ⟨(f x : ℂ), (f x).ne_zero⟩,
    Continuous.subtype_mk (Units.continuous_val.comp f.continuous) fun x => (f x).ne_zero⟩

/-- View a continuous map to the subtype of nonzero complex numbers as a units-valued map. -/
def fromNonzeroSubtype {α : Type*} [TopologicalSpace α] (f : C(α, Cstar)) : C(α, ℂˣ) :=
  ContinuousMap.unitsOfForallIsUnit
    (f := ⟨fun x => (f x : ℂ), continuous_subtype_val.comp f.continuous⟩)
    fun x => isUnit_iff_ne_zero.mpr (f x).property

@[simp] theorem coe_toNonzeroSubtype_apply {α : Type*} [TopologicalSpace α] (f : C(α, ℂˣ))
    (x : α) : (f.toNonzeroSubtype x : ℂ) = f x := rfl

@[simp] theorem coe_fromNonzeroSubtype_apply {α : Type*} [TopologicalSpace α]
    (f : C(α, Cstar)) (x : α) : ((f.fromNonzeroSubtype x : ℂˣ) : ℂ) = f x := rfl

@[simp] theorem toNonzeroSubtype_fromNonzeroSubtype {α : Type*} [TopologicalSpace α]
    (f : C(α, Cstar)) : f.fromNonzeroSubtype.toNonzeroSubtype = f := by
  ext x
  rfl

@[simp] theorem fromNonzeroSubtype_toNonzeroSubtype {α : Type*} [TopologicalSpace α]
    (f : C(α, ℂˣ)) : f.toNonzeroSubtype.fromNonzeroSubtype = f := by
  ext x
  rfl

/-- The winding number of a continuous map from the circle to `ℂˣ`. -/
noncomputable def windingNumber (f : C(Circle, ℂˣ)) : ℤ :=
  DefWNS1 f.toNonzeroSubtype

@[simp] theorem windingNumber_const (c : ℂˣ) :
    windingNumber (ContinuousMap.const _ c : C(Circle, ℂˣ)) = 0 := by
  simpa [windingNumber, toNonzeroSubtype] using constS1 ⟨(c : ℂ), c.ne_zero⟩

theorem windingNumber_eq_of_homotopy {f g : C(Circle, ℂˣ)} (H : ContinuousMap.Homotopy f g) :
    windingNumber f = windingNumber g := by
  let H' : C(Circle × Set.Icc (0 : ℝ) 1, Cstar) :=
    ⟨fun x => ⟨(H (x.2, x.1) : ℂ), (H (x.2, x.1)).ne_zero⟩,
      Continuous.subtype_mk
        ((Units.continuous_val.comp H.continuous).comp (continuous_snd.prodMk continuous_fst))
        fun x => (H (x.2, x.1)).ne_zero⟩
  have hzero : ∀ z, H' (z, 0) = f.toNonzeroSubtype z := by
    intro z
    apply Subtype.ext
    simp [H', toNonzeroSubtype]
  have hone : ∀ z, H' (z, 1) = g.toNonzeroSubtype z := by
    intro z
    apply Subtype.ext
    simp [H', toNonzeroSubtype]
  simpa [windingNumber] using S1homotopy f.toNonzeroSubtype g.toNonzeroSubtype H' hzero hone

theorem exists_homotopy_of_norm_sub_lt {f g : C(Circle, ℂˣ)}
    (hclose : ∀ z : Circle, ‖(f z : ℂ) - g z‖ < ‖(f z : ℂ)‖) :
    Nonempty (ContinuousMap.Homotopy f g) := by
  obtain ⟨H, hzero, hone⟩ := walkingdog f.toNonzeroSubtype g.toNonzeroSubtype hclose
  let H' : C(Set.Icc (0 : ℝ) 1 × Circle, Cstar) :=
    ⟨fun x => H (x.2, x.1), H.continuous.comp (continuous_snd.prodMk continuous_fst)⟩
  refine ⟨{ toContinuousMap := H'.fromNonzeroSubtype, map_zero_left := ?_, map_one_left := ?_ }⟩
  · intro z
    apply Units.ext
    simpa using congrArg Subtype.val (hzero z)
  · intro z
    apply Units.ext
    simpa using congrArg Subtype.val (hone z)

theorem windingNumber_eq_of_norm_sub_lt {f g : C(Circle, ℂˣ)}
    (hclose : ∀ z : Circle, ‖(f z : ℂ) - g z‖ < ‖(f z : ℂ)‖) :
    windingNumber f = windingNumber g := by
  obtain ⟨H⟩ := exists_homotopy_of_norm_sub_lt hclose
  exact windingNumber_eq_of_homotopy H

theorem windingNumber_eq_zero_of_exists_extension {f : C(Circle, ℂˣ)} {F : C(ClosedUnitDisk, ℂˣ)}
    (hF : ∀ z : Circle, F (Circle.toClosedUnitDisk z) = f z) :
    windingNumber f = 0 := by
  have hF' : ∀ z : Circle, F.toNonzeroSubtype (Circle.toClosedUnitDisk z) = f.toNonzeroSubtype z := by
    intro z
    apply Subtype.ext
    simpa using congrArg Units.val (hF z)
  simpa [windingNumber] using boundsWN0 f.toNonzeroSubtype F.toNonzeroSubtype hF'

end ContinuousMap

/-- The monomial map `z ↦ a * (Rz)^n` on the unit circle, valued in `ℂˣ`. -/
noncomputable def circleMonomial (a : ℂˣ) (n : ℕ) (R : ℝ) (hR : 0 < R) : C(Circle, ℂˣ) :=
  (monomialS1Map (a : ℂ) n R hR a.ne_zero).fromNonzeroSubtype

@[simp] theorem coe_circleMonomial_apply (a : ℂˣ) (n : ℕ) (R : ℝ) (hR : 0 < R) (z : Circle) :
    ((circleMonomial a n R hR z : ℂˣ) : ℂ) = a * (((R : ℂ) * z) ^ n) := rfl

theorem circleMonomial_windingNumber (a : ℂˣ) (n : ℕ) (R : ℝ) (hR : 0 < R) :
    (circleMonomial a n R hR).windingNumber = (n : ℤ) := by
  simpa [circleMonomial, ContinuousMap.windingNumber] using zkWNk (a : ℂ) n R hR a.ne_zero

namespace Polynomial

/-- The circle map `z ↦ p(Rz)` valued in `ℂˣ`, assuming it avoids zero on the circle. -/
noncomputable def mapCircleUnits (p : Polynomial ℂ) (R : ℝ)
    (hR : ∀ z : Circle, p.eval ((R : ℂ) * z) ≠ 0) : C(Circle, ℂˣ) :=
  (polyCircleMap p R hR).fromNonzeroSubtype

/-- The disk map `z ↦ p(Rz)` valued in `ℂˣ`, assuming it avoids zero on the closed unit disk. -/
noncomputable def mapClosedUnitDiskUnits (p : Polynomial ℂ) (R : ℝ)
    (hR : ∀ z : ClosedUnitDisk, p.eval ((R : ℂ) * z) ≠ 0) : C(ClosedUnitDisk, ℂˣ) :=
  (polyDiskMap p R hR).fromNonzeroSubtype

@[simp] theorem coe_mapCircleUnits_apply (p : Polynomial ℂ) (R : ℝ)
    (hR : ∀ z : Circle, p.eval ((R : ℂ) * z) ≠ 0) (z : Circle) :
    ((p.mapCircleUnits R hR z : ℂˣ) : ℂ) = p.eval ((R : ℂ) * z) := rfl

@[simp] theorem coe_mapClosedUnitDiskUnits_apply (p : Polynomial ℂ) (R : ℝ)
    (hR : ∀ z : ClosedUnitDisk, p.eval ((R : ℂ) * z) ≠ 0) (z : ClosedUnitDisk) :
    ((p.mapClosedUnitDiskUnits R hR z : ℂˣ) : ℂ) = p.eval ((R : ℂ) * z) := rfl

theorem leadingTerm_dominates_on_circle (p : Polynomial ℂ) (hdeg : 0 < p.natDegree) :
    ∃ R0 : ℝ, 0 < R0 ∧ ∀ R : ℝ, R0 ≤ R → ∀ z : Circle,
      ‖p.eval ((R : ℂ) * z) - p.leadingCoeff * (((R : ℂ) * z) ^ p.natDegree)‖ <
        ‖p.leadingCoeff * (((R : ℂ) * z) ^ p.natDegree)‖ :=
  zkdominates p hdeg

theorem eventually_windingNumber_eq_natDegree (p : Polynomial ℂ) (hdeg : 0 < p.natDegree) :
    ∃ R0 : ℝ, 0 < R0 ∧ ∀ R : ℝ, R0 ≤ R →
      ∃ f : C(Circle, ℂˣ), (∀ z, (f z : ℂ) = p.eval ((R : ℂ) * z)) ∧
        f.windingNumber = (p.natDegree : ℤ) := by
  obtain ⟨R0, hR0pos, hWN⟩ := WNthm p hdeg
  refine ⟨R0, hR0pos, ?_⟩
  intro R hR
  obtain ⟨f, hf, hwind⟩ := hWN R hR
  refine ⟨f.fromNonzeroSubtype, ?_, ?_⟩
  · intro z
    simpa using hf z
  · simpa [ContinuousMap.windingNumber] using hwind

theorem exists_root_of_natDegree_pos (p : Polynomial ℂ) (hdeg : 0 < p.natDegree) :
    ∃ z : ℂ, p.IsRoot z := by
  by_contra hroot
  have hnonzero : ∀ z : ℂ, p.eval z ≠ 0 := by
    intro z hz
    exact hroot ⟨z, hz⟩
  obtain ⟨R0, hR0pos, hWN⟩ := eventually_windingNumber_eq_natDegree p hdeg
  obtain ⟨f, hf, hwind⟩ := hWN R0 le_rfl
  let F : C(ClosedUnitDisk, ℂˣ) :=
    p.mapClosedUnitDiskUnits R0 fun z => hnonzero ((R0 : ℂ) * z)
  have hboundary : ∀ z : Circle, F (Circle.toClosedUnitDisk z) = f z := by
    intro z
    apply Units.ext
    have hz : (((Circle.toClosedUnitDisk z : ClosedUnitDisk) : ℂ)) = z := rfl
    calc
      ((F (Circle.toClosedUnitDisk z) : ℂˣ) : ℂ) =
          p.eval ((R0 : ℂ) * (((Circle.toClosedUnitDisk z : ClosedUnitDisk) : ℂ))) := by
        simp [F]
      _ = p.eval ((R0 : ℂ) * z) := by rw [hz]
      _ = (f z : ℂ) := (hf z).symm
  have hzero : f.windingNumber = 0 :=
    ContinuousMap.windingNumber_eq_zero_of_exists_extension hboundary
  have hdeg_ne : (p.natDegree : ℤ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hdeg
  exact hdeg_ne <| by rw [← hwind, hzero]

end Polynomial
