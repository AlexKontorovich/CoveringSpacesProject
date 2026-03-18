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
  let Hbase : C(Set.Icc (0 : ℝ) 1 × Circle, ℂ) :=
    ⟨fun x =>
      (((1 - (x.1 : ℝ)) : ℂ) * (f x.2 : ℂ)) + (((x.1 : ℝ) : ℂ) * (g x.2 : ℂ)), by
        fun_prop⟩
  have hHbase : ∀ x : Set.Icc (0 : ℝ) 1 × Circle, Hbase x ≠ 0 := by
    intro x hx
    have hs0 : 0 ≤ (x.1 : ℝ) := x.1.2.1
    have hs1 : (x.1 : ℝ) ≤ 1 := x.1.2.2
    have hsNorm : ‖((x.1 : ℝ) : ℂ)‖ ≤ 1 := by
      simpa [RCLike.norm_ofReal, abs_of_nonneg hs0] using hs1
    have hle :
        ‖((x.1 : ℝ) : ℂ) * ((f x.2 : ℂ) - g x.2)‖ ≤ ‖(f x.2 : ℂ) - g x.2‖ := by
      calc
        ‖((x.1 : ℝ) : ℂ) * ((f x.2 : ℂ) - g x.2)‖
            = ‖((x.1 : ℝ) : ℂ)‖ * ‖(f x.2 : ℂ) - g x.2‖ := norm_mul _ _
        _ ≤ 1 * ‖(f x.2 : ℂ) - g x.2‖ := by gcongr
        _ = ‖(f x.2 : ℂ) - g x.2‖ := by ring
    have hEq : (f x.2 : ℂ) = ((x.1 : ℝ) : ℂ) * ((f x.2 : ℂ) - g x.2) := by
      calc
        (f x.2 : ℂ) = (f x.2 : ℂ) - Hbase x := by rw [hx]; ring
        _ = ((x.1 : ℝ) : ℂ) * ((f x.2 : ℂ) - g x.2) := by
              simp [Hbase]
              ring
    have hlt : ‖(f x.2 : ℂ)‖ < ‖(f x.2 : ℂ)‖ := by
      calc
        ‖(f x.2 : ℂ)‖
            = ‖((x.1 : ℝ) : ℂ) * ((f x.2 : ℂ) - g x.2)‖ := by
                exact congrArg norm hEq
        _ ≤ ‖(f x.2 : ℂ) - g x.2‖ := hle
        _ < ‖(f x.2 : ℂ)‖ := hclose x.2
    exact (lt_irrefl ‖(f x.2 : ℂ)‖ hlt).elim
  let H : C(Set.Icc (0 : ℝ) 1 × Circle, ℂˣ) :=
    ContinuousMap.unitsOfForallIsUnit (f := Hbase) fun x => isUnit_iff_ne_zero.mpr (hHbase x)
  refine ⟨{ toContinuousMap := H, map_zero_left := ?_, map_one_left := ?_ }⟩
  · intro z
    apply Units.ext
    simp [H, Hbase]
  · intro z
    apply Units.ext
    simp [H, Hbase]

theorem windingNumber_eq_of_norm_sub_lt {f g : C(Circle, ℂˣ)}
    (hclose : ∀ z : Circle, ‖(f z : ℂ) - g z‖ < ‖(f z : ℂ)‖) :
    windingNumber f = windingNumber g := by
  obtain ⟨H⟩ := exists_homotopy_of_norm_sub_lt hclose
  exact windingNumber_eq_of_homotopy H

theorem windingNumber_eq_zero_of_exists_extension {f : C(Circle, ℂˣ)} {F : C(ClosedUnitDisk, ℂˣ)}
    (hF : ∀ z : Circle, F (Circle.toClosedUnitDisk z) = f z) :
    windingNumber f = 0 := by
  let Jfun : Set.Icc (0 : ℝ) 1 × Circle → ℂ := fun x =>
    (((1 - (x.1 : ℝ)) : ℂ) * (x.2 : ℂ))
  have hJfun_mem : ∀ x : Set.Icc (0 : ℝ) 1 × Circle, ‖Jfun x‖ ≤ 1 := by
    intro x
    have hs0 : 0 ≤ (x.1 : ℝ) := x.1.2.1
    have hs1 : (x.1 : ℝ) ≤ 1 := x.1.2.2
    have hnonneg : 0 ≤ 1 - (x.1 : ℝ) := by
      linarith
    have hreal : ‖((1 - (x.1 : ℝ)) : ℂ)‖ = |1 - (x.1 : ℝ)| := by
      simpa using (RCLike.norm_ofReal (K := ℂ) (1 - (x.1 : ℝ)))
    calc
      ‖Jfun x‖ = ‖((1 - (x.1 : ℝ)) : ℂ)‖ * ‖(x.2 : ℂ)‖ := by
        simp [Jfun]
      _ = |1 - (x.1 : ℝ)| * 1 := by
        rw [hreal]
        simp
      _ = (1 - (x.1 : ℝ)) * 1 := by
        rw [abs_of_nonneg hnonneg]
      _ ≤ 1 := by
        linarith
  let J : C(Set.Icc (0 : ℝ) 1 × Circle, ClosedUnitDisk) :=
    ⟨fun x => ⟨Jfun x, hJfun_mem x⟩, Continuous.subtype_mk (by fun_prop) hJfun_mem⟩
  let H : C(Set.Icc (0 : ℝ) 1 × Circle, ℂˣ) := F.comp J
  have hJ0 : ∀ z : Circle, J (0, z) = Circle.toClosedUnitDisk z := by
    intro z
    apply Subtype.ext
    change Jfun (0, z) = (z : ℂ)
    simp [Jfun]
  have hJ1 : ∀ z : Circle, J (1, z) = closedUnitDiskZero := by
    intro z
    apply Subtype.ext
    change Jfun (1, z) = (0 : ℂ)
    simp [Jfun]
  let hHom : ContinuousMap.Homotopy f (ContinuousMap.const _ (F closedUnitDiskZero)) :=
    { toContinuousMap := H
      map_zero_left := by
        intro z
        calc
          H (0, z) = F (J (0, z)) := rfl
          _ = F (Circle.toClosedUnitDisk z) := by rw [hJ0 z]
          _ = f z := hF z
      map_one_left := by
        intro z
        calc
          H (1, z) = F (J (1, z)) := rfl
          _ = F closedUnitDiskZero := by rw [hJ1 z]
          _ = ContinuousMap.const _ (F closedUnitDiskZero) z := rfl }
  calc
    windingNumber f = windingNumber (ContinuousMap.const _ (F closedUnitDiskZero)) := by
      exact windingNumber_eq_of_homotopy hHom
    _ = 0 := windingNumber_const (F closedUnitDiskZero)

theorem windingNumber_eq_zero_of_exists_extension' {f : C(Circle, ℂˣ)} {F : C(ClosedUnitDisk, Cstar)}
    (hF : ∀ z : Circle, F (Circle.toClosedUnitDisk z) = f.toNonzeroSubtype z) :
    windingNumber f = 0 := by
  have hF' : ∀ z : Circle, F.fromNonzeroSubtype (Circle.toClosedUnitDisk z) = f z := by
    intro z
    apply Units.ext
    simpa using congrArg Subtype.val (hF z)
  exact windingNumber_eq_zero_of_exists_extension hF'

end ContinuousMap

/-- The monomial map `z ↦ a * (Rz)^n` on the unit circle, valued in `ℂˣ`. -/
noncomputable def circleMonomial (a : ℂˣ) (n : ℕ) (R : ℝ) (hR : 0 < R) : C(Circle, ℂˣ) :=
  ContinuousMap.unitsOfForallIsUnit
    (f := ⟨fun z => a * (((R : ℂ) * z) ^ n), by
      fun_prop⟩)
    fun z => by
      have hR0 : (R : ℂ) ≠ 0 := by
        exact_mod_cast hR.ne'
      exact isUnit_iff_ne_zero.mpr <|
        mul_ne_zero a.ne_zero (pow_ne_zero n <| mul_ne_zero hR0 (Circle.coe_ne_zero z))

@[simp] theorem coe_circleMonomial_apply (a : ℂˣ) (n : ℕ) (R : ℝ) (hR : 0 < R) (z : Circle) :
    ((circleMonomial a n R hR z : ℂˣ) : ℂ) = a * (((R : ℂ) * z) ^ n) := rfl

theorem circleMonomial_windingNumber (a : ℂˣ) (n : ℕ) (R : ℝ) (hR : 0 < R) :
    (circleMonomial a n R hR).windingNumber = (n : ℤ) := by
  have hEq :
      circleMonomial a n R hR = (monomialS1Map (a : ℂ) n R hR a.ne_zero).fromNonzeroSubtype := by
    ext z
    rfl
  rw [hEq]
  simpa [ContinuousMap.windingNumber] using zkWNk (a : ℂ) n R hR a.ne_zero

namespace Polynomial

/-- The circle map `z ↦ p(Rz)` valued in `ℂˣ`, assuming it avoids zero on the circle. -/
noncomputable def mapCircleUnits (p : Polynomial ℂ) (R : ℝ)
    (hR : ∀ z : Circle, p.eval ((R : ℂ) * z) ≠ 0) : C(Circle, ℂˣ) :=
  ContinuousMap.unitsOfForallIsUnit
    (f := ⟨fun z => p.eval ((R : ℂ) * z), p.continuous.comp (continuous_const.mul continuous_subtype_val)⟩)
    fun z => isUnit_iff_ne_zero.mpr (hR z)

/-- The disk map `z ↦ p(Rz)` valued in `ℂˣ`, assuming it avoids zero on the closed unit disk. -/
noncomputable def mapClosedUnitDiskUnits (p : Polynomial ℂ) (R : ℝ)
    (hR : ∀ z : ClosedUnitDisk, p.eval ((R : ℂ) * z) ≠ 0) : C(ClosedUnitDisk, ℂˣ) :=
  ContinuousMap.unitsOfForallIsUnit
    (f := ⟨fun z => p.eval ((R : ℂ) * z), p.continuous.comp (continuous_const.mul continuous_subtype_val)⟩)
    fun z => isUnit_iff_ne_zero.mpr (hR z)

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
  obtain ⟨R0, hR0pos, hdom⟩ := leadingTerm_dominates_on_circle p hdeg
  refine ⟨R0, hR0pos, ?_⟩
  intro R hR
  have hp : p ≠ 0 := by
    intro hp0
    simp [hp0] at hdeg
  have hlead : p.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp
  let a0 : ℂˣ := Units.mk0 p.leadingCoeff hlead
  have hRpos : 0 < R := lt_of_lt_of_le hR0pos hR
  have hpoly_nonzero : ∀ z : Circle, p.eval ((R : ℂ) * z) ≠ 0 := by
    intro z hz
    have hbad :
        ‖p.leadingCoeff * (((R : ℂ) * z) ^ p.natDegree)‖ <
          ‖p.leadingCoeff * (((R : ℂ) * z) ^ p.natDegree)‖ := by
      simpa [hz, norm_sub_rev] using hdom R hR z
    exact (lt_irrefl _ hbad).elim
  let f : C(Circle, ℂˣ) := p.mapCircleUnits R hpoly_nonzero
  have hclose :
      ∀ z : Circle,
        ‖(circleMonomial a0 p.natDegree R hRpos z : ℂ) - f z‖ <
          ‖(circleMonomial a0 p.natDegree R hRpos z : ℂ)‖ := by
    intro z
    simpa [f, norm_sub_rev] using hdom R hR z
  refine ⟨f, ?_, ?_⟩
  · intro z
    rfl
  · calc
      f.windingNumber = (circleMonomial a0 p.natDegree R hRpos).windingNumber := by
        symm
        exact ContinuousMap.windingNumber_eq_of_norm_sub_lt hclose
      _ = (p.natDegree : ℤ) := circleMonomial_windingNumber a0 p.natDegree R hRpos

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
