import Mathlib
import «CoveringSpacesProject».ComplexPathWinding

open Complex TopologicalSpace

open scoped unitInterval

noncomputable section

namespace Circle

/-- The canonical inclusion of the circle into the closed unit disk. -/
def toClosedUnitDisk (z : Circle) : Metric.closedBall (0 : ℂ) 1 :=
  ⟨z, by simp [Metric.mem_closedBall, Circle.norm_coe z]⟩

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

/-- The winding number of a continuous map from the circle to `ℂˣ`. -/
noncomputable def windingNumber (f : C(Circle, ℂˣ)) : ℤ :=
  f.circleLoop.unitsWindingNumber

@[simp] theorem windingNumber_const (c : ℂˣ) :
    windingNumber (ContinuousMap.const _ c : C(Circle, ℂˣ)) = 0 := by
  change (ContinuousMap.const _ c : C(Circle, ℂˣ)).circleLoop.unitsWindingNumber = 0
  have hloop : (ContinuousMap.const _ c : C(Circle, ℂˣ)).circleLoop = Path.refl c := by
    ext t
    rfl
  rw [hloop]
  exact Path.unitsWindingNumber_refl c

theorem windingNumber_eq_of_homotopy {f g : C(Circle, ℂˣ)} (H : ContinuousMap.Homotopy f g) :
    windingNumber f = windingNumber g := by
  let Hbase : C(I × I, ℂˣ) :=
    ⟨fun x => H (x.1, Circle.exp (2 * Real.pi * (x.2 : ℝ))),
      H.continuous.comp
        (continuous_fst.prodMk
          (Circle.exp.continuous.comp <| by fun_prop))⟩
  have hhom : Hbase.IsLoopHomotopy := by
    intro s
    change H (s, Circle.exp (2 * Real.pi * (0 : ℝ))) =
      H (s, Circle.exp (2 * Real.pi * (1 : ℝ)))
    simp [Circle.exp_two_pi]
  have hzero : ∀ t, Hbase (0, t) = f.circleLoop t := by
    intro t
    change H (0, Circle.exp (2 * Real.pi * (t : ℝ))) = f (Circle.exp (2 * Real.pi * (t : ℝ)))
    exact H.map_zero_left (Circle.exp (2 * Real.pi * (t : ℝ)))
  have hone : ∀ t, Hbase (1, t) = g.circleLoop t := by
    intro t
    change H (1, Circle.exp (2 * Real.pi * (t : ℝ))) = g (Circle.exp (2 * Real.pi * (t : ℝ)))
    exact H.map_one_left (Circle.exp (2 * Real.pi * (t : ℝ)))
  simpa [windingNumber] using
    Path.unitsWindingNumber_eq_of_homotopy f.circleLoop g.circleLoop Hbase hhom hzero hone

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

theorem windingNumber_eq_zero_of_exists_extension {f : C(Circle, ℂˣ)}
    {F : C(Metric.closedBall (0 : ℂ) 1, ℂˣ)}
    (hF : ∀ z : Circle, F (Circle.toClosedUnitDisk z) = f z) :
    windingNumber f = 0 := by
  let Jfun : Set.Icc (0 : ℝ) 1 × Circle → ℂ := fun x =>
    (((1 - (x.1 : ℝ)) : ℂ) * (x.2 : ℂ))
  have hJfun_mem : ∀ x : Set.Icc (0 : ℝ) 1 × Circle, Jfun x ∈ Metric.closedBall (0 : ℂ) 1 := by
    intro x
    have hs0 : 0 ≤ (x.1 : ℝ) := x.1.2.1
    have hs1 : (x.1 : ℝ) ≤ 1 := x.1.2.2
    have hnonneg : 0 ≤ 1 - (x.1 : ℝ) := by
      linarith
    have hreal : ‖((1 - (x.1 : ℝ)) : ℂ)‖ = |1 - (x.1 : ℝ)| := by
      simpa using (RCLike.norm_ofReal (K := ℂ) (1 - (x.1 : ℝ)))
    have hnorm : ‖Jfun x‖ ≤ 1 := by
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
    simpa [Metric.mem_closedBall] using hnorm
  let J : C(Set.Icc (0 : ℝ) 1 × Circle, Metric.closedBall (0 : ℂ) 1) :=
    ⟨fun x => ⟨Jfun x, hJfun_mem x⟩, Continuous.subtype_mk (by fun_prop) hJfun_mem⟩
  let H : C(Set.Icc (0 : ℝ) 1 × Circle, ℂˣ) := F.comp J
  have hJ0 : ∀ z : Circle, J (0, z) = Circle.toClosedUnitDisk z := by
    intro z
    apply Subtype.ext
    change Jfun (0, z) = (z : ℂ)
    simp [Jfun]
  have hJ1 : ∀ z : Circle, J (1, z) = 0 := by
    intro z
    apply Subtype.ext
    change Jfun (1, z) = (0 : ℂ)
    simp [Jfun]
  let hHom : ContinuousMap.Homotopy f (ContinuousMap.const _ (F 0)) :=
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
          _ = F 0 := by rw [hJ1 z]
          _ = ContinuousMap.const _ (F 0) z := rfl }
  calc
    windingNumber f = windingNumber (ContinuousMap.const _ (F 0)) := by
      exact windingNumber_eq_of_homotopy hHom
    _ = 0 := windingNumber_const (F 0)

theorem windingNumber_eq_zero_of_exists_extension' {f : C(Circle, ℂˣ)}
    {F : C(Metric.closedBall (0 : ℂ) 1, {z : ℂ // z ≠ 0})}
    (hF : ∀ z : Circle, F (Circle.toClosedUnitDisk z) = f.toNonzeroSubtype z) :
    windingNumber f = 0 := by
  let F' : C(Metric.closedBall (0 : ℂ) 1, ℂˣ) := F.fromNonzeroSubtype
  have hF' : ∀ z : Circle, F' (Circle.toClosedUnitDisk z) = f z := by
    intro z
    apply Units.ext
    simpa [F'] using congrArg Subtype.val (hF z)
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
  let c0 : {z : ℂ // z ≠ 0} := ⟨(a : ℂ) * (R : ℂ) ^ n, by
    refine mul_ne_zero a.ne_zero ?_
    exact pow_ne_zero n (by exact_mod_cast hR.ne')⟩
  let a0 : ℂ := Complex.log c0
  have ha0 : Complex.exp a0 = (c0 : ℂ) := by
    simpa [a0] using Complex.exp_log c0.property
  let tildeω : C(I, ℂ) := by
    refine ⟨fun t => a0 + (n : ℂ) * ((2 * Real.pi : ℂ) * (t : ℂ)) * Complex.I, ?_⟩
    fun_prop
  have hlift :
      ∀ t,
        Complex.exp (tildeω t) = (((circleMonomial a n R hR).circleLoop t : ℂˣ) : ℂ) := by
    intro t
    calc
      Complex.exp (tildeω t)
          = Complex.exp a0 *
              Complex.exp (((n : ℂ) * ((2 * Real.pi : ℂ) * (t : ℂ))) * Complex.I) := by
              simp [tildeω, Complex.exp_add]
      _ = ((a : ℂ) * (R : ℂ) ^ n) *
            Complex.exp (((n : ℂ) * ((2 * Real.pi : ℂ) * (t : ℂ))) * Complex.I) := by
            simpa [c0] using
              congrArg
                (fun z : ℂ => z * Complex.exp (((n : ℂ) * ((2 * Real.pi : ℂ) * (t : ℂ))) * Complex.I))
                ha0
      _ = ((a : ℂ) * (R : ℂ) ^ n) *
            Complex.exp ((n : ℂ) * (((2 * Real.pi : ℂ) * (t : ℂ)) * Complex.I)) := by
            ring_nf
      _ = ((a : ℂ) * (R : ℂ) ^ n) *
            (Complex.exp (((2 * Real.pi : ℂ) * (t : ℂ)) * Complex.I)) ^ n := by
            rw [Complex.exp_nat_mul]
      _ = ((a : ℂ) * (R : ℂ) ^ n) * (Circle.exp (2 * Real.pi * (t : ℝ)) : ℂ) ^ n := by
            have hexp :
                Complex.exp (((2 * Real.pi : ℂ) * (t : ℂ)) * Complex.I) =
                  (Circle.exp (2 * Real.pi * (t : ℝ)) : ℂ) := by
              simpa using (Circle.coe_exp (2 * Real.pi * (t : ℝ))).symm
            rw [hexp]
      _ = (a : ℂ) * (((R : ℂ) * (Circle.exp (2 * Real.pi * (t : ℝ)) : ℂ)) ^ n) := by
            rw [mul_pow]
            ring
      _ = ((circleMonomial a n R hR (Circle.exp (2 * Real.pi * (t : ℝ))) : ℂˣ) : ℂ) := by
            symm
            exact coe_circleMonomial_apply a n R hR (Circle.exp (2 * Real.pi * (t : ℝ)))
      _ = (((circleMonomial a n R hR).circleLoop t : ℂˣ) : ℂ) := by
            rfl
  have hwind : ((circleMonomial a n R hR).windingNumber : ℂ) = n := by
    calc
      ((circleMonomial a n R hR).windingNumber : ℂ)
          = (tildeω 1 - tildeω 0) / ((2 * Real.pi : ℂ) * Complex.I) := by
              symm
              simpa [ContinuousMap.windingNumber] using
                Path.unitsWindingNumber_eq_of_lift (circleMonomial a n R hR).circleLoop tildeω hlift
      _ = ((n : ℂ) * (2 * Real.pi : ℂ) * Complex.I) / ((2 * Real.pi : ℂ) * Complex.I) := by
            simp [tildeω]
      _ = (n : ℂ) := by
            have hpi : (Real.pi : ℂ) ≠ 0 := by
              exact_mod_cast Real.pi_ne_zero
            field_simp [tildeω, hpi, Complex.I_ne_zero]
  exact_mod_cast hwind

namespace Polynomial

/-- The circle map `z ↦ p(Rz)` valued in `ℂˣ`, assuming it avoids zero on the circle. -/
noncomputable def mapCircleUnits (p : Polynomial ℂ) (R : ℝ)
    (hR : ∀ z : Circle, p.eval ((R : ℂ) * z) ≠ 0) : C(Circle, ℂˣ) :=
  ContinuousMap.unitsOfForallIsUnit
    (f := ⟨fun z => p.eval ((R : ℂ) * z), p.continuous.comp (continuous_const.mul continuous_subtype_val)⟩)
    fun z => isUnit_iff_ne_zero.mpr (hR z)

/-- The disk map `z ↦ p(Rz)` valued in `ℂˣ`, assuming it avoids zero on the closed unit disk. -/
noncomputable def mapClosedUnitDiskUnits (p : Polynomial ℂ) (R : ℝ)
    (hR : ∀ z : Metric.closedBall (0 : ℂ) 1, p.eval ((R : ℂ) * z) ≠ 0) :
    C(Metric.closedBall (0 : ℂ) 1, ℂˣ) :=
  ContinuousMap.unitsOfForallIsUnit
    (f := ⟨fun z => p.eval ((R : ℂ) * z), p.continuous.comp (continuous_const.mul continuous_subtype_val)⟩)
    fun z => isUnit_iff_ne_zero.mpr (hR z)

@[simp] theorem coe_mapCircleUnits_apply (p : Polynomial ℂ) (R : ℝ)
    (hR : ∀ z : Circle, p.eval ((R : ℂ) * z) ≠ 0) (z : Circle) :
    ((p.mapCircleUnits R hR z : ℂˣ) : ℂ) = p.eval ((R : ℂ) * z) := rfl

@[simp] theorem coe_mapClosedUnitDiskUnits_apply (p : Polynomial ℂ) (R : ℝ)
    (hR : ∀ z : Metric.closedBall (0 : ℂ) 1, p.eval ((R : ℂ) * z) ≠ 0)
    (z : Metric.closedBall (0 : ℂ) 1) :
    ((p.mapClosedUnitDiskUnits R hR z : ℂˣ) : ℂ) = p.eval ((R : ℂ) * z) := rfl

theorem leadingTerm_dominates_on_circle (p : Polynomial ℂ) (hdeg : 0 < p.natDegree) :
    ∃ R0 : ℝ, 0 < R0 ∧ ∀ R : ℝ, R0 ≤ R → ∀ z : Circle,
      ‖p.eval ((R : ℂ) * z) - p.leadingCoeff * (((R : ℂ) * z) ^ p.natDegree)‖ <
        ‖p.leadingCoeff * (((R : ℂ) * z) ^ p.natDegree)‖ :=
  by
    let S : ℝ := ∑ i ∈ Finset.range p.natDegree, ‖p.coeff i‖
    let R0 : ℝ := max 1 (S / ‖p.leadingCoeff‖ + 1)
    refine ⟨R0, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
    intro R hR z
    have hp : p ≠ 0 := by
      intro hp0
      rw [hp0] at hdeg
      exact (lt_irrefl 0 hdeg).elim
    have hlead : p.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp
    have hleadPos : 0 < ‖p.leadingCoeff‖ := norm_pos_iff.mpr hlead
    have hR1 : 1 ≤ R := le_trans (le_max_left _ _) hR
    have hR0 : 0 ≤ R := le_trans (by norm_num) hR1
    have hdivlt : S / ‖p.leadingCoeff‖ < R := by
      have htmp : S / ‖p.leadingCoeff‖ + 1 ≤ R := le_trans (le_max_right _ _) hR
      exact lt_of_lt_of_le (lt_add_of_pos_right (S / ‖p.leadingCoeff‖) zero_lt_one) htmp
    have hSlt : S < ‖p.leadingCoeff‖ * R := by
      simpa [mul_comm] using (div_lt_iff₀ hleadPos).mp hdivlt
    let x : ℂ := (R : ℂ) * z
    have hxnorm : ‖x‖ = R := by
      calc
        ‖x‖ = ‖(R : ℂ)‖ * ‖(z : ℂ)‖ := by simp [x]
        _ = |R| * 1 := by simp
        _ = R := by
          rw [abs_of_nonneg hR0]
          ring
    have hsplit :
        p.eval x =
          ∑ i ∈ Finset.range p.natDegree, p.coeff i * x ^ i + p.leadingCoeff * x ^ p.natDegree := by
      rw [Polynomial.eval_eq_sum_range, Finset.sum_range_succ, Polynomial.coeff_natDegree]
    have hsumle :
        ‖∑ i ∈ Finset.range p.natDegree, p.coeff i * x ^ i‖ ≤ S * R ^ (p.natDegree - 1) := by
      calc
        ‖∑ i ∈ Finset.range p.natDegree, p.coeff i * x ^ i‖
            ≤ ∑ i ∈ Finset.range p.natDegree, ‖p.coeff i * x ^ i‖ := by
              exact norm_sum_le _ _
        _ ≤ ∑ i ∈ Finset.range p.natDegree, ‖p.coeff i‖ * R ^ (p.natDegree - 1) := by
              refine Finset.sum_le_sum ?_
              intro i hi
              have hi' : i < p.natDegree := Finset.mem_range.mp hi
              have hpow : R ^ i ≤ R ^ (p.natDegree - 1) := by
                exact pow_le_pow_right₀ hR1 (Nat.le_pred_of_lt hi')
              calc
                ‖p.coeff i * x ^ i‖ = ‖p.coeff i‖ * ‖x ^ i‖ := norm_mul _ _
                _ = ‖p.coeff i‖ * R ^ i := by rw [norm_pow, hxnorm]
                _ ≤ ‖p.coeff i‖ * R ^ (p.natDegree - 1) := by
                    exact mul_le_mul_of_nonneg_left hpow (norm_nonneg _)
        _ = S * R ^ (p.natDegree - 1) := by
              unfold S
              rw [Finset.sum_mul]
    have hstrict : S * R ^ (p.natDegree - 1) < ‖p.leadingCoeff‖ * R ^ p.natDegree := by
      have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR1
      have hpow_pos : 0 < R ^ (p.natDegree - 1) := pow_pos hRpos _
      have hmul : S * R ^ (p.natDegree - 1) < (‖p.leadingCoeff‖ * R) * R ^ (p.natDegree - 1) := by
        exact mul_lt_mul_of_pos_right hSlt hpow_pos
      have hdeg' : (p.natDegree - 1) + 1 = p.natDegree := by
        exact Nat.sub_add_cancel (Nat.succ_le_of_lt hdeg)
      calc
        S * R ^ (p.natDegree - 1) < (‖p.leadingCoeff‖ * R) * R ^ (p.natDegree - 1) := hmul
        _ = ‖p.leadingCoeff‖ * R ^ ((p.natDegree - 1) + 1) := by
          rw [pow_add, pow_one]
          ring
        _ = ‖p.leadingCoeff‖ * R ^ p.natDegree := by rw [hdeg']
    have hleadnorm : ‖p.leadingCoeff * x ^ p.natDegree‖ = ‖p.leadingCoeff‖ * R ^ p.natDegree := by
      calc
        ‖p.leadingCoeff * x ^ p.natDegree‖ = ‖p.leadingCoeff‖ * ‖x ^ p.natDegree‖ := norm_mul _ _
        _ = ‖p.leadingCoeff‖ * R ^ p.natDegree := by rw [norm_pow, hxnorm]
    calc
      ‖p.eval ((R : ℂ) * z) - p.leadingCoeff * (((R : ℂ) * z) ^ p.natDegree)‖
          = ‖∑ i ∈ Finset.range p.natDegree, p.coeff i * x ^ i‖ := by
              change ‖p.eval x - p.leadingCoeff * x ^ p.natDegree‖ = _
              rw [hsplit]
              ring_nf
              simp [mul_comm]
      _ ≤ S * R ^ (p.natDegree - 1) := hsumle
      _ < ‖p.leadingCoeff‖ * R ^ p.natDegree := hstrict
      _ = ‖p.leadingCoeff * (((R : ℂ) * z) ^ p.natDegree)‖ := by
            simpa [x] using hleadnorm.symm

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
  let F : C(Metric.closedBall (0 : ℂ) 1, ℂˣ) :=
    p.mapClosedUnitDiskUnits R0 fun z => hnonzero ((R0 : ℂ) * z)
  have hboundary : ∀ z : Circle, F (Circle.toClosedUnitDisk z) = f z := by
    intro z
    apply Units.ext
    have hz : (((Circle.toClosedUnitDisk z : Metric.closedBall (0 : ℂ) 1) : ℂ)) = z := rfl
    calc
      ((F (Circle.toClosedUnitDisk z) : ℂˣ) : ℂ) =
          p.eval ((R0 : ℂ) * (((Circle.toClosedUnitDisk z : Metric.closedBall (0 : ℂ) 1) : ℂ))) := by
        simp [F]
      _ = p.eval ((R0 : ℂ) * z) := by rw [hz]
      _ = (f z : ℂ) := (hf z).symm
  have hzero : f.windingNumber = 0 :=
    ContinuousMap.windingNumber_eq_zero_of_exists_extension hboundary
  have hdeg_ne : (p.natDegree : ℤ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hdeg
  exact hdeg_ne <| by rw [← hwind, hzero]

end Polynomial
