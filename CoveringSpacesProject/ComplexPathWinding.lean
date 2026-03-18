import Mathlib

open Complex TopologicalSpace

open scoped unitInterval

noncomputable section

namespace ContinuousMap

/-- A homotopy through loops on the interval `[a, b]`. -/
def IsLoopHomotopy {X : Type*} [TopologicalSpace X] {a b : ℝ} (hab : a ≤ b)
    (H : C(Set.Icc a b × Set.Icc (0 : ℝ) 1, X)) : Prop :=
  ∀ s, H (⟨a, ⟨le_rfl, hab⟩⟩, s) = H (⟨b, ⟨hab, le_rfl⟩⟩, s)

/-- The standard homeomorphism between complex units and nonzero complex numbers. -/
noncomputable def complexUnitsHomeomorphNeZero :
    ℂˣ ≃ₜ {z : ℂ // z ≠ 0} :=
  unitsHomeomorphNeZero (G₀ := ℂ)

@[simp] theorem coe_complexUnitsHomeomorphNeZero (u : ℂˣ) :
    ((complexUnitsHomeomorphNeZero u : {z : ℂ // z ≠ 0}) : ℂ) = u := rfl

/-- View a units-valued continuous map as a map to nonzero complex numbers. -/
noncomputable def toNonzeroSubtype {α : Type*} [TopologicalSpace α] (f : C(α, ℂˣ)) :
    C(α, {z : ℂ // z ≠ 0}) :=
  (complexUnitsHomeomorphNeZero : C(ℂˣ, {z : ℂ // z ≠ 0})).comp f

/-- View a continuous map to nonzero complex numbers as a units-valued map. -/
noncomputable def fromNonzeroSubtype {α : Type*} [TopologicalSpace α]
    (f : C(α, {z : ℂ // z ≠ 0})) : C(α, ℂˣ) :=
  (complexUnitsHomeomorphNeZero.symm : C({z : ℂ // z ≠ 0}, ℂˣ)).comp f

@[simp] theorem coe_toNonzeroSubtype_apply {α : Type*} [TopologicalSpace α] (f : C(α, ℂˣ))
    (x : α) : (f.toNonzeroSubtype x : ℂ) = f x := rfl

@[simp] theorem coe_fromNonzeroSubtype_apply {α : Type*} [TopologicalSpace α]
    (f : C(α, {z : ℂ // z ≠ 0})) (x : α) : ((f.fromNonzeroSubtype x : ℂˣ) : ℂ) = (f x : ℂ) := by
  have h' : complexUnitsHomeomorphNeZero (f.fromNonzeroSubtype x) = f x := by
    simp [fromNonzeroSubtype]
  exact congrArg Subtype.val h'

@[simp] theorem toNonzeroSubtype_fromNonzeroSubtype {α : Type*} [TopologicalSpace α]
    (f : C(α, {z : ℂ // z ≠ 0})) : f.fromNonzeroSubtype.toNonzeroSubtype = f := by
  ext x
  simp [fromNonzeroSubtype, toNonzeroSubtype]

@[simp] theorem fromNonzeroSubtype_toNonzeroSubtype {α : Type*} [TopologicalSpace α]
    (f : C(α, ℂˣ)) : f.toNonzeroSubtype.fromNonzeroSubtype = f := by
  ext x
  simp [fromNonzeroSubtype, toNonzeroSubtype]

/-- Lift a path in `ℂ \ {0}` through `Complex.exp` with a prescribed starting point. -/
noncomputable def expLift {a b : ℝ} (hab : a < b)
    (ω : C(Set.Icc a b, {z : ℂ // z ≠ 0})) (z0 : ℂ)
    (hz0 : Complex.exp z0 = (ω ⟨a, ⟨le_rfl, hab.le⟩⟩ : ℂ)) : C(Set.Icc a b, ℂ) := by
  let e := iccHomeoI a b hab
  let γ : C(↑unitInterval, {z : ℂ // z ≠ 0}) :=
    ⟨fun t => ω (e.symm t), ω.continuous.comp e.symm.continuous⟩
  have hleft : e.symm 0 = ⟨a, ⟨le_rfl, hab.le⟩⟩ := by
    apply Subtype.ext
    simp [e]
  have hγ0 : γ 0 = ⟨Complex.exp z0, Complex.exp_ne_zero z0⟩ := by
    apply Subtype.ext
    simpa [γ, hleft] using hz0.symm
  let Γ := Complex.isCoveringMap_exp.liftPath γ z0 hγ0
  exact ⟨fun t => Γ (e t), Γ.continuous.comp e.continuous⟩

@[simp] theorem expLift_apply {a b : ℝ} (hab : a < b)
    (ω : C(Set.Icc a b, {z : ℂ // z ≠ 0})) (z0 : ℂ)
    (hz0 : Complex.exp z0 = (ω ⟨a, ⟨le_rfl, hab.le⟩⟩ : ℂ)) (t : Set.Icc a b) :
    Complex.exp (expLift hab ω z0 hz0 t) = (ω t : ℂ) := by
  let e := iccHomeoI a b hab
  let γ : C(↑unitInterval, {z : ℂ // z ≠ 0}) :=
    ⟨fun s => ω (e.symm s), ω.continuous.comp e.symm.continuous⟩
  have hleft : e.symm 0 = ⟨a, ⟨le_rfl, hab.le⟩⟩ := by
    apply Subtype.ext
    simp [e]
  have hγ0 : γ 0 = ⟨Complex.exp z0, Complex.exp_ne_zero z0⟩ := by
    apply Subtype.ext
    simpa [γ, hleft] using hz0.symm
  have hΓ :=
    congrFun (Complex.isCoveringMap_exp.liftPath_lifts γ z0 hγ0) (e t)
  simpa [expLift, γ, e] using congrArg Subtype.val hΓ

@[simp] theorem expLift_source {a b : ℝ} (hab : a < b)
    (ω : C(Set.Icc a b, {z : ℂ // z ≠ 0})) (z0 : ℂ)
    (hz0 : Complex.exp z0 = (ω ⟨a, ⟨le_rfl, hab.le⟩⟩ : ℂ)) :
    expLift hab ω z0 hz0 ⟨a, ⟨le_rfl, hab.le⟩⟩ = z0 := by
  let e := iccHomeoI a b hab
  let γ : C(↑unitInterval, {z : ℂ // z ≠ 0}) :=
    ⟨fun s => ω (e.symm s), ω.continuous.comp e.symm.continuous⟩
  have hleft : e.symm 0 = ⟨a, ⟨le_rfl, hab.le⟩⟩ := by
    apply Subtype.ext
    simp [e]
  have hright : e ⟨a, ⟨le_rfl, hab.le⟩⟩ = 0 := by
    apply Subtype.ext
    simp [e]
  have hγ0 : γ 0 = ⟨Complex.exp z0, Complex.exp_ne_zero z0⟩ := by
    apply Subtype.ext
    simpa [γ, hleft] using hz0.symm
  simpa [expLift, e, hright] using Complex.isCoveringMap_exp.liftPath_zero (γ := γ) (e := z0)
    (γ_0 := hγ0)

/-- Uniqueness of path lifts through `Complex.exp` on an arbitrary interval. -/
theorem eq_expLift {a b : ℝ} (hab : a < b)
    (ω : C(Set.Icc a b, {z : ℂ // z ≠ 0})) (z0 : ℂ)
    (hz0 : Complex.exp z0 = (ω ⟨a, ⟨le_rfl, hab.le⟩⟩ : ℂ))
    (tildeω : C(Set.Icc a b, ℂ))
    (hlift : ∀ t, Complex.exp (tildeω t) = (ω t : ℂ))
    (h0 : tildeω ⟨a, ⟨le_rfl, hab.le⟩⟩ = z0) :
    tildeω = expLift hab ω z0 hz0 := by
  let e := iccHomeoI a b hab
  let γ : C(↑unitInterval, {z : ℂ // z ≠ 0}) :=
    ⟨fun s => ω (e.symm s), ω.continuous.comp e.symm.continuous⟩
  have hleft : e.symm 0 = ⟨a, ⟨le_rfl, hab.le⟩⟩ := by
    apply Subtype.ext
    simp [e]
  have hγ0 : γ 0 = ⟨Complex.exp z0, Complex.exp_ne_zero z0⟩ := by
    apply Subtype.ext
    simpa [γ, hleft] using hz0.symm
  let Γ' : C(↑unitInterval, ℂ) :=
    ⟨fun s => tildeω (e.symm s), tildeω.continuous.comp e.symm.continuous⟩
  have hΓ' : Γ' = Complex.isCoveringMap_exp.liftPath γ z0 hγ0 := by
    apply (Complex.isCoveringMap_exp.eq_liftPath_iff' (γ := γ) (e := z0) (γ_0 := hγ0)
      (Γ := Γ')).2
    constructor
    · ext s
      change Complex.exp (tildeω (e.symm s)) = (ω (e.symm s) : ℂ)
      exact hlift (e.symm s)
    · change tildeω (e.symm 0) = z0
      simpa [hleft] using h0
  ext t
  have hval := congrFun (congrArg DFunLike.coe hΓ') (e t)
  simpa [Γ', expLift, e] using hval

private theorem exp_sub_int_mul_two_pi_I_eq (z : ℂ) (n : ℤ) :
    Complex.exp (z - n * (2 * Real.pi * Complex.I)) = Complex.exp z := by
  apply (Complex.exp_eq_exp_iff_exists_int).2
  refine ⟨-n, ?_⟩
  simp [sub_eq_add_neg, Int.cast_neg]

/-- The winding number of a loop in `ℂ \ {0}`. -/
noncomputable def pathWindingNumber {a b : ℝ} (hab : a < b)
    (ω : C(Set.Icc a b, {z : ℂ // z ≠ 0}))
    (hloop : ω ⟨a, ⟨le_rfl, hab.le⟩⟩ = ω ⟨b, ⟨hab.le, le_rfl⟩⟩) : ℤ := by
  let a0 : Set.Icc a b := ⟨a, ⟨le_rfl, hab.le⟩⟩
  let b0 : Set.Icc a b := ⟨b, ⟨hab.le, le_rfl⟩⟩
  let z0 : ℂ := Complex.log (ω a0)
  have hz0 : Complex.exp z0 = (ω a0 : ℂ) := by
    simpa [z0] using Complex.exp_log (ω a0).property
  let tildeω := expLift hab ω z0 hz0
  have hper : Complex.exp (tildeω b0) = Complex.exp (tildeω a0) := by
    calc
      Complex.exp (tildeω b0) = (ω b0 : ℂ) := expLift_apply hab ω z0 hz0 b0
      _ = (ω a0 : ℂ) := by
        simpa [a0, b0] using congrArg Subtype.val hloop.symm
      _ = Complex.exp (tildeω a0) := by
        exact (expLift_apply hab ω z0 hz0 a0).symm
  exact Classical.choose ((Complex.exp_eq_exp_iff_exists_int).1 hper)

theorem pathWindingNumber_eq_of_lift {a b : ℝ} (hab : a < b)
    (ω : C(Set.Icc a b, {z : ℂ // z ≠ 0}))
    (hloop : ω ⟨a, ⟨le_rfl, hab.le⟩⟩ = ω ⟨b, ⟨hab.le, le_rfl⟩⟩)
    (tildeω : C(Set.Icc a b, ℂ))
    (hlift : ∀ t, Complex.exp (tildeω t) = (ω t : ℂ)) :
    (tildeω ⟨b, ⟨hab.le, le_rfl⟩⟩ - tildeω ⟨a, ⟨le_rfl, hab.le⟩⟩) / (2 * Real.pi * Complex.I) =
      pathWindingNumber hab ω hloop := by
  let a0 : Set.Icc a b := ⟨a, ⟨le_rfl, hab.le⟩⟩
  let b0 : Set.Icc a b := ⟨b, ⟨hab.le, le_rfl⟩⟩
  let z0 : ℂ := Complex.log (ω a0)
  have hz0 : Complex.exp z0 = (ω a0 : ℂ) := by
    simpa [z0] using Complex.exp_log (ω a0).property
  let liftω : C(Set.Icc a b, ℂ) := expLift hab ω z0 hz0
  have hliftω : ∀ t, Complex.exp (liftω t) = (ω t : ℂ) := fun t =>
    expLift_apply hab ω z0 hz0 t
  have haeq : Complex.exp (tildeω a0) = Complex.exp (liftω a0) := by
    rw [hlift a0, hliftω a0]
  obtain ⟨n, hn⟩ := (Complex.exp_eq_exp_iff_exists_int).1 haeq
  let shifted : C(Set.Icc a b, ℂ) :=
    ⟨fun t => tildeω t - n * (2 * Real.pi * Complex.I), tildeω.continuous.sub continuous_const⟩
  have hshifted_lift : ∀ t, Complex.exp (shifted t) = (ω t : ℂ) := by
    intro t
    calc
      Complex.exp (shifted t) = Complex.exp (tildeω t) := by
        exact exp_sub_int_mul_two_pi_I_eq _ _
      _ = (ω t : ℂ) := hlift t
  have hshifted0 : shifted a0 = z0 := by
    calc
      shifted a0 = tildeω a0 - n * (2 * Real.pi * Complex.I) := by rfl
      _ = liftω a0 := by rw [hn]; ring
      _ = z0 := by
        change expLift hab ω z0 hz0 ⟨a, ⟨le_rfl, hab.le⟩⟩ = z0
        exact expLift_source hab ω z0 hz0
  have huniq : shifted = liftω := by
    simpa [liftω] using eq_expLift hab ω z0 hz0 shifted hshifted_lift hshifted0
  have hshift_eq : ∀ t, tildeω t = liftω t + n * (2 * Real.pi * Complex.I) := by
    intro t
    have ht : shifted t = liftω t := by
      simpa using congrFun (congrArg DFunLike.coe huniq) t
    calc
      tildeω t = (tildeω t - n * (2 * Real.pi * Complex.I)) + n * (2 * Real.pi * Complex.I) := by
        ring
      _ = shifted t + n * (2 * Real.pi * Complex.I) := by rfl
      _ = liftω t + n * (2 * Real.pi * Complex.I) := by rw [ht]
  have hbase_eq :
      liftω b0 = liftω a0 + pathWindingNumber hab ω hloop * (2 * Real.pi * Complex.I) := by
    unfold pathWindingNumber
    dsimp [liftω]
    exact Classical.choose_spec ((Complex.exp_eq_exp_iff_exists_int).1 <|
      by
        calc
          Complex.exp ((expLift hab ω z0 hz0) b0) = (ω b0 : ℂ) := expLift_apply hab ω z0 hz0 b0
          _ = (ω a0 : ℂ) := by
            simpa [a0, b0] using congrArg Subtype.val hloop.symm
          _ = Complex.exp ((expLift hab ω z0 hz0) a0) := by
            exact (expLift_apply hab ω z0 hz0 a0).symm)
  have hbase :
      (liftω b0 - liftω a0) / (2 * Real.pi * Complex.I) = pathWindingNumber hab ω hloop := by
    rw [hbase_eq]
    ring_nf
    field_simp [Complex.two_pi_I_ne_zero]
  calc
    (tildeω b0 - tildeω a0) / (2 * Real.pi * Complex.I)
        = ((liftω b0 + n * (2 * Real.pi * Complex.I)) -
            (liftω a0 + n * (2 * Real.pi * Complex.I))) / (2 * Real.pi * Complex.I) := by
            rw [hshift_eq b0, hshift_eq a0]
    _ = (liftω b0 - liftω a0) / (2 * Real.pi * Complex.I) := by ring
    _ = pathWindingNumber hab ω hloop := hbase

theorem pathWindingNumber_eq_of_homotopy {a b : ℝ} (hab : a < b)
    (ω ω' : C(Set.Icc a b, {z : ℂ // z ≠ 0}))
    (hloop : ω ⟨a, ⟨le_rfl, hab.le⟩⟩ = ω ⟨b, ⟨hab.le, le_rfl⟩⟩)
    (hloop' : ω' ⟨a, ⟨le_rfl, hab.le⟩⟩ = ω' ⟨b, ⟨hab.le, le_rfl⟩⟩)
    (H : C(Set.Icc a b × Set.Icc (0 : ℝ) 1, {z : ℂ // z ≠ 0}))
    (hhom : IsLoopHomotopy hab.le H)
    (hzero : ∀ t, H (t, 0) = ω t)
    (hone : ∀ t, H (t, 1) = ω' t) :
    pathWindingNumber hab ω hloop = pathWindingNumber hab ω' hloop' := by
  let a0 : Set.Icc a b := ⟨a, ⟨le_rfl, hab.le⟩⟩
  let b0 : Set.Icc a b := ⟨b, ⟨hab.le, le_rfl⟩⟩
  let z0 : ℂ := Complex.log (ω a0)
  have hz0 : Complex.exp z0 = (ω a0 : ℂ) := by
    simpa [z0] using Complex.exp_log (ω a0).property
  let tildeω : C(Set.Icc a b, ℂ) := expLift hab ω z0 hz0
  have htildeω : ∀ t, Complex.exp (tildeω t) = (ω t : ℂ) := fun t =>
    expLift_apply hab ω z0 hz0 t
  let Hswap : C(Set.Icc (0 : ℝ) 1 × Set.Icc a b, {z : ℂ // z ≠ 0}) :=
    ⟨fun x => H (x.2, x.1), H.continuous.comp (continuous_snd.prodMk continuous_fst)⟩
  have hHswap0 : ∀ t, Hswap (0, t) = ⟨Complex.exp (tildeω t), (Complex.exp_ne_zero _ )⟩ := by
    intro t
    apply Subtype.ext
    calc
      (Hswap (0, t) : ℂ) = (H (t, 0) : ℂ) := rfl
      _ = (ω t : ℂ) := by simpa using congrArg Subtype.val (hzero t)
      _ = Complex.exp (tildeω t) := by symm; exact htildeω t
  let tildeH : C(Set.Icc (0 : ℝ) 1 × Set.Icc a b, ℂ) :=
    Complex.isCoveringMap_exp.liftHomotopy Hswap tildeω hHswap0
  have htildeH_lifts : ∀ x, Complex.exp (tildeH x) = (Hswap x : ℂ) := by
    intro x
    exact congrArg Subtype.val (congrFun
      (Complex.isCoveringMap_exp.liftHomotopy_lifts Hswap tildeω hHswap0) x)
  have htildeH_zero : ∀ t, tildeH (0, t) = tildeω t := by
    intro t
    simpa using Complex.isCoveringMap_exp.liftHomotopy_zero (H := Hswap) (f := tildeω)
      (H_0 := hHswap0) t
  let μ : C(Set.Icc (0 : ℝ) 1, {z : ℂ // z ≠ 0}) :=
    ⟨fun s => H (a0, s), H.continuous.comp (continuous_const.prodMk continuous_id)⟩
  let μa : C(Set.Icc (0 : ℝ) 1, ℂ) :=
    ⟨fun s => tildeH (s, a0), tildeH.continuous.comp (continuous_id.prodMk continuous_const)⟩
  let μb : C(Set.Icc (0 : ℝ) 1, ℂ) :=
    ⟨fun s => tildeH (s, b0), tildeH.continuous.comp (continuous_id.prodMk continuous_const)⟩
  have hμa : (∀ s, Complex.exp (μa s) = (μ s : ℂ)) ∧ μa 0 = tildeω a0 := by
    constructor
    · intro s
      simpa [μa, μ, Hswap] using htildeH_lifts (s, a0)
    · simpa [μa] using htildeH_zero a0
  have hμb : (∀ s, Complex.exp (μb s) = (μ s : ℂ)) ∧ μb 0 = tildeω b0 := by
    constructor
    · intro s
      calc
        Complex.exp (μb s) = (H (b0, s) : ℂ) := by
          simpa [μb, Hswap] using htildeH_lifts (s, b0)
        _ = (H (a0, s) : ℂ) := by
          simpa [a0, b0] using congrArg Subtype.val (hhom s).symm
        _ = (μ s : ℂ) := by rfl
    · simpa [μb] using htildeH_zero b0
  have hstart : Complex.exp (tildeω b0) = Complex.exp (tildeω a0) := by
    calc
      Complex.exp (tildeω b0) = (ω b0 : ℂ) := htildeω b0
      _ = (ω a0 : ℂ) := by
        simpa [a0, b0] using congrArg Subtype.val hloop.symm
      _ = Complex.exp (tildeω a0) := by symm; exact htildeω a0
  obtain ⟨n, hn⟩ := (Complex.exp_eq_exp_iff_exists_int).1 hstart
  let shiftedμa : C(Set.Icc (0 : ℝ) 1, ℂ) :=
    ⟨fun s => μa s + n * (2 * Real.pi * Complex.I), μa.continuous.add continuous_const⟩
  have hshiftedμa : (∀ s, Complex.exp (shiftedμa s) = (μ s : ℂ)) ∧ shiftedμa 0 = μb 0 := by
    constructor
    · intro s
      calc
        Complex.exp (shiftedμa s) = Complex.exp (μa s) := by
          apply (Complex.exp_eq_exp_iff_exists_int).2
          refine ⟨n, by simp [shiftedμa]⟩
        _ = (μ s : ℂ) := hμa.1 s
    · calc
        shiftedμa 0 = μa 0 + n * (2 * Real.pi * Complex.I) := by rfl
        _ = tildeω a0 + n * (2 * Real.pi * Complex.I) := by rw [hμa.2]
        _ = tildeω b0 := by rw [hn]
        _ = μb 0 := by rw [hμb.2]
  have hshifted_eq :
      shiftedμa = expLift (show (0 : ℝ) < 1 by norm_num) μ (μb 0) (hμb.1 0) :=
    eq_expLift (show (0 : ℝ) < 1 by norm_num) μ (μb 0) (hμb.1 0) shiftedμa hshiftedμa.1
      hshiftedμa.2
  have hμb_eq :
      μb = expLift (show (0 : ℝ) < 1 by norm_num) μ (μb 0) (hμb.1 0) :=
    eq_expLift (show (0 : ℝ) < 1 by norm_num) μ (μb 0) (hμb.1 0) μb hμb.1 rfl
  have huniq : shiftedμa = μb := by
    calc
      shiftedμa = expLift (show (0 : ℝ) < 1 by norm_num) μ (μb 0) (hμb.1 0) := hshifted_eq
      _ = μb := hμb_eq.symm
  have hshift_eq : ∀ s, μb s = μa s + n * (2 * Real.pi * Complex.I) := by
    intro s
    have hfun := congrArg DFunLike.coe huniq
    simpa [shiftedμa] using (congrFun hfun s).symm
  let tildeω' : C(Set.Icc a b, ℂ) :=
    ⟨fun t => tildeH (1, t), tildeH.continuous.comp (continuous_const.prodMk continuous_id)⟩
  have htildeω' : ∀ t, Complex.exp (tildeω' t) = (ω' t : ℂ) := by
    intro t
    calc
      Complex.exp (tildeω' t) = (H (t, 1) : ℂ) := by
        simpa [tildeω', Hswap] using htildeH_lifts (1, t)
      _ = (ω' t : ℂ) := by
        simpa using congrArg Subtype.val (hone t)
  have hwind :
      (tildeω' b0 - tildeω' a0) / (2 * Real.pi * Complex.I) =
        (tildeω b0 - tildeω a0) / (2 * Real.pi * Complex.I) := by
    have hdiff : tildeω' b0 - tildeω' a0 = tildeω b0 - tildeω a0 := by
      calc
        tildeω' b0 - tildeω' a0 = μb 1 - μa 1 := by rfl
        _ = μb 0 - μa 0 := by
          rw [hshift_eq 1, hshift_eq 0]
          ring
        _ = tildeω b0 - tildeω a0 := by
          rw [hμb.2, hμa.2]
    rw [hdiff]
  have hcast :
      ((pathWindingNumber hab ω hloop : ℤ) : ℂ) =
        ((pathWindingNumber hab ω' hloop' : ℤ) : ℂ) := by
    calc
      ((pathWindingNumber hab ω hloop : ℤ) : ℂ)
          = (tildeω b0 - tildeω a0) / (2 * Real.pi * Complex.I) := by
              symm
              exact pathWindingNumber_eq_of_lift hab ω hloop tildeω htildeω
      _ = (tildeω' b0 - tildeω' a0) / (2 * Real.pi * Complex.I) := by
            symm
            exact hwind
      _ = ((pathWindingNumber hab ω' hloop' : ℤ) : ℂ) := by
            exact pathWindingNumber_eq_of_lift hab ω' hloop' tildeω' htildeω'
  exact_mod_cast hcast

@[simp] theorem pathWindingNumber_const {a b : ℝ} (hab : a < b)
    (c : {z : ℂ // z ≠ 0}) :
    pathWindingNumber hab (ContinuousMap.const _ c) rfl = 0 := by
  let tildeω : C(Set.Icc a b, ℂ) := ContinuousMap.const _ (Complex.log c)
  have hlift : ∀ t, Complex.exp (tildeω t) = ((ContinuousMap.const _ c : C(Set.Icc a b, {z : ℂ // z ≠ 0})) t : ℂ) := by
    intro t
    simpa [tildeω] using Complex.exp_log c.property
  have hq :
      (tildeω ⟨b, ⟨hab.le, le_rfl⟩⟩ - tildeω ⟨a, ⟨le_rfl, hab.le⟩⟩) /
          (2 * Real.pi * Complex.I) =
        pathWindingNumber hab (ContinuousMap.const _ c) rfl :=
    pathWindingNumber_eq_of_lift hab (ContinuousMap.const _ c) rfl tildeω hlift
  simpa [tildeω] using hq.symm

/-- The winding number of a loop in `ℂˣ`. -/
noncomputable def unitsPathWindingNumber {a b : ℝ} (hab : a < b)
    (ω : C(Set.Icc a b, ℂˣ))
    (hloop : ω ⟨a, ⟨le_rfl, hab.le⟩⟩ = ω ⟨b, ⟨hab.le, le_rfl⟩⟩) : ℤ :=
  pathWindingNumber hab ω.toNonzeroSubtype <| by
    simpa [toNonzeroSubtype] using congrArg complexUnitsHomeomorphNeZero hloop

theorem unitsPathWindingNumber_eq_of_lift {a b : ℝ} (hab : a < b)
    (ω : C(Set.Icc a b, ℂˣ))
    (hloop : ω ⟨a, ⟨le_rfl, hab.le⟩⟩ = ω ⟨b, ⟨hab.le, le_rfl⟩⟩)
    (tildeω : C(Set.Icc a b, ℂ))
    (hlift : ∀ t, Complex.exp (tildeω t) = (ω t : ℂ)) :
    (tildeω ⟨b, ⟨hab.le, le_rfl⟩⟩ - tildeω ⟨a, ⟨le_rfl, hab.le⟩⟩) / (2 * Real.pi * Complex.I) =
      unitsPathWindingNumber hab ω hloop := by
  have hloop' :
      ω.toNonzeroSubtype ⟨a, ⟨le_rfl, hab.le⟩⟩ =
        ω.toNonzeroSubtype ⟨b, ⟨hab.le, le_rfl⟩⟩ := by
    simpa [toNonzeroSubtype] using congrArg complexUnitsHomeomorphNeZero hloop
  simpa [unitsPathWindingNumber, hloop'] using
    pathWindingNumber_eq_of_lift hab ω.toNonzeroSubtype hloop' tildeω (by
      intro t
      simpa [toNonzeroSubtype] using hlift t)

theorem unitsPathWindingNumber_eq_of_homotopy {a b : ℝ} (hab : a < b)
    (ω ω' : C(Set.Icc a b, ℂˣ))
    (hloop : ω ⟨a, ⟨le_rfl, hab.le⟩⟩ = ω ⟨b, ⟨hab.le, le_rfl⟩⟩)
    (hloop' : ω' ⟨a, ⟨le_rfl, hab.le⟩⟩ = ω' ⟨b, ⟨hab.le, le_rfl⟩⟩)
    (H : C(Set.Icc a b × Set.Icc (0 : ℝ) 1, ℂˣ))
    (hhom : IsLoopHomotopy hab.le H)
    (hzero : ∀ t, H (t, 0) = ω t)
    (hone : ∀ t, H (t, 1) = ω' t) :
    unitsPathWindingNumber hab ω hloop = unitsPathWindingNumber hab ω' hloop' := by
  let H' : C(Set.Icc a b × Set.Icc (0 : ℝ) 1, {z : ℂ // z ≠ 0}) := H.toNonzeroSubtype
  have hloop0 :
      ω.toNonzeroSubtype ⟨a, ⟨le_rfl, hab.le⟩⟩ =
        ω.toNonzeroSubtype ⟨b, ⟨hab.le, le_rfl⟩⟩ := by
    simpa [toNonzeroSubtype] using congrArg complexUnitsHomeomorphNeZero hloop
  have hloop1 :
      ω'.toNonzeroSubtype ⟨a, ⟨le_rfl, hab.le⟩⟩ =
        ω'.toNonzeroSubtype ⟨b, ⟨hab.le, le_rfl⟩⟩ := by
    simpa [toNonzeroSubtype] using congrArg complexUnitsHomeomorphNeZero hloop'
  have hhom' : IsLoopHomotopy hab.le H' := by
    intro s
    simpa [H', toNonzeroSubtype] using congrArg complexUnitsHomeomorphNeZero (hhom s)
  have hzero' : ∀ t, H' (t, 0) = ω.toNonzeroSubtype t := by
    intro t
    simpa [H', toNonzeroSubtype] using congrArg complexUnitsHomeomorphNeZero (hzero t)
  have hone' : ∀ t, H' (t, 1) = ω'.toNonzeroSubtype t := by
    intro t
    simpa [H', toNonzeroSubtype] using congrArg complexUnitsHomeomorphNeZero (hone t)
  simpa [unitsPathWindingNumber, hloop0, hloop1] using
    pathWindingNumber_eq_of_homotopy hab
      ω.toNonzeroSubtype
      ω'.toNonzeroSubtype
      hloop0
      hloop1
      H' hhom' hzero' hone'

@[simp] theorem unitsPathWindingNumber_const {a b : ℝ} (hab : a < b)
    (c : ℂˣ) :
    unitsPathWindingNumber hab (ContinuousMap.const _ c) rfl = 0 := by
  let c0 : {z : ℂ // z ≠ 0} := complexUnitsHomeomorphNeZero c
  change pathWindingNumber hab (ContinuousMap.const _ c0) rfl = 0
  exact pathWindingNumber_const hab c0

end ContinuousMap
