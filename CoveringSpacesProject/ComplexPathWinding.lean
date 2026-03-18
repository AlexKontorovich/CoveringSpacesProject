import Mathlib

/-!
# Winding numbers from the covering map `Complex.exp`

This file is a thin wrapper around Mathlib's covering-space API for
`Complex.isCoveringMap_exp`. It does three things:

* packages homotopies through loops on `I`,
* defines winding numbers of loops in `ℂ \ {0}` via lifts through `Complex.exp`,
* provides `ℂˣ`-valued wrappers around the subtype-valued covering-map statements.
-/

open Complex TopologicalSpace

open scoped unitInterval

noncomputable section

namespace ContinuousMap

/-- A homotopy through loops on `I`. -/
def IsLoopHomotopy {X : Type*} [TopologicalSpace X] (H : C(I × I, X)) : Prop :=
  ∀ s, H (s, 0) = H (s, 1)

private noncomputable def complexUnitsHomeomorphNeZero :
    ℂˣ ≃ₜ {z : ℂ // z ≠ 0} :=
  unitsHomeomorphNeZero (G₀ := ℂ)

/-- View a units-valued continuous map as a map to nonzero complex numbers. -/
noncomputable def toNonzeroSubtype {α : Type*} [TopologicalSpace α] (f : C(α, ℂˣ)) :
    C(α, {z : ℂ // z ≠ 0}) :=
  (complexUnitsHomeomorphNeZero : C(ℂˣ, {z : ℂ // z ≠ 0})).comp f

/-- View a continuous map to nonzero complex numbers as a units-valued map. -/
noncomputable def fromNonzeroSubtype {α : Type*} [TopologicalSpace α]
    (f : C(α, {z : ℂ // z ≠ 0})) : C(α, ℂˣ) :=
  (complexUnitsHomeomorphNeZero.symm : C({z : ℂ // z ≠ 0}, ℂˣ)).comp f

@[simp] theorem coe_toNonzeroSubtype_apply {α : Type*} [TopologicalSpace α] (f : C(α, ℂˣ))
    (x : α) : (f.toNonzeroSubtype x : ℂ) = (f x : ℂ) := rfl

@[simp] theorem coe_fromNonzeroSubtype_apply {α : Type*} [TopologicalSpace α]
    (f : C(α, {z : ℂ // z ≠ 0})) (x : α) : ((f.fromNonzeroSubtype x : ℂˣ) : ℂ) = (f x : ℂ) := by
  have h :
      complexUnitsHomeomorphNeZero (f.fromNonzeroSubtype x) = f x := by
    simp [fromNonzeroSubtype]
  exact congrArg Subtype.val h

@[simp] theorem toNonzeroSubtype_fromNonzeroSubtype {α : Type*} [TopologicalSpace α]
    (f : C(α, {z : ℂ // z ≠ 0})) : f.fromNonzeroSubtype.toNonzeroSubtype = f := by
  ext x
  simp [fromNonzeroSubtype, toNonzeroSubtype]

@[simp] theorem fromNonzeroSubtype_toNonzeroSubtype {α : Type*} [TopologicalSpace α]
    (f : C(α, ℂˣ)) : f.toNonzeroSubtype.fromNonzeroSubtype = f := by
  ext x
  simp [fromNonzeroSubtype, toNonzeroSubtype]

end ContinuousMap

namespace Path

open ContinuousMap

/-- View a units-valued path as a path to nonzero complex numbers. -/
noncomputable def toNonzeroSubtype {u v : ℂˣ} (γ : Path u v) :
    Path (complexUnitsHomeomorphNeZero u) (complexUnitsHomeomorphNeZero v) :=
  γ.map (complexUnitsHomeomorphNeZero : C(ℂˣ, {z : ℂ // z ≠ 0})).continuous

@[simp] theorem coe_toNonzeroSubtype_apply {u v : ℂˣ} (γ : Path u v) (t : I) :
    ((γ.toNonzeroSubtype t : {z : ℂ // z ≠ 0}) : ℂ) = (γ t : ℂ) := rfl

/-- Lift a path in `ℂ \ {0}` through `Complex.exp` with a prescribed starting point. -/
noncomputable def expLift {z₀ z₁ : {z : ℂ // z ≠ 0}} (γ : Path z₀ z₁) (w0 : ℂ)
    (hw0 : Complex.exp w0 = (z₀ : ℂ)) : C(I, ℂ) :=
  Complex.isCoveringMap_exp.liftPath γ.toContinuousMap w0 <| by
    apply Subtype.ext
    simpa using hw0.symm

@[simp] theorem expLift_apply {z₀ z₁ : {z : ℂ // z ≠ 0}} (γ : Path z₀ z₁) (w0 : ℂ)
    (hw0 : Complex.exp w0 = (z₀ : ℂ)) (t : I) :
    Complex.exp (γ.expLift w0 hw0 t) = (γ t : ℂ) := by
  have h :=
    congrFun (Complex.isCoveringMap_exp.liftPath_lifts γ.toContinuousMap w0 <| by
      apply Subtype.ext
      simpa using hw0.symm) t
  simpa using congrArg Subtype.val h

@[simp] theorem expLift_zero {z₀ z₁ : {z : ℂ // z ≠ 0}} (γ : Path z₀ z₁) (w0 : ℂ)
    (hw0 : Complex.exp w0 = (z₀ : ℂ)) :
    γ.expLift w0 hw0 0 = w0 := by
  simpa [expLift] using Complex.isCoveringMap_exp.liftPath_zero (γ := γ.toContinuousMap)
    (e := w0) (γ_0 := by
      apply Subtype.ext
      simpa using hw0.symm)

/-- Uniqueness of path lifts through `Complex.exp`. -/
theorem eq_expLift {z₀ z₁ : {z : ℂ // z ≠ 0}} (γ : Path z₀ z₁) (w0 : ℂ)
    (hw0 : Complex.exp w0 = (z₀ : ℂ)) (Γ : C(I, ℂ))
    (hlift : ∀ t, Complex.exp (Γ t) = (γ t : ℂ)) (h0 : Γ 0 = w0) :
    Γ = γ.expLift w0 hw0 := by
  apply (Complex.isCoveringMap_exp.eq_liftPath_iff' (γ := γ.toContinuousMap) (e := w0)
    (γ_0 := by
      apply Subtype.ext
      simpa using hw0.symm) (Γ := Γ)).2
  constructor
  · ext t
    show Complex.exp (Γ t) = (γ t : ℂ)
    exact hlift t
  · exact h0

private theorem exp_sub_int_mul_two_pi_I_eq (z : ℂ) (n : ℤ) :
    Complex.exp (z - n * (2 * Real.pi * Complex.I)) = Complex.exp z := by
  apply (Complex.exp_eq_exp_iff_exists_int).2
  refine ⟨-n, ?_⟩
  simp [sub_eq_add_neg, Int.cast_neg]

/-- The winding number of a loop in `ℂ \ {0}`, defined via lifts through `Complex.exp`. -/
noncomputable def windingNumber {z : {z : ℂ // z ≠ 0}} (γ : Path z z) : ℤ := by
  let w0 : ℂ := Complex.log z
  have hw0 : Complex.exp w0 = (z : ℂ) := by
    simpa [w0] using Complex.exp_log z.property
  let Γ := γ.expLift w0 hw0
  have hper : Complex.exp (Γ 1) = Complex.exp (Γ 0) := by
    calc
      Complex.exp (Γ 1) = (γ 1 : ℂ) := expLift_apply γ w0 hw0 1
      _ = (z : ℂ) := by
        simpa using congrArg Subtype.val γ.target
      _ = (γ 0 : ℂ) := by
        simpa using congrArg Subtype.val γ.source
      _ = Complex.exp (Γ 0) := by
        symm
        exact expLift_apply γ w0 hw0 0
  exact Classical.choose ((Complex.exp_eq_exp_iff_exists_int).1 hper)

theorem windingNumber_eq_of_lift {z : {z : ℂ // z ≠ 0}} (γ : Path z z)
    (Γ : C(I, ℂ)) (hlift : ∀ t, Complex.exp (Γ t) = (γ t : ℂ)) :
    (Γ 1 - Γ 0) / (2 * Real.pi * Complex.I) = γ.windingNumber := by
  let w0 : ℂ := Complex.log z
  have hw0 : Complex.exp w0 = (z : ℂ) := by
    simpa [w0] using Complex.exp_log z.property
  let liftγ : C(I, ℂ) := γ.expLift w0 hw0
  have hliftγ : ∀ t, Complex.exp (liftγ t) = (γ t : ℂ) := fun t =>
    expLift_apply γ w0 hw0 t
  have h0eq : Complex.exp (Γ 0) = Complex.exp (liftγ 0) := by
    rw [hlift 0, hliftγ 0]
  obtain ⟨n, hn⟩ := (Complex.exp_eq_exp_iff_exists_int).1 h0eq
  let shifted : C(I, ℂ) :=
    ⟨fun t => Γ t - n * (2 * Real.pi * Complex.I), Γ.continuous.sub continuous_const⟩
  have hshifted_lift : ∀ t, Complex.exp (shifted t) = (γ t : ℂ) := by
    intro t
    calc
      Complex.exp (shifted t) = Complex.exp (Γ t) := by
        exact exp_sub_int_mul_two_pi_I_eq _ _
      _ = (γ t : ℂ) := hlift t
  have hshifted0 : shifted 0 = w0 := by
    calc
      shifted 0 = Γ 0 - n * (2 * Real.pi * Complex.I) := by rfl
      _ = liftγ 0 := by rw [hn]; ring
      _ = w0 := expLift_zero γ w0 hw0
  have huniq : shifted = liftγ := by
    simpa [liftγ] using eq_expLift γ w0 hw0 shifted hshifted_lift hshifted0
  have hshift_eq : ∀ t, Γ t = liftγ t + n * (2 * Real.pi * Complex.I) := by
    intro t
    have ht : shifted t = liftγ t := by
      simpa using congrFun (congrArg DFunLike.coe huniq) t
    calc
      Γ t = (Γ t - n * (2 * Real.pi * Complex.I)) + n * (2 * Real.pi * Complex.I) := by
        ring
      _ = shifted t + n * (2 * Real.pi * Complex.I) := by rfl
      _ = liftγ t + n * (2 * Real.pi * Complex.I) := by rw [ht]
  have hbase_eq :
      liftγ 1 = liftγ 0 + γ.windingNumber * (2 * Real.pi * Complex.I) := by
    unfold windingNumber
    dsimp [liftγ]
    exact Classical.choose_spec ((Complex.exp_eq_exp_iff_exists_int).1 <| by
      calc
        Complex.exp ((γ.expLift w0 hw0) 1) = (γ 1 : ℂ) := expLift_apply γ w0 hw0 1
        _ = (z : ℂ) := by
          simpa using congrArg Subtype.val γ.target
        _ = (γ 0 : ℂ) := by
          simpa using (congrArg Subtype.val γ.source).symm
        _ = Complex.exp ((γ.expLift w0 hw0) 0) := by
          symm
          exact expLift_apply γ w0 hw0 0)
  have hbase :
      (liftγ 1 - liftγ 0) / (2 * Real.pi * Complex.I) = γ.windingNumber := by
    rw [hbase_eq]
    ring_nf
    field_simp [Complex.two_pi_I_ne_zero]
  calc
    (Γ 1 - Γ 0) / (2 * Real.pi * Complex.I)
        = ((liftγ 1 + n * (2 * Real.pi * Complex.I)) -
            (liftγ 0 + n * (2 * Real.pi * Complex.I))) / (2 * Real.pi * Complex.I) := by
            rw [hshift_eq 1, hshift_eq 0]
    _ = (liftγ 1 - liftγ 0) / (2 * Real.pi * Complex.I) := by ring
    _ = γ.windingNumber := hbase

theorem windingNumber_eq_of_homotopy {z z' : {z : ℂ // z ≠ 0}}
    (γ : Path z z) (γ' : Path z' z') (H : C(I × I, {z : ℂ // z ≠ 0}))
    (hhom : H.IsLoopHomotopy) (hzero : ∀ t, H (0, t) = γ t)
    (hone : ∀ t, H (1, t) = γ' t) :
    γ.windingNumber = γ'.windingNumber := by
  let w0 : ℂ := Complex.log z
  have hw0 : Complex.exp w0 = (z : ℂ) := by
    simpa [w0] using Complex.exp_log z.property
  let tildeγ : C(I, ℂ) := γ.expLift w0 hw0
  have htildeγ : ∀ t, Complex.exp (tildeγ t) = (γ t : ℂ) := fun t =>
    expLift_apply γ w0 hw0 t
  have hH0 : ∀ t, H (0, t) = ⟨Complex.exp (tildeγ t), Complex.exp_ne_zero _⟩ := by
    intro t
    apply Subtype.ext
    calc
      (H (0, t) : ℂ) = (γ t : ℂ) := by
        simpa using congrArg Subtype.val (hzero t)
      _ = Complex.exp (tildeγ t) := by
        symm
        exact htildeγ t
  let tildeH : C(I × I, ℂ) := Complex.isCoveringMap_exp.liftHomotopy H tildeγ hH0
  have htildeH_lifts : ∀ x, Complex.exp (tildeH x) = (H x : ℂ) := by
    intro x
    exact congrArg Subtype.val <| congrFun
      (Complex.isCoveringMap_exp.liftHomotopy_lifts H tildeγ hH0) x
  have htildeH_zero : ∀ t, tildeH (0, t) = tildeγ t := by
    intro t
    simpa using Complex.isCoveringMap_exp.liftHomotopy_zero (H := H) (f := tildeγ)
      (H_0 := hH0) t
  let μ : Path z z' := {
    toFun := fun s => H (s, 0)
    continuous_toFun := H.continuous.comp (continuous_id.prodMk continuous_const)
    source' := by simpa using hzero 0
    target' := by simpa using hone 0 }
  let μ0 : C(I, ℂ) :=
    ⟨fun s => tildeH (s, 0), tildeH.continuous.comp (continuous_id.prodMk continuous_const)⟩
  let μ1 : C(I, ℂ) :=
    ⟨fun s => tildeH (s, 1), tildeH.continuous.comp (continuous_id.prodMk continuous_const)⟩
  have hμ0 : (∀ s, Complex.exp (μ0 s) = (μ s : ℂ)) ∧ μ0 0 = tildeγ 0 := by
    constructor
    · intro s
      simpa [μ, μ0] using htildeH_lifts (s, 0)
    · simpa [μ0] using htildeH_zero 0
  have hμ1 : (∀ s, Complex.exp (μ1 s) = (μ s : ℂ)) ∧ μ1 0 = tildeγ 1 := by
    constructor
    · intro s
      calc
        Complex.exp (μ1 s) = (H (s, 1) : ℂ) := by
          simpa [μ1] using htildeH_lifts (s, 1)
        _ = (H (s, 0) : ℂ) := by
          simpa using congrArg Subtype.val (hhom s).symm
        _ = (μ s : ℂ) := by rfl
    · simpa [μ1] using htildeH_zero 1
  have hstart : Complex.exp (tildeγ 1) = Complex.exp (tildeγ 0) := by
    calc
      Complex.exp (tildeγ 1) = (γ 1 : ℂ) := htildeγ 1
      _ = (z : ℂ) := by
        simpa using congrArg Subtype.val γ.target
      _ = (γ 0 : ℂ) := by
        simpa using (congrArg Subtype.val γ.source).symm
      _ = Complex.exp (tildeγ 0) := by
        symm
        exact htildeγ 0
  obtain ⟨n, hn⟩ := (Complex.exp_eq_exp_iff_exists_int).1 hstart
  let shiftedμ0 : C(I, ℂ) :=
    ⟨fun s => μ0 s + n * (2 * Real.pi * Complex.I), μ0.continuous.add continuous_const⟩
  have hshiftedμ0 : (∀ s, Complex.exp (shiftedμ0 s) = (μ s : ℂ)) ∧ shiftedμ0 0 = μ1 0 := by
    constructor
    · intro s
      calc
        Complex.exp (shiftedμ0 s) = Complex.exp (μ0 s) := by
          apply (Complex.exp_eq_exp_iff_exists_int).2
          refine ⟨n, by simp [shiftedμ0]⟩
        _ = (μ s : ℂ) := hμ0.1 s
    · calc
        shiftedμ0 0 = μ0 0 + n * (2 * Real.pi * Complex.I) := by rfl
        _ = tildeγ 0 + n * (2 * Real.pi * Complex.I) := by rw [hμ0.2]
        _ = tildeγ 1 := by rw [hn]
        _ = μ1 0 := by rw [hμ1.2]
  have hμ10 : Complex.exp (μ1 0) = (z : ℂ) := by
    calc
      Complex.exp (μ1 0) = (μ 0 : ℂ) := hμ1.1 0
      _ = (z : ℂ) := by
        simpa using congrArg Subtype.val μ.source
  have hshifted_eq :
      shiftedμ0 = μ.expLift (μ1 0) hμ10 :=
    eq_expLift μ (μ1 0) hμ10 shiftedμ0 hshiftedμ0.1 hshiftedμ0.2
  have hμ1_eq :
      μ1 = μ.expLift (μ1 0) hμ10 :=
    eq_expLift μ (μ1 0) hμ10 μ1 hμ1.1 rfl
  have huniq : shiftedμ0 = μ1 := by
    calc
      shiftedμ0 = μ.expLift (μ1 0) hμ10 := hshifted_eq
      _ = μ1 := hμ1_eq.symm
  have hshift_eq : ∀ s, μ1 s = μ0 s + n * (2 * Real.pi * Complex.I) := by
    intro s
    have hfun := congrArg DFunLike.coe huniq
    simpa [shiftedμ0] using (congrFun hfun s).symm
  let tildeγ' : C(I, ℂ) :=
    ⟨fun t => tildeH (1, t), tildeH.continuous.comp (continuous_const.prodMk continuous_id)⟩
  have htildeγ' : ∀ t, Complex.exp (tildeγ' t) = (γ' t : ℂ) := by
    intro t
    calc
      Complex.exp (tildeγ' t) = (H (1, t) : ℂ) := by
        simpa [tildeγ'] using htildeH_lifts (1, t)
      _ = (γ' t : ℂ) := by
        simpa using congrArg Subtype.val (hone t)
  have hwind :
      (tildeγ' 1 - tildeγ' 0) / (2 * Real.pi * Complex.I) =
        (tildeγ 1 - tildeγ 0) / (2 * Real.pi * Complex.I) := by
    have hdiff : tildeγ' 1 - tildeγ' 0 = tildeγ 1 - tildeγ 0 := by
      calc
        tildeγ' 1 - tildeγ' 0 = μ1 1 - μ0 1 := by rfl
        _ = μ1 0 - μ0 0 := by
          rw [hshift_eq 1, hshift_eq 0]
          ring
        _ = tildeγ 1 - tildeγ 0 := by
          rw [hμ1.2, hμ0.2]
    rw [hdiff]
  have hcast :
      ((γ.windingNumber : ℤ) : ℂ) = ((γ'.windingNumber : ℤ) : ℂ) := by
    calc
      ((γ.windingNumber : ℤ) : ℂ)
          = (tildeγ 1 - tildeγ 0) / (2 * Real.pi * Complex.I) := by
              symm
              exact windingNumber_eq_of_lift γ tildeγ htildeγ
      _ = (tildeγ' 1 - tildeγ' 0) / (2 * Real.pi * Complex.I) := by
            symm
            exact hwind
      _ = ((γ'.windingNumber : ℤ) : ℂ) := by
            exact windingNumber_eq_of_lift γ' tildeγ' htildeγ'
  exact_mod_cast hcast

@[simp] theorem windingNumber_refl (z : {z : ℂ // z ≠ 0}) :
    (Path.refl z).windingNumber = 0 := by
  let Γ : C(I, ℂ) := ContinuousMap.const _ (Complex.log z)
  have hlift : ∀ t, Complex.exp (Γ t) = ((Path.refl z) t : ℂ) := by
    intro t
    simpa [Γ] using Complex.exp_log z.property
  have hq : (Γ 1 - Γ 0) / (2 * Real.pi * Complex.I) = (Path.refl z).windingNumber :=
    windingNumber_eq_of_lift (Path.refl z) Γ hlift
  simpa [Γ] using hq.symm

/-- The winding number of a loop in `ℂˣ`. -/
noncomputable def unitsWindingNumber {u : ℂˣ} (γ : Path u u) : ℤ :=
  γ.toNonzeroSubtype.windingNumber

theorem unitsWindingNumber_eq_of_lift {u : ℂˣ} (γ : Path u u) (Γ : C(I, ℂ))
    (hlift : ∀ t, Complex.exp (Γ t) = (γ t : ℂ)) :
    (Γ 1 - Γ 0) / (2 * Real.pi * Complex.I) = γ.unitsWindingNumber := by
  simpa [unitsWindingNumber] using
    windingNumber_eq_of_lift γ.toNonzeroSubtype Γ (by
      intro t
      simpa using hlift t)

theorem unitsWindingNumber_eq_of_homotopy {u u' : ℂˣ}
    (γ : Path u u) (γ' : Path u' u') (H : C(I × I, ℂˣ))
    (hhom : H.IsLoopHomotopy) (hzero : ∀ t, H (0, t) = γ t)
    (hone : ∀ t, H (1, t) = γ' t) :
    γ.unitsWindingNumber = γ'.unitsWindingNumber := by
  let H' : C(I × I, {z : ℂ // z ≠ 0}) := H.toNonzeroSubtype
  have hhom' : H'.IsLoopHomotopy := by
    intro s
    apply Subtype.ext
    simpa [H', ContinuousMap.toNonzeroSubtype] using
      congrArg (fun z : ℂˣ => (z : ℂ)) (hhom s)
  have hzero' : ∀ t, H' (0, t) = γ.toNonzeroSubtype t := by
    intro t
    apply Subtype.ext
    simpa [H', ContinuousMap.toNonzeroSubtype, Path.toNonzeroSubtype] using
      congrArg (fun z : ℂˣ => (z : ℂ)) (hzero t)
  have hone' : ∀ t, H' (1, t) = γ'.toNonzeroSubtype t := by
    intro t
    apply Subtype.ext
    simpa [H', ContinuousMap.toNonzeroSubtype, Path.toNonzeroSubtype] using
      congrArg (fun z : ℂˣ => (z : ℂ)) (hone t)
  simpa [unitsWindingNumber] using
    windingNumber_eq_of_homotopy γ.toNonzeroSubtype γ'.toNonzeroSubtype H' hhom' hzero' hone'

@[simp] theorem unitsWindingNumber_refl (u : ℂˣ) :
    (Path.refl u).unitsWindingNumber = 0 := by
  have h :
      (Path.refl u).toNonzeroSubtype =
        Path.refl (⟨(u : ℂ), u.ne_zero⟩ : {z : ℂ // z ≠ 0}) := by
    ext t
    rfl
  rw [unitsWindingNumber, h]
  exact windingNumber_refl (⟨(u : ℂ), u.ne_zero⟩ : {z : ℂ // z ≠ 0})

end Path
