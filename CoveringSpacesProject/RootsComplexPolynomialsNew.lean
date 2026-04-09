import Mathlib

/-!
# A blueprint-style presentation of the winding-number proof

This file repackages the refactor of the winding-number and polynomial-root argument into a
single self-contained module. The exposition follows the style of
`CoveringSpacesProject/RootsComplexPolynomials.lean`, while the formal development uses the newer
Mathlib-facing abstractions based on `Path`, `I`, `ContinuousMap.Homotopy`, `Complex.exp`, and
`ℂˣ`.

## Upstreaming note

From a mathlib-quality point of view, this standalone file is intentionally too broad. A likely
upstream split would be:

* `ContinuousMap.IsLoopHomotopy` in a topology/path-support layer;
* `Circle.toClosedUnitDisk`, `ContinuousMap.circleLoop`, and `ContinuousMap.circleLoopHomotopy`
  near the existing circle API in `Mathlib/Analysis/SpecialFunctions/Complex/Circle.lean` and the
  path/homotopy API in `Mathlib/Topology/Homotopy/Path.lean`;
* `Path.expLift` and the `Path.windingNumber` API in or next to
  `Mathlib/Analysis/Complex/CoveringMap.lean` as a small winding-number companion file;
* the monomial and polynomial applications left downstream, since they are project-specific rather
  than reusable core library material.
-/

open scoped unitInterval

noncomputable section

namespace RootsComplexPolynomialsNew

/-%%
\section{Homotopies through loops}
%%-/

namespace ContinuousMap

/-%%
\begin{definition}\label{IsLoopHomotopyNew}\lean{RootsComplexPolynomialsNew.ContinuousMap.IsLoopHomotopy}\leanok
A homotopy $H\colon I\times I\to X$ is a homotopy through loops if each horizontal slice has the
same initial and terminal point.
\begin{verbatim}
def IsLoopHomotopy
    [TopologicalSpace X] (H : C(I × I, X)) :
    Prop
\end{verbatim}
\end{definition}
%%-/

def IsLoopHomotopy {X : Type*} [TopologicalSpace X] (H : C(I × I, X)) : Prop :=
  ∀ s, H (s, 0) = H (s, 1)

/-%%
\begin{proof}\leanok
This is the direct formalization of the condition that every slice $t\mapsto H(s,t)$ is a loop.
\end{proof}
%%-/

end ContinuousMap

/-%%
\section{Circle-valued helper constructions}
%%-/

namespace Circle

/-%%
\begin{definition}\label{circleToClosedUnitDiskNew}\lean{RootsComplexPolynomialsNew.Circle.toClosedUnitDisk}\leanok
The canonical inclusion of the unit circle into the closed unit disk.
\begin{verbatim}
abbrev toClosedUnitDisk :
    Circle → Metric.closedBall (0 : ℂ) 1
\end{verbatim}
\end{definition}
%%-/

abbrev toClosedUnitDisk : Circle → Metric.closedBall (0 : ℂ) 1 :=
  Set.inclusion Metric.sphere_subset_closedBall

/-%%
\begin{proof}\leanok
This is the direct inclusion of the unit circle into the closed unit disk in $\C$.
\end{proof}
%%-/

/-%%
\begin{lemma}\label{coe_toClosedUnitDiskNew}\lean{RootsComplexPolynomialsNew.Circle.coe_toClosedUnitDisk}\uses{circleToClosedUnitDiskNew}\leanok
After forgetting the subtype, the inclusion of the circle into the closed disk does not change the
underlying complex number.
\begin{verbatim}
theorem coe_toClosedUnitDisk (z : Circle) :
    ((toClosedUnitDisk z :
      Metric.closedBall (0 : ℂ) 1) : ℂ) = z
\end{verbatim}
\end{lemma}
%%-/

@[simp] theorem coe_toClosedUnitDisk (z : Circle) :
    ((toClosedUnitDisk z : Metric.closedBall (0 : ℂ) 1) : ℂ) = z := rfl

/-%%
\begin{proof}\leanok
The inclusion map is literally the identity on the underlying point.
\end{proof}
%%-/

end Circle

namespace ContinuousMap

/-%%
\begin{definition}\label{circleLoopNew}\lean{RootsComplexPolynomialsNew.ContinuousMap.circleLoop}\leanok
Given a continuous map $\psi\colon S^1\to X$, its associated loop is obtained by precomposing with
the standard parametrization $t\mapsto \exp(2\pi i t)$ of the circle on $I$.
\begin{verbatim}
def circleLoop
    [TopologicalSpace X] (f : C(Circle, X)) :
    Path (f 1) (f 1)
\end{verbatim}
\end{definition}
%%-/

def circleLoop {X : Type*} [TopologicalSpace X] (f : C(Circle, X)) : Path (f 1) (f 1) where
  toFun t := f (Circle.exp (2 * Real.pi * (t : ℝ)))
  continuous_toFun := f.continuous.comp <| Circle.exp.continuous.comp <| by fun_prop
  source' := by simp
  target' := by simp [Circle.exp_two_pi]

/-%%
\begin{proof}\leanok
The map is continuous by composition, and its endpoints agree because the circle parametrization
takes both $0$ and $1$ to the point $1\in S^1$.
\end{proof}
%%-/

/-%%
\begin{lemma}\label{circleLoop_applyNew}\lean{RootsComplexPolynomialsNew.ContinuousMap.circleLoop_apply}\uses{circleLoopNew}\leanok
The associated loop evaluates at $t\in I$ as $\psi(\exp(2\pi i t))$.
\begin{verbatim}
theorem circleLoop_apply
    [TopologicalSpace X] (f : C(Circle, X))
    (t : I) :
    (ContinuousMap.circleLoop f) t =
    f (Circle.exp (2 * Real.pi * (t : ℝ)))
\end{verbatim}
\end{lemma}
%%-/

@[simp] theorem circleLoop_apply {X : Type*} [TopologicalSpace X] (f : C(Circle, X)) (t : I) :
    (ContinuousMap.circleLoop f) t = f (Circle.exp (2 * Real.pi * (t : ℝ))) := rfl

/-%%
\begin{proof}\leanok
This is just the defining formula for the associated loop.
\end{proof}
%%-/

/-%%
\begin{definition}\label{circleLoopHomotopyNew}\lean{RootsComplexPolynomialsNew.ContinuousMap.circleLoopHomotopy}\uses{circleLoopNew}\leanok
A homotopy of circle maps induces a homotopy of the associated loops by precomposing with the
standard circle parametrization.
\begin{verbatim}
def circleLoopHomotopy
    [TopologicalSpace X] {f g : C(Circle, X)}
    (H : ContinuousMap.Homotopy f g) :
    C(I × I, X)
\end{verbatim}
\end{definition}
%%-/

def circleLoopHomotopy {X : Type*} [TopologicalSpace X] {f g : C(Circle, X)}
    (H : ContinuousMap.Homotopy f g) : C(I × I, X) :=
  ⟨fun x => H (x.1, Circle.exp (2 * Real.pi * (x.2 : ℝ))),
    H.continuous_toFun.comp
      (continuous_fst.prodMk
        (Circle.exp.continuous.comp <| by fun_prop))⟩

/-%%
\begin{proof}\leanok
This is obtained by composing the given homotopy with the standard map from $I$ to the circle.
\end{proof}
%%-/

/-%%
\begin{lemma}\label{circleLoopHomotopy_applyNew}\lean{RootsComplexPolynomialsNew.ContinuousMap.circleLoopHomotopy_apply}\uses{circleLoopHomotopyNew}\leanok
The induced homotopy evaluates by the expected formula
$\widehat H(s,t)=H(s,\exp(2\pi i t))$.
\begin{verbatim}
theorem circleLoopHomotopy_apply
    [TopologicalSpace X] {f g : C(Circle, X)}
    (H : ContinuousMap.Homotopy f g) (x : I × I) :
    circleLoopHomotopy H x =
    H (x.1, Circle.exp (2 * Real.pi * (x.2 : ℝ)))
\end{verbatim}
\end{lemma}
%%-/

@[simp] theorem circleLoopHomotopy_apply {X : Type*} [TopologicalSpace X] {f g : C(Circle, X)}
    (H : ContinuousMap.Homotopy f g) (x : I × I) :
    circleLoopHomotopy H x = H (x.1, Circle.exp (2 * Real.pi * (x.2 : ℝ))) := rfl

/-%%
\begin{proof}\leanok
This is immediate from the definition of the induced homotopy.
\end{proof}
%%-/

/-%%
\begin{lemma}\label{circleLoopHomotopy_isLoopHomotopyNew}\lean{RootsComplexPolynomialsNew.ContinuousMap.circleLoopHomotopy_isLoopHomotopy}\uses{circleLoopHomotopyNew, IsLoopHomotopyNew}\leanok
The induced homotopy of associated loops is a homotopy through loops.
\begin{verbatim}
theorem circleLoopHomotopy_isLoopHomotopy
    [TopologicalSpace X] {f g : C(Circle, X)}
    (H : ContinuousMap.Homotopy f g) :
    ContinuousMap.IsLoopHomotopy
    (circleLoopHomotopy H)
\end{verbatim}
\end{lemma}
%%-/

theorem circleLoopHomotopy_isLoopHomotopy {X : Type*} [TopologicalSpace X] {f g : C(Circle, X)}
    (H : ContinuousMap.Homotopy f g) : ContinuousMap.IsLoopHomotopy (circleLoopHomotopy H) := by
  intro s
  change H (s, Circle.exp (2 * Real.pi * (0 : ℝ))) =
    H (s, Circle.exp (2 * Real.pi * (1 : ℝ)))
  simp [Circle.exp_two_pi]

/-%%
\begin{proof}\leanok
For each fixed $s$, the two endpoints correspond to the same point of the circle because
$\exp(0)=\exp(2\pi i)=1$.
\end{proof}
%%-/

/-%%
\begin{lemma}\label{circleLoopHomotopy_zero_leftNew}\lean{RootsComplexPolynomialsNew.ContinuousMap.circleLoopHomotopy_zero_left}\uses{circleLoopHomotopyNew, circleLoopNew}\leanok
At the left endpoint of the homotopy parameter, the induced loop homotopy recovers the associated
loop of the initial map.
\begin{verbatim}
theorem circleLoopHomotopy_zero_left
    [TopologicalSpace X] {f g : C(Circle, X)}
    (H : ContinuousMap.Homotopy f g) (t : I) :
    circleLoopHomotopy H (0, t) =
    (ContinuousMap.circleLoop f) t
\end{verbatim}
\end{lemma}
%%-/

@[simp] theorem circleLoopHomotopy_zero_left {X : Type*} [TopologicalSpace X]
    {f g : C(Circle, X)} (H : ContinuousMap.Homotopy f g) (t : I) :
    circleLoopHomotopy H (0, t) = (ContinuousMap.circleLoop f) t := by
  change H (0, Circle.exp (2 * Real.pi * (t : ℝ))) = f (Circle.exp (2 * Real.pi * (t : ℝ)))
  exact H.map_zero_left (Circle.exp (2 * Real.pi * (t : ℝ)))

/-%%
\begin{proof}\leanok
This is the defining property of a homotopy at time $0$, evaluated along the circle
parametrization.
\end{proof}
%%-/

/-%%
\begin{lemma}\label{circleLoopHomotopy_one_leftNew}\lean{RootsComplexPolynomialsNew.ContinuousMap.circleLoopHomotopy_one_left}\uses{circleLoopHomotopyNew, circleLoopNew}\leanok
At the right endpoint of the homotopy parameter, the induced loop homotopy recovers the associated
loop of the terminal map.
\begin{verbatim}
theorem circleLoopHomotopy_one_left
    [TopologicalSpace X] {f g : C(Circle, X)}
    (H : ContinuousMap.Homotopy f g) (t : I) :
    circleLoopHomotopy H (1, t) =
    (ContinuousMap.circleLoop g) t
\end{verbatim}
\end{lemma}
%%-/

@[simp] theorem circleLoopHomotopy_one_left {X : Type*} [TopologicalSpace X]
    {f g : C(Circle, X)} (H : ContinuousMap.Homotopy f g) (t : I) :
    circleLoopHomotopy H (1, t) = (ContinuousMap.circleLoop g) t := by
  change H (1, Circle.exp (2 * Real.pi * (t : ℝ))) = g (Circle.exp (2 * Real.pi * (t : ℝ)))
  exact H.map_one_left (Circle.exp (2 * Real.pi * (t : ℝ)))

/-%%
\begin{proof}\leanok
This is the corresponding defining property of a homotopy at time $1$.
\end{proof}
%%-/

end ContinuousMap

/-%%
\section{Lifts and winding numbers of loops}
%%-/

private noncomputable def complexUnitsHomeomorphNeZero :
    ℂˣ ≃ₜ {z : ℂ // z ≠ 0} :=
  unitsHomeomorphNeZero (G₀ := ℂ)

namespace Path

private noncomputable def toNonzeroPath {u v : ℂˣ} (γ : Path u v) :
    Path (complexUnitsHomeomorphNeZero u) (complexUnitsHomeomorphNeZero v) :=
  γ.map (complexUnitsHomeomorphNeZero : C(ℂˣ, {z : ℂ // z ≠ 0})).continuous

private noncomputable def unitLog (u : ℂˣ) : ℂ :=
  Complex.log (u : ℂ)

@[simp] private theorem exp_unitLog (u : ℂˣ) : Complex.exp (unitLog u) = (u : ℂ) := by
  simpa [unitLog] using Complex.exp_log u.ne_zero

/-%%
\begin{definition}\label{expLiftNew}\lean{RootsComplexPolynomialsNew.Path.expLift}\leanok
Given a path in $\C^\times$ and a chosen logarithm of its starting point, lift the path through the
exponential covering map.
\begin{verbatim}
noncomputable def expLift
    {u₀ u₁ : ℂˣ} (γ : Path u₀ u₁) (w0 : ℂ)
    (hw0 : Complex.exp w0 = (u₀ : ℂ)) :
    C(I, ℂ)
\end{verbatim}
\end{definition}
%%-/

noncomputable def expLift {u₀ u₁ : ℂˣ} (γ : Path u₀ u₁) (w0 : ℂ)
    (hw0 : Complex.exp w0 = (u₀ : ℂ)) : C(I, ℂ) :=
  Complex.isCoveringMap_exp.liftPath (toNonzeroPath γ).toContinuousMap w0 <| by
    apply Subtype.ext
    simpa using hw0.symm

/-%%
\begin{proof}\leanok
Transport the path to the standard nonzero-complex subtype, where `Complex.exp` is already
registered as a covering map in Mathlib, and apply path lifting there.
\end{proof}
%%-/

/-%%
\begin{lemma}\label{expLift_applyNew}\lean{RootsComplexPolynomialsNew.Path.expLift_apply}\uses{expLiftNew}\leanok
The lifted path projects back to the original path under the exponential map.
\begin{verbatim}
theorem expLift_apply
    {u₀ u₁ : ℂˣ} (γ : Path u₀ u₁) (w0 : ℂ)
    (hw0 : Complex.exp w0 = (u₀ : ℂ)) (t : I) :
    Complex.exp (Path.expLift γ w0 hw0 t) =
    (γ t : ℂ)
\end{verbatim}
\end{lemma}
%%-/

@[simp] theorem expLift_apply {u₀ u₁ : ℂˣ} (γ : Path u₀ u₁) (w0 : ℂ)
    (hw0 : Complex.exp w0 = (u₀ : ℂ)) (t : I) :
    Complex.exp (Path.expLift γ w0 hw0 t) = (γ t : ℂ) := by
  have h :=
    congrFun (Complex.isCoveringMap_exp.liftPath_lifts ((toNonzeroPath γ).toContinuousMap) w0 <| by
      apply Subtype.ext
      simpa using hw0.symm) t
  simpa [toNonzeroPath] using congrArg Subtype.val h

/-%%
\begin{proof}\leanok
This is exactly the lifting property supplied by the covering-space API, after forgetting the
codomain subtype.
\end{proof}
%%-/

/-%%
\begin{lemma}\label{expLift_zeroNew}\lean{RootsComplexPolynomialsNew.Path.expLift_zero}\uses{expLiftNew}\leanok
The lifted path starts at the prescribed basepoint.
\begin{verbatim}
theorem expLift_zero
    {u₀ u₁ : ℂˣ} (γ : Path u₀ u₁) (w0 : ℂ)
    (hw0 : Complex.exp w0 = (u₀ : ℂ)) :
    Path.expLift γ w0 hw0 0 = w0
\end{verbatim}
\end{lemma}
%%-/

@[simp] theorem expLift_zero {u₀ u₁ : ℂˣ} (γ : Path u₀ u₁) (w0 : ℂ)
    (hw0 : Complex.exp w0 = (u₀ : ℂ)) :
    Path.expLift γ w0 hw0 0 = w0 := by
  simpa [expLift] using Complex.isCoveringMap_exp.liftPath_zero
    (γ := (toNonzeroPath γ).toContinuousMap) (e := w0) (γ_0 := by
      apply Subtype.ext
      simpa using hw0.symm)

/-%%
\begin{proof}\leanok
This is the standard initial-value property of the lifted path.
\end{proof}
%%-/

/-%%
\begin{lemma}\label{eq_expLiftNew}\lean{RootsComplexPolynomialsNew.Path.eq_expLift}\uses{expLiftNew}\leanok
Any other lift of the same path with the same starting point agrees with the canonical lifted path.
\begin{verbatim}
theorem eq_expLift
    {u₀ u₁ : ℂˣ} (γ : Path u₀ u₁) (w0 : ℂ)
    (hw0 : Complex.exp w0 = (u₀ : ℂ))
    (Γ : C(I, ℂ))
    (hlift : ∀ t, Complex.exp (Γ t) = (γ t : ℂ))
    (h0 : Γ 0 = w0) :
    Γ = Path.expLift γ w0 hw0
\end{verbatim}
\end{lemma}
%%-/

theorem eq_expLift {u₀ u₁ : ℂˣ} (γ : Path u₀ u₁) (w0 : ℂ)
    (hw0 : Complex.exp w0 = (u₀ : ℂ)) (Γ : C(I, ℂ))
    (hlift : ∀ t, Complex.exp (Γ t) = (γ t : ℂ)) (h0 : Γ 0 = w0) :
    Γ = Path.expLift γ w0 hw0 := by
  apply (Complex.isCoveringMap_exp.eq_liftPath_iff' (γ := (toNonzeroPath γ).toContinuousMap)
    (e := w0)
    (γ_0 := by
      apply Subtype.ext
      simpa using hw0.symm) (Γ := Γ)).2
  constructor
  · ext t
    show Complex.exp (Γ t) = (((toNonzeroPath γ).toContinuousMap) t : ℂ)
    simpa [toNonzeroPath] using hlift t
  · exact h0

/-%%
\begin{proof}\leanok
This is uniqueness of lifts for the covering map $\exp$, after transporting the path from
$\C^\times$ to the standard nonzero-complex subtype.
\end{proof}
%%-/

/-%%
\begin{lemma}\label{exp_add_int_mul_two_pi_I_eqNew}\lean{RootsComplexPolynomialsNew.Path.exp_add_int_mul_two_pi_I_eq}\leanok
Adding an integral multiple of $2\pi i$ does not change the exponential.
\begin{verbatim}
theorem exp_add_int_mul_two_pi_I_eq
    (z : ℂ) (n : ℤ) :
    Complex.exp (z + n * (2 * Real.pi *
    Complex.I)) = Complex.exp z
\end{verbatim}
\end{lemma}
%%-/

private theorem exp_add_int_mul_two_pi_I_eq (z : ℂ) (n : ℤ) :
    Complex.exp (z + n * (2 * Real.pi * Complex.I)) = Complex.exp z := by
  apply (Complex.exp_eq_exp_iff_exists_int).2
  refine ⟨n, ?_⟩
  simp

/-%%
\begin{proof}\leanok
This is the usual $2\pi i$-periodicity of the complex exponential map.
\end{proof}
%%-/

/-%%
\begin{lemma}\label{eq_add_int_mul_two_pi_I_of_liftsNew}\lean{RootsComplexPolynomialsNew.Path.eq_add_int_mul_two_pi_I_of_lifts}\uses{eq_expLiftNew, exp_add_int_mul_two_pi_I_eqNew}\leanok
Two lifts of the same path differ by a constant integral multiple of $2\pi i$.
\begin{verbatim}
theorem eq_add_int_mul_two_pi_I_of_lifts
    {u₀ u₁ : ℂˣ} (γ : Path u₀ u₁)
    (Γ₀ Γ₁ : C(I, ℂ))
    (hΓ₀ : ∀ t, Complex.exp (Γ₀ t) = (γ t : ℂ))
    (hΓ₁ : ∀ t, Complex.exp (Γ₁ t) = (γ t : ℂ)) :
    ∃ n : ℤ, ∀ t, Γ₁ t =
    Γ₀ t + n * (2 * Real.pi * Complex.I)
\end{verbatim}
\end{lemma}
%%-/

private theorem eq_add_int_mul_two_pi_I_of_lifts {u₀ u₁ : ℂˣ} (γ : Path u₀ u₁)
    (Γ₀ Γ₁ : C(I, ℂ)) (hΓ₀ : ∀ t, Complex.exp (Γ₀ t) = (γ t : ℂ))
    (hΓ₁ : ∀ t, Complex.exp (Γ₁ t) = (γ t : ℂ)) :
    ∃ n : ℤ, ∀ t, Γ₁ t = Γ₀ t + n * (2 * Real.pi * Complex.I) := by
  have h0eq : Complex.exp (Γ₁ 0) = Complex.exp (Γ₀ 0) := by
    rw [hΓ₁ 0, hΓ₀ 0]
  obtain ⟨n, hn⟩ := (Complex.exp_eq_exp_iff_exists_int).1 h0eq
  have hΓ₁0 : Complex.exp (Γ₁ 0) = (u₀ : ℂ) := by
    calc
      Complex.exp (Γ₁ 0) = (γ 0 : ℂ) := hΓ₁ 0
      _ = (u₀ : ℂ) := by
        simp [γ.source]
  let shiftedΓ₀ : C(I, ℂ) :=
    ⟨fun t => Γ₀ t + n * (2 * Real.pi * Complex.I), Γ₀.continuous.add continuous_const⟩
  have hshiftedΓ₀ : ∀ t, Complex.exp (shiftedΓ₀ t) = (γ t : ℂ) := by
    intro t
    calc
      Complex.exp (shiftedΓ₀ t) = Complex.exp (Γ₀ t) := by
        exact exp_add_int_mul_two_pi_I_eq _ _
      _ = (γ t : ℂ) := hΓ₀ t
  have hshiftedΓ₀_zero : shiftedΓ₀ 0 = Γ₁ 0 := by
    calc
      shiftedΓ₀ 0 = Γ₀ 0 + n * (2 * Real.pi * Complex.I) := by
        rfl
      _ = Γ₁ 0 := by
        simpa using hn.symm
  have hshifted_eq : shiftedΓ₀ = Path.expLift γ (Γ₁ 0) hΓ₁0 :=
    eq_expLift γ (Γ₁ 0) hΓ₁0 shiftedΓ₀ hshiftedΓ₀ hshiftedΓ₀_zero
  have hΓ₁_eq : Γ₁ = Path.expLift γ (Γ₁ 0) hΓ₁0 :=
    eq_expLift γ (Γ₁ 0) hΓ₁0 Γ₁ hΓ₁ rfl
  have huniq : shiftedΓ₀ = Γ₁ := by
    calc
      shiftedΓ₀ = Path.expLift γ (Γ₁ 0) hΓ₁0 := hshifted_eq
      _ = Γ₁ := hΓ₁_eq.symm
  refine ⟨n, ?_⟩
  intro t
  have ht : shiftedΓ₀ t = Γ₁ t := by
    simpa using congrFun (congrArg DFunLike.coe huniq) t
  calc
    Γ₁ t = shiftedΓ₀ t := ht.symm
    _ = Γ₀ t + n * (2 * Real.pi * Complex.I) := by
      rfl

/-%%
\begin{proof}\leanok
At the initial point, the two lifts have the same exponential, so their values differ by an
integral multiple of $2\pi i$. Shifting one lift by that constant does not change its projection,
and uniqueness of lifts then shows the two lifts agree everywhere.
\end{proof}
%%-/

/-%%
\begin{definition}\label{pathWindingNumberNew}\lean{RootsComplexPolynomialsNew.Path.windingNumber}\uses{expLiftNew}\leanok
The winding number of a loop in $\C^\times$ is defined from the endpoint difference of a
lift through the exponential covering map.
\begin{verbatim}
noncomputable def windingNumber
    {u : ℂˣ} (γ : Path u u) :
    ℤ
\end{verbatim}
\end{definition}
%%-/

noncomputable def windingNumber {u : ℂˣ} (γ : Path u u) : ℤ := by
  let Γ := Path.expLift γ (unitLog u) (exp_unitLog u)
  have hper : Complex.exp (Γ 1) = Complex.exp (Γ 0) := by
    calc
      Complex.exp (Γ 1) = (γ 1 : ℂ) := expLift_apply γ (unitLog u) (exp_unitLog u) 1
      _ = (u : ℂ) := by
        simp [γ.target]
      _ = (γ 0 : ℂ) := by
        simp [γ.source]
      _ = Complex.exp (Γ 0) := by
        symm
        exact expLift_apply γ (unitLog u) (exp_unitLog u) 0
  exact Classical.choose ((Complex.exp_eq_exp_iff_exists_int).1 hper)

/-%%
\begin{proof}\leanok
Choose the lift beginning at $\log(z)$. Since the path is a loop, the endpoints of the lift have
the same exponential, hence differ by an integral multiple of $2\pi i$; that integer is the
winding number.
\end{proof}
%%-/

/-%%
\begin{lemma}\label{pathWindingNumber_eq_of_liftNew}\lean{RootsComplexPolynomialsNew.Path.windingNumber_eq_of_lift}\uses{pathWindingNumberNew, eq_add_int_mul_two_pi_I_of_liftsNew, expLiftNew, expLift_applyNew}\leanok
If $\Gamma$ is any lift of a loop in $\C^\times$, then the endpoint quotient
$(\Gamma(1)-\Gamma(0))/(2\pi i)$ computes the winding number.
\begin{verbatim}
theorem windingNumber_eq_of_lift
    {u : ℂˣ} (γ : Path u u) (Γ : C(I, ℂ))
    (hlift : ∀ t, Complex.exp (Γ t) = (γ t : ℂ)) :
    (Γ 1 - Γ 0) / (2 * Real.pi * Complex.I) =
    Path.windingNumber γ
\end{verbatim}
\end{lemma}
%%-/

theorem windingNumber_eq_of_lift {u : ℂˣ} (γ : Path u u)
    (Γ : C(I, ℂ)) (hlift : ∀ t, Complex.exp (Γ t) = (γ t : ℂ)) :
    (Γ 1 - Γ 0) / (2 * Real.pi * Complex.I) = Path.windingNumber γ := by
  let liftγ : C(I, ℂ) := Path.expLift γ (unitLog u) (exp_unitLog u)
  have hliftγ : ∀ t, Complex.exp (liftγ t) = (γ t : ℂ) := fun t =>
    expLift_apply γ (unitLog u) (exp_unitLog u) t
  obtain ⟨n, hshift_eq⟩ := eq_add_int_mul_two_pi_I_of_lifts γ liftγ Γ hliftγ hlift
  have hbase_eq :
      liftγ 1 = liftγ 0 + Path.windingNumber γ * (2 * Real.pi * Complex.I) := by
    unfold windingNumber
    dsimp [liftγ]
    exact Classical.choose_spec ((Complex.exp_eq_exp_iff_exists_int).1 <| by
      calc
        Complex.exp ((Path.expLift γ (unitLog u) (exp_unitLog u)) 1) = (γ 1 : ℂ) := by
          exact expLift_apply γ (unitLog u) (exp_unitLog u) 1
        _ = (u : ℂ) := by
          simp [γ.target]
        _ = (γ 0 : ℂ) := by
          simp [γ.source]
        _ = Complex.exp ((Path.expLift γ (unitLog u) (exp_unitLog u)) 0) := by
          symm
          exact expLift_apply γ (unitLog u) (exp_unitLog u) 0)
  have hbase :
      (liftγ 1 - liftγ 0) / (2 * Real.pi * Complex.I) = Path.windingNumber γ := by
    rw [hbase_eq]
    ring_nf
    field_simp [Complex.two_pi_I_ne_zero]
  calc
    (Γ 1 - Γ 0) / (2 * Real.pi * Complex.I)
        = ((liftγ 1 + n * (2 * Real.pi * Complex.I)) -
            (liftγ 0 + n * (2 * Real.pi * Complex.I))) / (2 * Real.pi * Complex.I) := by
            rw [hshift_eq 1, hshift_eq 0]
    _ = (liftγ 1 - liftγ 0) / (2 * Real.pi * Complex.I) := by ring
    _ = Path.windingNumber γ := hbase

/-%%
\begin{proof}\leanok
Any lift differs from the canonical lift by a constant integral multiple of $2\pi i$, so the
endpoint difference and hence the quotient by $2\pi i$ are unchanged.
\end{proof}
%%-/

/-%%
\begin{lemma}\label{pathWindingNumber_eq_of_homotopyNew}\lean{RootsComplexPolynomialsNew.Path.windingNumber_eq_of_homotopy}\uses{pathWindingNumber_eq_of_liftNew, eq_add_int_mul_two_pi_I_of_liftsNew, IsLoopHomotopyNew, expLiftNew, expLift_applyNew, expLift_zeroNew}\leanok
Loops in $\C^\times$ that are freely homotopic through loops have the same winding number.
\begin{verbatim}
theorem windingNumber_eq_of_homotopy
    {u u' : ℂˣ} (γ : Path u u)
    (γ' : Path u' u') (H : C(I × I, ℂˣ))
    (hhom : ContinuousMap.IsLoopHomotopy H)
    (hzero : ∀ t, H (0, t) = γ t)
    (hone : ∀ t, H (1, t) = γ' t) :
    Path.windingNumber γ = Path.windingNumber γ'
\end{verbatim}
\end{lemma}
%%-/

theorem windingNumber_eq_of_homotopy {u u' : ℂˣ}
    (γ : Path u u) (γ' : Path u' u') (H : C(I × I, ℂˣ))
    (hhom : ContinuousMap.IsLoopHomotopy H) (hzero : ∀ t, H (0, t) = γ t)
    (hone : ∀ t, H (1, t) = γ' t) :
    Path.windingNumber γ = Path.windingNumber γ' := by
  let tildeγ : C(I, ℂ) := Path.expLift γ (unitLog u) (exp_unitLog u)
  have htildeγ : ∀ t, Complex.exp (tildeγ t) = (γ t : ℂ) := fun t =>
    expLift_apply γ (unitLog u) (exp_unitLog u) t
  let H' : C(I × I, {z : ℂ // z ≠ 0}) :=
    (complexUnitsHomeomorphNeZero : C(ℂˣ, {z : ℂ // z ≠ 0})).comp H
  have hH0 : ∀ t, H' (0, t) = ⟨Complex.exp (tildeγ t), Complex.exp_ne_zero _⟩ := by
    intro t
    apply Subtype.ext
    calc
      (H' (0, t) : ℂ) = (H (0, t) : ℂ) := by
        rfl
      _ = (γ t : ℂ) := by
        simpa using congrArg (fun z : ℂˣ => (z : ℂ)) (hzero t)
      _ = Complex.exp (tildeγ t) := by
        symm
        exact htildeγ t
  let tildeH : C(I × I, ℂ) := Complex.isCoveringMap_exp.liftHomotopy H' tildeγ hH0
  have htildeH_lifts : ∀ x, Complex.exp (tildeH x) = (H x : ℂ) := by
    intro x
    simpa [H'] using congrArg Subtype.val <| congrFun
      (Complex.isCoveringMap_exp.liftHomotopy_lifts H' tildeγ hH0) x
  have htildeH_zero : ∀ t, tildeH (0, t) = tildeγ t := by
    intro t
    simpa using Complex.isCoveringMap_exp.liftHomotopy_zero (H := H') (f := tildeγ)
      (H_0 := hH0) t
  let μ : Path u u' := {
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
          simpa using congrArg (fun z : ℂˣ => (z : ℂ)) (hhom s).symm
        _ = (μ s : ℂ) := by rfl
    · simpa [μ1] using htildeH_zero 1
  obtain ⟨n, hshift_eq⟩ := eq_add_int_mul_two_pi_I_of_lifts μ μ0 μ1 hμ0.1 hμ1.1
  let tildeγ' : C(I, ℂ) :=
    ⟨fun t => tildeH (1, t), tildeH.continuous.comp (continuous_const.prodMk continuous_id)⟩
  have htildeγ' : ∀ t, Complex.exp (tildeγ' t) = (γ' t : ℂ) := by
    intro t
    calc
      Complex.exp (tildeγ' t) = (H (1, t) : ℂ) := by
        simpa [tildeγ'] using htildeH_lifts (1, t)
      _ = (γ' t : ℂ) := by
        simpa using congrArg (fun z : ℂˣ => (z : ℂ)) (hone t)
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
      ((Path.windingNumber γ : ℤ) : ℂ) = ((Path.windingNumber γ' : ℤ) : ℂ) := by
    calc
      ((Path.windingNumber γ : ℤ) : ℂ)
          = (tildeγ 1 - tildeγ 0) / (2 * Real.pi * Complex.I) := by
              symm
              exact windingNumber_eq_of_lift γ tildeγ htildeγ
      _ = (tildeγ' 1 - tildeγ' 0) / (2 * Real.pi * Complex.I) := by
            symm
            exact hwind
      _ = ((Path.windingNumber γ' : ℤ) : ℂ) := by
            exact windingNumber_eq_of_lift γ' tildeγ' htildeγ'
  exact_mod_cast hcast

/-%%
\begin{proof}\leanok
Lift the whole free homotopy through the exponential covering map. The two boundary loops of the
lift differ by a constant integral multiple of $2\pi i$ along the side edges, so their endpoint
differences agree and hence their winding numbers agree.
\end{proof}
%%-/

/-%%
\begin{lemma}\label{pathWindingNumber_reflNew}\lean{RootsComplexPolynomialsNew.Path.windingNumber_refl}\uses{pathWindingNumber_eq_of_liftNew}\leanok
The constant loop has winding number zero.
\begin{verbatim}
theorem windingNumber_refl
    (u : ℂˣ) :
    Path.windingNumber (Path.refl u) = 0
\end{verbatim}
\end{lemma}
%%-/

@[simp] theorem windingNumber_refl (u : ℂˣ) :
    Path.windingNumber (Path.refl u) = 0 := by
  let Γ : C(I, ℂ) := ContinuousMap.const _ (unitLog u)
  have hlift : ∀ t, Complex.exp (Γ t) = ((Path.refl u) t : ℂ) := by
    intro t
    simp [Γ]
  have hq : (Γ 1 - Γ 0) / (2 * Real.pi * Complex.I) = Path.windingNumber (Path.refl u) :=
    windingNumber_eq_of_lift (Path.refl u) Γ hlift
  simpa [Γ] using hq.symm

/-%%
\begin{proof}\leanok
The constant loop is lifted by a constant logarithm, whose endpoint difference is zero.
\end{proof}
%%-/

end Path

/-%%
\section{Winding numbers of circle maps}
%%-/

namespace ContinuousMap

/-%%
\begin{definition}\label{circleWindingNumberNew}\lean{RootsComplexPolynomialsNew.ContinuousMap.windingNumber}\uses{circleLoopNew, pathWindingNumberNew}\leanok
The winding number of a continuous map from the circle to $\C^\times$ is the winding number of its
associated loop.
\begin{verbatim}
noncomputable def windingNumber
    (f : C(Circle, ℂˣ)) :
    ℤ
\end{verbatim}
\end{definition}
%%-/

noncomputable def windingNumber (f : C(Circle, ℂˣ)) : ℤ :=
  Path.windingNumber (ContinuousMap.circleLoop f)

/-%%
\begin{proof}\leanok
This is the modern `Path`-based version of passing from a circle map to its associated loop and
taking the loop winding number.
\end{proof}
%%-/

/-%%
\begin{lemma}\label{circleWindingNumber_constNew}\lean{RootsComplexPolynomialsNew.ContinuousMap.windingNumber_const}\uses{circleWindingNumberNew, pathWindingNumber_reflNew, circleLoopNew}\leanok
A constant map from the circle to $\C^\times$ has winding number zero.
\begin{verbatim}
theorem windingNumber_const
    (c : ℂˣ) :
    windingNumber (ContinuousMap.const _ c :
    C(Circle, ℂˣ)) = 0
\end{verbatim}
\end{lemma}
%%-/

@[simp] theorem windingNumber_const (c : ℂˣ) :
    windingNumber (ContinuousMap.const _ c : C(Circle, ℂˣ)) = 0 := by
  change Path.windingNumber (ContinuousMap.circleLoop (ContinuousMap.const _ c : C(Circle, ℂˣ))) = 0
  have hloop : ContinuousMap.circleLoop (ContinuousMap.const _ c : C(Circle, ℂˣ)) = Path.refl c := by
    ext t
    rfl
  rw [hloop]
  exact Path.windingNumber_refl c

/-%%
\begin{proof}\leanok
The associated loop of a constant circle map is the constant loop, whose winding number is zero.
\end{proof}
%%-/

/-%%
\begin{lemma}\label{circleWindingNumber_eq_of_homotopyNew}\lean{RootsComplexPolynomialsNew.ContinuousMap.windingNumber_eq_of_homotopy}\uses{circleWindingNumberNew, pathWindingNumber_eq_of_homotopyNew, circleLoopHomotopyNew, circleLoopHomotopy_applyNew, circleLoopHomotopy_isLoopHomotopyNew, circleLoopHomotopy_zero_leftNew, circleLoopHomotopy_one_leftNew}\leanok
Homotopic circle maps into $\C^\times$ have the same winding number.
\begin{verbatim}
theorem windingNumber_eq_of_homotopy
    {f g : C(Circle, ℂˣ)}
    (H : ContinuousMap.Homotopy f g) :
    windingNumber f = windingNumber g
\end{verbatim}
\end{lemma}
%%-/

theorem windingNumber_eq_of_homotopy {f g : C(Circle, ℂˣ)} (H : ContinuousMap.Homotopy f g) :
    windingNumber f = windingNumber g := by
  simpa [windingNumber] using
    Path.windingNumber_eq_of_homotopy (ContinuousMap.circleLoop f) (ContinuousMap.circleLoop g) (circleLoopHomotopy H)
      (circleLoopHomotopy_isLoopHomotopy H) (circleLoopHomotopy_zero_left H)
      (circleLoopHomotopy_one_left H)

/-%%
\begin{proof}\leanok
Precompose the homotopy with the standard parametrization of the circle to obtain a free homotopy
between the associated loops, then apply homotopy invariance for loop winding numbers.
\end{proof}
%%-/

/-%%
\begin{lemma}\label{exists_homotopy_of_norm_sub_ltNew}\lean{RootsComplexPolynomialsNew.ContinuousMap.exists_homotopy_of_norm_sub_lt}\leanok
If two maps into $\Bbbk^\times$ satisfy the walking-dog inequality
$\lVert f(x)-g(x)\rVert < \lVert f(x)\rVert$ pointwise, then they are homotopic through maps into
$\Bbbk^\times$.
\begin{verbatim}
theorem exists_homotopy_of_norm_sub_lt
    [TopologicalSpace α] [RCLike 𝕜]
    {f g : C(α, 𝕜ˣ)}
    (hclose :
      ∀ z : α, ‖(f z : 𝕜) - g z‖ <
        ‖(f z : 𝕜)‖) :
    Nonempty (ContinuousMap.Homotopy f g)
\end{verbatim}
\end{lemma}
%%-/

theorem exists_homotopy_of_norm_sub_lt {α : Type*} [TopologicalSpace α]
    {𝕜 : Type*} [RCLike 𝕜] {f g : C(α, 𝕜ˣ)}
    (hclose : ∀ z : α, ‖(f z : 𝕜) - g z‖ < ‖(f z : 𝕜)‖) :
    Nonempty (ContinuousMap.Homotopy f g) := by
  let Hbase : C(I × α, 𝕜) :=
    ⟨fun x =>
      (((1 - (x.1 : ℝ)) : 𝕜) * (f x.2 : 𝕜)) + (((x.1 : ℝ) : 𝕜) * (g x.2 : 𝕜)), by
        fun_prop⟩
  have hHbase : ∀ x : I × α, Hbase x ≠ 0 := by
    intro x hx
    have hs0 : 0 ≤ (x.1 : ℝ) := x.1.2.1
    have hs1 : (x.1 : ℝ) ≤ 1 := x.1.2.2
    have hsNorm : ‖((x.1 : ℝ) : 𝕜)‖ ≤ 1 := by
      simpa [RCLike.norm_ofReal, abs_of_nonneg hs0] using hs1
    have hle :
        ‖((x.1 : ℝ) : 𝕜) * ((f x.2 : 𝕜) - g x.2)‖ ≤ ‖(f x.2 : 𝕜) - g x.2‖ := by
      calc
        ‖((x.1 : ℝ) : 𝕜) * ((f x.2 : 𝕜) - g x.2)‖
            = ‖((x.1 : ℝ) : 𝕜)‖ * ‖(f x.2 : 𝕜) - g x.2‖ := norm_mul _ _
        _ ≤ 1 * ‖(f x.2 : 𝕜) - g x.2‖ := by gcongr
        _ = ‖(f x.2 : 𝕜) - g x.2‖ := by ring
    have hEq : (f x.2 : 𝕜) = ((x.1 : ℝ) : 𝕜) * ((f x.2 : 𝕜) - g x.2) := by
      calc
        (f x.2 : 𝕜) = (f x.2 : 𝕜) - Hbase x := by rw [hx]; ring
        _ = ((x.1 : ℝ) : 𝕜) * ((f x.2 : 𝕜) - g x.2) := by
              simp [Hbase]
              ring
    have hlt : ‖(f x.2 : 𝕜)‖ < ‖(f x.2 : 𝕜)‖ := by
      calc
        ‖(f x.2 : 𝕜)‖
            = ‖((x.1 : ℝ) : 𝕜) * ((f x.2 : 𝕜) - g x.2)‖ := by
                exact congrArg norm hEq
        _ ≤ ‖(f x.2 : 𝕜) - g x.2‖ := hle
        _ < ‖(f x.2 : 𝕜)‖ := hclose x.2
    exact (lt_irrefl ‖(f x.2 : 𝕜)‖ hlt).elim
  let H : C(I × α, 𝕜ˣ) :=
    ContinuousMap.unitsOfForallIsUnit (f := Hbase) fun x => isUnit_iff_ne_zero.mpr (hHbase x)
  refine ⟨{ toContinuousMap := H, map_zero_left := ?_, map_one_left := ?_ }⟩
  · intro z
    apply Units.ext
    simp [H, Hbase]
  · intro z
    apply Units.ext
    simp [H, Hbase]

/-%%
\begin{proof}\leanok
Use the straight-line homotopy $(1-t)f+t g$. If this vanished at some point, then
$f=t(f-g)$ there, which would force $\|f\|\le \|f-g\|$, contradicting the hypothesis.
\end{proof}
%%-/

/-%%
\begin{corollary}\label{circleWindingNumber_eq_of_norm_sub_ltNew}\lean{RootsComplexPolynomialsNew.ContinuousMap.windingNumber_eq_of_norm_sub_lt}\uses{exists_homotopy_of_norm_sub_ltNew, circleWindingNumber_eq_of_homotopyNew}\leanok
Circle maps satisfying the walking-dog inequality have the same winding number.
\begin{verbatim}
theorem windingNumber_eq_of_norm_sub_lt
    {f g : C(Circle, ℂˣ)}
    (hclose :
      ∀ z : Circle, ‖(f z : ℂ) - g z‖ <
        ‖(f z : ℂ)‖) :
    windingNumber f = windingNumber g
\end{verbatim}
\end{corollary}
%%-/

theorem windingNumber_eq_of_norm_sub_lt {f g : C(Circle, ℂˣ)}
    (hclose : ∀ z : Circle, ‖(f z : ℂ) - g z‖ < ‖(f z : ℂ)‖) :
    windingNumber f = windingNumber g := by
  obtain ⟨H⟩ := exists_homotopy_of_norm_sub_lt hclose
  exact windingNumber_eq_of_homotopy H

/-%%
\begin{proof}\leanok
Apply the previous existence theorem for a homotopy and then homotopy invariance of winding
number.
\end{proof}
%%-/

/-%%
\begin{theorem}\label{circleWindingNumber_eq_zero_of_exists_extensionNew}\lean{RootsComplexPolynomialsNew.ContinuousMap.windingNumber_eq_zero_of_exists_extension}\uses{circleToClosedUnitDiskNew, circleWindingNumber_eq_of_homotopyNew, circleWindingNumber_constNew}\leanok
If a map from the unit circle to $\C^\times$ extends to the closed unit disk through maps into
$\C^\times$, then its winding number is zero.
\begin{verbatim}
theorem windingNumber_eq_zero_of_exists_extension
    {f : C(Circle, ℂˣ)}
    {F : C(Metric.closedBall (0 : ℂ) 1, ℂˣ)}
    (hF :
      ∀ z : Circle,
        F (Circle.toClosedUnitDisk z) = f z) :
    windingNumber f = 0
\end{verbatim}
\end{theorem}
%%-/

theorem windingNumber_eq_zero_of_exists_extension {f : C(Circle, ℂˣ)}
    {F : C(Metric.closedBall (0 : ℂ) 1, ℂˣ)}
    (hF : ∀ z : Circle, F (Circle.toClosedUnitDisk z) = f z) :
    windingNumber f = 0 := by
  let Jfun : I × Circle → ℂ := fun x =>
    (((1 - (x.1 : ℝ)) : ℂ) * (x.2 : ℂ))
  have hJfun_mem : ∀ x : I × Circle, Jfun x ∈ Metric.closedBall (0 : ℂ) 1 := by
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
  let J : C(I × Circle, Metric.closedBall (0 : ℂ) 1) :=
    ⟨fun x => ⟨Jfun x, hJfun_mem x⟩, Continuous.subtype_mk (by fun_prop) hJfun_mem⟩
  let H : C(I × Circle, ℂˣ) := F.comp J
  have hJ0 : ∀ z : Circle, J (0, z) = Circle.toClosedUnitDisk z := by
    intro z
    apply Subtype.ext
    simp [J, Jfun]
  have hJ1 : ∀ z : Circle, J (1, z) = 0 := by
    intro z
    apply Subtype.ext
    simp [J, Jfun]
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

/-%%
\begin{proof}\leanok
Radially contract the closed disk to its center. Composing the extension with this contraction
produces a homotopy from the boundary map to a constant map, and constant maps have winding number
zero.
\end{proof}
%%-/

end ContinuousMap

/-%%
\section{Monomials on the circle}
%%-/

/-%%
\begin{definition}\label{circleScaledMonomialNew}\lean{RootsComplexPolynomialsNew.circleScaledMonomial}\leanok
Given $a,c\in \C^\times$ and $n\in \mathbb N$, define the circle map
$z\mapsto a\,(cz)^n$ with values in $\C^\times$.
\begin{verbatim}
noncomputable def circleScaledMonomial
    (a c : ℂˣ) (n : ℕ) :
    C(Circle, ℂˣ)
\end{verbatim}
\end{definition}
%%-/

noncomputable def circleScaledMonomial (a c : ℂˣ) (n : ℕ) : C(Circle, ℂˣ) :=
  ContinuousMap.unitsOfForallIsUnit
    (f := ⟨fun z => a * (((c : ℂ) * z) ^ n), by
      fun_prop⟩)
    fun z => by
      exact isUnit_iff_ne_zero.mpr <|
        mul_ne_zero a.ne_zero (pow_ne_zero n <| mul_ne_zero c.ne_zero (Circle.coe_ne_zero z))

/-%%
\begin{proof}\leanok
The underlying formula is continuous, and it never vanishes because $a$, $c$, and every point of
the circle are nonzero.
\end{proof}
%%-/

/-%%
\begin{definition}\label{circleMonomialNew}\lean{RootsComplexPolynomialsNew.circleMonomial}\uses{circleScaledMonomialNew}\leanok
For $R>0$, the map $z\mapsto a\,(Rz)^n$ is obtained by specializing the previous construction to
the nonzero scalar $R$.
\begin{verbatim}
noncomputable def circleMonomial
    (a : ℂˣ) (n : ℕ) (R : ℝ) (hR : 0 < R) :
    C(Circle, ℂˣ)
\end{verbatim}
\end{definition}
%%-/

noncomputable def circleMonomial (a : ℂˣ) (n : ℕ) (R : ℝ) (hR : 0 < R) : C(Circle, ℂˣ) :=
  circleScaledMonomial a (Units.mk0 (R : ℂ) (by exact_mod_cast hR.ne')) n

/-%%
\begin{proof}\leanok
This is just the scaled monomial with $c=R\in \C^\times$.
\end{proof}
%%-/

/-%%
\begin{lemma}\label{coe_circleMonomial_applyNew}\lean{RootsComplexPolynomialsNew.coe_circleMonomial_apply}\uses{circleMonomialNew, circleScaledMonomialNew}\leanok
After coercing to $\C$, the circle monomial evaluates as $a\,(Rz)^n$.
\begin{verbatim}
theorem coe_circleMonomial_apply
    (a : ℂˣ) (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z : Circle) :
    ((circleMonomial a n R hR z : ℂˣ) : ℂ) =
    a * (((R : ℂ) * z) ^ n)
\end{verbatim}
\end{lemma}
%%-/

@[simp] theorem coe_circleMonomial_apply (a : ℂˣ) (n : ℕ) (R : ℝ) (hR : 0 < R) (z : Circle) :
    ((circleMonomial a n R hR z : ℂˣ) : ℂ) = a * (((R : ℂ) * z) ^ n) := by
  simp [circleMonomial, circleScaledMonomial]

/-%%
\begin{proof}\leanok
Unfold the specialized definition and simplify.
\end{proof}
%%-/

/-%%
\begin{theorem}\label{circleScaledMonomial_windingNumberNew}\lean{RootsComplexPolynomialsNew.circleScaledMonomial_windingNumber}\uses{circleScaledMonomialNew, circleWindingNumberNew, pathWindingNumber_eq_of_liftNew, circleLoopNew, circleLoop_applyNew}\leanok
The winding number of the map $z\mapsto a\,(cz)^n$ on the unit circle is $n$.
\begin{verbatim}
theorem circleScaledMonomial_windingNumber
    (a c : ℂˣ) (n : ℕ) :
    ContinuousMap.windingNumber
    (circleScaledMonomial a c n) = (n : ℤ)
\end{verbatim}
\end{theorem}
%%-/

theorem circleScaledMonomial_windingNumber (a c : ℂˣ) (n : ℕ) :
    ContinuousMap.windingNumber (circleScaledMonomial a c n) = (n : ℤ) := by
  let c0 : ℂˣ := a * c ^ n
  let a0 : ℂ := Complex.log (c0 : ℂ)
  have ha0 : Complex.exp a0 = (c0 : ℂ) := by
    simpa [a0] using Complex.exp_log c0.ne_zero
  let tildeω : C(I, ℂ) := by
    refine ⟨fun t => a0 + (n : ℂ) * ((2 * Real.pi : ℂ) * (t : ℂ)) * Complex.I, ?_⟩
    fun_prop
  have hlift :
      ∀ t,
        Complex.exp (tildeω t) =
          (((ContinuousMap.circleLoop (circleScaledMonomial a c n)) t : ℂˣ) : ℂ) := by
    intro t
    calc
      Complex.exp (tildeω t)
          = Complex.exp a0 *
              Complex.exp (((n : ℂ) * ((2 * Real.pi : ℂ) * (t : ℂ))) * Complex.I) := by
              simp [tildeω, Complex.exp_add]
      _ = ((a : ℂ) * (c : ℂ) ^ n) *
            Complex.exp (((n : ℂ) * ((2 * Real.pi : ℂ) * (t : ℂ))) * Complex.I) := by
            simpa [c0] using
              congrArg
                (fun z : ℂ => z * Complex.exp (((n : ℂ) * ((2 * Real.pi : ℂ) * (t : ℂ))) * Complex.I))
                ha0
      _ = ((a : ℂ) * (c : ℂ) ^ n) *
            Complex.exp ((n : ℂ) * (((2 * Real.pi : ℂ) * (t : ℂ)) * Complex.I)) := by
            ring_nf
      _ = ((a : ℂ) * (c : ℂ) ^ n) *
            (Complex.exp (((2 * Real.pi : ℂ) * (t : ℂ)) * Complex.I)) ^ n := by
            rw [Complex.exp_nat_mul]
      _ = ((a : ℂ) * (c : ℂ) ^ n) * (Circle.exp (2 * Real.pi * (t : ℝ)) : ℂ) ^ n := by
            simp [Circle.coe_exp]
      _ = (a : ℂ) * (((c : ℂ) * (Circle.exp (2 * Real.pi * (t : ℝ)) : ℂ)) ^ n) := by
            rw [mul_pow]
            ring
      _ = (((ContinuousMap.circleLoop (circleScaledMonomial a c n)) t : ℂˣ) : ℂ) := by
            change (a : ℂ) * (((c : ℂ) * Circle.exp (2 * Real.pi * (t : ℝ))) ^ n) =
              ((circleScaledMonomial a c n (Circle.exp (2 * Real.pi * (t : ℝ))) : ℂˣ) : ℂ)
            rfl
  have hwind : (((ContinuousMap.windingNumber (circleScaledMonomial a c n) : ℤ) : ℂ)) = n := by
    calc
      (((ContinuousMap.windingNumber (circleScaledMonomial a c n) : ℤ) : ℂ))
          = (tildeω 1 - tildeω 0) / ((2 * Real.pi : ℂ) * Complex.I) := by
              symm
              simpa [ContinuousMap.windingNumber] using
                Path.windingNumber_eq_of_lift (ContinuousMap.circleLoop (circleScaledMonomial a c n)) tildeω hlift
      _ = ((n : ℂ) * (2 * Real.pi : ℂ) * Complex.I) / ((2 * Real.pi : ℂ) * Complex.I) := by
            simp [tildeω]
      _ = (n : ℂ) := by
            have hpi : (Real.pi : ℂ) ≠ 0 := by
              exact_mod_cast Real.pi_ne_zero
            field_simp [tildeω, hpi, Complex.I_ne_zero]
  exact_mod_cast hwind

/-%%
\begin{proof}\leanok
Choose a logarithm of the nonzero constant $a c^n$. Then
$t\mapsto \log(ac^n)+n(2\pi t)i$ is a lift of the associated loop, and its endpoint difference is
exactly $2\pi n i$.
\end{proof}
%%-/

/-%%
\begin{theorem}\label{circleMonomial_windingNumberNew}\lean{RootsComplexPolynomialsNew.circleMonomial_windingNumber}\uses{circleMonomialNew, circleScaledMonomial_windingNumberNew}\leanok
For $R>0$, the winding number of the map $z\mapsto a\,(Rz)^n$ on the unit circle is $n$.
\begin{verbatim}
theorem circleMonomial_windingNumber
    (a : ℂˣ) (n : ℕ) (R : ℝ) (hR : 0 < R) :
    ContinuousMap.windingNumber (circleMonomial a
    n R hR) = (n : ℤ)
\end{verbatim}
\end{theorem}
%%-/

theorem circleMonomial_windingNumber (a : ℂˣ) (n : ℕ) (R : ℝ) (hR : 0 < R) :
    ContinuousMap.windingNumber (circleMonomial a n R hR) = (n : ℤ) := by
  simpa [circleMonomial] using
    circleScaledMonomial_windingNumber a (Units.mk0 (R : ℂ) (by exact_mod_cast hR.ne')) n

/-%%
\begin{proof}\leanok
This is the previous theorem applied to the special case $c=R\in \C^\times$.
\end{proof}
%%-/

/-%%
\section{Polynomial maps on the circle and disk}
%%-/

namespace Polynomial

/-%%
\begin{definition}\label{mapCircleUnitsNew}\lean{RootsComplexPolynomialsNew.Polynomial.mapCircleUnits}\leanok
If a polynomial has no zeros on the circle of radius $R$, then $z\mapsto p(Rz)$ defines a map
from the unit circle to $\C^\times$.
\begin{verbatim}
noncomputable def mapCircleUnits
    (p : Polynomial ℂ) (R : ℝ)
    (hR : ∀ z : Circle, p.eval ((R : ℂ) * z) ≠ 0)
    :
    C(Circle, ℂˣ)
\end{verbatim}
\end{definition}
%%-/

noncomputable def mapCircleUnits (p : Polynomial ℂ) (R : ℝ)
    (hR : ∀ z : Circle, p.eval ((R : ℂ) * z) ≠ 0) : C(Circle, ℂˣ) :=
  ContinuousMap.unitsOfForallIsUnit
    (f := ⟨fun z => p.eval ((R : ℂ) * z), p.continuous.comp (continuous_const.mul continuous_subtype_val)⟩)
    fun z => isUnit_iff_ne_zero.mpr (hR z)

/-%%
\begin{proof}\leanok
The polynomial evaluation map is continuous, and the nonvanishing hypothesis upgrades it to a
units-valued map.
\end{proof}
%%-/

/-%%
\begin{definition}\label{mapClosedUnitDiskUnitsNew}\lean{RootsComplexPolynomialsNew.Polynomial.mapClosedUnitDiskUnits}\leanok
If a polynomial has no zeros on the closed unit disk of radius $R$, then $z\mapsto p(Rz)$ defines
a map from that disk to $\C^\times$.
\begin{verbatim}
noncomputable def mapClosedUnitDiskUnits
    (p : Polynomial ℂ) (R : ℝ)
    (hR :
      ∀ z : Metric.closedBall (0 : ℂ) 1,
        p.eval ((R : ℂ) * z) ≠ 0) :
    C(Metric.closedBall (0 : ℂ) 1, ℂˣ)
\end{verbatim}
\end{definition}
%%-/

noncomputable def mapClosedUnitDiskUnits (p : Polynomial ℂ) (R : ℝ)
    (hR : ∀ z : Metric.closedBall (0 : ℂ) 1, p.eval ((R : ℂ) * z) ≠ 0) :
    C(Metric.closedBall (0 : ℂ) 1, ℂˣ) :=
  ContinuousMap.unitsOfForallIsUnit
    (f := ⟨fun z => p.eval ((R : ℂ) * z), p.continuous.comp (continuous_const.mul continuous_subtype_val)⟩)
    fun z => isUnit_iff_ne_zero.mpr (hR z)

/-%%
\begin{proof}\leanok
This is the disk-valued analogue of the previous construction.
\end{proof}
%%-/

/-%%
\begin{lemma}\label{coe_mapCircleUnits_applyNew}\lean{RootsComplexPolynomialsNew.Polynomial.coe_mapCircleUnits_apply}\uses{mapCircleUnitsNew}\leanok
After coercing to $\C$, the circle-valued units map evaluates as $p(Rz)$.
\begin{verbatim}
theorem coe_mapCircleUnits_apply
    (p : Polynomial ℂ) (R : ℝ)
    (hR : ∀ z : Circle, p.eval ((R : ℂ) * z) ≠ 0)
    (z : Circle) :
    ((Polynomial.mapCircleUnits p R hR z : ℂˣ) :
    ℂ) = p.eval ((R : ℂ) * z)
\end{verbatim}
\end{lemma}
%%-/

@[simp] theorem coe_mapCircleUnits_apply (p : Polynomial ℂ) (R : ℝ)
    (hR : ∀ z : Circle, p.eval ((R : ℂ) * z) ≠ 0) (z : Circle) :
    ((Polynomial.mapCircleUnits p R hR z : ℂˣ) : ℂ) = p.eval ((R : ℂ) * z) := rfl

/-%%
\begin{proof}\leanok
This is immediate from the definition.
\end{proof}
%%-/

/-%%
\begin{lemma}\label{coe_mapClosedUnitDiskUnits_applyNew}\lean{RootsComplexPolynomialsNew.Polynomial.coe_mapClosedUnitDiskUnits_apply}\uses{mapClosedUnitDiskUnitsNew}\leanok
After coercing to $\C$, the disk-valued units map evaluates as $p(Rz)$.
\begin{verbatim}
theorem coe_mapClosedUnitDiskUnits_apply
    (p : Polynomial ℂ) (R : ℝ)
    (hR :
      ∀ z : Metric.closedBall (0 : ℂ) 1,
        p.eval ((R : ℂ) * z) ≠ 0)
    (z : Metric.closedBall (0 : ℂ) 1) :
    ((Polynomial.mapClosedUnitDiskUnits p R hR z :
    ℂˣ) : ℂ) = p.eval ((R : ℂ) * z)
\end{verbatim}
\end{lemma}
%%-/

@[simp] theorem coe_mapClosedUnitDiskUnits_apply (p : Polynomial ℂ) (R : ℝ)
    (hR : ∀ z : Metric.closedBall (0 : ℂ) 1, p.eval ((R : ℂ) * z) ≠ 0)
    (z : Metric.closedBall (0 : ℂ) 1) :
    ((Polynomial.mapClosedUnitDiskUnits p R hR z : ℂˣ) : ℂ) = p.eval ((R : ℂ) * z) := rfl

/-%%
\begin{proof}\leanok
Again this is immediate from the definition.
\end{proof}
%%-/

/-%%
\begin{lemma}\label{leadingTerm_dominates_on_circleNew}\lean{RootsComplexPolynomialsNew.Polynomial.leadingTerm_dominates_on_circle}\leanok
For a nonconstant complex polynomial, there is a radius beyond which the leading term dominates the
sum of the lower terms on every circle of larger radius.
\begin{verbatim}
theorem leadingTerm_dominates_on_circle
    (p : Polynomial ℂ) (hdeg : 0 < p.natDegree) :
    ∃ R0 : ℝ, 0 < R0 ∧ ∀ R : ℝ, R0 ≤ R →
    ∀ z : Circle, ‖p.eval ((R : ℂ) * z) -
    p.leadingCoeff * (((R : ℂ) * z) ^
    p.natDegree)‖ < ‖p.leadingCoeff * (((R : ℂ) *
    z) ^ p.natDegree)‖
\end{verbatim}
\end{lemma}
%%-/

theorem leadingTerm_dominates_on_circle (p : Polynomial ℂ) (hdeg : 0 < p.natDegree) :
    ∃ R0 : ℝ, 0 < R0 ∧ ∀ R : ℝ, R0 ≤ R → ∀ z : Circle,
      ‖p.eval ((R : ℂ) * z) - p.leadingCoeff * (((R : ℂ) * z) ^ p.natDegree)‖ <
        ‖p.leadingCoeff * (((R : ℂ) * z) ^ p.natDegree)‖ := by
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

/-%%
\begin{proof}\leanok
Choose $R$ so large that the sum of the lower-order coefficients is small compared with the
leading coefficient. On the circle of radius $R$, the lower-order terms are then bounded by a
strictly smaller quantity than the norm of the leading term.
\end{proof}
%%-/

/-%%
\begin{corollary}\label{eventually_leadingTerm_dominates_on_circleNew}\lean{RootsComplexPolynomialsNew.Polynomial.eventually_leadingTerm_dominates_on_circle}\uses{leadingTerm_dominates_on_circleNew}\leanok
Equivalently, the leading-term domination estimate holds eventually along the filter $R\to +\infty$.
\begin{verbatim}
theorem eventually_leadingTerm_dominates_on_circle
    (p : Polynomial ℂ) (hdeg : 0 < p.natDegree) :
    ∀ᶠ R : ℝ in Filter.atTop, ∀ z : Circle,
      ‖p.eval ((R : ℂ) * z) -
        p.leadingCoeff * (((R : ℂ) * z) ^
          p.natDegree)‖ <
        ‖p.leadingCoeff * (((R : ℂ) * z) ^
          p.natDegree)‖
\end{verbatim}
\end{corollary}
%%-/

theorem eventually_leadingTerm_dominates_on_circle (p : Polynomial ℂ) (hdeg : 0 < p.natDegree) :
    ∀ᶠ R : ℝ in Filter.atTop, ∀ z : Circle,
      ‖p.eval ((R : ℂ) * z) - p.leadingCoeff * (((R : ℂ) * z) ^ p.natDegree)‖ <
        ‖p.leadingCoeff * (((R : ℂ) * z) ^ p.natDegree)‖ := by
  obtain ⟨R0, -, hdom⟩ := leadingTerm_dominates_on_circle p hdeg
  exact Filter.eventually_atTop.2 ⟨R0, fun R hR => hdom R hR⟩

/-%%
\begin{proof}\leanok
This is the previous threshold statement rewritten in the standard `atTop` language.
\end{proof}
%%-/

/-%%
\begin{theorem}\label{eventually_windingNumber_eq_natDegreeNew}\lean{RootsComplexPolynomialsNew.Polynomial.eventually_windingNumber_eq_natDegree}\uses{eventually_leadingTerm_dominates_on_circleNew, mapCircleUnitsNew, coe_mapCircleUnits_applyNew, circleMonomialNew, coe_circleMonomial_applyNew, circleWindingNumber_eq_of_norm_sub_ltNew, circleMonomial_windingNumberNew}\leanok
For all sufficiently large $R$, the restriction of a nonconstant polynomial to the circle of
radius $R$ has winding number equal to the degree of the polynomial.
\begin{verbatim}
theorem eventually_windingNumber_eq_natDegree
    (p : Polynomial ℂ) (hdeg : 0 < p.natDegree) :
    ∀ᶠ R : ℝ in Filter.atTop,
      ∃ f : C(Circle, ℂˣ), (∀ z, (f z : ℂ) = p.eval
      ((R : ℂ) * z)) ∧ ContinuousMap.windingNumber f
      = (p.natDegree : ℤ)
\end{verbatim}
\end{theorem}
%%-/

theorem eventually_windingNumber_eq_natDegree (p : Polynomial ℂ) (hdeg : 0 < p.natDegree) :
    ∀ᶠ R : ℝ in Filter.atTop,
      ∃ f : C(Circle, ℂˣ), (∀ z, (f z : ℂ) = p.eval ((R : ℂ) * z)) ∧
        ContinuousMap.windingNumber f = (p.natDegree : ℤ) := by
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ),
      eventually_leadingTerm_dominates_on_circle p hdeg]
      with R hRpos hdom
  have hp : p ≠ 0 := by
    intro hp0
    simp [hp0] at hdeg
  have hlead : p.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp
  let a0 : ℂˣ := Units.mk0 p.leadingCoeff hlead
  have hpoly_nonzero : ∀ z : Circle, p.eval ((R : ℂ) * z) ≠ 0 := by
    intro z hz
    have hbad :
        ‖p.leadingCoeff * (((R : ℂ) * z) ^ p.natDegree)‖ <
          ‖p.leadingCoeff * (((R : ℂ) * z) ^ p.natDegree)‖ := by
      simpa [hz, norm_sub_rev] using hdom z
    exact (lt_irrefl _ hbad).elim
  let f : C(Circle, ℂˣ) := Polynomial.mapCircleUnits p R hpoly_nonzero
  have hclose :
      ∀ z : Circle,
        ‖(circleMonomial a0 p.natDegree R hRpos z : ℂ) - f z‖ <
          ‖(circleMonomial a0 p.natDegree R hRpos z : ℂ)‖ := by
    intro z
    simpa [f, norm_sub_rev] using hdom z
  refine ⟨f, ?_, ?_⟩
  · intro z
    simp [f]
  · calc
      ContinuousMap.windingNumber f = ContinuousMap.windingNumber (circleMonomial a0 p.natDegree R hRpos) := by
        symm
        exact ContinuousMap.windingNumber_eq_of_norm_sub_lt hclose
      _ = (p.natDegree : ℤ) := circleMonomial_windingNumber a0 p.natDegree R hRpos

/-%%
\begin{proof}\leanok
For large radius, the polynomial map is uniformly close on the circle to its leading monomial in
the walking-dog sense. The monomial has winding number equal to the degree, so the polynomial map
has the same winding number.
\end{proof}
%%-/

/-%%
\begin{theorem}\label{exists_root_of_natDegree_posNew}\lean{RootsComplexPolynomialsNew.Polynomial.exists_root_of_natDegree_pos}\uses{eventually_windingNumber_eq_natDegreeNew, mapClosedUnitDiskUnitsNew, coe_mapClosedUnitDiskUnits_applyNew, circleToClosedUnitDiskNew, coe_toClosedUnitDiskNew, circleWindingNumber_eq_zero_of_exists_extensionNew}\leanok
Every nonconstant complex polynomial has a complex root.
\begin{verbatim}
theorem exists_root_of_natDegree_pos
    (p : Polynomial ℂ) (hdeg : 0 < p.natDegree) :
    ∃ z : ℂ, p.IsRoot z
\end{verbatim}
\end{theorem}
%%-/

theorem exists_root_of_natDegree_pos (p : Polynomial ℂ) (hdeg : 0 < p.natDegree) :
    ∃ z : ℂ, p.IsRoot z := by
  by_contra hroot
  have hnonzero : ∀ z : ℂ, p.eval z ≠ 0 := by
    intro z hz
    exact hroot ⟨z, hz⟩
  obtain ⟨R, hR⟩ := (eventually_windingNumber_eq_natDegree p hdeg).exists
  obtain ⟨f, hf, hwind⟩ := hR
  let F : C(Metric.closedBall (0 : ℂ) 1, ℂˣ) :=
    Polynomial.mapClosedUnitDiskUnits p R fun z => hnonzero ((R : ℂ) * z)
  have hboundary : ∀ z : Circle, F (Circle.toClosedUnitDisk z) = f z := by
    intro z
    apply Units.ext
    have hz : (((Circle.toClosedUnitDisk z : Metric.closedBall (0 : ℂ) 1) : ℂ)) = z :=
      Circle.coe_toClosedUnitDisk z
    calc
      ((F (Circle.toClosedUnitDisk z) : ℂˣ) : ℂ) =
          p.eval ((R : ℂ) * (((Circle.toClosedUnitDisk z : Metric.closedBall (0 : ℂ) 1) : ℂ))) := by
        simp [F]
      _ = p.eval ((R : ℂ) * z) := by rw [hz]
      _ = (f z : ℂ) := (hf z).symm
  have hzero : ContinuousMap.windingNumber f = 0 :=
    ContinuousMap.windingNumber_eq_zero_of_exists_extension hboundary
  have hdeg_ne : (p.natDegree : ℤ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hdeg
  exact hdeg_ne <| by rw [← hwind, hzero]

/-%%
\begin{proof}\leanok
Assume the polynomial has no complex roots. Then it is nonzero on the whole plane, so the map
$z\mapsto p(Rz)$ extends from the unit circle to the closed unit disk through nonzero values.
Hence its winding number must be zero. On the other hand, for sufficiently large $R$, the previous
theorem shows that the same winding number is the positive degree of the polynomial, a
contradiction.
\end{proof}
%%-/

end Polynomial

end RootsComplexPolynomialsNew
