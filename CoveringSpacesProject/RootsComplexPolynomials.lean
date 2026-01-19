import Mathlib

open TopologicalSpace Function

open Complex Set

theorem isConnected_range_of_continuousOn {α : Type*} {β : Type*} [TopologicalSpace α] [TopologicalSpace β] {s : Set α} {f : α → β} (h : ContinuousOn f s) (hs : IsConnected s) :
IsConnected (f '' s) := by
exact IsConnected.image hs f h


theorem Singleton_of_isConnected_SetInt {s : Set ℤ} (hs : IsConnected s) (hs' : s.Nonempty) : ∃ k : ℤ, s = {k} := by
sorry

theorem ContinuousOn.coe {f : ℝ → ℤ} {s : Set ℝ} (h : ContinuousOn (fun x ↦ (f x : ℂ)) s) : ContinuousOn f s := by
sorry


local notation "π" => Real.pi

/-%%
\section{Results from LEAN}
%%-/

/-%%
Here are basic definitions and results already in LEAN:
%%-/

section trivializations

variable {X Y F : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace F]
  (proj : X → Y)

/-%%

\begin{definition}\label{trivialization}\lean{trivialization}\leanok
$f\colon X\to Y$ a local trivialization for $f$ on $U$  is:
\begin{itemize}
\item an open subset $U\subset Y$
\item a discrete space set $I$
\item a homeomorphism $\varphi\colon f^{-1}(U)\to U\times I$
\end{itemize}
such that letting $p_1\colon U\times I\to U$ be the projection onto the first
factor, we have
$p_1\circ \varphi(x)=f(x)$ for all $x\in f^{-1}(U)$
\end{definition}
%%-/

def trivialization := Trivialization F proj

/-%%

\begin{definition}\label{DefIsCoveringOn}\lean{IsCoveringOn}\leanok
Let
$f\colon X\to Y$ be a continuous map and $A\subset Y$. Then $f$ is an even cover on $A\subset X$
if every $a\in A$ has a neighborhood which is contained in the target of a trivialization
\end{definition}
%%-/

def IsCoveringOn := IsCoveringMapOn proj

end trivializations

/-%%
\begin{definition}\label{Defexp}\lean{CSexp}\leanok
$CSexp\colon \C\to \C$ defined by
the usual power series.
\end{definition}
%%-/

noncomputable def CSexp : ℂ → ℂ := Complex.exp

/-%%

\begin{lemma}\label{Contexp}\lean{Contexp}\leanok
$CSexp\colon \C\to \C$ is continuous.
\end{lemma}
%%-/

lemma Contexp : Continuous exp := by
  apply Complex.continuous_exp

/-%%
\begin{proof}\uses{Defexp}\leanok
  In Mathlib.
\end{proof}
%%-/


/-%%
\begin{lemma}\label{Eulersformula}\lean{Eulersformula}\leanok
$$CSexp(r+\theta *I)=exp_\R(r)*CSexp(\theta * I)
=exp_\R(r)*({\rm cos}(\theta+{\rm sin}(\theta)*I),$$
for $r,\theta\in \R$.
\end{lemma}
%%-/

lemma Eulersformula (r θ : ℝ) :
    CSexp (r + θ * I) = CSexp r * Complex.exp (θ * I) := by
  unfold CSexp
  rw [Complex.exp_add, Complex.exp_mul_I]

/-%%
\begin{proof}\uses{Defexp}\leanok
  In Mathlib.
\end{proof}
%%-/

/-%%
\begin{lemma}\label{multiplicativity}\lean{multiplicativity}\leanok
 $CSexp(z+w)=CSexp(z)* CSexp(w)$.
\end{lemma}
%%-/

lemma multiplicativity (z w : ℂ) :
    CSexp (z + w) = CSexp z * CSexp w := by
  unfold CSexp
  rw [Complex.exp_add]

/-%%
\begin{proof}\uses{Defexp}\leanok
  In Mathlib.
\end{proof}
%%-/

/-%%
\begin{lemma}\label{periodicity}\lean{periodicity}\leanok
$CSexp\colon \C\to \C$ is periodic of period $2\pi  i$ and with no smaller period.
\end{lemma}
%%-/

lemma periodicity (x y : ℂ) : CSexp x = CSexp y ↔ ∃ (n : ℤ), x = y + n * (2 * ↑Real.pi * I) := by
  unfold CSexp
  exact Complex.exp_eq_exp_iff_exists_int

/-%%
\begin{proof}\uses{Defexp}\leanok
  In Mathlib.
\end{proof}
%%-/


/-%%
\begin{definition}\label{DefPBlog}\lean{DefPBlog}\leanok
There is a map $PBlog\colon \C\to \C$.
\end{definition}
%%-/

noncomputable def PBlog (z : ℂ) : ℂ := Complex.log z

/-%%
\begin{lemma}\label{ImPBlog}\lean{ImPBlog}\leanok
The image of $PBlog$ is contained in $\{z\in \C |-\pi < Im(z)\le \pi \}$
 and
 for all $\{z\in \C | z\not=0\}$ $CSexp(PBlog(z))=z$.
\end{lemma}
%%-/
lemma ImPBlog (z : ℂ) (hz : z ≠ 0) :
    CSexp (PBlog z) = z ∧ -π < im (PBlog z) ∧ im (PBlog z) ≤ π := by
  unfold PBlog CSexp
  split_ands
  · exact exp_log hz
  · exact neg_pi_lt_log_im z
  · exact log_im_le_pi z

/-%%
\begin{proof}\uses{DefPBlog, Defexp, Eulersformula}\leanok
This is immediate from Definition~\ref{DefPBlog} and Lemma~\ref{Eulersformula}.
\end{proof}
%%-/

/-%%
\begin{definition}\label{splitPlane}\lean{splitPlane}\leanok
$T=\{z\in \C |Re(z)>0 \cup Im(z)\not= 0\}$
\end{definition}
%%-/

def splitPlane : Set ℂ := {z : ℂ | re z > 0 ∨ im z ≠ 0}

/-%%
Missing Mathlib lemma:
if `z.re ≥ 0 ∨ z.im ≠ 0` then `log z.im < π`.
%%-/

/-%%
\begin{lemma}\label{ContPBlog}\lean{ContPBlog}\leanok
$PBlog$ is continuous on $T$ and if $z\in T$ then
$PBlog(z)\in \{z\in \C |-\pi  < Im(z) < \pi \}$.
\end{lemma}
%%-/

lemma ContPBlog :
    ContinuousOn PBlog splitPlane ∧ ∀ (z : ℂ) (hz : z ∈ splitPlane),
    -π < im (PBlog z) ∧ im (PBlog z) < π := by
  unfold splitPlane
  unfold PBlog
  split_ands
  · intro z hz
    simp only [gt_iff_lt, ne_eq, mem_setOf_eq] at hz
    apply ContinuousAt.continuousWithinAt
    exact continuousAt_clog hz
  · intro z hz
    simp only [gt_iff_lt, ne_eq, mem_setOf_eq] at hz
    split_ands
    · exact neg_pi_lt_log_im z
    · rw [Complex.log_im]
      refine arg_lt_pi_iff.mpr ?_
      cases' hz with hRe hIm
      · left
        linarith
      · right
        exact hIm

/-%%
\begin{proof}\uses{Eulersformula, ImPBlog, splitPlane}\leanok
By Lemma~\ref{Eulersformula}  for $x\in T$
$Re(cos(x))\not=-1$ and hence by Lemma~\ref{ImPBlog} $PBlog(x)\in S$.
\end{proof}
%%-/

/-%%
\section{$CSexp\colon \C\to \C$ is a covering projection on $Cstar$}

\begin{definition}\label{Cstar}\lean{Cstar}\leanok
$Cstar=\{z\in \C | z\not= 0\}$
\end{definition}
%%-/

def Cstar : Set ℂ := {z : ℂ | z ≠ 0}

/-%%
\begin{definition}\label{deflift}\lean{deflift}\leanok
Let $f\colon X\to Y$ be a continuous map between topological spaces and $\alpha\colon A\to Y$
a continuous map. A lift of $\alpha$ through $f$ is a continuous map $\tilde\alpha\colon A\to X$
such that
$f\circ \tilde\alpha = \alpha$.
\end{definition}
%%-/

def deflift {A X Y : Type*} [TopologicalSpace A] [TopologicalSpace X] [TopologicalSpace Y]
  (f : X → Y) (α : A → Y)
  (tildeα : A → X) :
  Prop := Continuous tildeα ∧ f ∘ tildeα = α

/-%%
\begin{definition}\label{Defstrip}\lean{Defstrip}\leanok
For any $a, b\in \R$ (in practice, we assume $a < b$), we define
$S(a,b)=\{z\in \C | a < Im{z} < b\}$.
\end{definition}
%%-/

def Defstrip (a b : ℝ) : Set ℂ :=
  {z : ℂ | a < im z ∧ im z < b}

/-%%
\begin{definition}\label{Sstrip}\lean{Sstrip}\uses{Defstrip}\leanok
Define $S\subset \C$ by $S=S(-\pi ,\pi )$.
\end{definition}
%%-/

def Sstrip : Set ℂ := Defstrip (-π) π

/-%%
\begin{lemma}\label{CSexpInS}\lean{CSexpInS}\leanok
For $w\in S$, $CSexp(w)\in T$.
\end{lemma}
%%-/

theorem CSexpInS {w : ℂ} (hw : w ∈ Sstrip) :
    CSexp w ∈ splitPlane := by
  unfold CSexp splitPlane
  unfold Sstrip Defstrip at hw
  simp only [gt_iff_lt, ne_eq, mem_setOf_eq]
  simp only [mem_setOf_eq] at hw
  by_contra h
  push_neg at h
  rw [Complex.exp_im] at h
  have := h.2
  have : Real.sin w.im = 0 := by
    have h2 := Real.exp_pos w.re
    apply (mul_eq_zero_iff_left ?_).mp this
    linarith
  rw [Real.sin_eq_zero_iff] at this
  obtain ⟨k, hk⟩ := this
  rw [← hk] at hw
  have keq : k = 0 := by
    have pi : 0 < π := by exact Real.pi_pos
    have h1 : -1 < (k : ℝ) := by
      have : -π < (k : ℝ) * π := hw.1
      rw [← neg_one_mul π] at this
      rwa [mul_lt_mul_iff_of_pos_right pi] at this
    have h2 : (k : ℝ) < 1 := by
      have : (k : ℝ) * π < π := hw.2
      apply (mul_lt_mul_iff_of_pos_right pi (b := (k : ℝ)) (c := 1)).1
      simp [one_mul, this]
    norm_cast at h1 h2
    omega
  rw [keq] at hk
  simp only [Int.cast_zero, zero_mul] at hk
  have := h.1
  rw [Complex.exp_re] at this
  rw [← hk] at this
  simp only [Real.cos_zero, mul_one] at this
  linarith [Real.exp_pos w.re]

/-%%
\begin{proof}\uses{Sstrip, splitPlane, CSexp}\leanok
A calculation.
\end{proof}
%%-/

/-%%
\begin{proposition}\label{inverseHomeo}\lean{inverseHomeo}\leanok
Then $CSexp\colon S\to T$ and $PBlog\colon T\to S$ are inverse homeomorphisms.
\end{proposition}
%%-/

noncomputable def inverseHomeo :
    Homeomorph Sstrip splitPlane where
      toFun := fun w ↦ by
        let z := CSexp w
        have hz : z ∈ splitPlane := by
          unfold splitPlane
          simp only [gt_iff_lt, ne_eq, mem_setOf_eq]
          apply CSexpInS
          exact w.2
        exact ⟨z, hz⟩
      invFun := fun w ↦ by
        obtain ⟨w₀, hw₀⟩ := w
        set z := PBlog w₀ with zDef
        have hz : z ∈ Sstrip := by
          unfold Sstrip Defstrip
          simp only [mem_setOf_eq]
          rw [zDef]
          exact ContPBlog.2 w₀ hw₀
        exact ⟨z, hz⟩
      left_inv w := by
        simp only
        ext
        simp only
        unfold PBlog CSexp
        have := w.2
        unfold Sstrip Defstrip at this
        apply log_exp
        · exact this.1
        · linarith [this.2]
      right_inv z := by
        simp only
        ext
        simp only
        refine (ImPBlog z ?_).1
        unfold splitPlane at z
        have := z.2
        intro h
        rw [h] at this
        simp at this
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact Continuous.comp Complex.continuous_exp continuous_subtype_val
      continuous_invFun := by
        apply Continuous.subtype_mk
        unfold PBlog
        change Continuous (Complex.log ∘ (fun x : splitPlane => (x : ℂ)))
        apply ContinuousOn.comp_continuous (s := splitPlane)
        · exact ContPBlog.1
        · exact continuous_subtype_val
        · intro x
          simp [splitPlane]

/-%%
\begin{proof}\uses{Sstrip, Eulersformula, Contexp, ContPBlog, periodicity, CSexpInS}\leanok
By Lemma~\ref{Eulersformula} $CSexp(z)\in \R^-$ if and only if $CSexp({\rm Im}(z))\in \R^-$ if and
only if
$\{ {\rm Im}(z)\in \{\pi +(2\pi )\Z\} \}$. Since, by Definition~\ref{Defstrip} for  $z∈ S$,
$-\pi < Im(z) < \pi $.
It follows that $CSexp(S)\subset T$.
Conversely, by Lemma~\ref{ContPBlog} if $z\in T$ then $PBlog(z)\in S$.

By Lemma~\ref{Contexp} $CSexp$ is continuous and,
by Lemma~\ref{ContPBlog}, $PBlog$ is continuous on $T$.
Suppose that $z,w\in S$ and $CSexp(z)=CSexp(w)$.
By Lemma~\ref{periodicity}
there is an integer $n$ such that $z-w =2\pi  * n * I$ and
$-2\pi < Im(z)-Im(w)<2\pi $. It follows that $n=0$ and hence that $z=w$. This shows that   $CSexp|_S$ is one-to-one.
Since $CSexp|_S$ is one-to-one and $CSexp({\rm PBlog}(z))=z$
for all $z\in T$,
it follows that $CSexp\colon S\to T$ and ${PBlog}\colon T\to S$
are inverse functions. Since each is continuous,
they are inverse homeomorphisms.
\end{proof}
%%-/

/-%%

\begin{definition}\label{DeftildeS}\leanok
$\tilde S\subset \C$ is the subset $\{r+\theta* I|r,\theta\in \R \text{\ and\ } \theta\not=
(2k+1)\pi  \text{ for any } k\in \Z\}$.
\end{definition}
%%-/

def DeftildeS : Set ℂ :=
  {z : ℂ | ∀ (k : ℤ), im z ≠ (2 * k + 1) * π}

/-%%
\begin{lemma}\label{tildeShomeo}\lean{tildeShomeo}\uses{DeftildeS, Sstrip}\leanok
Define $\varphi\colon S\times \Z \to \C$  by $\varphi(z,k)=z+2k\pi  *I$. Then
$\varphi\colon S\times \Z\to \tilde S$  is a homeomorphism.
\end{lemma}
%%-/

-- Key lemma: the argument to floor is never an integer
lemma floor_arg_not_int (w : ↑DeftildeS) :
    (w.val.im + π) / (2 * π) ∉ Set.range (Int.cast : ℤ → ℝ) := by
  intro ⟨k, hk⟩
  have hw := w.prop k
  simp only [DeftildeS, Set.mem_setOf_eq] at hw
  field_simp at hk
  have hw' := w.prop (k - 1)
  apply hw'
  have hpi := Real.pi_pos
  have : (w.val).im = ↑k * (2 * π) - π := by linarith
  rw [this]
  push_cast
  linarith

lemma continuous_floor_arg :
    Continuous (fun w : DeftildeS => ⌊((w.val).im + π) / (2 * π)⌋) := by
  rw [← IsLocallyConstant.iff_continuous]
  rw [IsLocallyConstant.iff_isOpen_fiber]
  intro n
  -- Show {w : DeftildeS | ⌊(w.im + π)/(2π)⌋ = n} is open
  have : (fun w : ↑DeftildeS => ⌊((w.val).im + π) / (2 * π)⌋) ⁻¹' {n} =
         Subtype.val ⁻¹' {z : ℂ | (2 * n - 1) * π < z.im ∧ z.im < (2 * n + 1) * π} := by
    ext w
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq]
    constructor
    · intro h
      have hpi : (0 : ℝ) < π := Real.pi_pos
      have h2pi : (0 : ℝ) < 2 * π := by linarith
      have hne := floor_arg_not_int w
      have h1 : (n : ℝ) ≤ ((w.val).im + π) / (2 * π) := by
        rw [← h]
        exact Int.floor_le (((w.val).im + π) / (2 * π))
      have h2 : ((w.val).im + π) / (2 * π) < n + 1 := by
        rw [← h]
        exact Int.lt_floor_add_one (((w.val).im + π) / (2 * π))
      split_ands
      · have h1' : (n : ℝ) < ((w.val).im + π) / (2 * π) := h1.lt_of_ne' (fun heq => hne ⟨n, heq.symm⟩)
        rw [lt_div_iff₀] at h1'
        · linarith
        · linarith
      · rw [div_lt_iff₀] at h2
        · linarith
        · linarith
    · intro ⟨h1, h2⟩
      have hpi : (0 : ℝ) < π := Real.pi_pos
      have h2pi : (0 : ℝ) < 2 * π := by linarith
      rw [Int.floor_eq_iff]
      split_ands
      · rw [le_div_iff₀]
        · linarith
        · linarith
      · rw [div_lt_iff₀] <;> linarith
  rw [this]
  apply IsOpen.preimage continuous_subtype_val
  apply IsOpen.inter
  · exact isOpen_lt continuous_const continuous_im
  · exact isOpen_lt continuous_im continuous_const

noncomputable def tildeShomeo :
    Homeomorph (Sstrip × ℤ) DeftildeS where
      toFun := fun ⟨z, n⟩ ↦ by
        set w := z + (2 * n : ℂ) * π * I with wDef
        have hw : w ∈ DeftildeS := by
          obtain ⟨z₀, hz₀⟩ := z
          unfold DeftildeS
          simp only [ne_eq, mem_setOf_eq]
          intro k h
          rw [wDef] at h
          simp only [add_im, mul_im, mul_re, re_ofNat, intCast_re, im_ofNat, intCast_im, mul_zero,
            sub_zero, ofReal_re, zero_mul, add_zero, ofReal_im, I_im, mul_one, I_re] at h
          unfold Sstrip Defstrip at hz₀
          simp only [mem_setOf_eq] at hz₀
          set m := k - n with hm
          have h' : z₀.im = (2 * m + 1) * π := by rw [hm]; push_cast; linarith
          rw [h'] at hz₀
          -- Let m = k - n
          -- From hz₀.1: -π < (2m + 1)π  →  -1 < 2m + 1  →  m > -1
          -- From hz₀.2: (2m + 1)π < π  →  2m + 1 < 1    →  m < 0
          -- Since m : ℤ, this is impossible (no integer in (-1, 0))
          have h1 : (-1 : ℝ) < 2 * m + 1 := by
            have := hz₀.1
            have hpi := Real.pi_pos
            nlinarith
          have h1 : -1 < 2 * m + 1 := by
            exact_mod_cast h1
          have h2 : (2 : ℝ) * m + 1 < 1 := by
            have := hz₀.2
            nlinarith
          have h2 : 2 * m + 1 < 1 := by exact_mod_cast h2
          -- From h1: m > -1, from h2: m < 0
          have hm_gt : m > -1 := by linarith
          have hm_lt : m < 0 := by linarith
          -- No integer in (-1, 0)
          omega
        exact ⟨w, hw⟩
      invFun := fun w ↦ by
        obtain ⟨w₀, hw₀⟩ := w
        set θ := im w₀ with θDef
        set n := Int.floor ((θ + π) / (2 * π)) with nDef
        set z := w₀ - (2 * (n : ℝ)) * π * I with zDef
        have hz : z ∈ Sstrip := by
          unfold Sstrip Defstrip
          simp only [mem_setOf_eq]
          have hpi : (0 : ℝ) < π := Real.pi_pos
          have h2pi : (0 : ℝ) < 2 * π := by linarith
          -- Get the floor inequalities
          have hn_le : (n : ℝ) ≤ (θ + π) / (2 * π) := Int.floor_le _
          have hn_lt : (θ + π) / (2 * π) < n + 1 := Int.lt_floor_add_one _
          -- Compute z.im
          have hz_im : z.im = θ - 2 * n * π := by
            simp only [zDef, sub_im, mul_im, ofReal_im, ofReal_re, I_im, I_re]
            ring_nf
            simp only [ofReal_intCast, mul_re, intCast_re, ofReal_re, intCast_im, ofReal_im,
              mul_zero, sub_zero, re_ofNat, mul_im, zero_mul, add_zero, im_ofNat]
            rw [θDef]
            linarith
          rw [hz_im]
          constructor
          · -- -π < θ - 2 * n * π
            -- From hn_le: n ≤ (θ + π) / (2π), need to show strict
            have hne : (θ + π) / (2 * π) ≠ n := fun heq => by
              have : θ = (2 * n - 1) * π := by field_simp at heq; linarith
              have : θ = (2 * (n - 1) + 1) * π := by linarith
              exact hw₀ (n - 1) (by rw [← θDef, this]; push_cast; ring)
            have hlt : (n : ℝ) < (θ + π) / (2 * π) := hn_le.lt_of_ne' hne
            rw [lt_div_iff₀ h2pi] at hlt
            linarith
          · -- θ - 2 * n * π < π
            rw [div_lt_iff₀ h2pi] at hn_lt
            linarith
        exact ⟨⟨z, hz⟩,n⟩
      left_inv w := by
        obtain ⟨⟨z, hz⟩, n⟩ := w
        simp only [Subtype.mk.injEq, Prod.mk.injEq]
        -- hz : -π < z.im ∧ z.im < π
        -- Need: z + 2nπi - 2⌊...⌋πi = z  and  ⌊...⌋ = n
        -- The key is showing ⌊(z.im + 2nπ + π)/(2π)⌋ = n

        have hpi : (0 : ℝ) < π := Real.pi_pos
        have h2pi : (0 : ℝ) < 2 * π := by linarith

        -- Compute the imaginary part of w₀ = z + 2nπi
        have hw_im : (↑z + 2 * ↑n * ↑π * I : ℂ).im = z.im + 2 * n * π := by
          simp [mul_im, I_im, I_re, ofReal_re, ofReal_im]

        -- Show that ⌊(z.im + 2nπ + π)/(2π)⌋ = n
        have hfloor : ⌊(z.im + 2 * n * π + π) / (2 * π)⌋ = n := by
          rw [Int.floor_eq_iff]
          obtain ⟨hz_lo, hz_hi⟩ := hz
          constructor
          · -- n ≤ (z.im + 2 * n * π + π) / (2 * π)
            rw [le_div_iff₀ h2pi]
            linarith
          · -- (z.im + 2 * n * π + π) / (2 * π) < n + 1
            rw [div_lt_iff₀ h2pi]
            linarith
        constructor
        · -- z + 2nπi - 2nπi = z
          simp only [hw_im, hfloor]
          norm_cast
          ring
        · -- ⌊...⌋ = n
          simp only [hw_im, hfloor]
      right_inv z := by
        obtain ⟨z, hz⟩ := z
        simp only [Subtype.mk.injEq]
        -- Need to show: (z - 2nπi) + 2nπi = z
        -- This is just algebra
        norm_cast
        ring
      continuous_toFun := by
        -- Approach 1: Use continuity of the underlying function
        refine Continuous.subtype_mk ?_ _
        continuity
      continuous_invFun := by
        -- The key lemma you need:
        -- If (θ + π) / (2π) ∉ ℤ for all θ in your domain, then floor is locally constant

        refine Continuous.prodMk ?_ ?_
        · have := continuous_floor_arg
          continuity
        · exact continuous_floor_arg

/-%%
\begin{proof}\uses{DeftildeS, Sstrip}\leanok
According to Definition~\ref{Defstrip}  image of $S$ under the translation action of $(2\pi )\Z$ on $\C$
is the union
of all strips $S(2n-1)\pi ,(2n+1)\pi )$. By Definition~\ref{DeftildeS} this union is $\tilde S$.
Thus we have a map $S\times \Z\to \tilde S$ defined by
$(z,n)\mapsto z+2\pi  *n *I$. Since translation is a homeomorphism of $\C\to \C$,
this map is a local homeomorphism onto its image $\tilde S$. If $n ,n'\in \Z$ with $n\not=n'$ then
$S((2n-1)\pi ,(2n+1)\pi )\cap S((2n'-1)\pi ,(2n'+1)\pi )=\emptyset$.
Also $\tilde S=\coprod_{n\in \Z}S((2n-1)\pi ,(2n+1)\pi )$. It follows that
$\varphi$ is a bijective map and hence a  homeomorphism.
\end{proof}
%%-/

/-%%

\begin{definition}\label{DefwidetildePBlog}
Let $\widetilde{PBlog}\colon T\times \Z\to S\times \Z$
be defined by $\widetilde{PBlog}(z,n)=(PBlog(z),n)$
for all $z\in T$ and $n\in \Z$.
\end{definition}
%%-/

/-%%

\begin{lemma}\label{widetildePBlogHomeo}
$\widetilde{PBlog}\colon T\times \Z\to S\times \Z$ is a homeomorphism.
\end{lemma}
%%-/

/-%%

\begin{proof}\uses{DefwidetildePBlog, inverseHomeo}
By Definition~\ref{DefwidetildePBlog} $\widetilde PBlog$
is the product of $PBlog\colon T\to S$
and ${\rm Id}_\Z\colon \Z\to\Z$.
By Lemma~\ref{inverseHomeo} the first of these factors
is a homeomorphism. Since ${\rm Id}_\Z$ is a homeomorphism.
it follows from basic properties of homeomorphisms that the
product $\widetilde{PBlog}$ is a homeomorphism.
\end{proof}
%%-/

/-%%

\begin{proposition}\label{trivOverT}
The composition $\psi=\varphi\circ\widetilde{PBlog}\colon T\times \Z\to \tilde S$ defines
a trivialization of $CSexp$
on $T$
\end{proposition}
%%-/

/-%%

\begin{proof}\uses{tildeShomeo, widetildePBlogHomeo, periodicity, trivialization}
$\varphi$ is a homeomorphism by Lemma~\ref{tildeShomeo}.
By Lemma~\ref{widetildePBlogHomeo}
$\widetilde{PBlog}\colon T\times \Z\to S\times \Z$ is
a homemorphism.
Thus, the composition
$\varphi\circ\widetilde{PBlog}\colon T\times \Z\to \tilde S$
is a homeomorphism.
For $(z,n)\in T\times \Z$,
$$CSexp\circ\varphi\circ \widetilde{PBlog}(z,n)=CSexp(\varphi(PBlog(z),n)=CSexp(PBlog(z)+2\pi  * n * I).$$
By Lemma~\ref{periodicity}, $CSexp(PBlog(z)+2\pi  * n * I)=CSexp(PBlog(z))$,
which by Lemma~\ref{widetildePBlogHomeo} equals $z$. This establishes that $\psi$ satisfies all
the conditions of the  Definition~\ref{trivialization} on $T⊆ $.
\end{proof}
%%-/

/-%%


\begin{lemma}\label{homeoInv}
Suppose $f\colon E\to X$ is a map between topological spaces and $U\subset X$ is an open subset
and there is a trivialization for $f$ on $U$. Suppose also that there are homeomorphisms $\varphi\colon X\to X$ and $\tilde \varphi\colon E\to E$
with $f\circ\tilde\varphi =\varphi\circ f$. The there is a trivialization for $f$ on $\varphi(U)$.
\end{lemma}

%%-/

/-%%
\begin{proof}\uses{trivialization}
Since $f\circ \tilde\varphi=\varphi\circ f$,  we have  $\tilde\varphi\colon f^{-1}(U)\to f^{-1}(\varphi(U))$.
Since $\varphi$ and $\tilde\varphi$ are homeomorphisms the induced map
 $\tilde\varphi\colon f^{-1}(U) \to f^{-1}(\varphi(U))$ is a homeomorphism.
Let $\psi\colon f^{-1}(U)\to U\times I$ be a homeomorphism with $p_1\circ \psi$ being the map $f\colon f^{-1}U\to U$. Such a map is equivalent to  a trivialization for $f$ with base $U$. Then
$$ f^{-1}\varphi(U) \buildrel \tilde\varphi^{-1}\over\longrightarrow f^{-1}(U)\buildrel \psi\over\longrightarrow U\times I
\buildrel \varphi \times{\rm Id}_I\over\longrightarrow \varphi(U)\times I$$
is a homeomorphism. Furthrmore, projection to the first factor is
$$f^{-1}(\varphi(U))\buildrel \varphi^{-1}\over \longrightarrow f^{-1}(U) \buildrel f\over\longrightarrow U\buildrel \varphi\over\longrightarrow \varphi(U).$$
This composition is $f\colon f^{-1}(\varphi(U))\to \varphi(U)$, so that this homeomorphism determines a trivialization
for $f$ with base $\varphi(U)$.
\end{proof}
%%-/

/-%%

\begin{definition}\label{TprimeDef}
Let $T'=\{z\in \C | Re(z)<0\cup z\in \C | Im(z)\not= 0\}$.
\end{definition}
%%-/

/-%%

\begin{corollary}\label{trivOverTprime}
$T'$ is the base of a trivialization for $CSexp\colon \C\to \C$
with non-empty fiber.
\end{corollary}
%%-/

/-%%

\begin{proof}\uses{multiplicativity, Eulersformula, homeoInv, trivOverT, splitPlane, TprimeDef}
We have homeomorphism $\mu \colon \C\to \C$ that sends $z \to CSexp(\pi  *I)z)$
and the homeomorphism $\tilde \mu\colon \C\to \C$ defined by $\tilde \mu(z)=z+\pi  *I$
Clearly  by Lemma~\ref{multiplicativity} and Lemma~\ref{Eulersformula}
$CSexp(\tilde\mu(z))= \mu(CSexp(z))$.
By Definition~\ref{splitPlane} and Definition~\ref{TprimeDef}
$\mu(T)=T'$. The result now follows from Lemma~\ref{homeoInv} and Proposition~\ref{trivOverT}.
\end{proof}
%%-/

/-%%

\begin{lemma}\label{xinTorTprime}
For $x\in \C$ with $x\not= 0$, either $x\in T$ or $x\in T'$.
\end{lemma}
%%-/

/-%%

\begin{proof}\uses{splitPlane, TprimeDef}
Suppose that $x\in \C$ and $x\not= 0$. Then either $Re(x)> 0$ or $Re(x)\le 0$. If $Re(x)>0$, then by Definition~\ref{splitPlane} $x\in T$. if $Re(x)< 0$ then by Definition~\ref{TprimeDef} $x\in T'$. Finally, if $Re(z)=0$
and $z\not=0$, then $Im(z)\not= 0$ and $z\in T$.
\end{proof}
%%-/

/-%%

\begin{corollary}\label{TcupTprimeCstar}
$T\cup T'=\{z\in \C | z∈ Cstar\}$.
\end{corollary}
%%-/

/-%%

\begin{proof}\uses{xinTorTprime, Cstar}
Immediate from Lemma~\ref{xinTorTprime} and Definition~\ref{Cstar}.
\end{proof}
%%-/

/-%%

\begin{corollary}\label{expCP}
$CSexp\colon \C\to \C $ is a covering projection over $Cstar$ with source $\C$.
The image of $CSexp$ is  $Cstar$.
\end{corollary}
%%-/

/-%%

\begin{proof}\uses{Cstar, trivOverT, trivOverTprime, ImPBlog, TcupTprimeCstar, DefIsCoveringOn}
By Corollary~\ref{TcupTprimeCstar}
$T\cup T'= Cstar$. By Proposition~\ref{trivOverT} and Corollary~\ref{trivOverTprime}
$CSexp$ is a trivialization on $T$ and on $T'$. Hence, every point  of $Cstar$ lies
in the base of a trivialization for $CSexp$. By definition, this shows that
$CSexp\colon \C\to \C $ is a covering on $Cstar$.
Since $CSexp(z)\not=0$ for all $z\in \C$, it follows that $CSexp^{-1}(Cstar)=\C$.
Lastly, by Lemma~\ref{ImPBlog} if $z\in\C$ and $z\not= 0$ then $CSexp(PBlog)(z)=z$.
This proves that $CSexp$ is onto $\{z\in \C | z\not=0\}$, which by Lemma~\ref{Cstar},
is equal to $Cstar$.\end{proof}
%%-/

/-%%

\begin{corollary}\label{expUPL}
Given a path $\omega\colon [ a , b]\to \C $ with $\omega(t)\not=0$ for all $t\in [ a, b]$, and
$\tilde a_0\in CSexp^{-1}(\omega(a))$, there is a unique map
$\tilde\omega\colon [ a, b ]\to \C$ with $\tilde\omega(a)=\tilde a_0$ and $exp(\tilde\omega)=\omega$.
\end{corollary}
%%-/

/-%%

\begin{proof}\uses{expCP}
By Corollary~\ref{expCP} and the basic result about covering projections.
\end{proof}
%%-/

/-%%

\begin{corollary}\label{expHLP}
$CSexp$ satisfies the homotopy lifting property on $Cstar$.
\end{corollary}
%%-/

/-%%
\begin{proof}\uses{expCP}
This is immediate from Corollary~\ref{expCP} and the theorem that covering projections
have the homotopy lifting property.
\end{proof}
%%-/


/-%%

\section{Homotopy Classes of Loops and maps of $S^1$ into $Cstar$}

\begin{definition}\label{loop}\lean{loop}\leanok
Let $X$ be a topological space and $a, b ∈ ℝ$ with $b > a$.  A loop in $X$ is a map
$\omega\colon [ a, b]\to X$ with $\omega(b)=\omega(a)$.  A loop is {\em based at $x_0\in X$} if
$\omega(a)=x_0$.
\end{definition}
%%-/

def loop {X : Type*} [TopologicalSpace X] (a b : ℝ) (ω : ℝ → X) : Prop :=
  ω b = ω a

/-%%

\begin{definition}\label{homotopyloop}
A homotopy of loops is a one parameter family $\Omega\colon [a, b]\times [0, 1]\to X$ with
$\Omega|_{[a, b]\times\{s\}}$
a loop for all $s\in [0, 1]$. A homotopy of loops based at $x_0$ is a one parameter family
indexed by $[0, 1]$ of loops based at $x_0$.
\end{definition}
%%-/

/-%%

\begin{lemma}\label{existlift}
Let $\omega\colon [a, b]\to \C$ be a loop. Assume that $\omega(t)\in Cstar$ for all $t\in [a, b]$.
There is a lift of $\omega$ through $exp$.
\end{lemma}
%%-/

/-%%

\begin{proof}\uses{expCP, expUPL}
By Corollary~\ref{expCP}  $CSexp^{-1}(\omega(a))\not=\emptyset$.
Fix a point $x\in CSexp^{-1}(\omega(a))$ and
 let $\tilde\omega_x\colon [a, b]\to \C$ be  lift of $\omega$ through the $CSexp$ with initial
 point $x$
as guaranteed by Corollary~\ref{expUPL}.
\end{proof}
%%-/

/-%%

\begin{definition}\label{DefWNlift}\lean{DefWNlift}\leanok
Suppose given a loop $\omega\colon a\colon [a, b]\to \C$
with $\omega(t)\in Cstar$ for all $t\in [a, b]$,
and given a lift $\tilde\omega$ of $\omega$ through $CSexp$
the {\em winding number} of the lift $\tilde\omega$,
denoted $w(\tilde\omega)$,
is $(\tilde\omega_x(b)-\tilde\omega_x(a))/2\pi  *I$.
\end{definition}
%%-/

noncomputable def DefWNlift (a b : ℝ)
-- (ω : ℝ → ℂ)
-- (hω : loop a b ω)
--  (hCstar : ∀ t ∈ Icc a b, ω t ∈ Cstar)
  (tildeω : ℝ → ℂ)
--  (hlift : deflift CSexp ω tildeω)
  :
  ℂ :=
  (tildeω b - tildeω a) / (2 * Real.pi * I)


/-%%

\begin{lemma}\label{diffinitpoint}\lean{diffinitpoint}\leanok
Let $\omega\colon [a, b]\to \C$ be continuous with $\omega(t)\in Cstar$ for all $t\in [a ,b]$.
Suppose that $\tilde\omega$ and $\tilde\omega'$ are lifts of $\omega$
through $CSexp$.
Then DefWNlift$(\tilde\omega)\in \Z$ and DefWNlift$(\tilde\omega')=$DefWNlift$(\tilde\omega)$.
\end{lemma}
%%-/

lemma diffinitpoint {a b : ℝ} (hab : a ≤ b) (ω : ℝ → ℂ)
    --(ωCont : ContinuousOn ω (Icc a b))
    (hω : loop a b ω)
    --(hCstar : ∀ t ∈ Icc a b, ω t ∈ Cstar)
    (tildeω tildeω' : ℝ → ℂ)
    (hlift : deflift CSexp ω tildeω)
    (hlift' : deflift CSexp ω tildeω') :
    ∃ (k : ℤ), DefWNlift a b tildeω = k ∧ DefWNlift a b tildeω' = k := by
  unfold deflift at hlift hlift'
  unfold loop at hω
  unfold DefWNlift
  have h : ∀ t, CSexp (tildeω t) = CSexp (tildeω' t) := by
    intro t
    change (CSexp ∘ tildeω) t = (CSexp ∘ tildeω') t
    rw [hlift.2, hlift'.2]
  have h' : ∀ t, ∃ n : ℤ, tildeω' t - tildeω t = 2 * π * n * I := by
    intro t
    specialize h t
    choose n hn using (periodicity (tildeω' t) (tildeω t)).1 h.symm
    use n
    rw [hn]
    ring
  choose n hn using h'
  have nCont : ContinuousOn n (Icc a b) := by
    have h1 : ContinuousOn tildeω (Icc a b) := hlift.1.continuousOn
    have h2 : ContinuousOn tildeω' (Icc a b) := hlift'.1.continuousOn
    have hdiff : ContinuousOn (fun t => tildeω' t - tildeω t) (Icc a b) :=
      ContinuousOn.sub h2 h1
    have htot : ContinuousOn (fun t => (tildeω' t - tildeω t) / (2 * π * I)) (Icc a b) := by
      apply ContinuousOn.div_const hdiff
    have setEqOn : Set.EqOn (fun t => (tildeω' t - tildeω t) / (2 * π * I)) (fun t => n t) (Icc a b) := by
      intro t ht
      simp only
      rw [hn t]
      have : (2 : ℂ) * π * I ≠ 0 := by
        norm_cast
        have : (π : ℝ) ≠ 0 := by exact Real.pi_ne_zero
        norm_num
        exact this
      field_simp
      ring_nf
    have := (continuousOn_congr setEqOn).1 htot
    exact ContinuousOn.coe this
  have nConst : ∃ k : ℤ, ∀ t ∈ Icc a b, n t = k := by
    have : IsConnected (Icc a b) := by
      exact isConnected_Icc hab
    have := isConnected_range_of_continuousOn nCont this
    have nne : (n '' Icc a b).Nonempty := by
      exact IsConnected.nonempty this
    have := Singleton_of_isConnected_SetInt this nne
    choose k hk using this
    use k
    intro t ht
    have : n t ∈ n '' Icc a b := Set.mem_image_of_mem n ht
    rw [hk] at this
    simpa [mem_singleton_iff] using this

  obtain ⟨k, hk⟩ := nConst

  let tildea := tildeω a
  let tildeb := tildeω b
  let tildea' := tildeω' a
  let tildeb' := tildeω' b

  have f1 : tildea' - tildea = tildeb' - tildeb := by
    unfold tildea tildeb tildea' tildeb'
    rw [hn a, hn b]
    rw [hk a (⟨by linarith, by linarith⟩), hk b (⟨by linarith, by linarith⟩)]
  have f2 : tildeb' - tildea' = tildeb - tildea := by
    calc tildeb' - tildea'
    = (tildeb' - tildeb) + (tildeb - tildea') := by ring
    _ = (tildeb' - tildeb) + (tildeb - tildea) - (tildea' - tildea) := by ring
    _ = (tildeb' - tildeb) - (tildea' - tildea) + (tildeb - tildea) := by ring
    _ = (tildeb - tildea) := by rw [f1]; ring

  have h1 : CSexp (tildeω b) = CSexp (tildeω a) := by
    have := hlift.2
    change (CSexp ∘ tildeω) b = (CSexp ∘ tildeω) a
    rwa [this]
  have h1' : CSexp (tildeω' b) = CSexp (tildeω' a) := by
    have := hlift'.2
    change (CSexp ∘ tildeω') b = (CSexp ∘ tildeω') a
    rwa [this]

  choose ℓ hℓ using (periodicity (tildeω b) (tildeω a)).mp h1
  use ℓ
  split_ands
  · rw [hℓ]
    ring_nf
    have : I ≠ 0 := by norm_num
    have : (π : ℂ) ≠ 0 := by
      norm_cast
      exact Real.pi_ne_zero
    field_simp
    rw [show ℓ * π * I * I = - (ℓ * π) by ring_nf; norm_cast; simp]
    norm_cast
    ring_nf
  · rw [f2]
    unfold tildeb tildea
    rw [hℓ]
    ring_nf
    have : I ≠ 0 := by norm_num
    have : (π : ℂ) ≠ 0 := by
      norm_cast
      exact Real.pi_ne_zero
    field_simp
    rw [show ℓ * π * I * I = - (ℓ * π) by ring_nf; norm_cast; simp]
    norm_cast
    ring_nf

/-%%
\begin{proof}\uses{deflift, loop, periodicity, DefWNlift}\leanok
By the Definition~\ref{deflift} we have
 $CSexp(\tilde\omega(b))=\omega(b)$ and $CSexp(\tilde\omega(a)=\omega(a)$.
 By Definition~\ref{loop} $\omega(b)=\omega(a)$.
 Thus, $CSexp(\tilde\omega(b))=CSexp(\tilde\omega(a))$.
 By Lemma~\ref{periodicity}, there is $k\in \Z$,
 such that $\tilde\omega(b)-\tilde\omega(b)=2\pi *k* I$.
 By Definition~\ref{DefWNlift}, the winding number of $\tilde\omega$ is $k$


Let $\tilde\omega'$ be another lift of $\omega$. Since
$CSexp(\tilde\omega'(t))=CSexp(\tilde\omega(t))$
 for every $t\in [ a, b]$,
there is an integer $k(t)\in \Z$ with
$\tilde\omega'(t)-\tilde\omega_x(t)=2\pi  k(t)*I$.
Since $\tilde\omega'$ and $\tilde\omega$ are continuous functions of $t$
so is $k(t)$.
Since the $[ a, b]$ is connected and $\Z$ is discrete, $k(t)$
is a constant function; i.e.,
there is an integer $k_0$ such that for all $t\in [ a, b]$, we have
$\tilde\omega'(t)=\tilde\omega(t)+2\pi * k_0*I$.
Thus, $\tilde ω'(b) -\tilde ω'(b)=\tilde ω'(a)-\tilde ω(a)$.
It follows from Definition~\ref{DefWNlift} $w(\tilde ω')=w(\tilde ω).$
\end{proof}
%%-/

/-%%

 \begin{corollary}\label{constWNomega}
 Let $\omega\colon [ a, b]\to \C$ be a loop with $\omega(t)\in Cstar$ for all $t\in [ a, b]$.
 There is a lift $\tilde\omega\colon [ a, b]\to \C$ of $\omega$ through $CSexp$.
 There is a constant $w(\omega)\in \Z$ such that for every lift $\tilde\omega \colon [ a, b]\to \C$
 the winding number of  $\tilde\omega$ is $w(\omega)$.
 \end{corollary}
%%-/

/-%%

 \begin{proof}\uses{diffinitpoint, existlift}
 This is immediate from Lemmas~\ref{diffinitpoint} and Lemma~\ref{existlift}.
 \end{proof}
%%-/

/-%%

 \begin{definition}\label{WNloop}\uses{constWNomega}
 Suppose that $\omega\colon [ a, b ]\to \C$ is a loop with $\omega(t)\in Cstar$ for all
 $t\in [ a, b ]$.
 Then the constant $w(\omega)$ given in Corollary~\ref{constWNomega} is the {\em winding number
 of $\omega$}.
 \end{definition}
%%-/

/-%%


\begin{lemma}\label{equalwinding}
If $\omega\colon [ a, b ]\to \C$ and $\omega'\colon [ a, b ]\to \C$
are loops with $\omega(t) , \omega'(t) \in Cstar$ for all $t\in [ a, b ]$
and if $H\colon [ a, b ]\times[ 0, 1 ]\to \C$ is a homotopy of loops from $\omega$ to $\omega'$
with $H(t,s)\in Cstar$ for all $t\in [ a, b ]$ and $s\in[ 0, 1 ]$, then $w(\omega)=w(\omega')$
\end{lemma}
%%-/

/-%%

\begin{proof}\uses{homotopyloop, diffinitpoint, constWNomega, expHLP}
By Definition~\ref{homotopyloop} for all $\{t∈ ℝ : 0≤t≤1\}$ $H(a,t)=H(b,t)$.
Let $\mu\colon \{t∈ ℝ : 0≤t≤1\} \to \C$ be the path $μ(t)=H(a,t)$.
By Corollary~\ref{expHLP} since the image of $H$ is contained in $Cstar$,
there  is a lift $\tilde H\colon [ a, b]\times I$ of $H$ through $CSexp$.
Then $\tilde H|_{\{a\}\times I}$
and $\tilde H|_{\{b\}\times I}$ are two liftings of $\mu$. So by Lemma~\ref{diffinitpoint}
$\tilde H(b,1)-\tilde H(b,0)=\tilde H(a,1)-\tilde H(a,0)$.
Rewriting we have
$⁀ H(b,1)-⁀ H(a,1)= \tilde H(b,0)-\tilde H(a,0)$.
Since $\tilde H(t,0)$ is a lift of $\omega$ through $CSexp$ and  $\tilde H(t,1)$ is a lift of
$\omega'$
through $CSexp$,  by Definition~\ref{WNloop}
$w(\omega')=w(ω)$.
\end{proof}
%%-/

/-%%

\begin{corollary}\label{constpath}
Suppose that $\omega\colon [ a, b ]\to \C$ is a loop and $\omega(t)\in Cstar$
for all $t\in [ a, b ]$.
Suppose that $H\colon [ a, b ]\times [ 0, 1 ]\to \C$ is a  homotopy of loops
from $\omega$  to a constant loop
and $H(t,s)\in Cstar$ for all $(t,s)\in [ a, b ]\times [ 0, 1 ]$. Then
the winding number of $\omega$ is zero
\end{corollary}
%%-/

/-%%

\begin{proof}\uses{equalwinding, expUPL, WNloop}
By Lemma~\ref{equalwinding} the winding number of the loop $\omega$
is equal to the winding number of a constant loop. By Lemma~\ref{expUPL}
the lift of a constant loop through $CSexp$ is a constant path. Thus, the endpoints of the lift of
the constant loop
are equal and hence by Definition~\ref{WNloop} the winding number of a constant loop is zero.
\end{proof}
%%-/

/-%%

\begin{definition}\label{DefS1loop}
Given a map of the circle $\psi\colon S^1\to X$ the associated loop is
$\omega\colon [ 0, 2\pi  ]\to X$ is defined by $\omega(t)=\psi(CSexp(it))$.
\end{definition}
%%-/

/-%%

\begin{lemma}\label{sameImage}
 Let $ρ : S^1→ \C$ be a map with $ρ(z)∈ Cstar$ for all $z∈ S^1$.
 Let $ω$ be the loop associated with $ρ$.
 Then the image of $ω$ is contained in $Cstar$.
\end{lemma}

%%-/

/-%%

\begin{proof}\uses{DefS1loop}
Let $ω \colon [ 0, 2\pi  ] \to \C$ be the loop associated to $ρ$.
Then by Definition~\ref{DefS1loop} for all $t∈ [ 0 ,1 ]$ $ω(t)=ρ(2\pi * t *I)∈ Cstar$.
\end{proof}

%%-/


/-%%

\begin{definition}\label{DefWNS1}\uses{DefS1loop, sameImage}
The winding number of a map $\rho\colon S^1\to \C$ with $\rho(z)\in Cstar$
for all $z\in S^1$  is the winding number of the associated loop.
\end{definition}
%%-/

/-%%

\begin{lemma}\label{constS1}
If $f\colon S^1\to \C$ is a constant map to a point $z\in Cstar$, then $w(f)=0$.
\end{lemma}

\begin{proof}\uses{DefS1loop, DefWNS1, constpath}
By Definition~\ref{DefS1loop} the loop associated with the constant map $f\colon S^1\to Cstar$
is a constant loop at a point of $Cstar$.
By Lemma~\ref{DefWNS1} the winding number of $f$ is equal to the winding number
of the constant loop at $f(S^1)\in Cstar$. By Lemma~\ref{constpath} this winding number is zero.
\end{proof}

%%-/


/-%%

\begin{lemma}\label{S1homotopy}
Let $\psi, \psi'\colon S^1\to \C$ be maps and $H : S^1→ \C$ a homotopy between them
whose image lies in  $Cstar$. Then the winding numbers of $\psi$ and $\psi'$ are equal.
\end{lemma}
%%-/

/-%%

\begin{proof}\uses{DefS1loop, equalwinding, DefWNS1 }
Let $H\colon S^1\times I\to \C$ be a homotopy from $\psi$ to $\psi'$ whose image lies in $Cstar$.
Let $ω$ and $ω'$ be the loops associated to $ψ$ and $ψ'$ respectively
Define $\hat H\colon [ 0, 2\pi  ]\times [ 0, 1 ]\to X$ by
$\hat H(t,s)=H(CSexp(it),s)$. Then by Definition~\ref{DefS1loop} $\hat H$ is a homotopy from
 the loop $\omega$ to the loop $\omega'$. The images of $H$ and $\hat H$ are the same
 so that the image of $\hat H$ lies in $Cstar$. By Lemma~\ref{equalwinding}
 the winding numbers of $\omega$ and $\omega'$ are equal. By Definition~\ref{DefWNS1} this means
 that the winding numbers of $\psi$
 that the winding numbers of $ψ$ and $ψ'$ are equal.
\end{proof}
%%-/





/-%%

\begin{theorem}\label{boundsWN0}
Let $\rho\colon S^1\to \C$ be a map with $\rho(z)\in Cstar$ for all $z\in S^1$.
Suppose there is a map $\hat f\colon D^2\to \C$ with $\hat f|_{S^1}=f$ and with
the image of $\hat f$ contained in $Cstar$. Then the winding $w(\rho)=0$.
\end{theorem}
%%-/

/-%%


\begin{proof}\uses{S1homotopy, constS1}
Define a continuous map $J\colon S^1\times [ 0,1 ]\to D^2$ by
$(z,t)\mapsto (1-t)z$. Then $\hat f\circ J(z,0)= \rho(z)$ and
$\hat f\circ J(z,1)=\hat f(0)$ for all $z\in S^1$.
This is a homotopy in $Cstar$ from $\rho$ to a constant map of $S^1\to Cstar$.
By Lemma~\ref{S1homotopy} the winding number of $\rho$ is equal to the winding number
of a constant map $S^1\to C\star$.
By Lemma~\ref{constS1}, the winding number of a constant
map $S^1\to \hat f(0)\in Cstar$ is zero.




Since there is a homotopy $H$ from $\rho$
to a constant map with image in $Cstar$, it follows from Lemma~\ref{S1homotopy}
that the winding number of $\rho$ is zero.
\end{proof}

%%-/

/-%%


\section{Winding numbers at Infinity for complex polynomials}

%%-/

/-%%
\begin{lemma}\label{zkWNk}
For any $\alpha_0\in \C$  and any $k\in \Z$ $k≥ 0$, define $\psi_{\alpha_0,k}\colon \C\to \C$ by
$\psi_{\alpha_0,k}(z)=\alpha_0 z^k$.
 Then for any $R>0$ if $\alpha_0\not=0$ and $k>0$  the winding number of the map of
 the restriction of $\psi_{\alpha_0,k}$ to the circle of radius $R$
is $k$
\end{lemma}
%%-/

/-%%

\begin{proof}\uses{DefS1loop, multiplicativity, expCP, WNloop}
By Definition`\ref{DefS1loop} and by Lemma~\ref{multiplicativity} the loop
 $\omega\colon [ 0, 2\pi  ]\to \C$ associated to $\psi_{\alpha_0,t}$ restricted to the circle of
 radius $R$ is given by
$\omega(t)= \alpha_0 R^kCSexp(kt *I)$.

By Lemma~\ref{expCP} there is an $\tilde\alpha_0\in \C$ with $CSexp(\tilde\alpha_0)=\alpha_0 R^k$.
Define $\tilde\omega(t)=\tilde\alpha_0+kt *I$ for $0\le t\le 2\pi $.
Then by Lemma~\ref{multiplicativity}
$$CSexp(\tilde\alpha_0 +kt*I)=\alpha_0 R^kCSexp (kt*I).$$
By Definition~\ref{deflift} this means that $\tilde\omega$ is a lift of $\omega$ through $CSexp$.
By Definition~\ref{WNloop}  $w(\omega)=(2\pi  k*I-0)/2\pi  * I = k$.
By Definition~\ref{DefWNS1}, this means that the winding number of $\psi_{\alpha_0,k}$ is $k$.
\end{proof}

%%-/

/-%%
\begin{lemma}\label{walkingdog}
Suppose that $\psi\colon S^1\to \C$ and $\psi'\colon S^1\to \C$ are maps
and for each $z\in S^1$, we have $|\psi(z)-\psi'(z)|<|\psi(z)|$. Then there is a homotopy
$H$ from $\psi$ to $\psi'$ whose image lies in $Cstar$.
\end{lemma}
%%-/

/-%%

\begin{proof}
Since for all $z\in S^1$, $|\psi(z)-|\psi'(z)|<|\psi(z)|$, it follows that $|\psi(z)|>0$ and
$|\psi'(z)|>0$ for all $z\in S^1$.
Define a homotopy $H\colon S^1× [ 0, 2\pi ]\to \C$ by
$H(z,t)=t\psi'(z)+(1-t)\psi(z)$.
$H(z,0)=\psi(z)$ and $H(z,1)=\psi'(z)$, so $H$ is a homotopy from $\psi$ to $\psi'$.

We establish that $H(z,t)\not= 0$. For all $z\in S^1$ and $t\in [ 0, 1 ]$
 $|\psi(z)-(t\psi(z)-(1-t)\psi'(z)|=|(1-t)(\psi-\psi')|$. Since $0\le t\le 1$, $0\le (1-t)\le 1$.
Then, $|\psi(z)-H(z,t)|=|\psi(z)-(t\psi(z)-(1-t)\psi'(z)|=(1-t)|\psi(z)-\psi'(z)|<|\psi(z)|$.
So $H(z,t)\not=0$ for all $z\in S^1$ and all $t\in[ 0, 1 ]$.

Consequently, $H$ is a homotopy $S^1\times [ 0 , 1 ]\to \C$ from $\psi$ to $\psi'$ whose image lies
in $Cstar$.
\end{proof}
%%-/

/-%%

\begin{corollary}\label{sameWN}
Suppose that $\psi,\psi'\colon S^1\to \C$ with $|\psi(z)-\psi'(z)|<|\psi(z)|$
for all $s\in [ 0, 2\pi  ]$. Then $\psi$ and $\psi'$ have the same winding number.
\end{corollary}

\begin{proof}\uses{walkingdog, S1homotopy}
By Lemma~\ref{walkingdog}, there is a homotopy $H$ from $\psi$ to $\psi'$ whose image lies in
$Cstar$.
Thus, by Lemma~\ref{S1homotopy}, $\psi$ and $\psi'$ have the same winding number.
\end{proof}
%%-/



/-%%




\begin{lemma}\label{zkdominates}
Let $p(z)$ be a complex polynomial of degree $k$;  $p(z)=\sum_{i=0}^k\alpha_iz^{k-i}$ with
$\alpha_i\in \C$ and $\alpha_0\not= 0$.
For all $R$ sufficiently large $|\alpha_0|R^k>|\alpha_0z^k - p(z)|$ for any $z$ with $|z|=R$.
\end{lemma}
%%-/

/-%%

\begin{proof}
For each $1\le i\le k$ set $\beta_i=\alpha_i/\alpha_0$
Choose $R>\sum_{i=1}^k|\beta_j|$ and $R>1$.
For any $z\in \C$ with $|z|=R$, we have
$$
|\alpha_0z^k-p(z)|=|\sum_{i=1}^k\alpha_iz^{k-i}|  \le
\sum_{i=1}^k|\alpha_i|R^{k-i}=|\alpha_0|\sum_{i=1}^k|\beta_i|R^{k-1}
<|\alpha_0|R^k=|\alpha_0R^k|.$$
\end{proof}
%%-/

/-%%

\begin{theorem}\label{WNthm}
Let $p(z)$ be a complex polynomial of degree $k>1$ given by $p(z)=\sum_{i=0}^k\alpha_iz^{k-i}$ with
$α_i∈ℂ$ for all $i$ and $α_0\not= 0$. Then for $R$ sufficiently large,
 the map $f : S^1\to \C$ given by
$f(z)= p(R* z)$ for $z\in S^1$ has winding number $k$.
\end{theorem}


\begin{proof}\uses{zkWNk, zkdominates,sameWN}
By Lemma~\ref{zkdominates} for $R>{\rm max}(1,\sum_{i=1}^k|\beta_j|)$,
and for any $z\in \C$ with $|z|=1$
$|\alpha_0(R*z)^k-f(z)| <|\alpha_0 R^k|$. By Lemma~\ref{sameWN} the maps defined on $S^1$ by
$z ↦\alpha_0*(R* z)^k$ and by $f$ have the same winding number.

But according the Lemma~\ref{zkWNk}
the   winding number of the map $S^1\mapsto \C$ given by $z\mapsto \alpha_0(R*z)^k=(α_0R^k)*z^k$ is $k$.
Thus, the winding number of $f$ is also $k$.
\end{proof}

%%-/

/-%%


\begin{theorem}\label{ExistRoot}
Every complex polynomial of degree $k>0$ has a complex root.
\end{theorem}
%%-/

/-%%

\begin{proof}\uses{WNthm, boundsWN0}
The proof is by contradiction. Suppose that $p(z)=\sum_{i=0}^k\alpha_iz^{k-i} $ with
$\alpha_0\not= 0$. Suppose that
$p(z)\not= 0$ for all $z\in \C$.
By Theorem ~\ref{WNthm} for $R>0$ sufficiently large  the winding number of the restriction
of $p(z)$ to the circle of radius $R$ is $k$. Fix such an $R$


 Let $D^2\to \C$ be the map $z\mapsto Rz$.
Define $\rho\colon D^2\to \C$ by $z\mapsto p(Rz)$. The restriction of this map to the boundary
circle
is the restriction of $p(z)$ to the circle of radius $R$.
Since $p(z)\not=0 $ for all $z\in \C$, the image of $\rho$ is contained in $Cstar$.
According to Lemma~\ref{boundsWN0}, this implies that the winding number of
of $p$ on the circle of radius $R$ is zero.

Since $k>0$, this is a contradiction.
\end{proof}


%%-/
