import Mathlib

--- TODO : make a glossary of everything we're defining here, to be able to quickly access everything...

open TopologicalSpace Function

open Complex Set

/-%%
\begin{lemma}\label{isConnected_range_of_continuousOn}\lean{isConnected_range_of_continuousOn}\leanok
The image of a connected set under a continuous map is connected.
\end{lemma}
%%-/

theorem isConnected_range_of_continuousOn {α : Type*} {β : Type*} [TopologicalSpace α] [TopologicalSpace β] {s : Set α} {f : α → β} (h : ContinuousOn f s) (hs : IsConnected s) :
IsConnected (f '' s) := by
exact IsConnected.image hs f h

/-%%
\begin{proof}\leanok
This is the standard fact that the image of a connected space under a continuous map is connected.
Apply this to the restriction of $f$ to the connected set $s$.
\end{proof}
%%-/

/-%%
\begin{lemma}\label{Singleton_of_isConnected_SetInt}\lean{Singleton_of_isConnected_SetInt}\leanok
Any nonempty connected subset of $\mathbb Z$ is a singleton.
\end{lemma}
%%-/

theorem Singleton_of_isConnected_SetInt {s : Set ℤ} (hs : IsConnected s) (hs' : s.Nonempty) : ∃ k : ℤ, s = {k} := by
  rcases hs' with ⟨k, hk⟩
  have hsSub : s.Subsingleton := by
    intro x hx y hy
    haveI : PreconnectedSpace s := Subtype.preconnectedSpace hs.isPreconnected
    haveI : Subsingleton s := PreconnectedSpace.trivial_of_discrete
    exact congrArg Subtype.val (Subsingleton.elim (⟨x, hx⟩ : s) ⟨y, hy⟩)
  exact ⟨k, hsSub.eq_singleton_of_mem hk⟩

/-%%
\begin{proof}\leanok
The subspace topology on $s\subset \mathbb Z$ is discrete, because $\mathbb Z$ itself is discrete.
A connected discrete space cannot contain two distinct points: otherwise one of those points would
be a nontrivial clopen subset, contradicting connectedness. Hence $s$ has at most one point.
Since $s$ is assumed nonempty, it must be of the form $\{k\}$ for some $k\in \mathbb Z$.
\end{proof}
%%-/

/-%%
\begin{lemma}\label{ContinuousOn.coe}\lean{ContinuousOn.coe}\leanok
If a map into $\mathbb Z$ is continuous after coercion to $\C$, then it is continuous.
\end{lemma}
%%-/

theorem ContinuousOn.coe {f : ℝ → ℤ} {s : Set ℝ} (h : ContinuousOn (fun x ↦ (f x : ℂ)) s) : ContinuousOn f s := by
  have hReal : ContinuousOn (fun x ↦ (f x : ℝ)) s := by
    simpa using (Complex.continuous_re.continuousOn.comp (s := s) (t := Set.univ) h (by
      intro x hx
      simp))
  have hCast : ContinuousOn (((↑) : ℤ → ℝ) ∘ f) s := by
    simpa [Function.comp] using hReal
  exact (Int.isClosedEmbedding_coe_real.isEmbedding.continuousOn_iff).2 hCast

/-%%
\begin{proof}\leanok
Compose the map $x\mapsto f(x)\in \mathbb C$ with the real-part map $\Re\colon \mathbb C\to \mathbb R$.
This shows that the same function, viewed as an $\mathbb R$-valued map, is continuous on $s$.
Now the inclusion $\mathbb Z\hookrightarrow \mathbb R$ is an embedding, so continuity after
composing with this inclusion is equivalent to continuity of the original $\mathbb Z$-valued map.
\end{proof}
%%-/

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

\begin{definition}\label{IsCoveringOn}\lean{IsCoveringOn}\leanok
Let
$f\colon X\to Y$ be a continuous map and $A\subset Y$. Then $f$ is an even cover on $A\subset X$
if every $a\in A$ has a neighborhood which is contained in the target of a trivialization
\end{definition}
%%-/

def IsCoveringOn := IsCoveringMapOn proj

end trivializations

/-%%
\begin{definition}\label{CSexp}\lean{CSexp}\leanok
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
\begin{proof}\uses{CSexp}\leanok
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
\begin{proof}\uses{CSexp}\leanok
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
\begin{proof}\uses{CSexp}\leanok
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
\begin{proof}\uses{CSexp}\leanok
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
\begin{proof}\uses{DefPBlog, CSexp, Eulersformula}\leanok
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
    ContinuousOn PBlog splitPlane ∧ ∀ (z : ℂ) (_ : z ∈ splitPlane),
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
\begin{lemma}\label{floor_arg_not_int}\lean{floor_arg_not_int}\leanok
For each $w\in \tilde S$, the number $\frac{\Im(w)+\pi}{2\pi}$ is not an integer.
\end{lemma}
%%-/

lemma floor_arg_not_int {w : ℂ} (hw : w ∈ DeftildeS) :
    (w.im + π) / (2 * π) ∉ Set.range (Int.cast : ℤ → ℝ) := by
  intro ⟨k, hk⟩
  have hw' := hw k
  simp only [DeftildeS, Set.mem_setOf_eq] at hw
  field_simp at hk
  have hw'' := hw (k - 1)
  apply hw''
  have hpi := Real.pi_pos
  have : (w).im = ↑k * (2 * π) - π := by linarith
  rw [this]
  push_cast
  linarith

/-%%
\begin{proof}\uses{DeftildeS}\leanok
If $\frac{\Im(w)+\pi}{2\pi}$ were an integer, say equal to $k$, then
\[
\Im(w)=(2k-1)\pi=(2(k-1)+1)\pi.
\]
But this says that $\Im(w)$ is an odd multiple of $\pi$, contradicting the definition of
$\tilde S$.
\end{proof}
%%-/

/-%%
\begin{lemma}\label{continuous_floor_arg}\lean{continuous_floor_arg}\leanok
The map $w\mapsto\left\lfloor\frac{\Im(w)+\pi}{2\pi}\right\rfloor$ is continuous on $\tilde S$.
\end{lemma}
%%-/

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
      have hne := floor_arg_not_int w.prop
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

/-%%
\begin{proof}\uses{DeftildeS, floor_arg_not_int}\leanok
Fix $n\in \mathbb Z$. The fiber where
\[
\left\lfloor\frac{\Im(w)+\pi}{2\pi}\right\rfloor=n
\]
is exactly the strip
\[
(2n-1)\pi<\Im(w)<(2n+1)\pi
\]
inside $\tilde S$. The point is that equality at one of the endpoints would make
$\frac{\Im(w)+\pi}{2\pi}$ an integer, which is excluded by Lemma~\ref{floor_arg_not_int}.
Hence each fiber is open in $\tilde S$, so the map is locally constant, and therefore continuous.
\end{proof}
%%-/

/-%%
\begin{definition}\label{tildeShomeo_toFun}\lean{tildeShomeo_toFun}\leanok
Define $\varphi\colon \C\times \Z\to \C$ by $\varphi(z,n)=z+2n\pi i$.
\end{definition}
%%-/

noncomputable def tildeShomeo_toFun (zn : ℂ × ℤ) : ℂ :=
  zn.1 + (2 * zn.2 : ℂ) * π * I

/-%%
\begin{lemma}\label{tildeShomeo_toFun_mem}\lean{tildeShomeo_toFun_mem}\leanok
If $z\in S$, then $\varphi(z,n)\in \tilde S$.
\end{lemma}
%%-/

lemma tildeShomeo_toFun_mem {zn : ℂ × ℤ} (hzn : zn.1 ∈ Sstrip) : tildeShomeo_toFun zn ∈ DeftildeS := by
  obtain ⟨z, n⟩ := zn
  unfold DeftildeS tildeShomeo_toFun
  simp only [ne_eq, mem_setOf_eq]
  intro k h
  simp only [add_im, mul_im, mul_re, re_ofNat, intCast_re, im_ofNat, intCast_im, mul_zero,
    sub_zero, ofReal_re, zero_mul, add_zero, ofReal_im, I_im, mul_one, I_re] at h
  unfold Sstrip Defstrip at hzn
  simp only [mem_setOf_eq] at hzn
  set m := k - n with hm
  have h' : z.im = (2 * m + 1) * π := by rw [hm]; push_cast; linarith
  rw [h'] at hzn
  have h1 : (-1 : ℝ) < 2 * m + 1 := by nlinarith [Real.pi_pos, hzn.1]
  have h2 : (2 : ℝ) * m + 1 < 1 := by nlinarith [Real.pi_pos, hzn.2]
  have h1 : -1 < 2 * m + 1 := by exact_mod_cast h1
  have h2 : 2 * m + 1 < 1 := by exact_mod_cast h2
  omega

/-%%
\begin{proof}\uses{Sstrip, DeftildeS, tildeShomeo_toFun}\leanok
Let $z\in S$, so $-\pi<\Im(z)<\pi$. For $\varphi(z,n)=z+2n\pi i$, the imaginary part is
\[
\Im(\varphi(z,n))=\Im(z)+2n\pi.
\]
If this were equal to an odd multiple $(2k+1)\pi$, then
\[
\Im(z)=(2(k-n)+1)\pi,
\]
which is impossible because $\Im(z)$ lies strictly between $-\pi$ and $\pi$.
Therefore $\varphi(z,n)\in\tilde S$.
\end{proof}
%%-/

/-%%
\begin{definition}\label{tildeShomeo_floor}\lean{tildeShomeo_floor}\leanok
Define $N(w)=\left\lfloor\frac{\Im(w)+\pi}{2\pi}\right\rfloor$.
\end{definition}
%%-/

noncomputable def tildeShomeo_floor (w : ℂ) : ℤ := ⌊(w.im + π) / (2 * π)⌋

/-%%
\begin{definition}\label{tildeShomeo_invFun_complex}\lean{tildeShomeo_invFun_complex}\leanok
Define $\tilde\varphi^{-1}_{\C}(w)=w-2N(w)\pi i$.
\end{definition}
%%-/

noncomputable def tildeShomeo_invFun_complex (w : ℂ) : ℂ :=
  w - (2 * (tildeShomeo_floor w : ℝ)) * π * I

/-%%
\begin{lemma}\label{tildeShomeo_invFun_mem}\lean{tildeShomeo_invFun_mem}\leanok
If $w\in \tilde S$, then $\tilde\varphi^{-1}_{\C}(w)\in S$.
\end{lemma}
%%-/

lemma tildeShomeo_invFun_mem {w : ℂ} (hw : w ∈ DeftildeS) : tildeShomeo_invFun_complex w ∈ Sstrip := by
  unfold Sstrip Defstrip tildeShomeo_invFun_complex tildeShomeo_floor
  simp only [mem_setOf_eq]
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have h2pi : (0 : ℝ) < 2 * π := by linarith
  set n := ⌊(w.im + π) / (2 * π)⌋
  have hn_le : (n : ℝ) ≤ (w.im + π) / (2 * π) := Int.floor_le _
  have hn_lt : (w.im + π) / (2 * π) < n + 1 := Int.lt_floor_add_one _
  have hz_im : (w - (2 * (n : ℝ)) * ↑π * I).im = w.im - 2 * n * π := by
    simp only [sub_im, mul_im, ofReal_im, ofReal_re, I_im, I_re]
    ring_nf
    simp only [ofReal_intCast, mul_re, intCast_re, ofReal_re, intCast_im, ofReal_im,
      mul_zero, sub_zero, re_ofNat, mul_im, zero_mul, add_zero, im_ofNat]
  rw [hz_im]
  constructor
  · have hne : (w.im + π) / (2 * π) ≠ n := fun heq => by
      have : w.im = (2 * n - 1) * π := by field_simp at heq; linarith
      have : w.im = (2 * (n - 1) + 1) * π := by linarith
      exact hw (n - 1) (by rw [this]; push_cast; ring)
    have hlt : (n : ℝ) < (w.im + π) / (2 * π) := (Int.floor_le _).lt_of_ne' hne
    rw [lt_div_iff₀ h2pi] at hlt; linarith
  · rw [div_lt_iff₀ h2pi] at hn_lt; linarith

/-%%
\begin{proof}\uses{DeftildeS, Sstrip, tildeShomeo_floor, tildeShomeo_invFun_complex, floor_arg_not_int}\leanok
Set $N(w)=\left\lfloor\frac{\Im(w)+\pi}{2\pi}\right\rfloor$. By the defining inequalities for the floor
function,
$$
N(w)\le \frac{\Im(w)+\pi}{2\pi} < N(w)+1.
$$
Because $w\in\tilde S$, Lemma~\ref{floor_arg_not_int} shows that the left inequality is in fact strict.
Multiplying through by $2\pi$ gives
\[
(2N(w)-1)\pi<\Im(w)<(2N(w)+1)\pi.
\]
After subtracting $2N(w)\pi i$, the imaginary part lands in the interval $(-\pi,\pi)$, which is exactly
the condition defining $S$.
\end{proof}
%%-/

/-%%
\begin{definition}\label{tildeShomeo_invFun}\lean{tildeShomeo_invFun}\leanok
Define $\tilde\varphi^{-1}(w)=(\tilde\varphi^{-1}_{\C}(w),N(w))\in \C\times \Z$.
\end{definition}
%%-/

noncomputable def tildeShomeo_invFun (w : ℂ) : ℂ × ℤ :=
  (tildeShomeo_invFun_complex w, tildeShomeo_floor w)

/-%%
\begin{definition}\label{tildeShomeo_invFun_lift}\lean{tildeShomeo_invFun_lift}\leanok
Restrict $\tilde\varphi^{-1}$ to a map $\tilde S\to S\times \Z$.
\end{definition}
%%-/

noncomputable def tildeShomeo_invFun_lift (w : DeftildeS) : Sstrip × ℤ :=
  (⟨tildeShomeo_invFun_complex w.1, tildeShomeo_invFun_mem w.2⟩, tildeShomeo_floor w)

/-%%
\begin{lemma}\label{tildeShomeo_left_inv}\lean{tildeShomeo_left_inv}\leanok
The maps $\tilde\varphi$ and $\tilde\varphi^{-1}$ are left inverses on $S\times \Z$.
\end{lemma}
%%-/

lemma tildeShomeo_left_inv (zn : Sstrip × ℤ) :
    tildeShomeo_invFun_lift
      (⟨tildeShomeo_toFun (zn.1.1, zn.2), tildeShomeo_toFun_mem zn.1.2⟩ : DeftildeS) = zn := by
  rcases zn with ⟨⟨z, hz⟩, n⟩
  have h2pi : (0 : ℝ) < 2 * π := by nlinarith [Real.pi_pos]
  have hfloor : ⌊(z.im + 2 * n * π + π) / (2 * π)⌋ = n := by
    rw [Int.floor_eq_iff]
    constructor
    · rw [le_div_iff₀ h2pi]
      linarith [hz.1]
    · rw [div_lt_iff₀ h2pi]
      linarith [hz.2]
  apply Prod.ext
  · ext
    simp [tildeShomeo_invFun_lift, tildeShomeo_invFun_complex, tildeShomeo_floor,
      tildeShomeo_toFun, hfloor]
  · simp [tildeShomeo_invFun_lift, tildeShomeo_floor, tildeShomeo_toFun, hfloor]

/-%%
\begin{proof}\uses{Sstrip, tildeShomeo_toFun, tildeShomeo_invFun_lift, tildeShomeo_floor, tildeShomeo_invFun_complex}\leanok
Take $(z,n)\in S\times \mathbb Z$. Since $z\in S$, we have $-\pi<\Im(z)<\pi$, so
\[
n\le \frac{\Im(z+2n\pi i)+\pi}{2\pi} < n+1.
\]
Hence the floor function recovers exactly the integer $n$. Therefore
$\tilde\varphi^{-1}$ subtracts precisely the same shift $2n\pi i$ that $\varphi$ added, and it also
returns the second coordinate $n$. Thus $\tilde\varphi^{-1}(\varphi(z,n))=(z,n)$.
\end{proof}
%%-/

/-%%
\begin{lemma}\label{tildeShomeo_right_inv}\lean{tildeShomeo_right_inv}\leanok
The maps $\tilde\varphi$ and $\tilde\varphi^{-1}$ are right inverses on $\tilde S$.
\end{lemma}
%%-/

lemma tildeShomeo_right_inv (w : DeftildeS) :
    (⟨tildeShomeo_toFun (tildeShomeo_invFun w), tildeShomeo_toFun_mem (tildeShomeo_invFun_mem w.2)⟩ : DeftildeS) = w := by
  rcases w with ⟨w, hw⟩
  ext
  simp [tildeShomeo_toFun, tildeShomeo_invFun, tildeShomeo_invFun_complex]

/-%%
\begin{proof}\uses{tildeShomeo_toFun, tildeShomeo_invFun, tildeShomeo_invFun_complex, tildeShomeo_floor}\leanok
By definition,
\[
\tilde\varphi^{-1}(w)=\bigl(w-2N(w)\pi i,\;N(w)\bigr).
\]
Applying $\tilde\varphi$ to this pair adds back the same quantity $2N(w)\pi i$, so the first coordinate
returns to $w$. Therefore $\tilde\varphi(\tilde\varphi^{-1}(w))=w$.
\end{proof}
%%-/

/-%%
\begin{lemma}\label{tildeShomeo_continuous_toFun}\lean{tildeShomeo_continuous_toFun}\leanok
The forward map $S\times \Z\to \tilde S$ is continuous.
\end{lemma}
%%-/

lemma tildeShomeo_continuous_toFun : Continuous (fun zn : Sstrip × ℤ =>
    (⟨tildeShomeo_toFun (zn.1.1, zn.2), tildeShomeo_toFun_mem zn.1.2⟩ : DeftildeS)) := by
  refine Continuous.subtype_mk ?_ ?_
  have hz : Continuous (fun zn : Sstrip × ℤ => (zn.1.1 : ℂ)) :=
    continuous_subtype_val.comp continuous_fst
  have hn : Continuous (fun zn : Sstrip × ℤ => (zn.2 : ℂ)) :=
    (continuous_of_discreteTopology : Continuous (fun n : ℤ => (n : ℂ))).comp continuous_snd
  have hterm : Continuous (fun zn : Sstrip × ℤ => (2 : ℂ) * (zn.2 : ℂ) * π * I) := by
    exact (((continuous_const.mul hn).mul continuous_const).mul continuous_const)
  simpa [tildeShomeo_toFun] using hz.add hterm

/-%%
\begin{proof}\uses{tildeShomeo_toFun, tildeShomeo_toFun_mem}\leanok
The formula for the forward map is
\[
(z,n)\longmapsto z+2n\pi i.
\]
The first term is continuous in $(z,n)$, and the second term depends only on $n$; since $\mathbb Z$ is
discrete, every map out of it is continuous. Therefore the sum is continuous as a map into $\mathbb C$.
Lemma~\ref{tildeShomeo_toFun_mem} shows that its image lies in $\tilde S$, so it is continuous as a map
into $\tilde S$.
\end{proof}
%%-/

/-%%
\begin{lemma}\label{tildeShomeo_continuous_invFun}\lean{tildeShomeo_continuous_invFun}\leanok
The inverse map $\tilde S\to S\times \Z$ is continuous.
\end{lemma}
%%-/

lemma tildeShomeo_continuous_invFun : Continuous tildeShomeo_invFun_lift := by
  refine Continuous.prodMk ?_ ?_
  · refine Continuous.subtype_mk ?_ ?_
    have hfloor_int : Continuous (fun w : DeftildeS => tildeShomeo_floor w.1) := by
      simpa [tildeShomeo_floor] using continuous_floor_arg
    have hfloor_c : Continuous (fun w : DeftildeS => (tildeShomeo_floor w.1 : ℂ)) :=
      (continuous_of_discreteTopology : Continuous (fun n : ℤ => (n : ℂ))).comp hfloor_int
    have hterm : Continuous (fun w : DeftildeS => (2 : ℂ) * (tildeShomeo_floor w.1 : ℂ) * π * I) := by
      exact (((continuous_const.mul hfloor_c).mul continuous_const).mul continuous_const)
    have hterm' : Continuous (fun w : DeftildeS => (2 * (tildeShomeo_floor w.1 : ℝ)) * π * I) := by
      simpa [Int.cast_ofNat, Int.cast_mul, Int.cast_two, mul_assoc, mul_left_comm, mul_comm] using hterm
    simpa [tildeShomeo_invFun_complex, mul_assoc, mul_left_comm, mul_comm] using
      continuous_subtype_val.sub hterm'
  · simpa [tildeShomeo_invFun_lift, tildeShomeo_floor] using continuous_floor_arg

/-%%
\begin{proof}\uses{continuous_floor_arg, tildeShomeo_invFun_lift, tildeShomeo_invFun_complex, tildeShomeo_floor}\leanok
The second component of $\tilde\varphi^{-1}$ is the function
\[
w\mapsto N(w)=\left\lfloor\frac{\Im(w)+\pi}{2\pi}\right\rfloor,
\]
which is continuous on $\tilde S$ by Lemma~\ref{continuous_floor_arg}. The first component is
\[
w\mapsto w-2N(w)\pi i,
\]
so it is obtained from the identity map and the continuous function $N(w)$ by continuous algebraic
operations. Hence both components are continuous, and therefore the product map
$\tilde\varphi^{-1}\colon \tilde S\to S\times\mathbb Z$ is continuous.
\end{proof}
%%-/

/-%%
\begin{lemma}\label{tildeShomeo}\lean{tildeShomeo}\uses{DeftildeS, Sstrip}\leanok
Define $\varphi\colon S\times \Z \to \C$  by $\varphi(z,k)=z+2k\pi  *I$. Then
$\varphi\colon S\times \Z\to \tilde S$  is a homeomorphism.
\end{lemma}
%%-/

noncomputable def tildeShomeo : Homeomorph (Sstrip × ℤ) DeftildeS where
  toFun zn := ⟨tildeShomeo_toFun (zn.1.1, zn.2), tildeShomeo_toFun_mem zn.1.2⟩
  invFun := tildeShomeo_invFun_lift
  left_inv := tildeShomeo_left_inv
  right_inv := tildeShomeo_right_inv
  continuous_toFun := tildeShomeo_continuous_toFun
  continuous_invFun := tildeShomeo_continuous_invFun

/-%%
\begin{proof}\uses{DeftildeS, Sstrip, tildeShomeo_toFun, tildeShomeo_toFun_mem, tildeShomeo_invFun_lift, tildeShomeo_left_inv, tildeShomeo_right_inv, tildeShomeo_continuous_toFun, tildeShomeo_continuous_invFun}\leanok
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

\begin{definition}\label{DefwidetildePBlog}\leanok
Let $\widetilde{PBlog}\colon T\times \Z\to S\times \Z$
be defined by $\widetilde{PBlog}(z,n)=(PBlog(z),n)$
for all $z\in T$ and $n\in \Z$.
\end{definition}
%%-/

noncomputable def DefwidetildePBlog :
    splitPlane × ℤ → Sstrip × ℤ
  | (z, n) => (inverseHomeo.invFun z, n)

/-%%
\begin{lemma}\label{widetildePBlogHomeo}\lean{widetildePBlogHomeo}\leanok
$\widetilde{PBlog}\colon T\times \Z\to S\times \Z$ is a homeomorphism.
\end{lemma}
%%-/

noncomputable def widetildePBlogHomeo :
    Homeomorph (splitPlane × ℤ) (Sstrip × ℤ) := inverseHomeo.symm.prodCongr (Homeomorph.refl _)

/-%%

\begin{proof}\uses{DefwidetildePBlog, inverseHomeo}\leanok
By Definition~\ref{DefwidetildePBlog}
$\widetilde PBlog$
is the product of $PBlog\colon T\to S$
and ${\rm Id}_\Z\colon \Z\to\Z$.
By Lemma~\ref{inverseHomeo} the first of these factors
is a homeomorphism. Since ${\rm Id}_\Z$ is a homeomorphism.
it follows from basic properties of homeomorphisms that the
product $\widetilde{PBlog}$ is a homeomorphism.
\end{proof}
%%-/

/-%%
\begin{lemma}\label{splitPlane_isOpen}\lean{splitPlane_isOpen}\uses{splitPlane}\leanok
The set $T=\{z\in \C \mid \Re(z)>0 \text{ or } \Im(z)\neq 0\}$ is open.
\end{lemma}
%%-/

lemma splitPlane_isOpen : IsOpen splitPlane := by
  unfold splitPlane
  refine IsOpen.union ?_ ?_
  · exact isOpen_lt continuous_const continuous_re
  · exact isOpen_ne_fun continuous_im continuous_const

lemma splitPlane_ne_zero {z : ℂ} (hz : z ∈ splitPlane) : z ≠ 0 := by
  intro hz0
  have hz' : z.re > 0 ∨ z.im ≠ 0 := by simpa [splitPlane] using hz
  rw [hz0] at hz'
  simp at hz'

/-%%
\begin{proof}\uses{splitPlane}\leanok
By Definition~\ref{splitPlane}, $T$ is the union of
$\{z\mid \Re(z)>0\}$ and $\{z\mid \Im(z)\neq 0\}$.
Both are open: the first is an open strict inequality set,
and the second is the complement of the closed set $\{\Im(z)=0\}$.
Hence $T$ is open.
\end{proof}
%%-/

/-%%
\begin{lemma}\label{mem_Deftilde_of_mem_source}\lean{mem_Deftilde_of_mem_source}\uses{CSexp, splitPlane, DeftildeS}\leanok
If $x\in CSexp^{-1}(T)$, then $x\in \widetilde S$.
\end{lemma}
%%-/

lemma mem_Deftilde_of_mem_source {x : ℂ} (hx : x ∈ CSexp ⁻¹' splitPlane) : x ∈ DeftildeS := by
  intro k hk
  have hx' : (CSexp x).re > 0 ∨ (CSexp x).im ≠ 0 := by
    simpa [splitPlane, Set.mem_preimage] using hx
  have harg : (2 * (k : ℝ) + 1) * π = ((2 * k + 1 : ℤ) : ℝ) * π := by
    push_cast
    ring_nf
  have him0 : (CSexp x).im = 0 := by
    unfold CSexp
    rw [Complex.exp_im, hk]
    rw [harg]
    simpa using (Real.sin_int_mul_pi (2 * k + 1))
  have hre_not_pos : ¬ (CSexp x).re > 0 := by
    unfold CSexp
    rw [Complex.exp_re, hk]
    rw [harg]
    have hcos : Real.cos ((((2 * k + 1 : ℤ) : ℝ) * π)) = -1 := by
      have hk' : (((2 * k + 1 : ℤ) : ℝ) * π) = π + k * (2 * π) := by
        push_cast
        ring_nf
      rw [hk', Real.cos_add_int_mul_two_pi, Real.cos_pi]
    rw [hcos]
    have hpos : 0 < Real.exp x.re := Real.exp_pos _
    linarith
  exact (hx'.elim hre_not_pos (fun him => him him0))

/-%%
\begin{proof}\uses{CSexp, splitPlane, DeftildeS}\leanok
By contradiction, suppose $\Im(x)=(2k+1)\pi$ for some $k\in \Z$.
Then $\Im(CSexp(x))=0$ and $\Re(CSexp(x))<0$, so $CSexp(x)\notin T$.
This contradicts $x\in CSexp^{-1}(T)$.
Hence no odd multiple of $\pi$ occurs as $\Im(x)$, i.e. $x\in\widetilde S$.
\end{proof}
%%-/

/-%%
\begin{lemma}\label{CSexp_tildeShomeo_invFun_complex}\lean{CSexp_tildeShomeo_invFun_complex}\uses{periodicity, tildeShomeo_invFun_complex, tildeShomeo_floor}\leanok
For every $x\in \C$, one has
$CSexp(\tilde\varphi^{-1}_{\C}(x))=CSexp(x)$.
\end{lemma}
%%-/

lemma CSexp_tildeShomeo_invFun_complex (x : ℂ) :
    CSexp (tildeShomeo_invFun_complex x) = CSexp x := by
  apply (periodicity _ _).2
  refine ⟨-(tildeShomeo_floor x), ?_⟩
  unfold tildeShomeo_invFun_complex
  simp [sub_eq_add_neg, mul_assoc, mul_left_comm, mul_comm]

/-%%
\begin{proof}\uses{periodicity, tildeShomeo_invFun_complex, tildeShomeo_floor}\leanok
By Definition~\ref{tildeShomeo_invFun_complex},
$\tilde\varphi^{-1}_{\C}(x)=x-2N(x)\pi i$, where $N(x)$ is an integer
(Definition~\ref{tildeShomeo_floor}).
By periodicity of $CSexp$ (Lemma~\ref{periodicity}),
shifting by an integer multiple of $2\pi i$ does not change the value.
\end{proof}
%%-/

/-%%
\begin{lemma}\label{PBlog_CSexp_eq_tildeShomeo_invFun_complex}\lean{PBlog_CSexp_eq_tildeShomeo_invFun_complex}\uses{mem_Deftilde_of_mem_source, tildeShomeo_invFun_mem, inverseHomeo, CSexp_tildeShomeo_invFun_complex}\leanok
If $x\in CSexp^{-1}(T)$, then
$PBlog(CSexp(x))=\tilde\varphi^{-1}_{\C}(x)$.
\end{lemma}
%%-/

lemma PBlog_CSexp_eq_tildeShomeo_invFun_complex {x : ℂ}
    (hx : x ∈ CSexp ⁻¹' splitPlane) :
    PBlog (CSexp x) = tildeShomeo_invFun_complex x := by
  have hxDeftilde : x ∈ DeftildeS := mem_Deftilde_of_mem_source hx
  have hxS : tildeShomeo_invFun_complex x ∈ Sstrip := tildeShomeo_invFun_mem hxDeftilde
  have hlog : PBlog (CSexp (tildeShomeo_invFun_complex x)) = tildeShomeo_invFun_complex x := by
    exact congrArg Subtype.val (inverseHomeo.left_inv ⟨tildeShomeo_invFun_complex x, hxS⟩)
  simpa [CSexp_tildeShomeo_invFun_complex x] using hlog

/-%%
\begin{proof}\uses{mem_Deftilde_of_mem_source, tildeShomeo_invFun_mem, inverseHomeo, CSexp_tildeShomeo_invFun_complex}\leanok
From Lemma~\ref{mem_Deftilde_of_mem_source}, $x\in \widetilde S$.
Then Lemma~\ref{tildeShomeo_invFun_mem} gives
$\tilde\varphi^{-1}_{\C}(x)\in S$.
Applying the left-inverse identity from Lemma~\ref{inverseHomeo} to
$\tilde\varphi^{-1}_{\C}(x)$ gives
$PBlog(CSexp(\tilde\varphi^{-1}_{\C}(x)))=\tilde\varphi^{-1}_{\C}(x)$.
Finally use Lemma~\ref{CSexp_tildeShomeo_invFun_complex}.
\end{proof}
%%-/

/-%%
\begin{lemma}\label{floor_shift_PBlog}\lean{floor_shift_PBlog}\uses{ContPBlog}\leanok
For $z\in T$ and $n\in \Z$,
\[
\left\lfloor\frac{\Im(PBlog(z)+2n\pi i)+\pi}{2\pi}\right\rfloor=n.
\]
\end{lemma}
%%-/

lemma floor_shift_PBlog (z : ℂ) (hz : z ∈ splitPlane) (n : ℤ) :
    ⌊((PBlog z + (2 * n : ℂ) * π * I).im + π) / (2 * π)⌋ = n := by
  have hzIm : -π < im (PBlog z) ∧ im (PBlog z) < π := (ContPBlog.2 z hz)
  have h2pi : (0 : ℝ) < 2 * π := by linarith [Real.pi_pos]
  have him : (PBlog z + (2 * n : ℂ) * π * I).im = (PBlog z).im + 2 * n * π := by
    simp [mul_assoc, mul_left_comm, mul_comm]
  rw [Int.floor_eq_iff]
  constructor
  · rw [le_div_iff₀ h2pi]
    rw [him]
    linarith [hzIm.1]
  · rw [div_lt_iff₀ h2pi]
    rw [him]
    linarith [hzIm.2]

/-%%
\begin{proof}\uses{ContPBlog}\leanok
By Lemma~\ref{ContPBlog}, for $z\in T$ we have
$-\pi<\Im(PBlog(z))<\pi$.
Hence
$2n\pi-\pi<\Im(PBlog(z)+2n\pi i)<2n\pi+\pi$,
which is exactly the interval characterization of
\[
\left\lfloor\frac{\Im(PBlog(z)+2n\pi i)+\pi}{2\pi}\right\rfloor=n.
\]
\end{proof}
%%-/

lemma CSexp_PBlog_add_period (z : ℂ) (hz : z ∈ splitPlane) (n : ℤ) :
    CSexp (PBlog z + (2 * n : ℂ) * π * I) = z := by
  have hz0 : z ≠ 0 := splitPlane_ne_zero hz
  have hperiod : CSexp ((2 * n : ℂ) * π * I) = 1 := by
    unfold CSexp
    have hmul : ((2 * n : ℂ) * π * I) = (n : ℂ) * (2 * π * I) := by ring
    rw [hmul, Complex.exp_int_mul_two_pi_mul_I]
  calc
    CSexp (PBlog z + (2 * n : ℂ) * π * I)
        = CSexp (PBlog z) * CSexp ((2 * n : ℂ) * π * I) := multiplicativity _ _
    _ = z * CSexp ((2 * n : ℂ) * π * I) := by rw [(ImPBlog z hz0).1]
    _ = z * 1 := by rw [hperiod]
    _ = z := by simp

/-%%

\begin{proposition}\label{trivOverT}\lean{trivOverT}\leanok
The composition $\psi=\varphi\circ\widetilde{PBlog}\colon T\times \Z\to \tilde S$ defines
a trivialization of $CSexp$
on $T$
\end{proposition}
%%-/

noncomputable def trivOverT : Trivialization ℤ CSexp where
  toFun := fun x => (CSexp x, ⌊(x.im + π) / (2 * π)⌋)
  invFun := fun x => PBlog x.1 + (2 * x.2 : ℂ) * π * I
  source := CSexp ⁻¹' splitPlane  -- = DeftildeS
  target := splitPlane ×ˢ ⊤
  baseSet := splitPlane
  open_baseSet := splitPlane_isOpen
  source_eq := by rfl
  target_eq := by rfl
  proj_toFun p hp := by simp
  map_source' x hx := ⟨hx, trivial⟩
  map_target' x hx := by
    rcases x with ⟨z, n⟩
    have hz : z ∈ splitPlane := hx.1
    change CSexp (PBlog z + (2 * n : ℂ) * π * I) ∈ splitPlane
    simpa [CSexp_PBlog_add_period z hz n] using hz
  continuousOn_toFun := by
    refine (Contexp.continuousOn).prodMk ?_
    rw [continuousOn_iff_continuous_restrict]
    let g : (CSexp ⁻¹' splitPlane) → DeftildeS := fun x => ⟨x.1, mem_Deftilde_of_mem_source x.2⟩
    have hg : Continuous g :=
      Continuous.subtype_mk continuous_subtype_val (fun x => mem_Deftilde_of_mem_source x.2)
    have hfloor : Continuous (fun w : DeftildeS => ⌊((w.val).im + π) / (2 * π)⌋) :=
      continuous_floor_arg
    simpa [Set.restrict, g] using hfloor.comp hg
  continuousOn_invFun := by
    have hlog : ContinuousOn (fun x : ℂ × ℤ => PBlog x.1) (splitPlane ×ˢ (⊤ : Set ℤ)) := by
      refine ContPBlog.1.comp continuousOn_fst ?_
      intro x hx
      exact hx.1
    have hsnd : Continuous (fun x : ℂ × ℤ => (x.2 : ℂ)) :=
      (continuous_of_discreteTopology : Continuous (fun n : ℤ => (n : ℂ))).comp continuous_snd
    have hshift : ContinuousOn (fun x : ℂ × ℤ => (2 * x.2 : ℂ) * π * I) (splitPlane ×ˢ (⊤ : Set ℤ)) :=
      ((((continuous_const.mul hsnd).mul continuous_const).mul continuous_const)).continuousOn
    exact hlog.add hshift
  left_inv' x hx := by
    have hPB : PBlog (CSexp x) = tildeShomeo_invFun_complex x :=
      PBlog_CSexp_eq_tildeShomeo_invFun_complex hx
    have hPB' : PBlog (CSexp x) = x - (2 * (⌊(x.im + π) / (2 * π)⌋ : ℝ)) * π * I := by
      simpa [tildeShomeo_floor, tildeShomeo_invFun_complex] using hPB
    calc
      PBlog (CSexp x) + (2 * (⌊(x.im + π) / (2 * π)⌋ : ℂ)) * π * I
          = (x - (2 * (⌊(x.im + π) / (2 * π)⌋ : ℝ)) * π * I)
              + (2 * (⌊(x.im + π) / (2 * π)⌋ : ℂ)) * π * I := by
                simp [hPB']
      _ = x := by
        norm_cast
        ring_nf
  right_inv' x hx := by
    rcases x with ⟨z, n⟩
    have hz : z ∈ splitPlane := hx.1
    have hexp : CSexp (PBlog z + (2 * n : ℂ) * π * I) = z :=
      CSexp_PBlog_add_period z hz n
    have hfloor : ⌊((PBlog z + (2 * n : ℂ) * π * I).im + π) / (2 * π)⌋ = n :=
      floor_shift_PBlog z hz n
    refine Prod.ext ?_ ?_
    · exact hexp
    · simpa [mul_assoc, mul_left_comm, mul_comm] using hfloor
  open_source := by
    simpa [CSexp] using splitPlane_isOpen.preimage Contexp
  open_target := by
    simpa [Set.top_eq_univ] using splitPlane_isOpen.prod isOpen_univ

/-%%

\begin{proof}\uses{tildeShomeo, widetildePBlogHomeo, periodicity, trivialization}\leanok
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
\begin{lemma}\label{commute_symm_of_commute}\lean{commute_symm_of_commute}\leanok
Suppose $f\colon E\to X$ is a map between topological spaces and
$\varphi\colon X\to X$, $\tilde\varphi\colon E\to E$ are homeomorphisms such that
$f\circ\tilde\varphi=\varphi\circ f$.
Then also
$f\circ\tilde\varphi^{-1}=\varphi^{-1}\circ f$.
\end{lemma}
%%-/

lemma commute_symm_of_commute {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    {f : E → X} (φ : X ≃ₜ X) (tildeφ : E ≃ₜ E) (hcomm : f ∘ tildeφ = φ ∘ f) :
    f ∘ tildeφ.symm = φ.symm ∘ f := by
  ext x
  have hx : f x = φ (f (tildeφ.symm x)) := by
    simpa using congrFun hcomm (tildeφ.symm x)
  calc
    f (tildeφ.symm x) = φ.symm (φ (f (tildeφ.symm x))) := by rw [φ.symm_apply_apply]
    _ = φ.symm (f x) := by rw [hx.symm]

/-%%
\begin{proof}\leanok
Apply the identity $f\circ\tilde\varphi=\varphi\circ f$ to a point of the form
$\tilde\varphi^{-1}(x)$. This gives
\[
f(x)=\varphi(f(\tilde\varphi^{-1}(x))).
\]
Now compose both sides with $\varphi^{-1}$ to obtain
\[
f(\tilde\varphi^{-1}(x))=\varphi^{-1}(f(x)).
\]
Since this holds for every $x$, the desired identity follows.
\end{proof}
%%-/


/-%%
\begin{lemma}\label{homeoInv}\lean{homeoInv}\leanok
Suppose $f\colon E\to X$ is a map between topological spaces and $U\subset X$ is an open subset
and there is a trivialization for $f$ on $U$. Suppose also that there are homeomorphisms $\varphi\colon X\to X$ and $\tilde \varphi\colon E\to E$
with $f\circ\tilde\varphi =\varphi\circ f$. Then there is a trivialization for $f$ on $\varphi(U)$.
\end{lemma}
%%-/

noncomputable def homeoInv {E X I : Type*} [TopologicalSpace E] [TopologicalSpace X]
    [TopologicalSpace I] {f : E → X} (e : Trivialization I f) (φ : X ≃ₜ X)
    (tildeφ : E ≃ₜ E) (hcomm : f ∘ tildeφ = φ ∘ f) :
    {e' : Trivialization I f // e'.baseSet = φ '' e.baseSet} := by
  let e' : Trivialization I (f ∘ tildeφ.symm) := e.compHomeomorph tildeφ.symm
  let ψ : X × I ≃ₜ X × I := φ.prodCongr (Homeomorph.refl I)
  have hcomm_symm : f ∘ tildeφ.symm = φ.symm ∘ f := commute_symm_of_commute φ tildeφ hcomm
  let t : Trivialization I f :=
    { toPartialHomeomorph := e'.toPartialHomeomorph.transHomeomorph ψ
      baseSet := φ '' e.baseSet
      open_baseSet := by
        simpa using φ.isOpenMap _ e.open_baseSet
      source_eq := by
        ext x
        suffices hx : tildeφ.symm x ∈ e.source ↔ x ∈ f ⁻¹' (φ '' e.baseSet) by
          simpa [PartialHomeomorph.transHomeomorph, e', Trivialization.compHomeomorph] using hx
        rw [e.mem_source]
        have hsymm : f (tildeφ.symm x) = φ.symm (f x) := by
          simpa [Function.comp] using congrFun hcomm_symm x
        rw [hsymm]
        constructor
        · intro hx
          exact ⟨φ.symm (f x), hx, by simp⟩
        · rintro ⟨y, hy, hyx⟩
          have hxy : φ.symm (f x) = y := by
            simpa [hyx] using (φ.symm_apply_apply y)
          simpa [hxy] using hy
      target_eq := by
        ext x
        suffices hx : ψ.symm x ∈ e'.target ↔ x ∈ (φ '' e.baseSet) ×ˢ (Set.univ : Set I) by
          simpa [PartialHomeomorph.transHomeomorph] using hx
        rw [e'.target_eq]
        change (φ.symm x.1 ∈ e.baseSet ∧ x.2 ∈ (Set.univ : Set I)) ↔
          x ∈ (φ '' e.baseSet) ×ˢ (Set.univ : Set I)
        constructor
        · intro hx
          exact ⟨⟨φ.symm x.1, hx.1, by simp⟩, hx.2⟩
        · rintro ⟨hx1, hx2⟩
          rcases hx1 with ⟨y, hy, hyx⟩
          refine ⟨?_, hx2⟩
          rw [← hyx]
          simpa using hy
      proj_toFun := by
        intro p hp
        have hp' : p ∈ e'.source := by simpa using hp
        change (ψ (e' p)).1 = f p
        simp [ψ, Equiv.prodCongr_apply]
        have hproj : (e' p).1 = f (tildeφ.symm p) := by
          simpa [Function.comp] using e'.proj_toFun p hp'
        simpa [hproj, Function.comp] using (congrFun hcomm (tildeφ.symm p)).symm }
  exact ⟨t, rfl⟩

@[simp] theorem homeoInv_baseSet {E X I : Type*} [TopologicalSpace E] [TopologicalSpace X]
    [TopologicalSpace I] {f : E → X} (e : Trivialization I f) (φ : X ≃ₜ X)
    (tildeφ : E ≃ₜ E) (hcomm : f ∘ tildeφ = φ ∘ f) :
    (homeoInv e φ tildeφ hcomm).1.baseSet = φ '' e.baseSet :=
  (homeoInv e φ tildeφ hcomm).2

/-%%
\begin{proof}\uses{trivialization, commute_symm_of_commute}\leanok
By Lemma~\ref{commute_symm_of_commute}, we also have
$f\circ\tilde\varphi^{-1}=\varphi^{-1}\circ f$.
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

\begin{definition}\label{TprimeDef}\lean{TprimeDef}\leanok
Let
\[
T'=\{z\in \C \mid \Re(z)<0 \text{ or } \Im(z)\neq 0\}.
\]
\end{definition}
%%-/

def TprimeDef : Set ℂ := {z : ℂ | re z < 0 ∨ im z ≠ 0}

/-%%

\begin{corollary}\label{trivOverTprime}\lean{trivOverTprime}\leanok
$T'$ is the base of a trivialization for $CSexp\colon \C\to \C$
with non-empty fiber.
\end{corollary}
%%-/

noncomputable def trivOverTprime : {e : Trivialization ℤ CSexp // e.baseSet = TprimeDef} := by
  let φ : ℂ ≃ₜ ℂ := Homeomorph.neg ℂ
  let tildeφ : ℂ ≃ₜ ℂ := Homeomorph.addRight (π * I)
  have hcomm : CSexp ∘ tildeφ = φ ∘ CSexp := by
    ext z
    calc
      CSexp (tildeφ z) = CSexp (z + π * I) := by rfl
      _ = CSexp z * CSexp (π * I) := multiplicativity z (π * I)
      _ = CSexp z * (-1) := by
        unfold CSexp
        rw [Complex.exp_pi_mul_I]
      _ = φ (CSexp z) := by simp [φ]
  rcases homeoInv trivOverT φ tildeφ hcomm with ⟨e, he⟩
  refine ⟨e, ?_⟩
  rw [he]
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    change w ∈ splitPlane at hw
    simpa [φ, splitPlane, TprimeDef]
  · intro hz
    refine ⟨-z, ?_, by simp [φ]⟩
    change -z ∈ splitPlane
    simpa [splitPlane, TprimeDef] using hz

@[simp] theorem trivOverTprime_baseSet : trivOverTprime.1.baseSet = TprimeDef :=
  trivOverTprime.2

/-%%

\begin{proof}\uses{multiplicativity, Eulersformula, homeoInv, trivOverT, splitPlane, TprimeDef}\leanok
We have homeomorphism $\mu \colon \C\to \C$ that sends $z \to CSexp(\pi  *I)z)$
and the homeomorphism $\tilde \mu\colon \C\to \C$ defined by $\tilde \mu(z)=z+\pi  *I$
Clearly  by Lemma~\ref{multiplicativity} and Lemma~\ref{Eulersformula}
$CSexp(\tilde\mu(z))= \mu(CSexp(z))$.
By Definition~\ref{splitPlane} and Definition~\ref{TprimeDef}
$\mu(T)=T'$. The result now follows from Lemma~\ref{homeoInv} and Proposition~\ref{trivOverT}.
\end{proof}
%%-/

/-%%

\begin{lemma}\label{xinTorTprime}\lean{xinTorTprime}\leanok
For $x\in \C$ with $x\not= 0$, either $x\in T$ or $x\in T'$.
\end{lemma}
%%-/

lemma xinTorTprime (x : ℂ) (hx : x ≠ 0) : x ∈ splitPlane ∨ x ∈ TprimeDef := by
  by_cases hre : x.re > 0
  · left
    simp [splitPlane, hre]
  · have hre_le : x.re ≤ 0 := le_of_not_gt hre
    by_cases hlt : x.re < 0
    · right
      simp [TprimeDef, hlt]
    · left
      have hre0 : x.re = 0 := le_antisymm hre_le (le_of_not_gt hlt)
      have him : x.im ≠ 0 := by
        intro him0
        apply hx
        apply Complex.ext <;> simp [hre0, him0]
      simp [splitPlane, hre0, him]

/-%%

\begin{proof}\uses{splitPlane, TprimeDef}\leanok
Suppose that $x\in \C$ and $x\not= 0$. Then either $Re(x)> 0$ or $Re(x)\le 0$. If $Re(x)>0$, then by Definition~\ref{splitPlane} $x\in T$. if $Re(x)< 0$ then by Definition~\ref{TprimeDef} $x\in T'$. Finally, if $Re(z)=0$
and $z\not=0$, then $Im(z)\not= 0$ and $z\in T$.
\end{proof}
%%-/

/-%%

\begin{corollary}\label{TcupTprimeCstar}\lean{TcupTprimeCstar}\leanok
$T\cup T'=\{z\in \C | z∈ Cstar\}$.
\end{corollary}
%%-/

theorem TcupTprimeCstar : splitPlane ∪ TprimeDef = Cstar := by
  ext z
  rw [Cstar]
  constructor
  · rintro (hz | hz) hz0
    · have hz' : z.re > 0 ∨ z.im ≠ 0 := by
        simpa [splitPlane] using hz
      rcases hz' with hre | him
      · simp [hz0] at hre
      · simp [hz0] at him
    · have hz' : z.re < 0 ∨ z.im ≠ 0 := by
        simpa [TprimeDef] using hz
      rcases hz' with hre | him
      · simp [hz0] at hre
      · simp [hz0] at him
  · intro hz
    exact xinTorTprime z hz

/-%%

\begin{proof}\uses{xinTorTprime, splitPlane, TprimeDef, Cstar}\leanok
If $x\in T\cup T'$, then by Definitions~\ref{splitPlane} and \ref{TprimeDef}
either $\Re(x)>0$, or $\Re(x)<0$, or $\Im(x)\neq 0$. In each case $x\neq 0$, so
$x\in Cstar$ by Definition~\ref{Cstar}.
Conversely, if $x\in Cstar$, then $x\neq 0$, so Lemma~\ref{xinTorTprime} shows that
$x\in T$ or $x\in T'$. Hence $x\in T\cup T'$.
\end{proof}
%%-/

/-%%

\begin{corollary}\label{expCP}\lean{expCP}\leanok
$CSexp\colon \C\to \C $ is a covering projection over $Cstar$ with source $\C$.
The image of $CSexp$ is  $Cstar$.
\end{corollary}
%%-/

theorem expCP : IsCoveringOn CSexp Cstar ∧ CSexp ⁻¹' Cstar = Set.univ ∧ Set.SurjOn CSexp Set.univ Cstar := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    have hx' : x ∈ splitPlane ∪ TprimeDef := by
      simpa [TcupTprimeCstar] using hx
    rcases hx' with hxT | hxT'
    · exact IsEvenlyCovered.to_isEvenlyCovered_preimage ⟨inferInstance, trivOverT, by simpa using hxT⟩
    · exact IsEvenlyCovered.to_isEvenlyCovered_preimage
        ⟨inferInstance, trivOverTprime.1, by simpa using hxT'⟩
  · ext z
    simp [Cstar, CSexp, Complex.exp_ne_zero]
  · intro z hz
    refine ⟨PBlog z, by simp, ?_⟩
    exact (ImPBlog z (by simpa [Cstar] using hz)).1

/-%%

\begin{proof}\uses{Cstar, trivOverT, trivOverTprime, ImPBlog, TcupTprimeCstar, IsCoveringOn}\leanok
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

\begin{definition}\label{CSexpCstar}\lean{CSexpCstar}\uses{CSexp, Cstar}\leanok
Let
\[
CSexpCstar\colon \C \to Cstar
\]
be the map obtained from $CSexp$ by regarding $CSexp(z)$ as an element of $Cstar$.
\end{definition}
%%-/

noncomputable def CSexpCstar : ℂ → Cstar :=
  Cstar.codRestrict CSexp fun z => by
    simp [Cstar, CSexp, Complex.exp_ne_zero]

/-%%

\begin{lemma}\label{CSexpCstar_coe}\lean{CSexpCstar_coe}\leanok
For every $z\in \C$, forgetting that $CSexpCstar(z)$ lies in $Cstar$ gives back $CSexp(z)$.
\end{lemma}
%%-/

@[simp] theorem CSexpCstar_coe (z : ℂ) : ((CSexpCstar z : Cstar) : ℂ) = CSexp z :=
  rfl

/-%%
\begin{proof}\uses{CSexpCstar}\leanok
This is immediate from Definition~\ref{CSexpCstar}.
\end{proof}
%%-/

/-%%
\begin{lemma}\label{splitPlane_subset_Cstar}\lean{splitPlane_subset_Cstar}\leanok
We have $T\subset Cstar$.
\end{lemma}
%%-/

lemma splitPlane_subset_Cstar : splitPlane ⊆ Cstar := by
  intro z hz
  exact splitPlane_ne_zero hz

/-%%
\begin{proof}\uses{splitPlane, Cstar}\leanok
If $z\in T$, then by Definition~\ref{splitPlane} either $\Re(z)>0$ or $\Im(z)\neq 0$.
In either case $z\neq 0$, so $z\in Cstar$ by Definition~\ref{Cstar}.
\end{proof}
%%-/

/-%%
\begin{lemma}\label{TprimeDef_subset_Cstar}\lean{TprimeDef_subset_Cstar}\leanok
We have $T'\subset Cstar$.
\end{lemma}
%%-/

lemma TprimeDef_subset_Cstar : TprimeDef ⊆ Cstar := by
  intro z hz
  have hz' : z.re < 0 ∨ z.im ≠ 0 := by
    simpa [TprimeDef] using hz
  rcases hz' with hre | him
  · intro hz0
    simp [hz0] at hre
  · intro hz0
    simp [hz0] at him

/-%%
\begin{proof}\uses{TprimeDef, Cstar}\leanok
If $z\in T'$, then by Definition~\ref{TprimeDef} either $\Re(z)<0$ or $\Im(z)\neq 0$.
Again either alternative implies $z\neq 0$, hence $z\in Cstar$ by Definition~\ref{Cstar}.
\end{proof}
%%-/

/-%%
\begin{lemma}\label{trivializationCstar}\lean{trivializationCstar}\leanok
If $e$ is a trivialization of $CSexp\colon \C\to \C$ over a set $U$, then the same formulas
define a trivialization of $CSexpCstar\colon \C\to Cstar$ over $U\cap Cstar$.
\end{lemma}
%%-/

noncomputable def trivializationCstar (e : Trivialization ℤ CSexp) :
    Trivialization ℤ CSexpCstar where
  toFun := fun x => (⟨CSexp x, by simp [Cstar, CSexp, Complex.exp_ne_zero]⟩, (e x).2)
  invFun := fun x => e.invFun ((x.1 : ℂ), x.2)
  source := e.source
  target := ((((↑) : Cstar → ℂ) ⁻¹' e.baseSet) : Set Cstar) ×ˢ (Set.univ : Set ℤ)
  baseSet := (((↑) : Cstar → ℂ) ⁻¹' e.baseSet : Set Cstar)
  open_baseSet := e.open_baseSet.preimage continuous_subtype_val
  source_eq := by
    ext x
    simp [e.source_eq, CSexpCstar]
  target_eq := by
    rfl
  proj_toFun := by
    intro p hp
    rfl
  map_source' := by
    intro x hx
    have hx_target : e x ∈ e.target := e.map_source hx
    have hx_base : (e x).1 ∈ e.baseSet := by
      simpa [e.target_eq] using hx_target
    have hproj : (e x).1 = CSexp x := e.proj_toFun x hx
    refine ⟨?_, trivial⟩
    simpa [hproj] using hx_base
  map_target' := by
    intro x hx
    have hx' : ((x.1 : ℂ), x.2) ∈ e.target := by
      simpa [e.target_eq] using hx
    simpa using e.map_target hx'
  continuousOn_toFun := by
    rw [continuousOn_iff_continuous_restrict]
    have hfst : Continuous fun x : e.source => (⟨CSexp x, by
        simp [Cstar, CSexp, Complex.exp_ne_zero]⟩ : Cstar) :=
      Continuous.subtype_mk (Contexp.comp continuous_subtype_val) fun x => by
        simp [Cstar, CSexp, Complex.exp_ne_zero]
    have hecont : Continuous fun x : e.source => e x :=
      continuousOn_iff_continuous_restrict.mp e.continuousOn_toFun
    have hsnd : Continuous fun x : e.source => (e x).2 :=
      continuous_snd.comp hecont
    exact hfst.prodMk hsnd
  continuousOn_invFun := by
    rw [continuousOn_iff_continuous_restrict]
    have hecont : Continuous fun x : e.target => e.invFun x :=
      continuousOn_iff_continuous_restrict.mp e.continuousOn_invFun
    have hmap : Continuous fun x : ((((↑) : Cstar → ℂ) ⁻¹' e.baseSet : Set Cstar) ×ˢ (Set.univ : Set ℤ)) =>
        (⟨((x.1.1 : ℂ), x.1.2), by
          rw [e.target_eq]
          exact ⟨x.2.1, trivial⟩⟩ : e.target) := by
      apply Continuous.subtype_mk
      · have hfst : Continuous fun x : ((((↑) : Cstar → ℂ) ⁻¹' e.baseSet : Set Cstar) ×ˢ (Set.univ : Set ℤ)) =>
            (x.1.1 : ℂ) :=
          continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val)
        have hsnd : Continuous fun x : ((((↑) : Cstar → ℂ) ⁻¹' e.baseSet : Set Cstar) ×ˢ (Set.univ : Set ℤ)) =>
            x.1.2 :=
          continuous_snd.comp continuous_subtype_val
        exact hfst.prodMk hsnd
    simpa [Set.restrict] using hecont.comp hmap
  left_inv' := by
    intro x hx
    change e.invFun (CSexp x, (e x).2) = x
    rw [← e.proj_toFun x hx]
    exact e.left_inv hx
  right_inv' := by
    intro x hx
    have hx' : ((x.1 : ℂ), x.2) ∈ e.target := by
      simpa [e.target_eq] using hx
    have hsrc : e.invFun ((x.1 : ℂ), x.2) ∈ e.source := e.map_target hx'
    have hright : e (e.invFun ((x.1 : ℂ), x.2)) = ((x.1 : ℂ), x.2) := e.right_inv hx'
    apply Prod.ext
    · apply Subtype.ext
      have hproj :
          (e (e.invFun ((x.1 : ℂ), x.2))).1 = CSexp (e.invFun ((x.1 : ℂ), x.2)) :=
        e.proj_toFun _ hsrc
      have hfst : (e (e.invFun ((x.1 : ℂ), x.2))).1 = (x.1 : ℂ) :=
        congrArg Prod.fst hright
      exact hproj.symm.trans hfst
    · simpa using congrArg Prod.snd hright
  open_source := e.open_source
  open_target := by
    simpa [Set.top_eq_univ] using (e.open_baseSet.preimage continuous_subtype_val).prod isOpen_univ

/-%%
\begin{proof}\uses{trivialization, CSexpCstar}\leanok
Because $CSexp(z)\neq 0$ for every $z\in \C$, the first coordinate of the old
trivialization already lands in $Cstar$. Thus we may keep the same source and inverse map,
replace the base by $U\cap Cstar$, and regard the target as $(U\cap Cstar)\times \Z$.
All the axioms of a trivialization are inherited from those of $e$.
\end{proof}
%%-/

/-%%
\begin{corollary}\label{trivOverTCstar}\lean{trivOverTCstar}\leanok
There is a trivialization of $CSexpCstar$ over $T$, viewed as a subset of $Cstar$.
\end{corollary}
%%-/

noncomputable def trivOverTCstar : Trivialization ℤ CSexpCstar :=
  trivializationCstar trivOverT

/-%%
\begin{proof}\uses{splitPlane_subset_Cstar, trivializationCstar, trivOverT}\leanok
By Proposition~\ref{trivOverT}, $CSexp$ is trivial over $T$.
Since $T\subset Cstar$ by Lemma~\ref{splitPlane_subset_Cstar},
Lemma~\ref{trivializationCstar} turns this into a trivialization of $CSexpCstar$
over $T$ viewed inside $Cstar$.
\end{proof}
%%-/

/-%%
\begin{corollary}\label{trivOverTprimeCstar}\lean{trivOverTprimeCstar}\leanok
There is a trivialization of $CSexpCstar$ over $T'$, viewed as a subset of $Cstar$.
\end{corollary}
%%-/

noncomputable def trivOverTprimeCstar : Trivialization ℤ CSexpCstar :=
  trivializationCstar trivOverTprime.1

/-%%
\begin{proof}\uses{TprimeDef_subset_Cstar, trivializationCstar, trivOverTprime}\leanok
By Corollary~\ref{trivOverTprime}, $CSexp$ is trivial over $T'$.
Since $T'\subset Cstar$ by Lemma~\ref{TprimeDef_subset_Cstar},
Lemma~\ref{trivializationCstar} turns this into a trivialization of $CSexpCstar$
over $T'$ viewed inside $Cstar$.
\end{proof}
%%-/

/-%%
\begin{lemma}\label{trivOverTCstar_baseSet}\lean{trivOverTCstar_baseSet}\leanok
The base of the trivialization of Corollary~\ref{trivOverTCstar} is exactly $T$,
viewed as a subset of $Cstar$.
\end{lemma}
%%-/

@[simp] theorem trivOverTCstar_baseSet :
    trivOverTCstar.baseSet = (((↑) : Cstar → ℂ) ⁻¹' splitPlane : Set Cstar) :=
  rfl

/-%%
\begin{proof}\uses{trivOverTCstar}\leanok
This is immediate from the construction of Corollary~\ref{trivOverTCstar}.
\end{proof}
%%-/

/-%%
\begin{lemma}\label{trivOverTprimeCstar_baseSet}\lean{trivOverTprimeCstar_baseSet}\leanok
The base of the trivialization of Corollary~\ref{trivOverTprimeCstar} is exactly $T'$,
viewed as a subset of $Cstar$.
\end{lemma}
%%-/

@[simp] theorem trivOverTprimeCstar_baseSet :
    trivOverTprimeCstar.baseSet = (((↑) : Cstar → ℂ) ⁻¹' TprimeDef : Set Cstar) := by
  simp [trivOverTprimeCstar, trivializationCstar, trivOverTprime_baseSet]

/-%%
\begin{proof}\uses{trivOverTprimeCstar}\leanok
This is immediate from the construction of Corollary~\ref{trivOverTprimeCstar}.
\end{proof}
%%-/

/-%%
\begin{lemma}\label{CSexpCstar_isCoveringMap}\lean{CSexpCstar_isCoveringMap}\leanok
The map $CSexpCstar\colon \C\to Cstar$ is a covering map.
\end{lemma}
%%-/

theorem CSexpCstar_isCoveringMap : IsCoveringMap CSexpCstar := by
  intro x
  have hx : (x : ℂ) ∈ splitPlane ∪ TprimeDef := by
    have hxC : (x : ℂ) ∈ Cstar := x.property
    simp [TcupTprimeCstar, x.property]
  rcases hx with hs | ht
  · exact IsEvenlyCovered.to_isEvenlyCovered_preimage
      ⟨inferInstance, trivOverTCstar, by simpa [trivOverTCstar_baseSet] using hs⟩
  · exact IsEvenlyCovered.to_isEvenlyCovered_preimage
      ⟨inferInstance, trivOverTprimeCstar, by simpa [trivOverTprimeCstar_baseSet] using ht⟩

/-%%
\begin{proof}\uses{CSexpCstar, TcupTprimeCstar, trivOverTCstar, trivOverTprimeCstar, trivOverTCstar_baseSet, trivOverTprimeCstar_baseSet}\leanok
By Corollary~\ref{TcupTprimeCstar}, every point of $Cstar$ lies in $T$ or in $T'$.
By Corollaries~\ref{trivOverTCstar} and \ref{trivOverTprimeCstar}, together with
Lemmas~\ref{trivOverTCstar_baseSet} and \ref{trivOverTprimeCstar_baseSet},
these two sets are bases of trivializations for $CSexpCstar$.
Hence every point of $Cstar$ has an evenly covered neighborhood, so
$CSexpCstar$ is a covering map.
\end{proof}
%%-/

/-%%

\begin{corollary}\label{expUPL}\lean{expUPL}\leanok
Given $a,b\in \R$ with $a < b$, a path $\omega\colon [ a , b]\to \C $ with $\omega(t)\not=0$ for all $t\in [ a, b]$, and
$\tilde a_0\in CSexp^{-1}(\omega(a))$, there is a unique map
$\tilde\omega\colon [ a, b ]\to \C$ with $\tilde\omega(a)=\tilde a_0$ and $exp(\tilde\omega)=\omega$.
\end{corollary}
%%-/

theorem expUPL {a b : ℝ} (hab : a < b) (ω : C(Set.Icc a b, Cstar)) (z0 : ℂ)
    (hz0 : CSexp z0 = (ω ⟨a, ⟨le_rfl, hab.le⟩⟩ : ℂ)) :
    ∃! tildeω : C(Set.Icc a b, ℂ),
      (∀ t, CSexp (tildeω t) = (ω t : ℂ)) ∧ tildeω ⟨a, ⟨le_rfl, hab.le⟩⟩ = z0 := by
  let e := iccHomeoI a b hab
  let γ : C(↥(Set.Icc (0 : ℝ) 1), Cstar) :=
    ⟨fun t => ω (e.symm t), ω.continuous.comp e.symm.continuous⟩
  have hleft : e.symm 0 = ⟨a, ⟨le_rfl, hab.le⟩⟩ := by
    apply Subtype.ext
    simp [e]
  have hright : e ⟨a, ⟨le_rfl, hab.le⟩⟩ = 0 := by
    apply Subtype.ext
    simp [e]
  have hγ0 : γ 0 = CSexpCstar z0 := by
    apply Subtype.ext
    simpa [γ, hleft, CSexpCstar] using hz0.symm
  let Γ := CSexpCstar_isCoveringMap.liftPath γ z0 hγ0
  refine ⟨⟨fun t => Γ (e t), Γ.continuous.comp e.continuous⟩, ?_, ?_⟩
  · constructor
    · intro t
      have hΓ :=
        congrFun (CSexpCstar_isCoveringMap.liftPath_lifts (γ := γ) (e := z0) (γ_0 := hγ0)) (e t)
      simpa [γ, e, CSexpCstar] using congrArg Subtype.val hΓ
    · simpa [hright] using
        (CSexpCstar_isCoveringMap.liftPath_zero (γ := γ) (e := z0) (γ_0 := hγ0))
  · intro tildeω htilde
    rcases htilde with ⟨hlift, h0⟩
    let Γ' : C(↥(Set.Icc (0 : ℝ) 1), ℂ) :=
      ⟨fun t => tildeω (e.symm t), tildeω.continuous.comp e.symm.continuous⟩
    have hΓ' : Γ' = CSexpCstar_isCoveringMap.liftPath γ z0 hγ0 := by
      apply (CSexpCstar_isCoveringMap.eq_liftPath_iff'
        (γ := γ) (e := z0) (γ_0 := hγ0) (Γ := Γ')).2
      constructor
      · ext t
        change CSexp (tildeω (e.symm t)) = (ω (e.symm t) : ℂ)
        exact hlift (e.symm t)
      · change tildeω (e.symm 0) = z0
        simpa [hleft] using h0
    ext t
    have hval := congrFun (congrArg DFunLike.coe hΓ') (e t)
    simpa [Γ', e] using hval

/-%%

\begin{proof}\uses{CSexpCstar, CSexpCstar_coe, CSexpCstar_isCoveringMap}\leanok
By Lemma~\ref{CSexpCstar_isCoveringMap}, the codomain-restricted exponential
$CSexpCstar\colon \C\to Cstar$ is a covering map.
Therefore the standard path-lifting theorem for covering maps yields a unique lift of $\omega$
starting at $\tilde a_0$.
Finally, Lemma~\ref{CSexpCstar_coe} says that forgetting the codomain restriction turns the
identity $CSexpCstar\circ\tilde\omega=\omega$ into $CSexp\circ\tilde\omega=\omega$,
which is exactly the desired conclusion.
\end{proof}
%%-/

/-%%

\begin{corollary}\label{expHLP}\lean{expHLP}\leanok
Let $A$ be a topological space, let $H\colon [0,1]\times A\to Cstar$ be continuous, and let
$f\colon A\to \C$ be continuous. Assume that
\[
CSexp(f(a))=H(0,a)
\]
for all $a\in A$. Then there is a unique continuous map
\[
\tilde H\colon [0,1]\times A\to \C
\]
such that $\tilde H(0,a)=f(a)$ for all $a\in A$ and
$CSexp(\tilde H(t,a))=H(t,a)$ for all $(t,a)\in [0,1]\times A$.
\end{corollary}
%%-/

theorem expHLP {A : Type*} [TopologicalSpace A]
    (H : C(↥(Set.Icc (0 : ℝ) 1) × A, Cstar)) (f : C(A, ℂ))
    (h0 : ∀ a, CSexp (f a) = (H (0, a) : ℂ)) :
    ∃! H' : C(↥(Set.Icc (0 : ℝ) 1) × A, ℂ),
      (∀ x, CSexp (H' x) = (H x : ℂ)) ∧ ∀ a, H' (0, a) = f a := by
  have h0' : ∀ a, H (0, a) = CSexpCstar (f a) := by
    intro a
    apply Subtype.ext
    simpa [CSexpCstar] using (h0 a).symm
  refine ⟨CSexpCstar_isCoveringMap.liftHomotopy H f h0', ?_, ?_⟩
  · constructor
    · intro x
      have hx :=
        congrFun (CSexpCstar_isCoveringMap.liftHomotopy_lifts (H := H) (f := f) (H_0 := h0')) x
      simpa [CSexpCstar] using congrArg Subtype.val hx
    · intro a
      simpa using
        (CSexpCstar_isCoveringMap.liftHomotopy_zero (H := H) (f := f) (H_0 := h0') a)
  · intro H' hH'
    rcases hH' with ⟨hH'lifts, hH'zero⟩
    exact (CSexpCstar_isCoveringMap.eq_liftHomotopy_iff'
      (H := H) (f := f) (H_0 := h0') (H' := H')).2
      ⟨by
          ext x
          simpa [Function.comp, CSexpCstar] using hH'lifts x,
        hH'zero⟩

/-%%
\begin{proof}\uses{CSexpCstar, CSexpCstar_coe, CSexpCstar_isCoveringMap}\leanok
By Lemma~\ref{CSexpCstar_isCoveringMap}, the map
$CSexpCstar\colon \C\to Cstar$ is a covering map.
Hence the general homotopy lifting theorem for covering maps gives a unique lift
$\tilde H$ of the homotopy $H$ starting from the prescribed map $f$ at time $0$.
Finally, Lemma~\ref{CSexpCstar_coe} identifies the equality
$CSexpCstar\circ \tilde H=H$ with the desired equality
$CSexp\circ \tilde H=H$ after forgetting that the codomain is $Cstar$.
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

\begin{definition}\label{homotopyloop}\lean{homotopyloop}\uses{loop}\leanok
A homotopy of loops is a one parameter family $\Omega\colon [a, b]\times [0, 1]\to X$ with
$\Omega|_{[a, b]\times\{s\}}$
a loop for all $s\in [0, 1]$. A homotopy of loops based at $x_0$ is a one parameter family
indexed by $[0, 1]$ of loops based at $x_0$.
\end{definition}
%%-/

def homotopyloop {X : Type*} [TopologicalSpace X] {a b : ℝ} (hab : a ≤ b)
    (H : C(Set.Icc a b × Set.Icc (0 : ℝ) 1, X)) : Prop :=
  ∀ s, H (⟨a, ⟨le_rfl, hab⟩⟩, s) = H (⟨b, ⟨hab, le_rfl⟩⟩, s)

/-%%

\begin{lemma}\label{existlift}\lean{existlift}\leanok
Let $\omega\colon [a, b]\to \C$ be a loop. Assume that $\omega(t)\in Cstar$ for all $t\in [a, b]$.
There is a lift of $\omega$ through $exp$.
\end{lemma}
%%-/

theorem existlift {a b : ℝ} (hab : a < b) (ω : C(Set.Icc a b, Cstar)) :
    ∃ tildeω : C(Set.Icc a b, ℂ), deflift CSexp (fun t => (ω t : ℂ)) tildeω := by
  let t0 : Set.Icc a b := ⟨a, ⟨le_rfl, hab.le⟩⟩
  have hsurj : Set.SurjOn CSexp Set.univ Cstar := expCP.2.2
  obtain ⟨z0, -, hz0⟩ : (ω t0 : ℂ) ∈ CSexp '' Set.univ := hsurj (ω t0).property
  rcases ExistsUnique.exists (expUPL hab ω z0 hz0) with ⟨tildeω, htilde⟩
  refine ⟨tildeω, ?_⟩
  refine ⟨tildeω.continuous, ?_⟩
  ext t
  exact htilde.1 t

/-%%

\begin{proof}\uses{deflift, expCP, expUPL}\leanok
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
  (tildeω : ℝ → ℂ) : ℂ :=
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
    (hω : loop a b ω)
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
\begin{proof}\uses{deflift, loop, periodicity, DefWNlift, ContinuousOn.coe, isConnected_range_of_continuousOn, Singleton_of_isConnected_SetInt}\leanok
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

 \begin{corollary}\label{constWNomega}\lean{constWNomega}\leanok
 Let $\omega\colon [ a, b]\to \C$ be a loop with $\omega(t)\in Cstar$ for all $t\in [ a, b]$.
 There is a lift $\tilde\omega\colon [ a, b]\to \C$ of $\omega$ through $CSexp$.
 There is a constant $w(\omega)\in \Z$ such that for every lift $\tilde\omega \colon [ a, b]\to \C$
 the winding number of  $\tilde\omega$ is $w(\omega)$.
 \end{corollary}
%%-/

theorem constWNomega {a b : ℝ} (hab : a < b) (ω : C(Set.Icc a b, Cstar))
    (hloop : ω ⟨a, ⟨le_rfl, hab.le⟩⟩ = ω ⟨b, ⟨hab.le, le_rfl⟩⟩) :
    ∃ k : ℤ, (∃ tildeω : C(Set.Icc a b, ℂ), deflift CSexp (fun t => (ω t : ℂ)) tildeω) ∧
      ∀ tildeω : C(Set.Icc a b, ℂ), deflift CSexp (fun t => (ω t : ℂ)) tildeω →
        (tildeω ⟨b, ⟨hab.le, le_rfl⟩⟩ - tildeω ⟨a, ⟨le_rfl, hab.le⟩⟩) / (2 * π * I) = k := by
  let a0 : Set.Icc a b := ⟨a, ⟨le_rfl, hab.le⟩⟩
  let b0 : Set.Icc a b := ⟨b, ⟨hab.le, le_rfl⟩⟩
  obtain ⟨tildeω, hlift⟩ := existlift hab ω
  have htilde : (∀ t, CSexp (tildeω t) = (ω t : ℂ)) ∧ tildeω a0 = tildeω a0 := by
    constructor
    · intro t
      simpa [Function.comp] using congrFun hlift.2 t
    · rfl
  have hz0 : CSexp (tildeω a0) = (ω a0 : ℂ) := by
    simpa [Function.comp] using congrFun hlift.2 a0
  have hloop' : (ω b0 : ℂ) = (ω a0 : ℂ) := by
    simpa [a0, b0] using congrArg Subtype.val hloop.symm
  have hper : CSexp (tildeω b0) = CSexp (tildeω a0) := by
    calc
      CSexp (tildeω b0) = (ω b0 : ℂ) := by simpa [Function.comp] using congrFun hlift.2 b0
      _ = (ω a0 : ℂ) := hloop'
      _ = CSexp (tildeω a0) := by simpa [Function.comp] using (congrFun hlift.2 a0).symm
  obtain ⟨k, hk⟩ := (periodicity (tildeω b0) (tildeω a0)).1 hper
  refine ⟨k, ⟨tildeω, hlift⟩, ?_⟩
  intro tildeω' hlift'
  have hbase : (tildeω b0 - tildeω a0) / (2 * π * I) = k := by
    rw [hk]
    ring_nf
    have : I ≠ 0 := by norm_num
    have : (π : ℂ) ≠ 0 := by
      norm_cast
      exact Real.pi_ne_zero
    field_simp
    rw [show k * π * I * I = - (k * π) by ring_nf; norm_cast; simp]
    norm_cast
    ring_nf
  have haeq : CSexp (tildeω' a0) = CSexp (tildeω a0) := by
    calc
      CSexp (tildeω' a0) = (ω a0 : ℂ) := by simpa [Function.comp] using congrFun hlift'.2 a0
      _ = CSexp (tildeω a0) := by simpa [Function.comp] using (congrFun hlift.2 a0).symm
  obtain ⟨n, hn⟩ := (periodicity (tildeω' a0) (tildeω a0)).1 haeq
  let shifted : C(Set.Icc a b, ℂ) :=
    ⟨fun t => tildeω' t - n * (2 * π * I), tildeω'.continuous.sub continuous_const⟩
  have hshifted : (∀ t, CSexp (shifted t) = (ω t : ℂ)) ∧ shifted a0 = tildeω a0 := by
    constructor
    · intro t
      have hperiod :
          CSexp (shifted t) = CSexp (tildeω' t) := by
        apply (periodicity _ _).2
        refine ⟨-n, by
          simp [shifted]
          ring⟩
      exact hperiod.trans (by simpa [Function.comp] using congrFun hlift'.2 t)
    · calc
        shifted a0 = tildeω' a0 - n * (2 * π * I) := by rfl
        _ = tildeω a0 := by rw [hn]; ring
  have huniq : shifted = tildeω := by
    exact ExistsUnique.unique (expUPL hab ω (tildeω a0) hz0) hshifted htilde
  have hshift_eq : ∀ t, tildeω' t = tildeω t + n * (2 * π * I) := by
    intro t
    have ht : shifted t = tildeω t := by
      have hfun := congrArg DFunLike.coe huniq
      simpa using congrFun hfun t
    calc
      tildeω' t = (tildeω' t - n * (2 * π * I)) + n * (2 * π * I) := by ring
      _ = shifted t + n * (2 * π * I) := by rfl
      _ = tildeω t + n * (2 * π * I) := by rw [ht]
  calc
    (tildeω' b0 - tildeω' a0) / (2 * π * I)
        = ((tildeω b0 + n * (2 * π * I)) - (tildeω a0 + n * (2 * π * I))) / (2 * π * I) := by
            rw [hshift_eq b0, hshift_eq a0]
    _ = (tildeω b0 - tildeω a0) / (2 * π * I) := by ring
    _ = k := hbase

/-%%

 \begin{proof}\uses{existlift, periodicity, expUPL}\leanok
 By Lemma~\ref{existlift}, there is at least one lift $\tilde\omega$ of $\omega$ through $CSexp$.
 Since $\omega(a)=\omega(b)$ and $CSexp(\tilde\omega(a))=\omega(a)$,
 $CSexp(\tilde\omega(b))=\omega(b)$, Lemma~\ref{periodicity} implies that
 $\tilde\omega(b)-\tilde\omega(a)=2\pi k I$ for some $k\in \Z$.
 Hence the winding number of this lift is $k$.

 If $\tilde\omega'$ is any other lift, then again by Lemma~\ref{periodicity} the values
 $\tilde\omega'(a)$ and $\tilde\omega(a)$ differ by an integral multiple of $2\pi I$.
 After subtracting this multiple from $\tilde\omega'$, we obtain another lift of $\omega$
 with the same initial value as $\tilde\omega$.
 By Corollary~\ref{expUPL}, lifts with the same initial value are equal.
 Therefore $\tilde\omega'$ differs from $\tilde\omega$ by the same constant period
 at every point of $[a,b]$, so the endpoint difference
 $\tilde\omega'(b)-\tilde\omega'(a)$ equals $\tilde\omega(b)-\tilde\omega(a)$.
 Thus every lift has the same winding number $k$.
 \end{proof}
%%-/

/-%%

 \begin{definition}\label{WNloop}\lean{WNloop}\uses{constWNomega}\leanok
 Suppose that $\omega\colon [ a, b ]\to \C$ is a loop with $\omega(t)\in Cstar$ for all
 $t\in [ a, b ]$.
 Then the constant $w(\omega)$ given in Corollary~\ref{constWNomega} is the {\em winding number
 of $\omega$}.
 \end{definition}
%%-/

noncomputable def WNloop {a b : ℝ} (hab : a < b) (ω : C(Set.Icc a b, Cstar))
    (hloop : ω ⟨a, ⟨le_rfl, hab.le⟩⟩ = ω ⟨b, ⟨hab.le, le_rfl⟩⟩) : ℤ :=
  Classical.choose (constWNomega hab ω hloop)

/-%%

\begin{lemma}\label{WNloop_exists_lift}\lean{WNloop_exists_lift}\uses{constWNomega}\leanok
If $\omega$ is a loop in $Cstar$, then it admits a lift through $CSexp$.
\end{lemma}
%%-/

theorem WNloop_exists_lift {a b : ℝ} (hab : a < b) (ω : C(Set.Icc a b, Cstar))
    (hloop : ω ⟨a, ⟨le_rfl, hab.le⟩⟩ = ω ⟨b, ⟨hab.le, le_rfl⟩⟩) :
    ∃ tildeω : C(Set.Icc a b, ℂ), deflift CSexp (fun t => (ω t : ℂ)) tildeω :=
  (Classical.choose_spec (constWNomega hab ω hloop)).1

/-%%
\begin{proof}\uses{constWNomega}\leanok
This is one of the conclusions of Corollary~\ref{constWNomega}.
\end{proof}
%%-/

/-%%
\begin{lemma}\label{WNloop_eq_of_lift}\lean{WNloop_eq_of_lift}\uses{WNloop, constWNomega}\leanok
If $\tilde\omega$ is any lift of the loop $\omega$ through $CSexp$, then its winding number is
$w(\omega)$.
\end{lemma}
%%-/

theorem WNloop_eq_of_lift {a b : ℝ} (hab : a < b) (ω : C(Set.Icc a b, Cstar))
    (hloop : ω ⟨a, ⟨le_rfl, hab.le⟩⟩ = ω ⟨b, ⟨hab.le, le_rfl⟩⟩)
    (tildeω : C(Set.Icc a b, ℂ)) (hlift : deflift CSexp (fun t => (ω t : ℂ)) tildeω) :
    (tildeω ⟨b, ⟨hab.le, le_rfl⟩⟩ - tildeω ⟨a, ⟨le_rfl, hab.le⟩⟩) / (2 * π * I) =
      WNloop hab ω hloop :=
  (Classical.choose_spec (constWNomega hab ω hloop)).2 tildeω hlift

/-%%
\begin{proof}\uses{WNloop, constWNomega}\leanok
By definition, $w(\omega)$ is the integer supplied by Corollary~\ref{constWNomega}.
That corollary also says that every lift of $\omega$ has winding number equal to this integer.
\end{proof}
%%-/

/-%%


\begin{lemma}\label{equalwinding}\lean{equalwinding}\leanok
If $\omega\colon [ a, b ]\to \C$ and $\omega'\colon [ a, b ]\to \C$
are loops with $\omega(t) , \omega'(t) \in Cstar$ for all $t\in [ a, b ]$
and if $H\colon [ a, b ]\times[ 0, 1 ]\to \C$ is a homotopy of loops from $\omega$ to $\omega'$
with $H(t,s)\in Cstar$ for all $t\in [ a, b ]$ and $s\in[ 0, 1 ]$, then $w(\omega)=w(\omega')$
\end{lemma}
%%-/

theorem equalwinding {a b : ℝ} (hab : a < b)
    (ω ω' : C(Set.Icc a b, Cstar))
    (hloop : ω ⟨a, ⟨le_rfl, hab.le⟩⟩ = ω ⟨b, ⟨hab.le, le_rfl⟩⟩)
    (hloop' : ω' ⟨a, ⟨le_rfl, hab.le⟩⟩ = ω' ⟨b, ⟨hab.le, le_rfl⟩⟩)
    (H : C(Set.Icc a b × Set.Icc (0 : ℝ) 1, Cstar))
    (hhom : homotopyloop hab.le H)
    (hzero : ∀ t, H (t, 0) = ω t)
    (hone : ∀ t, H (t, 1) = ω' t) :
    WNloop hab ω hloop = WNloop hab ω' hloop' := by
  let a0 : Set.Icc a b := ⟨a, ⟨le_rfl, hab.le⟩⟩
  let b0 : Set.Icc a b := ⟨b, ⟨hab.le, le_rfl⟩⟩
  let Hswap : C(Set.Icc (0 : ℝ) 1 × Set.Icc a b, Cstar) :=
    ⟨fun x => H (x.2, x.1), H.continuous.comp (continuous_snd.prodMk continuous_fst)⟩
  obtain ⟨tildeω, hlift⟩ := WNloop_exists_lift hab ω hloop
  have hHswap0 : ∀ t, CSexp (tildeω t) = (Hswap (0, t) : ℂ) := by
    intro t
    calc
      CSexp (tildeω t) = (ω t : ℂ) := by
        simpa [Function.comp] using congrFun hlift.2 t
      _ = (H (t, 0) : ℂ) := by
        simpa using congrArg Subtype.val (hzero t).symm
      _ = (Hswap (0, t) : ℂ) := by
        rfl
  obtain ⟨tildeH, htildeH⟩ := ExistsUnique.exists (expHLP Hswap tildeω hHswap0)
  have htildeH_lifts : ∀ x, CSexp (tildeH x) = (Hswap x : ℂ) := htildeH.1
  have htildeH_zero : ∀ t, tildeH (0, t) = tildeω t := htildeH.2
  let μ : C(Set.Icc (0 : ℝ) 1, Cstar) :=
    ⟨fun s => H (a0, s), H.continuous.comp (continuous_const.prodMk continuous_id)⟩
  let μa : C(Set.Icc (0 : ℝ) 1, ℂ) :=
    ⟨fun s => tildeH (s, a0), tildeH.continuous.comp (continuous_id.prodMk continuous_const)⟩
  let μb : C(Set.Icc (0 : ℝ) 1, ℂ) :=
    ⟨fun s => tildeH (s, b0), tildeH.continuous.comp (continuous_id.prodMk continuous_const)⟩
  have hμa : (∀ s, CSexp (μa s) = (μ s : ℂ)) ∧ μa 0 = tildeω a0 := by
    constructor
    · intro s
      simpa [μa, μ, Hswap] using htildeH_lifts (s, a0)
    · simpa [μa] using htildeH_zero a0
  have hμb : (∀ s, CSexp (μb s) = (μ s : ℂ)) ∧ μb 0 = tildeω b0 := by
    constructor
    · intro s
      calc
        CSexp (μb s) = (H (b0, s) : ℂ) := by
          simpa [μb, Hswap] using htildeH_lifts (s, b0)
        _ = (H (a0, s) : ℂ) := by
          simpa [a0, b0] using congrArg Subtype.val (hhom s).symm
        _ = (μ s : ℂ) := by
          rfl
    · simpa [μb] using htildeH_zero b0
  have hstart : CSexp (tildeω b0) = CSexp (tildeω a0) := by
    calc
      CSexp (tildeω b0) = (ω b0 : ℂ) := by
        simpa [Function.comp] using congrFun hlift.2 b0
      _ = (ω a0 : ℂ) := by
        simpa [a0, b0] using congrArg Subtype.val hloop.symm
      _ = CSexp (tildeω a0) := by
        simpa [Function.comp] using (congrFun hlift.2 a0).symm
  obtain ⟨n, hn⟩ := (periodicity (tildeω b0) (tildeω a0)).1 hstart
  let shiftedμa : C(Set.Icc (0 : ℝ) 1, ℂ) :=
    ⟨fun s => μa s + n * (2 * π * I), μa.continuous.add continuous_const⟩
  have hshiftedμa : (∀ s, CSexp (shiftedμa s) = (μ s : ℂ)) ∧ shiftedμa 0 = μb 0 := by
    constructor
    · intro s
      have hperiod : CSexp (shiftedμa s) = CSexp (μa s) := by
        exact (periodicity (shiftedμa s) (μa s)).2 ⟨n, by rfl⟩
      exact hperiod.trans (hμa.1 s)
    · calc
        shiftedμa 0 = μa 0 + n * (2 * π * I) := by rfl
        _ = tildeω a0 + n * (2 * π * I) := by rw [hμa.2]
        _ = tildeω b0 := by rw [hn]
        _ = μb 0 := by rw [hμb.2]
  have hμb_self : (∀ s, CSexp (μb s) = (μ s : ℂ)) ∧ μb 0 = μb 0 := by
    exact ⟨hμb.1, rfl⟩
  have huniq : shiftedμa = μb := by
    exact ExistsUnique.unique
      (expUPL (show (0 : ℝ) < 1 by norm_num) μ (μb 0) (hμb.1 0))
      hshiftedμa hμb_self
  have hshift_eq : ∀ s, μb s = μa s + n * (2 * π * I) := by
    intro s
    have hfun := congrArg DFunLike.coe huniq
    simpa [shiftedμa] using (congrFun hfun s).symm
  let tildeω' : C(Set.Icc a b, ℂ) :=
    ⟨fun t => tildeH (1, t), tildeH.continuous.comp (continuous_const.prodMk continuous_id)⟩
  have hlift' : deflift CSexp (fun t => (ω' t : ℂ)) tildeω' := by
    refine ⟨tildeω'.continuous, ?_⟩
    ext t
    calc
      CSexp (tildeω' t) = (H (t, 1) : ℂ) := by
        simpa [tildeω', Hswap] using htildeH_lifts (1, t)
      _ = (ω' t : ℂ) := by
        simpa using congrArg Subtype.val (hone t)
  have hwind :
      (tildeω' b0 - tildeω' a0) / (2 * π * I) =
        (tildeω b0 - tildeω a0) / (2 * π * I) := by
    have hdiff : tildeω' b0 - tildeω' a0 = tildeω b0 - tildeω a0 := by
      calc
        tildeω' b0 - tildeω' a0 = μb 1 - μa 1 := by rfl
        _ = μb 0 - μa 0 := by
          rw [hshift_eq 1, hshift_eq 0]
          ring
        _ = tildeω b0 - tildeω a0 := by
          rw [hμb.2, hμa.2]
    rw [hdiff]
  have hcomplex : (WNloop hab ω hloop : ℂ) = (WNloop hab ω' hloop' : ℂ) := by
    calc
    (WNloop hab ω hloop : ℂ) = (tildeω b0 - tildeω a0) / (2 * π * I) := by
      symm
      exact WNloop_eq_of_lift hab ω hloop tildeω hlift
    _ = (tildeω' b0 - tildeω' a0) / (2 * π * I) := by
      symm
      exact hwind
    _ = (WNloop hab ω' hloop' : ℂ) := by
      exact WNloop_eq_of_lift hab ω' hloop' tildeω' hlift'
  exact_mod_cast hcomplex

/-%%

\begin{proof}\uses{homotopyloop, WNloop_exists_lift, WNloop_eq_of_lift, expHLP, expUPL, periodicity}\leanok
Choose a lift $\tilde\omega$ of $\omega$ using Lemma~\ref{WNloop_exists_lift}.
Applying Corollary~\ref{expHLP} to the homotopy $H$ and the initial lift $\tilde\omega$,
we obtain a lift $\tilde H$ of the whole homotopy.

Now consider the two boundary paths
\[
s\mapsto \tilde H(a,s), \qquad s\mapsto \tilde H(b,s).
\]
By Definition~\ref{homotopyloop}, the projected paths agree, because
$H(a,s)=H(b,s)$ for all $s$.
At time $s=0$, the starting points $\tilde H(a,0)$ and $\tilde H(b,0)$ differ by an integral
multiple of $2\pi I$ by Lemma~\ref{periodicity}, since $\omega(a)=\omega(b)$.
Shift the first boundary lift by this constant period. The shifted path is still a lift of the
same projected path, and now it has the same initial value as the second boundary lift.
By Corollary~\ref{expUPL}, these two lifts are equal. Therefore
$\tilde H(b,s)-\tilde H(a,s)$ is independent of $s$.

Evaluating at $s=0$ and $s=1$ shows that
\[
\tilde H(b,1)-\tilde H(a,1)=\tilde H(b,0)-\tilde H(a,0).
\]
But the slice $t\mapsto \tilde H(t,0)$ is a lift of $\omega$, and the slice
$t\mapsto \tilde H(t,1)$ is a lift of $\omega'$.
Lemma~\ref{WNloop_eq_of_lift} therefore identifies the two corresponding endpoint quotients with
$w(\omega)$ and $w(\omega')$, so these winding numbers are equal.
\end{proof}
%%-/

/-%%

\begin{corollary}\label{constpath}\lean{constpath}\leanok
Suppose that $\omega\colon [ a, b ]\to \C$ is a loop and $\omega(t)\in Cstar$
for all $t\in [ a, b ]$.
Suppose that $H\colon [ a, b ]\times [ 0, 1 ]\to \C$ is a  homotopy of loops
from $\omega$  to a constant loop
and $H(t,s)\in Cstar$ for all $(t,s)\in [ a, b ]\times [ 0, 1 ]$. Then
the winding number of $\omega$ is zero.
\end{corollary}
%%-/

theorem constpath {a b : ℝ} (hab : a < b) (ω : C(Set.Icc a b, Cstar))
    (hloop : ω ⟨a, ⟨le_rfl, hab.le⟩⟩ = ω ⟨b, ⟨hab.le, le_rfl⟩⟩)
    (H : C(Set.Icc a b × Set.Icc (0 : ℝ) 1, Cstar))
    (hhom : homotopyloop hab.le H)
    (hzero : ∀ t, H (t, 0) = ω t)
    (c : Cstar)
    (hone : ∀ t, H (t, 1) = c) :
    WNloop hab ω hloop = 0 := by
  let ωconst : C(Set.Icc a b, Cstar) := ContinuousMap.const _ c
  have hloopconst :
      ωconst ⟨a, ⟨le_rfl, hab.le⟩⟩ = ωconst ⟨b, ⟨hab.le, le_rfl⟩⟩ := by
    rfl
  have hequal : WNloop hab ω hloop = WNloop hab ωconst hloopconst := by
    apply equalwinding hab ω ωconst hloop hloopconst H hhom hzero
    intro t
    simpa [ωconst] using hone t
  have hsurj : Set.SurjOn CSexp Set.univ Cstar := expCP.2.2
  obtain ⟨z0, -, hz0⟩ : (c : ℂ) ∈ CSexp '' Set.univ := hsurj c.property
  have hconstlift :
      deflift CSexp (fun t => (ωconst t : ℂ)) (ContinuousMap.const _ z0) := by
    refine ⟨(ContinuousMap.const _ z0).continuous, ?_⟩
    ext t
    simpa [ωconst] using hz0
  have hconstcomplex : (WNloop hab ωconst hloopconst : ℂ) = 0 := by
    have hq :
        (0 : ℂ) = WNloop hab ωconst hloopconst := by
      simpa [ωconst] using
        (WNloop_eq_of_lift hab ωconst hloopconst (ContinuousMap.const _ z0) hconstlift)
    simpa using hq.symm
  have hconst : WNloop hab ωconst hloopconst = 0 := by
    exact_mod_cast hconstcomplex
  exact hequal.trans hconst

/-%%

\begin{proof}\uses{equalwinding, expCP, WNloop_eq_of_lift}\leanok
By Lemma~\ref{equalwinding}, the winding number of $\omega$ is equal to the winding number of a
constant loop.
Choose a point $z_0\in \C$ with $CSexp(z_0)=c$; this is possible by Corollary~\ref{expCP}.
Then the constant map $t\mapsto z_0$ is a lift of the constant loop at $c$ through $CSexp$.
Its endpoint difference is zero, so Lemma~\ref{WNloop_eq_of_lift} shows that the winding number of
the constant loop is zero.
\end{proof}
%%-/

/-%%

\begin{definition}\label{DefS1loop}\lean{DefS1loop}\leanok
Given a map of the circle $\psi\colon S^1\to X$ the associated loop is
$\omega\colon [ 0, 2\pi  ]\to X$ defined by $\omega(t)=\psi(CSexp(it))$.
\end{definition}
%%-/

/-%%

\begin{lemma}\label{DefS1loop_loop}\lean{DefS1loop_loop}\uses{DefS1loop}\leanok
For every circle map $\psi$, the associated path begins and ends at the same point, so it is a
loop.
\end{lemma}

%%-/

/-%%

\begin{proof}\uses{DefS1loop}\leanok
By Definition~\ref{DefS1loop}, the endpoints of the associated path are
$\psi(CSexp(0))$ and $\psi(CSexp(2\pi i))$. Since $CSexp(0)=CSexp(2\pi i)=1$, these endpoints
agree.
\end{proof}

%%-/

/-%%

\begin{lemma}\label{sameImage}\lean{sameImage}\leanok
 Let $ρ : S^1→ \C$ be a map with $ρ(z)∈ Cstar$ for all $z∈ S^1$.
 Let $ω$ be the loop associated with $ρ$.
 Then the image of $ω$ is contained in $Cstar$.
\end{lemma}

%%-/

/-%%

\begin{proof}\uses{DefS1loop}\leanok
Let $ω \colon [ 0, 2\pi  ] \to \C$ be the loop associated to $ρ$.
Then by Definition~\ref{DefS1loop}, for every $t\in [0,2\pi]$ we have
$ω(t)=ρ(CSexp(it))\in Cstar$.
\end{proof}

%%-/


/-%%

\begin{definition}\label{DefWNS1}\lean{DefWNS1}\uses{DefS1loop, sameImage}\leanok
The winding number of a map $\rho\colon S^1\to \C$ with $\rho(z)\in Cstar$
for all $z\in S^1$  is the winding number of the associated loop.
\end{definition}
%%-/

/-%%

\begin{lemma}\label{constS1}\lean{constS1}\leanok
If $f\colon S^1\to \C$ is a constant map to a point $z\in Cstar$, then $w(f)=0$.
\end{lemma}

\begin{proof}\uses{DefS1loop, DefWNS1, constpath}\leanok
By Definition~\ref{DefS1loop} the loop associated with the constant map $f\colon S^1\to Cstar$
is a constant loop at a point of $Cstar$.
By Lemma~\ref{DefWNS1} the winding number of $f$ is equal to the winding number
of the constant loop at $f(S^1)\in Cstar$. By Lemma~\ref{constpath} this winding number is zero.
\end{proof}

%%-/


/-%%

\begin{lemma}\label{S1homotopy}\lean{S1homotopy}\leanok
Let $\psi, \psi'\colon S^1\to \C$ be maps and let $H : S^1\times I\to \C$ be a homotopy between them
whose image lies in  $Cstar$. Then the winding numbers of $\psi$ and $\psi'$ are equal.
\end{lemma}
%%-/

/-%%

\begin{proof}\uses{DefS1loop, equalwinding, DefWNS1}\leanok
Let $H\colon S^1\times I\to \C$ be a homotopy from $\psi$ to $\psi'$ whose image lies in $Cstar$.
Let $ω$ and $ω'$ be the loops associated to $ψ$ and $ψ'$ respectively.
Define $\hat H\colon [ 0, 2\pi  ]\times [ 0, 1 ]\to \C$ by
$\hat H(t,s)=H(CSexp(it),s)$. Then by Definition~\ref{DefS1loop} $\hat H$ is a homotopy from
the loop $\omega$ to the loop $\omega'$. The images of $H$ and $\hat H$ are the same, so the
image of $\hat H$ also lies in $Cstar$. By Lemma~\ref{equalwinding}, the winding numbers of
$\omega$ and $\omega'$ are equal. By Definition~\ref{DefWNS1}, this means that the winding
numbers of $ψ$ and $ψ'$ are equal.
\end{proof}
%%-/





/-%%

\begin{definition}\label{D2}\lean{D2}\leanok
Let $D^2=\{z\in \C : |z|\le 1\}$ be the closed unit disk.
\end{definition}
%%-/

/-%%

\begin{definition}\label{circleToD2}\lean{circleToD2}\uses{D2}\leanok
The canonical inclusion $S^1\hookrightarrow D^2$ sends a point of the unit circle to the same
complex number, now viewed as a point of the closed disk.
\end{definition}
%%-/

/-%%

\begin{definition}\label{zeroD2}\lean{zeroD2}\uses{D2}\leanok
Let $0_{D^2}$ denote the center of the closed unit disk.
\end{definition}
%%-/

/-%%

\begin{theorem}\label{boundsWN0}\lean{boundsWN0}\leanok
Let $\rho\colon S^1\to \C$ be a map with $\rho(z)\in Cstar$ for all $z\in S^1$.
Suppose there is a map $\hat f\colon D^2\to \C$ with $\hat f|_{S^1}=\rho$ and with
the image of $\hat f$ contained in $Cstar$. Then the winding $w(\rho)=0$.
\end{theorem}
%%-/

/-%%


\begin{proof}\uses{S1homotopy, constS1}\leanok
Define a continuous map $J\colon S^1\times [ 0,1 ]\to D^2$ by
$(z,t)\mapsto (1-t)z$. Then $\hat f\circ J(z,0)= \rho(z)$ and
$\hat f\circ J(z,1)=\hat f(0)$ for all $z\in S^1$.
This is a homotopy in $Cstar$ from $\rho$ to a constant map of $S^1\to Cstar$.
By Lemma~\ref{S1homotopy} the winding number of $\rho$ is equal to the winding number
of a constant map $S^1\to C\star$.
By Lemma~\ref{constS1}, the winding number of a constant
map $S^1\to \hat f(0)\in Cstar$ is zero.
\end{proof}

%%-/

/-%%


\section{Winding numbers at Infinity for complex polynomials}

%%-/

/-%%
\begin{definition}\label{monomialS1Map}\lean{monomialS1Map}\leanok
Given $\alpha_0\in \C^\times$, a natural number $k$, and $R>0$, let
$\psi_{\alpha_0,k,R}\colon S^1\to Cstar$ be the map
$\psi_{\alpha_0,k,R}(z)=\alpha_0(Rz)^k$.
\end{definition}
%%-/

/-%%
\begin{lemma}\label{zkWNk}\lean{zkWNk}\leanok
For any $\alpha_0\in \C$ and any $k\in \mathbb N$, define $\psi_{\alpha_0,k}\colon \C\to \C$ by
$\psi_{\alpha_0,k}(z)=\alpha_0 z^k$.
Then for any $R>0$, if $\alpha_0\not=0$, the winding number of the restriction of
$\psi_{\alpha_0,k}$ to the circle of radius $R$ is $k$.
\end{lemma}
%%-/

/-%%

\begin{proof}\uses{DefS1loop, multiplicativity, expCP, deflift, WNloop, DefWNS1}\leanok
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
\begin{lemma}\label{walkingdog}\lean{walkingdog}\leanok
Suppose that $\psi\colon S^1\to \C$ and $\psi'\colon S^1\to \C$ are maps
and for each $z\in S^1$, we have $|\psi(z)-\psi'(z)|<|\psi(z)|$. Then there is a homotopy
$H$ from $\psi$ to $\psi'$ whose image lies in $Cstar$.
\end{lemma}
%%-/

/-%%

\begin{proof}\leanok
Since for all $z\in S^1$, $|\psi(z)-\psi'(z)|<|\psi(z)|$, it follows that $|\psi(z)|>0$ and
$|\psi'(z)|>0$ for all $z\in S^1$.
Define a homotopy $H\colon S^1\times [ 0, 1 ]\to \C$ by
$H(z,t)=t\psi'(z)+(1-t)\psi(z)$.
$H(z,0)=\psi(z)$ and $H(z,1)=\psi'(z)$, so $H$ is a homotopy from $\psi$ to $\psi'$.

We establish that $H(z,t)\not= 0$. For all $z\in S^1$ and $t\in [ 0, 1 ]$ we have
$|\psi(z)-H(z,t)|=|(1-t)(\psi(z)-\psi'(z))|\le |\psi(z)-\psi'(z)|<|\psi(z)|$.
So $H(z,t)\not=0$ for all $z\in S^1$ and all $t\in[ 0, 1 ]$.

Consequently, $H$ is a homotopy $S^1\times [ 0 , 1 ]\to \C$ from $\psi$ to $\psi'$ whose image lies
in $Cstar$.
\end{proof}
%%-/

/-%%

\begin{corollary}\label{sameWN}\lean{sameWN}\leanok
Suppose that $\psi,\psi'\colon S^1\to \C$ satisfy $|\psi(z)-\psi'(z)|<|\psi(z)|$
for all $z\in S^1$. Then $\psi$ and $\psi'$ have the same winding number.
\end{corollary}

\begin{proof}\uses{walkingdog, S1homotopy}\leanok
By Lemma~\ref{walkingdog}, there is a homotopy $H$ from $\psi$ to $\psi'$ whose image lies in
$Cstar$.
Thus, by Lemma~\ref{S1homotopy}, $\psi$ and $\psi'$ have the same winding number.
\end{proof}
%%-/



/-%%

\begin{definition}\label{polyCircleMap}\lean{polyCircleMap}\leanok
If a polynomial $p$ has no zeros on the circle of radius $R$, let $f_{p,R}\colon S^1\to Cstar$
be the map $f_{p,R}(z)=p(Rz)$.
\end{definition}
%%-/

/-%%

\begin{definition}\label{polyDiskMap}\lean{polyDiskMap}\uses{D2}\leanok
If a polynomial $p$ has no zeros on the closed disk of radius $R$, let $F_{p,R}\colon D^2\to Cstar$
be the map $F_{p,R}(z)=p(Rz)$.
\end{definition}
%%-/

/-%%




\begin{lemma}\label{zkdominates}\lean{zkdominates}\leanok
Let $p(z)$ be a complex polynomial of degree $k$;  $p(z)=\sum_{i=0}^k\alpha_iz^{k-i}$ with
$\alpha_i\in \C$ and $\alpha_0\not= 0$.
For all $R$ sufficiently large $|\alpha_0|R^k>|\alpha_0z^k - p(z)|$ for any $z$ with $|z|=R$.
\end{lemma}
%%-/

/-%%

\begin{proof}\leanok
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

\begin{theorem}\label{WNthm}\lean{WNthm}\leanok
Let $p(z)$ be a complex polynomial of degree $k>0$ given by $p(z)=\sum_{i=0}^k\alpha_iz^{k-i}$ with
$α_i∈ℂ$ for all $i$ and $α_0\not= 0$. Then for $R$ sufficiently large,
 the map $f : S^1\to \C$ given by
$f(z)= p(R* z)$ for $z\in S^1$ has winding number $k$.
\end{theorem}


\begin{proof}\uses{zkWNk, zkdominates, sameWN}\leanok
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


\begin{theorem}\label{ExistRoot}\lean{ExistRoot}\leanok
Every complex polynomial of degree $k>0$ has a complex root.
\end{theorem}
%%-/

/-%%

\begin{proof}\uses{WNthm, boundsWN0}\leanok
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

local notation "I01" => Set.Icc (0 : ℝ) 1
local notation "I2π" => Set.Icc (0 : ℝ) (2 * π)

/-%%
\begin{definition}\label{DefS1loop}\lean{DefS1loop}\leanok
Given a map of the circle $\psi\colon S^1\to X$ the associated loop is
$\omega\colon [ 0, 2\pi  ]\to X$ defined by $\omega(t)=\psi(CSexp(it))$.
\end{definition}
%%-/

noncomputable def DefS1loop {X : Type*} [TopologicalSpace X] (ψ : C(Circle, X)) : C(I2π, X) :=
  ⟨fun t => ψ (Circle.exp t), ψ.continuous.comp (Circle.exp.continuous.comp continuous_subtype_val)⟩

/-%%
\begin{lemma}\label{DefS1loop_loop}\lean{DefS1loop_loop}\uses{DefS1loop}\leanok
The path associated with a circle map is a loop.
\end{lemma}
%%-/

theorem DefS1loop_loop {X : Type*} [TopologicalSpace X] (ψ : C(Circle, X)) :
    DefS1loop ψ ⟨0, ⟨le_rfl, Real.two_pi_pos.le⟩⟩ =
      DefS1loop ψ ⟨2 * π, ⟨Real.two_pi_pos.le, le_rfl⟩⟩ := by
  simp [DefS1loop, Circle.exp_two_pi]

/-%%
\begin{proof}\uses{DefS1loop}\leanok
By Definition~\ref{DefS1loop}, the endpoints of the path are
$\psi(CSexp(0))$ and $\psi(CSexp(2\pi i))$. Since both exponentials are equal to $1\in S^1$,
these two values coincide.
\end{proof}
%%-/

/-%%
\begin{lemma}\label{sameImage}\lean{sameImage}\uses{DefS1loop}\leanok
If $\rho\colon S^1\to \Cstar$, then the image of the associated loop is contained in $\Cstar$.
\end{lemma}
%%-/

theorem sameImage (ρ : C(Circle, Cstar)) :
    Set.range (fun t => (DefS1loop ρ t : ℂ)) ⊆ Cstar := by
  rintro z ⟨t, rfl⟩
  exact (DefS1loop ρ t).property

/-%%
\begin{proof}\uses{DefS1loop}\leanok
Every point on the associated loop has the form $\rho(CSexp(it))$ by
Definition~\ref{DefS1loop}. Since $\rho$ already takes values in $Cstar$, the whole image of the
loop lies in $Cstar$ as well.
\end{proof}
%%-/

/-%%
\begin{definition}\label{DefWNS1}\lean{DefWNS1}\uses{DefS1loop, sameImage}\leanok
The winding number of a map $\rho\colon S^1\to \Cstar$ is the winding number of the associated loop.
\end{definition}
%%-/

noncomputable def DefWNS1 (ρ : C(Circle, Cstar)) : ℤ :=
  WNloop Real.two_pi_pos (DefS1loop ρ) (DefS1loop_loop ρ)

/-%%
\begin{lemma}\label{constS1}\lean{constS1}\uses{DefS1loop, DefWNS1, constpath}\leanok
If $f\colon S^1\to \Cstar$ is constant, then its winding number is zero.
\end{lemma}
%%-/

theorem constS1 (c : Cstar) : DefWNS1 (ContinuousMap.const _ c : C(Circle, Cstar)) = 0 := by
  let H : C(I2π × I01, Cstar) := ContinuousMap.const _ c
  have hhom : homotopyloop Real.two_pi_pos.le H := by
    intro s
    rfl
  have hzero :
      ∀ t, H (t, 0) = DefS1loop (ContinuousMap.const _ c : C(Circle, Cstar)) t := by
    intro t
    simp [H, DefS1loop]
  have hone : ∀ t, H (t, 1) = c := by
    intro t
    rfl
  simpa [DefWNS1, H] using
    constpath Real.two_pi_pos
      (DefS1loop (ContinuousMap.const _ c : C(Circle, Cstar)))
      (DefS1loop_loop (ContinuousMap.const _ c : C(Circle, Cstar)))
      H hhom hzero c hone

/-%%
\begin{proof}\uses{DefS1loop, DefWNS1, constpath}\leanok
The loop associated to a constant map on $S^1$ is a constant loop by
Definition~\ref{DefS1loop}. By Definition~\ref{DefWNS1}, the winding number of the map is the
winding number of that loop, and Lemma~\ref{constpath} says the latter is zero.
\end{proof}
%%-/

/-%%
\begin{lemma}\label{S1homotopy}\lean{S1homotopy}\uses{DefS1loop, equalwinding, DefWNS1}\leanok
If two maps $S^1\to \Cstar$ are homotopic through maps into $\Cstar$, then they have equal
winding numbers.
\end{lemma}
%%-/

theorem S1homotopy (ψ ψ' : C(Circle, Cstar))
    (H : C(Circle × I01, Cstar))
    (hzero : ∀ z, H (z, 0) = ψ z)
    (hone : ∀ z, H (z, 1) = ψ' z) :
    DefWNS1 ψ = DefWNS1 ψ' := by
  have hfst : Continuous fun x : I2π × I01 => Circle.exp x.1 :=
    Circle.exp.continuous.comp (continuous_subtype_val.comp continuous_fst)
  let Hhat : C(I2π × I01, Cstar) :=
    ⟨fun x => H (Circle.exp x.1, x.2), H.continuous.comp (hfst.prodMk continuous_snd)⟩
  have hhom : homotopyloop Real.two_pi_pos.le Hhat := by
    intro s
    change H (Circle.exp 0, s) = H (Circle.exp (2 * π), s)
    rw [Circle.exp_zero, Circle.exp_two_pi]
  have hzero' : ∀ t, Hhat (t, 0) = DefS1loop ψ t := by
    intro t
    simp [Hhat, DefS1loop, hzero]
  have hone' : ∀ t, Hhat (t, 1) = DefS1loop ψ' t := by
    intro t
    simp [Hhat, DefS1loop, hone]
  simpa [DefWNS1] using
    equalwinding Real.two_pi_pos
      (DefS1loop ψ) (DefS1loop ψ')
      (DefS1loop_loop ψ) (DefS1loop_loop ψ')
      Hhat hhom hzero' hone'

/-%%
\begin{proof}\uses{DefS1loop, equalwinding, DefWNS1}\leanok
Precompose the given homotopy on $S^1$ with the parametrization $t \mapsto CSexp(it)$ of the
circle. This produces a homotopy between the associated loops in $Cstar$. By
Lemma~\ref{equalwinding} those two loops have the same winding number, hence by
Definition~\ref{DefWNS1} the original circle maps do as well.
\end{proof}
%%-/

/-%%
\begin{definition}\label{D2}\lean{D2}\leanok
The closed unit disk in $\C$.
\end{definition}
%%-/

abbrev D2 := {z : ℂ // ‖z‖ ≤ 1}

/-%%
\begin{definition}\label{circleToD2}\lean{circleToD2}\uses{D2}\leanok
The canonical inclusion of the unit circle into the closed unit disk.
\end{definition}
%%-/

def circleToD2 (z : Circle) : D2 := ⟨z, by simp [Circle.norm_coe z]⟩

/-%%
\begin{definition}\label{zeroD2}\lean{zeroD2}\uses{D2}\leanok
The center of the closed unit disk.
\end{definition}
%%-/

def zeroD2 : D2 := ⟨0, by simp⟩

/-%%
\begin{theorem}\label{boundsWN0}\lean{boundsWN0}\uses{S1homotopy, constS1}\leanok
If a map $\rho\colon S^1\to \Cstar$ extends to a map from the closed disk to $\Cstar$,
then its winding number is zero.
\end{theorem}
%%-/

theorem boundsWN0 (ρ : C(Circle, Cstar)) (F : C(D2, Cstar))
    (hF : ∀ z : Circle, F (circleToD2 z) = ρ z) :
    DefWNS1 ρ = 0 := by
  let Jfun : Circle × I01 → ℂ := fun x => (((1 - (x.2 : ℝ)) : ℂ) * (x.1 : ℂ))
  have hJfun_mem : ∀ x : Circle × I01, ‖Jfun x‖ ≤ 1 := by
    intro x
    have hs0 : 0 ≤ (x.2 : ℝ) := x.2.2.1
    have hs1 : (x.2 : ℝ) ≤ 1 := x.2.2.2
    have hnonneg : 0 ≤ 1 - (x.2 : ℝ) := by
      linarith
    have hreal : ‖((1 - (x.2 : ℝ)) : ℂ)‖ = |1 - (x.2 : ℝ)| := by
      simpa using (RCLike.norm_ofReal (K := ℂ) (1 - (x.2 : ℝ)))
    calc
      ‖Jfun x‖ = ‖((1 - (x.2 : ℝ)) : ℂ)‖ * ‖(x.1 : ℂ)‖ := by
        simp [Jfun, norm_mul]
      _ = |1 - (x.2 : ℝ)| * 1 := by
        rw [hreal]
        simp [Circle.norm_coe]
      _ = (1 - (x.2 : ℝ)) * 1 := by
        rw [abs_of_nonneg hnonneg]
      _ ≤ 1 := by
        linarith
  have hJfun_cont : Continuous Jfun := by
    simpa [Jfun] using
      (continuous_ofReal.comp
          (continuous_const.sub (continuous_subtype_val.comp continuous_snd))).mul
        (continuous_subtype_val.comp continuous_fst)
  let J : C(Circle × I01, D2) :=
    ⟨fun x => ⟨Jfun x, hJfun_mem x⟩, Continuous.subtype_mk hJfun_cont hJfun_mem⟩
  let H : C(Circle × I01, Cstar) := F.comp J
  have hJ0 : ∀ z : Circle, J (z, 0) = circleToD2 z := by
    intro z
    apply Subtype.ext
    change Jfun (z, 0) = (z : ℂ)
    simp [Jfun]
  have hJ1 : ∀ z : Circle, J (z, 1) = zeroD2 := by
    intro z
    apply Subtype.ext
    change Jfun (z, 1) = 0
    simp [Jfun, zeroD2]
  have hzero : ∀ z, H (z, 0) = ρ z := by
    intro z
    calc
      H (z, 0) = F (J (z, 0)) := rfl
      _ = F (circleToD2 z) := by rw [hJ0 z]
      _ = ρ z := hF z
  have hone : ∀ z, H (z, 1) = F zeroD2 := by
    intro z
    calc
      H (z, 1) = F (J (z, 1)) := rfl
      _ = F zeroD2 := by rw [hJ1 z]
  calc
    DefWNS1 ρ = DefWNS1 (ContinuousMap.const _ (F zeroD2) : C(Circle, Cstar)) := by
      exact S1homotopy ρ (ContinuousMap.const _ (F zeroD2)) H hzero hone
    _ = 0 := constS1 (F zeroD2)

/-%%
\begin{proof}\uses{S1homotopy, constS1}\leanok
Contract the disk radially to its center. Composing the extension $F$ with this contraction gives a
homotopy in $Cstar$ from $\rho$ to the constant boundary value $F(0)$. Lemma~\ref{S1homotopy}
shows that $\rho$ has the same winding number as this constant map, and Lemma~\ref{constS1}
shows that constant map has winding number zero.
\end{proof}
%%-/

/-%%
\begin{lemma}\label{walkingdog}\lean{walkingdog}\leanok
If two maps of the circle satisfy $|\psi(z)-\psi'(z)|<|\psi(z)|$ for every $z$, then the straight
line homotopy between them stays inside $\Cstar$.
\end{lemma}
%%-/

theorem walkingdog (ψ ψ' : C(Circle, Cstar))
    (hclose : ∀ z : Circle, ‖(ψ z : ℂ) - ψ' z‖ < ‖(ψ z : ℂ)‖) :
    ∃ H : C(Circle × I01, Cstar), (∀ z, H (z, 0) = ψ z) ∧ ∀ z, H (z, 1) = ψ' z := by
  let Hfun : Circle × I01 → ℂ := fun x =>
    (((1 - (x.2 : ℝ)) : ℂ) * (ψ x.1 : ℂ)) + (((x.2 : ℝ) : ℂ) * (ψ' x.1 : ℂ))
  have hHfun_cont : Continuous Hfun := by
    have hψ : Continuous fun x : Circle × I01 => (ψ x.1 : ℂ) :=
      continuous_subtype_val.comp (ψ.continuous.comp continuous_fst)
    have hψ' : Continuous fun x : Circle × I01 => (ψ' x.1 : ℂ) :=
      continuous_subtype_val.comp (ψ'.continuous.comp continuous_fst)
    simpa [Hfun] using
      ((continuous_ofReal.comp
          (continuous_const.sub (continuous_subtype_val.comp continuous_snd))).mul hψ).add
        ((continuous_ofReal.comp (continuous_subtype_val.comp continuous_snd)).mul hψ')
  have hHfun_ne : ∀ x : Circle × I01, Hfun x ≠ 0 := by
    intro x hx
    have hs0 : 0 ≤ (x.2 : ℝ) := x.2.2.1
    have hs1 : (x.2 : ℝ) ≤ 1 := x.2.2.2
    have hsNorm : ‖((x.2 : ℝ) : ℂ)‖ ≤ 1 := by
      simpa [RCLike.norm_ofReal, abs_of_nonneg hs0] using hs1
    have hle :
        ‖((x.2 : ℝ) : ℂ) * ((ψ x.1 : ℂ) - ψ' x.1)‖ ≤ ‖(ψ x.1 : ℂ) - ψ' x.1‖ := by
      calc
        ‖((x.2 : ℝ) : ℂ) * ((ψ x.1 : ℂ) - ψ' x.1)‖
            = ‖((x.2 : ℝ) : ℂ)‖ * ‖(ψ x.1 : ℂ) - ψ' x.1‖ := norm_mul _ _
        _ ≤ 1 * ‖(ψ x.1 : ℂ) - ψ' x.1‖ := by
          gcongr
        _ = ‖(ψ x.1 : ℂ) - ψ' x.1‖ := by ring
    have hEq : (ψ x.1 : ℂ) = ((x.2 : ℝ) : ℂ) * ((ψ x.1 : ℂ) - ψ' x.1) := by
      calc
        (ψ x.1 : ℂ) = (ψ x.1 : ℂ) - Hfun x := by rw [hx]; ring
        _ = ((x.2 : ℝ) : ℂ) * ((ψ x.1 : ℂ) - ψ' x.1) := by
              simp [Hfun]
              ring
    have hlt :
        ‖(ψ x.1 : ℂ)‖ < ‖(ψ x.1 : ℂ)‖ := by
      calc
        ‖(ψ x.1 : ℂ)‖
            = ‖((x.2 : ℝ) : ℂ) * ((ψ x.1 : ℂ) - ψ' x.1)‖ := by
                exact congrArg norm hEq
        _ ≤ ‖(ψ x.1 : ℂ) - ψ' x.1‖ := hle
        _ < ‖(ψ x.1 : ℂ)‖ := hclose x.1
    have : False := (lt_irrefl ‖(ψ x.1 : ℂ)‖) hlt
    exact this.elim
  let H : C(Circle × I01, Cstar) :=
    ⟨fun x => ⟨Hfun x, hHfun_ne x⟩, Continuous.subtype_mk hHfun_cont hHfun_ne⟩
  refine ⟨H, ?_, ?_⟩
  · intro z
    apply Subtype.ext
    simp [H, Hfun]
  · intro z
    apply Subtype.ext
    simp [H, Hfun]

/-%%
\begin{proof}\leanok
Use the straight-line homotopy
$H(z,t)=(1-t)\psi(z)+t\psi'(z)$. If $H(z,t)=0$, then
$\psi(z)=t(\psi(z)-\psi'(z))$, so
$|\psi(z)| \le |\psi(z)-\psi'(z)|$, contradicting the hypothesis. Thus the entire homotopy avoids
zero and stays inside $Cstar$.
\end{proof}
%%-/

/-%%
\begin{corollary}\label{sameWN}\lean{sameWN}\uses{walkingdog, S1homotopy}\leanok
Maps satisfying the walking-dog hypothesis have the same winding number.
\end{corollary}
%%-/

theorem sameWN (ψ ψ' : C(Circle, Cstar))
    (hclose : ∀ z : Circle, ‖(ψ z : ℂ) - ψ' z‖ < ‖(ψ z : ℂ)‖) :
    DefWNS1 ψ = DefWNS1 ψ' := by
  obtain ⟨H, hzero, hone⟩ := walkingdog ψ ψ' hclose
  exact S1homotopy ψ ψ' H hzero hone

/-%%
\begin{proof}\uses{walkingdog, S1homotopy}\leanok
Lemma~\ref{walkingdog} supplies a homotopy through maps into $Cstar$ between the two circle maps.
Lemma~\ref{S1homotopy} then implies that their winding numbers are equal.
\end{proof}
%%-/

/-%%
\begin{definition}\label{monomialS1Map}\lean{monomialS1Map}\leanok
The map $z \mapsto \alpha_0 (Rz)^k$ from the unit circle to $\Cstar$.
\end{definition}
%%-/

noncomputable def monomialS1Map (α0 : ℂ) (k : ℕ) (R : ℝ) (hR : 0 < R) (hα0 : α0 ≠ 0) :
    C(Circle, Cstar) := by
  refine ⟨fun z => ⟨α0 * (((R : ℂ) * z) ^ k), ?_⟩, ?_⟩
  · refine mul_ne_zero hα0 ?_
    exact pow_ne_zero k <| mul_ne_zero (by exact_mod_cast hR.ne') (Circle.coe_ne_zero z)
  · exact Continuous.subtype_mk
      (continuous_const.mul ((continuous_const.mul continuous_subtype_val).pow k))
      (by
        intro z
        refine mul_ne_zero hα0 ?_
        exact pow_ne_zero k <| mul_ne_zero (by exact_mod_cast hR.ne') (Circle.coe_ne_zero z))

/-%%
\begin{lemma}\label{zkWNk}\lean{zkWNk}\uses{DefS1loop, multiplicativity, expCP, deflift, WNloop, DefWNS1}\leanok
The map $z \mapsto \alpha_0 (Rz)^k$ on the unit circle has winding number $k$.
\end{lemma}
%%-/

theorem zkWNk (α0 : ℂ) (k : ℕ) (R : ℝ) (hR : 0 < R) (hα0 : α0 ≠ 0) :
    DefWNS1 (monomialS1Map α0 k R hR hα0) = (k : ℤ) := by
  let c0 : Cstar := ⟨α0 * (R : ℂ) ^ k, by
    refine mul_ne_zero hα0 ?_
    exact pow_ne_zero k (by exact_mod_cast hR.ne')⟩
  have hsurj : Set.SurjOn CSexp Set.univ Cstar := expCP.2.2
  obtain ⟨a0, -, ha0⟩ : (c0 : ℂ) ∈ CSexp '' Set.univ := hsurj c0.property
  let tildeω : C(I2π, ℂ) := by
    refine ⟨fun t => a0 + (k : ℂ) * (t : ℂ) * I, ?_⟩
    fun_prop
  have hlift :
      deflift CSexp (fun t => (DefS1loop (monomialS1Map α0 k R hR hα0) t : ℂ)) tildeω := by
    refine ⟨tildeω.continuous, ?_⟩
    ext t
    calc
      CSexp (tildeω t)
          = CSexp a0 * CSexp ((k : ℂ) * (t : ℂ) * I) := by
              simp [tildeω, multiplicativity]
      _ = (α0 * (R : ℂ) ^ k) * CSexp ((k : ℂ) * (t : ℂ) * I) := by
            rw [ha0]
      _ = (α0 * (R : ℂ) ^ k) * CSexp ((k : ℂ) * ((t : ℂ) * I)) := by
            ring_nf
      _ = (α0 * (R : ℂ) ^ k) * (CSexp (t * I)) ^ k := by
            unfold CSexp
            rw [Complex.exp_nat_mul]
      _ = (α0 * (R : ℂ) ^ k) * (Circle.exp t : ℂ) ^ k := by
            unfold CSexp
            rw [Circle.coe_exp]
      _ = α0 * (((R : ℂ) * (Circle.exp t : ℂ)) ^ k) := by
            rw [mul_pow]
            ring
      _ = (DefS1loop (monomialS1Map α0 k R hR hα0) t : ℂ) := by
            rfl
  have hwind :
      (DefWNS1 (monomialS1Map α0 k R hR hα0) : ℂ) = k := by
    calc
      (DefWNS1 (monomialS1Map α0 k R hR hα0) : ℂ)
          =
            (tildeω ⟨2 * π, ⟨Real.two_pi_pos.le, le_rfl⟩⟩ -
                tildeω ⟨0, ⟨le_rfl, Real.two_pi_pos.le⟩⟩) / (2 * π * I) := by
              symm
              simpa [DefWNS1] using
                WNloop_eq_of_lift Real.two_pi_pos
                  (DefS1loop (monomialS1Map α0 k R hR hα0))
                  (DefS1loop_loop (monomialS1Map α0 k R hR hα0))
                  tildeω hlift
      _ = (k : ℂ) := by
            have hpi : (π : ℂ) ≠ 0 := by
              exact_mod_cast Real.pi_ne_zero
            field_simp [tildeω, hpi, Complex.I_ne_zero]
            ring
  exact_mod_cast hwind

/-%%
\begin{proof}\uses{DefS1loop, multiplicativity, expCP, deflift, WNloop, DefWNS1}\leanok
The associated loop is $t \mapsto \alpha_0 R^k CSexp(kit)$. Choose a logarithm of the nonzero
constant $\alpha_0 R^k$ using Lemma~\ref{expCP}; then
$\tilde\omega(t)=\tilde\alpha_0+kit$ is a lift of this loop through $CSexp$ by
Lemma~\ref{multiplicativity}. The endpoint difference of the lift is exactly $2\pi k i$, so
Definition~\ref{WNloop} gives winding number $k$, and Definition~\ref{DefWNS1} transfers this to
the map on $S^1$.
\end{proof}
%%-/

/-%%
\begin{definition}\label{polyCircleMap}\lean{polyCircleMap}\leanok
The polynomial map $z \mapsto p(Rz)$ from the unit circle to $\Cstar$ when it avoids zero.
\end{definition}
%%-/

noncomputable def polyCircleMap (p : Polynomial ℂ) (R : ℝ)
    (hR : ∀ z : Circle, p.eval ((R : ℂ) * z) ≠ 0) : C(Circle, Cstar) := by
  refine ⟨fun z => ⟨p.eval ((R : ℂ) * z), hR z⟩, ?_⟩
  exact Continuous.subtype_mk
    (p.continuous.comp (continuous_const.mul continuous_subtype_val))
    (by
      intro z
      simpa using hR z)

/-%%
\begin{definition}\label{polyDiskMap}\lean{polyDiskMap}\uses{D2}\leanok
The polynomial map $z \mapsto p(Rz)$ from the closed unit disk to $\Cstar$ when it avoids zero.
\end{definition}
%%-/

noncomputable def polyDiskMap (p : Polynomial ℂ) (R : ℝ)
    (hR : ∀ z : D2, p.eval ((R : ℂ) * z) ≠ 0) : C(D2, Cstar) := by
  refine ⟨fun z => ⟨p.eval ((R : ℂ) * z), hR z⟩, ?_⟩
  exact Continuous.subtype_mk
    (p.continuous.comp (continuous_const.mul continuous_subtype_val))
    (by
      intro z
      simpa using hR z)

/-%%
\begin{lemma}\label{zkdominates}\lean{zkdominates}\leanok
For a nonconstant complex polynomial, the leading term dominates the lower-order terms on
sufficiently large circles.
\end{lemma}
%%-/

theorem zkdominates (p : Polynomial ℂ) (hdeg : 0 < p.natDegree) :
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
      ‖x‖ = ‖(R : ℂ)‖ * ‖(z : ℂ)‖ := by simp [x, norm_mul]
      _ = |R| * 1 := by simp [Circle.norm_coe]
      _ = R := by rw [abs_of_nonneg hR0]; ring
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
Write the polynomial as its leading term plus the sum of lower-degree terms. On the circle
$|z|=R$, each lower-degree monomial is bounded by a constant multiple of $R^{k-1}$, so their sum is
at most $S R^{k-1}$ for a fixed constant $S$. For $R$ sufficiently large we have
$S R^{k-1} < |\alpha_0| R^k$, which proves that the leading term strictly dominates the remainder.
\end{proof}
%%-/

/-%%
\begin{theorem}\label{WNthm}\lean{WNthm}\uses{zkWNk, zkdominates, sameWN}\leanok
On a sufficiently large circle, a complex polynomial has winding number equal to its degree.
\end{theorem}
%%-/

theorem WNthm (p : Polynomial ℂ) (hdeg : 0 < p.natDegree) :
    ∃ R0 : ℝ, 0 < R0 ∧ ∀ R : ℝ, R0 ≤ R →
      ∃ f : C(Circle, Cstar), (∀ z, (f z : ℂ) = p.eval ((R : ℂ) * z)) ∧
        DefWNS1 f = (p.natDegree : ℤ) := by
  obtain ⟨R0, hR0pos, hdom⟩ := zkdominates p hdeg
  refine ⟨R0, hR0pos, ?_⟩
  intro R hR
  have hp : p ≠ 0 := by
    intro hp0
    rw [hp0] at hdeg
    exact (lt_irrefl 0 hdeg).elim
  have hlead : p.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp
  have hRpos : 0 < R := lt_of_lt_of_le hR0pos hR
  have hpoly_nonzero : ∀ z : Circle, p.eval ((R : ℂ) * z) ≠ 0 := by
    intro z hz
    have hbad :
        ‖p.leadingCoeff * (((R : ℂ) * z) ^ p.natDegree)‖ <
          ‖p.leadingCoeff * (((R : ℂ) * z) ^ p.natDegree)‖ := by
      simpa [hz, norm_sub_rev] using hdom R hR z
    exact (lt_irrefl _ hbad).elim
  let f : C(Circle, Cstar) := polyCircleMap p R hpoly_nonzero
  have hclose :
      ∀ z : Circle,
        ‖(monomialS1Map p.leadingCoeff p.natDegree R hRpos hlead z : ℂ) - f z‖ <
          ‖(monomialS1Map p.leadingCoeff p.natDegree R hRpos hlead z : ℂ)‖ := by
    intro z
    simpa [f, polyCircleMap, monomialS1Map, norm_sub_rev] using hdom R hR z
  refine ⟨f, ?_, ?_⟩
  · intro z
    rfl
  · calc
      DefWNS1 f = DefWNS1 (monomialS1Map p.leadingCoeff p.natDegree R hRpos hlead) := by
        symm
        exact sameWN (monomialS1Map p.leadingCoeff p.natDegree R hRpos hlead) f hclose
      _ = (p.natDegree : ℤ) := zkWNk p.leadingCoeff p.natDegree R hRpos hlead

/-%%
\begin{proof}\uses{zkWNk, zkdominates, sameWN}\leanok
For large $R$, Lemma~\ref{zkdominates} shows that the polynomial map
$z \mapsto p(Rz)$ is uniformly close, in the walking-dog sense, to its leading monomial
$z \mapsto \alpha_0 (Rz)^k$. Therefore Lemma~\ref{sameWN} says these two maps have the same winding
number. Lemma~\ref{zkWNk} computes the winding number of the monomial to be $k$, so the polynomial
has winding number $k$ as well.
\end{proof}
%%-/

/-%%
\begin{theorem}\label{ExistRoot}\lean{ExistRoot}\uses{WNthm, boundsWN0}\leanok
Every nonconstant complex polynomial has a complex root.
\end{theorem}
%%-/

theorem ExistRoot (p : Polynomial ℂ) (hdeg : 0 < p.natDegree) : ∃ z : ℂ, p.IsRoot z := by
  by_contra hroot
  have hnoroot : ∀ z : ℂ, p.eval z ≠ 0 := by
    intro z hz
    exact hroot ⟨z, hz⟩
  obtain ⟨R0, hR0pos, hWN⟩ := WNthm p hdeg
  obtain ⟨f, hf, hwind⟩ := hWN R0 le_rfl
  let F : C(D2, Cstar) := polyDiskMap p R0 (fun z => hnoroot ((R0 : ℂ) * z))
  have hboundary : ∀ z : Circle, F (circleToD2 z) = f z := by
    intro z
    apply Subtype.ext
    calc
      (F (circleToD2 z) : ℂ) = p.eval ((R0 : ℂ) * z) := by
        rfl
      _ = (f z : ℂ) := (hf z).symm
  have hzero : DefWNS1 f = 0 := boundsWN0 f F hboundary
  have hdeg_ne : (p.natDegree : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hdeg)
  exact hdeg_ne <| by
    rw [← hwind, hzero]

/-%%
\begin{proof}\uses{WNthm, boundsWN0}\leanok
Assume for contradiction that the polynomial has no complex root. Then for sufficiently large
$R$, Theorem~\ref{WNthm} shows that the restriction of $p$ to the circle of radius $R$ has
nonzero winding number, namely its degree. But under the no-root assumption, the map
$z \mapsto p(Rz)$ extends from the boundary circle to the whole closed disk without hitting zero.
Theorem~\ref{boundsWN0} therefore says its winding number must be zero, a contradiction.
\end{proof}
%%-/
