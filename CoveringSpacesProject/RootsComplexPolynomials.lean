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
