import Mathlib

open TopologicalSpace Function

open Complex Set

local notation "π" => Real.pi

/-%%
We have ${\rm exp}\colon \C\to \C$ defined by
$${\rm exp}(r+\theta *I)={\rm exp}_\R(r){\rm exp}(\theta * I)
={\rm exp}_\R(r)*({\rm cos}(\theta+{\rm sin}(\theta)*I),$$
for $r,\theta\in \R$. Since ${\exp}_\R(r)>0$,
the image of ${\rm exp}$ lies in $\C\setminus\{0\} :=\C^*$.
This map satisfies ${\rm exp}(z+w)={\rm exp}(z)\cdot{\rm exp}(w)$.
That is to say ${\rm exp}\colon \C\to \C^*$ is a homomorphism from the additive group of $\C$
to the multiplicative group of $\C^*$.
%%-/
example (r θ : ℝ) :
    exp (r + θ * I) =
    Real.exp r * (cos θ + sin θ * I) := by
  rw [exp_add]
  rw [ofReal_exp]
  rw [exp_mul_I]

/-%%
\begin{lemma}[periodicity]\label{periodicity}\lean{periodicity}\leanok
${\rm exp}\colon \C\to \C^*$ is periodic of period $2\pi i$ and with no smaller period. \end{lemma}
%%-/
lemma periodicity (z : ℂ) :
    (∀ n : ℤ, exp (z + n * (2 * π) * I) = exp z)
    ∧ ∀ (w : ℂ), exp w = exp z → ∃ n : ℤ, w = z + n * 2 * π * I := by
  constructor
  · intro n
    rw [exp_add, exp_mul_I]
    rw [cos_int_mul_two_pi n]
    have : sin (n * (2 * π)) = sin (2 * n * π) := by
      ring_nf
    rw [this]
    simp only [ne_eq, exp_ne_zero, not_false_eq_true, mul_eq_left₀, add_eq_left, mul_eq_zero,
      I_ne_zero, or_false]
    convert Complex.sin_int_mul_pi (2 * n)
    norm_cast
  · intro w hw
    convert Complex.exp_eq_exp_iff_exists_int.mp hw using 4
    ring
/-%%
\begin{proof}\leanok
Since, for $z,w\in \C$, we
${\rm exp}(z+w)={\rm exp}(z)\cdot{\rm exp}(w)$,  ${\rm exp}$ is periodic of period $w$ if and only if ${\rm exp}(w)=1$.
Since $\|{\rm exp}(w)\|={\rm exp}_\R(Re(w))$, if ${\rm exp}(w)=1$ have real part equal to ${\rm Re}(w)=0$.
By Euler's Formula we have
${\rm exp}(\theta *I)= {\rm cos}(\theta)+{\rm sin}(\theta) *I.$
It follows from the basic properties of sine and cosine that ${\rm exp}(2\pi*I)=1$ and that
 ${\rm exp}(\theta*I)\not= 1$ for $0<\theta<2\pi$.
Thus, ${\rm exp}$ is periodic of period $2\pi *I$ and ${\rm exp}$ is periodic of period $w$ if and only if $w\in (2\pi *I)\Z$.
\end{proof}
%%-/

/-%%
We have a branch of the complex log  defined on $\C\setminus \{0\}$ and continuous
off the negative real axis  and semi-continuous along the negative
real axis (excluding $0$) as we approach this axis from the upper half plan. Furthermore, for all $z\in \C^*$
${\rm exp}(log(z))=z$
%%-/
example (z : ℂ) (hz : z ≠ 0) :
    exp (log z) = z := by
  rw [exp_log hz]

/-%%
\begin{definition}[strip]\label{strip}\lean{strip}\leanok
Let $S\subset \C$ be the strip $\{(r+\theta *I)\}$ for $r,\theta\in \R$ and $-\pi<\theta <\pi$.
\end{definition}
%%-/
def strip : Set ℂ :=
--  { z | ∃ r θ : ℝ, z = r + θ * I ∧ -π < θ ∧ θ < π }
  (univ : Set ℝ) ×ℂ Ioo (-π) π

example : strip = { z | ∃ r θ : ℝ, z = r + θ * I ∧ -π < θ ∧ θ < π } := by
  sorry

/-%%
\begin{definition}[slitPlane']\label{slitPlane'}\lean{slitPlane'}\leanok
 Let $T\subset \C^*$ be $\C\setminus \{x\in \R|x \le 0\}$.
 \end{definition}
%%-/
def slitPlane' : Set ℂ :=
  univ \ {x : ℂ | x.re ≤ 0 ∧ x.im = 0}

example : slitPlane' = slitPlane := by
  ext z
  simp only [slitPlane', mem_diff, mem_univ, mem_setOf_eq, not_and, true_and, slitPlane, ne_eq]
  sorry

/-%%
\begin{corollary}
Then ${\rm exp}\colon S\to T$ and ${\rm log}\colon T\to S$ are inverse homeomorphisms.
\end{corollary}
%%-/

/-%%
\begin{proof}
Since ${\rm exp}(z)\in \R^+$ if and only if ${\rm exp}({\rm Im}(z))\in \R^+$ if and only if
${\rm Im}(z)\in (2\pi *I)\Z$. Since every  element of $S$ has imaginary part strictly between $0$ and $2\pi$,
it follows that ${\rm exp}(S)\subset T$. Conversely, every element of $T$ can be written uniquely as
$r{\rm exp}(\theta *I)$ with $r,\theta\in \R$, $r>0$, and $0<\theta<2\pi$. Since ${\rm log}(r{\rm exp}(\theta *I)$
is ${\rm log}_{\R}(r)+\theta *I$. Thus, ${\rm log}(T)\subset S$.

By standard results both ${\rm exp}$ and ${\rm log}|_T$ are continuous. Also, ${\rm exp}|_S$ is one-to-one
since the imaginary part of any element of $S$ is strictly between $0$ and $2\pi$, so if $z\in S$ and for some $n\in \Z$,
 if $ z+2\pi n *Is\in S$, then $n=0$. Since ${\rm exp}|_S$ is one-to-one and ${\rm exp}({\rm log}(z)=z$ for all $z\in T$,
 it follows that ${\rm exp}\colon S\to T$ and ${\rm \log}\colon T\to S$ are inverse functions. Since each is continuous,
 they are inverse homeomorphisms.
\end{proof}
%%-/

/-%%
\begin{definition}
$\tilde S\subset \C$ is the subset $\{r+\theta* I|r,\theta\in \R \text{\ and\ } \theta\not= (2k+1)\pi \text{\ for\  any\ } k\in \Z\}$.
\end{definition}
%%-/

/-%%
\begin{lemma}
$\varphi\colon S\times \Z \to \C$ defined by $\varphi(z,k)=z+2k\pi *I$ is a homeomorphism
$S\times \Z\to \tilde S$.
\end{lemma}
%%-/

/-%%
\begin{proof}
Let $z=(r+\theta *I)\in \tilde S$. Then $\theta$ is not an odd multiple integral multiple of of $\pi$ so there is a unique $\theta_0\in (-\pi,\pi)$ for which there exists $k\in \Z$ with $\theta-\theta_0= (2k\pi )$. Then $\varphi(r+\theta_0*I,k)$.
This show that $\varphi$ is onto. By the uniqueness of $k$ in the above argument, we see that $\varphi$ is also one-to-one.
Lastly, it is given by a complex polynomial map so it is continuous. Lastly, $\tilde S$ is a union of disjoint open sets
$$S_k= \{r+\theta *I | r,\theta\in \R \text{\ and\ } (2k-1)\pi <\theta< (2k+1)\pi$$
and  $S_k =\varphi(S\times \{2k\pi\})$
and the map is the homeomorphism that adds $2k\pi *I$. This shows that $\varphi$ is a local homeomorphism Being bijective it is a homeomorphism.
\end{proof}
%%-/

/-%%
\begin{definition}
Let $\rho\colon \tilde S\to \Z$ send $x\in \tilde S$ to $p_2(\varphi^{-1}(z)$ where $p_2$ is the projection to the second factor.
\end{definition}
%%-/

/-%%
\begin{theorem}
$\tilde S={\rm exp}^{-1}(T)$ and the map $\psi\colon \tilde S\to T\times \Z$ given by $z\mapsto ({\rm exp}(z) ,\rho(z))$
is a homeomorphism and $p_1\circ \psi\tilde S\to T$ is the restriction to $\tilde S$ of ${\rm exp}$.
\end{theorem}
%%-/

/-%%
\begin{proof}
By construction $p_1\circ \psi={\rm exp}+{\tilde S}$. To show  $\psi$ is a homeomorphism, it suffices to shwo that
$\psi\circ \varphi\colon S\times \Z\to T\times \Z$ is a homeomorphism. But this map is product of
 ${\rm exp}\colon S\to T$ with the identity from $\Z$ to $\Z$. Being a product of homeomorphisms it is a homeomorphism.
\end{proof}
%%-/

/-%%
\begin{corollary}[triv_over_T]
This defines a trivialization of ${\rm exp}$ over $T$.
\end{corollary}
%%-/

/-%%
\begin{proposition}[invariance]
Suppose $f\colon E\to X$ is a map between topological spaces and $U]subset X$ is an open subset which is the base of a trivialization. Suppose also that there are homeomorphism $\varphi\colon X\to X$ and $\tilde \varphi\colon E\to E$
with $f\circ\tilde\varphi =\varphi\circ f$. The $\varphi(U)$ is the base of a trivialization.
\end{proposition}
%%-/

/-%%
\begin{proof}
The image $\tilde\varphi\colon f^{-1}(U) \to f^{-1}(\varphi(U))$ is a homeomorphism.
Let $\psi\colon f^{-1}(U)\to U\times I$ be a trivialization. Then
$$ f^{-1}\varphi(U) \buildrel \tilde\varphi^{-1}\over\longrightarrow f^{-1}(U)\buildrel \psi\over\longrightarrow U\times I
\buildrel \varphi \times{\rm Id}_I\over\longrightarrow \varphi(U)\times I$$
is a trivialization with base $\varphi(U)$.
\end{proof}
%%-/

/-%%
\begin{corollary}
Let $T'\subset \C^*$ be the complement of $\R^+$. Then $T'$ is the base of a trivialization.
\end{corollary}
%%-/

/-%%
\begin{proof}
We have homeomorphism $\mu \colon \C^*\to \C^*$ that sends $z to {\rm exp}(\pi *I)z$
and the homoeomorphism $\tilde \mu\colon \C\to \C$ defined by $\tilde mu(z)=z+\pi *I$
Clearly ${\rm exp}(\tilde\mu(z)= \mu({\rm exp}(z)$ and $\mu(T)=T'$.
\end{proof}
%%-/

/-%%
\begin{corollary}[exp_CP]\label{exp_CP}
${\rm exp}\colon \C\to \C^* $ is a covering projection.
\end{corollary}
%%-/

/-%%
\begin{proof}
$T\cup T'=\C^*$ and each of $T$ and $T'$ is the base of trivialization for ${\rm exp}$. Hence, every point
of $\C^*$ lies in the base of a trivialization.
\end{proof}
%%-/
/-%%

\begin{corollary}[exp_UPL]\label{exp_UPL}
Given a path $\omega\colon [a,b]\to \Cee^*$ and $\tilde a_0\in {\rm exp}^{-1}(\omega(a)$, there is a unique map
$\tilde\omega\colon [a,b]\to \Cee$ with $\tilde\omega(a)=\tilde a_0$ and ${\rm exp}(\tilde\omega)=\omega$.
\end{corollary}

\begin{proof}
By Corollary~\ref{exp_CP} and the basic result about covering projections.
\end{proof}

%%-/
