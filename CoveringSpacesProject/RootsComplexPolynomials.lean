import Mathlib

open TopologicalSpace Function

open Complex Set

local notation "π" => Real.pi

/-%%

\section{Results from LEAN}
%%-/


/-%%
Here are basic definitions and results already in LEAN:
%%-/

variable {X Y F : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace F]
  (proj : X → Y)

/-%%

\begin{definition}\label{trivialization}\lean{trivialization}\leanok
$f\colon X\to Y$ a local trivialization for $f$ is:
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

\begin{definition}\label{DefIsCoveringOn}\lean{DefIsCoveringOn}\leanok
Let
$f\colon X\to Y$ be a continuous map and $A\subset Y$. Then $f$ is an even cover on $A\subset X$
if every $a\in A$ has a neighborhood which is contained in the target of a trivialization
\end{definition}
%%-/

def DefIsCoveringOn := IsCoveringMapOn proj

/-%%

\begin{definition}\label{Defexp}\lean{Defexp}\leanok
$exp\colon \C\to \C$ defined by
the usual power series.
\end{definition}
%%-/

noncomputable def Defexp : ℂ → ℂ := Complex.exp

/-%%

\begin{lemma}\label{Contexp}
$exp\colon \C\to \C$ is continuous.
\end{lemma}
%%-/
lemma Contexp : Continuous Defexp := by
  apply Complex.continuous_exp
/-%%
\begin{proof}\uses{Defexp}
  In Mathlib.
\end{proof}
%%-/


/-%%

\begin{lemma}\label{Eulersformula}\lean{Eulersformula}\leanok
$$exp(r+\theta *I)=exp_\R(r)exp(\theta * I)
=exp_\R(r)*({\rm cos}(\theta+{\rm sin}(\theta)*I),$$
for $r,\theta\in \R$.
\end{lemma}
%%-/

lemma Eulersformula (r θ : ℝ) :
    Defexp (r + θ * I) = Defexp r * Complex.exp (θ * I) := by
  unfold Defexp
  rw [Complex.exp_add, Complex.exp_mul_I]

/-%%
\begin{proof}\uses{Defexp}\leanok
  In Mathlib.
\end{proof}
%%-/

/-%%
\begin{lemma}\label{multiplicativity}\lean{multiplicativity}\leanok
 $exp(z+w)=exp(z)\cdotexp(w)$.
\end{lemma}
%%-/

lemma multiplicativity (z w : ℂ) :
    Defexp (z + w) = Defexp z * Defexp w := by
  unfold Defexp
  rw [Complex.exp_add]

/-%%
\begin{proof}\uses{Defexp}\leanok
  In Mathlib.
\end{proof}
%%-/

/-%%

\begin{lemma}\label{periodicity}\lean{periodicity}\leanok
$exp\colon \C\to \C$ is periodic of period $2π  i$ and with no smaller period.
\end{lemma}
%%-/

lemma periodicity : Function.Periodic Defexp (2 * π * I) := by
  unfold Defexp
  apply Complex.exp_periodic
/-%%
\begin{proof}\uses{Defexp}\leanok
  In Mathlib.
\end{proof}
%%-/


/-%%

\begin{definition}\label{DefPBlog}\lean{DefPBlog}\leanok
There is a $DefPBlog\colon \C\to \C$.
\end{definition}
%%-/

noncomputable def DefPBlog (z : ℂ) : ℂ :=
  Complex.log z

/-% **Wrong delimiters on purpose**

\begin{lemma}\label{DefPBlogInverse}
If $z\in \C$ and $z\not=0$ then $exp(DefPBlog(z))=z$.
\end{lemma}
\begin{proof}\uses{DefPBlog, Defexp}
In Mathlib.
\end{proof}
%-/

/-%%

\begin{lemma}\label{ImPBlog}
The image of $DefPBlog$ is contained in $\{z\in \C |-π < Im(z)\le π \}$ and
 for all $\{z\in \C | z\not=0\}$ $exp(DefPBlog)(z)=z$.
\end{lemma}
%%-/

/-%%
\begin{proof}\uses{DefPBlog, Defexp, Eulersformula}
This is immediate from Definition~\ref{DefPBlog} and Lemma~\ref{Eulersformula}.
\end{proof}
%%-/

/-%%

\begin{definition}\label{splitPlane}
$T=\{z\in \C |Re(z)>0 \cup Im(z)\not= 0\}$
\end{definition}
%%-/

/-%%

\begin{lemma}\label{ContDefPBlog}
$DefPBlog$ is continuous on $T$ and if $z\in T$ then
$DefPBlog(z)\in \{z\in \C |-π  < Im(z) < π \}$.
\end{lemma}

%%-/
/-%%
\begin{proof}\uses{Eulersformula}
By Lemma|~\ref{Eulersformula}  for $x\in T$  $Re(cos(x))\not=-1$ and hence $DefPBlog(x)\in S$.
\end{proof}
%%-/

/-% **Wrong delimiters on purpose**
\begin{lemma}
For all $x\in T$, $DefPBlog(x)\in \{z\in \C | -π  < Im(z) < π \}$
\end{lemma}
%-/
/-%
\begin{proof}\uses{DefPBlog, Defexp}
In Mathlib.
\end{proof}
%-/

/-%%

\section{$exp\colon \C\to \C$ is a covering projection on $Cstar$}

\begin{definition}\label{Cstar}
$Cstar=\{z\in \C |z\not= 0\}$
\end{definition}

%%-/

/-%%
\begin{definition}\label{deflift}
Let $f\colon X\to Y$ be a continuous map between topological spaces and $\alpha\colon A\to Y$
a continuous map. A lift of $\alpha$ through $f$ is a continuous map $\tilde\alpha\colon A\to X$ such that
$f\circ \tilde\alpha =f$.
\end{definition}
%%-/

/-%%


\begin{definition}\label{stripDef}
For any $a, b\in \R$ with $a < b$ we define $S(a,b)=\{z\in \C | a < Im{z} < b$.
Define $S\subset \C$ by $S=S(-π ,π )$.
\end{definition}

%%-/

/-%%


\begin{proposition}\label{inverseHomeo}
Then $exp\colon S\to T$ and ${\rm log}\colon T\to S$ are inverse homeomorphisms.
\end{proposition}

%%-/

/-%%
\begin{proof}\uses{stripDef, Eulersformula, Contexp, ContDefPBlog, periodicity}
By Lemma~\ref{Eulersformula} $exp(z)\in \R^-$ if and only if $exp({\rm Im}(z))\in \R^-$ if and only if
${\rm Im}(z)\in (π  *I)+(2π )\Z$. Since, by Definition~\ref{stripDef} every  element of $S$ has imaginary part strictly between $-π $
and $π $,
it follows that $exp(S)\subset T$.
Conversely, by Lemma~\ref{ContDefPBlog} if $z\in T$ then $DefPBlog(z)\in S$.

By Lemma~\ref{Contexp} $exp$ is continuous and, by Lemma~\ref{ContDefPBlog}, $DefPBlog$ is continuous on $T$.
Suppose that $z,w\in S$ and $exp(z)=exp(w)$.
By Lemma~\ref{periodicity}
 if $exp(z)=exp{w}$ then there is an integer $n$ such that $z-w =2π  *n*I$ If $z,w\in S$, then
 $-2π < Im(z)-Im(w)<2π $, so $z=w$. This shows that   $exp|_S$ is one-to-one.
 Since $exp|_S$ is one-to-one and $exp({\rm DefPBlog}(z))=z$
 for all $z\in T$,
 it follows that $exp\colon S\to T$ and ${DefPBlog}\colon T\to S$
 are inverse functions. Since each is continuous,
 they are inverse homeomorphisms.
\end{proof}
%%-/

/-%%

\begin{definition}\label{tildeSDef}
$\tilde S\subset \C$ is the subset $\{r+\theta* I|r,\theta\in \R \text{\ and\ } \theta\not=
(2k+1)π  \text{\ for\  any\ } k\in \Z\}$.
\end{definition}
%%-/

/-%%

\begin{lemma}\label{tildeShomeo}
Define $\varphi\colon S\times \Z \to \C$  by $\varphi(z,k)=z+2kπ  *I$. Then
$\varphi\colon S\times \Z\to \tilde S$  is a homeomorphism.
\end{lemma}
%%-/

/-%%

\begin{proof}\uses{stripDef, tildeSDef}
According to Definition~\ref{stripDef}  image of $S$ under the translation action of $(2π )\Z$ on $\C$   is the union
of all strips $S(2n-1)π ,(2n+1)π )$. By Definition~\ref{tildeSDef} this union is $\tilde S$. Thus we have a map $S\times \Z\to \tilde S$ defined by
$(z,n)\mapsto z+2π  *n *I$. Since translation is a homeomorphism of $\C\to \C$, this map is a local homeomorphism onto its image $\tilde S$. If $n ,n'\in \Z$ with $n\not=n'$ then
$S((2n-1)π ,(2n+1)π )\cap S((2n'-1)π ,(2n'+1)π )=\emptyset$.
Also $\tilde S=\coprod_{n\in \Z}S((2n-1)π ,(2n+1)π )$. It follows that
$\varphi$ is a bijective map and hence a  homeomorphism.
\end{proof}
%%-/

/-%%






\begin{definition}\label{widetildeDefPBlogDef}
Let $\widetilde{DefPBlog}\colon T\times \Z\to S\times \Z$ be defined by $\widetilde{DefPBlog}(z,n)=(DefPBlog(z),n)$
for all $z\in T$ and $n\in \Z$.
\end{definition}
%%-/

/-%%

\begin{lemma}\label{widetildeDefPBlogHomeo}
$\widetilde{DefPBlog}\colon T\times \Z\to S\times \Z$ is a homeomorphism.
\end{lemma}
%%-/

/-%%

\begin{proof}\uses{widetildeDefPBlogDef, inverseHomeo}
By Definition~\ref{widetildeDefPBlogDef} $\widetilde DefPBlog$ is the product of $DefPBlog\colon T\to S$ and ${\rm Id}_\Z\colon \Z\to\Z$.
By Lemma~\ref{inverseHomeo} the first of these factors is a homeomorphism. Since ${\rm Id}_\Z$ is a homeomorphism.
it follows from basic properties of homeomorphisms that the product $\widetilde{DefPBlog}$ is a homeomorphism
\end{proof}
%%-/

/-%%

\begin{proposition}\label{trivOverT}
The composition $\psi=\varphi\circ\widetilde{DefPBlog}\colon T\times \Z\to \tilde S$ defines a trivialization of $exp$
on $T$
\end{proposition}
%%-/

/-%%

\begin{proof}\uses{tildeShomeo, widetildeDefPBlogHomeo, periodicity}
$\varphi$ is a homeomorphism by Lemma~\ref{tildeShomeo}.
By Lemma~\ref{widetildeDefPBlogHomeo}    $\widetilde{DefPBlog}\colon T\times \Z\to S\times \Z$ is a homemorphism.
Thus, the composition $\varphi\circ\widetilde{DefPBlog}\colon T\times \Z\to \tilde S$ is a homeomorphism.
For $(z,n)\in T\times \Z$,
$$exp\circ\varphi\circ \widetilde{DefPBlog}(z,n)=exp(\varphi(DefPBlog(z),n)=exp(DefPBlog(z)+2π  * n * I).$$
By Lemma~\ref{periodicity}, $exp(DefPBlog(z)+2π  * n * I)=exp(DefPBlog(z)$, which by Lemma~\ref{widetildeDefPBlogHomeo} equals $z$. This establishes that$\psi$ satisfies all  the conditions of the  Definition of Trivialization over the open set $T$.
\end{proof}
%%-/

/-%%


\begin{lemma}\label{homeoInv}
Suppose $f\colon E\to X$ is a map between topological spaces and $U\subset X$ is an open subset which is the base of a trivialization for $f$. Suppose also that there are homeomorphisms $\varphi\colon X\to X$ and $\tilde \varphi\colon E\to E$
with $f\circ\tilde\varphi =\varphi\circ f$. The $\varphi(U)$ is the base of a trivialization for $f$.
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
$T'$ is the base of a trivialization for $exp\colon \C\to \C$
with non-empty fiber.
\end{corollary}
%%-/

/-%%

\begin{proof}\uses{multiplicativity, Eulersformula, homeoInv, trivOverT, splitPlane, TprimeDef}
We have homeomorphism $\mu \colon \C\to \C$ that sends $z \to exp(π  *I)z)$
and the homeomorphism $\tilde \mu\colon \C\to \C$ defined by $\tilde \mu(z)=z+π  *I$
Clearly  by Lemma~\ref{multiplicativity} and Lemma~\ref{Eulersformula}
$exp(\tilde\mu(z))= \mu(exp(z))$.
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

\begin{proof}\uses{xinTorTprime}
Immediate from Lemma~\ref{xinTorTprime}.
\end{proof}
%%-/

/-%%

\begin{corollary}\label{expCP}
$exp\colon \C\to \C $ is a covering projection over $Cstar$ with source $\C$ and is surjective onto $Cstar$.
\end{corollary}
%%-/

/-%%

\begin{proof}\uses{Cstar, trivOverT, trivOverTprime, ImPBlog, TcupTprimeCstar, DefPBlogInverse, DefIsCoveringOn}
By Corollary~\ref{TcupTprimeCstar}
$T\cup T'= Cstar$. By Proposition~\ref{trivOverT} and Corollary~\ref{trivOverTprime} and each of $T$ and $T'$ is the base of trivialization for $exp$ with non-trivial fiber. Hence, every point  of $Cstar$ lies in the base of a trivialization for $exp$. By definition, this shows that $exp\colon \C\to \C $ is a covering on $Cstar$.
Since $exp(z)\not=0$ for all $z\in \C$, it follows that $exp^{-1}(Cstar)=\C$.
Lastly, by Lemma~\ref{ImPBlog} if $z\in\C$ and $z\not= 0$ then $exp(DefPBlog)(z)=z$.
This proves that $exp$ is onto $\{z\in \C | z\not=0\}$, which by Lemma~\ref{Cstar}, is equal to $Cstar$.\end{proof}
%%-/

/-%%

\begin{corollary}\label{expUPL}
Given a path $\omega\colon [ a , b]\to \C $ with $\omega(t)\not=0$ for all $t\in [ a, b]$, and
$\tilde a_0\in exp^{-1}(\omega(a)$, there is a unique map
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
$exp$ satisfies the homotopy lifting property on $Cstar$.
\end{corollary}
%%-/

/-%%
\begin{proof}\uses{expCP}
This is immediate from Corollary~\ref{expCP} and the theorem that covering projections have the homotopy lifting property.
\end{proof}
%%-/

/-%%


\section{Homotopy Classes of Loops and maps of $S^1$ in $Cstar$}

We fix $a < b\in \R$.
%%-/

/-%%

\begin{definition}\label{loop}
Let $X$ be a topological space.  A {\em loop} in $X$ is a map $\omega\colon [ a, b]\to X$ with $\omega(b)=\omega(a)$.  A loop is {\em based at $x_0\in X$} if $\omega(a)=x_0$.
\end{definition}
%%-/

/-%%

\begin{definition}\label{homotopyloop}
A homotopy of loops is a one parameter family $\Omega\colon [a, b]\times [0, 1]\to X$ with $\Omega|_{[a, b]\times\{s\}}$
a loop for all $s\in [0, 1]$. A homotopy of loop based at $x_0$ is a one parameter family indexed by $[0, 1]$ of loops based at $x_0$.
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
Bu Corollary~\ref{expCP}  $exp^{-1}(\omega(a))\not=\emptyset$.
Fix a point $x\in exp^{-1}(\omega(a))$ and
 let $\tilde\omega_x\colon [a, b]\to \C$ be  lift of $\omega$ through the $exp$ with initial point $x$
as guaranteed by Corollary~\ref{expUPL}.
\end{proof}
%%-/

/-%%

 \begin{definition}\label{DefWNlift}
 Suppose given a loop $\omega\colon a\colon [a, b]\to \C$
 with $\omega(t)\in Cstar$ for all $t\in [a, b]$,
 and given a lift $\tilde\omega$ of $\omega$ through $exp$
 the {\em winding number} of the lift $\tilde\omega$,
 denoted $w(\tilde\omega)$,
 is $(\tilde\omega_x(b)-\tilde\omega_x(a))/2π  *I$.
\end{definition}
%%-/

/-%%

\begin{lemma}\label{diffinitpoint}
Let $\omega\colon [ a, b]\to \C$ with $\omega(t)\in Cstar$ for all $t\in [ a ,b]$.
Suppose that $\tilde\omega$ and $\tilde\omega'$ are lifts of $\omega$
through $exp$.
Then $w(\tilde\omega)\in \Z$ and
such that $w(\tilde\omega')=w(\tilde\omega)$.
\end{lemma}
%%-/

/-%%

\begin{proof}\uses{deflift, loop, periodicity, DefWNlift}
By the Definition~\ref{deflift} we have
 $exp(\tilde\omega(b))=\omega(b)$ and $exp(\tilde\omega(a)=\omega(a)$.
 By Definition~\ref{loop} $\omega(b)=\omega(a)$.
 This gives $exp(\tilde\omega(b))=exp(\tilde\omega(a))$.
 By Lemma~\ref{periodicity}, there is $k\in \Z$,
 such that $\tilde\omega(b)-\tilde\omega(b)=2π *k* I$.
 By Lemma~\ref{DefWNlift} the winding number of $\tilde\omega$ is $k$


If $\tilde\omega'$ is another lift of $\omega$, then for every $t\in [ a, b]$,
since $exp(\tilde\omega'(t))=exp(\tilde\omega(t))$,
there is an integer $k(t)\in \Z$ with
$\tilde\omega'(t)-\tilde\omega_x(t)=2π  k(t)*I$.
Since $\tilde\omega'$ and $\tilde\omega$ are continuous functions of $t$
so is $k(t)$.
Since the $[ a, b]$ is connected and $\Z$ is discrete, $k(t)$
is a constant function; i.e.,
there is an integer $k_0$ such that for all $t\in [ a, b]$, we have
$\tilde\omega'(t)=\tilde\omega(t)+2π * k_0*I$.
Thus, $\tilde ω'(b) -\tilde ω'(b)=\tilde ω'()-\tilde ω(a)$.
It follows from Definition~\ref{DefWNlift} $w(\tilde ω')=w(\tilde ω).$
\end{proof}
%%-/

/-%%

 \begin{corollary}\label{constWNomega}
 Let $\omega\colon [ a, b]\to \C$ be a loop with $\omega(t)\in Cstar$ for all $t\in [ a, b]$
 Let $X$ be the set of lifts of $\omega$. Then $X\not=\emptyset$ and there is a $w(\omega)\in \Z$
 such that for every $x\in X$ the winding number of the lift $\tilde\omega_x$ of $\omega$ through $exp$
 indexed by $x$ is $w(\omega)$.
 \end{corollary}
%%-/

/-%%

 \begin{proof}\uses{diffinitpoint, existlift}
 This is immediate from Lemmas~\ref{diffinitpoint} and Lemma~\ref{existlift}.
 \end{proof}
%%-/

/-%%

 \begin{definition}\label{WNloop}\uses{constWNomega}
 Suppose that $\omega\colon [ a, b ]\to \C$ is a loop with $\omega(t)\in Cstar$ for all $t\in [ a, b ]$.
 Then the constant $w(\omega)$ given in Corollary~\ref{constWNomega} is the {\em winding number of $\omega$}.
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

\begin{proof}\uses{homotopyloop, diffendpoint, constWNomega, expHLP}
By Definition~\ref{homotopyloop} $H(\{a\}\times I)=H(\{b\}\times I)$.
Let $\mu\colon I \to \C$ be this path.
By Corollary~\ref{expHLP} since the image of $H$ is contained in $Cstar$,
there  is a lift $\tilde H\colon [ a, b]\times I$ of $H$ through $exp$.
Then $\tilde H|_{\{a\}\times I}$
and $\tilde H|_{\{b\}\times I}$ are two liftings of $\mu$. So by Lemma~\ref{diffendpoint}
there is $n\in \Z$ such that
$\tilde H(b,1)-\tilde H(b,0)=\tilde H(a,1)-\tilde H(a,0)$.
Rewriting we have
$⁀ H(b,1)-⁀ H(a,1)= \tilde H(b,0)-\tilde H(a,0)$.
Since $\tilde H(t,0)$ is a lift of $\omega$ through $exp$ and  $\tilde H(t,0)$ is a lift of $\omega'$
through $exp$,  by Definition~\ref{WNloop}
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
the lift of a constant loop through $exp$ is a constant path. Thus, the endpoints of the lift of the constant loop
are equal and hence by Definition~\ref{WNloop} the winding number of a constant loop is zero.
\end{proof}
%%-/

/-%%

\begin{definition}\label{DefS1loop}
Given a map of the circle $\psi\colon S^1\to X$ the associated loop is
$\omega\colon [ 0, 2π  ]\to X$ is defined by $\omega(t)=\psi(exp(it))$.
\end{definition}
%%-/

/-%%

\begin{definition}\label{DefWNS1}
The winding number of a map $\rho\colon S^1\to \C$ with $\rho(z)\in Cstar$
for all $z\in S^1$  is the winding number of the associated loop.
\end{definition}
%%-/

/-%%

\begin{lem}\label{constS1}
If $f\colon S^1to \Cee$ is a constant map to a point $z\in Cstar$, then $w(f)=0$.
\end{lem}

\begin{proof}\uses{S1loop, DefWNS1, constpath}
By Definition~\ref{S1loop} the loop associated with the constant map $f\colon S^1\to Cstar$ is a constant loop
at a point of $Cstar$. By Lemma~\ref{DefWNS1} the winding number of $f$ is equal to the winding number of the constant loop at $f(S^1)\in Cstar$. By Lemma~\ref{constpath} this winding number is zero.
\end{proof}

%%-/


/-%%

\begin{lemma}\label{homotopic}
If $\psi, \psi'\colon S^1\to X$ are homotopic by a homotopy whose image lies in a subset $U$ of $X$  the loops
 associated to $\psi$ and $\psi$ are $\omega$ and $\omega'$, then there is a homotopy $H$ of loops whose image lies in $U$.
\end{lemma}
%%-/

/-%%

\begin{proof}\uses{DefS1loop, equalwinding,DefWNS1 }
Let $H\colon S^1\times I\to X$ be a homotopy from $\psi$ to $\psi'$.
Let $ω$ and $ω'$ be the loops associated to $ψ$ and $ψ'$ respectively
Define $\hat H\colon [ 0, 2π  ]\times [0,1]\to X$ by
$\hat H(t,s)=H(exp(it),s)$. Then by Definition~\ref{DefS1loop} $\hat H$ is a homotopy from
 the loop $\omega$ to the loop$\omega'$. The images of $H$ and $\hat H$ are the same
 so that the image of $\hat H$ lies in $Cstar$. By Lemma~\ref{equalwinding}
 the winding numbers of $\omega$ and $\omega'$ are equal. By Definition~\ref{DefWNS1} this means that the winding numbers of $\psi$
 that the winding numbers of $ψ$ and $ψ'$ are equal.
\end{proof}
%%-/

/-%%

\begin{corollary}\label{S1homotopy}
If $\psi,\psi'\colon S^1\to \C$ are maps whose images lie in $Cstar$
and there is a homotopy $H : S^1⁀s[0,1]→ ℂ$ from $ψ$ to $ψ'$  whose image lies in $Cstar$,
then the winding numbers of $\psi$ and $\psi'$ are equal.
\end{corollary}
%%-/

/-%%

\begin{proof}\uses{DefWNS1, equalwinding, DefS1loop}
By Definition~\ref{DefWNS1} we need only show that the winding numbers of the
paths associated to $\psi$ and $\psi'$
are equal
This is immediate from Lemmas~\ref{equalwinding}  and ~\ref{DefS1loop}.
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
Define a continuous map $J\colon S^1\times [0,1]\to D^2$ by
$(z,t)\mapsto (1-t)z$. Then $\hat f\circ J(z,0)= \rho(z)$ and
$\hat f\circ J(z,1)=\hat f(0)$ for all $z\in S^1$.
This is a homotopy in $Cstar$ from $\rho$ to a constant map of $S^1\to Cstar$.
By Lemma~\ref{S1homotopy} the winding number of $\rho$ is equal to the winding number
of a constant map $S^1\to C\star$.
By Lemma~\ref{constS1}, the winding number of a constant
map $S^1\to \hat f(0)\in Cstar$ is zero.
\end{proof}



ince there is a homotopy $H$ from $\rho$
to a constant map with image in $Cstar$, it follows from Corollary~\ref{S1homotopy} that the winding number of $\rho$ is zero.
\end{proof}

%%-/

/-%%


\section{Winding numbers at Infinity for complex polynomials}

%%-/

/-%%
\begin{lemma}\label{zkWNk}
For any $\alpha_0\in \C$ with $\alpha_0\not=0$ and any $k\in \Z$ $k>0$, define $\psi_{\alpha_0,k}\colon \C\to \C$ by $\psi_{\alpha_0,k}(z)=\alpha_0 z^k$.
 Then for any $R>0$  the winding number of the map of the restriction of $\psi_{\alpha_0,k}$ tothe circle of radius $R$
is $k$
\end{lemma}
%%-/

/-%%

\begin{proof}\uses{DefS1loop, multiplicativity, expCP, WNloop}
By Definition`\ref{DefS1loop} and by Lemma~\ref{multiplicativity} the loop  $\omega\colon [ 0, 2π  ]\to \C$ associated to $\psi_{\alpha_0,t}$ restricted to the circle of radius $R$ is given by
$\omega(t)= \alpha_0 R^kexp(kt *I)$.

By Lemma~\ref{expCP} there is an $\tilde\alpha_0\in \C$ with $exp(\tilde\alpha_0)=\alpha_0 R^k$.
Define $\tilde\omega(t)=\tilde\alpha_0+kt *I$ for $[0\le t\le 2π $.
Then by Lemma~\ref{multiplicativity}
$$exp(\tilde\alpha_0 +kt*I)=\alpha_0 R^kexp (kt*I).$$
By Definition~\ref{deflift} this means that $\tilde\omega$ is a lift of $\omega$ through $exp$.
By Definition~\ref{WNloop}  $w(\omega)=(2π  k*I-0)/2π  * I * k$.
By Definition~\ref{DefWNS1}, this means that the winding number of $\psi_{\alpha_0,k}$ is $k$.
\end{proof}

%%-/

/-%%
\begin{lemma}\label{walkingdog}
Suppose that $\psi\colon S^1\to \C$ and $\psi'\colon S^1\to \C$ are maps
and for each $z\in S^1$, we have $|\psi(z)-\psi'(z)|<|\psi(z)|$. Then there is a homotopy $H$ from $\psi$ to $\psi'$ whose image lies in $Cstar$.
\end{lemma}
%%-/

/-%%

\begin{proof}
Since for all $t\in [ a, b ]$, $|\psi(t)-|\psi'(t)|<|\psi(t)|$, it follows that $|\psi(t)|>0$ and $|\psi'(t)|>0$ for all $t\in [ a, b ]$.
Define a homotopy $H\colon [ 0, 2π ]\times I\to \C$ by
$H(s,t)=t\psi'(s)+(1-t)\psi(s)$.
$H(s,0)=\psi(s)$ and $H(s,1)=\psi'(s)$, so $H$ is a homotopy from $\psi$ to $\psi'$. Also, by Definition~\ref{loop}
$\psi(b)=\psi(a)$ and $\psi'(b)=\psi'(a)$. It follows that $H(a,t)=H(b,t)$ for all $t\in [ 0, 1 ]$. That is to say $H$ is a homotopy of loops.

We establish that $H(s,t)\not= 0$ for all $s\in [ 0, 2π  ]$ and $t\in [ 0, 1 ]$.
For $s$ every point $|\psi(s)-(t\psi(s)-(1-t)\psi'(s)|=|(1-t)(\psi-\psi')|$. Since $0\le t\le 1$, $0\le (1-t)\le 1$.
Then, $|\psi(s)-H(s,t)|=|\psi(s)-(t\psi(s)-(1-t)\psi'(s)|=(1-t)|\psi(s)-\psi'(s)|<|\psi(s)|$.
So $H(s,t)\not=0$ for all $s\in [ a, b ]$ and all $t\in[ 0, 1 ]$.

Consequently, $H$ is a homotopy of loops  from $\psi$ to $\psi'$ whose image lies in $Cstar$. By Lemma~\ref{S1homotopy} the $w(\psi)=w(\psi')$.
\end{proof}
%%-/

/-%%

\begin{corollary}\label{sameWN}
Suppose that $\psi,\psi'\colon S^1\to \C$ with $|\psi(z)-\psi'(z)|<|\psi(z)|$
for all $s\in [ 0, 2π  ]$. Then $\psi$ and $\psi'$ have the same winding number.
\end{corollary}
%%-/

/-%%

\begin{proof}\uses{walkingdog, S1homotopy}
According to Lemma~\ref{walkingdog} there is a homotopy of loops from $\psi$ to $\psi'$ with image in  $Cstar$.
Thus, by Corollary~\ref{S1homotopy}, $\psi$ and $\psi'$ have the same winding number.
\end{proof}
%%-/

/-%%




\begin{lemma}\label{zkdominates}
Let $p(z)$ be a complex polynomial of degree $k$; i.e., $p(z)=\sum_{i=0}^k\alpha_iz^{k-i}$ with $\alpha_i\in \C$ and $\alpha_0\not= 0$.
For all $R$ sufficiently large $|\alpha_0|R^k>|p(z)-\alpha_0z^k|$ for any $z$ with $|z|=R$.
\end{lemma}
%%-/

/-%%

\begin{proof}
For each $1\le i\le k$ set $\beta_i=\alpha_i/\alpha_0$
Choose $R>\sum_{i=1}^k|\beta_j|$ and $R>1$.
For any $z\in \C$ with $|z|=R$, we have
$$
|p(z)-\alpha_0z^k|=|\sum_{i=1}^k\alpha_iz^{k-i}|  \le  \sum_{i=1}^k|\alpha_i|R^{k-i}=|\alpha_0|\sum_{i=1}^k|\beta_i|R^{k-1}
<|\alpha_0|R^k=|\alpha_0R^k|.$$
\end{proof}
%%-/

/-%%

\begin{theorem}\label{WNthm}
Let $f(z)=p(z)$ be a complex polynomial of degree $k>1$. Then for $R$ sufficiently large,
the winding number of the path $[ 0, 2π  ]\to \C$ given by
$t\mapsto f(Rexp(t*I))$
is a loop  with winding number $k$.
\end{theorem}
%%-/

/-%%

\begin{proof}\uses{zkWNk, zkdominates, walkingdog}
By Lemma~\ref{zkdominates} for $R>{\rm max}(1,\sum_{i=1}^k|\beta_j|)$,
and for any $z\in \C$ with $|z|=R$
$|p(z)-\alpha_0z^k| <||\alpha_0 R^k|$. By Lemma~\ref{walkingdog} the loops $\alpha_0Rexp(k t *I))$ and
$p(Rexp( t *I)$ defined on $0\le t\le 2π $ have the same winding number.

But according the Lemma~\ref{zkWNk}
the latter has winding number $k$.
\end{proof}

%%-/

/-%%


\begin{theorem}\label{Thereexistroot}
Every complex polynomial of degree $k>0$ has a complex root.
\end{theorem}
%%-/

/-%%

\begin{proof}\uses{WNthm, boundsWN0}
The proof is by contradiction. Suppose that $p(z)=\sum_{i=0}^k\alpha_iz^{k-i} $ with $\alpha_0\not= 0$. Suppose that
$p(z)\not= 0$ for all $z\in \C$.
By Theorem ~\ref{WNthm} fix $R>0$ sufficiently large that the winding number of the restriction of $p(z)$ to the circle of radius $R$ is $k$.


 Let $D^2\to \C$ be the map $z\mapsto Rz$.
Define $\rho\colon D^2\to \C$ by $z\mapsto p(Rz)$. The restriction of this map to the boundary circle
is the restriction of $p(z)$ to the circle of radius $R$.
Since $p(z)\not=0 $ for all $z\in \C$, the image of $\rho$ is contained in $Cstar$.
According to Lemma~\ref{boundsWN0}, this implies that the winding number of
of $p$ on the circle of radius $R$ is zero.

Since $k>0$, this is a contradiction.
\end{proof}


%%-/
