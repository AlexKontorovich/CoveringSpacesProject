import Mathlib

/-%%
\section{Unique Path Liftiing}
\begin{definition}[IsLift]\label{IsLift}\lean{IsLift}\leanok
Let $f\colon X\to Y$. A {\em lift of a map $\alpha\colon A\to Y$ through $f$} is a map
$\tilde\alpha\colon A\to X$ such that $f\circ \tilde \alpha=\alpha$.
\end{definition}
%%-/
def IsLift {X Y A : Type*}
    (f : X → Y) (α : A → Y) (α' : A → X) : Prop :=
  f ∘ α' = α

/-%%
\begin{definition}
Let $f\colon X\to Y$ be a map. An open set $U\subset Y$ is {\em evenly covered by $f$} if there exist a discrete space $F$
and a homeomorphism $\rho\colon F\times U\to f^{-1}(U)$ with the property that $f\circ \rho\colon F\times U\to U$
is projection onto the second factor. The choice of $(F,\rho)$ with these properties is a {\em sheet structure} on $f^{-1}(U)$.
The {\em sheet indexed by $x\in F_U$} is $\rho(\{x\}\times U)$.
\end{definition}

\noindent
{\bf N.B.} Given $U$ evenly covered by $f$, if $U$ is not connected, there can be different notions of the sheets above $U$.

\begin{definition}
A map $\pi\colon P\to B$ is a {\em covering projection} if it is surjective and every
point $x\in B$ has an evenly covered open neighborhood.
\end{definition}

\begin{lemma}[sheet]\label{sheet}\lean{sheet}
Let $f\colon X\to Y$ be a map, $U\subset Y$ an open set of $Y$ that is evenly covered by $f$, and  ${\mathcal S}=(F_u,\rho_U)$ a sheet structure on $f^{-1}(U)$. Let $A$ be a connected space and $\varphi\colon A\to U\subset Y$.
Then the lifts of $\varphi$ through $f$ are exactly the  maps  $A\to Y$ of the form $a\mapsto \rho_U(x,\varphi(a))$
for $x\in F_U$.
\end{lemma}

\begin{proof}
Since $\varphi(A)\subset U$ for any lift $\tilde \varphi\colon A\to X$ had image contained in $f^{-1}(U)$.
Since $A$ is connected and the  sheets are disjoint, open subsets of $X$ and $\varphi(A)$ is contained in their union,
$\varphi(A)$ is contained in one of them, say $\rho_U(\{x\}\times U)$. The map $u\mapsto \rho_U(x,u)$
is the inverse to the projection of $\rho_U(\{x\}\times U)\to U$. Thus, if $\tilde\varphi\colon A\to \rho_U(\{x\}\times U)$
and $\pi\circ \tilde \varphi=\varphi$, it follows that $\tilde\varphi(a)=\rho_U(x,\varphi(a))$.
\end{proof}

\begin{corollary}[cor4]\label{cor4}\lean{cor4}
Let $\pi\colon P\to B$ be a covering space. Let $U\subset B$ be an open subset that is evenly covered and let
${\mathcal S}=(F_U,\rho_U)$ be a sheet structure for $\pi^{-1}(U)$. Let $\alpha\colon [a,b]\to B$ have image contained in $U$.
For each $x\in F_U$, $\tilde\alpha(t)=\rho_U((x,\alpha(t)))$ is a lift of $\alpha$ through $\pi$ and
any lifting of $\alpha$ through $\pi$ is of the form $\tilde\alpha_x(t)=\rho_U((x,\alpha(t)))$ for some $x\in F_U$.
\end{corollary}

\begin{proof}\uses{sheet}
$[a,b]$ is connected so we can apply Lemma~\ref{sheet}
\end{proof}

Fix a covering projection $\pi\colon P\to B$.

The key ingredient in all the arguments is the notion of the data required to construct a lift through $\pi$ of a map of an interval $[a,b]$ to the base $B$.

\begin{definition}[Lifting Data]\label{LiftingData}\lean{LiftingData}
{\em Lifting Data} consists of the following:
\begin{itemize}
\item[(i)] $n\in \mathbb{N}$  with $n\ge 1$.
\item[(ii)] For all $0 \le i\le n$ a point $t_i\in [a,b]$,  subject to:
\item[(iii)] $t_0=a, t_n=b$ for all $1\le i\le n$ and  $t_{i-1}< t_i$.        (THIS DIVIDES $[a,b]$ INTO SUB-INTERVLS)
\item[(iv)] For $0\le i < n$ evenly covered open sets $U_i \subset B$ with $U_i\cap U_{I+1}$ non-empty. EVENLY COVERED OPEN SETS
\end{itemize}
\end{definition}

\begin{definition}[sheet structure]\label{sheetstructure}\lean{sheetstructure}
A sheet structure for Lifting Data $(n,t_i,U_i)$ is the following. For all $0\le i < n$  a sheet structure ${\mathcal S}_i=(F_{U_i},\rho_{U_i})$ for $\pi^{-1}(U_i)$.
\end{definition}

By definition of an evenly covered open set, any Lifting Data has a sheet structure.

\bigskip

 COMPATIBILITY OF A PATH WITH LIFTING DATA:

 \begin{definition}
  Given a path $\omega \colon [a,b] \to B$ then lifting data LD is  {\em compatible with $\omega$}  if  for all $0 \le i < n$ we have $\omega([t_i,t_{i+1}])\subset U_i$.
\end{definition}


\begin{definition}
Given $\omega\colon [a,b]\to B$, lifting data compatible with $\omega$ with sheet structure and a choice of sheets $\tilde U_i$ in $\pi^{-1}(U_i)$, the {\em corresponding  lifts $\tilde\omega|_{[t_i,t_{i+1}]}$
of the $\omega|_{[t_i,t_{i+1}]}$}  are the lifts contained in $\tilde U_i$. These lifts {\em fit together} if and only if
for each $1\le i\le n-1$ we have  $\tilde\omega|_{[t_{i-1},t_i]}$ and $\tilde \omega_{[t_i,t_{i+1}]}$ agree at the point $t_i$.
\end{definition}

\begin{lemma}[partcomp]\label{partcomp}\lean{partcomp}
Given $\omega\colon [a,b]\to B$, lifting data compatible with $\omega$ with sheet structure and a choice of sheets $\tilde U_i$ in $\pi^{-1}(U_i)$ so that the resulting lifts fit together, then there is a unique lift $\tilde\omega$ of $\omega$
so that  fir each $1\le i\le n$ the restriction of $\tilde\omega$ to $[t_{i-1},t_i]$ agrees with the partial lift of $\omega|_{[t_{i-1},t_i]}$ given by the sheets $\tilde U_i$.
\end{lemma}

\begin{proof}
Since the various partial lifts agree at the common endpoints, together they define a function $\tilde\omega\colon [a,b]\to P$. This function is continuous on each of the closed intervals $[t_{i-1},t_i]$. Hence it is continuous.
Since the partial lifts are lifts of the restriction of $\omega$, $\tilde\omega$ is a lift of $\omega$.
\end{proof}


\begin{definition}
In the context of the lemma we say a choice of sheets $\tilde U_i$ in $\pi^{-1}(U_i)$ is {compatible with $\omega$}
if the endpoints of the partial lift agree at the common endpoints. If we are also given an initial lift $\tilde a_0\in \pi^{-1}(\omega(a))$, we say a choice of sheets $\tilde U_i$ is {compatible with $\omega$ and $\tilde a_0$} if
the lifts are compatible with $\omega$ and $\tilde a_0\in \tilde U_0$.
\end{definition}


\begin{lemma}
Given $\omega\colon [a,b]\to B$ and $\tilde a_0\in \pi^{-1}(\omega(a))$, if the sheets $\tilde U_i$ are
compatible with $\omega$ and $\tilde a_0$, then the resulting lift $\tilde \omega$ has $\tilde a_0$ as initial point.
\end{lemma}

\begin{proof}
$\tilde a_0\in \tilde U_0$ and lies in $x\pi^{-1}(\omega(a))$.
\end{proof}

Existence and uniqueness of path lifting comes from the following theorem, which is proved by induction on n, the length of the liftiing data.



\begin{theorem}
Let $\pi\colon P\to B$ be a covering projection. Let $\omega\colon [a,b]\to B$ be a map.
There exist lifting data compatible with  $\omega$.

Fix lifting data compatible with  $\omega$ and for $0\le i < n$  a sheet structure for  $\pi^{-1}(U_i)$.
Fix $\tilde a_0\in \pi^{-1}(\omega(a))$. Then there is a unique choice of sheets $\tilde U_i\in \pi^{-1}(U_i)$
compatible with $\omega$ and $\tilde a_0$.
These choices lead to a lift $\tilde\omega\colon [a,b]\to P$ of $\omega$ through $\pi$ with initial point $\tilde\omega(a)$
This is the only lift of $\omega$ with initial point $\tilde a_0$.
\end{theorem}

\begin{proof}
First, we prove the existence of lifting data compatible with $\omega$.
Given $\omega\colon [a,b]\to B$ for each $x\in [a,b]$ there is a relative open interval  $I_x\subset [a,b]$ containing $x$
such that $\omega(I_x)$ is contained in an evenly covered open subset $U_x$ of $B$. By the compactness of $[a,b]$, there
is a finite collection of the $I_x$ that cover $[a,b]$. We label these $I_1,\ldots,I_k$ and for each $i$ there is an evenly covered open set $U_i\subset B$ with $\omega(I_i)\subset U_i$.
We argue by induction on $k$,   the number of elements in the covering. If the number is one, then $n=1$,, $t_0=a$, $t_1=b$ and $U_0$ is the evenly covered open set containing $\omega([a,b])$.

Now suppose that $k\ge 2$ we have established the existence for covers with fewer that $k$ elements
and our cover has exactly $k$ elements.
Renumbering we can assume that $a\in I_1$.
If $I_1$ contains $b$, then $I_1=[a,b]$ and we are in the case $k=1$.

Otherwise, let $x$ be the upper limit of $I_1$. It is not contained in $I_1$, so, after renumbering, there is $I_2$ with $x\in I_2$
choose $t_1\in I_1\cap I_2$ with $t_1>a$. The interval $[a,t_1]\subset I_1$, and the interval
$[t_1,b]$ is contained in the union of the intervals covering $[a,b]$ with $I_1$ removed since $[t_1,x]\subset I_2$.
Thus, by induction there is lifting data compatible with $(n,t'_i ,U'_i)$ for $\omega'\colon [t_1,b] \to B$ defined by $\omega'(t)=\omega(t)$ for all $t\in [t_1,b]$.
For $i\ge 2$ we set $t_i=t'_{i-1}$ and $U_{i}=U'_{i-1}$. We set $U_0$ equal to an evenly covered open set containing
$\omega(I_1)$.  Then $(n,t_i,U_i)$ is lifting data for $\omega$.

Now suppose that we have lifting data compatible with $\omega$. For $0\le i < n$ fiix   sheet structures for $\pi^{-1}(U_i)$.
Suppose also that we have sheets $\tilde U_i$ in $\pi^{-1} U_i$ compatible with $\omega$ and $\tilde a_0$. Then by Lemma~\ref{partcomp}, the results partial lifts of the $\omega$
fit together to determine a lift of $\omega$. By construction, the initial point of this lift is $\tilde a_0$.

It remains to prove  that given the lifting data compatible with $\omega$ and sheet structure for the $U_i$, there exist a unique choice of sheets $\tilde U_i$ compatible with $\omega$ and $\tilde a_0$.
We prove this by induction on $n$. If $n=1$ there is only one open set $U_0$ to consider and the only condition is $\tilde a_o\in \tilde U_0$.
There is a unique sheet $\tilde U_0$ containing $\tilde a_0$.

Suppose by induction that we have established the uniqueness for $n-1$ for some $n\ge 2$ and we will establish it for $n$.
We begin by choosing the sheet $\tilde U_0$ to contain $\tilde a_0$. Any compatible choice of sheets must have $\tilde U_0$ as its choice of sheet over $U_0$ since this sheet is required to contained $\tilde a_0$.
We have the partial lift of $\omega|_{[a,t_1]}$ to the sheet $\tilde U_0$. Denote this lift by
$\tilde\omega_0$.
Now replace $\omega\colon [a,b]\to B$ by $\omega'=\omega|_{[t_1, b]}$ and take $\tilde\omega_0(t_1)\in\pi^{-1}(\tilde\omega_0(t_1))$ as initial condition. For $0\le i< n$
Set $t_i'=t_{i+1}$ and for $0\le i< n-1$ set $U'_i=U_{i+1}$. Then $(n-1,t'_i,U'_i)$ are lifting data for $\omega'$
Take as initial point for $\omega'$ to be $\tilde\omega_0(t_1)$.
By induction there is a unique choice of sheets $\tilde U_i'$ compatible with $\omega'$ and  $\tilde\omega_0(t_1)$.
We have already fixed $\tilde U_0$.
For $1\le i< n_2$, set $\tilde U_i =\tilde U'_{i-1}$. Then the $\tilde U_i$ are compatible with $\omega$ and $\tilde a_0$.
This proves the existence of sheets $\tilde U_i$ as required.

But we have already seen that $\tilde U_0$ is uniquely determined by the lifting data compatible with $\omega$
its sheet structure.  Hence, the initial point $\omega_0(t_1)$ for the lift of $\omega'$ is also unique given the
 covering data. The uniqueness of the choice of sheets compatible with
$\omega$ and $\tilde a_0$ now follows.

Lastly, we must show that the lift $\tilde\omega$ of $\omega$ with initial point $\tilde a_0$ is unique.
Suppose that $\tilde\omega'$ is a lift of $\omega$ with initial point $\tilde a_0$.  The set of $t\in [a,b]$ for which
$\tilde\omega'(t)=\tilde\omega(t)$ is closed. We show that it is also open. Suppose that
for some $t\in [a,b]$ we have $\tilde\omega'(t)=\tilde\omega(t)$. There is $0\le i < n$ such that $t\in [t_i,t_{i+1}]$.
Hence, $\tilde\omega'(t)=\tilde\omega(t)\in \tilde U_i$. By continuity there is a relatively open interval $I\subset [a,b]$
with of $t\in I$ and $\tilde\omega(I)\subset \tilde U_i$ and $\tilde\omega'(I)\in \tilde U_i$.
Since the projection $B$ of $\tilde\omega$ and $\tilde\omega'$ are equal and because the projection of
$\tilde U_i\to B$ is an injection, it follows that $\tilde\omega'|_I=\tilde\omega|_I$. This proves that the subset of
$[a,b]$ where $\tilde\omega=\tilde\omega'$ is open. Since $[a,b]$ is connected, the subset $\{t| \tilde\omega'(t)=\tilde\omega(t)\}$ is either the empty set of all of $[a.b]$. But $\tilde\omega(a)=\tilde\omega(a)$,
so that $\tilde\omega'=\tilde\omega$.
\end{proof}

\begin{corollary}
Let $\pi\colon P\to B$ be a covering projection. Let $\omega\colon [a,b]\to B$ be a path and let $\tilde a_0\in \pi^{-1}(\omega(a)$.  Then there is a unique lifting $\tilde \omega\colon [a,b]\to P$ of $\omega$ with initial point $\tilde a_0$.
\end{corollary}
%%-/
