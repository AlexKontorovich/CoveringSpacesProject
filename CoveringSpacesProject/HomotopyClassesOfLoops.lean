import CoveringSpacesProject.ExpCovering

/-%%
\section{Homotopy Classes of Loops and maps of $S^1$ in $\C^*$}

\begin{definition}
Let $X$ be a topological space.  A {\em loop} in $X$ is a map $\omega\colon [a,b]\to \C^*$ with $\omega(b)=\omega(a)$.  A loop is {\em based at $x_0\in X$} if $\omega(a)=x_0$.
\end{definition}

\begin{definition}
A homotopy of loops is a one parameter family $\Omega\colon [a,b]\times [0,1]\to X$ with $\Omega|_{[a,b]\times\{s\}}$
a loop for all $s\in [0,1]$. A homotopy of loop based at $x_0$ is a one parameter family indexed by $[0,1]$ of loops based at $x_0$.
\end{definition}


Let $\omega\colon [a,b]\to \C^*$ be a loop.
Since ${\rm exp}\colon \C\to \C^*$, we have ${\rm exp}^{-1}(\omega(a)\not=\emptyset$.
Fix a point $x\in {\rm exp}^{-1}(\omega(a))$ and
 let $\tilde\omega_x\colon [a,b]\to \C$ be  lift of $\omega$ through the exp with initial point $x$
as guaranteed by Corollary~\ref{exp_UPL}.
 .

\begin{lemma}
$\tilde\omega_x(b)-\tilde\omega_x(a)\in (2\pi *I)\Z$.
If $x,y\in {\rm exp}^{-1}(\omega(a)$, then
The difference $\tilde\omega_y(b)-\tilde\omega_y(a) =\tilde\omega_x(b)-\tilde\omega_x(a)\in (2\pi *I)\Z$.
\end{lemma}

\begin{proof}
Since ${\rm exp}(\tilde\omega_x(b))={\rm exp}(\tilde \omega_x(a))$ by Lemma~\ref{periodicity}, it follows that
$\tilde\omega_x(b)-\tilde\omega_x(a)\in (2\pi *I)\Z$.

If $\tilde\omega_y$ is another lift of $\omega$, then for every $t\in [a,b]$, since ${\rm exp}(\tilde\omega_y(t))={\rm exp}(\tilde\omega_x(t))$, there is an integer $n(t)\in \Z$ with  $\tilde\omega_y(t)-\tilde\omega_x(t)=2\pi n(t)*I$.
Since $\tilde\omega_y$ and $\tilde\omega_x$ are continuous functions of $t$ so is $n(t)$. Since the $[a,b]$ is connected and $\Z$ is discrete, $n(t)$ is a constant function; i.e., there is an integer $n$ such that for all $t\in [a,b]$, we have
$\tilde\omega_y(t)=\tilde\omega_x(t)+n$.
Thus,
$$\tilde\omega_y(b)-\tilde\omega_y(a)=\tilde \omega_x(b)+n-(\tilde\omega_x(a)+n)=\tilde\omega_x(b)-\tilde\omega_x(a).$$
 \end{proof}

 \begin{definition}
 The {\em winding number of a loop $\omega$ in $\C^*$}, denoted $w(\omega)\in \Z$, is $(\tilde\omega_x(b)-\tilde\omega_x(a)/2\pi *I$
for any $x\in {\rm exp}^{-1}\omega(a)$; i.e., for any lift $\tilde\omega$ of $\omega$ through ${\rm exp}$.
\end{definition}

\begin{lemma}\label{equalwinding}
If $\omega$ and $\omega'$ are homotopic loops then $w(\omega)=w(\omega')$
\end{lemma}

\begin{proof}
Let $H\colon [a,b]\times I\to \C^*$ be a homotopy from $\omega$ to $\omega'$.
Since $H$ is a homotopy of loops, $H(\{a\}\times I)=H(\{b\}\times I)$
Let $\mu\colon I \to \C^*$ be this path.
By homotopy lifting $\tilde H\colon [a,b]\times I$ of $H$. Then $\tilde H|_{\{a\}\times I}$
and $\tilde H|_{\{b\}\times I}$ are two liftings of $\mu$. So there is $n\in \Z$ such that
$\tilde H(b,t)-\tilde H(a,t)=n$. Evaluating at $t=0$ gives $\tilde H(b,0)-\tilde H(a,0)=n$.
Since $\tilde H(s,0)$ is a lift of $\omega$,  $w(\omega)=n$.
Evaluating at $t=1$ gives $\tilde H(b,1)i\tilde H(a,1)=n$. Since $\tilde H(s,1)$ is a lift of $\omega'$,
$w(\omega')=n$.
\end{proof}

\begin{corollary}[constpath]\label{constpath}
Suppose that $\omega$ is homotopic to a constant loop. Then
the winding number of $\omega$ is zero
\end{corollary}

\begin{proof}
By Lemma~\ref{equalwinding} the winding number of the loop $\omega$
is equal to the winding number of a constant loop. By unique path lifting
the lift of a constant loop is a constant path. Thus, the endpoints of the lift
are equal and hence the winding number of a constant loop is zero.
\end{proof}

\begin{definition}
Given a map of the circle $\psi\colon S^1\to X$ the associated loop is
$\omega\colon [0,2\pi]\to X$ is defined by $\omega(t)=\psi({\rm exp}(it))$.
\end{definition}

\begin{definition}
The winding number of a map $S^1\to \C^*$ is the winding number of the associated loop.
\end{definition}

\begin{lemma}[homotopic]\label{homotopic}
If $\psi, \psi'\colon S^1\to X$ are homotopic, the the resulting loops are homotopic.
\end{lemma}

\begin{proof}
Let $H\colon S^1\times I\to X$ be a homotopy from $\psi$ to $\psi'$
Define $\hat H\colon [0,2\pi]\times I\to X$ by
$\hat H(t,s)=H({\rm exp}(it),s)$. Then $\hat H$ is a homotopy between the loops
 determined by $\psi$ and $\psi'$.
\end{proof}

\begin{corollary}\label{S1homotopy}
If $\psi,\psi'\colon S^1\to \C^*$ are homotopic, then the winding numbers of
$\psi$ and $\psi'$ are equal.
\end{corollary}

\begin{proof}
By Lemmas~\ref{equalwinding} and~\ref{homotopic}.
\end{proof}

\begin{lemma}\label{bounds}
If $f\colon S^1\to X$ extends to a map of the unit disk $\hat f\colon D^2\to X$, the $f$
is homotopic to a constant map of $S^1\to X$. \end{lemma}

\begin{proof}
Suppose there is $\hat f\colon D^2\to X$ with $\hat f|_{S^1}=f$,
Define a continuous map $J\colon S^1\times [0,1]\to D^2$ by
$(z,t)\mapsto (1-t)z$. Then $\hat f\circ J(z,0)= f(z)$ and $\hat f\circ J(z,1)=\hat f(0)$.
Thus, $\hat f\circ J$ is a homotopy from $f$ to a constant map of $S^1\to X$.
\end{proof}


\begin{corollary}\label{disk_ext_impies_wn_0}
If $\psi\colon S^1\to \C^*$ extends to a continuous map $\hat\psi\colon D^2\to \C^*$,'
then the winding number of $\psi$ is zero.
\end{corollary}

\begin{proof}
By Lemma~\ref{bounds} $\psi$ is homotopic to a constant map. By Corollary~\ref{S1homotopy}
the winding number of $\psi$ is equal to the winding number of a constant map of $S^1\to \C^*$.
The loop associated to a constant map of
$S^1\to X$ is a constant loop which  as $0$ winding number by Corollary~\ref{constpath}.
\end{proof}

\section{Winding numbers at Infinity for complex polynomials}

\begin{lemma}[zk_windingnumber_k]\label{zk_windingnumber_k}
For any $r>0$ define $\psi_r\colon S^1\to \C^*$ by $\psi_r(t)=r{\rm exp}(t *I)$ for $0\le t\le 2\pi$.
For $k \in N$ let   $R_k\colon \C^*\to \C^*$ be $z\mapsto z^k$. Then the winding number of the map
$S^1\to \C^*$ given by $t \mapsto R_k(\psi_r(t))$ has winding number $k$.
\end{lemma}

\begin{proof}
The associated path is $\omega\colon [0,2\pi]\to \C^*$ given by
$t\mapsto (r{\rm exp}(t *I))^k=r^k{\rm exp}(k* I)$.
A lift through ${\rm exp}$ of this map is $\tilde\omega(t)=k{\rm log}_\R(r)+k* t *I$.
The difference of the endpoints is $2k\pi *I$ and hence the winding number of $z^k$ is $k$.
\end{proof}

\begin{lemma}[walkingdog]\label{walkingdog}
Suppose that $\psi\colon S^1\to \C^*$ and $\psi'\colon S^1\to \C^*$ are maps
and for each $z\in S^1$, we have $|\psi(z)-\psi'(z)|<|\psi(z)|$. Then $\psi$ and $\psi'$ are homotopic in $\C^*$.
\end{lemma}

\begin{proof}
Define a homotopy $H\colon [0,2\pi]\times I\to \C$ by
$H(s,t)=t\psi'(s)+(1-t)\psi(s)$.
We establish that $H(s,t)\not= 0$ for all $s\in [0,2\pi]$ and $t\in [0,1]$.
For each $s$, $\psi'(s)\in B=B(\psi(s),|\psi(s)|)$. Thus the straight line $L(s)=\{t\psi'(s)+(1-t)\psi(s); 0\le t\le 1\}$
lies in $B$. The origin does not lie in $B$, so the straight line $L$ is disjoint from the origin. Since this is true for each $s$,
$H(s,t)\in \C^*$ for all $s,t$.
Consequently, $H$ is a homotopy in $\C^*$ from $\psi$ to $\psi'$ and by Lemma~\ref{S1homotopy} the $w(\psi)=w(\psi')$.

\end{proof}

\begin{corollary}
Suppose that $\psi,\psi'\colon S^1\to \C^*$ with $|\psi(z)-\psi'(z)| < |\psi(z)|$
for all $s\in [0,2\pi]$. Then $\psi$ and $\psi'$ have the same winding number.
\end{corollary}

\begin{proof}
According to Lemma~\ref{walkingdog} $\psi$ and $\psi'$ are homotopic in $\C^*$.
Thus, by Corollary~\ref{S1homotopy}, $\psi$ and $\psi'$ have the same winding number.
\end{proof}



\begin{thm}[windingnumberthm]\label{windingnumberthm}
Let $f(z)=p(z)$ be a complex polynomial of degree $k>1$. Then for $R$ sufficiently large,
the winding number of the path $[0,2\pi]\to \C$ given by $t\mapsto f(R{\rm exp}(t*I))$
is a loop in $\C^*$ and has winding number $k$.
\end{thm}


\begin{proof} First some preliminary claims and lemmas.

\begin{claim}[multiplyclaim]\label{multiplyclaim}
Let $\omega$ be a loop in $\C^*$ and $a_0\in \C^*$. Then  $w(a_0\omega)=w(\omega)$.
\end{claim}

\begin{proof}
$\C^*$ is path connected so there is a path $a\colon [0,1]\to \C^*$
with $a(0)=a_0$ and $a(1)=1$. This gives a homotopy $a(t)\omega$
between $a_0\omega$ an $\omega$. Thus, by Lemma~\ref{homotopic}
$w(a_0\omega)=w(\omega)$.
\end{proof}

We write $f(z)=\sum_{i=0}^k\alpha_iz^{k-i}$ with $\alpha_0\not= 0$.
Our loop is $f(R{\rm exp}(t*I)$. Multiplying this  $\alpha_0^{-1}$ and invoking Claim~\ref{multiplyclaim}
we can replace $p(z)$ by $q(z)= z^k+\sum_{i=1}^k \alpha_i/\alpha_0z^{k-i}$.
Define $\beta_i=\alpha_i/\alpha_0$.
\begin{claim}
For all $R$ sufficiently large $R^k>|\sum_{i=1}^k\beta_iz^{k-i}|$ for any $z$with $|z|=R$.
\end{claim}

\begin{proof}
Choose $R>\sum_{i=1}^k|\beta_j|$ and $R>1$.
Since $R>1$, we have
$$
|\sum_{i=1}^k\beta_iz^{k-i}| & \le & \sum_{i=1}^k|\beta_i|R^{k-i}\le (\sum_{i=1}^k|\beta_i|)R^{k-1}
< R^k.
$$

Then by Lemma~\ref{walkingdog} for $R>{\rm max}(1,\sum_{i=1}^k|\beta_j|)$, the loop $f(R{\rm exp}(t*I)$
and the loop $R{\rm exp}(t*I)$ have the same winding number. But according the Lemma~\ref{zk_windingnumber_k}
the latter has winding number $k$.
\end{proof}

\begin{corollary}
Every complex polynomial of degree $k>0$ has a complex zero.
\end{corollary}

\begin{proof}
Suppose $p(z)$ is a complex polynomial of degree $k>0$ with no zero. According to
Theorem~\ref{windingnumberthm}, the winding number of the restriction of $p(z)$ to a circle of radius $R$ sufficiently large is $k$. If $p(z)$ has no zero then the polynomial restricted to the disk of radius $R$ defines an extension
of $t\mapsto p(R{\rm exp}(t*I)$ to a map from $\overline{D(0,R)}$ to $\C^*$. This is a contradiction, since by
Corollary~\ref{disk_ext_impies_wn_0}, this extension of the map on the circle of radius $R$  to a map of the closed disk $\overline{ D(0,R)}\to \C^*$. implies that the winding number of the map on the boundary circle is $0$.
\end{proof}

%%-/
