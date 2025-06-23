import Mathlib
/-%%
This is section two of the Covering Spaces project.
%%-/

/-%%
\begin{theorem}[TheoremTwo]\label{TheoremTwo}\lean{TheoremTwo}\leanok
This is the second theorem.
\end{theorem}
%%-/
theorem TheoremTwo : True := by
  trivial
/-%%
\begin{proof}\uses{TheoremOne}
The proof is trivial, but uses Theorem \ref{TheoremOne}.
\end{proof}
%%-/
