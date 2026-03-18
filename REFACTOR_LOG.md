# Refactor Log

## 2026-03-18

### Current cleanup list

1. [done] Generalized `ContinuousMap.exists_homotopy_of_norm_sub_lt` in
   `CoveringSpacesProject/RootsMathlib.lean` from `Circle` to an arbitrary
   `α : Type*` with `[TopologicalSpace α]`.
   Note: `ContinuousMap.windingNumber_eq_of_norm_sub_lt` remains circle-specific because the
   current winding-number API itself is circle-specific.

2. [done] Factored out the repeated “two lifts differ by an integer multiple of `2 * π * I`”
   argument in `CoveringSpacesProject/ComplexPathWinding.lean`.
   Note: the shared bookkeeping now lives in a private helper comparing two lifts of the same path,
   and both `windingNumber_eq_of_lift` and `windingNumber_eq_of_homotopy` use it.

3. Reassess the right abstraction and naming for
   `{z : ℂ // z ≠ 0}` in
   `CoveringSpacesProject/ComplexPathWinding.lean`.
   Current issue: `abbrev Cstar` is fine as an internal name, but it is probably not the final API
   we want if this material moves toward Mathlib.
   Options to revisit later: keep `Cstar` internal, use a more explicit local name, or rely even
   harder on `ℂˣ` wrappers and hide the subtype almost completely.

4. Decide where `ContinuousMap.IsLoopHomotopy` should live.
   Current location: `CoveringSpacesProject/ComplexPathWinding.lean`.
   Current issue: it is a generic notion, not specific to complex winding numbers.
   Likely target: a small helper module if Mathlib does not already have the right abstraction for
   free homotopies of loops.

5. Revisit the generality of `circleMonomial_windingNumber` in
   `CoveringSpacesProject/RootsMathlib.lean`.
   Current issue: the theorem is stated for `R : ℝ` with `0 < R`, but the proof is really about a
   nonzero scaling factor.
   Goal: separate the genuinely reusable theorem from the circle/radius-facing corollary.

6. Reassess whether `circleLoop` and `circleLoopHomotopy` belong in
   `CoveringSpacesProject/RootsMathlib.lean`
   or in a separate circle helper module.
   Current issue: these are useful circle-specific constructions, but they are not inherently about
   roots of polynomials.

7. Decide the eventual home of `Metric.sphereToClosedBall`, currently in
   `CoveringSpacesProject/MetricSphereClosedBall.lean`.
   Current issue: the lemma is generic and plausibly upstreamable; we only created a local module
   because the current Mathlib snapshot seems to expose only `sphere_subset_closedBall` plus
   `Set.inclusion`.

8. Consider whether `exists_homotopy_of_norm_sub_lt` should eventually generalize in the codomain
   from `ℂˣ` to `𝕜ˣ` for a suitable class such as `RCLike 𝕜`.
   Current issue: the domain generalization is done, but the codomain is still fixed to `ℂ`.

### Notes for the eventual Mathlib branch

- The big topological input is already upstream via `Complex.isCoveringMap_exp`.
- The current project-local layer is mostly API packaging:
  `Path`-based winding numbers, free loop homotopies, and `ℂˣ` wrappers.
- Before upstreaming anything, re-check the newest Mathlib branch for:
  existing names around free homotopies of loops,
  any generic sphere-to-closed-ball inclusion map,
  and any more recent `Complex.exp` covering-map convenience lemmas.
