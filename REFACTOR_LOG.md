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

3. [done] Settled the local naming question for `{z : ℂ // z ≠ 0}` in
   `CoveringSpacesProject/ComplexPathWinding.lean`.
   Decision: keep `Cstar` as internal-only notation inside that file, and keep the bridge API
   outward-facing in terms of `ℂˣ` when possible.

4. [done] Moved `ContinuousMap.IsLoopHomotopy` out of
   `CoveringSpacesProject/ComplexPathWinding.lean` into the small generic helper module
   `CoveringSpacesProject/LoopHomotopy.lean`.
   Decision: keep it project-local for now, but treat it as generic topology infrastructure rather
   than winding-number-specific API.

5. [done] Revisited the generality of `circleMonomial_windingNumber` in
   `CoveringSpacesProject/RootsMathlib.lean`.
   Decision: the reusable theorem is now `circleScaledMonomial_windingNumber`, and the
   radius-parameterized `circleMonomial_windingNumber` is a corollary.

6. [done] Moved `circleLoop` and `circleLoopHomotopy` out of
   `CoveringSpacesProject/RootsMathlib.lean` into the separate circle helper module
   `CoveringSpacesProject/CirclePathHelpers.lean`.
   Decision: keep circle-specific path helpers separate from both winding-number infrastructure and
   polynomial applications.

7. [done] Decided the current home of `Metric.sphereToClosedBall`.
   Decision: keep it in the dedicated local helper module
   `CoveringSpacesProject/MetricSphereClosedBall.lean` for now.
   Note: this still looks plausibly upstreamable once we move onto a fresh Mathlib branch.

8. [done] Generalized `exists_homotopy_of_norm_sub_lt` in the codomain from `ℂˣ` to `𝕜ˣ` for
   `[RCLike 𝕜]`.
   Note: `windingNumber_eq_of_norm_sub_lt` remains specialized to `ℂˣ` because the current
   winding-number API is still complex-specific.

### Current status

- The active cleanup checklist above is complete.
- New follow-up items should be added here as they come up during the eventual Mathlib-branch
  cleanup.

### Notes for the eventual Mathlib branch

- The big topological input is already upstream via `Complex.isCoveringMap_exp`.
- The current project-local layer is mostly API packaging:
  `Path`-based winding numbers, free loop homotopies, and `ℂˣ` wrappers.
- Before upstreaming anything, re-check the newest Mathlib branch for:
  existing names around free homotopies of loops,
  any generic sphere-to-closed-ball inclusion map,
  and any more recent `Complex.exp` covering-map convenience lemmas.
