# Blueprint Migration Log

## 2026-03-18

### Goal

Create a new single Lean file, in the style of `CoveringSpacesProject/RootsComplexPolynomials.lean`,
that packages the modern refactor into one place:

- copy the current code now spread across
  `CoveringSpacesProject/LoopHomotopy.lean`,
  `CoveringSpacesProject/MetricSphereClosedBall.lean`,
  `CoveringSpacesProject/CirclePathHelpers.lean`,
  `CoveringSpacesProject/ComplexPathWinding.lean`, and
  `CoveringSpacesProject/RootsMathlib.lean`;
- present it in blueprint style, with natural-language statement blocks above each formal
  `def`/`lemma`/`theorem` and natural-language proof blocks below each one;
- keep the modern proofs and Mathlib-style abstractions, while restoring the exposition style of the
  blueprint.

### Open decisions to settle first

1. [done] Choose the final filename and module name for the new file.
   Use: `RootsComplexPolynomialsNew.lean`.

2. [done] Decide the formal naming policy inside the new file.
   - keep the new Mathlib-style names as the primary formal API and add blueprint prose only;

3. [done] Decide how self-contained the new file should be.
   Yes: import `Mathlib` and copy in the needed helper code directly, so the file is a
   genuine standalone blueprint-style presentation rather than a thin wrapper over local helper
   modules.

4. [done] Decide how strict to be about annotating helper lemmas.
   Yes: every formal `def`, `lemma`, and `theorem`, including coercion lemmas and
   `[simp]` lemmas, gets a short natural-language statement above and a short proof/explanation
   block below.

### Porting checklist

5. [done] Built a correspondence table from the modern code to the blueprint sections.
   See the table below.

6. [done] Created the new file skeleton with the same broad narrative order as the blueprint:
   winding numbers of loops, winding numbers of circle maps, disk-extension vanishing, polynomial
   winding at infinity, and root existence.
   Result: `CoveringSpacesProject/RootsComplexPolynomialsNew.lean`.

7. [done] Copied the generic helper layer into the new file:
   `ContinuousMap.IsLoopHomotopy` and `Metric.sphereToClosedBall`.

8. [done] Copied the circle-specific helper layer into the new file:
   `Circle.toClosedUnitDisk`,
   `ContinuousMap.circleLoop`,
   `ContinuousMap.circleLoopHomotopy`,
   and the associated endpoint/loop lemmas.

9. [done] Copied the path-lifting and winding-number core into the new file from
   `CoveringSpacesProject/ComplexPathWinding.lean`.

10. [done] Decided the exposed API policy.
    Decision: keep the modern `ℂˣ`-based API as primary, retain `Cstar` only as internal shorthand
    plus bridge infrastructure, and place the whole file under the top-level namespace
    `RootsComplexPolynomialsNew` to avoid collisions with the existing modules.

11. [done] Copied the circle winding-number layer from `CoveringSpacesProject/RootsMathlib.lean`:
    `ContinuousMap.windingNumber`,
    `windingNumber_const`,
    `windingNumber_eq_of_homotopy`,
    `exists_homotopy_of_norm_sub_lt`,
    `windingNumber_eq_of_norm_sub_lt`,
    `windingNumber_eq_zero_of_exists_extension`,
    and `windingNumber_eq_zero_of_exists_extension'`.

12. [done] Copied the monomial winding-number layer:
    `circleScaledMonomial`,
    `circleMonomial`,
    `circleScaledMonomial_windingNumber`,
    and `circleMonomial_windingNumber`.

13. [done] Copied the polynomial circle/disk map layer:
    `Polynomial.mapCircleUnits`,
    `Polynomial.mapClosedUnitDiskUnits`,
    and their coercion lemmas.

14. [done] Copied the large-radius dominance argument and its winding-number consequence:
    `Polynomial.leadingTerm_dominates_on_circle` and
    `Polynomial.eventually_windingNumber_eq_natDegree`.

15. [done] Copied the final root-existence theorem:
    `Polynomial.exists_root_of_natDegree_pos`.

16. [done] Added blueprint-style natural-language statement blocks above every copied
    `def`/`lemma`/`theorem`.

17. [done] Added blueprint-style natural-language proof/explanation blocks below every copied
    `def`/`lemma`/`theorem`.

18. [done] Added `\uses{...}` tags systematically throughout the statement environments of the new
    file.
    Verified by rebuilding the blueprint successfully with `make blueprint`.

19. [done] Rewrote the natural-language prose to reflect the new Mathlib-style proofs rather than
    the old interval-based implementation details when those have changed.

20. [done] Built the new file by itself.
    Verified with `lake build CoveringSpacesProject.RootsComplexPolynomialsNew`.

21. [done] Built the whole project with the new file added.
    Verified with `lake build CoveringSpacesProject`.

22. [done] Compared the new file against `CoveringSpacesProject/RootsComplexPolynomials.lean` for
    the relevant winding-number / FTA slice.
    Result: the correspondence table entries for the circle-loop, winding-number, monomial,
    polynomial-at-infinity, and root-existence pieces are all represented in the new file.

23. [done] Decided to import the new file from `CoveringSpacesProject.lean`.
    Reason: because the file now lives under its own namespace, it can be built as part of the
    library without colliding with the existing refactor modules.

### Working correspondence table

- `ContinuousMap.circleLoop` is the modern analogue of `DefS1loop`.
- `ContinuousMap.windingNumber` is the modern analogue of `DefWNS1`.
- `ContinuousMap.windingNumber_const` corresponds to `constS1`.
- `ContinuousMap.windingNumber_eq_of_homotopy` corresponds to `S1homotopy`.
- `Circle.toClosedUnitDisk` corresponds to `circleToD2`.
- `ContinuousMap.windingNumber_eq_zero_of_exists_extension` corresponds to `boundsWN0`.
- `ContinuousMap.exists_homotopy_of_norm_sub_lt` is the modern version of `walkingdog`.
- `ContinuousMap.windingNumber_eq_of_norm_sub_lt` corresponds to `sameWN`.
- `circleScaledMonomial` / `circleMonomial` correspond to `monomialS1Map`.
- `circleScaledMonomial_windingNumber` / `circleMonomial_windingNumber` correspond to `zkWNk`.
- `Polynomial.mapCircleUnits` corresponds to `polyCircleMap`.
- `Polynomial.mapClosedUnitDiskUnits` corresponds to `polyDiskMap`.
- `Polynomial.leadingTerm_dominates_on_circle` corresponds to `zkdominates`.
- `Polynomial.eventually_windingNumber_eq_natDegree` corresponds to `WNthm`.
- `Polynomial.exists_root_of_natDegree_pos` corresponds to `ExistRoot`.

### Notes

- The blueprint prose in `RootsComplexPolynomials.lean` still provides the narrative template.
- The modern code already has better abstractions than the blueprint in several places:
  `Path`, `I`, `ContinuousMap.Homotopy`, `Complex.isCoveringMap_exp`, and `ℂˣ`.
- When the old exposition and the new formalization diverge, prefer keeping the stronger modern
  formal statement and rewriting the prose to match it.

### Current status

- The new standalone annotated file now exists at
  `CoveringSpacesProject/RootsComplexPolynomialsNew.lean`.
- It is self-contained, imports only `Mathlib`, and is namespaced under
  `RootsComplexPolynomialsNew`.
- It builds on its own and as part of the whole project.
- The current standalone blueprint file is now feature-complete for this migration pass.

## 2026-03-30

### `RootsComplexPolynomialsNew.lean` vocabulary cleanup

Goal: remove the public `Cstar` vocabulary from
`CoveringSpacesProject/RootsComplexPolynomialsNew.lean` and keep `ℂˣ` as the single exposed
language for nonzero complex values.

Changes made:

1. Removed the file-local `Cstar` notation and the accompanying blueprint block for that alias.

2. Reworked the loop-lifting API so the public statements now use `ℂˣ` throughout:
   - `Path.expLift`
   - `Path.expLift_apply`
   - `Path.expLift_zero`
   - `Path.eq_expLift`
   - `Path.eq_add_int_mul_two_pi_I_of_lifts`
   - `Path.windingNumber`
   - `Path.windingNumber_eq_of_lift`
   - `Path.windingNumber_eq_of_homotopy`
   - `Path.windingNumber_refl`

3. Deleted the extra public bridge layer that converted back and forth between `ℂˣ` and the
   nonzero-complex subtype:
   - `ContinuousMap.toNonzeroSubtype`
   - `ContinuousMap.fromNonzeroSubtype`
   - `Path.toNonzeroSubtype`
   - the subtype-valued extension theorem
     `ContinuousMap.windingNumber_eq_zero_of_exists_extension'`

4. Updated the circle-map layer to use the path-level `ℂˣ` winding number directly:
   - `ContinuousMap.windingNumber`
   - `ContinuousMap.windingNumber_const`
   - `ContinuousMap.windingNumber_eq_of_homotopy`
   - downstream `\uses{...}` annotations

5. Updated the monomial winding-number proof to avoid the old subtype witness in the main proof
   line and use `ℂˣ` data directly.

6. Removed stale references to the deleted subtype bridge theorem from the final root-existence
   theorem metadata.

### Remaining internal bridge

An internal bridge to the nonzero-complex subtype is still present, but only privately, in the
path-lifting implementation. This remains necessary because Mathlib’s covering-map API for
`Complex.exp` is stated over `{z : ℂ // z ≠ 0}` rather than `ℂˣ`, so the file still transports
paths and homotopies to that subtype inside the proofs before applying
`Complex.isCoveringMap_exp`.

### Verification

Verified with:

```sh
lake build CoveringSpacesProject.RootsComplexPolynomialsNew
```

## 2026-03-30

### Mathlib-quality pass and dependency bump

Goal: reevaluate `CoveringSpacesProject/RootsComplexPolynomialsNew.lean` from the point of view of
upstream mathlib quality, record likely file placement, and bump the project to the latest
available mathlib snapshot.

Review conclusion:

1. The reusable declarations in `RootsComplexPolynomialsNew.lean` are mostly at the right level of
   generality already:
   - `Metric.sphereToClosedBall`
   - `ContinuousMap.IsLoopHomotopy`
   - `ContinuousMap.circleLoop`
   - `ContinuousMap.circleLoopHomotopy`
   - `ContinuousMap.exists_homotopy_of_norm_sub_lt`
   - `Path.expLift`
   - `Path.windingNumber`

2. The main mathlib-quality issue is not naming so much as file scope: the standalone blueprint
   file mixes generic topology helpers, reusable complex covering-map lemmas, and project-specific
   polynomial applications in one place.

Changes made:

3. Added an explicit upstreaming note to the header of
   `CoveringSpacesProject/RootsComplexPolynomialsNew.lean` explaining the likely split:
   - topology/path-support layer for `sphereToClosedBall` and `IsLoopHomotopy`,
   - circle-specific helpers near the existing complex-circle API,
   - winding-number lemmas next to `Mathlib/Analysis/Complex/CoveringMap.lean`,
   - monomial/polynomial applications kept downstream.

4. Bumped the project from Lean/mathlib `v4.28.0` to the latest available mathlib snapshot on
   2026-03-30:
   - Lean toolchain: `leanprover/lean4:v4.29.0-rc8`
   - mathlib pin: commit `47aa862678fb83cdc5d377e5c04d198d5acae5c8`
     (the `master-2026-03-30` snapshot)
   - doc-gen4 pin: `v4.29.0-rc8`

5. Reordered `require` lines in `lakefile.lean` so mathlib’s dependency versions take precedence
   over the optional `doc-gen4` dependency. This was needed for the cache hook to succeed under
   the upgraded package graph.

6. Updated `lake-manifest.json` by rerunning `lake update` under the new toolchain.

7. Built ProofWidgets’ JavaScript once locally after the bump, because the upgraded dependency
   graph invalidated the packaged widget build and the sandboxed npm run could not write its cache
   and log files.

8. Applied a small compatibility patch to the legacy file
   `CoveringSpacesProject/RootsComplexPolynomials.lean`:
   - opened `Bundle` so unqualified `Trivialization` names still resolve under the newer mathlib;
   - replaced deprecated `push_neg` with `push Not`.

### Verification

Verified with:

```sh
lake build CoveringSpacesProject.RootsComplexPolynomialsNew
lake build CoveringSpacesProject.RootsComplexPolynomials
lake build
```
