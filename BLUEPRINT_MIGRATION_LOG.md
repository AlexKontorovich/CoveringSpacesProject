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
