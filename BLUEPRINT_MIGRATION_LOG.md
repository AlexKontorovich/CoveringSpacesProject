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

5. [pending] Build a correspondence table from the modern code to the blueprint sections, so we can
   see exactly what needs to be copied and what should be renamed.

6. [pending] Create the new file skeleton with the same broad narrative order as the blueprint:
   winding numbers of loops, winding numbers of circle maps, disk-extension vanishing, polynomial
   winding at infinity, and root existence.

7. [pending] Copy the generic helper layer into the new file:
   `ContinuousMap.IsLoopHomotopy` and `Metric.sphereToClosedBall`.

8. [pending] Copy the circle-specific helper layer into the new file:
   `Circle.toClosedUnitDisk`,
   `ContinuousMap.circleLoop`,
   `ContinuousMap.circleLoopHomotopy`,
   and the associated endpoint/loop lemmas.

9. [pending] Copy the path-lifting and winding-number core into the new file from
   `CoveringSpacesProject/ComplexPathWinding.lean`.

10. [pending] Decide whether the new file should expose the modern `ℂˣ`-based API, the older
    `Cstar`-based API, or both, and implement the necessary bridge definitions consistently.

11. [pending] Copy the circle winding-number layer from `CoveringSpacesProject/RootsMathlib.lean`:
    `ContinuousMap.windingNumber`,
    `windingNumber_const`,
    `windingNumber_eq_of_homotopy`,
    `exists_homotopy_of_norm_sub_lt`,
    `windingNumber_eq_of_norm_sub_lt`,
    `windingNumber_eq_zero_of_exists_extension`,
    and `windingNumber_eq_zero_of_exists_extension'`.

12. [pending] Copy the monomial winding-number layer:
    `circleScaledMonomial`,
    `circleMonomial`,
    `circleScaledMonomial_windingNumber`,
    and `circleMonomial_windingNumber`.

13. [pending] Copy the polynomial circle/disk map layer:
    `Polynomial.mapCircleUnits`,
    `Polynomial.mapClosedUnitDiskUnits`,
    and their coercion lemmas.

14. [pending] Copy the large-radius dominance argument and its winding-number consequence:
    `Polynomial.leadingTerm_dominates_on_circle` and
    `Polynomial.eventually_windingNumber_eq_natDegree`.

15. [pending] Copy the final root-existence theorem:
    `Polynomial.exists_root_of_natDegree_pos`.

16. [pending] Add blueprint-style natural-language statement blocks above every copied
    `def`/`lemma`/`theorem`.

17. [pending] Add blueprint-style natural-language proof/explanation blocks below every copied
    `def`/`lemma`/`theorem`.

18. [pending] Add section headers, `\uses{...}` tags, and labels so the new file reads like a real
    blueprint rather than a raw code dump.

19. [pending] Make sure the natural-language prose reflects the new Mathlib-style proofs rather than
    the old interval-based implementation details when those have changed.

20. [pending] Build the new file by itself.

21. [pending] Build the whole project with the new file added.

22. [pending] Compare the new file against `CoveringSpacesProject/RootsComplexPolynomials.lean` to
    check for any missing theorem from the relevant winding-number / FTA slice.

23. [pending] Decide whether to import the new file from `CoveringSpacesProject.lean`, leave it as a
    sidecar working file, or eventually use it to replace parts of the old blueprint file.

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
