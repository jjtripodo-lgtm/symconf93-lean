# No symmetric configuration 93₁₀

John Tripodo’s theorem excludes a 93 by 93 binary incidence matrix with row
and column sums ten and pairwise row intersections at most one.
The statement applies to every incidence matrix of these parameters.

The proof enumerates the possible cycle profiles of the two-regular leave.
Determinant and local integral Gram obstructions exclude 35 profiles. A
cross-moment excludes one more. Finite circulant-block checks exclude the
final profile of three 31-cycles. The original development shares cycle and
Gram-matrix infrastructure with the earlier order-59 project.

- `Challenge.lean` states the incidence-matrix theorem.
- `Solution.lean` derives the same statement from
  `Symconf93.no_unrestricted_incidence93`.
- `comparator.json` selects the single theorem and the three standard
  axioms.

The project uses Lean 4.35.0-rc2 with pinned Mathlib dependencies. On Linux,
from the project root, run:

```sh
lake build Challenge Solution
lake env lean --trust=0 Audit.lean
lake comparator --config comparator.json --paranoid
```

The [original proof archive](https://github.com/jjtripodo-lgtm/symconf93-lean/tree/f0d8054c14bd20f5f42b4827a5c554be0b81aa72)
has the earlier Lean 4.31.0-rc1 project and its build receipt. This project
checks the single unrestricted order-93 statement. See [the order-59 companion](https://github.com/jjtripodo-lgtm/symconf59-checker)
for the preceding development.

AI systems helped develop the proofs, manuscript, and Lean formalization
under John Tripodo's direction. The code is available under Apache-2.0.
