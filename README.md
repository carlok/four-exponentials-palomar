# The four exponentials theorem in transcendence degree one, and Schneider's eighth problem

A Lean 4 and Mathlib proof of the four exponentials theorem in transcendence degree one,
prepared for the [Palomar registry](https://palomar-registry.org/). It is a self-contained
extract of the library [carlok/diaz-modulus-lean](https://github.com/carlok/diaz-modulus-lean),
which is the canonical home of the proofs.

## Results

- `FourExponentials.four_exponentials_trdeg_one`: **The four exponentials theorem in
  transcendence degree one** (Waldschmidt 1973; Brownawell 1974). Let `lᵢⱼ` be four non-zero
  logarithms of algebraic numbers with `l₁₁ l₂₂ = l₁₂ l₂₁`. If the field they generate has
  transcendence degree at most one over `ℚ`, then the rows or the columns of the matrix `(lᵢⱼ)`
  are linearly dependent over `ℚ`. Source: Waldschmidt 1973; Brownawell 1974.
- `FourExponentials.exp_e_or_exp_e_sq_transcendental`: **Schneider's eighth problem**
  (Waldschmidt 1973; Brownawell 1974): one of `e^e` and `e^{e²}` is transcendental. Source:
  Waldschmidt 1973 (solution of Schneider's eighth problem); Brownawell 1974.
- `FourExponentials.two_algebraically_independent_of_exp_column`: If `x₁, x₂` and `y₁, y₂` are
  each linearly independent over `ℚ` and `exp (x₁ y₂)`, `exp (x₂ y₂)` are algebraic, then two of
  the eight numbers `xᵢ, yⱼ, exp (xᵢ yⱼ)` are algebraically independent over `ℚ` (Waldschmidt
  1973; Brownawell 1974). Source: Waldschmidt 1973; Brownawell 1974.

## Layout

- `Challenge.lean`: the statements, with deliberate `sorry`, importing Mathlib only.
- `Solution.lean`: the same statements, proved by the library theorems.
- `Diaz/`: the 69 library modules the proofs need, copied from diaz-modulus-lean at
  `465147a3ec8b` and changed only for the Lean module system (`module`, `public import`,
  `@[expose] public section`). Paths and namespaces are the library's.
- `comparator.json`, `formalization.yaml`: the Palomar submission metadata.

## Build

```bash
lake exe cache get && lake build
```

Lean 4.36.0, Mathlib v4.36.0. `scripts/verify-comparator.sh` runs the toolchain's
`lake comparator` the way Palomar does.

## Related

- The six exponentials theorem from the same library is registered separately as
  [PALOMAR-2026-11-22-000020](https://palomar-registry.org/entry?id=PALOMAR-2026-11-22-000020&version=1).
- Submissions go to https://submit.palomar-registry.org/.

## Authorship

Claude agents (Anthropic) wrote the Lean statements and proofs under Carlo Perassi's direction;
see `formalization.yaml` and the library's `docs/method.md`. Licence: Apache-2.0.
