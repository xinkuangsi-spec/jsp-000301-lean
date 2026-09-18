# JSP-000301 — Consecutive powerful numbers need not include a square

Lean 4 + Mathlib formalization of the counterexample answering
[JSP-000301](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0301-0400.md#JSP-000301):

> If two consecutive positive integers are powerful, must at least one be a perfect square?

**Answer: no.** Golomb's 1970 counterexample ([Go70], *Powerful numbers*,
Amer. Math. Monthly 77(8), 848–852):

- `12167 = 23³`
- `12168 = 2³ · 3² · 13²`

Both are powerful (every prime factor occurs with exponent ≥ 2), consecutive,
and lie strictly between `110² = 12100` and `111² = 12321`, so neither is a
perfect square.

## Contents

- `Jsp000301/Basic.lean` — definition of `Powerful`, proofs that 12167 and
  12168 are powerful, that no integer strictly between `110²` and `111²` is a
  square, and the final negative answer `jsp_000301_answer`.

## Build

```
lake build
```

Tested with Lean 4.34.0 (`leanprover/lean4:v4.34.0`) and Mathlib `v4.34.0`.
No `sorry`, no additional axioms.
