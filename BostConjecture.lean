/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Adelic.Induction.Bost -- shake: keep

/-!
# Bost's tensor semistability theorem over adelic curves

Theorem 1.1 of `bost.pdf`: maximal slopes add under orthogonal tensor products
of positive-rank Hermitian adelic vector bundles over proper adelic curves
with countable characteristic-zero fields and the usual real or complex norms
at infinite places. The entry point exports binary and finite-family slope
additivity and semistability, together with tensor HN compatibility.

The concrete geometric quotient bound closes simultaneous rank induction.
All factors and quotients carry their actual completed Hilbert/epsilon norms.
See `CONTRIBUTIONS.md` for source attribution and `docs/main-theorem-scope.md`
for the retained dependency closure.
-/
