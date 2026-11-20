/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import AdelicBostConjecture.Adelic.Induction.Bost -- shake: keep
public import AdelicBostConjecture.Adelic.Preliminaries
public import AdelicBostConjecture.Classical.Bost

/-!
# Bost's tensor semistability theorem and the classical Bost conjecture

Theorem 1.2 of this paper: maximal slopes add under orthogonal tensor products
of positive-rank Hermitian adelic vector bundles over proper adelic curves
with countable characteristic-zero fields and the usual real or complex norms
at infinite places. The entry point exports binary and finite-family slope
additivity and semistability, together with tensor HN compatibility.

`Classical.Bost` deduces the classical number-field conjecture from Theorem 1.2,
using the original integral Hermitian metrics, tensor product and maximal slope.

The concrete geometric quotient bound closes simultaneous rank induction.
All factors and quotients carry their actual completed Hilbert/epsilon norms.
Source attribution is recorded in the project contribution records.
-/
