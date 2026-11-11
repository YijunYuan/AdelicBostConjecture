/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Main.MaxSlope.PiTensor -- shake: keep
public import BostConjecture.Adelic.Basic -- shake: keep
public import BostConjecture.Adelic.Contraction.Determinant -- shake: keep
public import BostConjecture.Adelic.Contraction.FiniteSpecht -- shake: keep
public import BostConjecture.Adelic.Contraction.Lattice -- shake: keep
public import BostConjecture.Adelic.Contraction.Pairing -- shake: keep
public import BostConjecture.Adelic.Geometry.Binary -- shake: keep
public import BostConjecture.Adelic.Geometry.Quotient -- shake: keep
public import BostConjecture.Adelic.Induction.Bost -- shake: keep
public import BostConjecture.Adelic.Induction.FiniteMaxSlope -- shake: keep
public import BostConjecture.Adelic.Induction.MaxSlope -- shake: keep
public import BostConjecture.Adelic.Induction.RankInduction -- shake: keep
public import BostConjecture.Adelic.Semistability.LineTensor -- shake: keep
public import BostConjecture.Adelic.Semistability.Specht -- shake: keep
public import BostConjecture.Adelic.Slope.BoolTensor -- shake: keep
public import BostConjecture.Adelic.Slope.Contraction -- shake: keep
public import BostConjecture.Adelic.Slope.CovolumeLimit -- shake: keep
public import BostConjecture.Adelic.Slope.DeterminantSpecht -- shake: keep
public import BostConjecture.Adelic.Slope.DeterminantSpechtDegree -- shake: keep
public import BostConjecture.Adelic.Slope.DeterminantSpechtTensor -- shake: keep
public import BostConjecture.Adelic.Slope.DualQuotient -- shake: keep
public import BostConjecture.Adelic.Slope.GeometricQuotient -- shake: keep
public import BostConjecture.Adelic.Slope.GeometricSubspace -- shake: keep
public import BostConjecture.Adelic.Specht.Semistability -- shake: keep

/-!
# Bost's tensor semistability conjecture

The existing number-field theorem from `old.pdf` gives maximal-slope additivity,
finite-family equality and tensor semistability over arbitrary number fields.

The adelic modules prove Theorem 1.1 of `bost.pdf`: maximal slopes add under
orthogonal tensor products of positive-rank Hermitian adelic vector bundles
over proper adelic curves with countable characteristic-zero fields and the
usual real or complex norms at infinite places. Binary and finite-family
semistability, and tensor HN compatibility, follow with the actual Hilbert and
epsilon tensor norms. The concrete geometric quotient bound closes simultaneous
rank induction without an additional geometric slope hypothesis.
See `CONTRIBUTIONS.md` for upstream sources and mathematical boundaries.
-/
