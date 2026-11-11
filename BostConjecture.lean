/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Main.MaxSlope.PiTensor -- shake: keep
public import BostConjecture.Adelic.Basic -- shake: keep
public import BostConjecture.Adelic.Contraction.Determinant -- shake: keep
public import BostConjecture.Adelic.Contraction.Lattice -- shake: keep
public import BostConjecture.Adelic.Geometry.Binary -- shake: keep
public import BostConjecture.Adelic.Geometry.Quotient -- shake: keep
public import BostConjecture.Adelic.Induction.MaxSlope -- shake: keep
public import BostConjecture.Adelic.Induction.RankInduction -- shake: keep
public import BostConjecture.Adelic.Semistability.LineTensor -- shake: keep
public import BostConjecture.Adelic.Semistability.Specht -- shake: keep
public import BostConjecture.Adelic.Slope.BoolTensor -- shake: keep
public import BostConjecture.Adelic.Slope.Contraction -- shake: keep
public import BostConjecture.Adelic.Slope.CovolumeLimit -- shake: keep
public import BostConjecture.Adelic.Slope.DeterminantSpecht -- shake: keep
public import BostConjecture.Adelic.Slope.DualQuotient -- shake: keep

/-!
# Bost's tensor semistability conjecture

The existing number-field theorem from `old.pdf` gives maximal-slope additivity,
finite-family equality and tensor semistability over arbitrary number fields.

The adelic modules develop the target in `bost.pdf`: actual constant Specht
bundles, geometric nonvanishing, completed-norm comparisons, and simultaneous
HN rank induction. The induction assembly currently assumes the geometric
quotient bound; it does not yet export the unconditional adelic Bost theorem.
See `CONTRIBUTIONS.md` for upstream sources and mathematical boundaries.
-/
