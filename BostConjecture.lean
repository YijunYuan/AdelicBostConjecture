module

public import BostConjecture.Slope.Subspace
public import BostConjecture.Arithmetic.HermitianLine
public import BostConjecture.Arithmetic.Degree
public import BostConjecture.Arithmetic.DegreeNormalization
public import BostConjecture.Arithmetic.LineContraction
public import BostConjecture.Arithmetic.MetricScaling
public import BostConjecture.Arithmetic.SubspaceDegree
public import BostConjecture.Arithmetic.QuotientMetric
public import BostConjecture.Arithmetic.TensorMetric
public import BostConjecture.Arithmetic.NestedQuotient
public import BostConjecture.Arithmetic.SaturationDegree
public import BostConjecture.Arithmetic.LineTensorDegree
public import BostConjecture.Arithmetic.DualFiber
public import BostConjecture.Arithmetic.LineDualDegree
public import BostConjecture.Arithmetic.DeterminantDual
public import BostConjecture.Arithmetic.DeterminantProduct
public import BostConjecture.Arithmetic.IntegralDeterminantProduct
public import BostConjecture.Arithmetic.IntegralExactDeterminant
public import BostConjecture.Arithmetic.ExactDegree
public import BostConjecture.LinearAlgebra.AlternatingTensorPower
public import BostConjecture.LinearAlgebra.ExteriorPower.BaseChange
public import BostConjecture.LinearAlgebra.PiTensorProduct.Projective
public import BostConjecture.Analysis.InnerProductSpace.Polar
public import BostConjecture.Balanced.PluckerNorm
public import BostConjecture.Balanced.SpectralExpansion
public import BostConjecture.InvariantTheory.Semistability
public import BostConjecture.Geometry.TensorRealization
public import BostConjecture.Geometry.FreeEmbedding
public import BostConjecture.Geometry.DeterminantBaseChange
public import BostConjecture.Geometry.LocalizationDescent
public import BostConjecture.Geometry.DeterminantNaturality
public import BostConjecture.Geometry.ProjectiveEmbedding
public import BostConjecture.Geometry.ProjectiveMetric
public import BostConjecture.Geometry.Contraction
public import BostConjecture.Geometry.ContractionMetric
public import BostConjecture.Geometry.ContractionBaseChange
public import BostConjecture.Geometry.ContractionNorm
public import BostConjecture.Tensor.Evaluation
public import BostConjecture.Tensor.EvaluationBaseChange
public import BostConjecture.Tensor.DualRegroupBaseChange
public import BostConjecture.Tensor.HilbertRegroup
public import BostConjecture.Tensor.DualRegroup
public import BostConjecture.Tensor.DualMetric
public import BostConjecture.Lattice.Covolume
public import BostConjecture.Specht.Tableau
public import BostConjecture.Specht.Metric
public import BostConjecture.Specht.Norm
public import BostConjecture.Specht.Rectangle
public import BostConjecture.Specht.ColumnTensor
public import BostConjecture.Specht.Covariance
public import BostConjecture.Specht.Standard
public import BostConjecture.Specht.Basis
public import BostConjecture.Specht.PrefixWeights
public import BostConjecture.Specht.PrefixNormalizer
public import BostConjecture.Specht.BulkNormalizer
public import BostConjecture.Specht.OccupancyMGF
public import BostConjecture.Specht.Orthogonal
public import BostConjecture.Specht.RealAction
public import BostConjecture.Specht.Content
public import BostConjecture.Specht.Central
public import BostConjecture.Specht.Seminormal
public import BostConjecture.Specht.OneRow
public import OAI.NumberTheory.ArithmeticGroups.Lattices.FrameMatrices
public import OAI.RepresentationTheory.Saxl.SpechtSubmodule
public import HarderNarasimhan.Filtration.Unique
public import HarderNarasimhan.PayoffFunction.Slope
public import HarderNarasimhan.PayoffFunction.NashEquilibrium
public import RepresentationTheory.Combinatorics.YoungDiagram.CornerStatistics

/-!
# Bost's tensor semistability conjecture

Checked prerequisites for the formalization of Theorem 1.1 of
`bost_specht_manuscript.pdf`. The main theorem is not yet formalized.
See `CONTRIBUTIONS.md` for upstream sources and mathematical boundaries.
-/
