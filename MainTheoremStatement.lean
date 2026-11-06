import Mathlib

/-!
# Bost manuscript Theorem 1.1 — statement and definition dossier

REVIEW COPY, NOT A PROOF FILE. All imports are from upstream mathlib (Lean/mathlib
v4.35.0, mathlib commit 56a005855ea17e0b0958f73ec801ae140b0a1679).
This file can be checked with `lake env lean MainTheoremStatement.lean`
in a mathlib project; neither BostConjecture nor HarderNarasimhan is imported.

The definitions below are extracted from the accepted BostConjecture source
revision dd5c6b6ed81b960910d4b63c941cbd144a9e87eb. The final theorem keeps its
original namespace, parameters and statement. Relevant data instances, induced
metrics, degree normalization, and the actual HN-based definition of maxSlope
are included. Proofs are omitted with `sorry`; a successful check of THIS file
certifies syntax/types only. The proved project does not import this review copy.

Read in this order: HermitianMetric; determinant/degree/slope; submodule metrics;
HN construction/maxSlope; tensor metrics; the final statements. Source comments
identify the original modules. Standard mathlib concepts (number fields, their
rings of integers, finite/projective modules, tensor/exterior powers, inner
product cores, fractional-ideal norms and Dedekind cuts) retain mathlib's actual
definitions and instances. No integral freeness assumption is introduced.

Attribution: the HN definitions below are by Yijun Yuan, Apache-2.0, from
HarderNarasimhan commit 14b3090e1e169b77fe381102a1289f24c2b08a11.
The exterior projection/base-change definitions include work by Eric Wieser
and Nailin Guan, Apache-2.0, extracted from mathlib PR #40948,
revision b642b6723caf97b7b462dd5ddeabb0226c3b5433 (project provenance retained
in vendor/mathlib-prs/40948/PROVENANCE.json). Edits here omit proofs and unused
lemmas, consolidate scopes, and expose private helpers needed to read the data.
-/

noncomputable section
open NumberField TensorProduct PiTensorProduct
open scoped nonZeroDivisors InnerProductSpace ComplexConjugate NNReal

namespace BostConjecture.Arithmetic
variable {K : Type*} [Field K]
variable (M : Type*) [AddCommGroup M] [Module (𝓞 K) M]

-- Source: BostConjecture/Arithmetic/Hermitian.lean · ComplexFiber
abbrev ComplexFiber (σ : K →+* ℂ) :=
  let : Algebra (𝓞 K) ℂ := (σ.comp (algebraMap (𝓞 K) K)).toAlgebra
  ℂ ⊗[𝓞 K] M

-- Source: BostConjecture/Arithmetic/Hermitian.lean · fiberSection
def fiberSection (σ : K →+* ℂ) (x : M) : ComplexFiber M σ :=
  let : Algebra (𝓞 K) ℂ := (σ.comp (algebraMap (𝓞 K) K)).toAlgebra
  1 ⊗ₜ[𝓞 K] x

-- Source: BostConjecture/Arithmetic/Hermitian.lean · HermitianMetric
structure HermitianMetric where
  /-- The Hermitian inner product on each canonical complex fiber. -/
  fiber : ∀ σ : K →+* ℂ, InnerProductSpace.Core ℂ (ComplexFiber M σ)
  /-- Conjugation compatibility on the spanning integral generators. -/
  conjugate : ∀ (σ : K →+* ℂ) (x y : M),
    (fiber (ComplexEmbedding.conjugate σ)).inner
      (fiberSection M (ComplexEmbedding.conjugate σ) x)
      (fiberSection M (ComplexEmbedding.conjugate σ) y) =
    star ((fiber σ).inner (fiberSection M σ x) (fiberSection M σ y))

namespace HermitianMetric
variable {M}

-- Source: BostConjecture/Arithmetic/Hermitian.lean · sectionNorm
def sectionNorm (h : HermitianMetric (K := K) M) (σ : K →+* ℂ) (x : M) : ℝ :=
  Real.sqrt (((h.fiber σ).inner (fiberSection M σ x) (fiberSection M σ x)).re)

end HermitianMetric
end BostConjecture.Arithmetic

namespace ExteriorAlgebra
variable (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]

-- Source: BostConjecture/LinearAlgebra/ExteriorPower/Projection.lean · toExteriorPower
def toExteriorPower (i : ℕ) : ExteriorAlgebra R M →ₗ[R] (⋀[R]^i M) :=
    (DFinsupp.lapply i).comp (GradedAlgebra.liftι R M).toLinearMap

end ExteriorAlgebra
namespace exteriorPower
variable (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M]
variable (S : Type*) [CommRing S] [Algebra R S]

-- Source: BostConjecture/LinearAlgebra/ExteriorPower/BaseChange.lean · baseChangeGenerator
def baseChangeGenerator (i : ℕ) : M [⋀^Fin i]→ₗ[R] ExteriorAlgebra S (S ⊗[R] M) where
  toFun m := ExteriorAlgebra.ιMulti S i ((TensorProduct.mk R S M 1) ∘ m)
  map_update_add' _ := by simp [Function.comp_update, map_add]
  map_update_smul' {_} m j r := by
    simp [Function.comp_update, -algebraMap_smul, ← algebraMap_smul S r]
  map_eq_zero_of_eq' m j k hjk hjk_ne := by
    have : ((mk R S M 1) ∘ m) j = ((mk R S M 1) ∘ m) k := by
      simpa using congrArg (TensorProduct.mk R S M 1) hjk
    simpa using
      (ExteriorAlgebra.ιMulti S i).map_eq_zero_of_eq (((TensorProduct.mk R S M 1) ∘ m)) this hjk_ne

-- Source: BostConjecture/LinearAlgebra/ExteriorPower/BaseChange.lean · baseChangeEquivForwardAux
def baseChangeEquivForwardAux (i : ℕ) : M [⋀^Fin i]→ₗ[R] (⋀[S]^i (S ⊗[R] M)) :=
  (baseChangeGenerator R M S i).codRestrict ((⋀[S]^i (S ⊗[R] M)).restrictScalars R) (fun m =>
    ExteriorAlgebra.ιMulti_range S i (Set.mem_range_self ((TensorProduct.mk R S M 1) ∘ m)))

-- Source: BostConjecture/LinearAlgebra/ExteriorPower/BaseChange.lean · baseChangeEquivForward
def baseChangeEquivForward (i : ℕ) : S ⊗[R] (⋀[R]^i M) →ₗ[S] (⋀[S]^i (S ⊗[R] M)) :=
  TensorProduct.AlgebraTensorModule.lift {
    toFun s := s • exteriorPower.alternatingMapLinearEquiv (baseChangeEquivForwardAux R M S i)
    map_add' s t := by simp [add_smul]
    map_smul' s t := by simp [smul_smul] }

-- Source: BostConjecture/LinearAlgebra/ExteriorPower/BaseChange.lean · baseChangeInverseAlternating
def baseChangeInverseAlternating (i : ℕ) : (S ⊗[R] M) [⋀^Fin i]→ₗ[S] S ⊗[R] (⋀[R]^i M) :=
  (((ExteriorAlgebra.toExteriorPower R M i).baseChange S).comp
    (ExteriorAlgebra.baseChangeEquiv R M S).symm.toAlgHom.toLinearMap).compAlternatingMap
      (ExteriorAlgebra.ιMulti S i)

-- Source: BostConjecture/LinearAlgebra/ExteriorPower/BaseChange.lean · baseChangeEquivInverse
def baseChangeEquivInverse (i : ℕ) : ⋀[S]^i (S ⊗[R] M) →ₗ[S] S ⊗[R] (⋀[R]^i M) :=
  alternatingMapLinearEquiv (baseChangeInverseAlternating R M S i)

-- Source: BostConjecture/LinearAlgebra/ExteriorPower/BaseChange.lean · baseChange_left_inverse
lemma baseChange_left_inverse (i : ℕ) :
    (baseChangeEquivInverse R M S i).comp (baseChangeEquivForward R M S i) = LinearMap.id := by sorry

-- Source: BostConjecture/LinearAlgebra/ExteriorPower/BaseChange.lean · baseChange_right_inverse
lemma baseChange_right_inverse (i : ℕ) :
    (baseChangeEquivForward R M S i).comp (baseChangeEquivInverse R M S i) = LinearMap.id := by sorry

-- Source: BostConjecture/LinearAlgebra/ExteriorPower/BaseChange.lean · baseChangeEquiv
def baseChangeEquiv (i : ℕ) : S ⊗[R] (⋀[R]^i M) ≃ₗ[S] ⋀[S]^i (S ⊗[R] M) where
  __ := baseChangeEquivForward R M S i
  invFun := baseChangeEquivInverse R M S i
  left_inv x := congr($(exteriorPower.baseChange_left_inverse R M S i) x)
  right_inv x := congr($(exteriorPower.baseChange_right_inverse R M S i) x)

-- Source: Arithmetic/DeterminantLine.lean · exteriorPower.instProjective
instance instProjective {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] (n : ℕ) :
    Module.Projective R (⋀[R]^n M) := by sorry

end exteriorPower

namespace BostConjecture.Geometry
open Module exteriorPower
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {a : ℕ}

-- Source: Geometry/DeterminantCoordinates.lean; both linear maps are retained.
def determinantCoordinates (b : Basis (Fin a) R M) : (⋀[R]^a M) ≃ₗ[R] R :=
  LinearEquiv.ofLinearMap (alternatingMapLinearEquiv b.det)
    (LinearMap.toSpanSingleton R _ (ιMulti R a b)) (by sorry) (by sorry)
end BostConjecture.Geometry

namespace BostConjecture.Arithmetic
variable {K : Type*} [Field K]
variable (M : Type*) [AddCommGroup M] [Module (𝓞 K) M]

-- Source: BostConjecture/Arithmetic/DeterminantLine.lean · DeterminantLine
abbrev DeterminantLine := ⋀[𝓞 K]^(Module.finrank K (K ⊗[𝓞 K] M)) M

-- Source: BostConjecture/Arithmetic/DeterminantLine.lean · complexFiber_finrank
lemma complexFiber_finrank (σ : K →+* ℂ) :
    Module.finrank ℂ (ComplexFiber M σ) = Module.finrank K (K ⊗[𝓞 K] M) := by sorry

-- Source: BostConjecture/Arithmetic/DeterminantLine.lean · determinantComplexEquiv
def determinantComplexEquiv (σ : K →+* ℂ) :
    ComplexFiber (DeterminantLine (K := K) M) σ ≃ₗ[ℂ]
      ⋀[ℂ]^(Module.finrank K (K ⊗[𝓞 K] M)) (ComplexFiber M σ) := by
  letI : Algebra (𝓞 K) ℂ := (σ.comp (algebraMap (𝓞 K) K)).toAlgebra
  exact exteriorPower.baseChangeEquiv (𝓞 K) M ℂ _

-- Source: Arithmetic/DeterminantLine.lean. These are Prop-valued instances.
instance determinant_nontrivial [Module.Finite (𝓞 K) M] :
    Nontrivial (DeterminantLine (K := K) M) := by sorry

-- Source: BostConjecture/Arithmetic/DeterminantLine.lean · determinant_generic_finrank
lemma determinant_generic_finrank [Module.Finite (𝓞 K) M] :
    Module.finrank K (K ⊗[𝓞 K] DeterminantLine (K := K) M) = 1 := by sorry

variable {M}
namespace HermitianMetric
variable [Module.Finite (𝓞 K) M]

@[instance_reducible]

-- Source: BostConjecture/Arithmetic/DeterminantMetric.lean · determinantFiber
def determinantFiber (h : HermitianMetric (K := K) M) (σ : K →+* ℂ) :
    InnerProductSpace.Core ℂ (ComplexFiber (DeterminantLine (K := K) M) σ) := by
  letI : InnerProductSpace.Core ℂ (ComplexFiber M σ) := h.fiber σ
  letI := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ComplexFiber M σ)
  letI := InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber M σ))
  let b := (stdOrthonormalBasis ℂ (ComplexFiber M σ)).reindex
    (finCongr (complexFiber_finrank M σ))
  let e := determinantComplexEquiv M σ ≪≫ₗ Geometry.determinantCoordinates b.toBasis
  letI := NormedAddCommGroup.induced _ ℂ e e.injective
  letI := InnerProductSpace.induced e.toLinearMap
  exact InnerProductSpace.toCore

-- Source: BostConjecture/Arithmetic/DeterminantMetric.lean · determinantFiber_conjugate
lemma determinantFiber_conjugate (h : HermitianMetric (K := K) M)
    (σ : K →+* ℂ) (x y : DeterminantLine (K := K) M) :
    (h.determinantFiber (ComplexEmbedding.conjugate σ)).inner
        (fiberSection _ (ComplexEmbedding.conjugate σ) x)
        (fiberSection _ (ComplexEmbedding.conjugate σ) y) =
      star ((h.determinantFiber σ).inner (fiberSection _ σ x) (fiberSection _ σ y)) := by sorry

-- Source: BostConjecture/Arithmetic/DeterminantMetric.lean · determinant
def determinant (h : HermitianMetric (K := K) M) :
    HermitianMetric (K := K) (DeterminantLine (K := K) M) where
  fiber := h.determinantFiber
  conjugate := h.determinantFiber_conjugate

-- Source: BostConjecture/Arithmetic/DeterminantMetric.lean · determinant_sectionNorm_wedge_sq
theorem determinant_sectionNorm_wedge_sq (h : HermitianMetric (K := K) M)
    (σ : K →+* ℂ) (x : Fin (Module.finrank K (K ⊗[𝓞 K] M)) → M) :
    (h.determinant.sectionNorm σ (exteriorPower.ιMulti (𝓞 K) _ x)) ^ 2 =
      ((Matrix.of fun i j => (h.fiber σ).inner
        (fiberSection M σ (x i)) (fiberSection M σ (x j))).det).re := by sorry

end HermitianMetric
end BostConjecture.Arithmetic

namespace BostConjecture.Arithmetic
variable {K : Type*} [Field K] [NumberField K]

-- Source: BostConjecture/Arithmetic/LineDegree.lean · archLog
def archLog (ρ : InfinitePlace K → ℝ) : ℝ :=
  ∑ v, (v.mult : ℝ) * Real.log (ρ v)

-- Source: BostConjecture/Arithmetic/LineDegree.lean · logIdealNorm
def logIdealNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ :=
  Real.log (FractionalIdeal.absNorm I : ℝ)

-- Source: BostConjecture/Arithmetic/LineDegree.lean · lineDegree
def lineDegree (I : FractionalIdeal (𝓞 K)⁰ K) (ρ : InfinitePlace K → ℝ) : ℝ :=
  (-logIdealNorm I - archLog ρ) / (Module.finrank ℚ K : ℝ)

variable {M : Type*} [AddCommGroup M] [Module (𝓞 K) M]

-- Source: BostConjecture/Arithmetic/HermitianLine.lean · lineCoordinate
def lineCoordinate [Module.Finite (𝓞 K) M]
    (hrank : Module.finrank K (K ⊗[𝓞 K] M) = 1) : M →ₗ[𝓞 K] K :=
  ((LinearEquiv.ofFinrankEq (R := K) (K ⊗[𝓞 K] M) K
    (by simpa using hrank)).restrictScalars (𝓞 K)).toLinearMap ∘ₗ
      TensorProduct.mk (𝓞 K) K M 1

section
variable [Module.Finite (𝓞 K) M]

-- Source: BostConjecture/Arithmetic/LineCoordinates.lean · coordinateIdeal
def coordinateIdeal (f : M →ₗ[𝓞 K] K) : FractionalIdeal (𝓞 K)⁰ K :=
  ⟨f.range, FractionalIdeal.isFractional_of_fg (Submodule.fg_range f)⟩

end
namespace HermitianMetric

-- Source: BostConjecture/Arithmetic/HermitianLine.lean · coordinateLength
def coordinateLength (h : HermitianMetric (K := K) M) (f : M →ₗ[𝓞 K] K)
    (x : M) (v : InfinitePlace K) : ℝ :=
  h.sectionNorm v.embedding x / v (f x)

variable [Module.Finite (𝓞 K) M]

-- Source: BostConjecture/Arithmetic/HermitianLine.lean · degreeInCoordinate
def degreeInCoordinate (h : HermitianMetric (K := K) M) (f : M →ₗ[𝓞 K] K) (x : M) : ℝ :=
  lineDegree (coordinateIdeal f) (h.coordinateLength f x)

section
variable [Module.Projective (𝓞 K) M] [Nontrivial M]

-- Source: BostConjecture/Arithmetic/HermitianLine.lean · lineDegree
def lineDegree (h : HermitianMetric (K := K) M)
    (hrank : Module.finrank K (K ⊗[𝓞 K] M) = 1) : ℝ :=
  h.degreeInCoordinate (lineCoordinate hrank) (Classical.choose (exists_ne (0 : M)))

end
variable [Module.Projective (𝓞 K) M]

-- Source: BostConjecture/Arithmetic/Degree.lean · degree
def degree (h : HermitianMetric (K := K) M) : ℝ :=
  h.determinant.lineDegree (determinant_generic_finrank M)

-- Source: BostConjecture/Arithmetic/Degree.lean · slope
def slope (h : HermitianMetric (K := K) M) : ℝ :=
  h.degree / (Module.finrank K (K ⊗[𝓞 K] M) : ℝ)

-- Source: BostConjecture/Arithmetic/Degree.lean · degree_eq
theorem degree_eq (h : HermitianMetric (K := K) M)
    {ξ : DeterminantLine (K := K) M} (hξ : ξ ≠ 0) :
    h.degree = (Real.log (Nat.card (DeterminantLine (K := K) M ⧸ (𝓞 K ∙ ξ))) -
      ∑ σ : K →+* ℂ, Real.log (h.determinant.sectionNorm σ ξ)) / (Module.finrank ℚ K : ℝ) := by sorry

end HermitianMetric
end BostConjecture.Arithmetic

namespace BostConjecture.Arithmetic
variable {K : Type*} [Field K] [numberField : NumberField K]
variable {M N : Type*} [AddCommGroup M] [Module (𝓞 K) M]
variable [AddCommGroup N] [Module (𝓞 K) N]

-- Source: BostConjecture/Arithmetic/SubmoduleMetric.lean · fiberMap
def fiberMap (f : N →ₗ[𝓞 K] M) (σ : K →+* ℂ) :
    ComplexFiber N σ →ₗ[ℂ] ComplexFiber M σ :=
  let : Algebra (𝓞 K) ℂ := (σ.comp (algebraMap (𝓞 K) K)).toAlgebra
  f.baseChange ℂ

-- Source: Arithmetic/SubmoduleMetric.lean; finite submodules over a Dedekind domain.
include numberField in
instance submoduleProjective [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]
    (P : Submodule (𝓞 K) M) : Module.Projective (𝓞 K) P := by sorry
namespace HermitianMetric
-- Source: Arithmetic/SubmoduleMetric.lean. The actual inner product is retained.
include numberField in
def pullback (h : HermitianMetric (K := K) M) (f : N →ₗ[𝓞 K] M)
    (hf : Function.Injective f) : HermitianMetric (K := K) N where
  fiber σ :=
    { inner := fun x y => (h.fiber σ).inner (fiberMap f σ x) (fiberMap f σ y)
      conj_inner_symm := by sorry
      re_inner_nonneg := by sorry
      add_left := by sorry
      smul_left := by sorry
      definite := by sorry }
  conjugate := by sorry

-- Source: BostConjecture/Arithmetic/SubmoduleMetric.lean · submodule
def submodule (h : HermitianMetric (K := K) M) (P : Submodule (𝓞 K) M) :
    HermitianMetric (K := K) P := h.pullback P.subtype P.injective_subtype

end HermitianMetric

-- Source: BostConjecture/Arithmetic/IntegralSubspace.lean · integralPart
def integralPart (X : Submodule K (K ⊗[𝓞 K] M)) : Submodule (𝓞 K) M :=
  (X.restrictScalars (𝓞 K)).comap (TensorProduct.mk (𝓞 K) K M 1)

namespace HermitianMetric
variable [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]

-- Source: BostConjecture/Arithmetic/SubspaceDegree.lean · subspaceDegree
def subspaceDegree (h : HermitianMetric (K := K) M)
    (X : Submodule K (K ⊗[𝓞 K] M)) : ℝ := (h.submodule (integralPart X)).degree

-- Source: BostConjecture/Arithmetic/Semistable.lean · IsSemistable
def IsSemistable (h : HermitianMetric (K := K) M) : Prop :=
  ∀ P : Submodule (𝓞 K) M, 0 < Module.finrank K (K ⊗[𝓞 K] P) →
    (h.submodule P).slope ≤ h.slope

end HermitianMetric
end BostConjecture.Arithmetic

/-! ## Harder–Narasimhan definitions used by the actual `maxSlope`

These definitions are copied from the pinned HarderNarasimhan package, not
imported. They expose the choices used by the original implementation. In
particular `maxSlope` below is not replaced by a new supremum definition.
-/

namespace HarderNarasimhan

-- Source: HarderNarasimhan/StrictIntvl.lean
structure StrictIntvl (ℒ : Type*) [LT ℒ] where
  left : ℒ
  right : ℒ
  lt : left < right

namespace StrictIntvl
variable {ℒ : Type*}
instance [LT ℒ] [LE ℒ] : Membership ℒ (StrictIntvl ℒ) :=
  ⟨fun I x ↦ I.left ≤ x ∧ x ≤ I.right⟩
instance [PartialOrder ℒ] : PartialOrder (StrictIntvl ℒ) where
  le I J := J.left ≤ I.left ∧ I.right ≤ J.right
  le_refl := by sorry
  le_trans := by sorry
  le_antisymm := by sorry
instance [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ] :
    OrderTop (StrictIntvl ℒ) where
  top := ⟨⊥, ⊤, bot_lt_top⟩
  le_top := by sorry
instance [LT ℒ] [LE ℒ] : CoeSort (StrictIntvl ℒ) (Type _) :=
  ⟨fun I ↦ {x // x ∈ I}⟩
variable [PartialOrder ℒ] {I : StrictIntvl ℒ}
instance : Nontrivial ↥I := by sorry
instance : BoundedOrder ↥I where
  bot := ⟨I.left, ⟨le_rfl, I.lt.le⟩⟩
  top := ⟨I.right, ⟨I.lt.le, le_rfl⟩⟩
  bot_le := by sorry
  le_top := by sorry
def ofSub (J : StrictIntvl ↥I) : StrictIntvl ℒ :=
  ⟨J.left, J.right, Subtype.coe_lt_coe.2 J.lt⟩
instance : CoeOut (StrictIntvl ↥I) (StrictIntvl ℒ) := ⟨ofSub⟩
end StrictIntvl

-- Source: HarderNarasimhan/PayoffFunction/Defs.lean
structure PayoffFunction (ℒ : Type*) [LT ℒ] (S : Type*) where
  toFun : StrictIntvl ℒ → S

namespace PayoffFunction
variable {ℒ S : Type*}
instance [LT ℒ] : FunLike (PayoffFunction ℒ S) (StrictIntvl ℒ) S where
  coe := toFun
  coe_injective := by sorry

section
variable [Preorder ℒ] [CompleteLattice S] (μ : PayoffFunction ℒ S)
def max : PayoffFunction ℒ S :=
  ⟨fun I ↦ ⨆ (u : ℒ) (hu : u ∈ Set.Ioc I.left I.right), μ ⟨I.left, u, hu.1⟩⟩
def A : PayoffFunction ℒ S :=
  ⟨fun I ↦ ⨅ (a : ℒ) (ha : a ∈ Set.Ico I.left I.right), μ.max ⟨a, I.right, ha.2⟩⟩
def IsAttained (I : StrictIntvl ℒ) : Prop :=
  ∃ (a : ℒ) (ha : a ∈ Set.Ico I.left I.right), μ.max ⟨a, I.right, ha.2⟩ = μ.A I
end

-- Source: HarderNarasimhan/PayoffFunction/Restrict.lean
def restrict [PartialOrder ℒ] (μ : PayoffFunction ℒ S) (I : StrictIntvl ℒ) :
    PayoffFunction I S := ⟨fun J ↦ μ ↑J⟩

-- Source: HarderNarasimhan/PayoffFunction/Convex.lean
section
variable [Lattice ℒ] [CompleteLattice S]
class IsConvex (μ : PayoffFunction ℒ S) : Prop where
  le : ∀ x y : ℒ, (h : ¬ x ≤ y) →
    μ ⟨x ⊓ y, x, inf_lt_left.2 h⟩ ≤ μ ⟨y, x ⊔ y, right_lt_sup.2 h⟩
class IsConvexOn (μ : PayoffFunction ℒ S) (I : StrictIntvl ℒ) : Prop where
  le : ∀ x y : ℒ, x ∈ I → y ∈ I → (h : ¬ x ≤ y) →
    μ ⟨x ⊓ y, x, inf_lt_left.2 h⟩ ≤ μ ⟨y, x ⊔ y, right_lt_sup.2 h⟩
lemma IsConvexOn.mono {μ : PayoffFunction ℒ S} {I₁ I₂ : StrictIntvl ℒ}
    (h : μ.IsConvexOn I₁) (hI : I₂ ≤ I₁) : μ.IsConvexOn I₂ := by sorry
instance [Nontrivial ℒ] [BoundedOrder ℒ] (μ : PayoffFunction ℒ S) [μ.IsConvex] :
    μ.IsConvexOn ⊤ := by sorry
end

-- Source: HarderNarasimhan/PayoffFunction/Semistable/Defs.lean
class ADCC [Preorder ℒ] [CompleteLattice S] (μ : PayoffFunction ℒ S) : Prop where
  dcc : ∀ a : ℒ, ∀ f : ℕ → ℒ, (h₁ : ∀ n : ℕ, f n > a) → StrictAnti f →
    ∃ N : ℕ, ¬ μ.A ⟨a, f N, h₁ N⟩ < μ.A ⟨a, f (N + 1), h₁ (N + 1)⟩

section
variable [PartialOrder ℒ] [CompleteLattice S]
variable (μ : PayoffFunction ℒ S) (I : StrictIntvl ℒ)
structure IsBreakpoint (x : ℒ) : Prop where
  mem : x ∈ I
  ne_left : I.left ≠ x
  not_lt : ∀ y : ℒ, (hyI : y ∈ I) → (hy : I.left ≠ y) →
    ¬ μ.A ⟨I.left, x, lt_of_le_of_ne mem.1 ne_left⟩ < μ.A ⟨I.left, y, lt_of_le_of_ne hyI.1 hy⟩
  le_of_eq : ∀ y : ℒ, (hyI : y ∈ I) → (hy : I.left ≠ y) →
    μ.A ⟨I.left, y, lt_of_le_of_ne hyI.1 hy⟩ = μ.A ⟨I.left, x, lt_of_le_of_ne mem.1 ne_left⟩ →
      y ≤ x
def breakpoints : Set ℒ := {x | μ.IsBreakpoint I x}
end

class IsSemistable [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ] [CompleteLattice S]
    (μ : PayoffFunction ℒ S) : Prop where
  not_lt : ∀ x : ℒ, (hx : ⊥ < x) → ¬ μ.A ⊤ < μ.A ⟨⊥, x, hx⟩

-- Source: HarderNarasimhan/Filtration/Defs.lean
class Admissible [Preorder ℒ] [CompleteLattice S] (μ : PayoffFunction ℒ S) : Prop where
  total_or_attained : Std.Total (· ≤ · : S → S → Prop) ∨ ∀ I : StrictIntvl ℒ, μ.IsAttained I
instance [Preorder ℒ] [CompleteLinearOrder S] (μ : PayoffFunction ℒ S) : μ.Admissible where
  total_or_attained := Or.inl inferInstance

section
variable [PartialOrder ℒ] [BoundedOrder ℒ] [CompleteLattice S]
structure HarderNarasimhanFiltration (μ : PayoffFunction ℒ S) where
  toFun : ℕ → ℒ
  length : ℕ
  monotone : Monotone toFun
  head_eq_bot : toFun 0 = ⊥
  length_eq_top : toFun length = ⊤
  strictMonoOn : StrictMonoOn toFun (Set.Iic length)
  piecewise_isSemistable : ∀ i, (hi : i < length) →
    (μ.restrict ⟨toFun i, toFun (i + 1), strictMonoOn hi.le hi (lt_add_one i)⟩).IsSemistable
  not_A_le_succ : ∀ i, (hi : i + 1 < length) →
    ¬ μ.A ⟨toFun i, toFun (i + 1),
        strictMonoOn (Nat.le_of_succ_le hi.le) hi.le (lt_add_one i)⟩ ≤
      μ.A ⟨toFun (i + 1), toFun (i + 2), strictMonoOn hi.le hi (lt_add_one (i + 1))⟩
instance {μ : PayoffFunction ℒ S} : FunLike (μ.HarderNarasimhanFiltration) ℕ ℒ where
  coe := HarderNarasimhanFiltration.toFun
  coe_injective := by sorry
end

-- Source: HarderNarasimhan/PayoffFunction/Semistable/Breakpoints.lean
lemma exists_isGreatest_breakpoints [Lattice ℒ] [CompleteLattice S]
    {μ : PayoffFunction ℒ S} {I : StrictIntvl ℒ} [hwf : WellFoundedGT ℒ] [μ.ADCC]
    (hμcvx : μ.IsConvexOn I)
    (h : Std.Total (· ≤ · : S → S → Prop) ∨
      ∀ z : ℒ, (hzI : z ∈ I) → (hz : I.left ≠ z) →
        μ.IsAttained ⟨I.left, z, lt_of_le_of_ne hzI.left hz⟩) :
    ∃ s : ℒ, IsGreatest (μ.breakpoints I) s := by sorry

-- Source: HarderNarasimhan/Filtration/Exists.lean
-- The original private names HNFil and HNlen are exposed here for review.
section
variable [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [hwf : WellFoundedGT ℒ]
variable [CompleteLattice S]
variable (μ : PayoffFunction ℒ S) [μ.ADCC] [μ.IsConvex] [hadm : μ.Admissible]
open Classical in
def HNFil (k : ℕ) : ℒ :=
  match k with
  | 0 => ⊥
  | n + 1 =>
    let prev := HNFil n
    if htop : prev = ⊤ then
      ⊤
    else
      (exists_isGreatest_breakpoints (I := ⟨prev, ⊤, lt_top_iff_ne_top.2 htop⟩)
        ((inferInstance : μ.IsConvexOn ⊤).mono le_top)
        (hadm.total_or_attained.imp id fun h z hzI hz ↦
          h ⟨prev, z, lt_of_le_of_ne hzI.left hz⟩)).choose
lemma HNFil_exists_eq_top : ∃ N : ℕ, HNFil μ N = ⊤ := by sorry
open Classical in
def HNlen : ℕ := Nat.find (HNFil_exists_eq_top μ)
def hnFiltration : μ.HarderNarasimhanFiltration where
  toFun := HNFil μ
  length := HNlen μ
  monotone := by sorry
  head_eq_bot := by sorry
  length_eq_top := by sorry
  strictMonoOn := by sorry
  piecewise_isSemistable := by sorry
  not_A_le_succ := by sorry
end

-- Source: HarderNarasimhan/PayoffFunction/Slope.lean
section
variable [PartialOrder ℒ]
variable {V : Type*} [AddCommGroup V] [Module ℝ V] [LinearOrder V] [IsOrderedAddMonoid V]
  [PosSMulStrictMono ℝ V]
def slope (r : StrictIntvl ℒ → ℝ≥0) (d : StrictIntvl ℒ → V) :
    PayoffFunction ℒ (DedekindCut V) :=
  ⟨fun I ↦ if _ : 0 < r I then .principal ((r I)⁻¹ • d I) else ⊤⟩
end
end PayoffFunction
end HarderNarasimhan

open HarderNarasimhan
open scoped NNReal

namespace BostConjecture.Subspace
-- Source: BostConjecture/Slope/Subspace.lean
variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
def intervalRank (I : StrictIntvl (Submodule K V)) : ℝ≥0 :=
  (Module.finrank K I.right - Module.finrank K I.left : ℕ)
def slope (degree : Submodule K V → ℝ) :
    PayoffFunction (Submodule K V) (DedekindCut ℝ) :=
  PayoffFunction.slope intervalRank (fun I => degree I.right - degree I.left)
end BostConjecture.Subspace

namespace BostConjecture.Slope
-- Source: BostConjecture/Slope/FiniteLength.lean
instance adcc_of_wellFoundedLT {L S : Type*} [Lattice L] [BoundedOrder L]
    [CompleteLinearOrder S] (μ : PayoffFunction L S) [WellFoundedLT L] : μ.ADCC := by sorry
end BostConjecture.Slope

namespace BostConjecture.Arithmetic.HermitianMetric
variable {K : Type*} [Field K] [NumberField K]
variable {M : Type*} [AddCommGroup M] [Module (𝓞 K) M]
variable [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]
-- Source: BostConjecture/Arithmetic/SubspaceSupermodular.lean
instance subspaceSlope_isConvex (h : HermitianMetric (K := K) M) :
    (BostConjecture.Subspace.slope h.subspaceDegree).IsConvex := by sorry

variable [Nontrivial (K ⊗[𝓞 K] M)]
-- Source: BostConjecture/Arithmetic/SubspaceHN.lean
def hnFlag (h : HermitianMetric (K := K) M) :
    (BostConjecture.Subspace.slope h.subspaceDegree).HarderNarasimhanFiltration :=
  (BostConjecture.Subspace.slope h.subspaceDegree).hnFiltration
def hnSubmodule (h : HermitianMetric (K := K) M) (n : ℕ) : Submodule (𝓞 K) M :=
  integralPart (h.hnFlag n)

-- Source: BostConjecture/Arithmetic/HermitianHN.lean
/-- The actual definition in the proved project: slope of the first saturated HN term. -/
def maxSlope (h : HermitianMetric (K := K) M) : ℝ :=
  (h.submodule (h.hnSubmodule 1)).slope

/-- Reading aid: the HN definition realizes the maximum over ALL positive-rank
integral submodules, with their induced metrics. Proof omitted in this copy. -/
theorem isGreatest_slopes (h : HermitianMetric (K := K) M) :
    IsGreatest {s : ℝ | ∃ P : Submodule (𝓞 K) M,
      0 < Module.finrank K (K ⊗[𝓞 K] P) ∧ (h.submodule P).slope = s} h.maxSlope := by sorry
end BostConjecture.Arithmetic.HermitianMetric

/-! ## The actual Hilbert tensor metric -/
namespace BostConjecture.Tensor
variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
variable {ι : Type*} (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]

-- Source: BostConjecture/Tensor/BaseChange.lean · scalarExtension
def scalarExtension : (⨂[R] i, M i) →ₗ[R] (⨂[S] i, S ⊗[R] M i) :=
  PiTensorProduct.lift <| ((PiTensorProduct.tprod S).restrictScalars R).compLinearMap
    (fun i => TensorProduct.mk R S (M i) 1)

-- Source: BostConjecture/Tensor/BaseChange.lean · baseChangeMap
def baseChangeMap : S ⊗[R] (⨂[R] i, M i) →ₗ[S] (⨂[S] i, S ⊗[R] M i) :=
  TensorProduct.AlgebraTensorModule.lift
    { toFun := fun s => s • scalarExtension R S M
      map_add' := by intros; simp [add_smul]
      map_smul' := by intros; simp [smul_smul] }

-- Source: BostConjecture/Tensor/BaseChange.lean · baseChangeMap_bijective
theorem baseChangeMap_bijective [Finite ι] : Function.Bijective (baseChangeMap R S M) := by sorry

-- Source: BostConjecture/Tensor/BaseChange.lean · baseChangeEquiv
def baseChangeEquiv [Finite ι] :
    S ⊗[R] (⨂[R] i, M i) ≃ₗ[S] (⨂[S] i, S ⊗[R] M i) :=
  LinearEquiv.ofBijective (baseChangeMap R S M) (baseChangeMap_bijective R S M)

end BostConjecture.Tensor
namespace BostConjecture.Tensor
variable {ι : Type*} (E : ι → Type*) [∀ i, NormedAddCommGroup (E i)]
  [∀ i, InnerProductSpace ℂ (E i)]

-- Source: BostConjecture/Tensor/Hilbert.lean · exists_hilbertCore
theorem exists_hilbertCore [Finite ι] :
    ∃ h : InnerProductSpace.Core ℂ (⨂[ℂ] i, E i),
      ∀ x y : ∀ i, E i, h.inner (PiTensorProduct.tprod ℂ x) (PiTensorProduct.tprod ℂ y) = ∏ᶠ i, inner ℂ (x i) (y i) := by sorry

@[instance_reducible]

-- Source: BostConjecture/Tensor/Hilbert.lean · hilbertCore
def hilbertCore [Finite ι] : InnerProductSpace.Core ℂ (⨂[ℂ] i, E i) :=
  (exists_hilbertCore E).choose

-- Source: BostConjecture/Tensor/Hilbert.lean · hilbertCore_inner_tprod
theorem hilbertCore_inner_tprod [Finite ι] (x y : ∀ i, E i) :
    (hilbertCore E).inner (PiTensorProduct.tprod ℂ x) (PiTensorProduct.tprod ℂ y) = ∏ᶠ i, inner ℂ (x i) (y i) := by sorry

end BostConjecture.Tensor
namespace BostConjecture.Arithmetic
variable {K : Type*} [Field K] {ι : Type*} [Fintype ι]
variable (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module (𝓞 K) (M i)]

-- Source: BostConjecture/Arithmetic/TensorMetric.lean · tensorFiberEquiv
def tensorFiberEquiv (σ : K →+* ℂ) :
    ComplexFiber (⨂[𝓞 K] i, M i) σ ≃ₗ[ℂ] (⨂[ℂ] i, ComplexFiber (M i) σ) :=
  letI : Algebra (𝓞 K) ℂ := (σ.comp (algebraMap (𝓞 K) K)).toAlgebra
  Tensor.baseChangeEquiv (𝓞 K) ℂ M

variable {M}
namespace HermitianMetric
-- `import Mathlib` additionally registers a projective tensor seminorm.
-- Exclude it for this definition to retain the original Hilbert-core instances.
attribute [-instance] PiTensorProduct.instSeminormedAddCommGroup in
@[instance_reducible]

-- Source: BostConjecture/Arithmetic/TensorMetric.lean · tensorFiber
def tensorFiber (h : ∀ i, HermitianMetric (K := K) (M i)) (σ : K →+* ℂ) :
    InnerProductSpace.Core ℂ (ComplexFiber (⨂[𝓞 K] i, M i) σ) := by
  letI : ∀ i, InnerProductSpace.Core ℂ (ComplexFiber (M i) σ) := fun i => (h i).fiber σ
  letI : ∀ i, NormedAddCommGroup (ComplexFiber (M i) σ) := fun i =>
    InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ComplexFiber (M i) σ)
  letI : ∀ i, InnerProductSpace ℂ (ComplexFiber (M i) σ) := fun i =>
    InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber (M i) σ))
  letI := Tensor.hilbertCore (fun i => ComplexFiber (M i) σ)
  letI := InnerProductSpace.Core.toNormedAddCommGroup
    (𝕜 := ℂ) (F := ⨂[ℂ] i, ComplexFiber (M i) σ)
  letI := InnerProductSpace.ofCore
    (inferInstance : PreInnerProductSpace.Core ℂ (⨂[ℂ] i, ComplexFiber (M i) σ))
  letI := NormedAddCommGroup.induced _ _ (tensorFiberEquiv M σ) (tensorFiberEquiv M σ).injective
  letI := InnerProductSpace.induced (tensorFiberEquiv M σ).toLinearMap
  exact InnerProductSpace.toCore

-- Source: BostConjecture/Arithmetic/TensorMetric.lean · tensorFiber_inner_tprod
lemma tensorFiber_inner_tprod (h : ∀ i, HermitianMetric (K := K) (M i))
    (σ : K →+* ℂ) (x y : ∀ i, M i) :
    (tensorFiber h σ).inner (fiberSection _ σ (PiTensorProduct.tprod (𝓞 K) x))
      (fiberSection _ σ (PiTensorProduct.tprod (𝓞 K) y)) =
        ∏ i, ((h i).fiber σ).inner (fiberSection (M i) σ (x i))
          (fiberSection (M i) σ (y i)) := by sorry

-- Source: BostConjecture/Arithmetic/TensorMetric.lean · tensorFiber_conjugate
lemma tensorFiber_conjugate (h : ∀ i, HermitianMetric (K := K) (M i))
    (σ : K →+* ℂ) (x y : ⨂[𝓞 K] i, M i) :
    (tensorFiber h (ComplexEmbedding.conjugate σ)).inner
      (fiberSection _ (ComplexEmbedding.conjugate σ) x)
      (fiberSection _ (ComplexEmbedding.conjugate σ) y) =
        star ((tensorFiber h σ).inner (fiberSection _ σ x) (fiberSection _ σ y)) := by sorry

-- Source: BostConjecture/Arithmetic/TensorMetric.lean · piTensor
def piTensor (h : ∀ i, HermitianMetric (K := K) (M i)) :
    HermitianMetric (K := K) (⨂[𝓞 K] i, M i) where
  fiber := tensorFiber h
  conjugate := tensorFiber_conjugate h

-- Source: BostConjecture/Arithmetic/TensorMetric.lean · sectionNorm_piTensor_tprod
lemma sectionNorm_piTensor_tprod (h : ∀ i, HermitianMetric (K := K) (M i))
    (σ : K →+* ℂ) (x : ∀ i, M i) :
    (piTensor h).sectionNorm σ (PiTensorProduct.tprod (𝓞 K) x) = ∏ i, (h i).sectionNorm σ (x i) := by sorry

end HermitianMetric
end BostConjecture.Arithmetic
namespace BostConjecture.Arithmetic
universe u

-- Source: BostConjecture/Arithmetic/BinaryTensorMetric.lean · binaryTensorFamily
abbrev binaryTensorFamily (M N : Type u) : Unit ⊕ Unit → Type u
  | .inl _ => M
  | .inr _ => N

-- Source: BostConjecture/Arithmetic/BinaryTensorMetric.lean · data instances
instance {M N : Type u} [AddCommGroup M] [AddCommGroup N] (i : Unit ⊕ Unit) :
    AddCommGroup (binaryTensorFamily M N i) :=
  Sum.casesOn i (fun _ => inferInstance) (fun _ => inferInstance)
instance {R : Type*} [CommRing R] {M N : Type u}
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N] (i : Unit ⊕ Unit) :
    Module R (binaryTensorFamily M N i) :=
  Sum.casesOn i (fun _ => inferInstance) (fun _ => inferInstance)
variable (R : Type*) [CommRing R] (M N : Type u)
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]

-- Source: BostConjecture/Arithmetic/BinaryTensorMetric.lean · binaryTensorEquiv
def binaryTensorEquiv :
    M ⊗[R] N ≃ₗ[R] (⨂[R] i, binaryTensorFamily M N i) :=
  (TensorProduct.congr (subsingletonEquiv (R := R) (s := fun _ : Unit => M) ()).symm
    (subsingletonEquiv (R := R) (s := fun _ : Unit => N) ()).symm).trans
      (tmulEquivDep R (binaryTensorFamily M N))

variable {R M N}
variable {K : Type*} [Field K] [NumberField K] [Module (𝓞 K) M] [Module (𝓞 K) N]
namespace HermitianMetric

-- Source: BostConjecture/Arithmetic/BinaryTensorMetric.lean · tensor
def tensor (h : HermitianMetric (K := K) M) (g : HermitianMetric (K := K) N) :
    HermitianMetric (K := K) (M ⊗[𝓞 K] N) :=
  (piTensor (fun i : Unit ⊕ Unit => Sum.casesOn i (fun _ => h) (fun _ => g))).pullback
    (binaryTensorEquiv (𝓞 K) M N).toLinearMap (binaryTensorEquiv (𝓞 K) M N).injective

-- Source: BostConjecture/Arithmetic/BinaryTensorMetric.lean · sectionNorm_tensor_tmul
lemma sectionNorm_tensor_tmul (h : HermitianMetric (K := K) M)
    (g : HermitianMetric (K := K) N) (σ : K →+* ℂ) (x : M) (y : N) :
    (h.tensor g).sectionNorm σ (x ⊗ₜ[𝓞 K] y) = h.sectionNorm σ x * g.sectionNorm σ y := by sorry

end HermitianMetric
end BostConjecture.Arithmetic

-- Source: BostConjecture/Main/MaxSlope/LowerBound.lean · tensorGenericNontrivial
-- Explicit binders preserve hypotheses formerly used only inside the proof.
namespace BostConjecture.Arithmetic.HermitianMetric
universe u
instance tensorGenericNontrivial {K : Type*} [Field K] [NumberField K]
    {M N : Type u} [AddCommGroup M] [Module (𝓞 K) M]
    [AddCommGroup N] [Module (𝓞 K) N]
    [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]
    [Module.Finite (𝓞 K) N] [Module.Projective (𝓞 K) N]
    [Nontrivial (K ⊗[𝓞 K] M)] [Nontrivial (K ⊗[𝓞 K] N)] :
    Nontrivial (K ⊗[𝓞 K] (M ⊗[𝓞 K] N)) := by sorry
end BostConjecture.Arithmetic.HermitianMetric

/-! ## Main theorem — manuscript Theorem 1.1

`M` and `N` are finite projective modules over the full ring of integers of an
arbitrary number field `K`. Together with `h` and `g` they are the Hermitian
vector bundles. The nontrivial generic fibers impose positive ranks. All metrics
and slopes in the equality are the definitions above, with degree normalized
by `[K : ℚ]`. There are no additional geometric or analytic hypotheses.
-/
namespace BostConjecture.Arithmetic.HermitianMetric
universe u
variable {K M N : Type u} [Field K] [NumberField K]
variable [AddCommGroup M] [Module (𝓞 K) M] [AddCommGroup N] [Module (𝓞 K) N]
variable [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]
variable [Module.Finite (𝓞 K) N] [Module.Projective (𝓞 K) N]
variable [Nontrivial (K ⊗[𝓞 K] M)] [Nontrivial (K ⊗[𝓞 K] N)]

-- Source: BostConjecture/Main/MaxSlope/Tensor.lean · maxSlope_tensor
theorem maxSlope_tensor (h : HermitianMetric (K := K) M)
    (g : HermitianMetric (K := K) N) :
    (h.tensor g).maxSlope = h.maxSlope + g.maxSlope := by sorry

end BostConjecture.Arithmetic.HermitianMetric
