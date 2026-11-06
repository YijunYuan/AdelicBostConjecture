module

public import BostConjecture.Arithmetic.Compactness.SequentialCompactness
public import BostConjecture.Arithmetic.Compactness.TensorContinuity
public import BostConjecture.Arithmetic.Compactness.MaximumTransport
public import Mathlib.Topology.Order.Compact

/-!
# Maximizing normalized semistable pairs

The value set below quantifies over actual modules and existing Hermitian
metrics. Arithmetic compactness proves its sequential compactness, with no
additional bundle representation or assumed extremal certificate.
-/

@[expose] public section

noncomputable section

open NumberField TensorProduct Filter
open scoped Topology Classical

namespace BostConjecture.Arithmetic.Compactness

universe u
variable {K : Type*} [Field K] [NumberField K]

/-- Real values attained by actual normalized semistable pairs of the fixed ranks.
The existential instance binders retain arbitrary, possibly nonfree, modules. -/
def tensorMaxDegreeValues (K : Type*) [Field K] [NumberField K] (a b : ℕ) : Set ℝ :=
  {d | ∃ M N : Type u, ∃ am : AddCommGroup M, ∃ an : AddCommGroup N,
    letI := am; letI := an;
    ∃ mm : Module (𝓞 K) M, ∃ mn : Module (𝓞 K) N,
    letI := mm; letI := mn;
    ∃ fm : Module.Finite (𝓞 K) M, ∃ pm : Module.Projective (𝓞 K) M,
    ∃ fn : Module.Finite (𝓞 K) N, ∃ pn : Module.Projective (𝓞 K) N,
    letI := fm; letI := pm; letI := fn; letI := pn;
    ∃ h : HermitianMetric (K := K) M, ∃ g : HermitianMetric (K := K) N,
      Module.finrank K (K ⊗[𝓞 K] M) = a ∧ Module.finrank K (K ⊗[𝓞 K] N) = b ∧
      h.degree = 0 ∧ g.degree = 0 ∧ h.IsSemistable ∧ g.IsSemistable ∧
      (h.tensor g).maxDegree = d}

/-- Arithmetic compactness in both factors gives compactness of the actual value set. -/
theorem isCompact_tensorMaxDegreeValues (a b : ℕ) :
    IsCompact (tensorMaxDegreeValues.{u} K a b) := by
  apply isCompact_iff_isSeqCompact.mpr
  intro v hv
  choose A B am an mm mn fm pm fn pn h g hrA hrB h0 g0 hs gs hval using hv
  letI : ∀ n, AddCommGroup (A n) := am
  letI : ∀ n, AddCommGroup (B n) := an
  letI : ∀ n, Module (𝓞 K) (A n) := mm
  letI : ∀ n, Module (𝓞 K) (B n) := mn
  letI : ∀ n, Module.Finite (𝓞 K) (A n) := fm
  letI : ∀ n, Module.Projective (𝓞 K) (A n) := pm
  letI : ∀ n, Module.Finite (𝓞 K) (B n) := fn
  letI : ∀ n, Module.Projective (𝓞 K) (B n) := pn
  obtain ⟨φ, hφ, m, e, H, H0, Hs, hH⟩ :=
    exists_normalized_semistable_subsequence A h a hrA h0 hs
  obtain ⟨ψ, hψ, n, f, G, G0, Gs, hG⟩ :=
    exists_normalized_semistable_subsequence (fun n => B (φ n)) (fun n => g (φ n)) b
      (fun n => hrB (φ n)) (fun n => g0 (φ n)) (fun n => gs (φ n))
  have hpair := (hH.comp hψ.tendsto_atTop).prodMk_nhds hG
  have hobj := HermitianMetric.continuous_tensor_maxDegree.tendsto (H, G) |>.comp hpair
  refine ⟨(H.tensor G).maxDegree, ?_, φ ∘ ψ, hφ.comp hψ, ?_⟩
  · exact ⟨A m, B (φ n), inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, inferInstance, inferInstance, inferInstance, H, G,
      hrA m, hrB (φ n), H0, G0, Hs, Gs, rfl⟩
  · have heq : (fun k => ((h (φ (ψ k))).pullback (e (ψ k)).toLinearMap
          (e (ψ k)).injective |>.tensor
          ((g (φ (ψ k))).pullback (f k).toLinearMap (f k).injective)).maxDegree) =
        v ∘ (φ ∘ ψ) := by
      funext k
      exact ((h (φ (ψ k))).maxDegree_tensor_pullback_equiv (g (φ (ψ k)))
        (e (ψ k)) (f k)).trans (hval (φ (ψ k)))
    rwa [heq] at hobj

end BostConjecture.Arithmetic.Compactness
