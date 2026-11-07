/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Arithmetic.Compactness.Frames.SequentialCompactness
public import BostConjecture.Arithmetic.Compactness.Topology.TensorContinuity
public import BostConjecture.Arithmetic.Compactness.Maximum.Transport
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
open scoped Topology

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
    ∃ h : HermitianMetric K M, ∃ g : HermitianMetric K N,
      Module.finrank K (K ⊗[𝓞 K] M) = a ∧ Module.finrank K (K ⊗[𝓞 K] N) = b ∧
      h.degree = 0 ∧ g.degree = 0 ∧ h.IsSemistable ∧ g.IsSemistable ∧
      (h.tensor g).maxDegree = d}

/-- An actual pair supplies a point of the realized-value set. -/
theorem tensor_maxDegree_mem {M N : Type u}
    [AddCommGroup M] [Module (𝓞 K) M] [Module.Finite (𝓞 K) M]
    [Module.Projective (𝓞 K) M] [AddCommGroup N] [Module (𝓞 K) N]
    [Module.Finite (𝓞 K) N] [Module.Projective (𝓞 K) N]
    (h : HermitianMetric K M) (g : HermitianMetric K N) {a b : ℕ}
    (hrM : Module.finrank K (K ⊗[𝓞 K] M) = a)
    (hrN : Module.finrank K (K ⊗[𝓞 K] N) = b)
    (h0 : h.degree = 0) (g0 : g.degree = 0) (hs : h.IsSemistable) (gs : g.IsSemistable) :
    (h.tensor g).maxDegree ∈ tensorMaxDegreeValues.{u} K a b :=
  ⟨M, N, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, h, g,
    hrM, hrN, h0, g0, hs, gs, rfl⟩

/-- Arithmetic compactness in both factors gives compactness of the actual value set. -/
theorem isCompact_tensorMaxDegreeValues (a b : ℕ) :
    IsCompact (tensorMaxDegreeValues.{u} K a b) := by
  apply isCompact_iff_isSeqCompact.mpr
  intro v hv
  choose A B am an mm mn fm pm fn pn h g hrA hrB h0 g0 hs gs hval using hv
  let : ∀ n, AddCommGroup (A n) := am
  let : ∀ n, AddCommGroup (B n) := an
  let : ∀ n, Module (𝓞 K) (A n) := mm
  let : ∀ n, Module (𝓞 K) (B n) := mn
  let : ∀ n, Module.Finite (𝓞 K) (A n) := fm
  let : ∀ n, Module.Projective (𝓞 K) (A n) := pm
  let : ∀ n, Module.Finite (𝓞 K) (B n) := fn
  let : ∀ n, Module.Projective (𝓞 K) (B n) := pn
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
    dsimp only [Function.comp_def] at hobj
    rwa [heq] at hobj

/-- A nonempty collection of actual normalized semistable pairs has a global
maximizing pair, together with an actual saturated tensor maximizer. -/
theorem exists_maximizing_pair (a b : ℕ)
    (hne : (tensorMaxDegreeValues.{u} K a b).Nonempty) :
    ∃ M N : Type u, ∃ am : AddCommGroup M, ∃ an : AddCommGroup N,
    letI := am; letI := an;
    ∃ mm : Module (𝓞 K) M, ∃ mn : Module (𝓞 K) N,
    letI := mm; letI := mn;
    ∃ fm : Module.Finite (𝓞 K) M, ∃ pm : Module.Projective (𝓞 K) M,
    ∃ fn : Module.Finite (𝓞 K) N, ∃ pn : Module.Projective (𝓞 K) N,
    letI := fm; letI := pm; letI := fn; letI := pn;
    ∃ h : HermitianMetric K M, ∃ g : HermitianMetric K N,
      Module.finrank K (K ⊗[𝓞 K] M) = a ∧ Module.finrank K (K ⊗[𝓞 K] N) = b ∧
      h.degree = 0 ∧ g.degree = 0 ∧ h.IsSemistable ∧ g.IsSemistable ∧
      ∃ P : Submodule (𝓞 K) (M ⊗[𝓞 K] N),
        Module.IsTorsionFree (𝓞 K) ((M ⊗[𝓞 K] N) ⧸ P) ∧
        ((h.tensor g).submodule P).degree = (h.tensor g).maxDegree ∧
        IsGreatest (tensorMaxDegreeValues.{u} K a b) (h.tensor g).maxDegree := by
  obtain ⟨d, hd, hmax⟩ := (isCompact_tensorMaxDegreeValues (K := K) a b).exists_isGreatest hne
  rcases hd with ⟨M, N, am, an, mm, mn, fm, pm, fn, pn, h, g, hrM, hrN, h0, g0, hs, gs, hval⟩
  let : AddCommGroup M := am
  let : AddCommGroup N := an
  let : Module (𝓞 K) M := mm
  let : Module (𝓞 K) N := mn
  let : Module.Finite (𝓞 K) M := fm
  let : Module.Projective (𝓞 K) M := pm
  let : Module.Finite (𝓞 K) N := fn
  let : Module.Projective (𝓞 K) N := pn
  obtain ⟨P, hP, hdeg⟩ := (h.tensor g).exists_degree_eq_maxDegree
  refine ⟨M, N, am, an, mm, mn, fm, pm, fn, pn, h, g, hrM, hrN, h0, g0, hs, gs,
    P, hP, hdeg, tensor_maxDegree_mem h g hrM hrN h0 g0 hs gs, ?_⟩
  rwa [hval]

end BostConjecture.Arithmetic.Compactness
