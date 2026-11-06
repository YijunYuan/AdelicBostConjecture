module

public import BostConjecture.Arithmetic.Compactness.TraceFrames
public import BostConjecture.Arithmetic.Compactness.FixedAction
public import BostConjecture.Arithmetic.Compactness.FrameLimit
public import BostConjecture.Arithmetic.Compactness.MetricTransport
public import Mathlib.Topology.Sequences

/-!
# Arithmetic sequential compactness for actual Hermitian modules

Normalized semistable modules of fixed generic rank have a subsequence which,
after actual ring-linear isomorphisms, converges on one fixed integral module
to a normalized semistable Hermitian metric. The exact covolume producer and
accepted real Mahler theorem are consumed, not postulated.

Reference: bost_specht_manuscript.pdf, page 11, Lemma 7.1.
-/

@[expose] public section

noncomputable section

open NumberField TensorProduct Matrix Filter
open scoped Classical Topology

namespace BostConjecture.Arithmetic.Compactness

universe u

variable {K : Type*} [Field K] [NumberField K]

/-- Actual arithmetic compactness, including arbitrary nonfree projective
modules. The fixed module is one of the original sequence's modules. -/
theorem exists_normalized_semistable_subsequence
    (A : ℕ → Type u) [∀ n, AddCommGroup (A n)] [∀ n, Module (𝓞 K) (A n)]
    [∀ n, Module.Finite (𝓞 K) (A n)] [∀ n, Module.Projective (𝓞 K) (A n)]
    (h : ∀ n, HermitianMetric (K := K) (A n)) (r : ℕ)
    (hr : ∀ n, Module.finrank K (K ⊗[𝓞 K] A n) = r)
    (h0 : ∀ n, (h n).degree = 0) (hs : ∀ n, (h n).IsSemistable) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ m : ℕ,
      ∃ e : ∀ n, A m ≃ₗ[𝓞 K] A (φ n),
      ∃ g : HermitianMetric (K := K) (A m),
        g.degree = 0 ∧ g.IsSemistable ∧
        Tendsto (fun n => (h (φ n)).pullback (e n).toLinearMap (e n).injective)
          atTop (𝓝 g) := by
  let E := EuclideanSpace ℝ (Fin (Module.finrank ℚ K * r))
  let e₀ := stdOrthonormalBasis ℝ E
  have hd (n : ℕ) : Module.finrank ℝ (h n).TraceSpace = Module.finrank ℝ E := by
    rw [(h n).traceSpace_finrank, hr n]
    simp [E]
  let b₀ n := (stdOrthonormalBasis ℝ (h n).TraceSpace).reindex (finCongr (hd n))
  obtain ⟨S, hS, hframes⟩ := exists_compact_trace_frames (K := K) r e₀
  choose b B hBS hB using fun n => hframes (A n) (h n) (hr n) (h0 n) (hs n) (b₀ n)
  obtain ⟨φ, hφ, e, he⟩ := exists_module_identifications_of_compact_frames
    A (Module.finBasis ℤ (𝓞 K)) h b b₀ hS B hBS hB
  let : FirstCountableTopology
      (Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ) :=
    inferInstanceAs (FirstCountableTopology
      (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ))
  let : FirstCountableTopology
      (Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isInducing.firstCountableTopology
  let : FirstCountableTopology (GeneralLinearGroup (Fin (Module.finrank ℝ E)) ℝ) :=
    Units.isEmbedding_embedProduct.isInducing.firstCountableTopology
  obtain ⟨Blim, _, ψ, hψ, hlim⟩ := hS.tendsto_subseq (fun n => hBS (φ n))
  let H n := (h (φ (ψ n))).pullback (e (ψ n)).toLinearMap (e (ψ n)).injective
  have hGram (n i j) :
      inner ℝ ((H n).traceSection (b (φ 0) i)) ((H n).traceSection (b (φ 0) j)) =
        ∑ k, (B (φ (ψ n))).val k i * (B (φ (ψ n))).val k j := by
    have ht := (h (φ (ψ n))).trace_inner_eq_sum_frame (b (φ (ψ n)))
      (b₀ (φ (ψ n))) (B (φ (ψ n))) (hB (φ (ψ n))) i j
    change (∑ σ : K →+* ℂ, (((H n).fiber σ).inner
      (fiberSection (A (φ 0)) σ (b (φ 0) i))
      (fiberSection (A (φ 0)) σ (b (φ 0) j))).re) = _
    simp only [H, HermitianMetric.pullback_inner, fiberMap_section,
      LinearEquiv.coe_coe, he]
    exact ht
  obtain ⟨g, hg⟩ := HermitianMetric.exists_metric_limit_of_trace_frames H (b (φ 0))
    (fun n => B (φ (ψ n))) Blim hlim hGram
  have hnorm (n) : (H n).degree = 0 := by
    dsimp only [H]
    rw [HermitianMetric.degree_pullback_equiv, h0]
  have hsemi (n) : (H n).IsSemistable := (hs (φ (ψ n))).pullback_equiv (e (ψ n))
  have hclosed := HermitianMetric.normalized_semistable_of_tendsto hg
    (Eventually.of_forall fun n => ⟨hnorm n, hsemi n⟩)
  exact ⟨φ ∘ ψ, hφ.comp hψ, φ 0, fun n => e (ψ n), g, hclosed.1, hclosed.2, hg⟩

end BostConjecture.Arithmetic.Compactness
