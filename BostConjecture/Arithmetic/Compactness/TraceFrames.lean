module

public import BostConjecture.Arithmetic.Compactness.TraceSystole
public import BostConjecture.Arithmetic.RestrictionCovolume.Main
public import OAI.NumberTheory.ArithmeticGroups.Lattices.FrameMatrices

/-!
# Uniform compact frames for actual arithmetic trace lattices

The exact discriminant–degree covolume formula and the actual semistable
systole meet the hypotheses of the accepted compact-frame Mahler theorem.
Transport to one fixed Euclidean space gives a compact set independent of
the module and metric, including nonfree modules over the ring of integers.

Reference: bost_specht_manuscript.pdf, page 11, Lemma 7.1.
-/

@[expose] public section

noncomputable section

open NumberField TensorProduct MeasureTheory Matrix
open OAI.NumberTheory.ArithmeticGroups.Lattices.FrameMatrices.Construction

namespace BostConjecture.Arithmetic.Compactness

universe u

variable {K : Type*} [Field K] [NumberField K]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- A single compact family of coordinate frames contains an integral frame
for every actual normalized semistable metric of the prescribed rank. -/
theorem exists_compact_trace_frames (r : ℕ)
    (e₀ : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E) :
    ∃ S : Set (GeneralLinearGroup (Fin (Module.finrank ℝ E)) ℝ), IsCompact S ∧
      ∀ (M : Type u) [AddCommGroup M] [Module (𝓞 K) M]
        [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]
        (h : HermitianMetric (K := K) M),
        Module.finrank K (K ⊗[𝓞 K] M) = r → h.degree = 0 → h.IsSemistable →
        ∀ b₀ : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ h.TraceSpace,
        ∃ b : Module.Basis (Fin (Module.finrank ℝ E)) ℤ M,
          ∃ B ∈ S, B.val = b₀.toBasis.toMatrix (h.traceBasis b) := by
  let c : ℝ := |(NumberField.discr K : ℝ)| ^ ((r : ℝ) / 2)
  have hc : 0 < c := Real.rpow_pos_of_pos (by
    apply abs_pos.mpr
    exact_mod_cast NumberField.discr_ne_zero K) _
  have hε : 0 < Real.sqrt (Module.finrank ℚ K : ℝ) :=
    Real.sqrt_pos.mpr (by exact_mod_cast Module.finrank_pos (R := ℚ) (M := K))
  obtain ⟨S, hS, hframes⟩ := exists_compact_lattice_matrices
    (volume : Measure E) e₀.toBasis _ c c hε hc
  refine ⟨S, hS, ?_⟩
  intro M _ _ _ _ h hr h0 hs b₀
  let e : E ≃ₗᵢ[ℝ] h.TraceSpace := e₀.equiv b₀ (Equiv.refl _)
  let L := ZLattice.comap ℝ h.traceLattice e.toContinuousLinearEquiv.toLinearMap
  have hvol : ZLattice.covolume L = c := by
    rw [ZLattice.covolume_comap h.traceLattice volume volume e.measurePreserving]
    change h.traceCovolume = c
    rw [h.traceCovolume_eq_discr_degree, hr, h0]
    simp [c]
  obtain ⟨bL, B, hBS, hB⟩ := hframes L (le_of_eq hvol.symm) hvol.le (by
    intro x hx hx0
    have hb := hs.traceLattice_systole h0 (e x) hx
      (fun he => hx0 (e.injective (by simpa using he)))
    simpa only [e.norm_map] using hb)
  let eL : M ≃ₗ[ℤ] L := h.traceLatticeEquiv.trans
    (ZLattice.comap_equiv ℝ h.traceLattice e.toLinearEquiv)
  let b := bL.map eL.symm
  refine ⟨b, B, hBS, ?_⟩
  rw [hB]
  have heB (i) : e (bL i).val = h.traceSection (b i) := by
    have hi := congrArg Subtype.val (eL.apply_symm_apply (bL i))
    change e.symm (h.traceSection (b i)) = (bL i).val at hi
    exact (congrArg e hi).symm.trans (e.apply_symm_apply _)
  ext i j
  simp only [Module.Basis.toMatrix_apply, b₀.coe_toBasis_repr_apply,
    e₀.coe_toBasis_repr_apply, HermitianMetric.traceBasis_apply,
    ← heB j, OrthonormalBasis.repr_apply_apply]
  rw [← e.inner_map_map (e₀ i) ((bL j).val)]
  simp only [e, OrthonormalBasis.equiv_apply_basis, Equiv.refl_apply]

end BostConjecture.Arithmetic.Compactness
