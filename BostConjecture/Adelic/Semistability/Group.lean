/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.Galois.HNScalarExtension
public import Mathlib.RepresentationTheory.Irreducible

/-!
# Irreducible isometric group actions and adelic semistability

The first assertion of Lemma 2.6 of this paper follows from invariance of the
actual largest destabilizing subspace. ArakelovGeometry proves that invariance
using its actual restricted degrees and the uniqueness of the largest
maximal-slope subspace. Irreducibility then makes this nonzero subspace the
whole representation.

The action preserves the norms on every completed fibre, rather than just a
chosen rational lattice. Neither finiteness of the group nor characteristic
zero is needed for this implication. In particular it applies to the product
group acting on the constant Specht factors, once that representation and its
completed isometries have been constructed.
-/

@[expose] public section

noncomputable section

namespace ArakelovGeometry.AdelicVectorBundle

variable {K : Type*} [Field K] {S : AdelicStructure K} [S.IsProper]
  {E : Type*} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  {G : Type*} [Group G]

/-- Lemma 2.6 of this paper: an irreducible group action preserving the actual
completed norms forces arithmetic mean-slope semistability. -/
theorem isMeanSlopeSemistable_of_isIrreducible (V : AdelicVectorBundle S E)
    [hS : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized]
    [hV : V.IsHermitian] (hr : 0 < Module.finrank K E)
    (ρ : Representation K G E) [ρ.IsIrreducible]
    (hρ : ∀ g ω z, V.toNormFamily.norm ω
      ((ρ g).baseChange (S.ϕ ω).Completion z) = V.toNormFamily.norm ω z) :
    V.IsMeanSlopeSemistable := by
  let D := V.destabilizingSubspace hr
  have hD : 0 < Module.finrank K D :=
    V.destabilizingSubspace_finrank_pos hr
  let σ : Subrepresentation ρ :=
    { toSubmodule := D
      apply_mem_toSubmodule := by
        intro g x hx
        let e := LinearEquiv.ofBijective (ρ g) (ρ.apply_bijective g)
        have hm := V.map_destabilizingSubspace_eq_of_completed_isometry V e
              hr hr (hρ g)
        exact hm.le (Submodule.mem_map_of_mem hx) }
  apply (V.destabilizingSubspace_eq_top_iff_isMeanSlopeSemistable hr).mp
  rcases eq_bot_or_eq_top σ with hbot | htop
  · have hz : D = ⊥ := congrArg Subrepresentation.toSubmodule hbot
    have : Module.finrank K D = 0 := Submodule.finrank_eq_zero.mpr hz
    omega
  · exact congrArg Subrepresentation.toSubmodule htop

end ArakelovGeometry.AdelicVectorBundle
