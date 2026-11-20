/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Measurability.Density.Basic

/-!
# Countable-field adapters for actual adelic norm families

The countability assumption of this paper supplies ArakelovGeometry's common
countable dense subfield hypothesis by taking the whole base field. The same
subfield works at every place, including trivially valued places.
-/

@[expose] public section

namespace ArakelovGeometry.AdelicStructure

variable {K : Type*} [Field K]

/-- The whole base field is dense in each of its actual completions. -/
private theorem isDenseSubfieldAt_top (S : AdelicStructure K) (ω : S.Ω) :
    S.IsDenseSubfieldAt ⊤ ω := by
  refine Dense.mono ?_ (UniformSpace.Completion.denseRange_coe (α := WithAbs (S.ϕ ω)))
  rintro _ ⟨x, rfl⟩
  exact ⟨⟨x.ofAbs, by simp⟩, rfl⟩

/-- This paper, Sections 2.1–2.3. See [Chen–Moriwaki, Proposition 4.1.24 and Remark 4.1.34][cm].

A countable base field supplies one countable subfield dense at every place,
as required by the adelic restriction, quotient, dual and tensor constructions. -/
instance hasCommonCountableDenseSubfield_of_countable [Countable K]
    (S : AdelicStructure K) : S.HasCommonCountableDenseSubfield :=
  ⟨⟨⊤, inferInstance, S.isDenseSubfieldAt_top⟩⟩

end ArakelovGeometry.AdelicStructure
