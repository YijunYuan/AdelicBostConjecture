import ArakelovGeometry.AdelicVectorBundle.Measurability.Density.Basic

/-!
# Countable-field adapters for actual adelic norm families

The countability assumption of this paper supplies ArakelovGeometry's common
countable dense subfield hypothesis by taking the whole base field. The same
subfield works at every place, including trivially valued places.
-/

namespace ArakelovGeometry.AdelicStructure

variable {K : Type*} [Field K]

/-- The whole rational field is dense in each of its actual completions. -/
theorem isDenseSubfieldAt_top (S : AdelicStructure K) (ω : S.Ω) :
    S.IsDenseSubfieldAt ⊤ ω := by
  refine Dense.mono ?_ (UniformSpace.Completion.denseRange_coe (α := WithAbs (S.ϕ ω)))
  rintro _ ⟨x, rfl⟩
  exact ⟨⟨x.ofAbs, by simp⟩, rfl⟩

/-- A countable base field supplies one countable subfield dense at every place,
as required by the adelic restriction, quotient, dual and tensor constructions. -/
theorem hasCommonCountableDenseSubfield_of_countable [Countable K]
    (S : AdelicStructure K) : S.HasCommonCountableDenseSubfield :=
  ⟨⊤, inferInstance, S.isDenseSubfieldAt_top⟩

end ArakelovGeometry.AdelicStructure
