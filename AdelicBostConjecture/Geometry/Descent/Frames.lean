/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-!
# Principal frames for finite projective modules

A finite projective module of constant stalk rank admits a finite principal
cover with bases of that rank. The frames live on the canonical scalar
extensions of the original module.
-/

@[expose] public section

noncomputable section

namespace AdelicBostConjecture.Geometry

open Module
open scoped TensorProduct

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [Module.Finite R M] [Module.Projective R M] {a : ℕ}

/-- A prescribed stalk rank gives a principal neighborhood with a frame of that rank. -/
theorem exists_principal_frame (p : PrimeSpectrum R) (ha : Module.rankAtStalk M p = a) :
    ∃ f : R, f ∉ p.asIdeal ∧
      Nonempty (Basis (Fin a) (Localization.Away f) (Localization.Away f ⊗[R] M)) := by
  let : Module.FinitePresentation R M := Module.finitePresentation_of_projective R M
  let : Module.Free (Localization.AtPrime p.asIdeal)
      (LocalizedModule p.asIdeal.primeCompl M) := Module.free_of_flat_of_isLocalRing
  let b := Module.finBasisOfFinrankEq (Localization.AtPrime p.asIdeal)
    (LocalizedModule p.asIdeal.primeCompl M) ha
  obtain ⟨f, hf, c, _⟩ := Module.FinitePresentation.exists_basis_localizedModule_powers
    p.asIdeal.primeCompl (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M)
    (Localization.AtPrime p.asIdeal) b
  exact ⟨f, hf, ⟨c.map (LocalizedModule.equivTensorProduct (Submonoid.powers f) M)⟩⟩

/-- Actual finite local frames, without a chosen global free model. -/
theorem exists_finite_principal_frames (ha : ∀ p : PrimeSpectrum R, Module.rankAtStalk M p = a) :
    ∃ s : Finset R, Ideal.span (s : Set R) = ⊤ ∧
      ∀ f ∈ s, Nonempty
        (Basis (Fin a) (Localization.Away f) (Localization.Away f ⊗[R] M)) := by
  classical
  let T : Set R := {f | Nonempty
    (Basis (Fin a) (Localization.Away f) (Localization.Away f ⊗[R] M))}
  have hT : Ideal.span T = ⊤ := by
    by_contra h
    obtain ⟨p, hp, hTp⟩ := Ideal.exists_le_maximal (Ideal.span T) h
    obtain ⟨f, hfp, hf⟩ := exists_principal_frame (M := M) ⟨p, hp.isPrime⟩ (ha _)
    exact hfp (hTp (Ideal.subset_span hf))
  obtain ⟨s, hsT, hs⟩ := (Ideal.span_eq_top_iff_finite T).mp hT
  exact ⟨s, hs, fun f hf => hsT hf⟩

end AdelicBostConjecture.Geometry
