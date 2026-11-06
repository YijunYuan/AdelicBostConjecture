module

public import BostConjecture.Arithmetic.TensorSubmodule
public import BostConjecture.Arithmetic.DualCoordinate
public import Mathlib.RingTheory.Finiteness.Projective

/-!
# Integral submodules under a projective line twist

Contraction by the integral dual and a finite projective splitting recover
every actual submodule of a tensor product with a rank-one projective module.
No integral generator of the line is chosen.
-/

@[expose] public section

noncomputable section

open NumberField TensorProduct

namespace BostConjecture.Arithmetic

universe u
variable {K : Type*} [Field K] [NumberField K]
variable {M L : Type u} [AddCommGroup M] [Module (𝓞 K) M]
    [AddCommGroup L] [Module (𝓞 K) L]

/-- Contract the line factor by an actual integral functional. -/
def lineContract (f : L →ₗ[𝓞 K] 𝓞 K) : (M ⊗[𝓞 K] L) →ₗ[𝓞 K] M :=
  (TensorProduct.rid (𝓞 K) M).toLinearMap.comp (f.lTensor M)

omit [NumberField K] in
@[simp]
lemma lineContract_tmul (f : L →ₗ[𝓞 K] 𝓞 K) (m : M) (l : L) :
    lineContract f (m ⊗ₜ[𝓞 K] l) = f l • m := by
  simp [lineContract]

/-- The actual integral submodule obtained by removing the line factor. -/
def lineUntwist (C : Submodule (𝓞 K) (M ⊗[𝓞 K] L)) : Submodule (𝓞 K) M where
  carrier := {m | ∀ l : L, m ⊗ₜ[𝓞 K] l ∈ C}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy l
    simpa only [add_tmul] using C.add_mem (hx l) (hy l)
  smul_mem' := by
    intro a x hx l
    simpa only [smul_tmul'] using C.smul_mem a (hx l)

variable [Module.Finite (𝓞 K) L] [Module.Projective (𝓞 K) L]

/-- Rank one makes evaluation symmetric even for a nonprincipal line. -/
lemma line_eval_smul (hL : Module.finrank K (K ⊗[𝓞 K] L) = 1)
    (f : L →ₗ[𝓞 K] 𝓞 K) (x y : L) : f x • y = f y • x := by
  by_cases hy : y = 0
  · simp [hy]
  let q := lineCoordinate (M := L) hL
  have hq := lineCoordinate_injective (M := L) hL
  apply hq
  simp only [map_smul, Algebra.smul_def]
  change (f x : K) * q y = (f y : K) * q x
  rw [← dualCoordinate_mul q hq hy f x, ← dualCoordinate_mul q hq hy f y]
  ring

/-- Contraction followed by retensoring is scalar multiplication on the whole tensor. -/
lemma lineContract_tmul_eq_smul (hL : Module.finrank K (K ⊗[𝓞 K] L) = 1)
    (f : L →ₗ[𝓞 K] 𝓞 K) (t : M ⊗[𝓞 K] L) (l : L) :
    lineContract f t ⊗ₜ[𝓞 K] l = f l • t := by
  induction t using TensorProduct.inductionOn with
  | tmul m x =>
    rw [lineContract_tmul, smul_tmul, ← tmul_smul, line_eval_smul hL f x l,
      tmul_smul]
  | add x y hx hy => simp only [map_add, add_tmul, smul_add, hx, hy]

lemma lineContract_mem_untwist (hL : Module.finrank K (K ⊗[𝓞 K] L) = 1)
    (C : Submodule (𝓞 K) (M ⊗[𝓞 K] L)) (f : L →ₗ[𝓞 K] 𝓞 K)
    {t : M ⊗[𝓞 K] L} (ht : t ∈ C) : lineContract f t ∈ lineUntwist C := by
  intro l
  rw [lineContract_tmul_eq_smul hL]
  exact C.smul_mem _ ht

/-- Removing and restoring the line factor recovers every actual integral submodule. -/
theorem tensorRight_lineUntwist (hL : Module.finrank K (K ⊗[𝓞 K] L) = 1)
    (C : Submodule (𝓞 K) (M ⊗[𝓞 K] L)) :
    tensorRight L (lineUntwist C) = C := by
  classical
  apply le_antisymm
  · rintro _ ⟨t, rfl⟩
    induction t using TensorProduct.inductionOn with
    | tmul m l => exact m.property l
    | add x y hx hy => simpa only [map_add] using C.add_mem hx hy
  · obtain ⟨n, p, i, _, _, hpi⟩ :=
      Module.Finite.exists_comp_eq_id_of_projective (𝓞 K) L
    let e (j : Fin n) : L := p (Pi.single j 1)
    let f (j : Fin n) : L →ₗ[𝓞 K] 𝓞 K := (LinearMap.proj j).comp i
    have he (l : L) : ∑ j, f j l • e j = l := by
      calc
        ∑ j, f j l • e j = p (∑ j, i l j • Pi.single j 1) := by
          simp [f, e, map_sum]
        _ = p (i l) := by congr 1; funext j; simp [Pi.single_apply]
        _ = l := LinearMap.congr_fun hpi l
    have ht (t : M ⊗[𝓞 K] L) :
        ∑ j, lineContract (f j) t ⊗ₜ[𝓞 K] e j = t := by
      induction t using TensorProduct.inductionOn with
      | tmul m l =>
        simp only [lineContract_tmul, smul_tmul, ← tmul_sum, he]
      | add x y hx hy => simp only [map_add, add_tmul, Finset.sum_add_distrib, hx, hy]
    intro t htc
    rw [← ht t]
    apply Submodule.sum_mem
    intro j _
    exact ⟨(⟨lineContract (f j) t, lineContract_mem_untwist hL C (f j) htc⟩ :
      lineUntwist C) ⊗ₜ[𝓞 K] e j, rfl⟩

end BostConjecture.Arithmetic
