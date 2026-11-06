module

public import BostConjecture.Slope.FiniteLength
public import HarderNarasimhan.Filtration.Unique

/-!
# Equivariance of a finite-length HN flag

An order automorphism preserving the actual payoff fixes the unique HN flag.
-/

@[expose] public section

namespace BostConjecture.Slope

open HarderNarasimhan

variable {L S : Type*} [Lattice L] [BoundedOrder L] [Nontrivial L]
variable [WellFoundedGT L] [WellFoundedLT L] [CompleteLinearOrder S]

/-- Payoff-preserving lattice automorphisms preserve every term of the HN filtration. -/
theorem hnFiltration_eq_of_orderIso (μ : PayoffFunction L S)
    [μ.IsSlopeLike] [μ.IsConvex] (e : L ≃o L)
    (he : ∀ I : StrictIntvl L, μ ⟨e I.left, e I.right, e.strictMono I.lt⟩ = μ I)
    (n : ℕ) : e (μ.hnFiltration n) = μ.hnFiltration n := by
  let F := μ.hnFiltration
  have hlt (i : ℕ) (hi : i < F.length) : F i < F (i + 1) :=
    F.strictMonoOn hi.le hi (Nat.lt_succ_self i)
  have hs (i : ℕ) (hi : i < F.length) :
      (μ.restrict ⟨e (F i), e (F (i + 1)), e.strictMono (hlt i hi)⟩).IsSemistable := by
    apply (isSemistable_restrict_iff μ _).mpr
    intro x hix hxi
    have hi' : F i < e.symm x := by simpa using e.symm.strictMono hix
    have hx' : e.symm x ≤ F (i + 1) := by simpa using e.symm.monotone hxi
    have hb := (isSemistable_restrict_iff μ _).mp (F.piecewise_isSemistable i hi)
      (e.symm x) hi' hx'
    have he' := he ⟨F i, e.symm x, hi'⟩
    simp only [OrderIso.apply_symm_apply] at he'
    exact he'.trans_le (hb.trans_eq (he ⟨F i, F (i + 1), hlt i hi⟩).symm)
  let G : μ.HarderNarasimhanFiltration :=
    { toFun := fun i => e (F i)
      length := F.length
      monotone := e.monotone.comp F.monotone
      head_eq_bot := by change e (F.toFun 0) = ⊥; rw [F.head_eq_bot, e.map_bot]
      length_eq_top := by change e (F.toFun F.length) = ⊤; rw [F.length_eq_top, e.map_top]
      strictMonoOn := fun _ hi _ hj hij => e.strictMono (F.strictMonoOn hi hj hij)
      piecewise_isSemistable := hs
      not_A_le_succ := by
        intro i hi
        rw [A_eq_of_isSemistable μ _ (hs i (Nat.lt_of_succ_lt hi)),
          A_eq_of_isSemistable μ _ (hs (i + 1) hi),
          he ⟨F i, F (i + 1), hlt i (Nat.lt_of_succ_lt hi)⟩,
          he ⟨F (i + 1), F (i + 2), hlt (i + 1) hi⟩,
          ← A_eq_of_isSemistable μ ⟨F i, F (i + 1), hlt i (Nat.lt_of_succ_lt hi)⟩
            (F.piecewise_isSemistable i (Nat.lt_of_succ_lt hi)),
          ← A_eq_of_isSemistable μ ⟨F (i + 1), F (i + 2), hlt (i + 1) hi⟩
            (F.piecewise_isSemistable (i + 1) hi)]
        exact F.not_A_le_succ i hi }
  have hGF : G = F := Subsingleton.elim _ _
  exact congrArg (fun f : μ.HarderNarasimhanFiltration => f n) hGF

end BostConjecture.Slope
