module

public import CFSG.RankThree.PartOne.TCX.E.ExchangeFamily
public import CFSG.RankThree.PartOne.TCX.E.AnFamily
public import CFSG.RankThree.PartOne.KE.FiniteFieldAlgClosure
public import CFSG.RankThree.PartOne.KE.E8TwoA2Family
public import CFSG.RankThree.PartOne.TCX.E.ExchangeBlock

public noncomputable section

namespace CFSG.RankThree.PartOne.TCX.E

open Matrix CFSG.RankThree.PartOne.KE CFSG.RankThree.Classical2 CFSG.Assembly.LowTwoRank
open CFSG.RankThree.PartOne.KLCE
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped MatrixGroups Pointwise

section Fields


end Fields

section Block

variable {τ : Tag} {S : Set (Fin τ.rank → ℤ)} {m : ℕ}


end Block

section Twist

variable {τ : Tag} {L : Type} [Field L]

theorem twist_pinnedX_w (Fr : L →+* L) (n : ModGL τ L) (hn : n ∈ monomialSubgroup τ L)
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    ∃ μ : Lˣ, ∀ c : L, n * Units.map (entrywiseHom Fr) (pinnedX τ L α c) * n⁻¹ =
      pinnedX τ L (weylQuotientHom τ L ⟨n, hn⟩ • α) ((μ : L) * Fr c) := by
  obtain ⟨μ, hμ⟩ := monomial_conj_pinnedX hn hα
  refine ⟨μ, fun c => ?_⟩
  rw [units_map_entrywiseHom_pinnedX, hμ]

theorem twist_rootSpan_le_w (Fr : L →+* L) (n : ModGL τ L) (hn : n ∈ monomialSubgroup τ L)
    {S S' : Set (Fin τ.rank → ℤ)} (hS : ∀ r ∈ S, IsRoot τ r)
    (hmap : ∀ α ∈ S, weylQuotientHom τ L ⟨n, hn⟩ • α ∈ S') :
    ∀ x ∈ rootSpan τ L S, n * Units.map (entrywiseHom Fr) x * n⁻¹ ∈ rootSpan τ L S' := by
  set Tm : ModGL τ L →* ModGL τ L :=
    (MulAut.conj n).toMonoidHom.comp (Units.map (entrywiseHom Fr)) with hTm
  have hle : rootSpan τ L S ≤ (rootSpan τ L S').comap Tm :=
    iSup₂_le fun α hα x hx => by
      obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hx
      obtain ⟨μ, hμ⟩ := twist_pinnedX_w Fr n hn (hS α hα)
      have h1 : Tm (pinnedX τ L α c) =
          pinnedX τ L (weylQuotientHom τ L ⟨n, hn⟩ • α) ((μ : L) * Fr c) := by
        rw [← hμ c]
        simp [hTm, MulAut.conj_apply]
      rw [Subgroup.mem_comap, h1]
      exact Subgroup.mem_iSup_of_mem _ (Subgroup.mem_iSup_of_mem (hmap α hα)
        (mem_rootSubgroup.2 ⟨_, rfl⟩))
  intro x hx
  have := hle hx
  rw [Subgroup.mem_comap] at this
  simpa [hTm, MulAut.conj_apply] using this


end Twist

section Exchange


end Exchange

end CFSG.RankThree.PartOne.TCX.E
