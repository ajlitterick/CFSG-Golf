module

public import CFSG.Dihedral.DihedralFusionAutomorphisms
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.X.ConjugationFamily
import all CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.X.ConjugationFamily

public noncomputable section

namespace CFSG.GorensteinWalter

open BenderSuzuki.External

universe u v

theorem hom_to_pGroup_image_on_sylow
    {N : Type u} {A : Type v} [Group N] [Finite N] [Group A]
    {p : ℕ} [Fact p.Prime] (hA : IsPGroup p A)
    (f : N →* A) (Q : Sylow p N) (n : N) :
    ∃ q : N, q ∈ (Q : Subgroup N) ∧ f q = f n := by
  let T : Sylow p f.range := Q.mapSurjective f.rangeRestrict_surjective
  have htop : (T : Subgroup f.range) = ⊤ := by
    exact (T.is_maximal' ((hA.to_subgroup f.range).to_subgroup ⊤) le_top).symm
  have hn : (⟨f n, ⟨n, rfl⟩⟩ : f.range) ∈ (T : Subgroup f.range) := by
    rw [htop]
    trivial
  change (⟨f n, ⟨n, rfl⟩⟩ : f.range) ∈
    (Q : Subgroup N).map f.rangeRestrict at hn
  obtain ⟨q, hq, heq⟩ := Subgroup.mem_map.mp hn
  exact ⟨q, hq, congrArg Subtype.val heq⟩


end CFSG.GorensteinWalter
