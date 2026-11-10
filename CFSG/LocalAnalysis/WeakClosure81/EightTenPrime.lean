module

public import CFSG.Goldschmidt.Steps.G3aBorel
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerPClosure
public import CFSG.LocalAnalysis.WeakClosure81.EightNine

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
  (IsL2 IsSz IsL3 IsU3 IsSp4 IsU4 IsU5 IsOmega8m Is3D4 IsAlt IsSL3 Bar2 OInf Opp)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (HasCompFactor)
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
  (relPPrimeCore_le relPPrimeCore_normal)

variable {G : Type} [Group G] [Finite G]

private theorem mem_normalizer_iff_map_conj {X : Type} [Group X] {H : Subgroup X} {g : X} :
    g ∈ Subgroup.normalizer (H : Set X) ↔ H.map (MulAut.conj g).toMonoidHom = H := by
  rw [Subgroup.mem_normalizer_iff]
  constructor
  · intro hg
    apply le_antisymm
    · rintro z ⟨y, hy, hyz⟩
      rw [← hyz]
      simpa [MulAut.conj_apply] using (hg y).mp hy
    · intro z hz
      refine ⟨(MulAut.conj g)⁻¹ z, (hg _).mpr ?_, by simp [mul_assoc]⟩
      simpa [MulAut.conj_apply, mul_assoc] using hz
  · intro hmap z
    constructor
    · intro hz
      have hzmap : (MulAut.conj g).toMonoidHom z ∈ H.map (MulAut.conj g).toMonoidHom :=
        ⟨z, hz, rfl⟩
      simpa [MulAut.conj_apply] using (hmap ▸ hzmap)
    · intro hz
      have hzmap : (MulAut.conj g).toMonoidHom z ∈ H.map (MulAut.conj g).toMonoidHom := by
        rw [hmap]; simpa [MulAut.conj_apply] using hz
      obtain ⟨y, hy, hyz⟩ := hzmap
      have hyz' : y = z := (MulAut.conj g).injective (by simpa using hyz)
      exact hyz' ▸ hy


end CFSG.LocalAnalysis.WeakClosure81

end
