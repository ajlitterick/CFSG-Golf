module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPrimeFunctor

public section

open CFSG.Open

namespace CFSG.RankThreeEvenClassification.Helpers

universe u v


theorem subgroup_map_commutative {G : Type u} {H : Type v} [Group G] [Group H]
    (subgroup : Subgroup G) (homomorphism : G →* H) (hcomm : IsMulCommutative subgroup) :
    IsMulCommutative (subgroup.map homomorphism) := by
  apply isMulCommutative_iff.mpr
  intro first second
  obtain ⟨firstPreimage, hfirstPreimage, hfirstEq⟩ := Subgroup.mem_map.mp first.property
  obtain ⟨secondPreimage, hsecondPreimage, hsecondEq⟩ := Subgroup.mem_map.mp second.property
  apply Subtype.ext
  change (first : H) * second = (second : H) * first
  rw [← hfirstEq, ← hsecondEq, ← map_mul, ← map_mul]
  apply congrArg homomorphism
  exact congrArg (fun element : subgroup => (element : G))
    (isMulCommutative_iff.mp hcomm ⟨firstPreimage, hfirstPreimage⟩ ⟨secondPreimage, hsecondPreimage⟩)


end CFSG.RankThreeEvenClassification.Helpers
