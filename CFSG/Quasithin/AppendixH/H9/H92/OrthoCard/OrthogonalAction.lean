module

public import CFSG.Quasithin.AppendixH.H9.H92.OrthoCard.OrthonormalBases
public import CFSG.Quasithin.AppendixH.H9.H92.OrthoCard.OrthogonalGroup

public section

open scoped Matrix

namespace CFSG.ASVolI.ChH

open CFSG.Quasithin CFSG.Open


theorem IsOrthonormalBasis5.image {B : GL (Fin 5) (ZMod 2)} (hB : IsOrthGL B)
    {S : Finset (Fin 5 → ZMod 2)} (hS : IsOrthonormalBasis5 S) :
    IsOrthonormalBasis5 (S.image fun x => (B : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ x) := by
  obtain ⟨hcard, hnorm, horth⟩ := hS
  refine ⟨?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _
      (Matrix.mulVec_injective_of_isUnit (Units.isUnit B)), hcard]
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    rw [hB.dotProduct_mulVec_mulVec]
    exact hnorm y hy
  · intro x hx x' hx' hne
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨y', hy', rfl⟩ := Finset.mem_image.mp hx'
    rw [hB.dotProduct_mulVec_mulVec]
    exact horth y hy y' hy' fun h => hne (congrArg _ h)


end CFSG.ASVolI.ChH
