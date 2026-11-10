module

public import CFSG.Quasithin.Background.D2Coprime
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.Quasithin.AppendixH.H11

open CFSG.Quasithin
open scoped symmDiff

variable {V : Type*} [CommGroup V] [Finite V]


theorem isElemAbelian2_of_isQuadratic (hV : ∀ v : V, v ^ 2 = 1) {A : Subgroup (MulAut V)}
    (hA : IsQuadratic A) : IsElemAbelian2 A := by
  refine ⟨?_, ?_⟩
  · intro a ha b hb
    ext v
    have hbva : b v * v⁻¹ ∈ fixV A :=
      hA (Subgroup.subset_closure ⟨b, hb, v, rfl⟩)
    have hava : a v * v⁻¹ ∈ fixV A :=
      hA (Subgroup.subset_closure ⟨a, ha, v, rfl⟩)
    have haw : a (b v * v⁻¹) = b v * v⁻¹ := hbva a ha
    have hbw : b (a v * v⁻¹) = a v * v⁻¹ := hava b hb
    calc (a * b) v = a (b v) := rfl
      _ = a ((b v * v⁻¹) * v) := by rw [show (b v * v⁻¹) * v = b v by group]
      _ = a (b v * v⁻¹) * a v := by rw [map_mul]
      _ = (b v * v⁻¹) * a v := by rw [haw]
      _ = (a v * v⁻¹) * b v := by ac_rfl
      _ = b (a v * v⁻¹) * b v := by rw [hbw]
      _ = b ((a v * v⁻¹) * v) := by rw [← map_mul]
      _ = b (a v) := by rw [show (a v * v⁻¹) * v = a v by group]
      _ = (b * a) v := rfl
  · intro a ha
    rw [pow_two]
    ext v
    have hava : a v * v⁻¹ ∈ fixV A :=
      hA (Subgroup.subset_closure ⟨a, ha, v, rfl⟩)
    have haw : a (a v * v⁻¹) = a v * v⁻¹ := hava a ha
    calc (a * a) v = a (a v) := rfl
      _ = a ((a v * v⁻¹) * v) := by rw [show (a v * v⁻¹) * v = a v by group]
      _ = a (a v * v⁻¹) * a v := by rw [map_mul]
      _ = (a v * v⁻¹) * a v := by rw [haw]
      _ = (a v * v⁻¹) * (a v * v⁻¹) * v := by group
      _ = v := by rw [← pow_two, hV, one_mul]


end CFSG.Quasithin.AppendixH.H11
