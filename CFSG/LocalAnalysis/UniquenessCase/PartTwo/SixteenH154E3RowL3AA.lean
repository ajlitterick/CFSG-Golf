module

public import CFSG.Quasithin.Background.B4L3Coord
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3RowL3AAA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5SumSecA
import CFSG.Fischer.Classification.Recognition.PSU6
import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W]


theorem s16h_twoNat_covering [Finite W] {L : Subgroup (MulAut W)} {U Z : Subgroup W}
    (hS : SumOfNat (fun H U Z => CFSG.Quasithin.BinaryNaturalSL H U Z 3 1) L U Z 2)
    (hLU : L ≤ stabSub U) (hLZ : L ≤ stabSub Z) (hLcard : Nat.card ↥L = 168)
    (E : Subgroup (MulAut W)) (hEN : E ≤ normalizer (L : Set (MulAut W)))
    (hEU : E ≤ stabSub U) (hEZ : E ≤ stabSub Z) (hEab : IsElemAbelian 3 E)
    (hEcard : 9 * Nat.card ↥(E ⊓ centSub U) ≤ Nat.card ↥E)
    (hErank : Nat.card ↥(autSub E U) ≤ 9) (hZcard : Nat.card ↥Z ≤ 2) :
    ∀ v : Sec U Z, v ≠ 1 → ∃ g : ↥L, ∃ b : ↥E, (b : MulAut W) ∉ centSub U ∧
      ∃ (hmem : (g : MulAut W) * (b : MulAut W) * (g : MulAut W)⁻¹ ∈
          stabSub U ⊓ stabSub Z),
        CFSG.Quasithin.B5.secHom (stabSub U ⊓ stabSub Z) inf_le_left inf_le_right
          ⟨(g : MulAut W) * (b : MulAut W) * (g : MulAut W)⁻¹, hmem⟩ v = v := by
  intro v hvne
  classical
  obtain ⟨d, hdne, l, hdfix⟩ :=
    s16h_twoNat_orbit_fix hS hLU hLZ hLcard E hEN hEU hEZ hEab hEcard hErank hZcard v hvne
  set X₀ : Subgroup (MulAut W) := stabSub U ⊓ stabSub Z with hX₀
  have hX₀U : X₀ ≤ stabSub U := inf_le_left
  have hX₀Z : X₀ ≤ stabSub Z := inf_le_right
  have hEX₀ : E ≤ X₀ := le_inf hEU hEZ
  have hLX₀ : L ≤ X₀ := le_inf hLU hLZ
  have hEsecEq : (E.subgroupOf X₀).map (CFSG.Quasithin.B5.secHom X₀ hX₀U hX₀Z) =
      autSec E U Z :=
    CFSG.Quasithin.B5.map_secHom_eq_autSec X₀ hX₀U hX₀Z hEX₀
  have hLsecEq : (L.subgroupOf X₀).map (CFSG.Quasithin.B5.secHom X₀ hX₀U hX₀Z) =
      autSec L U Z :=
    CFSG.Quasithin.B5.map_secHom_eq_autSec X₀ hX₀U hX₀Z hLX₀
  have hdmem : (d : MulAut (Sec U Z)) ∈
      (E.subgroupOf X₀).map (CFSG.Quasithin.B5.secHom X₀ hX₀U hX₀Z) := by
    rw [hEsecEq]
    exact d.2
  obtain ⟨b0, hb0E, hb0sec⟩ := Subgroup.mem_map.mp hdmem
  have hlmem : (CFSG.Quasithin.B5.secHom L hLU hLZ l : MulAut (Sec U Z)) ∈
      (L.subgroupOf X₀).map (CFSG.Quasithin.B5.secHom X₀ hX₀U hX₀Z) := by
    rw [hLsecEq, ← CFSG.Quasithin.B5.range_secHom L hLU hLZ]
    exact ⟨l, rfl⟩
  obtain ⟨l0, hl0L, hl0sec⟩ := Subgroup.mem_map.mp hlmem
  have h1 : (CFSG.Quasithin.B5.secHom X₀ hX₀U hX₀Z) l0 v =
      CFSG.Quasithin.B5.secHom L hLU hLZ l v := by
    rw [hl0sec]
  have hinv : (CFSG.Quasithin.B5.secHom X₀ hX₀U hX₀Z l0)⁻¹
      (CFSG.Quasithin.B5.secHom L hLU hLZ l v) = v := by
    rw [hl0sec]
    have hcancel : (CFSG.Quasithin.B5.secHom L hLU hLZ l)⁻¹ *
        CFSG.Quasithin.B5.secHom L hLU hLZ l = 1 := inv_mul_cancel _
    calc (CFSG.Quasithin.B5.secHom L hLU hLZ l)⁻¹
          (CFSG.Quasithin.B5.secHom L hLU hLZ l v)
        = ((CFSG.Quasithin.B5.secHom L hLU hLZ l)⁻¹ *
            CFSG.Quasithin.B5.secHom L hLU hLZ l) v := rfl
      _ = (1 : MulAut (Sec U Z)) v := by rw [hcancel]
      _ = v := rfl
  have h3 : (CFSG.Quasithin.B5.secHom X₀ hX₀U hX₀Z) (l0⁻¹ * b0 * l0) v = v := by
    rw [map_mul, map_mul, map_inv]
    change (CFSG.Quasithin.B5.secHom X₀ hX₀U hX₀Z l0)⁻¹
      ((CFSG.Quasithin.B5.secHom X₀ hX₀U hX₀Z b0)
        ((CFSG.Quasithin.B5.secHom X₀ hX₀U hX₀Z l0) v)) = v
    rw [h1, hb0sec, hdfix]
    exact hinv
  have hb0E' : ((b0 : X₀) : MulAut W) ∈ E := Subgroup.mem_subgroupOf.mp hb0E
  have hl0L' : ((l0 : X₀) : MulAut W) ∈ L := Subgroup.mem_subgroupOf.mp hl0L
  have hbcent : ((b0 : X₀) : MulAut W) ∉ centSub U := by
    intro hbc
    have hcentsec : ((b0 : X₀) : MulAut W) ∈ centSec U Z :=
      centSub_le_centSec U Z hbc
    have hker : b0 ∈ (CFSG.Quasithin.B5.secHom X₀ hX₀U hX₀Z).ker :=
      (CFSG.Quasithin.B5.mem_ker_secHom X₀ hX₀U hX₀Z b0).2 hcentsec
    have hb0one : CFSG.Quasithin.B5.secHom X₀ hX₀U hX₀Z b0 = 1 :=
      MonoidHom.mem_ker.mp hker
    have hd1 : (d : MulAut (Sec U Z)) = 1 := by
      rw [← hb0sec]
      exact hb0one
    exact hdne hd1
  refine ⟨⟨((l0 : X₀) : MulAut W)⁻¹, L.inv_mem hl0L'⟩,
    ⟨((b0 : X₀) : MulAut W), hb0E'⟩, hbcent, ?_, ?_⟩
  · simp only [hX₀]
    exact (l0⁻¹ * b0 * l0).2
  · change (CFSG.Quasithin.B5.secHom X₀ hX₀U hX₀Z) (l0⁻¹ * b0 * l0) v = v
    exact h3

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
