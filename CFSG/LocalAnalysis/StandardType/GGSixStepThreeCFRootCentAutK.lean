module

public import CFSG.LocalAnalysis.StandardType.GGSixStepThreeCFRootCent

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

section Generic

variable {X : Type} [Group X] [Finite X]


theorem ggLe_of_isPGroup_map_pPrimeCore {p : ℕ} (hp : p.Prime) {V E : Subgroup X}
    (hfus : GGControlsStrongFusion V E) (hE : IsElemAbelian p E) (hEcard : Nat.card E = p ^ 2)
    (hO : LargeEvenPPrimeCore p X ≤ V) {R : Subgroup X} (hR : R.Normal)
    (hRp : IsPGroup p ↥(R.map (QuotientGroup.mk' (LargeEvenPPrimeCore p X)))) : R ≤ V := by
  have : Fact p.Prime := ⟨hp⟩
  set O := LargeEvenPPrimeCore p X
  set π := QuotientGroup.mk' O
  have hcomapV : (V.map π).comap π = V := by
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr hO]
  have hfus' : GGControlsStrongFusion (V.map π) (E.map π) := by
    rw [ggControlsStrongFusion_iff]
    refine ⟨Subgroup.map_mono hfus.1, ?_⟩
    rintro _ ⟨e, he, rfl⟩ he1 g' hg'
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective O g'
    have he1' : e ≠ 1 := fun h => he1 (by rw [h, map_one])
    have hgV : g⁻¹ * e * g ∈ V := by
      have h1 : π (g⁻¹ * e * g) ∈ V.map π := by
        rw [map_mul, map_mul, map_inv]
        exact hg'
      rw [← Subgroup.mem_comap, hcomapV] at h1
      exact h1
    exact Subgroup.mem_map_of_mem π (hfus.mem_of_conj_mem he he1' hgV)
  have hcop : Nat.Coprime p (Nat.card O) := CFSG.pPrimeCore_coprime_card
  have hinj : Function.Injective (π.comp E.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro s hs
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hs
    have hsO : (s : X) ∈ O := by
      rw [← QuotientGroup.ker_mk' O]
      exact hs
    have h1 : orderOf (s : X) = 1 :=
      Nat.Coprime.eq_one_of_dvd
        (Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one (hE.2 _ s.2)) hcop)
        (Subgroup.orderOf_dvd_natCard O hsO)
    rw [Subgroup.mem_bot]
    exact Subtype.ext (orderOf_eq_one_iff.mp h1)
  have hmap : E.map π = (π.comp E.subtype).range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hEcard' : Nat.card (E.map π) = p ^ 2 := by
    rw [hmap, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, hEcard]
  have hpc := hfus'.pCore_le hp (ggIsElemAbelian_map hE π) hEcard' p
  have hRle : R.map π ≤ CFSG.pCore p (X ⧸ O) :=
    le_sSup ⟨hR.map π (QuotientGroup.mk'_surjective O), hRp⟩
  calc R ≤ (R.map π).comap π := Subgroup.le_comap_map π R
    _ ≤ (V.map π).comap π := Subgroup.comap_mono (hRle.trans hpc)
    _ = V := hcomapV

end Generic

section Inputs


end Inputs

end CFSG.StandardType
