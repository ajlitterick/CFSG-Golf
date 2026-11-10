module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveIdentDefs
import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowSCore

public section

namespace CFSG.StandardType

open CFSG.Blueprint CFSG.LieType.Steinberg.CentralExt

theorem ggSplitLie_of_rowSA
    {G : Type} [Group G] [Finite G] {p : ℕ} {K : Subgroup G} (hp : p.Prime)
    (h : StandardType.LargeEvenMarking ↥K (fun lab _ _ _ _ _ => ggRowP_SA p lab)) :
    GGSplitLie p K := by
  obtain ⟨⟨tag, l, n⟩, -, _, _, _, _, θ, -, -, hrow, hm⟩ := largeEvenMarking_exists_markedModel h
  have hX := MarkedModel.of_mulEquiv θ.symm hm
  obtain ⟨hlab, hpn⟩ : (tag = .A ∧ 3 ≤ l ∨ tag = .D ∧ l = 3) ∧ p ∣ 2 ^ n - 1 := hrow
  suffices H : ∀ m, 3 ≤ m → LieModel (↥K ⧸ Subgroup.center ↥K) .PSL (m + 1) 2 n →
      GGSplitLie p K by
    rcases hlab with ⟨rfl, hl⟩ | ⟨rfl, rfl⟩
    · exact H l hl hX
    · exact H 3 le_rfl hX
  intro m hm hXm
  haveI : Finite (ggU .PSL (m + 1) n).K := by
    change Finite (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 n))
    infer_instance
  refine ggSplitLie_of_lieModel (t := .PSL) hp (.inl rfl) hpn
    (fun hf E _ _ π hπ hcen => ?_) h.1 hXm
  have hc : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
  have h4 : 4 ≤ 2 ^ n := four_le_two_pow hf
  exact SLClosed.sl_exists_section_of_separating (by omega)
    (SLClosed.separating_of_card (by omega) (by omega) (by omega) (by omega)) hπ hcen

end CFSG.StandardType

end
