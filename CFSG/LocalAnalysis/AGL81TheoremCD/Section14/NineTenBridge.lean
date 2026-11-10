module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.InnerOnK
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTen
import CFSG.Models.PGLOrders

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.Assembly.RankThreeEven (projSL)
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem HypCGen.toNineSettingGen {M : Subgroup G} {q : ℕ} {E H : Subgroup G}
    (h : HypCGen G M q E H) : NineSettingGen G M q E H E 2 where
  setting :=
    { cstar := h.cstar
      maxLocal := h.maxLocal
      sigma_nonempty := h.sigma_nonempty }
  mem_Q := h.mem_QSet
  mem_H := h.mem_HFam
  stdE := ⟨Or.inl rfl, le_rfl, h.elem, h.card, h.gamma⟩


theorem exists_le_pPrimeCore_card_map_quotient_eq_index (p : ℕ) {K H : Subgroup G}
    (hKH : K ≤ H) :
    ∃ N : Subgroup ↥K, N ≤ CFSG.pPrimeCore p ↥K ∧
      Nat.card ((K.subgroupOf H).map
        (QuotientGroup.mk' (CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore
          (G := ↥H) p))) = N.index := by
  classical
  let O : Subgroup ↥H :=
    CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore (G := ↥H) p
  let incl : ↥K →* ↥H := Subgroup.inclusion hKH
  let f : ↥K →* ↥H ⧸ O := (QuotientGroup.mk' O).comp incl
  have hker : f.ker = O.comap incl := by
    ext x
    simp [f, QuotientGroup.eq_one_iff]
  have hker_card : Nat.card f.ker ∣ Nat.card O := by
    rw [hker]
    exact Subgroup.card_comap_dvd_of_injective O incl (Subgroup.inclusion_injective hKH)
  have hker_cop : Nat.Coprime p (Nat.card f.ker) :=
    (CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore_coprime (G := ↥H) p).of_dvd_right
      hker_card
  have hle : f.ker ≤ CFSG.pPrimeCore p ↥K := by
    dsimp [CFSG.pPrimeCore]
    exact le_sSup ⟨MonoidHom.normal_ker f, hker_cop⟩
  have hrange : f.range = (K.subgroupOf H).map (QuotientGroup.mk' O) := by
    dsimp [f]
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
  refine ⟨f.ker, hle, ?_⟩
  rw [← hrange, Subgroup.index_eq_card]
  exact (Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv).symm

theorem card_pPrimeCore_quotient_dvd_card_map_quotient (p : ℕ) {K H : Subgroup G}
    (hKH : K ≤ H) :
    Nat.card (↥K ⧸ CFSG.pPrimeCore p ↥K) ∣
      Nat.card ((K.subgroupOf H).map
        (QuotientGroup.mk' (CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore
          (G := ↥H) p))) := by
  obtain ⟨N, hNle, hNindex⟩ := exists_le_pPrimeCore_card_map_quotient_eq_index p hKH
  rw [hNindex, ← Subgroup.index_eq_card]
  exact Subgroup.index_dvd_of_le hNle


end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
