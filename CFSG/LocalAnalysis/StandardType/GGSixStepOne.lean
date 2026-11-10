module

public import CFSG.LocalAnalysis.StandardType.GGSixStepOneNine

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

section Sylow

variable {G : Type} [Group G]

theorem exists_sylow_of_bstarUnique {p : ℕ} (hp : p.Prime) {M Bs : Subgroup G}
    (hBs : IsElemAbelian p Bs) (hBsM : Bs ≤ M)
    (hU : ∀ P : Subgroup G, P ≤ M → IsPGroup p P → Bs ≤ P →
      (∀ Q : Subgroup G, Q ≤ M → IsPGroup p Q → P ≤ Q → Q = P) →
      ∀ E : Subgroup G, E ≤ P → IsElemAbelian p E →
        Nat.card E ≤ Nat.card Bs ∧ (Nat.card E = Nat.card Bs → E = Bs)) :
    ∃ P : Sylow p M, Bs ≤ (P : Subgroup M).map M.subtype ∧
      ∀ E : Subgroup G, E ≤ (P : Subgroup M).map M.subtype → IsElemAbelian p E →
        Nat.card E = Nat.card Bs → E = Bs := by
  have : Fact p.Prime := ⟨hp⟩
  have hBsp : IsPGroup p Bs := fun b => ⟨1, Subtype.ext (by simpa using hBs.2 b b.2)⟩
  obtain ⟨Q, hQ⟩ := (hBsp.comap_of_injective M.subtype M.subtype_injective).exists_le_sylow
  have hPM : (Q : Subgroup ↥M).map M.subtype ≤ M := Subgroup.map_subtype_le _
  have hPp : IsPGroup p ((Q : Subgroup ↥M).map M.subtype) := Q.isPGroup'.map M.subtype
  have hBsP : Bs ≤ (Q : Subgroup ↥M).map M.subtype := fun b hb => ⟨⟨b, hBsM hb⟩, hQ hb, rfl⟩
  have hmaxM : ∀ R : Subgroup G, R ≤ M → IsPGroup p R →
      (Q : Subgroup ↥M).map M.subtype ≤ R → R = (Q : Subgroup ↥M).map M.subtype := by
    intro R hRM hRp hPR
    have hRp' : IsPGroup p (R.subgroupOf M) :=
      hRp.comap_of_injective M.subtype M.subtype_injective
    have hQR : (Q : Subgroup ↥M) ≤ R.subgroupOf M := fun q hq => hPR ⟨q, hq, rfl⟩
    have hRQ := Q.is_maximal' hRp' hQR
    rw [← Subgroup.map_subgroupOf_eq_of_le hRM, hRQ]
  exact ⟨Q, hBsP, fun E hE hEel hcard => (hU _ hPM hPp hBsP hmaxM E hE hEel).2 hcard⟩

end Sylow


section Inputs


variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
  {t : StatedLieTag} {n f : ℕ} {ψ : (ggU t n f).K →* G}

theorem GGSixCtxV2.mem_of_conj_mem_d (h611 : GGSixLSixElevenInput) (h612 : GGSixLSixTwelveInput)
    (h613t : GGSixTrialityInput) (h613d : GGSixLinearJInput)
    (hctx : GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ)
    (hC : Subgroup.centralizer (ggG0 p B x L D J : Set G) = ⊥)
    (hU : GGSixBstarUnique p B Bs x L D J)
    (h9iii : ∀ d ∈ D, d ≠ 1 → Subgroup.centralizer {d} ≤ ggM p B x L D J) {d : G} (hd : d ∈ D)
    (hd1 : d ≠ 1) {g : G} (hg : g⁻¹ * d * g ∈ ggM p B x L D J) : g ∈ ggM p B x L D J := by
  by_contra hgM
  have hdBs : d ∈ Bs := hctx.d_le_bstar hd
  rcases h611 G p B Bs x L D J t n f ψ hctx hC hU d hdBs (h9iii d hd hd1) g hg hgM with
    hlin | htri
  · obtain ⟨hcard, hno⟩ :=
      h612 G p B Bs x L D J t n f ψ hctx hC hU d hdBs (h9iii d hd hd1) g hg hgM hlin
    obtain ⟨K, hK, hKA⟩ := h613d G p B Bs x L D J t n f ψ hctx hlin hcard d hd hd1
    exact hno K hK hKA
  · exact hgM (h613t G p B Bs x L D J t n f ψ hctx hC hU h9iii d hdBs (h9iii d hd hd1) g hg htri)


end Inputs

section Assembly


end Assembly

end CFSG.StandardType
