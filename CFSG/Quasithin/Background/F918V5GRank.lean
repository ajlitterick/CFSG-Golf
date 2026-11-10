module

public import CFSG.Assembly.Defs
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.lemma_4_5_a
import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.Quasithin

namespace F918V5G

variable {G : Type*} [Group G]

theorem le_pRank_of_card [Finite G] {p : ℕ} (hp : 1 < p) {H E : Subgroup G} (hEH : E ≤ H)
    (hE : CFSG.Assembly.IsElemAbelian p E) {k : ℕ} (hk : Nat.card E = p ^ k) :
    k ≤ CFSG.Assembly.pRank p H := CFSG.SectionRank.le_pRank hp hEH hE hk

theorem two_le_pRank_of_not_cyclic [Finite G] {H Q : Subgroup G} (hQH : Q ≤ H)
    (hQ : IsPGroup 3 Q) (hnc : ¬ IsCyclic ↥Q) : 2 ≤ CFSG.Assembly.pRank 3 H := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (IsPGroup 3 ↥Q) := ⟨hQ⟩
  obtain ⟨S, -, hS9, hSel⟩ := CFSG.lemma_4_5_a (p := 3) (by norm_num) hnc
  have := hSel
  have hEel : CFSG.IsElementaryAbelian 3 ↥(S.map Q.subtype) := CFSG.IsElementaryAbelian.map_subtype
  refine le_pRank_of_card (by norm_num) (E := S.map Q.subtype)
    ((Subgroup.map_subtype_le S).trans hQH) ⟨hEel.toIsMulCommutative, fun x hx => ?_⟩ ?_
  · exact CFSG.elemPow_eq_one_of_isElementaryAbelian x hx
  · rw [Subgroup.card_map_of_injective Q.subtype_injective, hS9]

@[expose] def HasNoncentral3 (K : Subgroup G) : Prop :=
  ∃ P : Subgroup G, P ≤ K ∧ IsPGroup 3 P ∧ ¬ P ≤ Subgroup.centralizer (K : Set G)


theorem HasNoncentral3.map_conj {K : Subgroup G} (h : HasNoncentral3 K) (m : G) :
    HasNoncentral3 (K.map (MulAut.conj m).toMonoidHom) := by
  obtain ⟨P, hPK, hP3, hPc⟩ := h
  refine ⟨P.map (MulAut.conj m).toMonoidHom, Subgroup.map_mono hPK, hP3.map _, fun hle => hPc ?_⟩
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have h1 : m * k * m⁻¹ * (m * x * m⁻¹) = m * x * m⁻¹ * (m * k * m⁻¹) :=
    Subgroup.mem_centralizer_iff.mp (hle ⟨x, hx, rfl⟩) (m * k * m⁻¹) ⟨k, hk, rfl⟩
  have h2 : m * (k * x) * m⁻¹ = m * (x * k) * m⁻¹ := by
    have e1 : m * (k * x) * m⁻¹ = m * k * m⁻¹ * (m * x * m⁻¹) := by group
    have e2 : m * (x * k) * m⁻¹ = m * x * m⁻¹ * (m * k * m⁻¹) := by group
    rw [e1, e2]
    exact h1
  exact mul_left_cancel (mul_right_cancel h2)


end F918V5G

end CFSG.Quasithin
