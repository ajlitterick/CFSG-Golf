module

public import CFSG.Quasithin.EmptyFaithful.S1515
public import CFSG.Quasithin.EmptyFaithful.S1511
public import CFSG.Quasithin.EmptyFaithful.S1414Defs
public import CFSG.Quasithin.EmptyFaithful.S141Statements

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

theorem thompsonJ_le_centralizer_VZ (h17 : StageLemma1417) {T Mc M : Subgroup G}
    (h : quasithinQTFE14Cat G T Mc) (hM : IsMf T Mc M) (hCE : IsCE1513 T M) :
    thompsonJ T ≤ Subgroup.centralizer (VZ T M : Set G) := by
  by_contra hnot
  have hnot' : ¬ thompsonJ T ≤ M ⊓ Subgroup.centralizer (VZ T M : Set G) := fun hle =>
    hnot (hle.trans inf_le_right)
  rcases h17 G T Mc h M (VZ T M) hM.1.1 (isTwoReducedIn_VZ h hM.1.1).1 hnot'
    (Or.inl hM.2.1) with h1 | h2
  · exact hCE.1 h1.1
  · exact hCE.2 h2.1

omit [Finite G] in
theorem normalizer_le_cgs {S : Subgroup G} (hS : S ≠ ⊥) :
    Subgroup.normalizer (S : Set G) ≤ CGS S := by
  have hchar : (S.subgroupOf S).Characteristic := by
    rw [Subgroup.subgroupOf_self]
    infer_instance
  unfold CGS
  exact le_iSup_of_le S (le_iSup_of_le le_rfl (le_iSup_of_le hS (le_iSup_of_le hchar le_rfl)))

omit [Finite G] in
theorem omegaOneCenterOf_le_self (X : Subgroup G) : omegaOneCenterOf X ≤ X := by
  refine (Subgroup.closure_le X).mpr fun x hx => ?_
  exact hx.1.1

theorem baum_ne_bot {T Mc : Subgroup G} (h : quasithinQTFE14Cat G T Mc) : baum T ≠ ⊥ := by
  have hZ : quasithinOmegaOneCenter T ≤ baum T := by
    intro z hz
    have hz' := quasithinOmegaOneCenter_le_center T hz
    refine ⟨hz'.1, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    have hyT : y ∈ T := (thompsonJ_le_self151 T) (omegaOneCenterOf_le_self _ hy)
    exact (Subgroup.mem_centralizer_iff.mp hz'.2 y hyT)
  intro hb
  exact h.omegaOneCenter_ne_bot (le_bot_iff.mp (hZ.trans hb.le))


end CFSG.Quasithin
