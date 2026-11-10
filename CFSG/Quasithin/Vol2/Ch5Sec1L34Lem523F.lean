module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.PSubgroupInfNormalNilpotentLePCore
public import CFSG.Quasithin.Vol2.Ch5Sec1L34Thm4

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

section Abstract

variable {W : Type*} [CommGroup W] [Finite W]


end Abstract

section Setting

variable {G : Type} [Group G] [Finite G] {T M L V H B D : Subgroup G} {n : ℕ}

theorem autOn_le_normalizer_autOn_of_normalizes {Γ : Type*} [Group Γ] [Finite Γ]
    {X Y W : Subgroup Γ} (hXY : X ≤ Subgroup.normalizer (Y : Set Γ)) :
    autOn X W ≤ Subgroup.normalizer (autOn Y W : Set (MulAut ↥W)) :=
  CFSG.Quasithin.AutOn.autOn_le_normalizer_autOn hXY


namespace Setup521

variable {D₃ Z₁ : Subgroup G} (s : Setup521 G T M L V H B D D₃ Z₁ n)
include s

theorem almostSpecialHyp_G₁ (h5114 : Stmt5_1_14_first) (hF : L2TorusFact) :
    AlmostSpecialHyp (conjClosure Z₁ D₃) Z₁ ⊥ T (Subgroup.centralizer (Z₁ : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hh := s.hyp.hyp.toHyp5_0_1
  obtain ⟨z, hz, hz1⟩ := s.exists_z
  obtain ⟨d, hd, hd1⟩ := s.exists_d
  have hTG₁ : T ≤ Subgroup.centralizer (Z₁ : Set G) :=
    s.hyp.hyp.hStar.1.1.trans (s.H_le_centralizer h5114)
  have hl1 : lOne (⊥ : Subgroup G) Z₁ = ⊥ := le_bot_iff.mp ((oTwoUpper_le _).trans inf_le_left)
  have hZ1T : Z₁ ≤ T := s.Z₁_le_Z.trans (quasithinOmegaOneCenter_le_self T)
  have hZ1O : Z₁ ≤ pCoreOf 2 (Subgroup.centralizer (Z₁ : Set G)) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hZ1T.trans hTG₁)
      (Subgroup.centralizer_le_normalizer _) (hh.sylow.1.to_le hZ1T)
  have hO₁ : pCoreOf 2 (Subgroup.centralizer (Z₁ : Set G)) ≠ ⊥ := fun hb => by
    have := hZ1O hz
    rw [hb, Subgroup.mem_bot] at this
    exact hz1 this
  obtain ⟨S, hS⟩ := exists_sylow_coe_eq hh.sylow
  have hSG₁ : (S : Subgroup G) ≤ Subgroup.centralizer (Z₁ : Set G) := by rw [hS]; exact hTG₁
  exact
    { elemAbelian := s.isElemAbelian_V₂
      ne_bot := fun hb => hz1 (by rw [hb] at hz; exact Subgroup.mem_bot.mp hz)
      le_V := le_conjClosure Z₁ D₃
      oTwo_eq := (le_bot_iff.mp (oTwoUpper_le ⊥)).symm
      V_le_T := s.V₂_le_T
      T_le_normV₁ := s.T_le_normalizer_Z₁
      T_le_normV := s.T_le_normalizer_V₂ hF
      T_le_normL := fun t _ => Subgroup.mem_normalizer_iff.mpr fun x => by
        simp only [Subgroup.mem_bot]
        constructor
        · rintro rfl
          group
        · intro hx
          have e : x = t⁻¹ * (t * x * t⁻¹) * t := by group
          rw [e, hx]
          group
      sylow_LT := by
        rw [bot_sup_eq]
        exact hh.isSylowTwoOf le_rfl
      H_le := Subgroup.centralizer_le_normalizer _
      lOne_sup_le := by
        rw [hl1, bot_sup_eq]
        exact hTG₁
      sylow_H := hh.isSylowTwoOf hTG₁
      charTwo := charTwo_of_le hh.qtke.2.1 S hSG₁ le_rfl ⟨hSG₁, hO₁⟩
      irred := by
        rw [hl1, bot_sup_eq]
        exact ⟨s.Z₁_lt_V₂ hz hz1 hd hd1 h5114, s.T_le_normalizer_V₂ hF, s.T_le_normalizer_Z₁,
          fun W hW1 hW2 _ => s.eq_or_eq hz hz1 hd hd1 h5114 hF hW1 hW2⟩ }

end Setup521

end Setting

end CFSG.Quasithin.H13
