module

public import CFSG.Quasithin.EmptyFaithful.S1422Quot
public import CFSG.Quasithin.EmptyFaithful.S1422Center

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7

section Cases

variable {G : Type} [Group G]

@[expose] def CaseTits (H L2 : Subgroup G) : Prop :=
  IsAmalgamOfGroup (RankTwoAmalgam.ofSubgroups H L2) (fun Y _ => Nonempty (Y ≃* quasithinTits)) ∧
    (Nonempty (oTwoQuot ↥H ≃* DihedralGroup 5) ∨ Nonempty (oTwoQuot ↥H ≃* ↥(Sz 0))) ∧
    Nat.card (pCoreOf 2 H) = 2 ^ 9 ∧
    IsL2Quot 1 (oTwoQuot ↥L2) ∧ Nat.card (pCoreOf 2 L2) = 2 ^ 10

@[expose] def Case2F4 (H L2 : Subgroup G) : Prop :=
  IsAmalgamOfGroup (RankTwoAmalgam.ofSubgroups H L2) (IsTwistedF4Over 1) ∧
    Nonempty (oTwoQuot ↥H ≃* Sz 0) ∧ Nat.card (pCoreOf 2 H) = 2 ^ 10 ∧
    IsL2Quot 1 (oTwoQuot ↥L2) ∧ Nat.card (pCoreOf 2 L2) = 2 ^ 11

@[expose] def CaseG2 (H L2 : Subgroup G) : Prop :=
  IsAmalgamOfGroup (RankTwoAmalgam.ofSubgroups H L2) (IsG2Over 1) ∧
    IsL2Quot 1 (oTwoQuot ↥H) ∧ IsL2Quot 1 (oTwoQuot ↥L2) ∧ IsSpecialPow 2 2 2 ↥(pCoreOf 2 H) ∧
    Nat.card (pCoreOf 2 L2) = 2 ^ 5

@[expose] def CaseG22P (H L2 : Subgroup G) : Prop :=
  IsAmalgamOfGroup (RankTwoAmalgam.ofSubgroups H L2) (fun Y _ => Nonempty (Y ≃* PSU3 3 1)) ∧
    IsL2Quot 1 (oTwoQuot ↥H) ∧ IsL2Quot 1 (oTwoQuot ↥L2) ∧ IsZ4StarQ8 ↥(pCoreOf 2 H) ∧
    IsZ4Sq ↥(pCoreOf 2 L2)

@[expose] def CaseM12 (H L2 : Subgroup G) : Prop :=
  IsAmalgamOfGroup (RankTwoAmalgam.ofSubgroups H L2) (fun Y _ => Nonempty (Y ≃* quasithinM12)) ∧
    IsL2Quot 1 (oTwoQuot ↥H) ∧ IsQ8Sq ↥(pCoreOf 2 H) ∧ IsL2Quot 1 (oTwoQuot ↥L2) ∧
    Nat.card (pCoreOf 2 L2) = 2 ^ 5

@[expose] def CaseAutM12 (H L2 : Subgroup G) : Prop :=
  IsAmalgamOfGroup (RankTwoAmalgam.ofSubgroups H L2)
      (fun Y _ => Nonempty (Y ≃* MulAut quasithinM12)) ∧
    IsL2Quot 1 (oTwoQuot ↥H) ∧ IsAutM12Vertex H ∧ IsL2Quot 1 (oTwoQuot ↥L2) ∧
    Nat.card (pCoreOf 2 L2) = 2 ^ 6

end Cases

namespace Setting1422

variable {G : Type} [Group G] [Finite G] {T M Y H : Subgroup G}


theorem H_not_iso_perm_four (S : Setting1422 T M Y H) : IsEmpty (↥H ≃* Equiv.Perm (Fin 4)) := by
  refine ⟨fun e => ?_⟩
  obtain ⟨x, hx, hx1, hxc⟩ := S.exists_central_H
  have h1 : e ⟨x, hx⟩ = 1 := by
    have hc : ∀ σ : Equiv.Perm (Fin 4), (∀ τ, σ * τ = τ * σ) → σ = 1 := by decide
    apply hc
    intro τ
    have := hxc (e.symm τ : G) (e.symm τ).2
    have h2 : (⟨x, hx⟩ : ↥H) * e.symm τ = e.symm τ * ⟨x, hx⟩ := Subtype.ext this
    have h3 := congrArg e h2
    simpa using h3
  have : (⟨x, hx⟩ : ↥H) = 1 := e.injective (by rw [h1, map_one])
  exact hx1 (congrArg Subtype.val this)

theorem YT_not_iso_z2_perm_four (S : Setting1422 T M Y H) :
    IsEmpty (↥(Y ⊔ T) ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)) := by
  refine ⟨fun e => ?_⟩
  refine no_iso_of_trivial_center S.center_YT e (Multiplicative.ofAdd 1, 1) ?_ ?_
  · intro h
    have := congrArg Prod.fst h
    simp at this
  · intro y
    refine Prod.ext ?_ (by simp)
    exact mul_comm _ _

include hSz


end Setting1422

end CFSG.Quasithin
