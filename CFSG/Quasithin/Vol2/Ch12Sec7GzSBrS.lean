module

public import CFSG.Quasithin.Vol2.Ch12Sec7GzSBr
public import CFSG.Quasithin.Vol2.Ch12Sec7GzSSig

public section

namespace CFSG.Quasithin.H13.I1277

open CFSG.Open Certificates.Data.S1277Struct Certificates.Data.S1277Cand Certificates.Data.S1277Bfs
  Certificates.Data.S1277Sig Std


section Cards

variable {G : Type} [Group G] {K Q : Subgroup G} {T : KTab} {κ : G → Nat}


end Cards

section PhiList

variable (T : KTab) (N : List Nat)


end PhiList

section FrBuild

variable {G : Type} [Group G] [Finite G] {H K Q : Subgroup G} {T : KTab} {κ : G → Nat}


end FrBuild

section Labels

variable {G : Type} [Group G] [Finite G] {H K Q : Subgroup G} {T : KTab} {κ : G → Nat}


end Labels

section XPart


end XPart

theorem card_le_relIndex_of_inf_eq_bot {Γ : Type*} [Group Γ] [Finite Γ] {X R P : Subgroup Γ}
    (hX : X ≤ P) (_hR : R ≤ P) (h : X ⊓ R = ⊥) : Nat.card X ≤ R.relIndex P := by
  have hinj : Function.Injective (fun x : X =>
      (QuotientGroup.mk (⟨x.1, hX x.2⟩ : ↥P) : ↥P ⧸ R.subgroupOf P)) := by
    intro x y hxy
    have h1 := QuotientGroup.eq.1 hxy
    have h2 : x.1⁻¹ * y.1 ∈ R := Subgroup.mem_subgroupOf.1 h1
    have h3 : x.1⁻¹ * y.1 ∈ X := X.mul_mem (X.inv_mem x.2) y.2
    have h4 : x.1⁻¹ * y.1 ∈ X ⊓ R := ⟨h3, h2⟩
    rw [h, Subgroup.mem_bot] at h4
    exact Subtype.ext (inv_mul_eq_one.1 h4)
  exact Nat.card_le_card_of_injective _ hinj


section BranchSig


end BranchSig

end CFSG.Quasithin.H13.I1277

end
