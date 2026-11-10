module

public import CFSG.Quasithin.Vol2.Ch12Sec7GzSFr
public import CFSG.Quasithin.Vol2.Ch12Sec7GzSW
public import CFSG.Quasithin.Vol2.Ch12Sec7IdentA
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.Quasithin.H13.I1277

open CFSG.Open Certificates.Data.S1277Struct Certificates.Data.S1277Cand
  Certificates.Data.S1277Sig Certificates.Data.S1277Surv Certificates.Data.S1277Bfs Std Subgroup
open scoped commutatorElement


section Extra

variable {G : Type} [Group G] [Finite G] {H K Q : Subgroup G} {T : KTab} {κ : G → Nat}


end Extra

section Unpack


end Unpack

section Hom

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G}

theorem card_range_eq_of_pkSet {φ : Nat → Nat} {R : Subgroup (Equiv.Perm (Fin (2 ^ 6)))}
    (hR : R ≤ Sig 6 φ) {S : List Nat} (hnd : S.Nodup) (hS : ∀ y, pkSet R y ↔ y ∈ S) :
    Nat.card R = S.length := by
  classical
  let f : ↥R → {y : Nat // y ∈ S} := fun r => ⟨pk r.1, (hS _).1 ⟨r.1, r.2, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      exact Subtype.ext (pk_injective (hR a.2) (hR b.2) (congrArg Subtype.val hab))
    · rintro ⟨y, hy⟩
      obtain ⟨r, hr, rfl⟩ := (hS y).2 hy
      exact ⟨⟨r, hr⟩, rfl⟩
  rw [Nat.card_congr (Equiv.ofBijective f hf)]
  have e2 : {y : Nat // y ∈ S} ≃ ↥S.toFinset := Equiv.subtypeEquivRight fun c => by simp
  rw [Nat.card_congr e2, Nat.card_eq_finsetCard, List.toFinset_card_of_nodup hnd]


end Hom

section AB


end AB

section Branch


end Branch

end CFSG.Quasithin.H13.I1277

end
