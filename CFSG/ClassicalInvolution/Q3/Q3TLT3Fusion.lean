module

public import CFSG.ClassicalInvolution.Q3.Q3TLT3Act
public import CFSG.ClassicalInvolution.Q3.Q3TLTDatum

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG CFSG.Open CFSG.ClassicalInvolution QuaternionGroup
open scoped commutatorElement

section Group

theorem orderOf_conj_eq {G : Type*} [Group G] (c g : G) : orderOf (c * g * c⁻¹) = orderOf g := by
  have := (MulAut.conj c).orderOf_eq g
  rwa [MulAut.conj_apply] at this


end Group

section Lift

variable {G : Type*} [Group G] [Finite G] {R S : Subgroup G} {t : G}


end Lift

section Datum

variable {G : Type*} [Group G] [Finite G] {R : Subgroup G} {S : Sylow 2 R} {t : G}

namespace TightDatum

@[expose] noncomputable def act (d : TightDatum R S t) :
    Subgroup.centralizer ({t} : Set G) →* MulAut (R ⧸ oddCore R) :=
  (tl3Act R).comp (Subgroup.inclusion d.le_normalizer)


theorem act_eq_one_iff (d : TightDatum R S t) {c : G}
    (hc : c ∈ Subgroup.centralizer ({t} : Set G)) :
    d.act ⟨c, hc⟩ = 1 ↔ ∀ r ∈ R, ⁅c, r⁆ ∈ oddCoreImg R :=
  tl3Act_eq_one_iff R ⟨c, d.le_normalizer hc⟩

omit [Finite G] in
theorem conj_mem (d : TightDatum R S t) {c : G} (hc : c ∈ Subgroup.centralizer ({t} : Set G))
    {g : G} (hg : g ∈ R) : c * g * c⁻¹ ∈ R :=
  (Subgroup.mem_normalizer_iff.mp (d.le_normalizer hc) g).mp hg

end TightDatum

end Datum

section Main


end Main

end CFSG.ClassicalInvolution.Q3
