module

public import CFSG.ClassicalInvolution.Q3.TL3Induct

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

structure Q8TwinDatum {G : Type*} [Group G] (R : Subgroup G) (S : Sylow 2 R) (t : G) : Prop where
  quat : ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup R) ≃* QuaternionGroup (2 ^ (r - 2)))
  mem : t ∈ (S : Subgroup R).map R.subtype
  order : orderOf t = 2
  cent : R ≤ Subgroup.centralizer ({t} : Set G)
  twoGroup : IsPGroup 2 (R ⧸ classicalInvolutionOddCore R)

theorem TightDatum.toQ8TwinDatum {G : Type*} [Group G] {R : Subgroup G} {S : Sylow 2 R} {t : G}
    (h : TightDatum R S t) : Q8TwinDatum R S t :=
  ⟨h.quat, h.mem, h.order, h.cent, h.twoGroup⟩

theorem Q8TwinDatum.toTightDatum {G : Type*} [Group G] {R : Subgroup G} {S : Sylow 2 R} {t : G}
    (h : Q8TwinDatum R S t)
    (hn : (R.subgroupOf (Subgroup.centralizer ({t} : Set G))).Normal) : TightDatum R S t :=
  ⟨h.quat, h.mem, h.order, h.cent, hn, h.twoGroup⟩

theorem Q8TwinDatum.sylow_core {G : Type} [Group G] [Finite G] {R : Subgroup G} {S : Sylow 2 R}
    {t : G} (_h : Q8TwinDatum R S t) :
    IsSylow2In ((S : Subgroup R).map R.subtype) (tightCore R) := by
  have hS : IsSylow2In ((S : Subgroup R).map R.subtype) R := Asc77.isSylow2In_map_subtype R S
  refine ⟨?_, hS.2.1, fun V hVK hV2 hle => hS.2.2 V (hVK.trans (tightCore_le R)) hV2 hle⟩
  intro s hs
  exact Subgroup.subset_closure ⟨hS.1 hs, hS.2.1.to_le (Subgroup.zpowers_le.mpr hs)⟩

theorem Q8TwinDatum.exists_sylow_q8 {G : Type} [Group G] [Finite G] {R : Subgroup G}
    {S : Sylow 2 R} {t : G} (h : Q8TwinDatum R S t)
    (hq8 : Nonempty (↥(S : Subgroup R) ≃* QuaternionGroup 2)) :
    ∃ P : Subgroup G, IsSylow2In P (tightCore R) ∧ Nonempty (↥P ≃* QuaternionGroup 2) :=
  ⟨_, h.sylow_core, ⟨(Subgroup.equivMapOfInjective (S : Subgroup R) R.subtype
    R.subtype_injective).symm.trans hq8.some⟩⟩


section Targets


end Targets

end CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
