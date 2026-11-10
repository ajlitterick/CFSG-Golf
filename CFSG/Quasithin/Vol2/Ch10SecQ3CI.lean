module

public import CFSG.Quasithin.Vol2.Ch10SecQ3CH
public import CFSG.Quasithin.Vol2.Ch10SecQ3CBc
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.EmptyFaithful.Setting
public import CFSG.Quasithin.Vol2.Ch10SecB3FactsE
public import CFSG.Quasithin.Vol2.Ch11SecBDerived
public import CFSG.Quasithin.Vol2.Ch1Local
public import CFSG.Quasithin.Vol2.Ch1Prop121

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

namespace C11AmS

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.H13

variable {G : Type} [Group G] [Finite G]


omit [Finite G] in
theorem isSylowTwoOf_top_subgroupOf {K S : Subgroup G} (hS : IsSylowTwoOf S K) :
    IsSylowTwoOf (S.subgroupOf K) (⊤ : Subgroup K) := by
  refine ⟨le_top, hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm, ?_⟩
  rw [← Subgroup.relIndex, Subgroup.relIndex_top_right]
  exact hS.2.2

omit [Finite G] in
theorem coe_mem_normalizer {K S : Subgroup G} (hSK : S ≤ K) {d : ↥K}
    (hd : d ∈ Subgroup.normalizer ((S.subgroupOf K : Subgroup K) : Set K)) :
    (d : G) ∈ Subgroup.normalizer (S : Set G) := by
  refine Subgroup.mem_normalizer_iff.mpr fun w => ⟨fun hw => ?_, fun hw => ?_⟩
  · have h := (Subgroup.mem_normalizer_iff.mp hd ⟨w, hSK hw⟩).mp hw
    exact h
  · have hwK : w ∈ K := by
      have h1 : (d : G) * w * (d : G)⁻¹ ∈ K := hSK hw
      have h2 := K.mul_mem (K.mul_mem (K.inv_mem d.2) h1) d.2
      simpa [mul_assoc] using h2
    exact (Subgroup.mem_normalizer_iff.mp hd ⟨w, hwK⟩).mpr hw

end C11AmS

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.H13 C11AmS


end CFSG.Quasithin.Vol2.Ch10.SecB
