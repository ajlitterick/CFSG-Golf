module

public import CFSG.Quasithin.Vol2.Ch12Sec8NonabHatAct
public import CFSG.Quasithin.Vol2.Ch12Sec8NonabEleven

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {T M L : Subgroup G}

namespace HatModel


end HatModel

namespace Hyp1281Two

section

variable (h : Hyp1281Two G T M L) (hU : ¬ IsMulCommutative ↥(uOfL22 T M)) {g : G}
  (hg : GoodElt128 T L g) (D : HatModel T M)

include h hU hg

theorem hat_isotropic : ∀ v ∈ D.hat (wOfU T M ⊓ rconj (wOfU T M) g),
    ∀ w ∈ D.hat (wOfU T M ⊓ rconj (wOfU T M) g), D.B v w = 0 := by
  intro v hv w hw
  obtain ⟨e, heE, heU, rfl⟩ := D.mem_hat.mp hv
  obtain ⟨e', he'E, he'U, rfl⟩ := D.mem_hat.mp hw
  rw [D.B_spec e heU e' he'U]
  have hE : IsElemAbelian 2 (wOfU T M ⊓ rconj (wOfU T M) g) :=
    (h.lemma_12_8_11_two hU hg).1
  have hcomm : e * e' = e' * e := congrArg Subtype.val (hE.1.is_comm.comm ⟨e, heE⟩ ⟨e', he'E⟩)
  calc e * e' * e⁻¹ * e'⁻¹ = (e' * e) * e⁻¹ * e'⁻¹ := by rw [hcomm]
    _ = 1 := by group


end

end Hyp1281Two

end CFSG.Quasithin
