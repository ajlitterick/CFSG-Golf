module

public import CFSG.Milestones.ASVolI.C121.P4GrpB

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {Ω : Type} [Group Ω] [Finite Ω]

namespace burnsideC121_p4_Hyp

variable {X L T R V Y : Subgroup Ω} (h : burnsideC121_p4_Hyp X L T R V Y)
include h

@[expose] noncomputable def eps :
    ↥((baum T ⊔ pCoreOf 2 X) ⊔ Y) →* ↥(autI h.hV (Y ⊔ thompsonJ R)) :=
  (convHom h.hV _ h.H_le_NV).codRestrict (autI h.hV (Y ⊔ thompsonJ R)) (fun x => by
    rw [← h.autI_H, ← range_convHom h.hV _ h.H_le_NV]
    exact ⟨x, rfl⟩)


@[expose] noncomputable def phi2 : ↥((baum T ⊔ pCoreOf 2 X) ⊔ Y) →*
    ↥(autI h.hV (Y ⊔ thompsonJ R)) ⧸ CFSG.pCore 2 ↥(autI h.hV (Y ⊔ thompsonJ R)) :=
  (QuotientGroup.mk' _).comp h.eps


@[expose] noncomputable def K2 : Subgroup Ω := h.phi2.ker.map (Subgroup.subtype _)


include hWm


end burnsideC121_p4_Hyp

end CFSG.Quasithin
