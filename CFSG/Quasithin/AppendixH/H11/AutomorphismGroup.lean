module

public import CFSG.Quasithin.Background.HModelType
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAut
public import CFSG.Quasithin.H13.A5M12CentBase
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.AppendixH.H11

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.ModelType
  CFSG.Quasithin.H13.A5.M12 CFSG.Quasithin.Vol2.Ch10.SecA.C10P01

section Aut

variable {V : Type*} [CommGroup V] {L M : Subgroup (MulAut V)}


@[expose] noncomputable def conjHom (hLM : IsOver L M) : ↥M →* MulAut ↥L :=
  L.normalizerMonoidHom.comp (Subgroup.inclusion hLM.2)

theorem coe_conjHom_apply (hLM : IsOver L M) (m : ↥M) (l : ↥L) :
    ((conjHom hLM m l : ↥L) : MulAut V) = (m : MulAut V) * (l : MulAut V) * (m : MulAut V)⁻¹ := by
  change ((L.normalizerMonoidHom (Subgroup.inclusion hLM.2 m) l : ↥L) : MulAut V) =
    (m : MulAut V) * (l : MulAut V) * (m : MulAut V)⁻¹
  exact Subgroup.normalizerMonoidHom_apply_apply_coe L (Subgroup.inclusion hLM.2 m) l


theorem even_card [Finite (MulAut V)]
    (hLM : IsOver L M) (θ : ↥L ≃* ↥CFSG.Blueprint.NativeSporadic.M12) :
    Even (Nat.card ↥M) := by
  have hcardL : Nat.card ↥L = 95040 := by
    rw [Nat.card_congr θ.toEquiv, CFSG.Sporadic.Mathieu.card_M12]
  have hdvd : Nat.card ↥L ∣ Nat.card ↥M := Subgroup.card_dvd_of_le hLM.1
  exact (show Even (Nat.card ↥L) by rw [hcardL]; norm_num).trans_dvd hdvd


end Aut

end CFSG.Quasithin.AppendixH.H11
