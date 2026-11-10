module

public import CFSG.Quasithin.Background.B4L3Fin

public section

namespace CFSG.Quasithin.C116Three.L3F

open CFSG.Quasithin.L3

@[expose] def e1 : Vec := ![1, 0, 0]

@[expose] def plane12 : Finset Vec := Finset.univ.filter fun x => x 2 = 0

@[expose] def Ppt (γ : Γ) : Prop := act γ e1 = e1

instance : DecidablePred Ppt := fun γ => by unfold Ppt; infer_instance

@[expose] def Pline (γ : Γ) : Prop := ∀ x ∈ plane12, act γ x ∈ plane12

instance : DecidablePred Pline := fun γ => by unfold Pline; infer_instance

@[expose] def Ustd (γ : Γ) : Prop := Ppt γ ∧ Pline γ

instance : DecidablePred Ustd := fun γ => by unfold Ustd; infer_instance

@[expose] def B1 : Finset Γ := BS plane12

@[expose] def B2 : Finset Γ := AS {0, e1}


set_option maxRecDepth 100000 in
theorem card_U : (Finset.univ.filter Ustd).card = 8 := by decide +kernel


end CFSG.Quasithin.C116Three.L3F
