module

public import CFSG.ClassicalInvolution.Asc77.AscT7HS4
public import CFSG.ClassicalInvolution.Asc77.AscT7HC5
public import CFSG.ClassicalInvolution.Asc77.AscT7HS3

public section

namespace CFSG.ClassicalInvolution.Asc77

variable {p f : ℕ} [Fact p.Prime]

theorem twinSquareFact_proved : TwinSquareFact p := by
  intro t k e hadm hp2 hq htag R hR R' hR' hne hcomm x hx x' hx' hx2 hx1 hx'2 hx'1 _ hc
  obtain ⟨c, hcZ, hcc⟩ := hc
  rcases htag with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact (T7H.psp2_twin_no_sq hp2 hq hadm R hR R' hR' hne hcomm x hx x' hx' hx2 hx1 hx'2
      hx'1 c hcZ hcc).elim
  · exact Or.inl ⟨rfl, rfl, T7H.psl4_twin_sq hp2 hq R hR R' hR' hne hcomm x hx x' hx' hx2 hx1
      hx'2 hx'1 c hcZ hcc⟩
  · exact Or.inr ⟨rfl, rfl, T7H.psu4_twin_sq hp2 hadm R hR R' hR' hne hcomm x hx x' hx' hx2 hx1
      hx'2 hx'1 c hcZ hcc⟩
  · exact (T7H.spinOdd_twin_no_sq hp2 hq hadm R hR R' hR' hne hcomm x hx x' hx' hx2 hx1 hx'2
      hx'1 c hcZ hcc).elim
  · exact (T7H.spinPlus_twin_no_sq hp2 hq hadm R hR R' hR' hne hcomm x hx x' hx' hx2 hx1 hx'2
      hx'1 c hcZ hcc).elim
  · exact (T7H.spinMinus_twin_no_sq hp2 hq hadm R hR R' hR' hne hcomm x hx x' hx' hx2 hx1 hx'2
      hx'1 c hcZ hcc).elim

namespace T7H

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77.ExactLayer AscE184Sect

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}


end T7H

theorem c23_4X_proved : C23_4X p f :=
  c23_4X_of_tsf twinSquareFact_proved

end CFSG.ClassicalInvolution.Asc77
