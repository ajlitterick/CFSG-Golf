module

public import CFSG.ClassicalInvolution.AschTight.Sec7L76C
public import CFSG.ClassicalInvolution.Asc77.AscL62Final
public import CFSG.ClassicalInvolution.AschTight.Sec7L612B

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

section Family

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}


end Family

variable (p f : ℕ) [Fact p.Prime]

theorem l6_12_mod : L6_12ModTmp p f :=
  l6_12ModTmp_of p f
    (fun G _ _ Ω hΩ S => (l6_9_proved p f hΩ.1 hΩ.2.1 G Ω hΩ.2.2.1 S).1)
    (fun G _ _ Ω hΩ η ⟨S, hS, hinv⟩ =>
      ((l6_9_proved p f hΩ.1 hΩ.2.1 G Ω hΩ.2.2.1 S).2 η hS hinv).1)
    (fun G _ _ Ω hΩ => l6_11_proved p f hΩ.1 hΩ.2.1 G Ω hΩ.2.2.1)


end CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7
