module

public import CFSG.Walter.Bender1970.S4.TypeL2Even

public section

namespace CFSG.Walter

open CFSG.GorensteinWalter

variable {G : Type} [Group G] [Finite G]

theorem BenderCounterexample.noJRComponents
    (hG : BenderCounterexample G) : NoJRComponents G := by
  intro s hs M hM J hJ hJR
  obtain ⟨T, hsT⟩ := exists_sylow_two_mem hs
  exact not_isTypeL2Even_of_isTypeJR hJR
    (Bender44.isTypeL2Even hG hs hM T hsT hJ (Or.inl hJR) hJ)


section Statements


end Statements

end CFSG.Walter
