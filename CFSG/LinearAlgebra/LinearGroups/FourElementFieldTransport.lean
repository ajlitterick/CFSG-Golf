module

public import CFSG.Fischer.F4
import all CFSG.Fischer.F4

public section

namespace CFSG.LinearGroups

open CFSG.Fischer


@[expose] noncomputable def frobeniusF4 : F4 ≃+* F4 :=
  RingEquiv.ofBijective (frobenius F4 2)
    ⟨(frobenius F4 2).injective, Finite.surjective_of_injective (frobenius F4 2).injective⟩

theorem frobeniusF4_apply (x : F4) : frobeniusF4 x = x ^ 2 :=
  frobenius_def 2 x


end CFSG.LinearGroups
