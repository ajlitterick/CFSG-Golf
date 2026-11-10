module

public import CFSG.Quasithin.AppendixH.H14.H142Table

public section

namespace CFSG.Quasithin.AppendixH.H14

open CFSG.Quasithin.H.Mathieu


@[expose] def hGens : List (Array ℕ) :=
  [#[0, 1, 3, 12, 21, 19, 4, 10, 8, 22, 6, 18, 9, 17, 20, 7, 15, 14, 13, 2, 23, 16, 5, 11],
    #[0, 2, 6, 10, 22, 19, 1, 15, 8, 4, 12, 14, 3, 13, 18, 21, 5, 17, 11, 16, 20, 7, 9, 23]]


theorem hGens_ok : ∀ a ∈ hGens, inAutOK a = true ∧ a[8]! = 8 ∧ permM a 9857280 = 9857280 := by
  decide +kernel


end CFSG.Quasithin.AppendixH.H14
