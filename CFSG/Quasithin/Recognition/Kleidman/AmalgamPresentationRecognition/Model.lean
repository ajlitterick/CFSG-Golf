module

public import Certificates.Certificate272032
import all CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition.ModelTuple

public section

namespace CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition

open CFSG.Sporadic.Th

noncomputable def letG (z : ℤ) : J3Model :=
  if 0 < z then uN (z - 1).toNat else (uN (-z - 1).toNat)⁻¹

theorem lift_letter (i : Fin 7) (s : Bool) :
    FreeGroup.lift uJ (FreeGroup.mk [(i, s)]) =
      letG (if s then (i.val : ℤ) + 1 else -((i.val : ℤ) + 1)) := by
  cases s
  · simp [letG, uJ]
  · simp [letG, uJ]


theorem uJ_satisfies : SatisfiesJ3Words uJ := Certificates.certificate272032.1

theorem closure_uJ : Subgroup.closure (Set.range uJ) = ⊤ := Certificates.certificate272032.2

end CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition
