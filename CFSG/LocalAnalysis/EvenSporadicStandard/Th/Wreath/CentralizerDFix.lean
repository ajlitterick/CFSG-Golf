module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.SylowEndSchur
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.W5

public section

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup SylowEnd


variable {G : Type} [Group G] [Finite G] {L R : Subgroup G} {t : G} {S A B Aa D : Subgroup G}
  {z b : G}

theorem ThCyc.t_sq (H : ThCyc G L R t) : t * t = 1 := by simpa [sq] using H.sq_t

theorem ThCyc.t_inv (H : ThCyc G L R t) : t⁻¹ = t := inv_eq_of_mul_eq_one_right H.t_sq

theorem ThCyc.t_conj_efix (H : ThCyc G L R t) {c : G} :
    t * (c⁻¹ * (t * c * t⁻¹)) * t⁻¹ = (c⁻¹ * (t * c * t⁻¹))⁻¹ := by
  have ht : t * t = 1 := H.t_sq
  have htinv : t⁻¹ = t := H.t_inv
  have h2 : t * (t * c * t⁻¹) * t⁻¹ = c := by
    calc t * (t * c * t⁻¹) * t⁻¹ = (t * t) * c * (t⁻¹ * t⁻¹) := by group
      _ = c := by rw [htinv]; simp only [ht, one_mul, mul_one]
  calc t * (c⁻¹ * (t * c * t⁻¹)) * t⁻¹
      = (t * c⁻¹ * t⁻¹) * (t * (t * c * t⁻¹) * t⁻¹) := by group
    _ = (t * c⁻¹ * t⁻¹) * c := by rw [h2]
    _ = (t * c * t⁻¹)⁻¹ * c := by group
    _ = (c⁻¹ * (t * c * t⁻¹))⁻¹ := by group

end CFSG.EvenSporadicStandard.ThStd
