module

public import CFSG.RankThree.PartOne.KC.UnitaryPrimaryCentralizer

public section

namespace CFSG.RankThree.PartOne

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary

theorem eq_one_of_sq_eq_one_of_finrank_lt_two {E W : Type*} [Field E] [AddCommGroup W] [Module E W]
    [FiniteDimensional E W] (h2 : (2 : E) = 0) (hW : Module.finrank E W < 2)
    (u : LinearMap.GeneralLinearGroup E W) (hu : u ^ 2 = 1) : u = 1 := by
  rcases Nat.lt_or_ge (Module.finrank E W) 1 with h0 | h1
  · have : Subsingleton W := (Module.finrank_zero_iff (R := E)).mp (by omega)
    exact Units.ext (LinearMap.ext fun w => Subsingleton.elim _ _)
  · have hfr : Module.finrank E W = 1 := by omega
    obtain ⟨v, hv0, hv⟩ := finrank_eq_one_iff'.mp hfr
    obtain ⟨c, hc⟩ := hv ((u : Module.End E W) v)
    have huu : (u : Module.End E W) ((u : Module.End E W) v) = v := by
      have h1 : ((u * u : LinearMap.GeneralLinearGroup E W) : Module.End E W) v = v := by
        rw [← pow_two, hu]
        rfl
      exact h1
    have hcc : c * c = 1 := by
      have h3 : (u : Module.End E W) ((u : Module.End E W) v) = (c * c) • v := by
        calc (u : Module.End E W) ((u : Module.End E W) v)
            = (u : Module.End E W) (c • v) := by rw [hc]
          _ = c • (u : Module.End E W) v := map_smul _ _ _
          _ = c • c • v := by rw [hc]
          _ = (c * c) • v := smul_smul _ _ _
      have h4 : (c * c - 1) • v = 0 := by rw [sub_smul, one_smul, ← h3, huu, sub_self]
      exact sub_eq_zero.mp ((smul_eq_zero.mp h4).resolve_right hv0)
    have hc1 : c = 1 := by
      have h8 : (c - 1) ^ 2 = 0 := by
        have : (c - 1) ^ 2 = c * c - 1 - 2 * (c - 1) := by ring
        rw [this, hcc, h2]
        ring
      exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h8)
    refine Units.ext (LinearMap.ext fun w => ?_)
    obtain ⟨d, rfl⟩ := hv w
    rw [map_smul]
    change d • (u : Module.End E W) v = d • v
    rw [← hc, hc1, one_smul]


end CFSG.RankThree.PartOne
