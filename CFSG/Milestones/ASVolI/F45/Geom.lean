module

public import CFSG.Quasithin.Recognition.F4Apart
public import CFSG.Milestones.ASVolI.F4

public section

namespace CFSG.ASVolI

open CFSG.Quasithin

universe u

section Graph

variable {V : Type u} {Γ : SimpleGraph V}

@[expose] def burnsideF45_cons {n : ℕ} (u : V) (p : GPath Γ n) (h : Γ.Adj u (p 0)) :
    GPath Γ (n + 1) where
  toFun i := if i = 0 then u else p (i - 1)
  adj i hi := by
    rcases i with _ | i
    · simpa using h
    · have := p.adj i (by omega)
      simpa using this
  tail i hi := by
    have h1 : i ≠ 0 := by omega
    have h2 : n + 1 ≠ 0 := by omega
    simp only [h1, h2, if_false]
    rw [p.tail (i - 1) (by omega)]
    simp

@[simp] theorem burnsideF45_cons_zero {n : ℕ} (u : V) (p : GPath Γ n) (h : Γ.Adj u (p 0)) :
    burnsideF45_cons u p h 0 = u := by
  show (if (0 : ℕ) = 0 then u else p (0 - 1)) = u
  simp

@[simp] theorem burnsideF45_cons_succ {n : ℕ} (u : V) (p : GPath Γ n) (h : Γ.Adj u (p 0))
    (i : ℕ) : burnsideF45_cons u p h (i + 1) = p i := by
  show (if i + 1 = 0 then u else p (i + 1 - 1)) = p i
  simp


end Graph

section Completion

open CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion CFSG.ASVolI.ChF


end Completion

end CFSG.ASVolI
