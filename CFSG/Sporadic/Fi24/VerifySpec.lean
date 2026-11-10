module

public import CFSG.Sporadic.Fi24.LoopSpec
public import Certificates.Data.CFSGNative.Fi24.Certificate

public section

namespace CFSG.Sporadic.Fi24.Native

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native

structure EnumFacts (E : Enum) (n : ℕ) : Prop where
  alpha_size : E.alpha.size = n
  beta_size : E.beta.size = n
  par_size : E.par.size = n
  lab_size : E.lab.size = n
  L3 : 3 ≤ E.starts.size
  st0 : E.st 0 = 0
  st1 : E.st 1 = 1
  stL : E.st (E.starts.size - 1) = n
  lab0 : ap E.lab 0 = 0
  mono : ∀ m, m < E.starts.size - 1 → E.st m < E.st (m + 1)
  alpha_lt : ∀ k < n, ap E.alpha k < n
  beta_lt : ∀ k < n, ap E.beta k < n
  alpha_invo : ∀ k < n, ap E.alpha (ap E.alpha k) = k
  beta_ord3 : ∀ k < n, ap E.beta (ap E.beta (ap E.beta k)) = k
  tree : ∀ m, 1 ≤ m → m < E.starts.size - 1 → ∀ k, E.st m ≤ k → k < E.st (m + 1) →
    E.st (m - 1) ≤ ap E.par k ∧ ap E.par k < E.st m ∧
      ((ap E.lab k = 1 ∧ ap E.alpha (ap E.par k) = k) ∨
        (ap E.lab k = 2 ∧ ap E.beta (ap E.par k) = k))


section Levels

variable {E : Enum} {n : ℕ} (hE : EnumFacts E n)
include hE


end Levels

theorem formAt_zero (gens : Unit → Gens) (E : Enum) (R0 : RRef) : formAt gens E R0 0 = R0 := by
  rw [formAt]; simp

theorem formAt_pos (gens : Unit → Gens) (E : Enum) (R0 : RRef) {k : ℕ} (hk0 : 0 < k)
    (hp : ap E.par k < k) :
    formAt gens E R0 k =
      stepForm ((gens ()).get (ap E.lab k)) (formAt gens E R0 (ap E.par k)).rows := by
  rw [formAt, dite_eq_left ⟨hk0, hp⟩]


@[expose] def tabOf (E : Enum) (g : ℕ) : Table := if g = 1 then E.alpha else E.beta


section Edges


end Edges


section Edges2


end Edges2


end CFSG.Sporadic.Fi24.Native
