module

public import CFSG.ClassicalInvolution.Q3.Q3T7M00
public import CFSG.ClassicalInvolution.Q3.Q3T7FUK0

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T7M

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Asc77
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}


theorem _root_.CFSG.ClassicalInvolution.Q3.Q3T7M.HM.toU {G : Type} [Group G] {Ω : Set (Subgroup G)} (hΩ : CFSG.ClassicalInvolution.Q3.Q3T7M.HM Ω) :
    CFSG.ClassicalInvolution.T7FU.HM (.sl2 3 1) Ω :=
  { toMod := hΩ, toGen := CFSG.ClassicalInvolution.Q3.Q3T7M.HM.toGen hΩ }

namespace CentQ

theorem natCard_conjSub_eq (n : G) (H : Subgroup G) :
    Nat.card ↥(conjSub n H) = Nat.card ↥H :=
  Nat.card_congr (Subgroup.equivMapOfInjective H (MulAut.conj n).toMonoidHom
    (MulAut.conj n).injective).symm.toEquiv

theorem le_centralizer_of_uniq {M : Subgroup G} {z : G} (hM : IsUniqueInvolution M z) :
    M ≤ Subgroup.centralizer ({z} : Set G) := fun _ hw =>
  Subgroup.mem_centralizer_singleton_iff.mpr (hM.commute_of_mem hw).symm

theorem centralizer_eq_of_central {z t : G} (hc : t⁻¹ * z ∈ Subgroup.center G) :
    Subgroup.centralizer ({t} : Set G) = Subgroup.centralizer ({z} : Set G) :=
  CFSG.ClassicalInvolution.T7FU.CentQ.centralizer_eq_of_central hc


theorem isSylow2In_sup_of_odd {N Q A : Subgroup G}
    (hQN : Q ≤ Subgroup.normalizer (N : Set G)) (hN : Odd (Nat.card N)) (hQN0 : Q ⊓ N = ⊥)
    (hA2 : IsPGroup 2 A) (hAle : A ≤ Q ⊔ N) (hcard : Nat.card Q ≤ Nat.card A) :
    IsSylow2In A (Q ⊔ N) :=
  CFSG.ClassicalInvolution.T7FU.CentQ.isSylow2In_sup_of_odd hQN hN hQN0 hA2 hAle hcard

theorem exists_conjSub_of_le_sup_odd {N Q Q' : Subgroup G}
    (hQN : Q ≤ Subgroup.normalizer (N : Set G)) (hN : Odd (Nat.card N)) (hQN0 : Q ⊓ N = ⊥)
    (hQ2 : IsPGroup 2 Q) (hQ'2 : IsPGroup 2 Q') (hcard : Nat.card Q' = Nat.card Q)
    (hle : Q' ≤ N ⊔ Q) : ∃ n ∈ N, conjSub n Q = Q' :=
  CFSG.ClassicalInvolution.T7FU.CentQ.exists_conjSub_of_le_sup_odd hQN hN hQN0 hQ2 hQ'2 hcard hle


end CentQ

end CFSG.ClassicalInvolution.Q3.Q3T7M
