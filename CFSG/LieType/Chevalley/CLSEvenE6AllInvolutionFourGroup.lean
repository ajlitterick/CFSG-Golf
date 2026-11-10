module

public import CFSG.LieType.Chevalley.CLSEvenE6GraphInvolutionFourGroup
public import CFSG.LieType.Chevalley.OddExceptionalOuterTwoRank
public import CFSG.LocalAnalysis.ComponentInitial.InvolutionFixedFourGroupTransport

public noncomputable section

namespace CFSG.LieType.Chevalley.EvenE6AllInvolution

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.FixedFourGroup
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.Assembly.LowTwoRank (StatedLieTag)


theorem mem_inner_of_conj_mul_rootDiagAut
    {τ : Tag} {K : Type} [Field K] [Finite K] {f : ℕ}
    (hK : Nat.card K = 2 ^ f) (hf : 1 ≤ f) {β : MulAut (adjointGroup τ K)}
    (g : adjointGroup τ K) (a : Fin τ.rank → Kˣ) (hβ : β = MulAut.conj g * rootDiagAut τ K a)
    (hβ2 : β ^ 2 = 1) : β ∈ inner (adjointGroup τ K) := by
  set q := 2 ^ f with hq
  have hq1 : Odd (q - 1) := by
    have h1 : 1 ≤ q := Nat.one_le_two_pow
    have h2 : Even q := (Nat.even_pow' (by omega)).2 even_two
    exact Nat.Even.sub_odd h1 h2 odd_one
  have ha : a ^ (q - 1) = 1 := funext fun j => by
    rw [Pi.pow_apply, Pi.one_apply, ← hK, ← Nat.card_units]
    exact pow_card_eq_one'
  have hδ : rootDiagAut τ K a ^ (q - 1) = 1 := by
    change rootDiagAutHom τ K a ^ (q - 1) = 1
    rw [← map_pow, ha, map_one]
  set x : Outer (adjointGroup τ K) := (β : Outer (adjointGroup τ K)) with hx
  have hg : ((MulAut.conj g : MulAut (adjointGroup τ K)) : Outer (adjointGroup τ K)) = 1 :=
    (QuotientGroup.eq_one_iff _).2 ⟨g, rfl⟩
  have hxq : x ^ (q - 1) = 1 := by
    rw [hx, hβ, QuotientGroup.mk_mul, hg, one_mul, ← QuotientGroup.mk_pow, hδ,
      QuotientGroup.mk_one]
  have hx2 : x ^ 2 = 1 := by rw [hx, ← QuotientGroup.mk_pow, hβ2, QuotientGroup.mk_one]
  have hord : orderOf x ∣ Nat.gcd 2 (q - 1) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hx2) (orderOf_dvd_of_pow_eq_one hxq)
  have hgcd : Nat.gcd 2 (q - 1) = 1 :=
    (Nat.coprime_two_left.2 hq1)
  rw [hgcd, Nat.dvd_one, orderOf_eq_one_iff] at hord
  exact (QuotientGroup.eq_one_iff β).1 hord


end CFSG.LieType.Chevalley.EvenE6AllInvolution
