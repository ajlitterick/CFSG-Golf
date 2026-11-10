module

public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.LocalAnalysis.ComponentClassification.SimpleStructure
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerSQTK
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.ReducedCore
public import CFSG.LocalAnalysis.SectionRank.SectionAssembly
public import CFSG.Quasithin.SteinbergBSDihedralPair
public import CFSG.Quasithin.SteinbergBSCubicPair

public section

namespace CFSG.Quasithin.SteinbergBS

open Subgroup CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup CFSG.Quasithin.B6

theorem map_eq_one_of_odd_card {G G' : Type*} [Group G] [Group G'] {N : Subgroup G'}
    (hN : Odd (Nat.card N)) (f : G →* G') {x : G} (hx : f x ∈ N) {n : ℕ} (hxn : x ^ 2 ^ n = 1) :
    f x = 1 := by
  have h1 : orderOf (⟨f x, hx⟩ : N) ∣ 2 ^ n :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext (by simp [← map_pow, hxn]))
  have h2 : orderOf (⟨f x, hx⟩ : N) ∣ Nat.card N := orderOf_dvd_natCard _
  have hcop : Nat.Coprime (2 ^ n) (Nat.card N) :=
    Nat.Coprime.pow_left n (Nat.coprime_two_left.2 hN)
  have h3 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
  exact congrArg Subtype.val (orderOf_eq_one_iff.1 h3)


end CFSG.Quasithin.SteinbergBS
