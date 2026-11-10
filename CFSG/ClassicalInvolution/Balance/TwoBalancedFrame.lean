module

public import CFSG.ClassicalInvolution.Balance.LocalBalance
public import CFSG.ClassicalInvolution.Balance.OmegaFreeComponents
public import CFSG.ClassicalInvolution.Balance.Quotient
public import CFSG.ClassicalInvolution.Balance.FrameIndex

public section

namespace CFSG.ClassicalInvolution.Balance

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution.Generic

variable {G : Type*} [Group G]

theorem pPrimeCore_oddQuot_eq_bot [Finite G] (a : G) : CFSG.pPrimeCore 2 (OddQuot a) = ⊥ := by
  rw [← CFSG.Assembly.Dichotomy.oddCore_eq_pPrimeCore]
  exact OddCore.quotient_corefree _

@[expose] def ComponentBalanceAt (Ω : Set (Subgroup G)) (a : G) : Prop :=
  ∀ L : Subgroup (OddQuot a), CFSG.IsComponent L →
    OmegaFreeAt Ω a L ∨ RankOneAt Ω a L ∨ IsLocallyTwoBalanced (L ⧸ Subgroup.center L)

theorem card_modOdd_of_exponent_two [Finite G] {a : G} {F₀ : Subgroup G}
    (hFC : F₀ ≤ Subgroup.centralizer ({a} : Set G)) (hF2 : ∀ f ∈ F₀, f * f = 1) :
    Nat.card (modOdd a F₀) = Nat.card F₀ := by
  set P : Subgroup ↥(Subgroup.centralizer ({a} : Set G)) :=
    F₀.subgroupOf (Subgroup.centralizer ({a} : Set G)) with hP
  have hinj : Function.Injective ((oddQuotMk a).comp P.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hx1 : oddQuotMk a (x : ↥(Subgroup.centralizer ({a} : Set G))) = 1 := hx
    have hxx : (x : ↥(Subgroup.centralizer ({a} : Set G))) * x = 1 :=
      Subtype.ext (hF2 _ (Subgroup.mem_subgroupOf.mp x.2))
    exact Subtype.ext (eq_one_of_oddQuotMk_eq_one hxx hx1)
  have hrange : modOdd a F₀ = ((oddQuotMk a).comp P.subtype).range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  rw [hrange, Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFC).toEquiv

section Frame


end Frame

section Triviality


end Triviality

end CFSG.ClassicalInvolution.Balance
