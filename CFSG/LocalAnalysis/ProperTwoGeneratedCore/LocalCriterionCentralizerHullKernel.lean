module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndexOddInvolutions
public import CFSG.Permutation.FiveTransitive.CharacteristicAutomorphism

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerHull

open CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex
open CFSG.FiveTransitive.CharacteristicAutomorphism
open CFSG.BenderSuzuki.PFAppendixIII

universe u v

variable {G : Type u} {F : Type v} [Group G] [Group F]

theorem quotient_trivial_automorphism_fixes_involution [Finite G]
    (f : G →* F) (hodd : Odd (Nat.card f.ker))
    (hcentral : f.ker ≤ Subgroup.center G) (a : MulAut G)
    (htrivial : ∀ x : G, f (a x) = f x) {x : G} (hx : IsInvolution x) :
    a x = x := by
  apply square_one_injective_of_central_odd_kernel f hodd hcentral
      (y := x) _ hx.sq_eq_one (htrivial x)
  rw [← map_pow, hx.sq_eq_one, map_one]

theorem quotient_trivial_automorphism_eq_one [Finite G]
    (f : G →* F) (hodd : Odd (Nat.card f.ker))
    (hcentral : f.ker ≤ Subgroup.center G)
    (hgen : Subgroup.closure {x : G | IsInvolution x} = ⊤)
    (a : MulAut G) (htrivial : ∀ x : G, f (a x) = f x) : a = 1 := by
  have hfixed : Set.EqOn a.toMonoidHom (MonoidHom.id G)
      {x : G | IsInvolution x} := by
    intro x hx
    exact quotient_trivial_automorphism_fixes_involution f hodd hcentral a htrivial hx
  have hclosure := MonoidHom.eqOn_closure hfixed
  apply MulEquiv.ext
  intro x
  exact hclosure (hgen.symm ▸ (show x ∈ (⊤ : Subgroup G) from Subgroup.mem_top x))

theorem characteristic_quotient_ker_eq_bot [Finite G]
    (N : Subgroup G) [N.Characteristic] (hodd : Odd (Nat.card N))
    (hcentral : N ≤ Subgroup.center G)
    (hgen : Subgroup.closure {x : G | IsInvolution x} = ⊤) :
    (quotient N).ker = ⊥ := by
  apply (Subgroup.eq_bot_iff_forall _).mpr
  intro a ha
  apply quotient_trivial_automorphism_eq_one (QuotientGroup.mk' N)
      (by simpa only [QuotientGroup.ker_mk'] using hodd)
      (by simpa only [QuotientGroup.ker_mk'] using hcentral) hgen
  intro x
  have hax := congrArg (fun b : MulAut (G ⧸ N) => b (QuotientGroup.mk' N x)) ha
  simpa only [quotient_apply_mk, MulAut.one_apply] using hax


end CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerHull
