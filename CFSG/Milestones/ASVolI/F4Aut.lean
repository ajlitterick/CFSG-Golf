module

public import CFSG.Milestones.ASVolI.F45.Two
public import CFSG.Milestones.ASVolI.F4Conjugacy
import all CFSG.Milestones.ASVolI.F4

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.ASVolI.ChF CFSG.ASVolI.ChF.ExceptionalRoots

section Generic

variable {S G : Type} [Group S] [Group G] (f : S →* G) (hf : Function.Injective f)

noncomputable def burnsideF45_conjOn (hR : f.range.Normal) : G →* MulAut S :=
  (MulAut.congr (MonoidHom.ofInjective hf).symm).toMonoidHom.comp
    (@MulAut.conjNormal G _ f.range hR)

theorem burnsideF45_conjOn_apply (hR : f.range.Normal) (g : G) (s : S) :
    f (burnsideF45_conjOn f hf hR g s) = g * f s * g⁻¹ := by
  show f ((MonoidHom.ofInjective hf).symm
    (@MulAut.conjNormal G _ f.range hR g (MonoidHom.ofInjective hf s))) = _
  rw [MonoidHom.apply_ofInjective_symm, MulAut.conjNormal_apply, MonoidHom.ofInjective_apply]

theorem burnsideF45_conjOn_injective (hR : f.range.index = 2)
    (hS : Subgroup.center S = ⊥) (hG : Subgroup.center G = ⊥) :
    Function.Injective (burnsideF45_conjOn f hf (Subgroup.normal_of_index_eq_two hR)) := by
  have hN : f.range.Normal := Subgroup.normal_of_index_eq_two hR
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro g hg
  rw [MonoidHom.mem_ker] at hg
  have hcent : ∀ s : S, g * f s = f s * g := by
    intro s
    have h1 := burnsideF45_conjOn_apply f hf hN g s
    rw [hg, MulAut.one_apply] at h1
    calc g * f s = (g * f s * g⁻¹) * g := by group
      _ = f s * g := by rw [← h1]
  have hZ : ∀ s : S, (∀ t : S, f s * f t = f t * f s) → s = 1 := by
    intro s hs
    have hsc : s ∈ Subgroup.center S := Subgroup.mem_center_iff.2 fun t =>
      hf (by rw [map_mul, map_mul]; exact (hs t).symm)
    rw [hS, Subgroup.mem_bot] at hsc
    exact hsc
  have hgc : g ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro x
    have hcR : x * g * x⁻¹ * g⁻¹ ∈ f.range := by
      have e : x * g * x⁻¹ * g⁻¹ = x * (g * x⁻¹ * g⁻¹) := by group
      rw [e, Subgroup.mul_mem_iff_of_index_two hR]
      constructor
      · intro hx
        exact hN.conj_mem _ (f.range.inv_mem hx) g
      · intro hx
        have := hN.conj_mem _ hx g⁻¹
        simpa [mul_assoc] using f.range.inv_mem this
    obtain ⟨s, hs⟩ := hcR
    have hcomm : ∀ t : S, f s * f t = f t * f s := by
      intro t
      rw [hs]
      obtain ⟨t', ht'⟩ : x⁻¹ * f t * x ∈ f.range := by
        have := hN.conj_mem _ ⟨t, rfl⟩ x⁻¹
        simpa using this
      have h1 : g * (x⁻¹ * f t * x) = (x⁻¹ * f t * x) * g := by
        rw [← ht']; exact hcent t'
      have h2 : g⁻¹ * f t = f t * g⁻¹ := by
        have := hcent t
        calc g⁻¹ * f t = g⁻¹ * (f t * g) * g⁻¹ := by group
          _ = g⁻¹ * (g * f t) * g⁻¹ := by rw [this]
          _ = f t * g⁻¹ := by group
      have h3 : x * g * x⁻¹ * f t = f t * (x * g * x⁻¹) := by
        calc x * g * x⁻¹ * f t = x * (g * (x⁻¹ * f t * x)) * x⁻¹ := by group
          _ = x * ((x⁻¹ * f t * x) * g) * x⁻¹ := by rw [h1]
          _ = f t * (x * g * x⁻¹) := by group
      calc x * g * x⁻¹ * g⁻¹ * f t = x * g * x⁻¹ * (g⁻¹ * f t) := by group
        _ = x * g * x⁻¹ * (f t * g⁻¹) := by rw [h2]
        _ = (x * g * x⁻¹ * f t) * g⁻¹ := by group
        _ = (f t * (x * g * x⁻¹)) * g⁻¹ := by rw [h3]
        _ = f t * (x * g * x⁻¹ * g⁻¹) := by group
    have hs1 := hZ s hcomm
    rw [hs1, map_one] at hs
    have : x * g * x⁻¹ = g := by
      have := congrArg (fun z => z * g) hs
      simpa [mul_assoc] using this.symm
    calc x * g = (x * g * x⁻¹) * x := by group
      _ = g * x := by rw [this]
  rw [hG, Subgroup.mem_bot] at hgc
  rw [Subgroup.mem_bot]
  exact hgc

theorem burnsideF45_card_of_index_two [Finite G] (hf : Function.Injective f)
    (hR : f.range.index = 2) :
    Nat.card G = 2 * Nat.card S := by
  have h := Subgroup.card_mul_index f.range
  rw [hR, ← Nat.card_congr (MonoidHom.ofInjective hf).toEquiv] at h
  omega

end Generic

section ExtEquiv


end ExtEquiv

section G2dCenter

open CFSG.Blueprint CFSG.Blueprint.Chevalley


variable {K : Type} [Field K] [Finite K]

theorem burnsideF45_g2_center_full : Subgroup.center (G2Native.FullModel K) = ⊥ :=
  burnsideF45_center_quotient_eq_bot CFSG.LieType.Chevalley.center_adjointGroup_eq_bot


theorem burnsideF45_g2_center_small (hK : Nat.card K = 2) :
    Subgroup.center (G2Native.SmallModel K) = ⊥ :=
  burnsideF45_center_quotient_eq_bot (burnsideF4h_g2_center_derived hK)

end G2dCenter

section G2d

open CFSG.Blueprint CFSG.Blueprint.Chevalley


variable {K : Type} [Field K] [Finite K]

theorem burnsideF45_g2_conj_bijective (hK : Nat.card K = 2) :
    Function.Bijective (burnsideF45_conjOn (burnsideF4h_g2_incl K hK)
      (burnsideF4h_g2_incl_injective hK)
      (Subgroup.normal_of_index_eq_two (burnsideF4h_g2_incl_index hK))) := by
  have hinj := burnsideF45_conjOn_injective (burnsideF4h_g2_incl K hK)
    (burnsideF4h_g2_incl_injective hK) (burnsideF4h_g2_incl_index hK)
    (burnsideF45_g2_center_small hK) burnsideF45_g2_center_full
  refine hinj.bijective_of_nat_card_le ?_
  rw [burnsideF45_card_of_index_two _ (burnsideF4h_g2_incl_injective hK)
    (burnsideF4h_g2_incl_index hK), burnsideF4h_g2_card_small hK,
    ← Nat.card_congr (MulAut.congr (burnsideF4h_g2_psi K hK)).toEquiv]
  exact card_mulAut_u33Pres_le


end G2d

section G2dExt

open CFSG.Blueprint CFSG.Blueprint.Chevalley


end G2dExt

section Tits

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Sporadic.Schreier.Tits


end Tits

section Main


end Main

end CFSG.ASVolI
