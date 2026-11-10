module

public import CFSG.Quasithin.Background.B1More13A
public import CFSG.Quasithin.Background.G10Clifford

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

namespace G108Hyp

variable [Finite V] {B : LinearMap.BilinForm (ZMod 2) V} {Γ : Subgroup (GLV V)} {v₁ : V}
  {W : Submodule (ZMod 2) V} {X X₀ L : Subgroup (GLV V)} (hyp : G108Hyp B Γ v₁ W X X₀ L)

include hyp

theorem exists_noncomm {a : GLV V} (ha1 : a ≠ 1)
    (hrank : Module.finrank (ZMod 2) (LinearMap.range (a.toLinearMap - LinearMap.id)) ≤ 2) :
    ∃ h ∈ normalClosure Γ L, a * h ≠ h * a := by
  by_contra hcon
  push Not at hcon
  set R := LinearMap.range (a.toLinearMap - LinearMap.id) with hR
  have hRinv : Invariant (normalClosure Γ L) R := by
    rintro h hh _ ⟨v, rfl⟩
    refine ⟨h v, ?_⟩
    have := congrArg (fun g : GLV V => g v) (hcon h hh)
    simp only [LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply, map_sub]
    have h2 : a (h v) = h (a v) := this
    rw [h2]
  have hR0 : R ≠ ⊥ := by
    intro h0
    apply ha1
    ext v
    have hmem : (a.toLinearMap - LinearMap.id : V →ₗ[ZMod 2] V) v ∈ R := ⟨v, rfl⟩
    rw [h0, Submodule.mem_bot] at hmem
    have : a v - v = 0 := hmem
    exact sub_eq_zero.1 this
  obtain ⟨J, hJR, hJ⟩ := exists_isIrr_le hRinv hR0
  have hJ' : IrrPlus (normalClosure Γ L) J := hJ.irrPlus hyp.fixedSpace_H
  have h1 := hyp.two_lt_finrank hJ
  have h2 := Submodule.finrank_mono hJR
  omega

theorem conj_eq_of_finrank_le {a : GLV V} (ha : a ∈ X)
    (hrank : Module.finrank (ZMod 2) (LinearMap.range (a.toLinearMap - LinearMap.id)) ≤ 2)
    {I : Submodule (ZMod 2) V} (hI : IrrPlus (normalClosure Γ L) I) : conjSub a I = I := by
  have hirr : IsIrr (normalClosure Γ L) I := hI.isIrr hyp.fixedSpace_H
  by_contra hne
  have hbot : conjSub a I ⊓ I = ⊥ := by
    rcases hirr.conj_eq_or_inf_eq_bot (normalClosure_normal Γ L) (hyp.X_le ha) with h | h
    · exact absurd h hne
    · exact h
  let φ : ↥I →ₗ[ZMod 2] V := (a.toLinearMap - LinearMap.id : V →ₗ[ZMod 2] V).domRestrict I
  have hφ : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    have h1 : a (u : V) - (u : V) = 0 := hu
    have h2 : a (u : V) = (u : V) := sub_eq_zero.1 h1
    have h3 : (u : V) ∈ conjSub a I ⊓ I := ⟨by
      have := apply_mem_conjSub (g := a) u.2
      rwa [h2] at this, u.2⟩
    rw [hbot, Submodule.mem_bot] at h3
    exact Subtype.ext h3
  have hle : LinearMap.range φ ≤ LinearMap.range (a.toLinearMap - LinearMap.id) := by
    rintro _ ⟨u, rfl⟩
    exact ⟨(u : V), rfl⟩
  have h1 := LinearEquiv.finrank_eq (LinearEquiv.ofInjective φ hφ)
  have h2 := Submodule.finrank_mono hle
  have h3 := hyp.two_lt_finrank hirr
  omega


end G108Hyp

end G11

end CFSG.Quasithin
