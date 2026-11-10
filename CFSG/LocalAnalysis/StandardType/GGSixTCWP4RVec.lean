module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RSet

public section

namespace CFSG.StandardType.TableCRes

open Certificates.TcRes CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus

section Vanish

variable {τ : Tag} {S : TcrSys}


theorem mem_kernelRoots_chiQ (p : ℕ) (Q : Set (Fin τ.rank → ZMod p)) (γ : Fin τ.rank → ℤ) :
    γ ∈ kernelRoots (tcChiQ τ p Q) ↔
      IsRoot τ γ ∧ ∀ v ∈ Q, ∑ k, ((γ k : ℤ) : ZMod p) * v k = 0 := by
  unfold kernelRoots tcChiQ
  simp only [Set.mem_setOf_eq, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd]
  refine and_congr_right fun _ => ?_
  rw [← ofAdd_zero, Multiplicative.ofAdd.injective.eq_iff]
  constructor
  · intro h v hv
    exact congrFun h ⟨v, hv⟩
  · intro h
    funext v
    exact h v v.2


end Vanish

end CFSG.StandardType.TableCRes

namespace CFSG.StandardType.TableCRes

open Certificates.TcRes CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus

section VecUtil

variable {τ : Tag} {p : ℕ}

@[expose] def tcrPairL (τ : Tag) (p : ℕ) (γ : Fin τ.rank → ℤ) :
    (Fin τ.rank → ZMod p) →ₗ[ZMod p] ZMod p :=
  ∑ k, ((γ k : ℤ) : ZMod p) • (LinearMap.proj k : (Fin τ.rank → ZMod p) →ₗ[ZMod p] ZMod p)

theorem tcrPairL_apply (γ : Fin τ.rank → ℤ) (v : Fin τ.rank → ZMod p) :
    tcrPairL τ p γ v = ∑ k, ((γ k : ℤ) : ZMod p) * v k := by
  simp [tcrPairL, LinearMap.sum_apply]

theorem kernelRoots_chiQ_eq_of_span (Q Q' : Set (Fin τ.rank → ZMod p))
    (h : Submodule.span (ZMod p) Q = Submodule.span (ZMod p) Q') :
    kernelRoots (tcChiQ τ p Q) = kernelRoots (tcChiQ τ p Q') := by
  have key : ∀ (A B : Set (Fin τ.rank → ZMod p)),
      Submodule.span (ZMod p) A ≤ Submodule.span (ZMod p) B →
      kernelRoots (tcChiQ τ p B) ⊆ kernelRoots (tcChiQ τ p A) := by
    intro A B hAB γ hγ
    rw [mem_kernelRoots_chiQ] at hγ ⊢
    refine ⟨hγ.1, fun v hv => ?_⟩
    have hker : Submodule.span (ZMod p) B ≤ LinearMap.ker (tcrPairL τ p γ) := by
      rw [Submodule.span_le]
      intro w hw
      rw [SetLike.mem_coe, LinearMap.mem_ker, tcrPairL_apply]
      exact hγ.2 w hw
    have := hker (hAB (Submodule.subset_span hv))
    rwa [LinearMap.mem_ker, tcrPairL_apply] at this
  exact Set.Subset.antisymm (key _ _ h.ge) (key _ _ h.le)

theorem kernelRoots_chiQ_mono {Q Q' : Set (Fin τ.rank → ZMod p)} (h : Q' ⊆ Q) :
    kernelRoots (tcChiQ τ p Q) ⊆ kernelRoots (tcChiQ τ p Q') := by
  intro γ hγ
  rw [mem_kernelRoots_chiQ] at hγ ⊢
  exact ⟨hγ.1, fun v hv => hγ.2 v (h hv)⟩

theorem kernelRoots_chiQ_smul [Fact p.Prime] (c : ZMod p) (hc : c ≠ 0)
    (x : Fin τ.rank → ZMod p) :
    kernelRoots (tcChiQ τ p {c • x}) = kernelRoots (tcChiQ τ p {x}) := by
  apply kernelRoots_chiQ_eq_of_span
  rw [Submodule.span_singleton_eq_span_singleton.2]
  exact ⟨Units.mk0 c⁻¹ (inv_ne_zero hc), by simp [Units.smul_def, smul_smul, inv_mul_cancel₀ hc]⟩

end VecUtil

end CFSG.StandardType.TableCRes

namespace CFSG.StandardType.TableCRes

open Certificates.TcRes CFSG.Blueprint.Chevalley

section PlaneLines


end PlaneLines

end CFSG.StandardType.TableCRes

end
