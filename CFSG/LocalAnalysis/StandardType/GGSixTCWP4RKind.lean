module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RSet
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RLabel
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RSimple
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4ROrbLen

public section

namespace CFSG.StandardType.TableCRes

open Certificates.TcRes CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus

section Aux


end Aux

section Kind

variable {τ : Tag} {S : TcrSys}

theorem twistInner_congr {Ψ : Set (Fin τ.rank → ℤ)}
    {σ σ' : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ)} (h : ∀ γ ∈ Ψ, σ γ = σ' γ) :
    twistInner Ψ σ ↔ twistInner Ψ σ' := by
  unfold twistInner
  constructor
  · rintro ⟨w, hw, hσ⟩
    exact ⟨w, hw, fun γ hγ => (h γ hγ).symm.trans (hσ γ hγ)⟩
  · rintro ⟨w, hw, hσ⟩
    exact ⟨w, hw, fun γ hγ => (h γ hγ).trans (hσ γ hγ)⟩


end Kind

end CFSG.StandardType.TableCRes

end
