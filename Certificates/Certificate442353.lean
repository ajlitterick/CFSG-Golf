module

public import CFSG.LieType.Multipliers.U43Action
import Certificates.Kernel.U43CentPlus.Final

public section

namespace Certificates

open CertificateChecks

open CFSG.LieType.Multipliers.U43 in
theorem certificate442353 :
    (∀ Q₁ Q₂ : Subgroup X₀, Nonempty (↥Q₁ ≃* QuaternionGroup 2) →
      Nonempty (↥Q₂ ≃* QuaternionGroup 2) → ⁅Q₁, Q₂⁆ = ⊥ → Nat.card ↥(Q₁ ⊔ Q₂) = 32 →
      Subgroup.centralizer ((Q₁ ⊔ Q₂ : Subgroup X₀) : Set X₀) ≤ Q₁ ⊔ Q₂) ∧
    (∀ Q₁ Q₂ Q₃ Q₄ : Subgroup X₀, Nonempty (↥Q₁ ≃* QuaternionGroup 2) →
      Nonempty (↥Q₂ ≃* QuaternionGroup 2) → ⁅Q₁, Q₂⁆ = ⊥ → Nat.card ↥(Q₁ ⊔ Q₂) = 32 →
      Nonempty (↥Q₃ ≃* QuaternionGroup 2) → Nonempty (↥Q₄ ≃* QuaternionGroup 2) →
      ⁅Q₃, Q₄⁆ = ⊥ → Nat.card ↥(Q₃ ⊔ Q₄) = 32 →
      ∃ g : X₀, Q₃ ⊔ Q₄ = (Q₁ ⊔ Q₂).map (MulAut.conj g).toMonoidHom) :=
  ⟨KernelU43CentPlus.x0_cent, KernelU43CentPlus.x0_conj⟩

end Certificates
