module

public import CFSG.ThirdParty.BrauerInduction.Background.LinearChar.Inertia

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG
end CFSG
open CFSG

/-!
# Eigenspaces attached to linear characters

This file constructs the `ψ`-eigenspace of a representation restricted to a
normal subgroup `A`, shows that it is stable under the inertia subgroup of `ψ`,
and packages it as an `FDRep`.

The final lemmas record the two Clifford-theoretic facts needed later: elements
of `A` act by the scalar `ψ`, and if the inertia subgroup is all of `G`, then a
nonzero eigenspace is the whole simple representation.
-/

universe u v w

namespace CFSG.LinearChar

open CategoryTheory

variable {k : Type u} [Field k]
variable {G : Type v} [Group G]

/--
The `ψ`-eigenspace of the restriction of `ρ` to a normal subgroup `A`.
A vector `v` belongs to this subspace iff every `a : A` acts by the scalar `ψ a`.
-/
@[expose] noncomputable def psiEigenspace
    (ρ : FDRep k G) (A : Subgroup G) (ψ : A →* kˣ) :
    Submodule k ρ :=
  ⨅ a : A, LinearMap.ker (ρ.ρ (a : G) - (ψ a : k) • LinearMap.id)

/--
Membership criterion for the `ψ`-eigenspace.
-/
lemma mem_psiEigenspace_iff
    (ρ : FDRep k G) (A : Subgroup G) (ψ : A →* kˣ) (v : ρ) :
    v ∈ psiEigenspace ρ A ψ
      ↔ ∀ a : A, ρ.ρ (a : G) v = (ψ a : k) • v := by
  simp only [psiEigenspace, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
    sub_eq_zero]

/--
The `ψ`-eigenspace is stable under the inertia subgroup of `ψ`.
-/
lemma psiEigenspace_invariant
    (ρ : FDRep k G) (A : Subgroup G) [hA : A.Normal]
    (ψ : A →* kˣ)
    (g : LinearChar.inertia (H := A) ψ)
    (v : ρ)
    (hv : v ∈ psiEigenspace ρ A ψ) :
    ρ.ρ (g : G) v ∈ psiEigenspace ρ A ψ := by
  rw [mem_psiEigenspace_iff] at hv ⊢
  intro a
  have hmem : g.1⁻¹ * (a : G) * g.1 ∈ A := by
    simpa using Subgroup.Normal.conj_mem hA (a : G) a.2 (g.1⁻¹)
  let a' : A := ⟨g.1⁻¹ * (a : G) * g.1, hmem⟩
  have hag : (a : G) * (g : G) = (g : G) * (a' : G) := by
    dsimp [a']
    group
  calc
    ρ.ρ (a : G) (ρ.ρ (g : G) v)
        = ρ.ρ ((a : G) * (g : G)) v := by
          simp only [map_mul, Module.End.mul_apply]
    _ = ρ.ρ ((g : G) * (a' : G)) v := by
          rw [hag]
    _ = ρ.ρ (g : G) (ρ.ρ (a' : G) v) := by
          simp only [map_mul, Module.End.mul_apply]
    _ = ρ.ρ (g : G) ((ψ a' : k) • v) := by
          rw [hv a']
    _ = ρ.ρ (g : G) ((ψ a : k) • v) := by
          have hψ_units : ψ a' = ψ a := by
            have hg_inv : LinearChar.conj (H := A) ψ ((g : G)⁻¹) = ψ := by
              exact (LinearChar.mem_inertia_iff (H := A) ψ ((g : G)⁻¹)).mp
                (Subgroup.inv_mem (LinearChar.inertia (H := A) ψ) g.2)
            calc
              ψ a' = LinearChar.conj (H := A) ψ ((g : G)⁻¹) a := by
                rw [LinearChar.conj_apply]
                congr
                ext
                simp [a']
              _ = ψ a := by
                rw [hg_inv]
          have hψ : ((ψ a' : kˣ) : k) = ((ψ a : kˣ) : k) :=
            congrArg (fun z : kˣ => (z : k)) hψ_units
          rw [hψ]
    _ = (ψ a : k) • ρ.ρ (g : G) v := by
          exact (ρ.ρ (g : G)).map_smul (ψ a : k) v

/--
The `ψ`-eigenspace of `ρ` as a representation of the inertia subgroup of `ψ`.
-/
@[expose] noncomputable def psiEigenspaceFDRep
    (ρ : FDRep k G)
    (A : Subgroup G) [A.Normal]
    (ψ : A →* kˣ) :
    FDRep k (LinearChar.inertia (H := A) ψ) :=
  FDRep.ofSubmodule
    (ρ.res (LinearChar.inertia (H := A) ψ))
    (psiEigenspace ρ A ψ)
    (by
      intro g v hv
      exact psiEigenspace_invariant
        ρ A ψ g v hv)

@[simp] lemma psiEigenspaceFDRep_rho_apply
    (ρ : FDRep k G)
    (A : Subgroup G) [A.Normal]
    (ψ : A →* kˣ)
    (g : inertia ψ)
    (v : psiEigenspace ρ A ψ) :
    (psiEigenspaceFDRep ρ A ψ).ρ g v
      =
    (⟨ρ.ρ (g : G) v.1,
      psiEigenspace_invariant ρ A ψ g v.1 v.2⟩ : psiEigenspace ρ A ψ) := by
  rfl

/--
The canonical inclusion of the `ψ`-eigenspace representation into the
restriction of `ρ` to the inertia subgroup of `ψ`.
-/
@[expose] noncomputable def psiEigenspaceIncl
    (ρ : FDRep k G)
    (A : Subgroup G) [A.Normal]
    (ψ : A →* kˣ) :
    psiEigenspaceFDRep ρ A ψ
      ⟶
    ρ.res (LinearChar.inertia (H := A) ψ) :=
  FDRep.ofSubmoduleIncl
    (ρ.res (LinearChar.inertia (H := A) ψ))
    (psiEigenspace ρ A ψ)
    (by
      intro g v hv
      exact psiEigenspace_invariant
        ρ A ψ g v hv)

instance psiEigenspaceIncl_mono
    (ρ : FDRep k G)
    (A : Subgroup G) [A.Normal]
    (ψ : A →* kˣ) :
    Mono (psiEigenspaceIncl ρ A ψ) := by
  apply ConcreteCategory.mono_of_injective
     (C := FDRep k (LinearChar.inertia (H := A) ψ))
  exact
    (Set.injective_codRestrict Subtype.property).mp fun ⦃a₁ a₂⦄ a ↦ a


lemma psiEigenspace_invariant_of_inertia_eq_top
    (ρ : FDRep k G)
    (A : Subgroup G) [A.Normal]
    (ψ : A →* kˣ)
    (hI : LinearChar.inertia ψ = ⊤)
    (g : G)
    (v : ρ)
    (hv : v ∈ psiEigenspace ρ A ψ) :
    ρ.ρ g v ∈ psiEigenspace ρ A ψ := by
  have hg : g ∈ LinearChar.inertia ψ := by
    simp only [hI, Subgroup.mem_top]
  exact psiEigenspace_invariant
    ρ A ψ
    ⟨g, hg⟩ v hv

/--
If the inertia subgroup is all of `G`, then the `ψ`-eigenspace is a
`G`-subrepresentation of `ρ`.
-/
@[expose] noncomputable def psiEigenspaceFDRepOfInertiaEqTop
    (ρ : FDRep k G)
    (A : Subgroup G) [A.Normal]
    (ψ : A →* kˣ)
    (hI : LinearChar.inertia ψ = ⊤) :
    FDRep k G := by
  let W : Submodule k ρ := psiEigenspace ρ A ψ
  exact FDRep.ofSubmodule ρ W (by
    intro g x hx
    exact psiEigenspace_invariant_of_inertia_eq_top
      ρ A ψ hI g x hx)

/--
The whole-group eigenspace representation embeds into `ρ`.
-/
@[expose] noncomputable def psiEigenspaceInclOfInertiaEqTop
    (ρ : FDRep k G)
    (A : Subgroup G) [A.Normal]
    (ψ : A →* kˣ)
    (hI : LinearChar.inertia ψ = ⊤) :
    psiEigenspaceFDRepOfInertiaEqTop
      ρ A ψ hI ⟶ ρ := by
  let W : Submodule k ρ := psiEigenspace ρ A ψ
  exact FDRep.ofSubmoduleIncl ρ W (by
    intro g x hx
    exact psiEigenspace_invariant_of_inertia_eq_top
      ρ A ψ hI g x hx)

@[simp] lemma psiEigenspaceInclOfInertiaEqTop_apply
    (ρ : FDRep k G)
    (A : Subgroup G) [A.Normal]
    (ψ : A →* kˣ)
    (hI : LinearChar.inertia ψ = ⊤)
    (x : psiEigenspace ρ A ψ) :
    (psiEigenspaceInclOfInertiaEqTop
      ρ A ψ hI).hom x
      =
    (x : ρ) := by
  rfl


end CFSG.LinearChar
