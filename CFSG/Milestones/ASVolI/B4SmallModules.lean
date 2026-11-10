module

public import CFSG.Milestones.ASVolI.B4
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.Quasithin.EmptyFaithful.SzN2Quot
public import CFSG.Quasithin.Vol2.Ch11SecB414MF
public import CFSG.Quasithin.Vol2.Ch11SecB414MS
public import CFSG.Quasithin.Vol2.Ch11SecB414N
public import CFSG.Quasithin.Vol2.Ch11SecB414PA
public import CFSG.Quasithin.Vol2.Ch11SecB414PC
public import CFSG.Quasithin.Vol2.Ch11SecB414PD

public section

namespace CFSG.ASVolI

open CFSG.Open

section

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain


section Generic

variable {K : Type} [Field K]


end Generic


end

section


end

section

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open scoped Matrix

section TwoElt

variable {K : Type} [Field K]


end TwoElt

end

section

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open scoped Matrix


theorem burnsideB4h_wedgeAct_one {K : Type} [Field K] :
    wedgeAct (1 : Matrix (Fin 4) (Fin 4) K) = LinearMap.id := by
  unfold wedgeAct
  rw [Matrix.toLin'_one, exteriorPower.map_id]

theorem burnsideB4h_wedgeAct_mul {K : Type} [Field K] (M N : Matrix (Fin 4) (Fin 4) K) :
    wedgeAct (M * N) = (wedgeAct M).comp (wedgeAct N) := by
  unfold wedgeAct
  rw [Matrix.toLin'_mul, exteriorPower.map_comp]

@[expose, instance_reducible] noncomputable def burnsideB4h_wact :
    MulAction (GL (Fin 4) (ZMod 2)) (wedgeSpace (ZMod 2)) where
  smul g w := wedgeAct g.1 w
  one_smul w := by
    show wedgeAct (1 : GL (Fin 4) (ZMod 2)).1 w = w
    rw [Units.val_one, burnsideB4h_wedgeAct_one]
    rfl
  mul_smul g h w := by
    show wedgeAct (g * h).1 w = wedgeAct g.1 (wedgeAct h.1 w)
    rw [Units.val_mul, burnsideB4h_wedgeAct_mul]
    rfl


section StabSection

attribute [local instance] burnsideB4h_wact


end StabSection


end

section

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open scoped Matrix


section PhiSection

variable {V : Type} [CommGroup V] (ρ : GL (Fin 4) (ZMod 2) →* MulAut V) (v : V)


variable {ρ v}


end PhiSection

end

section


end

section

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open scoped Matrix


section OrbitCount

attribute [local instance] burnsideB4h_wact


end OrbitCount


end

section

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open scoped Matrix


end

section

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open scoped Matrix


end

section

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open scoped Matrix


end

section

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open scoped Matrix


end

section

open CFSG.Open
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open scoped Matrix


end

section

section Transport
open CFSG.Quasithin CFSG.QuasithinUnique

variable {V : Type} [CommGroup V] (G : Subgroup (MulAut V)) {R : Type} [Group R] (α : ↥G ≃* R)


variable {G α}


variable [Finite V] [Finite R]


end Transport

end

section

section Unique
open CFSG.ASVolI.ChB

variable {F : Type} [Field F]


end Unique

end

section

section TrInv

variable {F : Type} [Field F]


end TrInv

end

section

section Found
open CFSG.ASVolI.ChB

variable {F : Type} [Field F]


end Found

section C0
open CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A CFSG.Quasithin.H13.Ch4.B414.M

variable {F : Type} [Field F]


end C0

section Cases
open scoped TensorProduct

variable {F : Type} [Field F]


end Cases

end

section

section NatBase
open CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A CFSG.Quasithin.H13.Ch4.B414.M

variable {F : Type} [Field F]


end NatBase

end

section

section Psi
open scoped TensorProduct

variable {F : Type} [Field F]


end Psi

section Classify

variable {F : Type} [Field F]

@[expose] def burnsideB4h_ConjInv (S : Submodule F (Matrix (Fin 2) (Fin 2) F)) : Prop :=
  ∀ A A' : Matrix (Fin 2) (Fin 2) F, A * A' = 1 → A' * A = 1 → A.det = 1 →
    ∀ N ∈ S, A * N * A' ∈ S


section KeyLemmas

variable {S : Submodule F (Matrix (Fin 2) (Fin 2) F)} (hS : burnsideB4h_ConjInv S)
  (h2 : (2 : F) = 0) {ω : F} (hω : ω ^ 2 + ω + 1 = 0)
include hS


include h2 hω


end KeyLemmas


end Classify

section Assembly
open scoped TensorProduct

variable {F : Type} [Field F]


end Assembly

end

section

section TensorBase
open scoped TensorProduct
open CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A CFSG.Quasithin.H13.Ch4.B414.M

variable {F : Type} [Field F]


end TensorBase

end

section

section Transport
open scoped TensorProduct
open CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A CFSG.Quasithin.H13.Ch4.B414.M

variable {F : Type} [Field F]


end Transport

end

section

section VLevel
open scoped TensorProduct
open CFSG.Quasithin CFSG.ASVolI.ChB

variable {V : Type} [CommGroup V] {F : Type} [Field F]


end VLevel

end

section

section NatBridge
open CFSG.Quasithin


section Induced

variable {V : Type} [CommGroup V] (H : Subgroup (MulAut V)) (C₁ C₂ : Subgroup V)
  (hC₁ : ∀ h ∈ H, ∀ c ∈ C₁, h c ∈ C₁) (hC₂ : ∀ h ∈ H, ∀ c ∈ C₂, h c ∈ C₂)
include hC₂


omit hC₂
include hC₁ hC₂


end Induced


end NatBridge

end

section

section Semi

open SemidirectProduct

variable {V : Type} [CommGroup V] (G : Subgroup (MulAut V))

abbrev burnsideB4h_Amb : Type := V ⋊[G.subtype] ↥G

@[expose] def burnsideB4h_V0 : Subgroup (burnsideB4h_Amb G) :=
  (inl : V →* burnsideB4h_Amb G).range


variable {G}


instance burnsideB4h_V0_normal : (burnsideB4h_V0 G).Normal := by
  unfold burnsideB4h_V0
  rw [range_inl_eq_ker_rightHom]
  exact MonoidHom.normal_ker _

instance burnsideB4h_finite_Amb [Finite V] [Finite ↥G] : Finite (burnsideB4h_Amb G) :=
  Finite.of_equiv (V × ↥G) (SemidirectProduct.equivProd (N := V) (G := ↥G) (φ := G.subtype)).symm


end Semi

end

section

section HypNat

open SemidirectProduct CFSG.Quasithin CFSG.QuasithinUnique


end HypNat

end

section

section ClsBeta

open Subgroup CFSG.QuasithinUnique.Setup.X7a CFSG.Quasithin.H13.Ch4 CFSG.Quasithin.H13.Ch4.B414
open scoped MatrixGroups Matrix


end ClsBeta

end

section

section HypBuild

open SemidirectProduct CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB


end HypBuild

end

section

section Cls

open SemidirectProduct CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB


end Cls

end

section

section
open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB


end

end

end CFSG.ASVolI
