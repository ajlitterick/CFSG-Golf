module

public import CFSG.LieType.Steinberg.Isogeny.Minuscule
public import CFSG.LieType.Steinberg.Adjoint.CertE6Valid
public import CFSG.LieType.Chevalley.RootOps.All

public noncomputable section

namespace CFSG.LieType.Steinberg.Isogeny

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.Adjoint

theorem e6_checkSigns : checkSigns e6Data e6AdjData = true := by decide +kernel

variable (k : Type) [Field k] [Finite k]

@[expose] def e6Isogeny : ↥(e6Data_valid.minGroup k) →* ↥(adjointGroup .E6 k) :=
  isogeny e6Data_valid posDef_cartan_E6 (rootOperatorFamily .E6) e6AdjData_valid noG2_E6
    e6_checkSigns k (roots_eq isFiniteType_cartan_E6) (e6_presentationB k)

theorem e6Isogeny_xm {γ : Fin (Tag.rank .E6) → ℤ} (hγ : IsRoot .E6 γ) (c : k) :
    e6Isogeny k (e6Data_valid.xm k γ c) = yPar (rootOperatorFamily .E6) e6AdjData_valid γ c :=
  isogeny_xm _ _ _ _ _ _ k _ _ hγ c

theorem e6Isogeny_xm_single (i : Fin (Tag.rank .E6)) (c : k) :
    e6Isogeny k (e6Data_valid.xm k (Pi.single i 1) c) =
      (rootOperatorFamily .E6).eltElement (simpleRoot .E6 i) c :=
  isogeny_xm_single _ _ _ _ _ _ k _ _ i c

theorem e6Isogeny_xm_neg_single (i : Fin (Tag.rank .E6)) (c : k) :
    e6Isogeny k (e6Data_valid.xm k (-Pi.single i 1) c) =
      (rootOperatorFamily .E6).eltElement (-simpleRoot .E6 i) c :=
  isogeny_xm_neg_single _ _ _ _ _ _ k _ _ i c

theorem e6Isogeny_surjective : Function.Surjective (e6Isogeny k) :=
  isogeny_surjective _ _ _ _ _ _ k _ _

theorem e6Isogeny_xm_single_one_ne_one (i : Fin (Tag.rank .E6)) :
    e6Isogeny k (e6Data_valid.xm k (Pi.single i 1) 1) ≠ 1 :=
  isogeny_xm_single_one_ne_one _ _ _ _ _ _ k _ _ i

theorem e6Isogeny_ne_one : ∃ g, e6Isogeny k g ≠ 1 :=
  isogeny_ne_one _ _ _ _ _ _ k _ _

end CFSG.LieType.Steinberg.Isogeny
