module

public import CFSG.CharacterTheory.BrauerSplittingField.Descent
public import CFSG.ThirdParty.BrauerInduction.Background.LinearChar.InducedCharacter
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ENatToNat
public import CFSG.ThirdParty.BrauerInduction.Background.Fintype.Basic

public section

namespace CFSG

namespace BrauerSplittingField

noncomputable section

variable {G : Type} [Group G] [Fintype G]

local notation "nG" => Monoid.exponent G
local notation "KG" => CyclotomicField nG ℚ

def complexLinearCharToRoots (H : Subgroup G) (psi : H →* ℂˣ) :
    H →* rootsOfUnity nG ℂ where
  toFun h := ⟨psi h, by
    rw [mem_rootsOfUnity, ← map_pow]
    rw [show h ^ nG = 1 by
      apply Subtype.ext
      exact Monoid.pow_exponent_eq_one (h : G)]
    exact map_one psi⟩
  map_one' := by
    apply Subtype.ext
    exact map_one psi
  map_mul' x y := by
    apply Subtype.ext
    exact map_mul psi x y

theorem cyclotomicPrimitiveRootsNonempty :
    (primitiveRoots nG KG).Nonempty := by
  let : NeZero nG := Monoid.neZero_exponent_of_finite
  let : NeZero (nG : ℚ) := ⟨by exact_mod_cast (NeZero.ne nG)⟩
  let : IsCyclotomicExtension {nG} ℚ KG :=
    CyclotomicField.isCyclotomicExtension nG ℚ
  refine ⟨IsCyclotomicExtension.zeta nG ℚ KG, ?_⟩
  exact (mem_primitiveRoots (NeZero.pos nG)).2
    (IsCyclotomicExtension.zeta_spec nG ℚ KG)

def descendLinearChar (phi : KG →+* ℂ) (H : Subgroup G) (psi : H →* ℂˣ) :
    H →* KGˣ := by
  letI : NeZero nG := Monoid.neZero_exponent_of_finite
  exact (rootsOfUnity nG KG).subtype.comp
    ((rootsOfUnityEquivOfPrimitiveRoots phi.injective
      (cyclotomicPrimitiveRootsNonempty (G := G))).symm.toMonoidHom.comp
        (complexLinearCharToRoots H psi))

@[simp]
theorem map_descendLinearChar (phi : KG →+* ℂ) (H : Subgroup G)
    (psi : H →* ℂˣ) (h : H) :
    phi (descendLinearChar phi H psi h : KG) = (psi h : ℂ) := by
  let : NeZero nG := Monoid.neZero_exponent_of_finite
  simpa [descendLinearChar, complexLinearCharToRoots] using
    (rootsOfUnityEquivOfPrimitiveRoots_symm_apply phi.injective
      (cyclotomicPrimitiveRootsNonempty (G := G))
      (complexLinearCharToRoots H psi h))

def inducedLinearCharacterValue {F : Type} [Field F]
    (H : Subgroup G) (psi : H →* Fˣ) (g : G) : F := by
  classical
  exact (Fintype.card H : F)⁻¹ * ∑ x : G,
      if h : x * g * x⁻¹ ∈ H then
        (psi ⟨x * g * x⁻¹, h⟩ : F)
      else 0

@[simp]
theorem map_inducedLinearCharacterValue
    (phi : KG →+* ℂ) (H : Subgroup G) (psi : H →* ℂˣ) (g : G) :
    phi (inducedLinearCharacterValue H (descendLinearChar phi H psi) g) =
      inducedLinearCharacterValue H psi g := by
  classical
  simp only [inducedLinearCharacterValue, map_mul, map_inv₀, map_natCast,
    map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  split_ifs
  · exact map_descendLinearChar phi H psi _
  · exact map_zero phi


end

end BrauerSplittingField

end CFSG
