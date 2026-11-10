module

public import CFSG.CharacterTheory.TwoRankLowerBound.CharacterInflation
public import CFSG.CharacterTheory.TwoRankLowerBound.ProductCharacterSlice
public import CFSG.CharacterTheory.TwoRankLowerBound.CharacterBasis

public section

open scoped BigOperators Classical

namespace CFSG.TwoRankLowerBound.Helpers

theorem virtualCharacter_conjugation_invariant {G : Type*} [Group G]
    (function : G → ℂ) (hvirtual : function ∈ virtualCharacters G) (element conjugator : G) :
    function (conjugator * element * conjugator⁻¹) = function element := by
  induction hvirtual using Submodule.span_induction with
  | mem character hmember =>
    obtain ⟨data, rfl⟩ := hmember
    exact Representation.char_conj data.representation element conjugator
  | zero => rfl
  | add left right _ _ hleft hright =>
    simp only [Pi.add_apply, hleft, hright]
  | smul scalar function _ hequal =>
    simp only [Pi.smul_apply, hequal]

theorem virtualCharacters_mul {G : Type*} [Group G]
    (left right : G → ℂ) (hleft : left ∈ virtualCharacters G) (hright : right ∈ virtualCharacters G) :
    left * right ∈ virtualCharacters G := by
  induction hleft using Submodule.span_induction with
  | mem character hmember =>
    obtain ⟨data, rfl⟩ := hmember
    induction hright using Submodule.span_induction with
    | mem otherCharacter hother =>
      obtain ⟨other, rfl⟩ := hother
      have hcharacter : data.character * other.character =
          (data.representation.tprod other.representation).character :=
        (Representation.char_tensor _ _).symm
      rw [hcharacter]
      exact character_mem_virtualCharacters
        { vector := TensorProduct ℂ data.vector other.vector
          representation := data.representation.tprod other.representation }
    | zero => simpa only [mul_zero] using (virtualCharacters G).zero_mem
    | add first second _ _ hfirst hsecond =>
      rw [mul_add]
      exact (virtualCharacters G).add_mem hfirst hsecond
    | smul scalar function _ hfunction =>
      rw [mul_smul_comm]
      exact (virtualCharacters G).smul_mem scalar hfunction
  | zero => simpa only [zero_mul] using (virtualCharacters G).zero_mem
  | add first second _ _ hfirst hsecond =>
    rw [add_mul]
    exact (virtualCharacters G).add_mem hfirst hsecond
  | smul scalar function _ hfunction =>
    rw [smul_mul_assoc]
    exact (virtualCharacters G).smul_mem scalar hfunction


end CFSG.TwoRankLowerBound.Helpers
