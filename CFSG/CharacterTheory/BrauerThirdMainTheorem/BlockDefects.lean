module

public import CFSG.CharacterTheory.BrauerThirdMainTheorem.ClassProducts
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.PolynomialCoefficients

public section

open CFSG
namespace CFSG.BrauerThirdMainTheorem.Helpers

theorem localMaxIdeal_mul_not_mem (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    {left right : ℂ} (hleftRing : left ∈ BlocksLocalRing m)
    (hrightRing : right ∈ BlocksLocalRing m)
    (hleft : left ∉ BlocksLocalMaxIdeal m) (hright : right ∉ BlocksLocalMaxIdeal m) :
    left * right ∉ BlocksLocalMaxIdeal m := by
  have hleftResidue : localResidue m hm ⟨left, hleftRing⟩ ≠ 0 :=
    fun hequal => hleft ((localResidue_eq_zero_iff m hm _).mp hequal)
  have hrightResidue : localResidue m hm ⟨right, hrightRing⟩ ≠ 0 :=
    fun hequal => hright ((localResidue_eq_zero_iff m hm _).mp hequal)
  intro hproduct
  have hzero := (localResidue_eq_zero_iff m hm
    (⟨left, hleftRing⟩ * ⟨right, hrightRing⟩)).mpr hproduct
  rw [map_mul] at hzero
  exact mul_ne_zero hleftResidue hrightResidue hzero

theorem localRing_natCast (m : Ideal BlocksAlgInt) (hm : m.IsMaximal) (number : ℕ) :
    (number : ℂ) ∈ BlocksLocalRing m := by
  simpa only [SubringClass.coe_natCast] using localRing_of_algInt m hm (number : BlocksAlgInt)

theorem localMaxIdeal_natCast_of_dvd (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    (prime : ℕ) (hprimeMem : (prime : BlocksAlgInt) ∈ m) {number : ℕ}
    (hdivides : prime ∣ number) : (number : ℂ) ∈ BlocksLocalMaxIdeal m := by
  obtain ⟨multiple, rfl⟩ := hdivides
  rw [Nat.cast_mul]
  exact localMaxIdeal_mul_localRing m hm (localMaxIdeal_of_mem m hm hprimeMem)
    (localRing_natCast m hm multiple)


end CFSG.BrauerThirdMainTheorem.Helpers
