module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.CharTwo
import CFSG.LocalAnalysis.QuasithinUnique.CharTwoTransport

public section

namespace CFSG.Quasithin.SteinbergCF

open CFSG Subgroup

variable {G : Type*} [Group G]

theorem charTwo_iff_isCharacteristicP {K : Subgroup G} :
    CFSG.QuasithinUnique.CharTwo K ↔ IsCharacteristicP 2 K :=
  CFSG.QuasithinUnique.charTwo_iff_isCharacteristicP


theorem isEvenCharacteristic_of_quasithinEvenCharacteristic
    (h : CFSG.Assembly.Quasithin.quasithinEvenCharacteristic G) : IsEvenCharacteristic G :=
  fun H hH hS => charTwo_iff_isCharacteristicP.mp (h H hH hS)


theorem charTwo_of_sylow_le [Finite G] {X J P : Subgroup G}
    (hX : CFSG.QuasithinUnique.CharTwo X) (hP : CFSG.QuasithinUnique.IsSylowTwoOf P X)
    (hPJ : P ≤ J) (hJX : J ≤ X) :
    CFSG.QuasithinUnique.CharTwo J :=
  CFSG.QuasithinUnique.charTwo_of_pCore_centralizer_le hX hJX
    (inf_le_left.trans ((CFSG.QuasithinUnique.EscapingLocal.pCoreOf_le_of_isSylowTwoOf hP).trans
      hPJ))

theorem isSylowTwoOf_of_le_of_le {P X H : Subgroup G}
    (hP : CFSG.QuasithinUnique.IsSylowTwoOf P H) (hPX : P ≤ X) (hXH : X ≤ H) :
    CFSG.QuasithinUnique.IsSylowTwoOf P X := by
  refine ⟨hPX, hP.2.1, fun h => hP.2.2 ?_⟩
  change 2 ∣ P.relIndex H
  change 2 ∣ P.relIndex X at h
  exact h.trans ⟨_, (relIndex_mul_relIndex P X H hPX hXH).symm⟩


end CFSG.Quasithin.SteinbergCF
