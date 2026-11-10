module

public import CFSG.Quasithin.Recognition.CertTitsSimpleMain
public meta import CFSG.Sporadic.Schreier.TitsArrays
public meta import CFSG.Quasithin.Recognition.CertTits
public meta import CFSG.Open.QuasithinDefs

public section

namespace CFSG.Quasithin

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
open CFSG.Sporadic.Schreier.Tits (titsD titsDGen titsDerivedArrs titsDerived_perm titsChains_check
  titsDerivedArrs_size titsModelEquiv isInvA_of_allPermsOK)

theorem titsBridge_array₁ :
    titsArray CFSG.Open.quasithinTitsData1 = titsDerivedArrs[0]! :=
  Certificates.certificate8072.1

theorem titsBridge_array₂ :
    titsArray CFSG.Open.quasithinTitsData2 = titsDerivedArrs[1]! :=
  Certificates.certificate8072.2

theorem titsBridge_isInv {j : ℕ} (hj : j < 2) :
    isInvA 1755 titsDerivedArrs[j]! (invCand 1755 titsDerivedArrs[j]!) = true :=
  isInvA_of_allPermsOK titsChains_check.2.2.2.2.2.2.1 (by rw [titsDerivedArrs_size]; omega)

theorem titsBridge_closure :
    Subgroup.closure ({permOfArr 1755 (titsArray CFSG.Open.quasithinTitsData1),
      permOfArr 1755 (titsArray CFSG.Open.quasithinTitsData2)} : Set (Equiv.Perm (Fin 1755))) =
      titsD := by
  rw [titsBridge_array₁, titsBridge_array₂, titsDerived_perm (by norm_num),
    titsDerived_perm (by norm_num), titsD]
  congr 1
  ext g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range, Fin.exists_fin_two]
  tauto

noncomputable def quasithinTitsEquivD :
    CFSG.Open.quasithinTits ≃* titsD :=
  (unitsClosurePairEquiv _ _ _ _
    (coe_permOfArr_titsArray CFSG.Open.quasithinTitsData1
      (by rw [titsBridge_array₁]; exact titsBridge_isInv (by norm_num)))
    (coe_permOfArr_titsArray CFSG.Open.quasithinTitsData2
      (by rw [titsBridge_array₂]; exact titsBridge_isInv (by norm_num)))).trans
    (MulEquiv.subgroupCongr titsBridge_closure)

theorem titsModelBridge_of_lieModel
    (X : Type) [Group X]
    (h : CFSG.Blueprint.LieModel X .Tits 0 2 1) : Nonempty (X ≃* CFSG.Open.quasithinTits) := by
  have hree : CFSG.Blueprint.ReeTitsModel X .Tits 2 1 := by
    rcases h with ⟨hcl, -⟩ | ⟨-, hce, -⟩ | ⟨-, -, hree⟩ | ⟨-, hsz, -⟩
    · exact absurd hcl (by decide)
    · exact absurd hce (by decide)
    · exact hree
    · exact absurd hsz (by decide)
  obtain ⟨e⟩ := titsModelEquiv X 2 1 hree
  exact ⟨e.trans quasithinTitsEquivD.symm⟩

end CFSG.Quasithin
