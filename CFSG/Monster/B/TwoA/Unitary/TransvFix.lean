module

public meta import CFSG.Monster.B.TwoA.Unitary.Action
public meta import CFSG.Monster.B.Co2.Data
public meta import CFSG.Monster.B.TwoA.Unitary.NData
public meta import CFSG.Monster.B.TwoA.Unitary.Orbit1408Data
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Data
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Matrix
public import Certificates.Certificate3081

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Unitary

open CFSG.Monster CFSG.Monster.B.Short CFSG.Monster.B.Co2 CFSG.Monster.B.TwoA

attribute [local irreducible] Native.vectors

theorem ncard_fix_range {n : ℕ} {f : Fin n → Wv v0} (hf : Function.Injective f) (k : Kstab v0)
    (p : Fin n → Prop) [DecidablePred p] (hp : ∀ j, wAct v0 k (f j) = f j ↔ p j) :
    {x | x ∈ Set.range f ∧ wAct v0 k x = x}.ncard = (Finset.univ.filter p).card := by
  have e : {x | x ∈ Set.range f ∧ wAct v0 k x = x} = f '' {j | p j} := by
    ext x
    constructor
    · rintro ⟨⟨j, rfl⟩, h⟩
      exact ⟨j, (hp j).1 h, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨⟨j, rfl⟩, (hp j).2 hj⟩
  rw [e, Set.ncard_image_of_injective _ hf, ← Set.ncard_coe_finset, Finset.coe_filter_univ]

theorem wAct_genK_decW_eq_iff
    (k : Fin 17) {c : ℕ} (hc : c < 2 ^ 22)
    (h : Native.actD 22 (genRows k) c < 2 ^ 22) :
    wAct v0 (genK k) (decW c) = decW c ↔ Native.actD 22 (genRows k) c = c := by
  rw [wAct_genK_decW]
  exact ⟨fun e => decW_injective h hc e, fun e => by rw [e]⟩

theorem fixOmega_lt :
    ∀ j : Ω, Native.actD 22 (genRows 6) (shortVec j) < 2 ^ 22 :=
  Certificates.certificate3081.1

theorem fixOmega_card :
    (Finset.univ.filter fun j : Ω => Native.actD 22 (genRows 6) (shortVec j) = shortVec j).card =
      284 :=
  Certificates.certificate3081.2.1


theorem ncard_fix_OmegaW :
    {x | x ∈ OmegaW ∧ wAct v0 (genK 6) x = x}.ncard = 284 := by
  rw [OmegaW_eq, ncard_fix_range wvec_injective (genK 6)
    (fun j : Ω => Native.actD 22 (genRows 6) (shortVec j) = shortVec j)
    (fun j => wAct_genK_decW_eq_iff 6 (shortVec_lt j) (fixOmega_lt j)), fixOmega_card]


theorem genRows_six_tau : Native.actD 22 (genRows 6) 60 = 60 := by decide +kernel

theorem wAct_genK_six_tauW :
    wAct v0 (genK 6) tauW = tauW := by
  rw [tauW, o14Tau, wAct_genK_decW, genRows_six_tau]

theorem tauWit_ok : Native.actD 22 (genRows 0) (Native.actD 22 (genRows 3) 1919652) = 60 ∧
    Native.actD 22 (genRows 6) 1919652 ≠ 1919652 ∧
    Native.actD 22 (genRows 6) 1919652 < 2 ^ 22 := by
  decide +kernel

theorem wAct_genK_three_zero_wit :
    wAct v0 (genK 0) (wAct v0 (genK 3) (decW 1919652)) = tauW := by
  rw [wAct_genK_decW, wAct_genK_decW, tauWit_ok.1]
  rfl

theorem wAct_genK_six_wit_ne :
    wAct v0 (genK 6) (decW 1919652) ≠ decW 1919652 := by
  rw [wAct_genK_decW]
  exact fun h => tauWit_ok.2.1 (decW_injective tauWit_ok.2.2 (by norm_num) h)

end CFSG.Monster.B.TwoA.Unitary
