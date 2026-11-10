module

public import CFSG.GH74.QTGen4.DSGen4.LeafWrappers
public import CFSG.Quasithin.EmptyFaithful.S1421QA17Surv10
public import CFSG.GH74.QTGen4.DSGen4.Leaf.FaithfulA5

public section

namespace CFSG.GH74.QTGen4.DSGen4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13
  CFSG.Quasithin.Background.Harris.F112S3Big
open scoped commutatorElement


theorem dsa6_mem_K {G : Type} [Group G] {P L Q : Subgroup G} {p : G} :
    p ∈ dsCentMod P L Q ↔ p ∈ P ∧ p ∈ Subgroup.normalizer (Q : Set G) ∧ ∀ l ∈ L, ⁅p, l⁆ ∈ Q :=
  Iff.rfl

theorem dsa6_K_conj {G : Type} [Group G] {P L Q : Subgroup G}
    (hPL : P ≤ Subgroup.normalizer (L : Set G)) (hPQ : P ≤ Subgroup.normalizer (Q : Set G))
    {p k : G} (hp : p ∈ P) (hk : k ∈ dsCentMod P L Q) : p * k * p⁻¹ ∈ dsCentMod P L Q := by
  rw [dsa6_mem_K] at hk ⊢
  obtain ⟨hkP, hkN, hkc⟩ := hk
  refine ⟨P.mul_mem (P.mul_mem hp hkP) (P.inv_mem hp), ?_, ?_⟩
  · exact (Subgroup.normalizer (Q : Set G)).mul_mem
      ((Subgroup.normalizer (Q : Set G)).mul_mem (hPQ hp) hkN)
      ((Subgroup.normalizer (Q : Set G)).inv_mem (hPQ hp))
  · intro l hl
    have h1 := Subgroup.mem_normalizer_iff.mp (hPL (P.inv_mem hp)) l
    rw [inv_inv] at h1
    have hl' : p⁻¹ * l * p ∈ L := h1.mp hl
    have key : ⁅p * k * p⁻¹, l⁆ = p * ⁅k, p⁻¹ * l * p⁆ * p⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [key]
    exact (Subgroup.mem_normalizer_iff.mp (hPQ hp) _).mp (hkc _ hl')


theorem dsa6_le_K {G : Type} [Group G] {P L Q : Subgroup G} (hLP : L ≤ P) (hQP : Q ≤ P)
    (hPQ : P ≤ Subgroup.normalizer (Q : Set G)) : Q ≤ dsCentMod P L Q := by
  intro q hq
  rw [dsa6_mem_K]
  refine ⟨hQP hq, hPQ (hQP hq), fun l hl => ?_⟩
  have hA : l * q⁻¹ * l⁻¹ ∈ Q :=
    (Subgroup.mem_normalizer_iff.mp (hPQ (hLP hl)) q⁻¹).mp (Q.inv_mem hq)
  have e : ⁅q, l⁆ = q * (l * q⁻¹ * l⁻¹) := by
    rw [commutatorElement_def]
    simp only [mul_assoc]
  rw [e]
  exact Q.mul_mem hq hA

private theorem dsa6_central_perm : ∀ g : Equiv.Perm (Fin 5), Equiv.Perm.sign g = 1 →
    (∀ h : Equiv.Perm (Fin 5), Equiv.Perm.sign h = 1 → g * h = h * g) → g = 1 := by
  decide +kernel

theorem dsa6_central_quot {X : Type} [Group X] (hq : IsL2Quot 2 X) (x : X)
    (hx : ∀ y : X, x * y = y * x) : x = 1 := by
  obtain ⟨ψ⟩ := CFSG.Quasithin.S1421QA17.nonempty_mulEquiv_alt5_of_isL2Quot_two hq
  have hcomm : ∀ h : alternatingGroup (Fin 5), ψ x * h = h * ψ x := by
    intro h
    have := congrArg ψ (hx (ψ.symm h))
    simpa only [map_mul, MulEquiv.apply_symm_apply] using this
  have hψ : ψ x = 1 := by
    apply Subtype.ext
    show ((ψ x : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) = 1
    apply dsa6_central_perm ((ψ x : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5))
      (Equiv.Perm.mem_alternatingGroup.mp (ψ x).2)
    intro h hh
    have := congrArg Subtype.val (hcomm ⟨h, Equiv.Perm.mem_alternatingGroup.mpr hh⟩)
    simpa using this
  have : x = ψ.symm (ψ x) := (ψ.symm_apply_apply x).symm
  rw [this, hψ, map_one]

theorem dsa6_K_inf {G : Type} [Group G] {L Q : Subgroup G} (hq : IsL2Quot 2 (oTwoQuot ↥L))
    (hQL : Q ⊓ L ≤ pCoreOf 2 L) {k : G} (hkL : k ∈ L) (hk : ∀ l ∈ L, ⁅k, l⁆ ∈ Q) :
    k ∈ pCoreOf 2 L := by
  set π : ↥L →* oTwoQuot ↥L := QuotientGroup.mk' (pCore 2 ↥L) with hπ
  have hsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hcen : ∀ y : oTwoQuot ↥L, π ⟨k, hkL⟩ * y = y * π ⟨k, hkL⟩ := by
    intro y
    obtain ⟨l, rfl⟩ := hsurj y
    have hcomm_mem : ⁅(⟨k, hkL⟩ : ↥L), l⁆ ∈ pCore 2 ↥L := by
      rw [F1.mem_pCore_iff_coe]
      have h1 : ((⁅(⟨k, hkL⟩ : ↥L), l⁆ : ↥L) : G) = ⁅k, (l : G)⁆ := by
        simp [commutatorElement_def]
      rw [h1]
      exact hQL ⟨hk _ l.2, L.mul_mem (L.mul_mem (L.mul_mem hkL l.2) (L.inv_mem hkL))
        (L.inv_mem l.2)⟩
    have h1 : π ⁅(⟨k, hkL⟩ : ↥L), l⁆ = 1 := (QuotientGroup.eq_one_iff _).mpr hcomm_mem
    rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    calc π ⟨k, hkL⟩ * π l = (π ⟨k, hkL⟩ * π l * (π ⟨k, hkL⟩)⁻¹ * (π l)⁻¹) * (π l * π ⟨k, hkL⟩) := by
          group
      _ = π l * π ⟨k, hkL⟩ := by rw [h1, one_mul]
  have hx1 : π ⟨k, hkL⟩ = 1 := dsa6_central_quot hq _ hcen
  have hmem : (⟨k, hkL⟩ : ↥L) ∈ pCore 2 ↥L := (QuotientGroup.eq_one_iff _).mp hx1
  exact (F1.mem_pCore_iff_coe _).mp hmem


end CFSG.GH74.QTGen4.DSGen4
