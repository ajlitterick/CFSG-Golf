module

public import CFSG.ClassicalInvolution.Balance.BootstrapBootTriple
public import CFSG.ClassicalInvolution.Balance.QNineStage
import CFSG.ClassicalInvolution.ModelFacts.ClauseZero

public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure

section Component

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {a : G}

theorem component_le_modOdd_of_hgen {A : Subgroup G} (hA : IsElemAbelian 2 A)
    (hcard : Nat.card A = 8) (haA : a ∈ A) (ha1 : a ≠ 1) (hAY : A ≤ centLayer Ω a)
    {Q : Subgroup (OddQuot a)} (hQJ : Q ≤ memberJoin Ω a)
    (hgen : ∀ F' ∈ signalizerFunctorEk 2 2 A,
      (∀ x ∈ modOdd a F', x ≠ 1 → ¬ ∀ y ∈ Q, x * y = y * x) →
        Q ≤ ⨆ g ∈ modOdd a F', ⨆ (_ : g ≠ 1),
          memberJoin Ω a ⊓ Subgroup.centralizer ({g} : Set (OddQuot a))) :
    Q ≤ modOdd a (⨆ F ∈ signalizerFunctorEk 2 2 A,
      (Subgroup.centralizer (F : Set G) ⊓ centLayer Ω a)) := by
  classical
  set C : Subgroup G := Subgroup.centralizer ({a} : Set G) with hC
  set Y : Subgroup G := centLayer Ω a with hY
  set J : Subgroup G := ⨆ F ∈ signalizerFunctorEk 2 2 A,
    (Subgroup.centralizer (F : Set G) ⊓ Y) with hJ
  have hA2 : ∀ x ∈ A, x * x = 1 := fun x hx => by
    rw [← pow_two]
    exact hA.2 x hx
  have hAC : A ≤ C := fun e he => Subgroup.mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (hA.1.is_comm.comm (⟨e, he⟩ : A) ⟨a, haA⟩))
  have haC : a ∈ C := hAC haA
  have hJmem : ∀ (F : Subgroup G), F ∈ signalizerFunctorEk 2 2 A → ∀ (y : G),
      y ∈ Subgroup.centralizer (F : Set G) → y ∈ Y → y ∈ J := fun F hF y hyF hyY =>
    (le_iSup₂ (f := fun (F : Subgroup G) (_ : F ∈ signalizerFunctorEk 2 2 A) =>
      Subgroup.centralizer (F : Set G) ⊓ Y) F hF) ⟨hyF, hyY⟩
  set Z : Subgroup G := A ⊓ ((Subgroup.centralizer (Q : Set (OddQuot a))).comap
    (oddQuotMk a)).map C.subtype with hZ
  have hZmem : ∀ x : ↥C, (x : G) ∈ A → oddQuotMk a x ∈ Subgroup.centralizer (Q : Set (OddQuot a)) →
      (x : G) ∈ Z := fun x hxA hx => ⟨hxA, ⟨x, hx, rfl⟩⟩
  have hZcent : ∀ (g : G) (hgC : g ∈ C), g ∈ Z → ∀ y ∈ Q,
      oddQuotMk a ⟨g, hgC⟩ * y = y * oddQuotMk a ⟨g, hgC⟩ := by
    rintro g hgC ⟨-, ⟨c, hc, rfl⟩⟩ y hy
    exact (Subgroup.mem_centralizer_iff.mp hc y hy).symm
  by_cases hF : ∃ F ∈ signalizerFunctorEk 2 2 A, F ≤ Z
  ·
    obtain ⟨F, hFE, hFZ⟩ := hF
    intro q hq
    obtain ⟨y, hyC, hyY, hyF, hyq⟩ := exists_lift_centralizer (E := F)
      (fun e he => hA2 e (hFE.1 he)) (hFE.1.trans hAY) (hQJ hq)
      (fun e he heC => hZcent e heC (hFZ he) q hq)
    exact ⟨⟨y, hyC⟩, hJmem F hFE y hyF hyY, hyq⟩
  ·
    obtain ⟨F', hF'E, hF'Z⟩ := exists_four_subgroup_inf_eq_bot hA hcard inf_le_left hF
    have hF'A : F' ≤ A := hF'E.1
    have hF'2 : ∀ x ∈ F', x * x = 1 := fun x hx => hA2 x (hF'A hx)
    have hfaith : ∀ x ∈ modOdd a F', x ≠ 1 → ¬ ∀ y ∈ Q, x * y = y * x := by
      intro x hx hx1 hcomm
      obtain ⟨k, hk, rfl⟩ := mem_modOdd_iff.mp hx
      have hkZ : (k : G) ∈ Z := hZmem k (hF'A hk)
        (Subgroup.mem_centralizer_iff.mpr fun y hy => (hcomm y hy).symm)
      have hk1 : (k : G) ∈ F' ⊓ Z := ⟨hk, hkZ⟩
      rw [hF'Z, Subgroup.mem_bot] at hk1
      exact hx1 (by rw [show k = 1 from Subtype.ext hk1, map_one])
    have hKG := hgen F' hF'E hfaith
    refine hKG.trans (iSup₂_le fun x hx => iSup_le fun hx1 => ?_)
    obtain ⟨k, hk, rfl⟩ := mem_modOdd_iff.mp hx
    have hkF' : (k : G) ∈ F' := hk
    have hk1 : (k : G) ≠ 1 := fun h => hx1 (by rw [show k = 1 from Subtype.ext h, map_one])
    have hka : (k : G) ≠ a := by
      intro h
      refine hfaith _ hx hx1 fun y _ => ?_
      have : k = ⟨a, haC⟩ := Subtype.ext h
      rw [this]
      exact oddQuotMk_central haC y
    have hkA : (k : G) ∈ A := hF'A hkF'
    have hcomm : a * (k : G) = (k : G) * a :=
      congrArg Subtype.val (hA.1.is_comm.comm (⟨a, haA⟩ : A) ⟨k, hkA⟩)
    have hE4 : Nat.card (Subgroup.closure ({a, (k : G)} : Set G)) = 4 :=
      card_closure_pair_eq_four (hA2 a haA) (hA2 _ hkA) ha1 hk1 (Ne.symm hka) hcomm
    have hEA : Subgroup.closure ({a, (k : G)} : Set G) ≤ A := by
      rw [Subgroup.closure_le]
      rintro z (rfl | rfl)
      exacts [haA, hkA]
    have hEmem : Subgroup.closure ({a, (k : G)} : Set G) ∈ signalizerFunctorEk 2 2 A :=
      ⟨hEA, by rw [hE4]; norm_num⟩
    rintro q ⟨hqJ, hqk⟩
    have hkq : oddQuotMk a k * q = q * oddQuotMk a k :=
      (Subgroup.mem_centralizer_singleton_iff.mp hqk).symm
    obtain ⟨y, hyC, hyY, hyk, hyq⟩ := exists_lift_centralizer (E := Subgroup.zpowers (k : G))
      (fun e he => by
        rcases mem_zpowers_involution (hF'2 _ hkF') he with rfl | rfl
        exacts [one_mul 1, hF'2 _ hkF'])
      (Subgroup.zpowers_le.mpr (hAY hkA)) hqJ
      (fun e he heC => by
        rcases mem_zpowers_involution (hF'2 _ hkF') he with rfl | rfl
        · change oddQuotMk a 1 * q = q * oddQuotMk a 1
          rw [map_one, one_mul, mul_one]
        · exact hkq)
    have hyE : y ∈ Subgroup.centralizer
        ((Subgroup.closure ({a, (k : G)} : Set G) : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have hsub : ({a, (k : G)} : Set G) ⊆
          ((Subgroup.centralizer ({y} : Set G) : Subgroup G) : Set G) := by
        rintro z (rfl | rfl)
        · exact Subgroup.mem_centralizer_singleton_iff.mpr
            (Subgroup.mem_centralizer_singleton_iff.mp hyC).symm
        · exact Subgroup.mem_centralizer_singleton_iff.mpr
            (Subgroup.mem_centralizer_iff.mp hyk _ (Subgroup.mem_zpowers _))
      exact Subgroup.mem_centralizer_singleton_iff.mp ((Subgroup.closure_le _).mpr hsub hx)
    exact ⟨⟨y, hyC⟩, hJmem _ hEmem y hyE hyY, hyq⟩

end Component

section Main

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {a : G}

theorem centralizerGenerationModOTwo_of_components (hΩc : ConjInvariant Ω) {A : Subgroup G}
    (hA : IsElemAbelian 2 A) (hcard : Nat.card A = 8) (haA : a ∈ A) (ha1 : a ≠ 1)
    (hAY : A ≤ centLayer Ω a) (D : LieDecomposition (memberImages Ω a) (memberJoin Ω a))
    (hgen : ∀ i, ∀ F' ∈ signalizerFunctorEk 2 2 A,
      (∀ x ∈ modOdd a F', x ≠ 1 → ¬ ∀ y ∈ D.Q i, x * y = y * x) →
        D.Q i ≤ ⨆ g ∈ modOdd a F', ⨆ (_ : g ≠ 1),
          memberJoin Ω a ⊓ Subgroup.centralizer ({g} : Set (OddQuot a))) :
    CentralizerGenerationModOTwo Ω A a := by
  classical
  set J : Subgroup G := ⨆ F ∈ signalizerFunctorEk 2 2 A,
    (Subgroup.centralizer (F : Set G) ⊓ centLayer Ω a) with hJ
  have hQ : ∀ i, D.Q i ≤ modOdd a J := fun i =>
    component_le_modOdd_of_hgen hA hcard haA ha1 hAY (D.le_join i) (hgen i)
  have hJY : J ≤ centLayer Ω a := iSup₂_le fun _ _ => inf_le_right
  show centLayer Ω a ≤ oddCoreIn (centLayer Ω a) ⊔ J
  intro y hy
  have hyC : y ∈ Subgroup.centralizer ({a} : Set G) := centLayer_le_centralizer Ω a hy
  have hyJ := oddQuotMk_mem_memberJoin hy hyC
  rw [← D.iSup_eq] at hyJ
  obtain ⟨k, hkJ, hk⟩ := mem_modOdd_iff.mp ((iSup_le hQ) hyJ)
  have hkY : (k : G) ∈ centLayer Ω a := hJY hkJ
  have hker : (⟨k, hkY⟩ : ↥(centLayer Ω a))⁻¹ * ⟨y, hy⟩ ∈ (layerToOddQuot Ω a).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, layerToOddQuot_apply, layerToOddQuot_apply]
    change (oddQuotMk a k)⁻¹ * oddQuotMk a ⟨y, hyC⟩ = 1
    rw [hk, inv_mul_cancel]
  rw [ker_layerToOddQuot hΩc] at hker
  have hodd : (k : G)⁻¹ * y ∈ oddCoreIn (centLayer Ω a) := ⟨_, hker, rfl⟩
  have hmem : (k : G) * ((k : G)⁻¹ * y) ∈ J ⊔ oddCoreIn (centLayer Ω a) :=
    Subgroup.mul_mem_sup hkJ hodd
  rwa [mul_inv_cancel_left, sup_comm] at hmem

end Main

section Stage2


end Stage2

end CFSG.ClassicalInvolution.Balance.Bootstrap
