module

public import CFSG.ClassicalInvolution.Balance.BootstrapBootTriple
import CFSG.ClassicalInvolution.ModelFacts.ClauseZero

public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.DeltaClosure

section FixedPoint

variable {G : Type*} [Group G]

theorem exists_conj_fixed_of_isPGroup {A N : Subgroup G} (hA : IsPGroup 2 A)
    (hN : Odd (Nat.card N)) (hAN : ∀ x ∈ A, ∀ n ∈ N, x * n * x⁻¹ ∈ N) {z : G} (hz : z * z = 1)
    (hzN : ∀ n ∈ N, z * n * z⁻¹ ∈ N) (hzA : ∀ x ∈ A, z * (x * z * x⁻¹) ∈ N) :
    ∃ n ∈ N, ∀ x ∈ A, x * (n * z * n⁻¹) * x⁻¹ = n * z * n⁻¹ := by
  classical
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  set S : Set G := {u | u * u = 1 ∧ z * u ∈ N} with hS
  let _ : MulAction N G := MulAction.compHom G (ConjAct.toConjAct.toMonoidHom.comp N.subtype)
  have hsmul : ∀ (o : N) (g : G), o • g = (o : G) * g * (o : G)⁻¹ := fun o g => by
    show ConjAct.toConjAct (o : G) • g = _
    rw [ConjAct.smul_def]
    rfl
  have hSorb : S = MulAction.orbit N z := by
    ext u
    constructor
    · rintro ⟨hu, hzu⟩
      obtain ⟨o, ho, hzo⟩ := exists_conj_of_mul_mem hu hz hN hzu
      refine ⟨⟨o⁻¹, N.inv_mem ho⟩, ?_⟩
      show (⟨o⁻¹, N.inv_mem ho⟩ : N) • z = u
      rw [hsmul]
      show o⁻¹ * z * o⁻¹⁻¹ = u
      rw [hzo]
      group
    · rintro ⟨o, rfl⟩
      show o • z ∈ S
      rw [hsmul]
      refine ⟨?_, ?_⟩
      · calc _ = (o : G) * (z * z) * (o : G)⁻¹ := by group
          _ = 1 := by rw [hz]; group
      · have h1 := N.mul_mem (hzN o o.2) (N.inv_mem o.2)
        have e : z * ((o : G) * z * (o : G)⁻¹) = z * (o : G) * z⁻¹ * (o : G)⁻¹ := by
          rw [hzinv]
          group
        rw [e]
        exact h1
  have hodd : ¬ 2 ∣ Nat.card S := by
    rw [hSorb, Nat.card_coe_set_eq, ← MulAction.index_stabilizer N z]
    have hd : (MulAction.stabilizer N z).index ∣ Nat.card N := Subgroup.index_dvd_card _
    intro h2
    exact (Nat.not_even_iff_odd.mpr hN) (even_iff_two_dvd.mpr (h2.trans hd))
  have hAS : ∀ x ∈ A, ∀ u ∈ S, x * u * x⁻¹ ∈ S := by
    rintro x hx u ⟨hu, hzu⟩
    refine ⟨?_, ?_⟩
    · calc _ = x * (u * u) * x⁻¹ := by group
        _ = 1 := by rw [hu]; group
    · have hw := N.mul_mem (hzA x hx) (hAN x hx _ hzu)
      have e : z * (x * u * x⁻¹) = z * (x * z * x⁻¹) * (x * (z * u) * x⁻¹) := by
        calc z * (x * u * x⁻¹) = z * (x * (z * (z * u)) * x⁻¹) := by
              rw [← mul_assoc z z u, hz, one_mul]
          _ = _ := by group
      rw [e]
      exact hw
  let _ : MulAction A S :=
    { smul := fun x u => ⟨(x : G) * u * (x : G)⁻¹, hAS x x.2 u u.2⟩
      one_smul := fun u => Subtype.ext
        (show ((1 : A) : G) * (u : G) * ((1 : A) : G)⁻¹ = u by simp)
      mul_smul := fun x y u => Subtype.ext
        (show ((x * y : A) : G) * (u : G) * ((x * y : A) : G)⁻¹ =
          (x : G) * ((y : G) * (u : G) * (y : G)⁻¹) * (x : G)⁻¹ by simp [mul_assoc]) }
  obtain ⟨u, hu⟩ := hA.nonempty_fixed_point_of_prime_not_dvd_card S hodd
  have hu' : (u : G) ∈ MulAction.orbit N z := hSorb ▸ u.2
  obtain ⟨o, ho⟩ := hu'
  have ho' : o • z = (u : G) := ho
  rw [hsmul] at ho'
  refine ⟨o, o.2, fun x hx => ?_⟩
  rw [ho']
  exact congrArg Subtype.val (MulAction.mem_fixedPoints.mp hu ⟨x, hx⟩)

end FixedPoint

section Lemmas

open scoped commutatorElement

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem members_eq_or_commute {L L' : Subgroup G} {w : G} (hL : IsClassicalMember p f L w)
    (hL' : IsClassicalMember p f L' w) (hqL : CFSG.Open.IsQuasisimple L)
    (hqL' : CFSG.Open.IsQuasisimple L') : L = L' ∨ Commutes L L' := by
  have hc : CFSG.Assembly.IsComponentOf L (Subgroup.centralizer ({w} : Set G)) :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isComponentOf_iff_open _ _).mpr
      ⟨isSubnormal_le hL.subnormal, hL.subnormal, hqL⟩
  have hc' : CFSG.Assembly.IsComponentOf L' (Subgroup.centralizer ({w} : Set G)) :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isComponentOf_iff_open _ _).mpr
      ⟨isSubnormal_le hL'.subnormal, hL'.subnormal, hqL'⟩
  rcases CFSG.LocalAnalysis.ComponentInitial.isComponentOf_eq_or_commute hc hc' with h | h
  · exact Or.inl h
  · refine Or.inr fun x hx y hy => ?_
    have h1 : ⁅x, y⁆ ∈ ⁅L, L'⁆ := Subgroup.commutator_mem_commutator hx hy
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1

omit [Finite G] in
theorem isQuasisimple_of_mem_exactMembers (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω)
    (hex : ExactMembers Ω) {L : Subgroup G} (hL : L ∈ Ω) : CFSG.Open.IsQuasisimple L := by
  obtain ⟨z, hz⟩ := hΩ.classical L hL
  obtain ⟨e⟩ := hz.nonempty_equiv_sl2 (hex L hL)
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  have h4 : 4 ≤ Nat.card (GaloisField p f) := by
    rw [GaloisField.card p f hf]
    omega
  exact CFSG.ComponentClassification.Components.quasisimple_of_equiv e
    (isQuasisimple_specialLinearGroup_two h4)

omit [Finite G] in
theorem oddQuotMk_eq_one_of_mem_oddCoreIn {a n : G}
    (hn : n ∈ oddCoreIn (Subgroup.centralizer ({a} : Set G)))
    (hnC : n ∈ Subgroup.centralizer ({a} : Set G)) : oddQuotMk a ⟨n, hnC⟩ = 1 := by
  obtain ⟨n', hn', hn'e⟩ := hn
  have : n' = ⟨n, hnC⟩ := Subtype.ext hn'e
  rw [← this]
  exact oddQuotMk_eq_one_iff.mpr hn'

omit [Finite G] in
theorem oddQuotMk_centralizes_of_closure {a : G} {L : Subgroup (OddQuot a)} {𝒵 : Set G}
    (h𝒵 : ∀ z ∈ 𝒵, ∃ hzC : z ∈ Subgroup.centralizer ({a} : Set G),
      ∀ y ∈ L, oddQuotMk a ⟨z, hzC⟩ * y = y * oddQuotMk a ⟨z, hzC⟩)
    {g : G} (hg : g ∈ Subgroup.closure 𝒵) (hgC : g ∈ Subgroup.centralizer ({a} : Set G))
    (y : OddQuot a) (hy : y ∈ L) :
    oddQuotMk a ⟨g, hgC⟩ * y = y * oddQuotMk a ⟨g, hgC⟩ := by
  let Q : Subgroup ↥(Subgroup.centralizer ({a} : Set G)) :=
    (Subgroup.centralizer ((L : Subgroup (OddQuot a)) : Set (OddQuot a))).comap (oddQuotMk a)
  have hsub : Subgroup.closure 𝒵 ≤ Q.map (Subgroup.centralizer ({a} : Set G)).subtype := by
    refine (Subgroup.closure_le _).mpr ?_
    intro z hz
    obtain ⟨hzC, hcomm⟩ := h𝒵 z hz
    refine ⟨⟨z, hzC⟩, ?_, rfl⟩
    show oddQuotMk a _ ∈ Subgroup.centralizer ((L : Subgroup (OddQuot a)) : Set (OddQuot a))
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (hcomm y hy).symm
  obtain ⟨q, hq, hqg⟩ := hsub hg
  have hqe : q = ⟨g, hgC⟩ := Subtype.ext hqg
  subst hqe
  exact (Subgroup.mem_centralizer_iff.mp hq y hy).symm

end Lemmas

section Main

open scoped commutatorElement

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem exists_centralized_component_of_not_inCommonComponent (hp2 : p ≠ 2) (hΩ : InClass p f Ω)
    (hIH : LocalLieSystems p f Ω) {A : Subgroup G}
    (hM : MemberFamily p f Ω A (frameFamily p f Ω A)) {a : G} (ha : a ∈ A)
    (hnc : ¬ ({a} : Set G) ⊆ Subgroup.center G) {K : Subgroup G} (hK : K ∈ centMembers Ω a)
    (hKL : ∀ L ∈ frameFamily p f Ω A, ¬ InCommonComponent a K L) :
    ∃ Q : Subgroup (OddQuot a), CFSG.IsComponent Q ∧ modOdd a K ≤ Q ∧
      ∀ x, x ∈ A → ∀ (hxC : x ∈ Subgroup.centralizer ({a} : Set G)), ∀ y ∈ Q,
        oddQuotMk a ⟨x, hxC⟩ * y = y * oddQuotMk a ⟨x, hxC⟩ := by
  classical
  have hnorm : (memberJoin Ω a).Normal := memberJoin_normal hΩ.conjInvariant
  obtain ⟨D⟩ := lieDecomposition_memberImages hp2 ModelFacts.modelClauseZero
    fundamentalWholeA1 hΩ hIH hnc
  obtain ⟨i, hi⟩ := D.exists_le _ (⟨K, hK, rfl⟩ : modOdd a K ∈ memberImages Ω a)
  have hQi : CFSG.IsComponent (D.Q i) := (CFSG.isComponent_iff_open _).mpr (D.isComponentOf i)
  have hcom : ∀ {x y : G}, x ∈ A → y ∈ A → x * y = y * x := fun hx hy =>
    congrArg Subtype.val (hM.elem.1.is_comm.comm (⟨_, hx⟩ : A) ⟨_, hy⟩)
  have hAC : ∀ {x : G}, x ∈ A → x ∈ Subgroup.centralizer ({a} : Set G) := fun hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hcom hx ha)
  have hFC : ∀ {L : Subgroup G}, L ∈ frameFamily p f Ω A →
      L ≤ Subgroup.centralizer ({a} : Set G) := fun hL =>
    hL.2.1.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr ha))
  refine ⟨D.Q i, hQi, hi, ?_⟩
  intro g hg hgC y hy
  refine oddQuotMk_centralizes_of_closure
    (𝒵 := {z | ∃ L ∈ frameFamily p f Ω A, IsClassicalMember p f L z}) ?_ ?_ hgC y hy
  · rintro z ⟨L, hL, hz⟩
    have hzA := hM.mem_of_isClassicalMember hL hz
    refine ⟨hAC hzA, fun y hy => ?_⟩
    obtain ⟨j, hj⟩ := D.exists_le _
      (⟨L, ⟨hL.1, hFC hL⟩, rfl⟩ : modOdd a L ∈ memberImages Ω a)
    have hne : i ≠ j := by
      rintro rfl
      exact hKL L hL ⟨D.Q i, hQi, hi, hj⟩
    exact (D.commute i j hne y hy _ (hj (oddQuotMk_mem_modOdd hz.mem (hAC hzA)))).symm
  · rw [← hM.generate]
    exact hg


end Main

end CFSG.ClassicalInvolution.Balance.Bootstrap
