module

public import CFSG.LocalAnalysis.AGLEmbedding.EscapeTwoCore
public import CFSG.LocalAnalysis.ComponentClassification.LocalComponents
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConj

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem isPGroup_iSup_of_pairwise_commute {p : ℕ} [Fact p.Prime] {ι : Type*} [Finite ι]
    (A : ι → Subgroup G) (hA : ∀ i, IsPGroup p (A i))
    (hc : Pairwise fun i j => ⁅A i, A j⁆ = ⊥) : IsPGroup p (⨆ i, A i : Subgroup G) := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  have key : ∀ s : Finset ι, IsPGroup p (⨆ i ∈ s, A i : Subgroup G) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      rw [show (⨆ i ∈ (∅ : Finset ι), A i : Subgroup G) = ⊥ by simp]
      exact IsPGroup.of_bot
    | insert a s ha ih =>
      rw [Finset.iSup_insert]
      refine (hA a).to_sup_of_normal_right' ih
        (le_trans ?_ (Subgroup.centralizer_le_normalizer _))
      rw [Subgroup.le_centralizer_iff]
      exact iSup₂_le fun i hi =>
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hc fun h => ha (h ▸ hi))
  have hall := key Finset.univ
  rwa [show (⨆ i ∈ (Finset.univ : Finset ι), A i : Subgroup G) = ⨆ i, A i by simp] at hall


omit [Finite G] in
theorem map_conj_mul_eq (H : Subgroup G) (a b : G) :
    H.map (MulAut.conj (a * b)).toMonoidHom =
      (H.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [mul_assoc]

omit [Finite G] in
theorem le_normalizer_of_forall_map_conj_le {K W : Subgroup G}
    (h : ∀ g ∈ K, W.map (MulAut.conj g).toMonoidHom ≤ W) :
    K ≤ Subgroup.normalizer (W : Set G) := fun g hg =>
  Subgroup.mem_normalizer_iff.mpr fun x =>
    ⟨fun hx => h g hg ⟨x, hx, rfl⟩, fun hx => by
      simpa [mul_assoc] using h g⁻¹ (K.inv_mem hg) ⟨_, hx, rfl⟩⟩

omit [Finite G] in
theorem map_conj_eq_of_map_conj_eq {K L U : Subgroup G}
    (hNU : K ⊓ Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (U : Set G)) {k k' : G}
    (hk : k ∈ K) (hk' : k' ∈ K)
    (hL : L.map (MulAut.conj k).toMonoidHom = L.map (MulAut.conj k').toMonoidHom) :
    U.map (MulAut.conj k).toMonoidHom = U.map (MulAut.conj k').toMonoidHom := by
  have hL' : L.map (MulAut.conj (k⁻¹ * k')).toMonoidHom = L := by
    rw [map_conj_mul_eq, ← hL, ← map_conj_mul_eq, inv_mul_cancel]
    ext x
    simp
  have hU : U.map (MulAut.conj (k⁻¹ * k')).toMonoidHom = U :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (hNU ⟨K.mul_mem (K.inv_mem hk) hk', Subgroup.mem_normalizer_iff_map_conj_eq.mpr hL'⟩)
  rw [← mul_inv_cancel_left k k', map_conj_mul_eq U k, hU]


theorem le_commutator_sup_inf_centralizer_of_coprime {R A : Subgroup G}
    (hAR : A ≤ Subgroup.normalizer (R : Set G)) (hcop : Nat.Coprime (Nat.card A) (Nat.card R))
    (hsolv : Group.IsSolvable R) :
    R ≤ ⁅R, A⁆ ⊔ R ⊓ Subgroup.centralizer (A : Set G) := by
  have : Subgroup.Normalizes A R := ⟨hAR⟩
  have hsup := CFSG.fixedPointSubgroup_sup_commutatorAction_eq_top_of_solvable_coprime
    (G := R) (A := A) hsolv hcop
  have hfix : CFSG.fixedPointSubgroup A R = (CFSG.subgroupCentralizerIn R A).subgroupOf R :=
    CFSG.fixedPointSubgroup_subgroup_conj_eq_subgroupCentralizerIn R A hAR
  intro x hx
  have h1 : (⟨x, hx⟩ : R) ∈ CFSG.fixedPointSubgroup A R ⊔ CFSG.commutatorAction A R := by
    rw [hsup]
    exact Subgroup.mem_top _
  have h2 := Subgroup.mem_map_of_mem R.subtype h1
  rw [Subgroup.map_sup, CFSG.commutatorAction_subgroup_conj_map_eq_commutator R A hAR, hfix,
    CFSG.subgroupCentralizerIn, Subgroup.map_subgroupOf_eq_of_le inf_le_left] at h2
  rw [sup_comm]
  exact h2

theorem normalClosure_le_normalizer_of_isComponentOf {L : Subgroup G} (hL : IsComponentOf L ⊤) :
    Subgroup.normalClosure (L : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  refine Subgroup.closure_le _ |>.mpr fun y hy => ?_
  obtain ⟨l, hl, hc⟩ := Group.mem_conjugatesOfSet_iff.mp hy
  obtain ⟨c, rfl⟩ := isConj_iff.mp hc
  have hmem : c * l * c⁻¹ ∈ L.map (MulAut.conj c).toMonoidHom := ⟨l, hl, rfl⟩
  by_cases heq : L.map (MulAut.conj c).toMonoidHom = L
  · exact Subgroup.le_normalizer (heq ▸ hmem)
  · refine Subgroup.centralizer_le_normalizer _ (Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (ComponentClassification.LocalComponents.commute_of_ne _ L
        ((ComponentClassification.LocalComponents.equiv_iff (MulAut.conj c) L).mpr hL) hL heq)
      hmem)

theorem mem_normalizer_of_commute_of_isComponentOf {L : Subgroup G} (hL : IsComponentOf L ⊤)
    {x s : G} (hxL : x ∈ L) (hxZ : x ∉ Subgroup.centralizer (L : Set G)) (hs : s * x = x * s) :
    s ∈ Subgroup.normalizer (L : Set G) := by
  refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_
  by_contra hne
  have hxs : x ∈ L.map (MulAut.conj s).toMonoidHom :=
    ⟨x, hxL, by simp [MulAut.conj_apply, hs, mul_assoc]⟩
  exact hxZ (Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    (ComponentClassification.LocalComponents.commute_of_ne _ L
      ((ComponentClassification.LocalComponents.equiv_iff (MulAut.conj s) L).mpr hL) hL hne) hxs)

theorem le_normalizer_of_odd_mem_component {L S : Subgroup G} (hL : IsComponentOf L ⊤)
    (hS : IsPGroup 2 S) {x : G} (hxL : x ∈ L) (hxZ : x ∉ Subgroup.centralizer (L : Set G))
    (hxS : x ∈ Subgroup.normalizer (S : Set G)) (hx : Odd (orderOf x)) :
    S ≤ Subgroup.normalizer (L : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent S := hS.isNilpotent
  have hcop : Nat.Coprime (Nat.card (Subgroup.zpowers x)) (Nat.card S) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hS
    rw [Nat.card_zpowers, hn]
    exact Nat.Coprime.pow_right n (Nat.coprime_two_right.mpr hx)
  refine (le_commutator_sup_inf_centralizer_of_coprime (Subgroup.zpowers_le.mpr hxS) hcop
    inferInstance).trans (sup_le ?_ fun s hs => ?_)
  · have hxE : Subgroup.zpowers x ≤ Subgroup.normalClosure (L : Set G) :=
      Subgroup.zpowers_le.mpr (Subgroup.subset_normalClosure hxL)
    exact ((Subgroup.commutator_mono le_rfl hxE).trans (Subgroup.commutator_le_right _ _)).trans
      (normalClosure_le_normalizer_of_isComponentOf hL)
  · exact mem_normalizer_of_commute_of_isComponentOf hL hxL hxZ
      (Subgroup.mem_centralizer_iff.mp hs.2 x (Subgroup.mem_zpowers x)).symm

theorem le_normalizer_of_component_quotient {N L S : Subgroup G} [N.Normal] (hNL : N ≤ L)
    (hL : IsComponentOf (L.map (QuotientGroup.mk' N)) ⊤) (hS : IsPGroup 2 S) {x : G}
    (hxL : x ∈ L) (hxS : x ∈ Subgroup.normalizer (S : Set G)) (hx : Odd (orderOf x))
    (hxN : ¬ ⁅Subgroup.zpowers x, L⁆ ≤ N) : S ≤ Subgroup.normalizer (L : Set G) := by
  set f := QuotientGroup.mk' N with hf
  have hxZ : f x ∉ Subgroup.centralizer ((L.map f : Subgroup (G ⧸ N)) : Set (G ⧸ N)) := by
    intro hxC
    apply hxN
    rw [← QuotientGroup.ker_mk' N, ← Subgroup.map_eq_bot_iff, Subgroup.map_commutator,
      MonoidHom.map_zpowers]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (Subgroup.zpowers_le.mpr hxC)
  have hbar := le_normalizer_of_odd_mem_component hL (hS.map f) (Subgroup.mem_map_of_mem f hxL)
    hxZ (Subgroup.le_normalizer_map f (Subgroup.mem_map_of_mem f hxS))
    (Odd.of_dvd_nat hx (orderOf_map_dvd f x))
  have hLf : (L.map f).comap f = L := by
    rw [Subgroup.comap_map_eq, hf, QuotientGroup.ker_mk', sup_of_le_left hNL]
  intro s hs
  have hs' : s ∈ (Subgroup.normalizer ((L.map f : Subgroup (G ⧸ N)) : Set (G ⧸ N))).comap f :=
    hbar (Subgroup.mem_map_of_mem f hs)
  rwa [Subgroup.comap_normalizer_eq_of_surjective _ (QuotientGroup.mk'_surjective N), hLf] at hs'

theorem le_normalizer_of_component {L S : Subgroup G} (hQL : CFSG.pCore 2 G ≤ L)
    (hL : IsComponentOf (L.map (QuotientGroup.mk' (CFSG.pCore 2 G))) ⊤) (hS : IsPGroup 2 S)
    {x : G} (hxL : x ∈ L) (hxS : x ∈ Subgroup.normalizer (S : Set G)) (hx : Odd (orderOf x))
    (hxQ : ¬ ⁅Subgroup.zpowers x, L⁆ ≤ CFSG.pCore 2 G) : S ≤ Subgroup.normalizer (L : Set G) :=
  le_normalizer_of_component_quotient hQL hL hS hxL hxS hx hxQ

end CFSG.AGLEmbedding
