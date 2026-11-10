module

public import CFSG.GroupTheory.PCore.Defs
public import CFSG.LocalAnalysis.ComponentClassification.OddCore
public import CFSG.LocalAnalysis.SignalizerFunctor.InvariantSylowAmbient
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.NoncyclicAbelianPGroup
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section1

public noncomputable section

namespace CFSG.Wreathed.OriginalSylowNormalizerWitness

open scoped Classical Pointwise IsKleinFour
open CFSG.SignalizerFunctor.Helpers

universe u v

variable {G : Type u} [Group G]

@[expose] def ambientOddCore (H : Subgroup G) : Subgroup G :=
  (CFSG.oddCore H).map H.subtype

@[expose] def ambientSylow {ell : ℕ} (H : Subgroup G)
    (P : Sylow ell (CFSG.oddCore H)) : Subgroup G :=
  ((P : Subgroup (CFSG.oddCore H)).map (CFSG.oddCore H).subtype).map H.subtype

theorem ambientOddCore_le (H : Subgroup G) : ambientOddCore H ≤ H :=
  Subgroup.map_subtype_le _

theorem ambientOddCore_odd [Finite G] (H : Subgroup G) :
    Odd (Nat.card (ambientOddCore H)) := by
  rw [ambientOddCore, Subgroup.card_subtype]
  exact CFSG.ComponentClassification.OddCore.odd_card H

theorem ambientOddCore_normalized (H : Subgroup G) :
    H ≤ Subgroup.normalizer (ambientOddCore H : Set G) := by
  apply (Subgroup.normal_subgroupOf_iff_le_normalizer (ambientOddCore_le H)).mp
  change (((CFSG.oddCore H).map H.subtype).comap H.subtype).Normal
  rw [Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
  infer_instance


theorem odd_automorphism_fixed_times_inverted
    {X : Type u} [Group X] [Finite X] (phi : MulAut X)
    (hphi : Function.Involutive phi) (hcop : Nat.Coprime 2 (Nat.card X)) (g : X) :
    ∃ c i : X, phi c = c ∧ phi i = i⁻¹ ∧ g = c * i := by
  let d : X := (phi g)⁻¹ * g
  obtain ⟨i, hi⟩ :=
    (CFSG.GorensteinWalter.sq_bijective_of_coprime_two (G := X) hcop).2 d
  change i ^ 2 = d at hi
  have hpd : phi d = d⁻¹ := by
    dsimp [d]
    rw [map_mul, map_inv, hphi]
    group
  have hpi : phi i = i⁻¹ := by
    apply (CFSG.GorensteinWalter.sq_bijective_of_coprime_two (G := X) hcop).1
    calc
      (phi i) ^ 2 = phi (i ^ 2) := (map_pow phi i 2).symm
      _ = phi d := congrArg phi hi
      _ = d⁻¹ := hpd
      _ = (i⁻¹) ^ 2 := by rw [← hi, inv_pow]
  have hprod : phi g * i ^ 2 = g := by
    rw [hi]
    dsimp [d]
    group
  have hpg : phi g = g * (i⁻¹) ^ 2 := by
    calc
      phi g = (phi g * i ^ 2) * (i⁻¹) ^ 2 := by simp only [pow_two]; group
      _ = g * (i⁻¹) ^ 2 := by rw [hprod]
  refine ⟨g * i⁻¹, i, ?_, hpi, by group⟩
  rw [map_mul, map_inv, hpi, inv_inv, hpg]
  group

theorem inverted_normalizing_fixed_element_commutes
    {X : Type u} [Group X] [Finite X] (phi : MulAut X)
    (hcop : Nat.Coprime 2 (Nat.card X)) (g y : X)
    (hg : phi g = g) (hy : phi y = y⁻¹)
    (hconj : phi (y⁻¹ * g * y) = y⁻¹ * g * y) : Commute g y := by
  have heq : y * g * y⁻¹ = y⁻¹ * g * y := by
    calc
      y * g * y⁻¹ = phi (y⁻¹ * g * y) := by rw [map_mul, map_mul, map_inv, hy, hg]; group
      _ = y⁻¹ * g * y := hconj
  have hconjsq : g * y ^ 2 * g⁻¹ = y ^ 2 := by
    have hsqcomm : y ^ 2 * g = g * y ^ 2 := by
      calc
        y ^ 2 * g = y * (y * g * y⁻¹) * y := by simp only [pow_two]; group
        _ = y * (y⁻¹ * g * y) * y := by rw [heq]
        _ = g * y ^ 2 := by simp only [pow_two]; group
    calc
      g * y ^ 2 * g⁻¹ = y ^ 2 * g * g⁻¹ := by rw [hsqcomm]
      _ = y ^ 2 := by group
  have hconjy : g * y * g⁻¹ = y := by
    apply (CFSG.GorensteinWalter.sq_bijective_of_coprime_two (G := X) hcop).1
    calc
      (g * y * g⁻¹) ^ 2 = g * y ^ 2 * g⁻¹ := by simp only [pow_two]; group
      _ = y ^ 2 := hconjsq
  show g * y = y * g
  calc
    g * y = (g * y * g⁻¹) * g := by group
    _ = y * g := by rw [hconjy]


@[expose] def actionCentralizer {A : Type v} {X : Type u} [Group A] [Group X]
    [MulDistribMulAction A X] (a : A) : Subgroup X :=
  CFSG.fixedPointSubgroup (↥(Subgroup.zpowers a)) X

theorem mem_actionCentralizer {A : Type v} {X : Type u} [Group A] [Group X]
    [MulDistribMulAction A X] {a : A} {g : X} :
    g ∈ actionCentralizer a ↔ a • g = g := by
  constructor
  · intro hg
    exact hg (⟨a, Subgroup.mem_zpowers a⟩ : Subgroup.zpowers a)
  · intro hg z
    exact smul_eq_self_of_mem_zpowers z.property hg

theorem actionCentralizer_invariant {A : Type v} {X : Type u} [CommGroup A] [Group X]
    [MulDistribMulAction A X] (a : A) :
    ∀ s : A, ∀ g ∈ actionCentralizer (X := X) a, s • g ∈ actionCentralizer (X := X) a := by
  intro s g hg
  apply (mem_actionCentralizer (a := a) (g := _)).mpr
  calc
    a • (s • g) = (a * s) • g := (mul_smul a s g).symm
    _ = (s * a) • g := by rw [mul_comm a s]
    _ = s • (a • g) := mul_smul s a g
    _ = s • g := congrArg (s • ·) ((mem_actionCentralizer (a := a) (g := g)).mp hg)

theorem four_group_normalizer_has_second_fixed_element
    {A : Type v} {X : Type u} [CommGroup A] [IsKleinFour A]
    [Group X] [Finite X] [MulDistribMulAction A X]
    (hcop : Nat.Coprime 2 (Nat.card X)) (hNC : NormalizerCondition X)
    (a b : A) (ha : a ≠ 1) (hb : b ≠ 1) (hab : a ≠ b)
    (hF : actionCentralizer (X := X) a ≠ ⊤) :
    ∃ t : A, (t = b ∨ t = a * b) ∧
      ∃ g : X, g ∈ Subgroup.normalizer (actionCentralizer (X := X) a : Set X) ∧
        t • g = g ∧ g ∉ actionCentralizer (X := X) a := by
  let F : Subgroup X := actionCentralizer a
  let N := Subgroup.normalizer (F : Set X)
  have hFN : F < N := hNC F (lt_top_iff_ne_top.mpr hF)
  have hFInv := actionCentralizer_invariant (X := X) a
  have hNInv := normalizer_invariant_of_invariant F hFInv
  let _action := invariantSubgroupAction N hNInv
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Fact (IsPGroup 2 A) := ⟨IsPGroup.of_card (n := 2) (by
    rw [IsKleinFour.card_four]; norm_num)⟩
  have hgen := CFSG.iSup_fixedPointSubgroup_zpowers_eq_top_of_noncyclic_abelian_pGroup_action
    (G := N) (A := A) 2
    (hcop.of_dvd_right (Subgroup.card_subgroup_dvd_card N)) IsKleinFour.not_isCyclic
  have hex : ∃ t : A, t ≠ 1 ∧ t ≠ a ∧
      ¬ (actionCentralizer (X := N) t ≤ F.subgroupOf N) := by
    by_contra hn
    push Not at hn
    have hle : (⨆ (s : A) (_ : s ≠ 1),
        CFSG.fixedPointSubgroup (↥(Subgroup.zpowers s)) N) ≤ F.subgroupOf N := by
      refine iSup₂_le ?_
      intro s hs
      by_cases hsa : s = a
      · subst s
        intro g hg
        change (g : X) ∈ F
        apply (mem_actionCentralizer (a := a) (g := _)).mpr
        exact congrArg (fun z : N => (z : X)) ((mem_actionCentralizer (a := a) (g := g)).mp hg)
      · exact hn s hs hsa
    rw [hgen] at hle
    have hNF : N ≤ F := by
      intro g hg
      exact hle (show (⟨g, hg⟩ : N) ∈ (⊤ : Subgroup N) from Subgroup.mem_top _)
    exact (not_le_of_gt hFN) hNF
  obtain ⟨t, ht1, hta, htle⟩ := hex
  obtain ⟨g, hg, hgf⟩ := IsConcreteLE.not_le_iff_exists.mp htle
  have htb : t = b ∨ t = a * b := by
    by_cases ht : t = b
    · exact Or.inl ht
    · exact Or.inr (IsKleinFour.eq_mul_of_ne_all ha hb hab ht1 hta ht)
  refine ⟨t, htb, (g : X), g.property, ?_, hgf⟩
  exact congrArg (fun z : N => (z : X)) ((mem_actionCentralizer (a := t) (g := g)).mp hg)


theorem four_group_odd_normalizer_centralizing_inverted_witness
    {A : Type v} {X : Type u} [CommGroup A] [IsKleinFour A]
    [Group X] [Finite X] [MulDistribMulAction A X]
    (hcop : Nat.Coprime 2 (Nat.card X)) (hNC : NormalizerCondition X)
    (a b : A) (ha : a ≠ 1) (hb : b ≠ 1) (hab : a ≠ b)
    (hF : actionCentralizer (X := X) a ≠ ⊤) :
    ∃ t : A, (t = b ∨ t = a * b) ∧
      ∃ y : X, y ≠ 1 ∧ a • y = y⁻¹ ∧ t • y = y ∧
        (∀ g ∈ actionCentralizer (X := X) a, Commute y g) ∧
        y ∉ actionCentralizer (X := X) a := by
  let F : Subgroup X := actionCentralizer a
  let N := Subgroup.normalizer (F : Set X)
  obtain ⟨t, ht, g, hgN, htg, hgf⟩ :=
    four_group_normalizer_has_second_fixed_element hcop hNC a b ha hb hab hF
  let R := N ⊓ actionCentralizer (X := X) t
  have hNInv := normalizer_invariant_of_invariant F
    (actionCentralizer_invariant (X := X) a)
  have hRInv : ∀ s : A, ∀ z ∈ R, s • z ∈ R := by
    intro s z hz
    exact ⟨hNInv s z hz.1, actionCentralizer_invariant t s z hz.2⟩
  let _action := invariantSubgroupAction R hRInv
  let phi : MulAut R := MulDistribMulAction.toMulEquiv R a
  have hphi : Function.Involutive phi := by
    intro z
    change a • (a • z) = z
    rw [← mul_smul, IsKleinFour.mul_self, one_smul]
  let gR : R := ⟨g, hgN, (mem_actionCentralizer (a := t) (g := g)).mpr htg⟩
  obtain ⟨c, i, hc, hi, hgci⟩ := odd_automorphism_fixed_times_inverted phi hphi
    (hcop.of_dvd_right (Subgroup.card_subgroup_dvd_card R)) gR
  have hcF : (c : X) ∈ F := by
    apply (mem_actionCentralizer (a := a) (g := _)).mpr
    exact congrArg (fun z : R => (z : X)) hc
  have hiInv : a • (i : X) = (i : X)⁻¹ :=
    congrArg (fun z : R => (z : X)) hi
  have hiNot : (i : X) ∉ F := by
    intro hiF
    apply hgf
    have eqg : g = (c : X) * (i : X) :=
      congrArg (fun z : R => (z : X)) hgci
    rw [eqg]
    exact F.mul_mem hcF hiF
  refine ⟨t, ht, (i : X), ?_, hiInv,
    (mem_actionCentralizer (a := t) (g := _)).mp i.property.2, ?_, hiNot⟩
  · intro hi1
    exact hiNot (hi1 ▸ F.one_mem)
  · intro z hz
    have hconj : (i : X)⁻¹ * z * (i : X) ∈ F :=
      ((Subgroup.mem_normalizer_iff''.mp i.property.1) z).mp hz
    exact (inverted_normalizing_fixed_element_commutes
      (MulDistribMulAction.toMulEquiv X a) hcop z (i : X)
      ((mem_actionCentralizer (a := a) (g := z)).mp hz) hiInv
      ((mem_actionCentralizer (a := a) (g := _)).mp hconj)).symm

theorem four_group_odd_p_group_centralizing_inverted_witness
    {A : Type v} {X : Type u} [Group A] [IsKleinFour A]
    [Group X] [Finite X] [MulDistribMulAction A X]
    {p : ℕ} (hp : p.Prime) (hpodd : Odd p) (hXp : IsPGroup p X)
    (a b : A) (ha : a ≠ 1) (hb : b ≠ 1) (hab : a ≠ b)
    (hF : actionCentralizer (X := X) a ≠ ⊤) :
    ∃ t : A, (t = b ∨ t = a * b) ∧
      ∃ y : X, y ≠ 1 ∧ a • y = y⁻¹ ∧ t • y = y ∧
        (∀ g ∈ actionCentralizer (X := X) a, Commute y g) ∧
        y ∉ actionCentralizer (X := X) a := by
  let : Fact p.Prime := ⟨hp⟩
  let : IsMulCommutative A := IsKleinFour.isMulCommutative
  let : CommGroup A := IsMulCommutative.instCommGroup
  let : Group.IsNilpotent X := hXp.isNilpotent
  obtain ⟨n, hn⟩ := hXp.exists_card_eq
  have hcop : Nat.Coprime 2 (Nat.card X) := by
    rw [hn]
    exact hpodd.pow.coprime_two_left
  exact four_group_odd_normalizer_centralizing_inverted_witness hcop
    Group.normalizerCondition_of_isNilpotent a b ha hb hab hF


theorem four_group_odd_p_group_prime_order_witness
    {A : Type v} {X : Type u} [Group A] [IsKleinFour A]
    [Group X] [Finite X] [MulDistribMulAction A X]
    {p : ℕ} (hp : p.Prime) (hpodd : Odd p) (hXp : IsPGroup p X)
    (a b : A) (ha : a ≠ 1) (hb : b ≠ 1) (hab : a ≠ b)
    (hF : actionCentralizer (X := X) a ≠ ⊤) :
    ∃ t : A, (t = b ∨ t = a * b) ∧
      ∃ y : X, orderOf y = p ∧ a • y = y⁻¹ ∧ t • y = y ∧
        (∀ g ∈ actionCentralizer (X := X) a, Commute y g) := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨t, ht, y, hy1, hya, hyt, hycomm, _⟩ :=
    four_group_odd_p_group_centralizing_inverted_witness hp hpodd hXp a b ha hb hab hF
  let k := orderOf y / p
  refine ⟨t, ht, y ^ k, ?_, ?_, ?_, ?_⟩
  · exact orderOf_pow_orderOf_div (orderOf_pos y).ne' (hXp.dvd_orderOf hy1)
  · rw [smul_pow', hya, inv_pow]
  · rw [smul_pow', hyt]
  · intro g hg
    exact (hycomm g hg).pow_left k

theorem prime_order_inverted_not_in_centralizer
    {G : Type u} [Group G] (x w : G) {p : ℕ} (hp : p.Prime) (hpodd : Odd p)
    (hw : orderOf w = p) (hinv : x * w * x⁻¹ = w⁻¹) :
    w ∉ Subgroup.centralizer ({x} : Set G) := by
  intro hcentral
  have hcomm : Commute x w := Subgroup.mem_centralizer_iff.mp hcentral x (by simp)
  have heq : w = w⁻¹ := hcomm.mul_inv_cancel.symm.trans hinv
  have hsq : w ^ 2 = 1 := by
    rw [pow_two]
    calc
      w * w = w * w⁻¹ := congrArg (w * ·) heq
      _ = 1 := mul_inv_cancel w
  have hdiv : p ∣ 2 := hw ▸ (orderOf_dvd_iff_pow_eq_one.mpr hsq)
  have hpeq : p = 2 := Nat.prime_two.eq_one_or_self_of_dvd p hdiv |>.resolve_left hp.ne_one
  have heven : Even p := by rw [hpeq]; exact ⟨1, rfl⟩
  exact (Nat.not_even_iff_odd.mpr hpodd) heven


theorem original_actionCentralizer_eq (T B : Subgroup G)
    (hTB : T ≤ Subgroup.normalizer (B : Set G)) (a : T) :
    let _action := conjugationAction T B hTB
    actionCentralizer (X := B) a =
      (B ⊓ Subgroup.centralizer ({(a : G)} : Set G)).subgroupOf B := by
  let _action := conjugationAction T B hTB
  ext g
  rw [mem_actionCentralizer]
  change a • g = g ↔ (g : G) ∈ B ⊓ Subgroup.centralizer ({(a : G)} : Set G)
  constructor
  · intro hfix
    refine ⟨g.property, ?_⟩
    apply Subgroup.mem_centralizer_iff.mpr
    intro z hz
    have hz' : z = (a : G) := Set.mem_singleton_iff.mp hz
    subst z
    have hconj : (a : G) * (g : G) * (a : G)⁻¹ = (g : G) :=
      congrArg (fun z : B => (z : G)) hfix
    calc
      (a : G) * (g : G) = ((a : G) * (g : G) * (a : G)⁻¹) * a := by group
      _ = (g : G) * a := by rw [hconj]
  · intro hg
    apply Subtype.ext
    change (a : G) * (g : G) * (a : G)⁻¹ = (g : G)
    have hcomm : Commute (a : G) (g : G) :=
      Subgroup.mem_centralizer_iff.mp hg.2 a (by simp)
    exact hcomm.mul_inv_cancel


noncomputable section

@[expose] def internalProductMap {G : Type u} [Group G] (P U : Subgroup G)
    (hcomm : ∀ p : P, ∀ u : U, Commute (P.subtype p) (U.subtype u)) :
    P × U →* ↥(P ⊔ U) :=
  ((P.subtype.noncommCoprod U.subtype hcomm).codRestrict (P ⊔ U) fun g =>
    Subgroup.mul_mem_sup g.1.property g.2.property)

theorem internalProductMap_injective {G : Type u} [Group G] (P U : Subgroup G)
    (hcomm : ∀ p : P, ∀ u : U, Commute (P.subtype p) (U.subtype u)) (hdis : Disjoint P U) :
    Function.Injective (internalProductMap P U hcomm) := by
  intro a b hab
  apply Subgroup.mul_injective_of_disjoint hdis
  exact congrArg (fun z : ↥(P ⊔ U) => (z : G)) hab

theorem internalProductMap_surjective {G : Type u} [Group G] (P U : Subgroup G)
    (hcomm : ∀ p : P, ∀ u : U, Commute (P.subtype p) (U.subtype u)) :
    Function.Surjective (internalProductMap P U hcomm) := by
  intro g
  have hrange : (P.subtype.noncommCoprod U.subtype hcomm).range = P ⊔ U := by
    have h := MonoidHom.noncommCoprod_range P.subtype U.subtype hcomm
    rwa [Subgroup.range_subtype, Subgroup.range_subtype] at h
  have hg : (g : G) ∈ (P.subtype.noncommCoprod U.subtype hcomm).range := by
    rw [hrange]
    exact g.property
  obtain ⟨a, ha⟩ := hg
  exact ⟨a, Subtype.ext ha⟩

@[expose] def internalProductEquiv {G : Type u} [Group G] (P U : Subgroup G)
    (hcomm : ∀ p : P, ∀ u : U, Commute (P.subtype p) (U.subtype u)) (hdis : Disjoint P U) :
    P × U ≃* ↥(P ⊔ U) :=
  MulEquiv.ofBijective (internalProductMap P U hcomm)
    ⟨internalProductMap_injective P U hcomm hdis, internalProductMap_surjective P U hcomm⟩


end


theorem original_four_group_generated_pair (T : Subgroup G) [IsKleinFour T]
    (x y : G) (hxT : x ∈ T) (hyT : y ∈ T) (hx : x ≠ 1) (hy : y ≠ 1) (hxy : x ≠ y) :
    T = Subgroup.closure ({x, y} : Set G) := by
  let a : T := ⟨x, hxT⟩
  let b : T := ⟨y, hyT⟩
  have ha : a ≠ 1 := fun h => hx (congrArg (fun z : T => (z : G)) h)
  have hb : b ≠ 1 := fun h => hy (congrArg (fun z : T => (z : G)) h)
  have hab : a ≠ b := fun h => hxy (congrArg (fun z : T => (z : G)) h)
  apply le_antisymm
  · intro g hg
    let c : T := ⟨g, hg⟩
    by_cases hc1 : c = 1
    · have hg1 : g = 1 := congrArg (fun z : T => (z : G)) hc1
      rw [hg1]
      exact Subgroup.one_mem _
    by_cases hca : c = a
    · have hga : g = x := congrArg (fun z : T => (z : G)) hca
      rw [hga]
      exact Subgroup.subset_closure (by simp)
    by_cases hcb : c = b
    · have hgb : g = y := congrArg (fun z : T => (z : G)) hcb
      rw [hgb]
      exact Subgroup.subset_closure (by simp)
    have hc := IsKleinFour.eq_mul_of_ne_all ha hb hab hc1 hca hcb
    have hgc : g = x * y := congrArg (fun z : T => (z : G)) hc
    rw [hgc]
    exact (Subgroup.closure ({x, y} : Set G)).mul_mem
      (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
  · apply (Subgroup.closure_le T).mpr
    intro g hg
    rcases Set.mem_insert_iff.mp hg with rfl | hg
    · exact hxT
    · exact Set.mem_singleton_iff.mp hg ▸ hyT


end CFSG.Wreathed.OriginalSylowNormalizerWitness
