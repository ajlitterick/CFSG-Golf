module

public import CFSG.LieType.HighestRoot.CentChevalleySLThree
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1PullBackSpin
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup
open scoped MatrixGroups Pointwise

namespace F3L221

theorem gwIsQuasisimple {Q : Type*} [Group Q] (hQ : IsQuasisimple Q) :
    GorensteinWalter.IsQuasisimple Q :=
  ⟨LocalCores.isQuasisimple_nontrivial hQ, (Group.isPerfect_def).1 hQ.1, hQ.2.1⟩

variable {Y : Type} [Group Y] [Finite Y]

theorem isSolvable_of_isSolvableTwoComponentIn {K A : Subgroup Y}
    (hK : IsSolvableTwoComponentIn K A) : Group.IsSolvable ↥K := by
  have h3 : Nat.card (ZMod 3) = 3 := by rw [Nat.card_eq_fintype_card, ZMod.card]
  have : Group.IsSolvable ↥(pPrimeCore 2 ↥K) :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard _ (odd_card_pPrimeCore_two ↥K)
  have : Group.IsSolvable (↥K ⧸ pPrimeCore 2 ↥K) := by
    have : Group.IsSolvable SL(2, ZMod 3) :=
      LieType.HighestRoot.isSolvable_of_mulEquiv h3 (MulEquiv.refl _)
    rcases hK.2.2.2 with h1 | h1
    · obtain ⟨e⟩ := h1
      have : Group.IsSolvable (PSL(2, ZMod 3)) :=
        Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective _)
      exact Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
    · obtain ⟨e⟩ := h1
      exact Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
  exact Group.isSolvable_of_ker_le_range (pPrimeCore 2 ↥K).subtype
    (QuotientGroup.mk' (pPrimeCore 2 ↥K)) (by rw [QuotientGroup.ker_mk', range_subtype])

theorem commute_of_isQuasisimple {C D K : Subgroup Y} (hDC : D ≤ C)
    (hDs : (D.subgroupOf C).IsSubnormal) (hDq : IsQuasisimple ↥D) (hKC : K ≤ C)
    (hKs : (K.subgroupOf C).IsSubnormal) (hKsol : Group.IsSolvable ↥K) :
    ∀ k ∈ K, ∀ d ∈ D, k * d = d * k := by
  have hEq : IsQuasisimple ↥(D.subgroupOf C) :=
    LocalCores.isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe hDC).symm hDq
  have hE : GorensteinWalter.IsComponentOf (D.subgroupOf C) (⊤ : Subgroup ↥C) :=
    ⟨le_top, hDs.subgroupOf, gwIsQuasisimple hEq⟩
  rcases GorensteinWalter.component_le_or_commutator_eq_bot hE hKs with hle | hbot
  · exfalso
    have hDK : D ≤ K := fun d hd =>
      hle (show (⟨d, hDC hd⟩ : ↥C) ∈ D.subgroupOf C from hd)
    have : Group.IsSolvable ↥D :=
      Group.isSolvable_of_isSolvable_injective (f := inclusion hDK) (inclusion_injective hDK)
    have : Nontrivial ↥D := LocalCores.isQuasisimple_nontrivial hDq
    have : Group.IsPerfect ↥D := hDq.1
    have h1 := Group.IsSolvable.commutator_lt_top_of_nontrivial ↥D
    rw [Group.IsPerfect.commutator_eq_top] at h1
    exact lt_irrefl _ h1
  · intro k hk d hd
    have h1 := commutator_mem_commutator (show (⟨d, hDC hd⟩ : ↥C) ∈ D.subgroupOf C from hd)
      (show (⟨k, hKC hk⟩ : ↥C) ∈ K.subgroupOf C from hk)
    rw [hbot, mem_bot] at h1
    have h2 : d * k * d⁻¹ * k⁻¹ = 1 := by
      have := congrArg Subtype.val h1
      simpa [commutatorElement_def] using this
    calc k * d = (d * k * d⁻¹ * k⁻¹)⁻¹ * (d * k) := by group
      _ = d * k := by rw [h2, inv_one, one_mul]

theorem commute_of_centralizes {L K : Subgroup Y} (hLs : L.IsSubnormal)
    (hLq : IsQuasisimple ↥L) {z : Y} (hzL : ∀ l ∈ L, z * l = l * z)
    (hK : IsSolvableTwoComponentIn K (centralizer {z})) : ∀ k ∈ K, ∀ l ∈ L, k * l = l * k := by
  have hLC : L ≤ centralizer ({z} : Set Y) := fun l hl =>
    mem_centralizer_singleton_iff.mpr (hzL l hl).symm
  exact commute_of_isQuasisimple hLC hLs.subgroupOf hLq hK.1 hK.2.1
    (isSolvable_of_isSolvableTwoComponentIn hK)

omit [Finite Y] in
theorem mem_normalizer_iff_map_conj_eq {L : Subgroup Y} {g : Y} :
    g ∈ normalizer (L : Set Y) ↔ L.map (MulAut.conj g).toMonoidHom = L := by
  constructor
  · intro hg
    ext x
    rw [mem_map_equiv, MulAut.conj_symm_apply]
    have h1 := (mem_normalizer_iff.mp (inv_mem hg) x)
    rw [inv_inv] at h1
    exact h1.symm
  · intro h
    rw [mem_normalizer_iff]
    intro x
    have h1 : x ∈ L ↔ g * x * g⁻¹ ∈ L.map (MulAut.conj g).toMonoidHom := by
      rw [mem_map_equiv, MulAut.conj_symm_apply]
      rw [show g⁻¹ * (g * x * g⁻¹) * g = x by group]
    rw [h] at h1
    exact h1

omit [Finite Y] in
theorem exists_sq_eq_of_odd {K : Subgroup Y} {x : Y} (hx : x ∈ K) (hodd : Odd (orderOf x)) :
    ∃ y ∈ K, y * y = x := by
  obtain ⟨m, hm⟩ := hodd
  refine ⟨x ^ (m + 1), pow_mem hx _, ?_⟩
  rw [← pow_add, show m + 1 + (m + 1) = orderOf x + 1 by omega, pow_succ, pow_orderOf_eq_one,
    one_mul]

theorem le_of_forall_odd {K A : Subgroup Y} (hK : IsSolvableTwoComponentIn K A) {N : Subgroup Y}
    (hN : ∀ x ∈ K, Odd (orderOf x) → x ∈ N) : K ≤ N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h3 : Nat.card (ZMod 3) = 3 := by rw [Nat.card_eq_fintype_card, ZMod.card]
  set R := pPrimeCore 2 ↥K with hR
  set π := QuotientGroup.mk' R with hπ
  set N' := N.subgroupOf K with hN'
  have hodd := odd_card_pPrimeCore_two ↥K
  obtain ⟨φ, hφ⟩ : ∃ φ : SL(2, ZMod 3) →* ↥K ⧸ R, Function.Surjective φ := by
    rcases hK.2.2.2 with h | h
    · obtain ⟨e⟩ := h
      exact ⟨e.symm.toMonoidHom.comp (QuotientGroup.mk' _),
        e.symm.surjective.comp (QuotientGroup.mk'_surjective _)⟩
    · obtain ⟨e⟩ := h
      exact ⟨e.symm.toMonoidHom, e.symm.surjective⟩
  have hcube : ∀ y : ↥K, y ^ 3 ∈ R → (y : Y) ∈ N := by
    intro y hy
    refine hN y y.2 ?_
    have h1 : y ^ (3 * Nat.card R) = 1 := by
      rw [pow_mul]
      have h2 := pow_card_eq_one' (G := ↥R) (x := ⟨y ^ 3, hy⟩)
      have h3' := congrArg Subtype.val h2
      simpa only [Subgroup.coe_pow, Subgroup.coe_one] using h3'
    have h4 : orderOf y ∣ 3 * Nat.card R := orderOf_dvd_of_pow_eq_one h1
    have h5 : Odd (3 * Nat.card R) := Odd.mul (by decide) hodd
    rw [← Subgroup.orderOf_coe] at h4
    exact h5.of_dvd_nat h4
  have hcl : closure {x : ↥K ⧸ R | x ^ 3 = 1} = ⊤ := by
    have h1 := LieType.HighestRoot.closure_orderOf_three_eq_top_of_mulEquiv h3
      (MulEquiv.refl (SL(2, ZMod 3)))
    have h2 := congrArg (Subgroup.map φ) h1
    rw [MonoidHom.map_closure, Subgroup.map_top_of_surjective φ hφ] at h2
    rw [eq_top_iff, ← h2]
    refine closure_mono ?_
    rintro _ ⟨y, hy, rfl⟩
    have hy3 : y ^ 3 = 1 := by
      have h : orderOf y = 3 := hy
      have h' := pow_orderOf_eq_one y
      rwa [h] at h'
    show φ y ^ 3 = 1
    rw [← map_pow, hy3, map_one]
  have hmap : N'.map π = ⊤ := by
    refine top_unique ?_
    rw [← hcl, closure_le]
    intro x hx
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective R x
    have hy : y ^ 3 ∈ R := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
      exact hx
    exact ⟨y, hcube y hy, rfl⟩
  have hker : π.ker ≤ N' := by
    intro y hy
    rw [hπ, QuotientGroup.ker_mk'] at hy
    have h1 : y ^ 3 ∈ R := pow_mem hy 3
    exact hcube y h1
  intro x hx
  have h1 : (⟨x, hx⟩ : ↥K) ∈ (N'.map π).comap π := by
    rw [mem_comap, hmap]
    exact mem_top _
  rw [comap_map_eq, sup_eq_left.mpr hker] at h1
  exact h1


end F3L221

end CFSG.ComponentClassification.HarrisLit.T1
