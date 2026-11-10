module

public import CFSG.Sporadic.Schreier.RuLocalSub
public import CFSG.Sporadic.Schreier.RuBlocks

public noncomputable section

namespace CFSG.Sporadic.RuSchreier

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
open scoped Pointwise

theorem ruCBlock_pointList
    {i : ℕ} (hi : i < 6) : PointList 4060 (ruCBlockList i) :=
  ⟨(ruBlocks_check.2.2.2.2.1 i hi).2, (ruBlocks_check.2.2.2.2.1 i hi).1⟩

theorem ruNBlock_pointList
    {i : ℕ} (hi : i < 7) : PointList 4060 (ruNBlockList i) :=
  ⟨(ruBlocks_check.2.2.2.2.2.1 i hi).2, (ruBlocks_check.2.2.2.2.2.1 i hi).1⟩

theorem ruCBlock_injective : Function.Injective ruCBlock := by
  intro i j h
  have hl := (ruCBlock_pointList i.2).eq_of_finSet_eq (ruCBlock_pointList j.2) h
  exact Fin.ext (List.inj_on_of_nodup_map ruBlocks_check.2.2.2.2.2.2.1
    (List.mem_range.2 i.2) (List.mem_range.2 j.2) hl)

theorem ruNBlock_injective : Function.Injective ruNBlock := by
  intro i j h
  have hl := (ruNBlock_pointList i.2).eq_of_finSet_eq (ruNBlock_pointList j.2) h
  exact Fin.ext (List.inj_on_of_nodup_map ruBlocks_check.2.2.2.2.2.2.2.1
    (List.mem_range.2 i.2) (List.mem_range.2 j.2) hl)

@[expose] def ruCPi (g : ℕ) (i : Fin 6) : Fin 6 :=
  ⟨(ruCBlockPerms.getD g #[])[(i : ℕ)]! % 6, Nat.mod_lt _ (by norm_num)⟩

@[expose] def ruNPi (g : ℕ) (i : Fin 7) : Fin 7 :=
  ⟨(ruNBlockPerms.getD g #[])[(i : ℕ)]! % 7, Nat.mod_lt _ (by norm_num)⟩

theorem ruCPi_val {g : ℕ} (hg : g < 2) (i : Fin 6) :
    ((ruCPi g i : Fin 6) : ℕ) = (ruCBlockPerms.getD g #[])[(i : ℕ)]! :=
  Nat.mod_eq_of_lt (ruBlocks_check.2.2.2.2.2.2.2.2.1 g hg i i.2)

theorem ruNPi_val {g : ℕ} (hg : g < 2) (i : Fin 7) :
    ((ruNPi g i : Fin 7) : ℕ) = (ruNBlockPerms.getD g #[])[(i : ℕ)]! :=
  Nat.mod_eq_of_lt (ruBlocks_check.2.2.2.2.2.2.2.2.2.1 g hg i i.2)

theorem ruC_gen_block
    {g : ℕ} (hg : g < 2) (i : Fin 6) :
    [ruC0, ruC1].getD g 1 • ruCBlock i = ruCBlock (ruCPi g i) := by
  have himg := (ruCBlock_pointList i.2).img (rep_pair_getD rep_ruC0 rep_ruC1 g hg)
  rw [ruCBlock, ← himg.2, ruBlocks_check.1 i i.2 g hg, ruCBlock, ruCPi_val hg]

theorem ruN_gen_block
    {g : ℕ} (hg : g < 2) (i : Fin 7) :
    [ruNs0, ruNs1].getD g 1 • ruNBlock i = ruNBlock (ruNPi g i) := by
  have himg := (ruNBlock_pointList i.2).img (rep_ruNsPair g hg)
  rw [ruNBlock, ← himg.2, ruBlocks_check.2.1 i i.2 g hg, ruNBlock, ruNPi_val hg]

theorem ruC_blocks :
    ∀ g ∈ ruC, ∀ i, ∃ j, g • ruCBlock i = ruCBlock j := by
  apply blocks_of_closure ruCBlock_injective
  intro x hx
  rcases hx with rfl | rfl
  · exact fun i => ⟨_, ruC_gen_block (g := 0) (by norm_num) i⟩
  · exact fun i => ⟨_, ruC_gen_block (g := 1) (by norm_num) i⟩

theorem ruN_blocks :
    ∀ g ∈ ruN, ∀ i, ∃ j, g • ruNBlock i = ruNBlock j := by
  apply blocks_of_closure ruNBlock_injective
  intro x hx
  rcases hx with rfl | rfl
  · exact fun i => ⟨_, ruN_gen_block (g := 0) (by norm_num) i⟩
  · exact fun i => ⟨_, ruN_gen_block (g := 1) (by norm_num) i⟩

@[expose] def ruCBlockHom :
    ruC →* Equiv.Perm (Fin 6) :=
  Classical.choose (exists_blockHom ruCBlock_injective ruC ruC_blocks)

@[expose] def ruNBlockHom :
    ruN →* Equiv.Perm (Fin 7) :=
  Classical.choose (exists_blockHom ruNBlock_injective ruN ruN_blocks)

theorem ruCBlockHom_spec
    (g : ruC) (i : Fin 6) :
    (g : Equiv.Perm (Fin 4060)) • ruCBlock i = ruCBlock (ruCBlockHom g i) :=
  Classical.choose_spec (exists_blockHom ruCBlock_injective ruC ruC_blocks) g i

theorem ruNBlockHom_spec
    (g : ruN) (i : Fin 7) :
    (g : Equiv.Perm (Fin 4060)) • ruNBlock i = ruNBlock (ruNBlockHom g i) :=
  Classical.choose_spec (exists_blockHom ruNBlock_injective ruN ruN_blocks) g i

theorem range_closure_pair {G M : Type*} [Group G] [Group M] {g₀ g₁ : G}
    (f : Subgroup.closure {g₀, g₁} →* M) :
    f.range = Subgroup.closure {f ⟨g₀, Subgroup.subset_closure (Set.mem_insert _ _)⟩,
      f ⟨g₁, Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)⟩} := by
  rw [range_closure]
  congr 1
  ext m
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨x, hx⟩, rfl⟩
    rcases hx with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨⟨g₀, Set.mem_insert _ _⟩, rfl⟩
    · exact ⟨⟨g₁, Set.mem_insert_of_mem _ rfl⟩, rfl⟩


theorem rep_ruCBlockHom
    {g : ℕ} (hg : g < 2) (hmem : [ruC0, ruC1].getD g 1 ∈ ruC) :
    Rep 6 (ruCBlockPerms.getD g #[]) (ruCBlockHom ⟨_, hmem⟩) := by
  intro i
  have h := (ruCBlockHom_spec ⟨_, hmem⟩ i).symm.trans (ruC_gen_block hg i)
  rw [← ruCPi_val hg i, ruCBlock_injective h]

theorem rep_ruNBlockHom
    {g : ℕ} (hg : g < 2) (hmem : [ruNs0, ruNs1].getD g 1 ∈ ruN) :
    Rep 7 (ruNBlockPerms.getD g #[]) (ruNBlockHom ⟨_, hmem⟩) := by
  intro i
  have h := (ruNBlockHom_spec ⟨_, hmem⟩ i).symm.trans (ruN_gen_block hg i)
  rw [← ruNPi_val hg i, ruNBlock_injective h]


theorem ruCBlockHom_range :
    ruCBlockHom.range = ruChainCBlock.originalSubgroup := by
  have h := ruChainBlocks_check.1
  obtain ⟨-, -, -, -, -, -, -, -, -, -, e0, e1, -, -⟩ := ruBlocks_check
  have p0 : permOfArr 6 ruCBlockStrong[0]! = ruCBlockHom ⟨ruC0, ruC0_memC⟩ :=
    ((rep_permOfArr (ruChain_strong_inv h (by decide))).1).unique
      (e0 ▸ rep_ruCBlockHom (g := 0) (by norm_num) ruC0_memC)
  have p1 : permOfArr 6 ruCBlockStrong[1]! = ruCBlockHom ⟨ruC1, ruC1_memC⟩ :=
    ((rep_permOfArr (ruChain_strong_inv h (by decide))).1).unique
      (e1 ▸ rep_ruCBlockHom (g := 1) (by norm_num) ruC1_memC)
  refine (range_closure_pair (g₀ := ruC0) (g₁ := ruC1) ruCBlockHom).trans ?_
  rw [RawSchreierDatum.originalSubgroup,
    show ruChainCBlock.original.toList = (List.range 2).map fun i => permOfArr 6
      ruCBlockStrong[i]! from ofArrays_original_toList, show List.range 2 = [0, 1] from rfl,
    List.map_cons, List.map_cons, List.map_nil, p0, p1, setOf_mem_pair]
  rfl

theorem ruNBlockHom_range :
    ruNBlockHom.range = ruChainNBlock.originalSubgroup := by
  have h := ruChainBlocks_check.2.2.1
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, e0, e1⟩ := ruBlocks_check
  have p0 : permOfArr 7 ruNBlockStrong[0]! = ruNBlockHom ⟨ruNs0, ruNs0_memN⟩ :=
    ((rep_permOfArr (ruChain_strong_inv h (by decide))).1).unique
      (e0 ▸ rep_ruNBlockHom (g := 0) (by norm_num) ruNs0_memN)
  have p1 : permOfArr 7 ruNBlockStrong[1]! = ruNBlockHom ⟨ruNs1, ruNs1_memN⟩ :=
    ((rep_permOfArr (ruChain_strong_inv h (by decide))).1).unique
      (e1 ▸ rep_ruNBlockHom (g := 1) (by norm_num) ruNs1_memN)
  refine (range_closure_pair (g₀ := ruNs0) (g₁ := ruNs1) ruNBlockHom).trans ?_
  rw [RawSchreierDatum.originalSubgroup,
    show ruChainNBlock.original.toList = (List.range 2).map fun i => permOfArr 7
      ruNBlockStrong[i]! from ofArrays_original_toList, show List.range 2 = [0, 1] from rfl,
    List.map_cons, List.map_cons, List.map_nil, p0, p1, setOf_mem_pair]
  rfl

theorem card_ruCBlockHom_range :
    Nat.card ruCBlockHom.range = 120 := by
  have h : Nat.card ruChainCBlock.originalSubgroup = _ := ruChain_card ruChainBlocks_check.1
  rw [ruChainBlocks_check.2.1] at h
  rw [ruCBlockHom_range]
  exact h

theorem card_ruNBlockHom_range :
    Nat.card ruNBlockHom.range = 168 := by
  have h : Nat.card ruChainNBlock.originalSubgroup = _ := ruChain_card ruChainBlocks_check.2.2.1
  rw [ruChainBlocks_check.2.2.2] at h
  rw [ruNBlockHom_range]
  exact h

theorem subgroupOf_le_ker {G M : Type*} [Group G] [Group M] {H : Subgroup G} (f : H →* M)
    {X : Set G} (hX : X ⊆ H) (h1 : ∀ x (hx : x ∈ X), f ⟨x, hX hx⟩ = 1) :
    (Subgroup.closure X).subgroupOf H ≤ f.ker := by
  rw [← Subgroup.map_eq_bot_iff, map_subgroupOf_closure f hX, Subgroup.closure_eq_bot_iff]
  rintro _ ⟨x, rfl⟩
  exact h1 x.1 x.2

theorem ruJ_le_ker :
    ruJ.subgroupOf ruC ≤ ruCBlockHom.ker := by
  apply subgroupOf_le_ker ruCBlockHom (X := {g | g ∈ ruJGens}) ruJGens_memC
  intro x hx
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hx
  have hj6 : j < 6 := by rw [ruJGens_length] at hj; exact hj
  apply Equiv.ext
  intro i
  apply ruCBlock_injective
  rw [← ruCBlockHom_spec, Equiv.Perm.one_apply]
  have himg := (ruCBlock_pointList i.2).img (rep_ruJGens j hj6)
  rw [List.getD_eq_getElem ruJGens 1 hj] at himg
  have hgoal : ruJGens[j]'hj • ruCBlock i = ruCBlock i := by
    rw [ruCBlock, ← himg.2, ruBlocks_check.2.2.1 i i.2 j hj6]
  exact hgoal

theorem ruK_le_ker :
    ruK.subgroupOf ruN ≤ ruNBlockHom.ker := by
  apply subgroupOf_le_ker ruNBlockHom (X := {g | g ∈ ruKGens}) fun g hg => ruK_leN
    (Subgroup.subset_closure hg)
  intro x hx
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hx
  have hj8 : j < 8 := by rw [ruKGens_length] at hj; exact hj
  apply Equiv.ext
  intro i
  apply ruNBlock_injective
  rw [← ruNBlockHom_spec, Equiv.Perm.one_apply]
  have himg := (ruNBlock_pointList i.2).img (rep_ruKGens j hj8)
  rw [List.getD_eq_getElem ruKGens 1 hj] at himg
  have hgoal : ruKGens[j]'hj • ruNBlock i = ruNBlock i := by
    rw [ruNBlock, ← himg.2, ruBlocks_check.2.2.2.1 i i.2 j hj8]
  exact hgoal

theorem card_subgroupOf_of_le {G : Type*} [Group G] {H K : Subgroup G} (h : H ≤ K) :
    Nat.card (H.subgroupOf K) = Nat.card H :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv

theorem ruCBlockHom_ker :
    ruCBlockHom.ker = ruJ.subgroupOf ruC := by
  symm
  apply Subgroup.eq_of_le_of_card_ge ruJ_le_ker
  have h1 := card_ker_mul_card_range ruCBlockHom
  rw [card_ruCBlockHom_range, card_ruC] at h1
  have h2 : Nat.card ruCBlockHom.ker = 2048 :=
    Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 120) (h1.trans (by norm_num))
  rw [h2, card_subgroupOf_of_le ruJ_leC, card_ruJ]

instance :

    Finite ruN := Nat.finite_of_card_ne_zero (by rw [card_ruN]; norm_num)

theorem ruNBlockHom_ker :
    ruNBlockHom.ker = ruK.subgroupOf ruN := by
  symm
  apply Subgroup.eq_of_le_of_card_ge ruK_le_ker
  have h1 := card_ker_mul_card_range ruNBlockHom
  rw [card_ruNBlockHom_range, card_ruN] at h1
  have h2 : Nat.card ruNBlockHom.ker = 2048 :=
    Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 168) (h1.trans (by norm_num))
  rw [h2, card_subgroupOf_of_le ruK_leN, card_ruK]

theorem ruJ_normal :
    (ruJ.subgroupOf ruC).Normal := by
  rw [← ruCBlockHom_ker]
  infer_instance

theorem ruK_normal :
    (ruK.subgroupOf ruN).Normal := by
  rw [← ruNBlockHom_ker]
  infer_instance

instance :

    Finite ruP := Nat.finite_of_card_ne_zero (by rw [card_ruP]; norm_num)

theorem factorization_ruP :
    (Nat.card ruP).factorization 2 = 14 := by
  rw [card_ruP, show (145926144000 : ℕ) = 2 ^ 14 * 8906625 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.factorization_pow_self Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬2 ∣ 8906625)]

@[expose] def ruSylow :
    Sylow 2 ruP :=
  Sylow.ofCard (ruS.subgroupOf ruP) (by
    rw [card_subgroupOf_of_le ruS_le, card_ruS, factorization_ruP]
    norm_num)

theorem ruSylow_coe :
    (ruSylow : Subgroup ruP) = ruS.subgroupOf ruP := rfl


end CFSG.Sporadic.RuSchreier
