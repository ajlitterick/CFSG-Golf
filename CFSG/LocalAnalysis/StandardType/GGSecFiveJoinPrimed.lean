module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveJoinHC
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
public import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1OfPrim
public import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1Weyl
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylKnownDefs
public import CFSG.LocalAnalysis.StandardType.GGCellWitness
public import CFSG.LocalAnalysis.StandardType.GGRealQFour
public import CFSG.LocalAnalysis.StandardType.GGNbrBalance

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem le_join_of_absorb
    {G : Type} [Group G] [Finite G] {L J Bs K' : Subgroup G} {𝒦 : Finset (Subgroup G)} (hJL : J ≤ L)
    (hcJ : ∀ c ∈ Subgroup.centralizer (Bs : Set G), ∀ j ∈ J, c * j * c⁻¹ ∈ J) (n : G)
    (hK' : K' ≤ J ⊔ J.map (MulAut.conj n).toMonoidHom)
    (φ : MulAut ↥Bs) (hφ : φ ∈ ggAutomizerJoin L Bs 𝒦)
    (hφn : ∀ b : ↥Bs, ((φ b : ↥Bs) : G) = n * b * n⁻¹) :
    K' ≤ L ⊔ ⨆ K ∈ 𝒦, K := by
  obtain ⟨g, hg, -, hgφ⟩ :=
    mem_ggAutomizer_iff.mp (ggAutomizerJoin_le_ggAutomizer L Bs 𝒦 hφ)
  have hc : g⁻¹ * n ∈ Subgroup.centralizer (Bs : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have h1 := hgφ ⟨b, hb⟩
    rw [hφn ⟨b, hb⟩] at h1
    have h2 : n * b = g * b * g⁻¹ * n := by rw [← h1]; group
    calc b * (g⁻¹ * n) = g⁻¹ * (g * b * g⁻¹ * n) := by group
      _ = g⁻¹ * (n * b) := by rw [← h2]
      _ = g⁻¹ * n * b := by group
  refine hK'.trans (sup_le (hJL.trans le_sup_left) ?_)
  rintro _ ⟨j, hj, rfl⟩
  have hj' := hcJ _ hc j hj
  have : (MulAut.conj n).toMonoidHom j = g * ((g⁻¹ * n) * j * (g⁻¹ * n)⁻¹) * g⁻¹ := by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group
  rw [this]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hg (le_sup_left (b := ⨆ K ∈ 𝒦, K) (hJL hj')))
    (Subgroup.inv_mem _ hg)


theorem map_conj_le_join_of_absorb
    {G : Type} [Group G] [Finite G] {L J Bs : Subgroup G} {𝒦 : Finset (Subgroup G)} (hJL : J ≤ L)
    (hcJ : ∀ c ∈ Subgroup.centralizer (Bs : Set G), ∀ j ∈ J, c * j * c⁻¹ ∈ J) (n : G)
    (φ : MulAut ↥Bs) (hφ : φ ∈ ggAutomizerJoin L Bs 𝒦)
    (hφn : ∀ b : ↥Bs, ((φ b : ↥Bs) : G) = n * b * n⁻¹) :
    J.map (MulAut.conj n).toMonoidHom ≤ L ⊔ ⨆ K ∈ 𝒦, K :=
  le_join_of_absorb (K' := J.map (MulAut.conj n).toMonoidHom) hJL hcJ n le_sup_right φ hφ hφn

theorem ggG0_le_join_of_reflMax_genN
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hJL : J ≤ L)
    (hcJ : ∀ c ∈ Subgroup.centralizer (Bs : Set G), ∀ j ∈ J, c * j * c⁻¹ ∈ J)
    (hRM : ∀ (y : G) (K' : Subgroup G), GGNbr p B x D J y K' →
      ggAutomizer K' Bs ≤ ggAutomizerJoin L Bs 𝒦)
    (hGen : ∀ (y : G) (K' : Subgroup G), GGNbr p B x D J y K' →
      ggAutomizer K' Bs ≤ ggAutomizerJoin L Bs 𝒦 →
      K' ≤ ⨆ (n : G) (_ : n ∈ K') (_ : ∃ φ : MulAut ↥Bs,
          n ∈ Subgroup.normalizer (Bs : Set G) ∧ ∀ b : ↥Bs, ((φ b : ↥Bs) : G) = n * b * n⁻¹),
        J.map (MulAut.conj n).toMonoidHom) :
    ggG0 p B x L D J ≤ L ⊔ ⨆ K ∈ 𝒦, K := by
  refine sup_le le_sup_left (iSup_le fun y => iSup_le fun K' => iSup_le fun hK' => ?_)
  refine (hGen y K' hK' (hRM y K' hK')).trans
    (iSup_le fun n => iSup_le fun hnK => iSup_le fun ⟨φ, hnN, hφn⟩ => ?_)
  have hφ : φ ∈ ggAutomizer K' Bs := Subgroup.subset_closure ⟨n, hnK, hnN, hφn⟩
  exact map_conj_le_join_of_absorb hJL hcJ n φ (hRM y K' hK' hφ) hφn

@[expose] def GGSecFiveRegionGuard
    {G : Type} [Group G] [Finite G] (p : ℕ) (L Bs : Subgroup G) (𝒦 : Finset (Subgroup G)) : Prop :=
  ∃ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
    GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e ∧ ∀ i j : ι, i ≠ j → M.M i j ≤ 3


theorem ggSecFiveRegionGuard_of_ADE
    {G : Type} [Group G] [Finite G] {p : ℕ} {L Bs : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (h : ∃ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
      GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e ∧ (GGIsWeylMatrixAD M ∨ GGIsWeylMatrixE M)) :
    GGSecFiveRegionGuard p L Bs 𝒦 := by
  obtain ⟨ι, M, e, hpres, hADE⟩ := h
  refine ⟨ι, M, e, hpres, fun i j hij => ?_⟩
  rcases hADE with hAD | hE
  · exact hAD.le_three i j hij
  · exact hE.le_three i j hij

section JoinPrimed

@[expose] def GGSecFiveRouteCfg'
    {G : Type} [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)) : Prop :=
  GGSecFiveRestHyp p B Bs x L D J ∧ GGSecFiveWeylCase' p B Bs x D J ∧
    ¬ GGSecFiveLeviCase p B Bs x L D J ∧ GGMaximalJoin p B Bs x L D J 𝒦

theorem ggSecFiveRouteCfg'_of_routeCfg
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (h : GGSecFiveRouteCfg p B Bs x L D J 𝒦) :
    GGSecFiveRouteCfg' p B Bs x L D J 𝒦 := by
  first
    | exact h
    | exact ⟨h.1, h.2.1.2, h.2.2.1, h.2.2.2⟩

@[expose] def GGSecFiveReflMaxInput'
    : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg' p B Bs x L D J 𝒦 → GGSplitLie p L →
      ∀ (y : G) (K' : Subgroup G), GGNbr p B x D J y K' →
        ggAutomizer K' Bs ≤ ggAutomizerJoin L Bs 𝒦

@[expose] def GGSecFiveNbrGenKNInput'
    : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg' p B Bs x L D J 𝒦 → GGSplitLie p L →
      GGSecFiveRegionGuard p L Bs 𝒦 →
      ∀ (y : G) (K' : Subgroup G), GGNbr p B x D J y K' →
        ggAutomizer K' Bs ≤ ggAutomizerJoin L Bs 𝒦 →
        K' ≤ ⨆ (n : G) (_ : n ∈ K') (_ : ∃ φ : MulAut ↥Bs,
            n ∈ Subgroup.normalizer (Bs : Set G) ∧ ∀ b : ↥Bs, ((φ b : ↥Bs) : G) = n * b * n⁻¹),
          J.map (MulAut.conj n).toMonoidHom

@[expose] def GGSecFiveJNormInput'
    : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg' p B Bs x L D J 𝒦 → GGSplitLie p L →
      J ≤ L ∧ ∀ c ∈ Subgroup.centralizer (Bs : Set G), ∀ j ∈ J, c * j * c⁻¹ ∈ J

@[expose] def GGSecFiveJoinRegionInput'
    : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg' p B Bs x L D J 𝒦 → GGSplitLie p L →
      (∃ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e ∧ (GGIsWeylMatrixAD M ∨ GGIsWeylMatrixE M)) →
      ggG0 p B x L D J = L ⊔ ⨆ K ∈ 𝒦, K

theorem ggSecFiveJoinRegionInput'_of_reflMax'
    (hRM : GGSecFiveReflMaxInput')
    (hGen : GGSecFiveNbrGenKNInput') (hJ : GGSecFiveJNormInput') : GGSecFiveJoinRegionInput' := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg hsplit hADE
  have hguard := ggSecFiveRegionGuard_of_ADE hADE
  obtain ⟨hJL, hcJ⟩ := hJ G p B Bs x L D J 𝒦 hcfg hsplit
  refine le_antisymm ?_ (ggJoin_le_ggG0 (Bs := Bs) hcfg.2.2.2.1)
  exact ggG0_le_join_of_reflMax_genN hJL hcJ (hRM G p B Bs x L D J 𝒦 hcfg hsplit)
    (hGen G p B Bs x L D J 𝒦 hcfg hsplit hguard)

theorem ggSecFiveJoinRegionInput_of_join'
    (h : GGSecFiveJoinRegionInput') :
    GGSecFiveJoinRegionInput := by
  intro G _ _ p B Bs x L D J 𝒦 hR hsplit hADE
  exact h G p B Bs x L D J 𝒦 (ggSecFiveRouteCfg'_of_routeCfg hR) hsplit hADE

theorem ggSecFiveJoinRegionInput_of_primed
    (hRM : GGSecFiveReflMaxInput')
    (hGen : GGSecFiveNbrGenKNInput') (hJ : GGSecFiveJNormInput') : GGSecFiveJoinRegionInput :=
  ggSecFiveJoinRegionInput_of_join' (ggSecFiveJoinRegionInput'_of_reflMax' hRM hGen hJ)


@[expose] def GGSecFiveJrInput
    : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg' p B Bs x L D J 𝒦 → GGSplitLie p L →
      ∀ r ∈ ggAutomizer J Bs, GGIsReflection p r → GGRealized p Bs r


@[expose] def GGSecFiveFixInput
    : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg' p B Bs x L D J 𝒦 → GGSplitLie p L →
      ∀ b : Bs, (∀ φ ∈ ggAutomizer L Bs, φ b = b) → (b : G) ∈ Subgroup.zpowers x


@[expose] def GGSecFiveRootReflInput
    : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (Bs : Subgroup G), p.Prime → p ≠ 2 →
    IsElemAbelian p Bs → GGNoTransvection p Bs →
      ∀ (A : Subgroup (MulAut ↥Bs)), A ≤ ggInduced ⊤ Bs →
        ∀ (ι : Type) (M : CoxeterMatrix ι), GGIsWeylMatrix M →
          (¬ ∃ e : Fin 2 ≃ ι, M = CoxeterMatrix.G₂.reindex e) →
          ∀ f : M.Group ≃* ↥A, (∀ i : ι, GGIsReflection p ((f (M.simple i) : ↥A) : MulAut ↥Bs)) →
            ∀ a : ↥A, GGIsReflection p (a : MulAut ↥Bs) →
              ∃ (i : ι) (g : M.Group), a = f (g * M.simple i * g⁻¹)


@[expose] def GGSecFiveCRInput
    : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg' p B Bs x L D J 𝒦 → GGSplitLie p L →
      ∀ t t' : MulAut ↥Bs,
        (∃ r ∈ ggAutomizer J Bs, GGIsReflection p r ∧ ∃ g ∈ ggInduced ⊤ Bs, t = g * r * g⁻¹) →
        GGIsReflection p t' → GGRealized p Bs t' → orderOf (t * t') ≤ 4

@[expose] noncomputable def ggAInf
    {G : Type} [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (L D J : Subgroup G) : Subgroup (MulAut ↥Bs) :=
  ggAutomizer L Bs ⊔ ⨆ (y : G) (K : Subgroup G) (_ : GGNbr p B x D J y K), ggAutomizer K Bs

@[expose] def GGSecFiveWeylBranchInput
    : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg' p B Bs x L D J 𝒦 → GGSplitLie p L →
      (∀ b : ↥Bs, (∀ φ ∈ ggAInf p B Bs x L D J, φ b = b) → b = 1) →
        GGWeylReflectionGroup p (ggAInf p B Bs x L D J)


end JoinPrimed

end CFSG.StandardType
