module

public import CFSG.Milestones.ASVolI.J4
public import CFSG.Quasithin.Recognition.RuRank3J5
public import CFSG.RankThree.PartOne.K159F.L2Leaf
public import CFSG.Sporadic.Recognition.LyonsAmalgamExtAut
public import CFSG.Quasithin.Recognition.RuRank3J55Data
public import CFSG.Quasithin.EmptyFaithful.S152N2Frob
public import Certificates.Certificate7340
public import Certificates.Certificate7341
public import Certificates.Certificate7342
public import CFSG.Quasithin.Background.D2
public import CFSG.Quasithin.Background.E3Gen
public import CFSG.Quasithin.EmptyFaithful.S14117
public import CFSG.Quasithin.EmptyFaithful.S152FinBasic
public import CFSG.Quasithin.EmptyFaithful.S152N2L14C
public import CFSG.Quasithin.EmptyFaithful.S152Stmts

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ASVolI.ChIJK

open CFSG.Open CFSG.Blueprint
open scoped MatrixGroups

scoped instance fact_prime_five : Fact (Nat.Prime 5) := ⟨by norm_num⟩

section J5

@[expose] def IsParabolicTwoSub {X : Type} [Group X] (P : Subgroup X) : Prop :=
  ∃ S : Sylow 2 X, Subgroup.normalizer ((S : Subgroup X) : Set X) ≤ P

@[expose] def IsL225Plus (Y : Type) [Group Y] : Prop :=
  ∃ N : Subgroup Y, N.Normal ∧ N.index = 2 ∧ StatedClassicalModel ↥N .PSL 2 5 2 ∧
    ∃ (P : Sylow 2 Y) (n : ℕ), 4 ≤ n ∧ Nonempty (↥(P : Subgroup Y) ≃* SemidihedralGroup n)

variable {G : Type} [Group G] {Ω : Type} [MulAction G Ω]

@[expose] def IsRudvalisRank3 (G : Type) [Group G] (Ω : Type) [MulAction G Ω] : Prop :=
  Nonempty Ω ∧ (∀ g : G, (∀ ω : Ω, g • ω = ω) → g = 1) ∧ MulAction.IsPretransitive G Ω ∧
    ∀ ω : Ω, Nat.card (MulAction.orbitRel.Quotient ↥(MulAction.stabilizer G ω) Ω) = 3 ∧
      IsTwoF4TwoGroup ↥(MulAction.stabilizer G ω) ∧
      (∃ δ : Ω, IsParabolicTwoSub ((MulAction.stabilizer G ω ⊓ MulAction.stabilizer G δ).subgroupOf
          (MulAction.stabilizer G ω)) ∧
        Nat.card ↥(MulAction.stabilizer G ω ⊓ MulAction.stabilizer G δ) = 2 ^ 12 * 5) ∧
      ∃ γ : Ω, IsL225Plus ↥(MulAction.stabilizer G ω ⊓ MulAction.stabilizer G γ)

@[expose] def DeltaAt (G : Type) [Group G] {Ω : Type} [MulAction G Ω] (ω δ ρ : Ω) : Set Ω :=
  {σ | ∃ g : G, g • ω = ρ ∧ g⁻¹ • σ ∈ MulAction.orbit ↥(MulAction.stabilizer G ω) δ}

@[expose] def SigmaAt (G : Type) [Group G] {Ω : Type} [MulAction G Ω] (ω γ ρ : Ω) : Set Ω :=
  {σ | ∃ g : G, g • ω = ρ ∧ g⁻¹ • σ ∈ MulAction.orbit ↥(MulAction.stabilizer G ω) γ}

@[expose] def pairStab (G : Type) [Group G] {Ω : Type} [MulAction G Ω] (α β : Ω) : Set G :=
  {g | ({g • α, g • β} : Set Ω) = {α, β}}

structure RudvalisSetting (G : Type) [Group G] (Ω : Type) [MulAction G Ω] (ω δ γ : Ω) : Prop where
  rank3 : IsRudvalisRank3 G Ω
  rub : IsParabolicTwoSub ((MulAction.stabilizer G ω ⊓ MulAction.stabilizer G δ).subgroupOf
      (MulAction.stabilizer G ω)) ∧
    Nat.card ↥(MulAction.stabilizer G ω ⊓ MulAction.stabilizer G δ) = 2 ^ 12 * 5
  ruc : IsL225Plus ↥(MulAction.stabilizer G ω ⊓ MulAction.stabilizer G γ)

end J5

section Geometry

variable {Y : Type} [Group Y]

@[expose] def incGraph (M1 M2 : Subgroup Y) : SimpleGraph (Y ⧸ M1 ⊕ Y ⧸ M2) where
  Adj u v := (∃ y : Y, u = Sum.inl (y : Y ⧸ M1) ∧ v = Sum.inr (y : Y ⧸ M2)) ∨
    (∃ y : Y, v = Sum.inl (y : Y ⧸ M1) ∧ u = Sum.inr (y : Y ⧸ M2))
  symm := ⟨fun _ _ h => Or.symm h⟩
  loopless := ⟨fun u h => by
    rcases h with ⟨y, h1, h2⟩ | ⟨y, h1, h2⟩
    · rw [h1] at h2; exact Sum.inl_ne_inr h2
    · rw [h1] at h2; exact Sum.inl_ne_inr h2⟩

end Geometry

open CFSG.Open CFSG.Blueprint
open scoped MatrixGroups

section J5b

variable {G : Type} [Group G] {Ω : Type} [MulAction G Ω]

@[expose] def FdOf (G : Type) [Group G] {Ω : Type} [MulAction G Ω] (ω δ : Ω) :
    Subgroup ↥(MulAction.stabilizer G ω) :=
  (MulAction.stabilizer G ω ⊓ MulAction.stabilizer G δ).subgroupOf (MulAction.stabilizer G ω)

structure RuBuilding (G : Type) [Group G] (Ω : Type) [MulAction G Ω] (ω δ γ : Ω)
    (M2 : Subgroup ↥(MulAction.stabilizer G ω))
    (φ : Ω → ↥(MulAction.stabilizer G ω) ⧸ FdOf G ω δ) : Prop where
  setting : RudvalisSetting G Ω ω δ γ
  amalgam : ∃ T' : Subgroup ↥(MulAction.stabilizer G ω),
    CFSG.Quasithin.IsYAmalgamPair T' (FdOf G ω δ) M2
  bij : Set.BijOn φ (DeltaAt G ω δ ω) Set.univ
  equivariant : ∀ f : ↥(MulAction.stabilizer G ω), ∀ ρ ∈ DeltaAt G ω δ ω, φ (f • ρ) = f • φ ρ
  base : φ δ = ((1 : ↥(MulAction.stabilizer G ω)) : ↥(MulAction.stabilizer G ω) ⧸ FdOf G ω δ)
  nbhd : ∀ ρ ∈ DeltaAt G ω δ ω, (ρ ∈ DeltaAt G ω δ δ ↔
    (0 < (incGraph (FdOf G ω δ) M2).dist (Sum.inl (φ δ)) (Sum.inl (φ ρ)) ∧
      (incGraph (FdOf G ω δ) M2).dist (Sum.inl (φ δ)) (Sum.inl (φ ρ)) < 8))

@[expose] def thetaAt (G : Type) [Group G] {Ω : Type} [MulAction G Ω] (ω δ u : Ω) : Set Ω :=
  {w | w ∈ DeltaAt G ω δ ω ∩ DeltaAt G ω δ u ∧
    (MulAction.orbit ↥(MulAction.stabilizer G ω ⊓ MulAction.stabilizer G u) w).ncard = 10}

@[expose] def LambdaAt (G : Type) [Group G] {Ω : Type} [MulAction G Ω] (ω δ γ u : Ω) : Set Ω :=
  DeltaAt G ω δ ω ∩ DeltaAt G ω δ u ∩ SigmaAt G ω γ δ

@[expose] def GeoFrom {W : Type} (Γ : SimpleGraph W) (x : W) (S : Set W) :
    Set (Σ b : W, Γ.Walk x b) :=
  {p | p.1 ∈ S ∧ p.2.length = Γ.dist x p.1}

@[expose] def WalkIncreases {W : Type} (Γ : SimpleGraph W) (δv : W) {a b : W} (p : Γ.Walk a b)
    (i i' : ℕ) : Prop :=
  i ≤ i' ∧ i' ≤ p.length ∧
    ∀ j, j ≤ i' - i → Γ.dist δv (p.getVert (i + j)) = Γ.dist δv (p.getVert i) + j

@[expose] noncomputable def dseq {W : Type} (Γ : SimpleGraph W) (δv : W) {a b : W} (p : Γ.Walk a b) (i : ℕ) : ℕ :=
  Γ.dist δv (p.getVert i)

@[expose] def NgeoSet {W : Type} (Γ : SimpleGraph W) (δv y : W) (e : ℕ) : Set (Σ b : W, Γ.Walk y b) :=
  {q | q.2.length = 8 - e ∧ ∀ j, j ≤ 8 - e → Γ.dist δv (q.2.getVert j) = e + j}

@[expose] def omegaGraph (G : Type) [Group G] {Ω : Type} [MulAction G Ω] (ω δ : Ω) : SimpleGraph Ω :=
  SimpleGraph.fromRel (fun ρ τ => τ ∈ DeltaAt G ω δ ρ)

@[expose] noncomputable def OmegaPrime (F : Type) [Group F] (M1 M2 E : Subgroup F) :
    SimpleGraph (Option (F ⧸ M1 ⊕ F ⧸ E)) :=
  SimpleGraph.fromRel (fun a b =>
    (∃ u : F ⧸ M1, a = none ∧ b = some (Sum.inl u)) ∨
    (∃ u v : F ⧸ M1, a = some (Sum.inl u) ∧ b = some (Sum.inl v) ∧
      (incGraph M1 M2).Reachable (Sum.inl u) (Sum.inl v) ∧
      (incGraph M1 M2).dist (Sum.inl u) (Sum.inl v) ≤ 6) ∨
    (∃ (u : F ⧸ M1) (v : F ⧸ E), a = some (Sum.inl u) ∧ b = some (Sum.inr v) ∧
      (MulAction.orbit ↥(MulAction.stabilizer F v) u).ncard = 780) ∨
    (∃ v w : F ⧸ E, a = some (Sum.inr v) ∧ b = some (Sum.inr w) ∧
      (MulAction.orbit ↥(MulAction.stabilizer F v) w).ncard = 975))

end J5b

end CFSG.ASVolI.ChIJK

namespace CFSG.ASVolI

open CFSG.Open CFSG.Blueprint CFSG.ASVolI.ChIJK
open scoped MatrixGroups

@[expose] def J_5_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L V T : Subgroup G), RuType G L V T →
    ∀ V2 : Subgroup G, IsV2 V T V2 →
    ∀ g ∈ L2Ru L V2, g ∉ HRu T →
    ∀ v : G, v ∈ CFSG.conjugate (URu V T) g → v ∉ CFSG.conjugate (URu V T) g ⊓ QRu T →
    ∀ B5 : Subgroup G, IsSylowIn 5 B5 (HRu T) → InvertsGroup v B5 →
    ∀ X : Subgroup G, IsSylowIn 3 X (G2Ru L V2 T) →
    ∀ a : G, IsAChoice L V T V2 B5 a →
      ARu L V V2 T a ≤ Subgroup.normalizer ((B5 ⊔ Q5Ru T B5 : Subgroup G) : Set G) →
      Q5Ru T B5 ≤ Subgroup.normalizer ((X ⊔ ARu L V V2 T a : Subgroup G) : Set G) →
        Nat.card (G ⧸ FRu L V V2 T a B5 X) = 2 ^ 2 * 5 * 7 * 29 ∧ 2 ^ 2 * 5 * 7 * 29 = 4060

section BurnsideJ10b


section


end


section


end


section


end


section


end


section


end

end BurnsideJ10b

section


end

@[expose] def J_5_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L V T : Subgroup G), RuType G L V T →
    ∀ V2 : Subgroup G, IsV2 V T V2 →
    ∀ g ∈ L2Ru L V2, g ∉ HRu T →
    ∀ v : G, v ∈ CFSG.conjugate (URu V T) g → v ∉ CFSG.conjugate (URu V T) g ⊓ QRu T →
    ∀ B5 : Subgroup G, IsSylowIn 5 B5 (HRu T) → InvertsGroup v B5 →
    ∀ X : Subgroup G, IsSylowIn 3 X (G2Ru L V2 T) →
    ∀ a : G, IsAChoice L V T V2 B5 a →
      ARu L V V2 T a ≤ Subgroup.normalizer ((B5 ⊔ Q5Ru T B5 : Subgroup G) : Set G) →
      Q5Ru T B5 ≤ Subgroup.normalizer ((X ⊔ ARu L V V2 T a : Subgroup G) : Set G) →
        ∃ δ : G ⧸ FRu L V V2 T a B5 X,
          Nat.card ↥(MulAction.orbit ↥(FRu L V V2 T a B5 X) δ) = 1755 ∧
          FRu L V V2 T a B5 X ⊓ MulAction.stabilizer G δ = F1Ru L V V2 T a B5 ∧
          pairStab G ((1 : G) : G ⧸ FRu L V V2 T a B5 X) δ =
            ((F1Ru L V V2 T a B5 ⊔ QRu T : Subgroup G) : Set G)

section


end

@[expose] def J_5_4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L V T : Subgroup G), RuType G L V T →
    ∀ V2 : Subgroup G, IsV2 V T V2 →
    ∀ g ∈ L2Ru L V2, g ∉ HRu T →
    ∀ v : G, v ∈ CFSG.conjugate (URu V T) g → v ∉ CFSG.conjugate (URu V T) g ⊓ QRu T →
    ∀ B5 : Subgroup G, IsSylowIn 5 B5 (HRu T) → InvertsGroup v B5 →
    ∀ X : Subgroup G, IsSylowIn 3 X (G2Ru L V2 T) →
    ∀ a : G, IsAChoice L V T V2 B5 a →
      ARu L V V2 T a ≤ Subgroup.normalizer ((B5 ⊔ Q5Ru T B5 : Subgroup G) : Set G) →
      Q5Ru T B5 ≤ Subgroup.normalizer ((X ⊔ ARu L V V2 T a : Subgroup G) : Set G) →
      ∀ δ : G ⧸ FRu L V V2 T a B5 X,
        Nat.card ↥(MulAction.orbit ↥(FRu L V V2 T a B5 X) δ) = 1755 →
        FRu L V V2 T a B5 X ⊓ MulAction.stabilizer G δ = F1Ru L V V2 T a B5 →
        pairStab G ((1 : G) : G ⧸ FRu L V V2 T a B5 X) δ =
          ((F1Ru L V V2 T a B5 ⊔ QRu T : Subgroup G) : Set G) →
        (∃ γ : G ⧸ FRu L V V2 T a B5 X,
          ((Set.univ : Set (G ⧸ FRu L V V2 T a B5 X)) =
              {((1 : G) : G ⧸ FRu L V V2 T a B5 X)} ∪ MulAction.orbit ↥(FRu L V V2 T a B5 X) δ ∪
                MulAction.orbit ↥(FRu L V V2 T a B5 X) γ ∧
            Nat.card ↥(MulAction.orbit ↥(FRu L V V2 T a B5 X) γ) = 2304 ∧
            IsL225Plus ↥(FRu L V V2 T a B5 X ⊓ MulAction.stabilizer G γ)) ∧
          ∃ S : Subgroup G,
            (S : Set G) = pairStab G ((1 : G) : G ⧸ FRu L V V2 T a B5 X) γ ∧
              Nonempty (↥S ≃* MulAut PSL(2, GaloisField 5 2))) ∧
        IsRudvalisRank3 G (G ⧸ FRu L V V2 T a B5 X)

section


end

@[expose] def J_5_5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Type) [Finite Ω] [MulAction G Ω] (ω δ γ : Ω),
    RudvalisSetting G Ω ω δ γ →
      ((DeltaAt G ω δ ω).ncard = 1755 ∧ (SigmaAt G ω γ ω).ncard = 2304 ∧
        (∀ ρ ∈ DeltaAt G ω δ ω, (DeltaAt G ω δ ω ∩ DeltaAt G ω δ ρ).ncard = 730) ∧
        (∀ ρ ∈ SigmaAt G ω γ ω, (DeltaAt G ω δ ω ∩ DeltaAt G ω δ ρ).ncard = 780)) ∧
      (∃ (T' M2 : Subgroup ↥(MulAction.stabilizer G ω)),
        CFSG.Quasithin.IsYAmalgamPair T'
          ((MulAction.stabilizer G ω ⊓ MulAction.stabilizer G δ).subgroupOf
            (MulAction.stabilizer G ω)) M2 ∧
        ∃ φ : Ω → ↥(MulAction.stabilizer G ω) ⧸
            (MulAction.stabilizer G ω ⊓ MulAction.stabilizer G δ).subgroupOf
              (MulAction.stabilizer G ω),
          Set.BijOn φ (DeltaAt G ω δ ω) Set.univ ∧
          (∀ f : ↥(MulAction.stabilizer G ω), ∀ ρ ∈ DeltaAt G ω δ ω, φ (f • ρ) = f • φ ρ) ∧
          φ δ = ((1 : ↥(MulAction.stabilizer G ω)) : ↥(MulAction.stabilizer G ω) ⧸
            (MulAction.stabilizer G ω ⊓ MulAction.stabilizer G δ).subgroupOf
              (MulAction.stabilizer G ω)) ∧
          ∀ ρ ∈ DeltaAt G ω δ ω, (ρ ∈ DeltaAt G ω δ δ ↔
            (0 < (incGraph ((MulAction.stabilizer G ω ⊓ MulAction.stabilizer G δ).subgroupOf
                (MulAction.stabilizer G ω)) M2).dist (Sum.inl (φ δ)) (Sum.inl (φ ρ)) ∧
              (incGraph ((MulAction.stabilizer G ω ⊓ MulAction.stabilizer G δ).subgroupOf
                (MulAction.stabilizer G ω)) M2).dist (Sum.inl (φ δ)) (Sum.inl (φ ρ)) < 8))) ∧
      (∃ a ∈ DeltaAt G ω δ ω ∩ DeltaAt G ω δ δ, ∃ b ∈ DeltaAt G ω δ ω ∩ DeltaAt G ω δ δ,
        ∃ c ∈ DeltaAt G ω δ ω ∩ DeltaAt G ω δ δ,
        DeltaAt G ω δ ω ∩ DeltaAt G ω δ δ =
          MulAction.orbit ↥(MulAction.stabilizer G ω ⊓ MulAction.stabilizer G δ) a ∪
            MulAction.orbit ↥(MulAction.stabilizer G ω ⊓ MulAction.stabilizer G δ) b ∪
            MulAction.orbit ↥(MulAction.stabilizer G ω ⊓ MulAction.stabilizer G δ) c ∧
        (MulAction.orbit ↥(MulAction.stabilizer G ω ⊓ MulAction.stabilizer G δ) a).ncard = 10 ∧
        (MulAction.orbit ↥(MulAction.stabilizer G ω ⊓ MulAction.stabilizer G δ) b).ncard = 80 ∧
        (MulAction.orbit ↥(MulAction.stabilizer G ω ⊓ MulAction.stabilizer G δ) c).ncard = 640 ∧
        Disjoint (MulAction.orbit ↥(MulAction.stabilizer G ω ⊓ MulAction.stabilizer G δ) a)
          (MulAction.orbit ↥(MulAction.stabilizer G ω ⊓ MulAction.stabilizer G δ) b) ∧
        Disjoint (MulAction.orbit ↥(MulAction.stabilizer G ω ⊓ MulAction.stabilizer G δ) a)
          (MulAction.orbit ↥(MulAction.stabilizer G ω ⊓ MulAction.stabilizer G δ) c) ∧
        Disjoint (MulAction.orbit ↥(MulAction.stabilizer G ω ⊓ MulAction.stabilizer G δ) b)
          (MulAction.orbit ↥(MulAction.stabilizer G ω ⊓ MulAction.stabilizer G δ) c)) ∧
      ((DeltaAt G ω δ ω ∩ DeltaAt G ω δ γ).ncard = 780 ∧
        (∀ σ ∈ DeltaAt G ω δ ω ∩ DeltaAt G ω δ γ, ∀ τ ∈ DeltaAt G ω δ ω ∩ DeltaAt G ω δ γ,
          ∃ f ∈ MulAction.stabilizer G ω ⊓ MulAction.stabilizer G γ, f • σ = τ) ∧
        (DeltaAt G ω δ ω ∩ SigmaAt G ω γ γ).ncard = 975 ∧
        (∀ σ ∈ DeltaAt G ω δ ω ∩ SigmaAt G ω γ γ, ∀ τ ∈ DeltaAt G ω δ ω ∩ SigmaAt G ω γ γ,
          ∃ f ∈ MulAction.stabilizer G ω ⊓ MulAction.stabilizer G γ, f • σ = τ) ∧
        (∀ σ ∈ DeltaAt G ω δ ω ∩ DeltaAt G ω δ γ,
          Nonempty (↥(MulAction.stabilizer G ω ⊓ MulAction.stabilizer G γ ⊓
            MulAction.stabilizer G σ) ≃* Sz 0)) ∧
        (∀ τ ∈ DeltaAt G ω δ ω ∩ SigmaAt G ω γ γ,
          IsSylowTwoIn (MulAction.stabilizer G ω ⊓ MulAction.stabilizer G γ ⊓
            MulAction.stabilizer G τ) (MulAction.stabilizer G ω ⊓ MulAction.stabilizer G γ))) ∧
      ((DeltaAt G ω δ γ ∩ SigmaAt G ω γ ω).ncard = 975 ∧
        (∀ σ ∈ DeltaAt G ω δ γ ∩ SigmaAt G ω γ ω, ∀ τ ∈ DeltaAt G ω δ γ ∩ SigmaAt G ω γ ω,
          ∃ f ∈ MulAction.stabilizer G ω ⊓ MulAction.stabilizer G γ, f • σ = τ) ∧
        ∀ ρ ∈ SigmaAt G ω γ ω,
          (MulAction.orbit ↥(MulAction.stabilizer G ω ⊓ MulAction.stabilizer G γ) ρ).ncard = 975 →
            MulAction.orbit ↥(MulAction.stabilizer G ω ⊓ MulAction.stabilizer G γ) ρ =
              DeltaAt G ω δ γ ∩ SigmaAt G ω γ ω)

section BurnsideJ55


section ModelE

open CFSG.Quasithin.RuRank3 CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.RuSchreier (ruP genSubgroup)


section


end

section


end

section


end


section


end

section


end

section


end


section


end

section


end

private theorem burnsideJ55_mem_ruR0 {p : Equiv.Perm (Fin 4060)} : p ∈ ruR0 ↔ p ∈ ruP ∧ p 0 = 0
    := by
  unfold ruR0
  rw [Subgroup.mem_inf, MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def]


section


end


section


end

section


end

section


end

section


end


section


end


section


end


section


end


section


end


section


end

section


end

section


end

section


end

section


end

section


end

section


end

section


end

end ModelE

section Frob20

variable {X : Type} [Group X]


end Frob20

section IncGraph

variable {Y : Type} [Group Y] (M1 M2 : Subgroup Y)


end IncGraph

section BurnsideJ55PartA

open CFSG.Open CFSG.Blueprint
open scoped MatrixGroups

section Copied


section


end


end Copied


section Transport

open CFSG.Quasithin.RuRank3 CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.RuSchreier (ruP)

structure burnsideJ55_Tr (G Ω : Type) [Group G] [MulAction G Ω] (ω δ : Ω) where
  Φ : Ω ≃ Fin 4060
  σ : G →* Equiv.Perm (Fin 4060)
  hω : Φ ω = 0
  hδ : Φ δ = 1
  hadj : ∀ z y, orbAdj G ω δ z y ↔ ruAdj (Φ z) (Φ y)
  hact : ∀ g z, Φ (g • z) = σ g (Φ z)
  hinj : Function.Injective σ
  hrange : σ.range = ruP

section


end


section

variable {G Ω : Type} [Group G] [MulAction G Ω] {ω δ : Ω} (T : burnsideJ55_Tr G Ω ω δ)

theorem burnsideJ55_Tr.σ_mem (g : G) : T.σ g ∈ ruP := by
  rw [← T.hrange]
  exact ⟨g, rfl⟩


theorem burnsideJ55_Tr.mem_stabilizer_iff (g : G) (x : Ω) :
    g ∈ MulAction.stabilizer G x ↔ T.σ g (T.Φ x) = T.Φ x := by
  rw [MulAction.mem_stabilizer_iff, ← T.Φ.injective.eq_iff, T.hact]


section


end


end

end Transport

section Transport2

open CFSG.Quasithin.RuRank3 CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.RuSchreier (ruP)

section

variable {G Ω : Type} [Group G] [MulAction G Ω] {ω δ : Ω} (T : burnsideJ55_Tr G Ω ω δ)

section


end

end

end Transport2

section Part1

open CFSG.Quasithin.RuRank3 CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.RuSchreier (ruP)

section


end

end Part1

section Part3

open CFSG.Quasithin.RuRank3 CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.RuSchreier (ruP)

section


end

end Part3

section Part4

open CFSG.Quasithin.RuRank3 CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.RuSchreier (ruP)

section


end

end Part4

section Part5

open CFSG.Quasithin.RuRank3 CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.RuSchreier (ruP)

section


end

end Part5

end BurnsideJ55PartA

section J513Facts

open CFSG.Quasithin.RuRank3 CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.RuSchreier (ruP)


section

variable {G Ω : Type} [Group G] [MulAction G Ω] {ω δ : Ω} (T : burnsideJ55_Tr G Ω ω δ)


section


end


section


end

end

end J513Facts

section OmegaPrimeAdj

variable {F : Type} [Group F] (M1 M2 E : Subgroup F)


end OmegaPrimeAdj


section J513Main

open CFSG.Quasithin.RuRank3 CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.RuSchreier (ruP)

section


end

end J513Main

section Octagon

variable {Y : Type} [Group Y] {X : Type} [MulAction Y X]


end Octagon


section Ball

open CFSG.Sporadic.Schreier.Tits CFSG.Quasithin.RuRank3

section


end

end Ball

section TitsSide

open CFSG.Sporadic.Schreier.Tits CFSG.Quasithin CFSG.Quasithin.RuType CFSG.Quasithin.RuRank3

section


end

section


end

end TitsSide


section FSide

open CFSG.Quasithin.RuRank3 CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.RuSchreier (ruP)

section

variable {G Ω : Type} [Group G] [MulAction G Ω] {ω δ : Ω} (T : burnsideJ55_Tr G Ω ω δ)

theorem burnsideJ55_Tr.σ_mem_ruR0 (f : ↥(MulAction.stabilizer G ω)) : T.σ f ∈ ruR0 :=
  burnsideJ55_mem_ruR0.2 ⟨T.σ_mem f, by
    rw [← T.hω, ← T.hact, MulAction.mem_stabilizer_iff.1 f.2]⟩

@[expose] noncomputable def burnsideJ55_Tr.σ0 : ↥(MulAction.stabilizer G ω) →* ruR0 :=
  (T.σ.comp (MulAction.stabilizer G ω).subtype).codRestrict ruR0 T.σ_mem_ruR0

section

@[expose] noncomputable def burnsideJ55_Tr.ρ : ↥(MulAction.stabilizer G ω) →* Equiv.Perm (Fin 1755) :=
  (Subgroup.subtype CFSG.Sporadic.Schreier.Tits.titsA).comp (ruR0Equiv.toMonoidHom.comp T.σ0)


end

section


end

end

section


end

section


end

end FSide

end BurnsideJ55

section


end

@[expose] def J_5_6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Type) [Finite Ω] [MulAction G Ω] (ω δ γ : Ω),
    RudvalisSetting G Ω ω δ γ →
      ∀ σ : Ω ≃ Ω, ((∀ ρ τ : Ω, τ ∈ DeltaAt G ω δ ρ ↔ σ τ ∈ DeltaAt G ω δ (σ ρ)) ↔
        ∃ g : G, ∀ ρ : Ω, σ ρ = g • ρ)

section BurnsideJ11b


end BurnsideJ11b

section


end

@[expose] def J_5_14 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Type) [Finite Ω] [MulAction G Ω],
    IsRudvalisRank3 G Ω → NativeSporadic.IsSporadic G .Ru

section


end

open CFSG.Open CFSG.Blueprint CFSG.ASVolI.ChIJK
open scoped MatrixGroups

@[expose] def J_5_7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Type) [Finite Ω] [MulAction G Ω] (ω δ γ : Ω)
    (M2 : Subgroup ↥(MulAction.stabilizer G ω))
    (φ : Ω → ↥(MulAction.stabilizer G ω) ⧸ FdOf G ω δ), RuBuilding G Ω ω δ γ M2 φ →
      (thetaAt G ω δ δ = {u | u ∈ DeltaAt G ω δ ω ∩ DeltaAt G ω δ δ ∧
          (DeltaAt G ω δ u ∩ DeltaAt G ω δ ω ∩ SigmaAt G ω γ δ).ncard = 2 ^ 9} ∧
        2 * 2 ^ 9 = (DeltaAt G ω δ ω ∩ SigmaAt G ω γ δ).ncard) ∧
      (∀ u ∈ thetaAt G ω δ δ,
        ∃! l : ↥(MulAction.stabilizer G ω) ⧸ M2,
          (incGraph (FdOf G ω δ) M2).Adj (Sum.inl (φ δ)) (Sum.inr l) ∧
          (incGraph (FdOf G ω δ) M2).Adj (Sum.inl (φ u)) (Sum.inr l)) ∧
      (∀ u ∈ thetaAt G ω δ δ, ∀ l : ↥(MulAction.stabilizer G ω) ⧸ M2,
        (incGraph (FdOf G ω δ) M2).Adj (Sum.inl (φ δ)) (Sum.inr l) →
        (incGraph (FdOf G ω δ) M2).Adj (Sum.inl (φ u)) (Sum.inr l) →
          ∃! u' : Ω, u' ∈ DeltaAt G ω δ ω ∧
            (incGraph (FdOf G ω δ) M2).Adj (Sum.inl (φ u')) (Sum.inr l) ∧
            u' ≠ δ ∧ u' ≠ u) ∧
      ∀ u ∈ thetaAt G ω δ δ, ∀ (l : ↥(MulAction.stabilizer G ω) ⧸ M2) (u' : Ω),
        u' ∈ DeltaAt G ω δ ω →
        (incGraph (FdOf G ω δ) M2).Adj (Sum.inl (φ δ)) (Sum.inr l) →
        (incGraph (FdOf G ω δ) M2).Adj (Sum.inl (φ u)) (Sum.inr l) →
        (incGraph (FdOf G ω δ) M2).Adj (Sum.inl (φ u')) (Sum.inr l) → u' ≠ δ → u' ≠ u →
          u' ∈ thetaAt G ω δ δ ∧
          ∀ w ∈ thetaAt G ω δ δ,
            (DeltaAt G ω δ w ∩ DeltaAt G ω δ ω ∩ SigmaAt G ω γ δ =
              (DeltaAt G ω δ ω ∩ SigmaAt G ω γ δ) \
                (DeltaAt G ω δ u ∩ DeltaAt G ω δ ω ∩ SigmaAt G ω γ δ) ↔ w = u')

section BurnsideJ57

section BurnsideJ57All

open CFSG.ASVolI.ChIJK

section BurnsideJ57PartA

open CFSG.Quasithin.H13.F45Ru

section BurnsideJ57Generic

variable {V : Type} {Γ : SimpleGraph V}


end BurnsideJ57Generic

section BurnsideJ57Count

variable {V : Type} (Γ : SimpleGraph V) (b : V)


variable {Γ b}


end BurnsideJ57Count

end BurnsideJ57PartA

section BurnsideJ57PartB

open CFSG.Quasithin.H13.F45Ru CFSG.RuF45 CFSG.Sporadic.Schreier.Tits CFSG.Monster.B.Co2

  CFSG.Sporadic.Schreier.Tits CFSG.Monster.B.Co2


section Oct


end Oct

section OctLam


end OctLam

section OctTheta


end OctTheta

section OctAll


end OctAll

section OctData


end OctData

section OctData12


end OctData12

section OctData7


end OctData7

end BurnsideJ57PartB

section BurnsideJ57PartC

open CFSG.Quasithin.H13.F45Ru

section Transport

variable {A B A' B' : Type} {Γ : SimpleGraph (A ⊕ B)} {Γ' : SimpleGraph (A' ⊕ B')}


end Transport

section CosetIso

variable {F X Y : Type} [Group F]


end CosetIso

end BurnsideJ57PartC

section BurnsideJ57Pair

open CFSG.Quasithin CFSG.QuasithinUnique


end BurnsideJ57Pair

section BurnsideJ57Flag

open CFSG.Sporadic.Schreier.Tits


end BurnsideJ57Flag

section BurnsideJ57Std

open CFSG.Sporadic.Schreier.Tits CFSG.Quasithin CFSG.Quasithin.RuType CFSG.Quasithin.RuRank3


end BurnsideJ57Std

section BurnsideJ57Bridge

open CFSG.Sporadic.Schreier.Tits CFSG.Quasithin CFSG.Quasithin.RuType CFSG.Quasithin.RuRank3 CFSG.Quasithin.H13.F45Ru CFSG.RuF45


end BurnsideJ57Bridge

section BurnsideJ57Ru

variable {G Ω : Type} [Group G] [MulAction G Ω]


variable {ω δ γ : Ω} {M2 : Subgroup ↥(MulAction.stabilizer G ω)}
  {φ : Ω → ↥(MulAction.stabilizer G ω) ⧸ FdOf G ω δ}


end BurnsideJ57Ru

section BurnsideJ57Main

variable {G Ω : Type} [Group G] [MulAction G Ω] {ω δ γ : Ω}
  {M2 : Subgroup ↥(MulAction.stabilizer G ω)}
  {φ : Ω → ↥(MulAction.stabilizer G ω) ⧸ FdOf G ω δ}


end BurnsideJ57Main

section BurnsideJ57Count3


end BurnsideJ57Count3

section BurnsideJ57Theta

variable {G Ω : Type} [Group G] [MulAction G Ω] {ω δ γ : Ω}
  {M2 : Subgroup ↥(MulAction.stabilizer G ω)}
  {φ : Ω → ↥(MulAction.stabilizer G ω) ⧸ FdOf G ω δ}


end BurnsideJ57Theta

section BurnsideJ57Theta2

variable {G Ω : Type} [Group G] [Finite G] [MulAction G Ω] [Finite Ω] {ω δ γ : Ω}
  {M2 : Subgroup ↥(MulAction.stabilizer G ω)}
  {φ : Ω → ↥(MulAction.stabilizer G ω) ⧸ FdOf G ω δ}


end BurnsideJ57Theta2

section BurnsideJ57Seven

variable {G Ω : Type} [Group G] [MulAction G Ω] {ω δ γ : Ω}
  {M2 : Subgroup ↥(MulAction.stabilizer G ω)}
  {φ : Ω → ↥(MulAction.stabilizer G ω) ⧸ FdOf G ω δ}


end BurnsideJ57Seven

section BurnsideJ57Data


end BurnsideJ57Data

end BurnsideJ57All

end BurnsideJ57

section
open CFSG.ASVolI.ChIJK


end

@[expose] def J_5_8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Type) [Finite Ω] [MulAction G Ω] (ω δ γ : Ω)
    (M2 : Subgroup ↥(MulAction.stabilizer G ω))
    (φ : Ω → ↥(MulAction.stabilizer G ω) ⧸ FdOf G ω δ), RuBuilding G Ω ω δ γ M2 φ →
      ∀ u ∈ DeltaAt G ω δ ω ∩ DeltaAt G ω δ δ,
        ∃ pmap : Ω → Σ b : (↥(MulAction.stabilizer G ω) ⧸ FdOf G ω δ ⊕
            ↥(MulAction.stabilizer G ω) ⧸ M2),
            (incGraph (FdOf G ω δ) M2).Walk (Sum.inl (φ u)) b,
          (∀ v ∈ LambdaAt G ω δ γ u,
            (pmap v).1 = Sum.inl (φ v) ∧
            (pmap v).2.length = (incGraph (FdOf G ω δ) M2).dist (Sum.inl (φ u)) (Sum.inl (φ v)) ∧
            ∀ q : (incGraph (FdOf G ω δ) M2).Walk (Sum.inl (φ u)) (Sum.inl (φ v)),
              q.length = (incGraph (FdOf G ω δ) M2).dist (Sum.inl (φ u)) (Sum.inl (φ v)) →
                (⟨Sum.inl (φ v), q⟩ : Σ b : (↥(MulAction.stabilizer G ω) ⧸ FdOf G ω δ ⊕
                  ↥(MulAction.stabilizer G ω) ⧸ M2),
                    (incGraph (FdOf G ω δ) M2).Walk (Sum.inl (φ u)) b) = pmap v) ∧
          Set.BijOn pmap (LambdaAt G ω δ γ u)
            (GeoFrom (incGraph (FdOf G ω δ) M2) (Sum.inl (φ u))
              ((fun v => (Sum.inl (φ v) : ↥(MulAction.stabilizer G ω) ⧸ FdOf G ω δ ⊕
                ↥(MulAction.stabilizer G ω) ⧸ M2)) '' LambdaAt G ω δ γ u))

section
open CFSG.ASVolI.ChIJK


end

@[expose] def J_5_9 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Type) [Finite Ω] [MulAction G Ω] (ω δ γ : Ω)
    (M2 : Subgroup ↥(MulAction.stabilizer G ω))
    (φ : Ω → ↥(MulAction.stabilizer G ω) ⧸ FdOf G ω δ), RuBuilding G Ω ω δ γ M2 φ →
      ∀ y : (↥(MulAction.stabilizer G ω) ⧸ FdOf G ω δ ⊕ ↥(MulAction.stabilizer G ω) ⧸ M2),
        ∀ e : ℕ, (incGraph (FdOf G ω δ) M2).dist (Sum.inl (φ δ)) y = e → 0 < e → e < 8 →
          ∃! y', (incGraph (FdOf G ω δ) M2).Adj y y' ∧
            (incGraph (FdOf G ω δ) M2).dist (Sum.inl (φ δ)) y' = e - 1

section
open CFSG.ASVolI.ChIJK


end

@[expose] def J_5_10 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Type) [Finite Ω] [MulAction G Ω] (ω δ γ : Ω)
    (M2 : Subgroup ↥(MulAction.stabilizer G ω))
    (φ : Ω → ↥(MulAction.stabilizer G ω) ⧸ FdOf G ω δ), RuBuilding G Ω ω δ γ M2 φ →
      ∀ u ∈ DeltaAt G ω δ ω ∩ DeltaAt G ω δ δ, ∀ v ∈ LambdaAt G ω δ γ u,
        ∀ p : (incGraph (FdOf G ω δ) M2).Walk (Sum.inl (φ u)) (Sum.inl (φ v)),
          p.length = (incGraph (FdOf G ω δ) M2).dist (Sum.inl (φ u)) (Sum.inl (φ v)) →
            (p.getVert 0 = Sum.inl (φ u) ∧ p.length ≤ 6 ∧
              dseq (incGraph (FdOf G ω δ) M2) (Sum.inl (φ δ)) p 0 =
                (incGraph (FdOf G ω δ) M2).dist (Sum.inl (φ δ)) (Sum.inl (φ u)) ∧
              (∀ i, i ≤ p.length → dseq (incGraph (FdOf G ω δ) M2) (Sum.inl (φ δ)) p i ≤ 8) ∧
              dseq (incGraph (FdOf G ω δ) M2) (Sum.inl (φ δ)) p p.length = 8) ∧
            (∀ i, i < p.length →
              dseq (incGraph (FdOf G ω δ) M2) (Sum.inl (φ δ)) p i <
                dseq (incGraph (FdOf G ω δ) M2) (Sum.inl (φ δ)) p (i + 1) →
              WalkIncreases (incGraph (FdOf G ω δ) M2) (Sum.inl (φ δ)) p i
                (min (i + 8 - dseq (incGraph (FdOf G ω δ) M2) (Sum.inl (φ δ)) p i) p.length)) ∧
            (∀ i, i ≤ p.length →
              dseq (incGraph (FdOf G ω δ) M2) (Sum.inl (φ δ)) p i + (p.length - i) = 8 →
              WalkIncreases (incGraph (FdOf G ω δ) M2) (Sum.inl (φ δ)) p i p.length) ∧
            ((incGraph (FdOf G ω δ) M2).dist (Sum.inl (φ δ)) (Sum.inl (φ u)) = 4 →
              ((p.length = 4 ∧ WalkIncreases (incGraph (FdOf G ω δ) M2) (Sum.inl (φ δ)) p 0 4) ∨
                (p.length = 6 ∧ WalkIncreases (incGraph (FdOf G ω δ) M2) (Sum.inl (φ δ)) p 0 4 ∧
                  dseq (incGraph (FdOf G ω δ) M2) (Sum.inl (φ δ)) p 5 = 7) ∨
                (p.length = 6 ∧ dseq (incGraph (FdOf G ω δ) M2) (Sum.inl (φ δ)) p 1 = 3 ∧
                  WalkIncreases (incGraph (FdOf G ω δ) M2) (Sum.inl (φ δ)) p 1 6))) ∧
            ((incGraph (FdOf G ω δ) M2).dist (Sum.inl (φ δ)) (Sum.inl (φ u)) = 6 →
              ((∀ i, 0 < i → i ≤ p.length →
                  7 ≤ dseq (incGraph (FdOf G ω δ) M2) (Sum.inl (φ δ)) p i) ∨
                (dseq (incGraph (FdOf G ω δ) M2) (Sum.inl (φ δ)) p 4 = 6 ∧
                  ∀ i, i ≤ p.length → i ≠ 0 → i ≠ 4 →
                    7 ≤ dseq (incGraph (FdOf G ω δ) M2) (Sum.inl (φ δ)) p i) ∨
                (dseq (incGraph (FdOf G ω δ) M2) (Sum.inl (φ δ)) p 1 = 5 ∧
                  ∀ i, i ≤ p.length → i ≠ 1 →
                    6 ≤ dseq (incGraph (FdOf G ω δ) M2) (Sum.inl (φ δ)) p i) ∨
                (dseq (incGraph (FdOf G ω δ) M2) (Sum.inl (φ δ)) p 2 = 4 ∧
                  WalkIncreases (incGraph (FdOf G ω δ) M2) (Sum.inl (φ δ)) p 2 6)))

section
open CFSG.ASVolI.ChIJK


end

@[expose] def J_5_11 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Type) [Finite Ω] [MulAction G Ω] (ω δ γ : Ω)
    (M2 : Subgroup ↥(MulAction.stabilizer G ω))
    (φ : Ω → ↥(MulAction.stabilizer G ω) ⧸ FdOf G ω δ), RuBuilding G Ω ω δ γ M2 φ →
      ∀ y : (↥(MulAction.stabilizer G ω) ⧸ FdOf G ω δ ⊕ ↥(MulAction.stabilizer G ω) ⧸ M2),
        ∀ e : ℕ, (incGraph (FdOf G ω δ) M2).Reachable (Sum.inl (φ δ)) y →
          (incGraph (FdOf G ω δ) M2).dist (Sum.inl (φ δ)) y = e → e < 8 →
          (e = 0 →
            (NgeoSet (incGraph (FdOf G ω δ) M2) (Sum.inl (φ δ)) y e).ncard = 5120 ∧
            ∀ y' ∈ (incGraph (FdOf G ω δ) M2).neighborSet y,
              (incGraph (FdOf G ω δ) M2).dist (Sum.inl (φ δ)) y' = e + 1 →
                {q ∈ NgeoSet (incGraph (FdOf G ω δ) M2) (Sum.inl (φ δ)) y e |
                  y' ∉ q.2.support}.ncard = 4096) ∧
          (0 < e → Even e →
            (NgeoSet (incGraph (FdOf G ω δ) M2) (Sum.inl (φ δ)) y e).ncard = 8 ^ ((8 - e) / 2) ∧
            ∀ y' ∈ (incGraph (FdOf G ω δ) M2).neighborSet y,
              (incGraph (FdOf G ω δ) M2).dist (Sum.inl (φ δ)) y' = e + 1 →
                {q ∈ NgeoSet (incGraph (FdOf G ω δ) M2) (Sum.inl (φ δ)) y e |
                  y' ∉ q.2.support}.ncard = 6 * 8 ^ ((6 - e) / 2)) ∧
          (Odd e →
            (NgeoSet (incGraph (FdOf G ω δ) M2) (Sum.inl (φ δ)) y e).ncard = 2 * 8 ^ ((7 - e) / 2) ∧
            ∀ y' ∈ (incGraph (FdOf G ω δ) M2).neighborSet y,
              (incGraph (FdOf G ω δ) M2).dist (Sum.inl (φ δ)) y' = e + 1 →
                {q ∈ NgeoSet (incGraph (FdOf G ω δ) M2) (Sum.inl (φ δ)) y e |
                  y' ∉ q.2.support}.ncard = 8 ^ ((7 - e) / 2))

section
open CFSG.ASVolI.ChIJK


end

@[expose] def J_5_12 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Type) [Finite Ω] [MulAction G Ω] (ω δ γ : Ω)
    (M2 : Subgroup ↥(MulAction.stabilizer G ω))
    (φ : Ω → ↥(MulAction.stabilizer G ω) ⧸ FdOf G ω δ), RuBuilding G Ω ω δ γ M2 φ →
      ∀ d : ℕ, (d = 2 ∨ d = 4 ∨ d = 6) → ∀ u ∈ DeltaAt G ω δ ω,
        (incGraph (FdOf G ω δ) M2).dist (Sum.inl (φ δ)) (Sum.inl (φ u)) = d →
          (LambdaAt G ω δ γ u).ncard ≤ 2 ^ 9 ∧ ((LambdaAt G ω δ γ u).ncard = 2 ^ 9 ↔ d = 2)

section
open CFSG.ASVolI.ChIJK


end

@[expose] def J_5_13 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Type) [Finite Ω] [MulAction G Ω] (ω δ γ : Ω)
    (M2 : Subgroup ↥(MulAction.stabilizer G ω))
    (φ : Ω → ↥(MulAction.stabilizer G ω) ⧸ FdOf G ω δ), RuBuilding G Ω ω δ γ M2 φ →
      Nonempty (omegaGraph G ω δ ≃g
        OmegaPrime ↥(MulAction.stabilizer G ω) (FdOf G ω δ) M2
          ((MulAction.stabilizer G ω ⊓ MulAction.stabilizer G γ).subgroupOf
            (MulAction.stabilizer G ω)))

section


end

end CFSG.ASVolI
