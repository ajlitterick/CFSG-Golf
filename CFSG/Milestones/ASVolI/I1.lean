module

public import CFSG.Quasithin.Background.ASVolIRegistered
public import CFSG.LocalAnalysis.SectionRank.QTK.Main
public import CFSG.LocalAnalysis.ComponentClassification.SymmetricLocalLinearFourTwo
public import CFSG.LocalAnalysis.ComponentInitial.FieldNineAlternatingSix
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.TrivialRows
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.RankThree.PartOne.LIT.RankPSL3
public import CFSG.ClassicalInvolution.Orders.Classical
public import CFSG.Timmesfeld.Orders.Classical
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434RemG24
public import CFSG.RankThree.Chevalley.EvenRealThreeCentralizingInvolution
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.Sporadic.Recognition.HNMultiplier

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ASVolI.ChIJK

open CFSG.Open CFSG.Blueprint
open scoped MatrixGroups

@[expose] noncomputable def h1Dim {G V : Type} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) : ℕ :=
  Module.finrank (ZMod 2) (groupCohomology (Rep.of ρ) 1)

@[expose] noncomputable def permRepF2 (n : ℕ) :
    Representation (ZMod 2) (Equiv.Perm (Fin n)) (Fin n → ZMod 2) where
  toFun σ := LinearMap.funLeft (ZMod 2) (ZMod 2) (σ.symm : Fin n → Fin n)
  map_one' := by
    refine LinearMap.ext fun v => funext fun i => ?_
    simp [LinearMap.funLeft]
    rfl
  map_mul' σ τ := by
    refine LinearMap.ext fun v => funext fun i => ?_
    simp [LinearMap.funLeft, Equiv.Perm.mul_def]

@[expose] def evenWeight (n : ℕ) : Submodule (ZMod 2) (Fin n → ZMod 2) where
  carrier := {v | ∑ i, v i = 0}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, Pi.add_apply, Finset.sum_add_distrib] at ha hb ⊢
    rw [ha, hb, add_zero]
  zero_mem' := by simp
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_ofPred_eq, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum] at hx ⊢
    rw [hx, mul_zero]

theorem evenWeight_inv (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    evenWeight n ≤ (evenWeight n).comap (permRepF2 n σ) := by
  intro v hv
  have hv' : ∑ i, v i = 0 := hv
  show ∑ i, (permRepF2 n σ v) i = 0
  have : (∑ i : Fin n, (permRepF2 n σ v) i) = ∑ i : Fin n, v i := by
    simp only [permRepF2, MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.funLeft_apply]
    exact Equiv.sum_comp σ.symm v
  rw [this]; exact hv'

@[expose] noncomputable def evenWeightRep (n : ℕ) :
    Representation (ZMod 2) (Equiv.Perm (Fin n)) (evenWeight n) :=
  (permRepF2 n).subrepresentation (evenWeight n) (evenWeight_inv n)

@[expose] def constInEven (n : ℕ) : Submodule (ZMod 2) (evenWeight n) :=
  (Submodule.span (ZMod 2) {fun _ : Fin n => (1 : ZMod 2)}).comap (evenWeight n).subtype

theorem constInEven_inv (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    constInEven n ≤ (constInEven n).comap (evenWeightRep n σ) := by
  intro v hv
  have hv' : (v : Fin n → ZMod 2) ∈
      Submodule.span (ZMod 2) {fun _ : Fin n => (1 : ZMod 2)} := hv
  rw [Submodule.mem_span_singleton] at hv'
  obtain ⟨c, hc⟩ := hv'
  show ((evenWeightRep n σ v : evenWeight n) : Fin n → ZMod 2) ∈
    Submodule.span (ZMod 2) {fun _ : Fin n => (1 : ZMod 2)}
  rw [Submodule.mem_span_singleton]
  refine ⟨c, ?_⟩
  funext i
  have := congrFun hc (σ.symm i)
  simpa [evenWeightRep, permRepF2, LinearMap.funLeft] using this

@[expose] noncomputable def symNaturalRep (n : ℕ) :
    Representation (ZMod 2) (Equiv.Perm (Fin n)) (evenWeight n ⧸ constInEven n) :=
  (evenWeightRep n).quotient (constInEven n) (constInEven_inv n)

@[expose] noncomputable def altNaturalRep (n : ℕ) :
    Representation (ZMod 2) (alternatingGroup (Fin n)) (evenWeight n ⧸ constInEven n) :=
  (symNaturalRep n).comp (alternatingGroup (Fin n)).subtype

@[expose] noncomputable def slNaturalRep (n : ℕ) (K : Type) [Field K] [Algebra (ZMod 2) K] :
    Representation (ZMod 2) SL(n, K) (Fin n → K) :=
  quasithinH1MatrixRep (quasithinH1SLMatrix n K)

@[expose] def sp4Derived (K : Type) [Field K] : Subgroup (Matrix.symplecticGroup (Fin 2) K) :=
  commutator (Matrix.symplecticGroup (Fin 2) K)

@[expose] noncomputable def sp4NaturalRep (K : Type) [Field K] [Algebra (ZMod 2) K] :
    Representation (ZMod 2) (sp4Derived K) (Fin 2 ⊕ Fin 2 → K) :=
  quasithinH1MatrixRep ((Matrix.symplecticGroup (Fin 2) K).subtype.comp (sp4Derived K).subtype)

@[expose] noncomputable def orthMinusRep (K : Type) [Field K] [Algebra (ZMod 2) K] (b c : K) :
    Representation (ZMod 2) (StatedOmega (StatedQuadMinus 2 K b c))
      (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K) :=
  quasithinH1MatrixRep ((Units.coeHom _).comp (StatedOmega (StatedQuadMinus 2 K b c)).subtype)

section Zorn

variable (K : Type) [Field K]

@[expose] def zornOne : quasithinZorn K := (1, 0, 0, 1)

@[expose] def zornTrace (x : quasithinZorn K) : K := x.1 + x.2.2.2

@[expose] def zornNorm (x : quasithinZorn K) : K := x.1 * x.2.2.2 - ∑ i, x.2.1 i * x.2.2.1 i

theorem cross_zero_right (u : Fin 3 → K) : quasithinCross u 0 = 0 := by
  ext i; fin_cases i <;> simp [quasithinCross]

theorem cross_zero_left (u : Fin 3 → K) : quasithinCross 0 u = 0 := by
  ext i; fin_cases i <;> simp [quasithinCross]

theorem cross_self (u : Fin 3 → K) : quasithinCross u u = 0 := by
  ext i; fin_cases i <;> simp [quasithinCross] <;> ring

theorem zornMul_one_left (y : quasithinZorn K) : quasithinZornMul (zornOne K) y = y := by
  obtain ⟨a, u, v, b⟩ := y
  simp [zornOne, quasithinZornMul, cross_zero_left]

theorem zornMul_one_right (y : quasithinZorn K) : quasithinZornMul y (zornOne K) = y := by
  obtain ⟨a, u, v, b⟩ := y
  simp [zornOne, quasithinZornMul, cross_zero_right]

theorem zornMul_self (x : quasithinZorn K) :
    quasithinZornMul x x = zornTrace K x • x - zornNorm K x • zornOne K := by
  obtain ⟨a, u, v, b⟩ := x
  simp only [zornOne, zornTrace, zornNorm, quasithinZornMul, cross_self]
  ext i <;> simp [mul_comm] <;> ring

theorem g2_gen (g : quasithinZorn K ≃ₗ[K] quasithinZorn K)
    (hg : ∀ x y, g (quasithinZornMul x y) = quasithinZornMul (g x) (g y)) :
    g (zornOne K) = zornOne K ∧ ∀ x, zornTrace K (g x) = zornTrace K x := by
  have h1 : g (zornOne K) = zornOne K := by
    obtain ⟨y, hy⟩ := g.surjective (zornOne K)
    have := hg (zornOne K) y
    rw [zornMul_one_left, hy, zornMul_one_right] at this
    exact this.symm
  refine ⟨h1, fun x => ?_⟩
  by_contra hne
  have e1 : quasithinZornMul (g x) (g x) =
      zornTrace K x • g x - zornNorm K x • zornOne K := by
    rw [← hg, zornMul_self, map_sub, map_smul, map_smul, h1]
  have e2 := zornMul_self K (g x)
  have hne' : zornTrace K (g x) - zornTrace K x ≠ 0 := sub_ne_zero.mpr hne
  have e3 : (zornTrace K (g x) - zornTrace K x) • g x =
      (zornNorm K (g x) - zornNorm K x) • zornOne K := by
    rw [sub_smul, sub_smul]
    exact sub_eq_sub_iff_sub_eq_sub.mp (e2.symm.trans e1)
  set c : K := (zornTrace K (g x) - zornTrace K x)⁻¹ * (zornNorm K (g x) - zornNorm K x) with hc
  have e4 : g x = c • zornOne K := by
    have := congrArg (fun z => (zornTrace K (g x) - zornTrace K x)⁻¹ • z) e3
    simp only [smul_smul, inv_mul_cancel₀ hne', one_smul] at this
    rw [this, hc]
  have e5 : x = c • zornOne K := by
    apply g.injective
    rw [e4, map_smul, h1]
  apply hne
  rw [e4]
  conv_rhs => rw [e5]

theorem g2_inv (g : quasithinZorn K ≃ₗ[K] quasithinZorn K) (hg : g ∈ quasithinG2 K) :
    g (zornOne K) = zornOne K ∧ ∀ x, zornTrace K (g x) = zornTrace K x := by
  induction hg using Subgroup.closure_induction with
  | mem g hg' => exact g2_gen K g hg'
  | one => exact ⟨rfl, fun x => rfl⟩
  | mul g h _ _ ihg ihh =>
    refine ⟨?_, fun x => ?_⟩
    · show g (h (zornOne K)) = zornOne K
      rw [ihh.1, ihg.1]
    · show zornTrace K (g (h x)) = zornTrace K x
      rw [ihg.2, ihh.2]
  | inv g _ ihg =>
    refine ⟨?_, fun x => ?_⟩
    · have := ihg.1
      apply g.injective
      simp [this]
    · have := ihg.2 (g⁻¹ x)
      simpa using this.symm

end Zorn

section G2Module

variable (K : Type) [Field K] [Algebra (ZMod 2) K]

@[expose] noncomputable def zornRep :
    Representation (ZMod 2) ↥(quasithinG2 K) (quasithinZorn K) where
  toFun g := (((g : quasithinZorn K ≃ₗ[K] quasithinZorn K) :
    quasithinZorn K →ₗ[K] quasithinZorn K)).restrictScalars (ZMod 2)
  map_one' := LinearMap.ext fun _ => rfl
  map_mul' _ _ := LinearMap.ext fun _ => rfl

@[expose] def zornTraceZero : Submodule (ZMod 2) (quasithinZorn K) where
  carrier := {x | zornTrace K x = 0}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, zornTrace, Prod.fst_add, Prod.snd_add] at ha hb ⊢
    calc a.1 + b.1 + (a.2.2.2 + b.2.2.2) = (a.1 + a.2.2.2) + (b.1 + b.2.2.2) := by ring
      _ = 0 := by rw [ha, hb, add_zero]
  zero_mem' := by simp [zornTrace]
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_ofPred_eq, zornTrace, Prod.smul_fst, Prod.smul_snd] at hx ⊢
    rw [← smul_add, hx, smul_zero]

theorem zornTraceZero_inv (g : ↥(quasithinG2 K)) :
    zornTraceZero K ≤ (zornTraceZero K).comap (zornRep K g) := by
  intro x hx
  have hx' : zornTrace K x = 0 := hx
  show zornTrace K (((g : quasithinZorn K ≃ₗ[K] quasithinZorn K)) x) = 0
  rw [(g2_inv K g g.2).2 x, hx']

@[expose] noncomputable def zornTraceZeroRep :
    Representation (ZMod 2) ↥(quasithinG2 K) (zornTraceZero K) :=
  (zornRep K).subrepresentation (zornTraceZero K) (zornTraceZero_inv K)

@[expose] def zornLine : Submodule (ZMod 2) (zornTraceZero K) :=
  ((Submodule.span K {zornOne K}).restrictScalars (ZMod 2)).comap (zornTraceZero K).subtype

theorem zornLine_inv (g : ↥(quasithinG2 K)) :
    zornLine K ≤ (zornLine K).comap (zornTraceZeroRep K g) := by
  intro x hx
  have hx' : (x : quasithinZorn K) ∈ Submodule.span K {zornOne K} := hx
  rw [Submodule.mem_span_singleton] at hx'
  obtain ⟨c, hc⟩ := hx'
  show ((zornTraceZeroRep K g x : zornTraceZero K) : quasithinZorn K) ∈
    Submodule.span K {zornOne K}
  rw [Submodule.mem_span_singleton]
  refine ⟨c, ?_⟩
  have h1 := (g2_inv K g g.2).1
  have : ((zornTraceZeroRep K g x : zornTraceZero K) : quasithinZorn K) =
      ((g : quasithinZorn K ≃ₗ[K] quasithinZorn K)) (x : quasithinZorn K) := rfl
  rw [this, ← hc, map_smul, h1]

@[expose] noncomputable def g2NaturalRep :
    Representation (ZMod 2) ↥(quasithinG2 K) (zornTraceZero K ⧸ zornLine K) :=
  (zornTraceZeroRep K).quotient (zornLine K) (zornLine_inv K)

@[expose] noncomputable def g2DerivedNaturalRep :
    Representation (ZMod 2) ↥(commutator ↥(quasithinG2 K)) (zornTraceZero K ⧸ zornLine K) :=
  (g2NaturalRep K).comp (commutator ↥(quasithinG2 K)).subtype

end G2Module

@[expose] def IsHatCover (X : Type) [Group X] (S : Type) [Group S] : Prop :=
  CFSG.IsQuasisimple X ∧ Nat.card (Subgroup.center X) = 3 ∧
    Nonempty (X ⧸ Subgroup.center X ≃* S)

@[expose] def ListedI13D2 (G : Type) [Group G] : Prop :=
  StatedClassicalModel G .PSL 4 2 1 ∨ ChevalleyExceptionalModel G .G2 2 2 ∨
    NativeSporadic.IsSporadic G .M12 ∨ NativeSporadic.IsSporadic G .J2 ∨
    NativeSporadic.IsSporadic G .HS ∨ NativeSporadic.IsSporadic G .Ru ∨
    ∃ p f : ℕ, p ≠ 2 ∧ 1 ≤ f ∧ p ^ f ≠ 9 ∧ StatedClassicalModel G .PSL 2 p f

@[expose] def ListedI13D3 (G : Type) [Group G] : Prop :=
  (∃ p f : ℕ, (p ^ f % 3 = 1 ∧ StatedClassicalModel G .PSL 3 p f) ∨
      (p ^ f % 3 = 2 ∧ StatedClassicalModel G .PSU 3 p f)) ∧
    ¬ StatedClassicalModel G .PSL 3 2 2

@[expose] def ListedI13D6 (G : Type) [Group G] : Prop :=
  Nonempty (G ≃* alternatingGroup (Fin 6)) ∨ Nonempty (G ≃* alternatingGroup (Fin 7))

@[expose] def ListedI14D2 (G : Type) [Group G] : Prop :=
  Nonempty (G ≃* alternatingGroup (Fin 9)) ∨ StatedClassicalModel G .PSU 4 2 1 ∨
    StatedClassicalModel G .PSL 4 3 1 ∨
    ∃ p f : ℕ, p ≠ 2 ∧ 1 ≤ f ∧ 9 < p ^ f ∧ StatedClassicalModel G .PSL 2 p f

@[expose] def ListedI14D3 (G : Type) [Group G] : Prop :=
  NativeSporadic.IsSporadic G .J3 ∨ NativeSporadic.IsSporadic G .McL ∨
    ChevalleyExceptionalModel G .G2 3 1 ∨
    ∃ p f : ℕ, p ≠ 2 ∧ ((p ^ f % 3 = 1 ∧ StatedClassicalModel G .PSL 3 p f) ∨
      (p ^ f % 3 = 2 ∧ StatedClassicalModel G .PSU 3 p f))

@[expose] def ListedI14D4 (G : Type) [Group G] : Prop :=
  (∃ r m : ℕ, r.Prime ∧ r = 2 ^ 2 ^ m + 1 ∧ 3 < r ∧ StatedClassicalModel G .PSL 4 r 1) ∨
    (∃ s m : ℕ, s.Prime ∧ s = 2 ^ m - 1 ∧ 3 < s ∧ StatedClassicalModel G .PSU 4 s 1)

end CFSG.ASVolI.ChIJK

namespace CFSG.ASVolI

open CFSG.Open CFSG.Blueprint CFSG.ASVolI.ChIJK
open scoped MatrixGroups

@[expose] def I_1_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (r : ℕ), r.Prime → r ≠ 2 → Group.IsPerfect G →
    CFSG.pRank r G ≤ 1 → ∀ x : quasithinHopfMultiplier G, Nat.Coprime (orderOf x) r

section BurnsideI12


end BurnsideI12


@[expose] def I_1_3 : Prop :=
  (∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → CFSG.SectionRank.IsSQTKCat G →
    Nontrivial (quasithinHopfMultiplier G) →
    ListedI13D2 G ∨ ListedI13D3 G ∨ ListedI13D6 G ∨ NativeSporadic.IsSporadic G .M22 ∨
      SuzukiModel G 2 3 ∨ StatedClassicalModel G .PSL 3 2 2) ∧
  (∀ (G : Type) [Group G] [Finite G], ListedI13D2 G → quasithinMultiplierCyclic G 2) ∧
  (∀ (G : Type) [Group G] [Finite G], ListedI13D3 G → quasithinMultiplierCyclic G 3) ∧
  (∀ (G : Type) [Group G] [Finite G], ListedI13D6 G → quasithinMultiplierCyclic G 6) ∧
  (∀ (G : Type) [Group G] [Finite G], NativeSporadic.IsSporadic G .M22 →
    quasithinMultiplierCyclic G 12) ∧
  (∀ (G : Type) [Group G] [Finite G], SuzukiModel G 2 3 →
    Nonempty (quasithinHopfMultiplier G ≃* Multiplicative (ZMod 2 × ZMod 2))) ∧
  (∀ (G : Type) [Group G] [Finite G], StatedClassicalModel G .PSL 3 2 2 →
    Nonempty (quasithinHopfMultiplier G ≃* Multiplicative (ZMod 4 × ZMod 4 × ZMod 3)))

section BurnsideI13_only13


end BurnsideI13_only13

section


end

@[expose] def I_1_4 : Prop :=
  (∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → CFSG.SectionRank.IsKGroupCat G →
    CFSG.Quasithin.IsQuasithin G → ¬ CFSG.IsStronglyQuasithin G →
    Nontrivial (quasithinHopfMultiplier G) →
    ListedI14D2 G ∨ ListedI14D3 G ∨ ListedI14D4 G ∨ StatedClassicalModel G .PSU 5 2 2 ∨
      StatedClassicalModel G .PSU 4 3 1 ∨
      StatedClassicalModel G .PSp 3 2 1 ∨
      (∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ StatedClassicalModel G .PSp 2 p 1)) ∧
  (∀ (G : Type) [Group G] [Finite G], ListedI14D2 G → quasithinMultiplierCyclic G 2) ∧
  (∀ (G : Type) [Group G] [Finite G], ListedI14D3 G → quasithinMultiplierCyclic G 3) ∧
  (∀ (G : Type) [Group G] [Finite G], ListedI14D4 G → quasithinMultiplierCyclic G 4) ∧
  (∀ (G : Type) [Group G] [Finite G], StatedClassicalModel G .PSU 5 2 2 →
    quasithinMultiplierCyclic G 5) ∧
  (∀ (G : Type) [Group G] [Finite G], StatedClassicalModel G .PSU 4 3 1 →
    Nonempty (quasithinHopfMultiplier G ≃* Multiplicative (ZMod 3 × ZMod 3 × ZMod 4))) ∧
  (∀ (G : Type) [Group G] [Finite G], StatedClassicalModel G .PSp 3 2 1 →
    quasithinMultiplierCyclic G 2) ∧
  (∀ (G : Type) [Group G] [Finite G] (p : ℕ), p.Prime → 5 ≤ p →
    StatedClassicalModel G .PSp 2 p 1 → quasithinMultiplierCyclic G 2)


section G24


end G24


section


end


section


end

@[expose] def I_1_6 : Prop :=
  (h1Dim (altNaturalRep 5) = 0 ∧ h1Dim (altNaturalRep 7) = 0 ∧
    h1Dim (altNaturalRep 6) = 1 ∧ h1Dim (altNaturalRep 8) = 1 ∧
    Module.Projective (MonoidAlgebra (ZMod 2) (alternatingGroup (Fin 5)))
      (altNaturalRep 5).asModule) ∧
  (∀ n : ℕ, 2 ≤ n → h1Dim (slNaturalRep 2 (GaloisField 2 n)) = n) ∧
  ((∀ n : ℕ, 1 ≤ n → ∀ b c : GaloisField 2 n, (∀ s : GaloisField 2 n, s ^ 2 + b * s + c ≠ 0) →
      h1Dim (orthMinusRep (GaloisField 2 n) b c) = 0) ∧
    (∀ b c : ZMod 2, (∀ s : ZMod 2, s ^ 2 + b * s + c ≠ 0) →
      (∃ (φ : StatedOmega (StatedQuadMinus 2 (ZMod 2) b c) ≃* alternatingGroup (Fin 5))
        (e : (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → ZMod 2) ≃ₗ[ZMod 2]
          (evenWeight 5 ⧸ constInEven 5)),
        ∀ (g : StatedOmega (StatedQuadMinus 2 (ZMod 2) b c)) (v : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → ZMod 2),
          e (orthMinusRep (ZMod 2) b c g v) = altNaturalRep 5 (φ g) (e v)) ∧
      Module.Projective (MonoidAlgebra (ZMod 2) (StatedOmega (StatedQuadMinus 2 (ZMod 2) b c)))
        (orthMinusRep (ZMod 2) b c).asModule)) ∧
  ((∀ n : ℕ, 2 ≤ n → h1Dim (slNaturalRep 3 (GaloisField 2 n)) = 0) ∧
    h1Dim (slNaturalRep 3 (ZMod 2)) = 1) ∧
  (∀ n : ℕ, 1 ≤ n → h1Dim (sp4NaturalRep (GaloisField 2 n)) = n ∧
    h1Dim (g2DerivedNaturalRep (GaloisField 2 n)) = n) ∧
  (h1Dim (slNaturalRep 4 (ZMod 2)) = 0 ∧ h1Dim (slNaturalRep 5 (ZMod 2)) = 0) ∧
  (∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V]
      (ρ : Representation (ZMod 2) SL(5, ZMod 2) V),
    ρ.IsIrreducible → Module.finrank (ZMod 2) V = 10 → h1Dim ρ = 0) ∧
  (∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V]
      (ρ : Representation (ZMod 2) (alternatingGroup (Fin 7)) V),
    ρ.IsIrreducible → Module.finrank (ZMod 2) V = 4 → h1Dim ρ = 0) ∧
  (∀ (G : Type) [Group G] [Finite G], IsHatCover G (alternatingGroup (Fin 6)) →
    ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] (ρ : Representation (ZMod 2) G V),
      Function.Injective ρ → ρ.IsIrreducible → Module.finrank (ZMod 2) V = 6 → h1Dim ρ = 0)


end CFSG.ASVolI
