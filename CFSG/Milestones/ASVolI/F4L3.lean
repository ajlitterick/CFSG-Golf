module

public import CFSG.Milestones.ASVolI.F4
public import CFSG.Quasithin.Vol2.GoldschmidtF431L3LieOutModel
import all CFSG.Milestones.ASVolI.F4
public import CFSG.GH74.QTGen4.DSGen4.L34Generic
public import CFSG.RankThree.PartOne.KC.LinearSubfieldPointwise
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InComplement
public import CFSG.Quasithin.Vol2.GoldschmidtF431F45L3Main
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42Am

public section

namespace CFSG.ASVolI

section Y1

open CFSG.Open
open CFSG.ASVolI.ChF

open CFSG.ASVolI.ChF.ClassicalRoots CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Setup.X7a

theorem burnsideF4d_Y1_mem_rawStabilizer {index : Type} [Fintype index] [DecidableEq index]
    {K : Type} [Field K] (space : Set (index → K)) (g : GL index K) :
    g ∈ rawStabilizer space ↔
      ∀ vector : index → K, (g : Matrix index index K).mulVec vector ∈ space ↔ vector ∈ space := by
  let S : Subgroup (GL index K) :=
    { carrier := {actor | ∀ vector : index → K,
        (actor : Matrix index index K).mulVec vector ∈ space ↔ vector ∈ space}
      one_mem' := by
        intro vector
        simp
      mul_mem' := by
        intro a b ha hb vector
        have h1 := ha ((b : Matrix index index K).mulVec vector)
        have h2 := hb vector
        rw [Units.val_mul, ← Matrix.mulVec_mulVec]
        exact h1.trans h2
      inv_mem' := by
        intro a ha vector
        have h1 := ha (((a⁻¹ : GL index K) : Matrix index index K).mulVec vector)
        rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec] at h1
        exact h1.symm }
  have hS : rawStabilizer space = S := Subgroup.closure_eq S
  rw [hS]
  exact Iff.rfl

theorem burnsideF4d_Y1_mem_stabilizer_iff {n : ℕ} {K : Type} [Field K]
    (W : Submodule K (Fin n → K)) (A : Matrix.SpecialLinearGroup (Fin n) K) :
    A ∈ stabilizer W ↔
      ∀ v : Fin n → K, (A : Matrix (Fin n) (Fin n) K).mulVec v ∈ W ↔ v ∈ W := by
  have hinv : ((A⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (A : Matrix (Fin n) (Fin n) K) = 1 := coe_inv_mul_coe A
  have hmul : (A : Matrix (Fin n) (Fin n) K) *
      ((A⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  rw [mem_stabilizer]
  constructor
  · intro h v
    constructor
    · intro hv
      rw [← h] at hv
      obtain ⟨w, hw, hwv⟩ := hv
      have h2 : (A : Matrix (Fin n) (Fin n) K).mulVec w = (A : Matrix (Fin n) (Fin n) K).mulVec v :=
        hwv
      have : w = v := by
        calc w = ((A⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K).mulVec
              ((A : Matrix (Fin n) (Fin n) K).mulVec w) := by
              rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
          _ = ((A⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K).mulVec
              ((A : Matrix (Fin n) (Fin n) K).mulVec v) := by rw [h2]
          _ = v := by rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
      rw [this] at hw
      exact hw
    · intro hv
      rw [← h]
      exact ⟨v, hv, rfl⟩
  · intro h
    ext x
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact (h w).2 hw
    · intro hx
      have hv : ((A⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K).mulVec x
          ∈ W := by
        refine (h _).1 ?_
        rw [Matrix.mulVec_mulVec, hmul, Matrix.one_mulVec]
        exact hx
      refine ⟨_, hv, ?_⟩
      show (A : Matrix (Fin n) (Fin n) K).mulVec
        (((A⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K).mulVec x) = x
      rw [Matrix.mulVec_mulVec, hmul, Matrix.one_mulVec]

theorem burnsideF4d_Y1_coordinateSpace_flag {K : Type} [Field K] (i : ℕ) (v : Fin 3 → K) :
    v ∈ coordinateSpace ({p : Fin 3 | (p : ℕ) < i} : Set (Fin 3)) ↔ v ∈ flagSpace 3 K i := by
  rw [mem_flagSpace]
  simp only [coordinateSpace, Set.mem_setOf_eq, not_lt]

theorem burnsideF4d_Y1_image_one {index : Type} [Fintype index] [DecidableEq index] {K : Type}
    [Field K] (S : Set (index → K)) :
    (fun vector => ((1 : GL index K) : Matrix index index K).mulVec vector) '' S = S := by
  simp

private theorem burnsideF4d_Y1_comap_nativeParabolic (q : ℕ) (K : Type) [Field K]
    (basis : GL (Fin 3) K) (hb : basis = 1) (b : Bool) :
    (nativeParabolic .L3 q K basis b).comap
        (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K).toMonoidHom =
      Q3 K (if b then 1 else 0) := by
  subst hb
  ext A
  have h1 : A ∈ (nativeParabolic .L3 q K 1 b).comap
        (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K).toMonoidHom ↔
      ((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K A : GL (Fin 3) K)) ∈
        rawStabilizer ((fun vector =>
            ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec vector) ''
          coordinateSpace (if b then flagTwo .L3 else flagOne .L3 : Set (Fin 3))) :=
    Iff.rfl
  refine h1.trans ?_
  rw [burnsideF4d_Y1_mem_rawStabilizer, burnsideF4d_Y1_image_one, Q3,
    burnsideF4d_Y1_mem_stabilizer_iff]
  have key : ∀ (S : Set (Fin 3)) (i : ℕ), S = {p : Fin 3 | (p : ℕ) < i} →
      ((∀ v : Fin 3 → K, (A : Matrix (Fin 3) (Fin 3) K).mulVec v ∈ coordinateSpace S ↔
          v ∈ coordinateSpace S) ↔
        ∀ v : Fin 3 → K, (A : Matrix (Fin 3) (Fin 3) K).mulVec v ∈ flagSpace 3 K i ↔
          v ∈ flagSpace 3 K i) := by
    intro S i hS
    subst hS
    simp only [burnsideF4d_Y1_coordinateSpace_flag]
  cases b
  · exact key _ 1 (by ext p; simp [flagOne] <;> omega)
  · exact key _ 2 (by ext p; simp [flagTwo] <;> omega)

private noncomputable def burnsideF4d_Y1_psi {f : ℕ} {H : Type} [Group H]
    (marking : ClassicalRoots.Marking .L3 2 f H) : H ≃* projectiveSL 3 marking.field :=
  marking.identification.symm.trans
    (CFSG.QuasithinUnique.Id2519.projectiveSLEquivStatedProj 3 marking.field).symm

private theorem burnsideF4d_Y1_psi_transport {f : ℕ} {H : Type} [Group H]
    (marking : ClassicalRoots.Marking .L3 2 f H)
    (A : Matrix.SpecialLinearGroup (Fin 3) marking.field) :
    burnsideF4d_Y1_psi marking (marking.transport
        (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 marking.field A)) =
      proj 3 marking.field A := by
  have h1 : CFSG.QuasithinUnique.Id2519.projectiveSLEquivStatedProj 3 marking.field
      (proj 3 marking.field A) =
      (QuotientGroup.mk
        (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 marking.field A) :
        StatedProj (StatedSL 3 marking.field)) := rfl
  show (CFSG.QuasithinUnique.Id2519.projectiveSLEquivStatedProj 3 marking.field).symm
      (marking.identification.symm (marking.identification (QuotientGroup.mk _))) = _
  rw [MulEquiv.symm_apply_apply]
  exact (MulEquiv.symm_apply_eq _).2 h1.symm

private theorem burnsideF4d_Y1_map_parabolic {f : ℕ} {H : Type} [Group H]
    (marking : ClassicalRoots.Marking .L3 2 f H) (b : Bool) :
    (marking.parabolic b).map (burnsideF4d_Y1_psi marking).toMonoidHom =
      (Q3 marking.field (if b then 1 else 0)).map (proj 3 marking.field) := by
  have hbasis : marking.basis = 1 := marking.basis_compatible
  have key := burnsideF4d_Y1_comap_nativeParabolic (2 ^ f) marking.field marking.basis hbasis b
  have hsurj := (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3
    marking.field).surjective
  ext x
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    obtain ⟨A, rfl⟩ := hsurj z
    refine ⟨A, ?_, (burnsideF4d_Y1_psi_transport marking A).symm⟩
    rw [← key]
    exact hz
  · rintro ⟨A, hA, rfl⟩
    rw [← key] at hA
    exact ⟨marking.transport (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3
      marking.field A), ⟨_, hA, rfl⟩, burnsideF4d_Y1_psi_transport marking A⟩

theorem burnsideF4d_Y1_noNormalTwo {F : Type} [Field F] [Finite F] :
    ∀ P : Subgroup (projectiveSL 3 F), P.Normal → IsPGroup 2 P → P = ⊥ := by
  intro P hP hp
  have hsimple : IsSimpleGroup (projectiveSL 3 F) :=
    CFSG.RankThree.PartOne.KCLinearSubfield.isSimpleGroup_projectiveSL (n := 3) (K := F) le_rfl
  rcases hP.eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hp' : IsPGroup 2 (projectiveSL 3 F) := by
      rw [h] at hp
      exact hp.of_equiv Subgroup.topEquiv
    have hnt : Nontrivial (projectiveSL 3 F) := hsimple.toNontrivial
    have hc := hp'.center_nontrivial
    obtain ⟨⟨z, hz⟩, hz1⟩ := exists_ne (1 : Subgroup.center (projectiveSL 3 F))
    apply hz1
    apply Subtype.ext
    exact CFSG.QuasithinUnique.Fin257.L3.center_trivial_M z
      (fun y => (Subgroup.mem_center_iff.mp hz y).symm)

theorem burnsideF4d_Y1_yam_of_marking {f : ℕ} {H : Type} [Group H]
    (marking : ClassicalRoots.Marking .L3 2 f H) :
    ∃ TD : Subgroup H, CFSG.Quasithin.IsYAmalgamPair TD (marking.parabolic false)
      (marking.parabolic true) := by
  have hcard : Nat.card marking.field = 2 ^ f := by
    have := marking.field_card
    simpa using this
  have hchar : CharP marking.field 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have := Fintype.ofFinite marking.field
    exact charP_of_card_eq_prime_pow (p := 2) (f := f)
      (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  have hBD := CFSG.QuasithinUnique.Borel252.L3.borelData_L3 (F := marking.field)
  have hOG := CFSG.QuasithinUnique.Borel252.L3.overgroupData_L3 (F := marking.field)
  have hY := CFSG.GH74.QTGen4.DSGen4.L34.isYAmalgamPair_of_borelData hBD
    burnsideF4d_Y1_noNormalTwo
  have e1 := hOG.eq_of_between hBD.lt₁ hBD.lt_top₁
  have e2 := hOG.eq_of_between hBD.lt₂ hBD.lt_top₂
  have hne := hBD.ne_norm
  have hY' : CFSG.Quasithin.IsYAmalgamPair (projUnitriangular 3 marking.field)
      ((Q3 marking.field 0).map (proj 3 marking.field))
      ((Q3 marking.field 1).map (proj 3 marking.field)) := by
    rcases e1 with e1 | e1 <;> rcases e2 with e2 | e2
    · exact absurd (e1.trans e2.symm) hne
    · rw [e1, e2] at hY
      exact hY
    · rw [e1, e2] at hY
      exact ⟨hY.1, hY.2.1.symm, fun M => (hY.2.2 M).trans or_comm⟩
    · exact absurd (e1.trans e2.symm) hne
  have hm0 := burnsideF4d_Y1_map_parabolic marking false
  have hm1 := burnsideF4d_Y1_map_parabolic marking true
  simp only [Bool.false_eq_true, if_false, if_true] at hm0 hm1
  refine ⟨(projUnitriangular 3 marking.field).map
    (burnsideF4d_Y1_psi marking).symm.toMonoidHom, ?_⟩
  have := hY'.map (burnsideF4d_Y1_psi marking).symm
  have hsymm : ∀ P : Subgroup H, ((P.map (burnsideF4d_Y1_psi marking).toMonoidHom).map
      (burnsideF4d_Y1_psi marking).symm.toMonoidHom) = P := by
    intro P
    ext x
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      simpa using hz
    · intro hx
      exact ⟨(burnsideF4d_Y1_psi marking) x, ⟨x, hx, rfl⟩, by simp⟩
  have h0 : Subgroup.map (burnsideF4d_Y1_psi marking).symm.toMonoidHom
      ((Q3 marking.field 0).map (proj 3 marking.field)) = marking.parabolic false := by
    rw [← hm0]
    exact hsymm _
  have h1 : Subgroup.map (burnsideF4d_Y1_psi marking).symm.toMonoidHom
      ((Q3 marking.field 1).map (proj 3 marking.field)) = marking.parabolic true := by
    rw [← hm1]
    exact hsymm _
  rw [h0, h1] at this
  exact this

theorem burnsideF4d_Y1_marking {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (h : CFSG.ASVolI.ChF.HypF_4_4g .L3 2 f Gp M₁ M₂) :
    ∃ marking : ClassicalRoots.Marking .L3 2 f Gp,
      M₁.subgroupOf Gp = marking.parabolic false ∧ M₂.subgroupOf Gp = marking.parabolic true := by
  obtain ⟨chart, -, hpts, hlines⟩ := h.lie_amalgam
  rcases chart.coordinates with
    ⟨c, hk, marking, h1, h2, h3, h4, h5⟩ | ⟨hk, -⟩ | ⟨hk, -⟩ | ⟨hk, -⟩ |
    ⟨-, exponent, K, fK, finK, charK, scope, ⟨hk, -⟩ | ⟨hk, -⟩⟩
  · have hc : c = .L3 := by
      cases c
      · rfl
      all_goals exact absurd hk (by decide)
    subst hc
    refine ⟨marking, ?_, ?_⟩
    · have : Gp ⊓ M₁ = (marking.parabolic false).map Gp.subtype := hpts.trans h2
      rw [← Subgroup.inf_subgroupOf_left M₁ Gp, this]
      exact Subgroup.comap_map_eq_self_of_injective Gp.subtype_injective _
    · have : Gp ⊓ M₂ = (marking.parabolic true).map Gp.subtype := hlines.trans h3
      rw [← Subgroup.inf_subgroupOf_left M₂ Gp, this]
      exact Subgroup.comap_map_eq_self_of_injective Gp.subtype_injective _
  all_goals exact absurd hk (by decide)

theorem burnsideF4d_Y1_lieModel {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (h : CFSG.ASVolI.ChF.HypF_4_4g .L3 2 f Gp M₁ M₂) :
    CFSG.Blueprint.LieModel (↥Gp) CFSG.Assembly.LowTwoRank.StatedLieTag.PSL 3 2 f := by
  obtain ⟨hp, hf, K, hK, hKfin, hcard, he⟩ := h.model
  refine (CFSG.Blueprint.LieModel.classical_iff (t := .PSL) (by decide)).2 ?_
  exact ⟨⟨hp, hf, by norm_num, by simp, by simp⟩, K, hK, hKfin, hcard, he⟩


theorem burnsideF4d_Y1_yam {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (h : CFSG.ASVolI.ChF.HypF_4_4g .L3 2 f Gp M₁ M₂) :
    ∃ TD : Subgroup ↥Gp, CFSG.Quasithin.IsYAmalgamPair TD (M₁.subgroupOf Gp)
      (M₂.subgroupOf Gp) := by
  obtain ⟨marking, h1, h2⟩ := burnsideF4d_Y1_marking h
  rw [h1, h2]
  exact burnsideF4d_Y1_yam_of_marking marking

end Y1

section F4dBaseRest

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431

section Conj

variable {E : Type} [Group E] {Gp : Subgroup E}

noncomputable abbrev burnsideF4d_rho (Gp : Subgroup E) [Gp.Normal] : E →* MulAut ↥Gp :=
  MulAut.conjNormal

theorem burnsideF4d_rho_apply [Gp.Normal] (e : E) (x : ↥Gp) :
    ((burnsideF4d_rho Gp e x : ↥Gp) : E) = e * (x : E) * e⁻¹ :=
  MulAut.conjNormal_apply e x

theorem burnsideF4d_rho_injective [Gp.Normal]
    (hc : Subgroup.centralizer (Gp : Set E) = ⊥) : Function.Injective (burnsideF4d_rho Gp) := by
  rw [injective_iff_map_eq_one]
  intro e he
  have : e ∈ Subgroup.centralizer (Gp : Set E) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h1 := congrArg (fun φ : MulAut ↥Gp => ((φ ⟨x, hx⟩ : ↥Gp) : E)) he
    simp only [burnsideF4d_rho_apply, MulAut.one_apply] at h1
    calc x * e = (e * x * e⁻¹) * e := by rw [h1]
      _ = e * x := by group
  rw [hc] at this
  exact Subgroup.mem_bot.mp this

theorem burnsideF4d_rho_mem_autStab [Gp.Normal] (P : Subgroup E) (e : E) :
    burnsideF4d_rho Gp e ∈ autStab (P.subgroupOf Gp) ↔
      ∀ x : ↥Gp, (x : E) ∈ P ↔ e * (x : E) * e⁻¹ ∈ P := by
  show (∀ x : ↥Gp, x ∈ P.subgroupOf Gp ↔ burnsideF4d_rho Gp e x ∈ P.subgroupOf Gp) ↔ _
  simp only [Subgroup.mem_subgroupOf, burnsideF4d_rho_apply]

theorem burnsideF4d_normalizer_iff [Gp.Normal] (P : Subgroup E) (e : E) :
    e ∈ Subgroup.normalizer ((Gp ⊓ P : Subgroup E) : Set E) ↔
      ∀ x : ↥Gp, (x : E) ∈ P ↔ e * (x : E) * e⁻¹ ∈ P := by
  rw [Subgroup.mem_normalizer_iff]
  constructor
  · intro h x
    have := h (x : E)
    simp only [Subgroup.mem_inf] at this
    constructor
    · intro hx
      exact (this.mp ⟨x.2, hx⟩).2
    · intro hx
      have hG : e * (x : E) * e⁻¹ ∈ Gp := Subgroup.Normal.conj_mem inferInstance (x : E) x.2 e
      exact (this.mpr ⟨hG, hx⟩).2
  · intro h y
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨hy, hyP⟩
      exact ⟨Subgroup.Normal.conj_mem inferInstance y hy e, (h ⟨y, hy⟩).mp hyP⟩
    · rintro ⟨hy, hyP⟩
      have hy' : y ∈ Gp := by
        have := Subgroup.Normal.conj_mem (inferInstance : Gp.Normal) _ hy e⁻¹
        simpa [mul_assoc] using this
      exact ⟨hy', (h ⟨y, hy'⟩).mpr hyP⟩

end Conj

section SelfNorm

variable {D : Type} [Group D] [Finite D]

theorem burnsideF4d_selfNorm {TD P1 P2 : Subgroup D} (h : IsYAmalgamPair TD P1 P2) (g : D)
    (hg : ∀ x : D, x ∈ P1 ↔ g * x * g⁻¹ ∈ P1) : g ∈ P1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmax : Quasithin.IsMaximalTwoLocal P1 := ((h.2.2 P1).mpr (Or.inl rfl)).1
  obtain ⟨⟨P, hPne, hPp, hP1⟩, hmaxi⟩ := hmax
  have hPle : P ≤ P1 := hP1 ▸ Subgroup.le_normalizer
  have hPcore : P ≤ pCoreOf 2 P1 :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hPle hP1.le hPp
  have hQne : pCoreOf 2 P1 ≠ ⊥ := by
    intro hb
    rw [hb] at hPcore
    exact hPne (le_bot_iff.mp hPcore)
  have hloc : CFSG.Open.IsTwoLocal (Subgroup.normalizer (pCoreOf 2 P1 : Set D)) :=
    ⟨pCoreOf 2 P1, hQne, CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 P1, rfl⟩
  have heq := hmaxi _ hloc (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P1)
  have hgN : g ∈ Subgroup.normalizer (P1 : Set D) := Subgroup.mem_normalizer_iff.mpr hg
  have := CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 P1 hgN
  rwa [heq] at this

end SelfNorm

section Ext

variable {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E} {κ : ChF.GLKind} {p f : ℕ}

theorem burnsideF4d_inf_subgroupOf (Gp M₁ M₂ : Subgroup E) :
    (M₁ ⊓ M₂).subgroupOf Gp = M₁.subgroupOf Gp ⊓ M₂.subgroupOf Gp := by
  ext x; simp [Subgroup.mem_subgroupOf]

@[expose] noncomputable def burnsideF4d_amalgamExt (hyp : ChF.HypF_4_4g κ p f Gp M₁ M₂) (TD : Subgroup ↥Gp)
    (hyam : IsYAmalgamPair TD (M₁.subgroupOf Gp) (M₂.subgroupOf Gp)) :
    LieAmalgamExt ↥Gp :=
  haveI := hyp.normal
  { Mbar := (burnsideF4d_rho Gp).range
    TD := TD
    P1 := M₁.subgroupOf Gp
    P2 := M₂.subgroupOf Gp
    inn_le := by
      rintro _ ⟨d, rfl⟩
      refine ⟨(d : E), ?_⟩
      ext x
      simp [burnsideF4d_rho_apply]
    yam := hyam
    diag := by
      rintro φ ⟨e, rfl⟩ hφ
      rw [← burnsideF4d_inf_subgroupOf, burnsideF4d_rho_mem_autStab] at hφ
      have h1 := (burnsideF4d_normalizer_iff (Gp := Gp) (M₁ ⊓ M₂) e).mpr hφ
      have h2 := hyp.dynkin e h1
      exact (burnsideF4d_rho_mem_autStab M₁ e).mpr
        ((burnsideF4d_normalizer_iff (Gp := Gp) M₁ e).mp h2) }

theorem burnsideF4d_conj_mem_iff {M : Subgroup E} {h : E} (hh : h ∈ M) (x : E) :
    h⁻¹ * x * h ∈ M ↔ x ∈ M := by
  constructor
  · intro hx
    have := M.mul_mem (M.mul_mem hh hx) (M.inv_mem hh)
    simpa [mul_assoc] using this
  · intro hx
    exact M.mul_mem (M.mul_mem (M.inv_mem hh) hx) hh

theorem burnsideF4d_rho_mem_stab_iff [Gp.Normal] (M : Subgroup E)
    (hsplit : ∀ e : E, ∃ n ∈ Gp, ∃ h ∈ M, e = n * h)
    (hself : ∀ g : ↥Gp, (∀ x : ↥Gp, x ∈ M.subgroupOf Gp ↔ g * x * g⁻¹ ∈ M.subgroupOf Gp) →
      g ∈ M.subgroupOf Gp) (e : E) :
    burnsideF4d_rho Gp e ∈ autStab (M.subgroupOf Gp) ↔ e ∈ M := by
  constructor
  · intro H
    have H' := (burnsideF4d_rho_mem_autStab M e).mp H
    obtain ⟨n, hn, h, hhM, rfl⟩ := hsplit e
    have hnM : ((⟨n, hn⟩ : ↥Gp) : E) ∈ M := by
      refine hself ⟨n, hn⟩ (fun x => ?_)
      have hy : h⁻¹ * (x : E) * h ∈ Gp := by
        have := Subgroup.Normal.conj_mem (inferInstance : Gp.Normal) _ x.2 h⁻¹
        simpa using this
      have h1 := H' ⟨_, hy⟩
      simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, InvMemClass.coe_inv]
      rw [show n * (x : E) * n⁻¹ = n * h * (h⁻¹ * (x : E) * h) * (n * h)⁻¹ by group, ← h1]
      exact (burnsideF4d_conj_mem_iff hhM _).symm
    exact M.mul_mem hnM hhM
  · intro hM
    refine (burnsideF4d_rho_mem_autStab M e).mpr (fun x => ?_)
    constructor
    · intro hx
      exact M.mul_mem (M.mul_mem hM hx) (M.inv_mem hM)
    · intro hx
      have := M.mul_mem (M.mul_mem (M.inv_mem hM) hx) hM
      simpa [mul_assoc] using this

theorem burnsideF4d_N1_eq [Finite E] [Gp.Normal] (hyp : ChF.HypF_4_4g κ p f Gp M₁ M₂)
    {TD : Subgroup ↥Gp} (hyam : IsYAmalgamPair TD (M₁.subgroupOf Gp) (M₂.subgroupOf Gp)) :
    (burnsideF4d_rho Gp).range ⊓ autStab (M₁.subgroupOf Gp) = M₁.map (burnsideF4d_rho Gp) := by
  have hiff := burnsideF4d_rho_mem_stab_iff (Gp := Gp) M₁
    (fun e => by
      obtain ⟨n, hn, h, hh, he⟩ := hyp.split e
      exact ⟨n, hn, h, hh.1, he⟩)
    (fun g hg => burnsideF4d_selfNorm hyam g hg)
  ext φ
  constructor
  · rintro ⟨⟨e, rfl⟩, h2⟩
    exact ⟨e, (hiff e).mp h2, rfl⟩
  · rintro ⟨e, he, rfl⟩
    exact ⟨⟨e, rfl⟩, (hiff e).mpr he⟩

theorem burnsideF4d_N2_eq [Finite E] [Gp.Normal] (hyp : ChF.HypF_4_4g κ p f Gp M₁ M₂)
    {TD : Subgroup ↥Gp} (hyam : IsYAmalgamPair TD (M₁.subgroupOf Gp) (M₂.subgroupOf Gp)) :
    (burnsideF4d_rho Gp).range ⊓ autStab (M₂.subgroupOf Gp) = M₂.map (burnsideF4d_rho Gp) := by
  have hyam' : IsYAmalgamPair TD (M₂.subgroupOf Gp) (M₁.subgroupOf Gp) := by
    refine ⟨hyam.1, hyam.2.1.symm, fun X => ?_⟩
    rw [hyam.2.2 X, or_comm]
  have hiff := burnsideF4d_rho_mem_stab_iff (Gp := Gp) M₂
    (fun e => by
      obtain ⟨n, hn, h, hh, he⟩ := hyp.split e
      exact ⟨n, hn, h, hh.2, he⟩)
    (fun g hg => burnsideF4d_selfNorm hyam' g hg)
  ext φ
  constructor
  · rintro ⟨⟨e, rfl⟩, h2⟩
    exact ⟨e, (hiff e).mp h2, rfl⟩
  · rintro ⟨e, he, rfl⟩
    exact ⟨⟨e, rfl⟩, (hiff e).mpr he⟩

@[expose] noncomputable def burnsideF4d_isoSub {A B : Type} [Group A] [Group B] (g : A →* B)
    (hg : Function.Injective g) (H : Subgroup B) (h : g.range = H) : A ≃* ↥H :=
  (MonoidHom.ofInjective hg).trans (MulEquiv.subgroupCongr h)

theorem burnsideF4d_K_eq [Finite E] (hyp : ChF.HypF_4_4g κ p f Gp M₁ M₂) {TD : Subgroup ↥Gp}
    (hyam : IsYAmalgamPair TD (M₁.subgroupOf Gp) (M₂.subgroupOf Gp)) :
    (burnsideF4d_amalgamExt hyp TD hyam).K = (haveI := hyp.normal; burnsideF4d_rho Gp).range := by
  haveI := hyp.normal
  have h1 := burnsideF4d_N1_eq hyp hyam
  have h2 := burnsideF4d_N2_eq hyp hyam
  show (burnsideF4d_rho Gp).range ⊓ autStab (M₁.subgroupOf Gp) ⊔
    (burnsideF4d_rho Gp).range ⊓ autStab (M₂.subgroupOf Gp) = _
  rw [h1, h2, ← Subgroup.map_sup, hyp.gen, ← MonoidHom.range_eq_map]

@[expose] noncomputable def burnsideF4d_lieExtE [Finite E] (hyp : ChF.HypF_4_4g κ p f Gp M₁ M₂)
    {TD : Subgroup ↥Gp} (hyam : IsYAmalgamPair TD (M₁.subgroupOf Gp) (M₂.subgroupOf Gp)) :
    LieExt ↥Gp M₁ M₂ :=
  haveI := hyp.normal
  have hinj : Function.Injective (burnsideF4d_rho Gp) :=
    burnsideF4d_rho_injective hyp.centralizer_trivial
  have h1 := burnsideF4d_N1_eq hyp hyam
  have h2 := burnsideF4d_N2_eq hyp hyam
  { toLieAmalgamExt := burnsideF4d_amalgamExt hyp TD hyam
    iso :=
      { φ1 := burnsideF4d_isoSub ((burnsideF4d_rho Gp).comp M₁.subtype)
          (hinj.comp M₁.subtype_injective) _ (by
            rw [MonoidHom.range_comp, Subgroup.range_subtype]; exact h1.symm)
        φ12 := burnsideF4d_isoSub ((burnsideF4d_rho Gp).comp (M₁ ⊓ M₂).subtype)
          (hinj.comp (M₁ ⊓ M₂).subtype_injective) _ (by
            rw [MonoidHom.range_comp, Subgroup.range_subtype, Subgroup.map_inf _ _ _ hinj]
            exact (congrArg₂ (· ⊓ ·) h1 h2).symm)
        φ2 := burnsideF4d_isoSub ((burnsideF4d_rho Gp).comp M₂.subtype)
          (hinj.comp M₂.subtype_injective) _ (by
            rw [MonoidHom.range_comp, Subgroup.range_subtype]; exact h2.symm)
        comm1 := fun g => rfl
        comm2 := fun g => rfl } }

end Ext

section MSide

open CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion CFSG.ASVolI.ChF
  CFSG.Quasithin.H13.F431.L3

variable {E : Type} [Group E] {M₁ M₂ : Subgroup E} {Y : Type} [Group Y] {M : Type} [Group M]

@[expose] noncomputable def burnsideF4d_bOne (β : Cpl M₁ M₂ Y) (ε : Y →* M) : ↥M₁ →* M :=
  (epsG β ε).comp (f1 (c := β))

@[expose] noncomputable def burnsideF4d_bTwo (β : Cpl M₁ M₂ Y) (ε : Y →* M) : ↥M₂ →* M :=
  (epsG β ε).comp (f2 (c := β))

@[expose] noncomputable def burnsideF4d_amalgIsoM (β : Cpl M₁ M₂ Y) (hβ : β.IsFaithful)
    (ε : Y →* M) (hε : Function.Injective (epsG β ε)) :
    AmalgIso M₁ M₂ (MiOne β ε) (MiTwo β ε) where
  b₁ := burnsideF4d_bOne β ε
  b₂ := burnsideF4d_bTwo β ε
  inj₁ := hε.comp (f1_injective β hβ)
  inj₂ := hε.comp (f2_injective β hβ)
  agree := fun g h1 h2 => by
    have e1 : β.φ1 (⟨g, h1⟩ : ↥M₁) = β.φ2 (⟨g, h2⟩ : ↥M₂) := by
      have a1 := β.comm1 (⟨g, h1, h2⟩ : ↥(M₁ ⊓ M₂))
      have a2 := β.comm2 (⟨g, h1, h2⟩ : ↥(M₁ ⊓ M₂))
      exact a1.trans a2.symm
    show epsG β ε (f1 (c := β) ⟨g, h1⟩) = epsG β ε (f2 (c := β) ⟨g, h2⟩)
    congr 1
    exact Subtype.ext e1
  range₁ := by
    show (burnsideF4d_bOne β ε).range = (f1 (c := β)).range.map (epsG β ε)
    exact MonoidHom.range_comp _ _
  range₂ := by
    show (burnsideF4d_bTwo β ε).range = (f2 (c := β)).range.map (epsG β ε)
    exact MonoidHom.range_comp _ _
  inter := fun x hx => by
    obtain ⟨_, ⟨a, rfl⟩, ha⟩ := hx.1
    obtain ⟨_, ⟨b, rfl⟩, hb⟩ := hx.2
    have hab : f1 (c := β) a = f2 (c := β) b := hε (ha.trans hb.symm)
    have hφ : β.φ1 a = β.φ2 b := congrArg Subtype.val hab
    have hmem : β.φ1 a ∈ β.φ1.range ⊓ β.φ2.range := ⟨⟨a, rfl⟩, ⟨b, hφ.symm⟩⟩
    rw [β.inter] at hmem
    obtain ⟨c0, hc⟩ := hmem
    have hca : (RankTwoAmalgam.ofSubgroups M₁ M₂).α1 c0 = a := hβ.1 (by rw [β.comm1]; exact hc)
    let c : ↥(M₁ ⊓ M₂) := c0
    refine ⟨(c : E), c.2.1, c.2.2, ?_⟩
    have h1 : (⟨(c : E), c.2.1⟩ : ↥M₁) = a := hca
    show epsG β ε (f1 (c := β) ⟨(c : E), c.2.1⟩) = x
    rw [h1]
    exact ha

end MSide

section Datum

open CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion CFSG.ASVolI.ChF
  CFSG.Quasithin.H13.F431.L3

theorem burnsideF4d_L3_datumE {f : ℕ} (hf : 2 ≤ f) {E : Type} [Group E] [Finite E]
    {Gp M₁ M₂ : Subgroup E} (hyp : HypF_4_4g .L3 2 f Gp M₁ M₂) (hodd : Odd Gp.index) :
    Nonempty (L3Datum M₁ M₂) := by
  obtain ⟨TD, hyam⟩ := burnsideF4d_Y1_yam hyp
  have hmodel := burnsideF4d_Y1_lieModel hyp
  haveI := hyp.normal
  have hinj : Function.Injective (burnsideF4d_rho Gp) :=
    burnsideF4d_rho_injective hyp.centralizer_trivial
  let X := burnsideF4d_lieExtE hyp hyam
  have hK : Nat.card ↥X.K = Nat.card E := by
    have : X.K = (burnsideF4d_rho Gp).range := burnsideF4d_K_eq hyp hyam
    rw [this, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
  have hodd' : Odd (Nat.card ↥X.K / Nat.card ↥Gp) := by
    rw [hK]
    have := Subgroup.card_mul_index Gp
    have hpos : 0 < Nat.card ↥Gp := Nat.card_pos
    rw [show Nat.card E / Nat.card ↥Gp = Gp.index by
      rw [← this, Nat.mul_div_cancel_left _ hpos]]
    exact hodd
  obtain ⟨D⟩ := f431L3Lie f hf ↥Gp hmodel X.toLieAmalgamExt hodd'
  exact D.nonempty_transport X.amalgIso

theorem burnsideF4d_L3_datumM {f : ℕ} (hf : 2 ≤ f) {E : Type} [Group E]
    {Gp M₁ M₂ : Subgroup E} {Y : Type} [Group Y] {β : Cpl M₁ M₂ Y} {M : Type} [Group M]
    {ε : Y →* M} {z : M} (hyp : HypF_4_31 .L3 f Gp M₁ M₂ β ε z) (hodd : Odd Gp.index) :
    Nonempty (L3Datum (MiOne β ε) (MiTwo β ε)) := by
  haveI := hyp.amalgam.finite
  obtain ⟨D⟩ := burnsideF4d_L3_datumE hf hyp.amalgam.toHypF_4_4g hodd
  exact D.nonempty_transport (burnsideF4d_amalgIsoM β hyp.faithful ε hyp.inj)

end Datum

section Out

open CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion CFSG.ASVolI.ChF
  CFSG.Quasithin.H13.F431.L3

theorem burnsideF4d_Out_not_mem_commutator {G : Type} [Group G] [Finite G] {M₁ M₂ : Subgroup G}
    (O : L3OutDatum M₁ M₂) {z : G}
    (hz : z ∈ centerOf O.S) (hz1 : z ≠ 1) (hC : Subgroup.centralizer ({z} : Set G) ≤ M₁) :
    O.f ∉ commutator G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcentG := O.centZ hz hz1 hC
  have hT1 : O.T ≤ M₁ := O.T_le.trans inf_le_left
  have hzT : z ∈ O.T := O.S_le_T ((L3OutDatum.mem_centerOf.mp hz).1)
  have hTw : ∃ w ∈ centerOf O.T, w ≠ 1 := by
    have hnt : Nontrivial O.T := ⟨⟨⟨z, hzT⟩, 1, fun h => hz1 (congrArg Subtype.val h)⟩⟩
    have := O.T_pgroup.center_nontrivial
    obtain ⟨w0, hw0⟩ := exists_ne (1 : Subgroup.center O.T)
    refine ⟨((w0 : O.T) : G), L3OutDatum.mem_centerOf.mpr ⟨(w0 : O.T).2, fun s hs => ?_⟩, ?_⟩
    · have := Subgroup.mem_center_iff.mp w0.2 ⟨s, hs⟩
      exact congrArg Subtype.val this
    · intro h
      apply hw0
      apply Subtype.ext
      apply Subtype.ext
      exact h
  have hTsyl : IsSylowTwoOf O.T ⊤ :=
    isSylowTwoOf_top_of_centralizer_le ⟨hT1, O.T_pgroup, O.T_index⟩ hTw (fun w hw hw1 y hy =>
      (hcentG w (O.ZT w hw) hw1 y (Subgroup.mem_centralizer_singleton_iff.mp hy)).1)
  have hconj : ∀ x ∈ O.S, x * x = 1 → x ≠ 1 → ∃ g : G, g * z * g⁻¹ = x := by
    intro x hx hx2 hx1
    obtain ⟨m, -, hmz⟩ := O.invS x hx hx2 hx1
    have hmx1 : m * x * m⁻¹ ≠ 1 := by
      intro h; apply hx1
      have := congrArg (fun y => m⁻¹ * y * m) h
      simpa [mul_assoc] using this
    obtain ⟨b, -, hbz⟩ := O.trans z hz hz1 _ hmz hmx1
    refine ⟨m⁻¹ * b, ?_⟩
    calc m⁻¹ * b * z * (m⁻¹ * b)⁻¹ = m⁻¹ * (b * z * b⁻¹) * m := by group
      _ = m⁻¹ * (m * x * m⁻¹) * m := by rw [hbz]
      _ = x := by group
  have hTf_le : O.T ⊓ Subgroup.centralizer ({O.f} : Set G) ≤ Subgroup.centralizer ({O.f} : Set G) :=
    inf_le_right
  have hZfS : centerOf (O.T ⊓ Subgroup.centralizer ({O.f} : Set G)) ⊓
      ⁅O.T ⊓ Subgroup.centralizer ({O.f} : Set G), O.T ⊓ Subgroup.centralizer ({O.f} : Set G)⁆ ≤
      O.T ⊓ Subgroup.centralizer ({O.f} : Set G) := inf_le_left.trans inf_le_left
  have hZfw : ∃ w ∈ centerOf (O.T ⊓ Subgroup.centralizer ({O.f} : Set G)) ⊓
      ⁅O.T ⊓ Subgroup.centralizer ({O.f} : Set G), O.T ⊓ Subgroup.centralizer ({O.f} : Set G)⁆,
      w ≠ 1 := by
    obtain ⟨a, ha⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp O.Zf_ne
    refine ⟨(a : G), a.2, fun h => ha (Subtype.ext h)⟩
  have hchar : ∀ n ∈ Subgroup.centralizer ({O.f} : Set G),
      n ∈ Subgroup.normalizer ((O.T ⊓ Subgroup.centralizer ({O.f} : Set G) : Subgroup G) : Set G) →
      ∀ x ∈ centerOf (O.T ⊓ Subgroup.centralizer ({O.f} : Set G)) ⊓
        ⁅O.T ⊓ Subgroup.centralizer ({O.f} : Set G), O.T ⊓ Subgroup.centralizer ({O.f} : Set G)⁆,
        n * x * n⁻¹ ∈ centerOf (O.T ⊓ Subgroup.centralizer ({O.f} : Set G)) ⊓
        ⁅O.T ⊓ Subgroup.centralizer ({O.f} : Set G),
          O.T ⊓ Subgroup.centralizer ({O.f} : Set G)⁆ := by
    intro n _ hn x hx
    have hcn := conjSub_eq_of_mem_normalizer hn
    have e : conjSub n (centerOf (O.T ⊓ Subgroup.centralizer ({O.f} : Set G)) ⊓
        ⁅O.T ⊓ Subgroup.centralizer ({O.f} : Set G),
          O.T ⊓ Subgroup.centralizer ({O.f} : Set G)⁆) =
        centerOf (O.T ⊓ Subgroup.centralizer ({O.f} : Set G)) ⊓
        ⁅O.T ⊓ Subgroup.centralizer ({O.f} : Set G),
          O.T ⊓ Subgroup.centralizer ({O.f} : Set G)⁆ := by
      rw [conjSub_inf, ← centerOf_conjSub, ← conjSub_commutator, hcn]
    rw [← e]
    exact mul_mem_conjSub hx
  have hmax := maximal_two_of_char (S := O.T ⊓ Subgroup.centralizer ({O.f} : Set G))
    (M := M₁ ⊓ M₂ ⊓ Subgroup.centralizer ({O.f} : Set G))
    (H := Subgroup.centralizer ({O.f} : Set G)) (Z' := centerOf (O.T ⊓ Subgroup.centralizer
      ({O.f} : Set G)) ⊓ ⁅O.T ⊓ Subgroup.centralizer ({O.f} : Set G),
        O.T ⊓ Subgroup.centralizer ({O.f} : Set G)⁆)
    O.Tf_sylow hZfS hZfw hchar (fun w hw hw1 y hy hyw => ⟨hcentG w (O.Zf_le hw) hw1 y hyw, hy⟩)
  have hTfSyl : IsSylowTwoOf (O.T ⊓ Subgroup.centralizer ({O.f} : Set G))
      (Subgroup.centralizer ({O.f} : Set G)) :=
    isSylowTwoOf_of_max hTf_le (O.T_pgroup.to_le inf_le_left) hmax
  have hf1 : O.f ≠ 1 := fun h => O.f_not (h ▸ O.S.one_mem)
  have hfG : ∀ g : G, g⁻¹ * O.f * g ∉ O.S := by
    intro g hg
    have hj2 : g⁻¹ * O.f * g * (g⁻¹ * O.f * g) = 1 := by
      calc g⁻¹ * O.f * g * (g⁻¹ * O.f * g) = g⁻¹ * (O.f * O.f) * g := by group
        _ = 1 := by rw [O.f_sq]; group
    obtain ⟨h, hh⟩ := hconj _ hg hj2 (conj_ne_one' hf1)
    have hfeq : O.f = (g * h) * z * (g * h)⁻¹ := by
      calc O.f = g * (g⁻¹ * O.f * g) * g⁻¹ := by group
        _ = g * (h * z * h⁻¹) * g⁻¹ := by rw [hh]
        _ = (g * h) * z * (g * h)⁻¹ := by group
    have hPp : IsPGroup 2 (conjSub (g * h) O.S) := F7.isPGroup_conjSub O.S_pgroup
    have hPH : conjSub (g * h) O.S ≤ Subgroup.centralizer ({O.f} : Set G) := by
      intro p hp
      rw [mem_conjSub] at hp
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hc := (L3OutDatum.mem_centerOf.mp hz).2 _ hp
      calc p * O.f = (g * h) * (((g * h)⁻¹ * p * (g * h)) * z) * (g * h)⁻¹ := by rw [hfeq]; group
        _ = (g * h) * (z * ((g * h)⁻¹ * p * (g * h))) * (g * h)⁻¹ := by rw [hc]
        _ = O.f * p := by rw [hfeq]; group
    obtain ⟨x, -, hPx⟩ := F7.isSylowTwoOf_exists_conj_le hTfSyl hPH hPp
    have h1 : Nat.card (conjSub (g * h) O.S) ≤ Nat.card (conjSub x
        (O.T ⊓ Subgroup.centralizer ({O.f} : Set G))) := Subgroup.card_le_of_le hPx
    rw [card_conjSub, card_conjSub] at h1
    exact absurd O.Tf_lt (not_lt.mpr h1)
  have hT2 : Nat.Coprime 2 O.T.index := by
    have h := hTsyl.2.2
    have h' : ¬ 2 ∣ O.T.index := by
      rw [← Subgroup.relIndex_top_right]; exact h
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h'
  have hTnorm : O.T ≤ Subgroup.normalizer (O.S : Set G) := O.T_le.trans O.H_le_normalizer_S
  have hnotcomm : O.f ∉ commutator G := by
    refine generalized_thompson_transfer_two (H := O.T) (K := O.S) hT2
      ⟨O.S_le_T, Subgroup.normal_subgroupOf_of_le_normalizer hTnorm⟩ ?_ O.f_mem O.f_not
      (orderOf_eq_prime (by rw [pow_two]; exact O.f_sq) hf1) ?_
    · exact Subgroup.commutator_le.mpr (fun x hx y hy => O.T_comm x hx y hy)
    · intro a ha
      exact O.T_cyc _ O.f_mem _ ha O.f_not (hfG a) (by rw [O.f_sq]; exact O.S.one_mem)
        (by
          have : a⁻¹ * O.f * a * (a⁻¹ * O.f * a) = 1 := by
            calc a⁻¹ * O.f * a * (a⁻¹ * O.f * a) = a⁻¹ * (O.f * O.f) * a := by group
              _ = 1 := by rw [O.f_sq]; group
          rw [this]; exact O.S.one_mem)
  exact hnotcomm

theorem burnsideF4d_mem_commutator_of_oTwoRes {G : Type} [Group G]
    (hO2 : oTwoRes (⊤ : Subgroup G) = ⊤) {x : G} (hx : x * x = 1) : x ∈ commutator G := by
  let T : Subgroup (Abelianization G) :=
    { carrier := {a | ∃ n : ℕ, Odd n ∧ a ^ n = 1}
      one_mem' := ⟨1, odd_one, one_pow 1⟩
      mul_mem' := by
        rintro a b ⟨m, hm, ha⟩ ⟨n, hn, hb⟩
        refine ⟨m * n, hm.mul hn, ?_⟩
        rw [mul_pow, pow_mul a m n, ha, one_pow, mul_comm m n, pow_mul b n m, hb, one_pow, one_mul]
      inv_mem' := by
        rintro a ⟨m, hm, ha⟩
        exact ⟨m, hm, by rw [inv_pow, ha, inv_one]⟩ }
  have hle : oTwoRes (⊤ : Subgroup G) ≤ T.comap (Abelianization.of : G →* Abelianization G) := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro y ⟨-, m, hm, hy⟩
    exact ⟨m, hm, by rw [← map_pow, hy, map_one]⟩
  rw [hO2] at hle
  obtain ⟨n, hn, hxn⟩ := hle (Subgroup.mem_top x)
  have h2 : (Abelianization.of x) ^ 2 = 1 := by rw [pow_two, ← map_mul, hx, map_one]
  have hg : Nat.gcd 2 n = 1 := (Nat.coprime_two_left.mpr hn)
  have h1 : (Abelianization.of x) ^ (Nat.gcd 2 n) = 1 := pow_gcd_eq_one.mpr ⟨h2, hxn⟩
  rw [hg, pow_one] at h1
  rw [← Abelianization.ker_of (G := G), MonoidHom.mem_ker]
  exact h1

end Out

section Y2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.Quasithin.H13.F431.L3 CFSG.QuasithinUnique.Borel252 CFSG.QuasithinUnique.Fin257.L3
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour
  CFSG.ASVolI.ChF

theorem burnsideF4d_Y2_pCore_eq {P E : Type} [Group P] [Group E] [Finite P] [Finite E]
    (Φ : P →* E) (hΦ : Function.Injective Φ) [hΦn : Φ.range.Normal]
    {U R₁ R₂ B₀ : Subgroup P} {s₁ s₂ : P} (hD : L3DData U R₁ R₂ B₀ s₁ s₂) {q : ℕ}
    (hO : L3OutHyp Φ U R₁ R₂ q) {N₁ N₂ : Subgroup E}
    (h₁ : N₁ = Subgroup.normalizer ((R₁.map Φ : Subgroup E) : Set E))
    (h₂ : N₂ = Subgroup.normalizer ((R₂.map Φ : Subgroup E) : Set E)) :
    N₁ ⊓ N₂ = Subgroup.normalizer ((U.map Φ : Subgroup E) : Set E) ∧
      pCoreOf 2 (N₁ ⊓ N₂) = U.map Φ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set I : Subgroup E := Φ.range with hI
  set T0 : Subgroup E := U.map Φ with hT0
  set Q₁ : Subgroup E := R₁.map Φ with hQ₁
  set Q₂ : Subgroup E := R₂.map Φ with hQ₂
  set B₀' : Subgroup E := B₀.map Φ with hB₀'
  have hIn : I.Normal := hΦn
  have hSylI : IsSylowTwoOf T0 I := isSylowTwoOf_map_range Φ hΦ hD.borel.sylow
  have hTp : IsPGroup 2 T0 := hSylI.2.1
  have hcenT : CFSG.Quasithin.centerOf T0 = (CFSG.Quasithin.centerOf U).map Φ :=
    centerOf_map_of_injective Φ hΦ U
  have hcardZ : Nat.card (CFSG.Quasithin.centerOf T0) = q := by
    rw [hcenT, Subgroup.card_map_of_injective hΦ]; exact hO.card_Z
  have hUN₁ : U ≤ Subgroup.normalizer (R₁ : Set P) :=
    Subgroup.le_normalizer.trans hD.borel.lt₁.le
  have hUN₂ : U ≤ Subgroup.normalizer (R₂ : Set P) :=
    Subgroup.le_normalizer.trans hD.borel.lt₂.le
  have hTN₁ : T0 ≤ N₁ := by
    rintro _ ⟨u, hu, rfl⟩
    rw [h₁]; exact map_mem_normalizer_map Φ (hUN₁ hu)
  have hTN₂ : T0 ≤ N₂ := by
    rintro _ ⟨u, hu, rfl⟩
    rw [h₂]; exact map_mem_normalizer_map Φ (hUN₂ hu)
  have hTsup : T0 = Q₁ ⊔ Q₂ := by rw [hT0, hQ₁, hQ₂, ← Subgroup.map_sup, hD.borel.sup]
  have hN_eq : N₁ ⊓ N₂ = Subgroup.normalizer (T0 : Set E) := by
    apply le_antisymm
    · intro n hn
      rw [hTsup]
      exact mem_normalizer_sup (h₁ ▸ hn.1) (h₂ ▸ hn.2)
    · intro n hn
      obtain ⟨hn1, hn2⟩ := hO.noswap n hn
      exact ⟨by rw [h₁]; exact hn1, by rw [h₂]; exact hn2⟩
  have hB₀N : B₀' ≤ Subgroup.normalizer (T0 : Set E) := by
    rintro _ ⟨b, hb, rfl⟩
    exact map_mem_normalizer_map Φ (hD.B₀_le hb)
  have hB₀I : B₀' ≤ I := Subgroup.map_le_range Φ B₀
  have hodd₀ : Odd (Nat.card B₀') := by
    rw [hB₀', Subgroup.card_map_of_injective hΦ]; exact hD.B₀_odd
  have hC : ∀ x ∈ T0, (∀ b ∈ B₀', x * b = b * x) → x = 1 := by
    rintro _ ⟨u, hu, rfl⟩ hcomm
    have : u = 1 := hD.centS u hu (fun b hb => hΦ (by
      rw [map_mul, map_mul]; exact hcomm _ (Subgroup.mem_map_of_mem Φ hb)))
    rw [this, map_one]
  have hUp : IsPGroup 2 U := hD.borel.sylow.2.1
  have hcardP : Nat.card (Subgroup.normalizer (U : Set P)) = Nat.card U * Nat.card B₀ :=
    card_eq_mul_of_split Subgroup.le_normalizer hD.B₀_le
      (fun x hx hxB => eq_one_of_pgroup_of_odd hUp hD.B₀_odd hx hxB) hD.mul
  have hcard : Nat.card ↥(Subgroup.normalizer (T0 : Set E) ⊓ I) =
      Nat.card T0 * Nat.card B₀' := by
    rw [hT0, normalizer_map_inf_range Φ hΦ U, Subgroup.card_map_of_injective hΦ, hcardP,
      Subgroup.card_map_of_injective hΦ, hB₀', Subgroup.card_map_of_injective hΦ]
  have hSk : OutSkel I T0 B₀' := ⟨hSylI, hB₀I, hB₀N, hodd₀, hC, hcard⟩
  have hZne : ∃ x ∈ CFSG.Quasithin.centerOf T0, x ≠ 1 := by
    obtain ⟨x, hx, -, -, hx1, -, -⟩ := hD.Z_big
    exact ⟨Φ x, by rw [hcenT]; exact Subgroup.mem_map_of_mem Φ hx,
      fun h => hx1 (hΦ (by rw [h, map_one]))⟩
  have hZtrans : ∀ x ∈ CFSG.Quasithin.centerOf T0, x ≠ 1 → ∀ y ∈ CFSG.Quasithin.centerOf T0,
      y ≠ 1 → ∃ c ∈ B₀', c * x * c⁻¹ = y := by
    intro x hx hx1 y hy hy1
    rw [hcenT] at hx hy
    obtain ⟨x', hx', rfl⟩ := hx
    obtain ⟨y', hy', rfl⟩ := hy
    have hx1' : x' ≠ 1 := fun h => hx1 (by rw [h, map_one])
    have hy1' : y' ≠ 1 := fun h => hy1 (by rw [h, map_one])
    obtain ⟨b, hb, hbxy⟩ := hD.trans x' hx' hx1' y' hy' hy1'
    exact ⟨Φ b, Subgroup.mem_map_of_mem Φ hb, by rw [← map_mul, ← map_inv, ← map_mul, hbxy]⟩
  have hq2 := hO.two_le
  have hout : ∀ b ∈ Subgroup.normalizer (T0 : Set E), (∃ k : ℕ, orderOf b = 2 ^ k) → b ∉ I →
      ¬ ∀ z ∈ CFSG.Quasithin.centerOf T0, b * z = z * b := by
    intro b hb hk hbI hcentr
    have h3 := (hO.bound b hb hk hbI).2.2 (CFSG.Quasithin.centerOf T0) hcenT.le hcentr
    rw [hcardZ] at h3
    nlinarith
  have hpc : pCoreOf 2 (N₁ ⊓ N₂) ≤ T0 := by
    rw [hN_eq]; exact hSk.pCore_le rfl hZtrans hZne hout
  exact ⟨hN_eq, le_antisymm hpc
    (CFSG.QuasithinUnique.le_pCoreOf_of_le_normalizer (le_inf hTN₁ hTN₂) hN_eq.le hTp)⟩

theorem burnsideF4d_Y2_card_U {P H : Type} [Group P] [Finite P] [Group H] (Φ : P →* H)
    {U R₁ R₂ B₀ : Subgroup P} {s₁ s₂ : P} (hD : L3DData U R₁ R₂ B₀ s₁ s₂) {q : ℕ}
    (hO : L3OutHyp Φ U R₁ R₂ q) : Nat.card U = q ^ 3 := by
  have hF := hD.frame
  have hcardQ₂ : Nat.card R₂ = q ^ 2 := by rw [← hF.card_eq]; exact hO.card_R₁
  have hUsup : U = R₁ ⊔ R₂ := hD.borel.sup.symm
  have hUN₁ : U ≤ Subgroup.normalizer (R₁ : Set P) :=
    Subgroup.le_normalizer.trans hD.borel.lt₁.le
  have hQ₂N : R₂ ≤ Subgroup.normalizer (R₁ : Set P) := hF.Q₂_le.trans hUN₁
  have h1 := A4.relIndex_sup_eq_of_le_normalizer' hQ₂N
  rw [sup_comm, ← hUsup] at h1
  have h2 := Subgroup.relIndex_mul_card R₁ R₂
  rw [hF.inter, hO.card_Z, hcardQ₂] at h2
  have hrel : R₁.relIndex U = q := by
    rw [h1]
    have hpos : 0 < q := by have := hO.two_le; omega
    have : R₁.relIndex R₂ * q = q * q := by rw [h2]; ring
    exact Nat.eq_of_mul_eq_mul_right hpos this
  have h := Subgroup.relIndex_mul_card R₁ U
  rw [inf_of_le_left hF.Q₁_le, hrel, hO.card_R₁] at h
  rw [← h]; ring

theorem burnsideF4d_Y2_cards {P E : Type} [Group P] [Finite P] [Group E]
    (Φ : P →* E) (hΦ : Function.Injective Φ)
    {U R₁ R₂ B₀ : Subgroup P} {s₁ s₂ : P} (hD : L3DData U R₁ R₂ B₀ s₁ s₂) {q : ℕ}
    (hO : L3OutHyp Φ U R₁ R₂ q) {N₁ N₂ : Subgroup E}
    (hN : N₁ ⊓ N₂ = Subgroup.normalizer ((U.map Φ : Subgroup E) : Set E))
    (h₁ : N₁ = Subgroup.normalizer ((R₁.map Φ : Subgroup E) : Set E))
    (h₂ : N₂ = Subgroup.normalizer ((R₂.map Φ : Subgroup E) : Set E)) :
    Nat.card ↥(ctr (pCoreOf 2 (Φ.range ⊓ (N₁ ⊓ N₂)))) = q ∧
      Nat.card ↥(pCoreOf 2 (Φ.range ⊓ N₁)) = q ^ 2 ∧
      Nat.card ↥(pCoreOf 2 (Φ.range ⊓ N₂)) = q ^ 2 ∧
      Nat.card ↥(pCoreOf 2 (Φ.range ⊓ (N₁ ⊓ N₂))) = q ^ 3 := by
  have e1 : Φ.range ⊓ (N₁ ⊓ N₂) = (Subgroup.normalizer (U : Set P)).map Φ := by
    rw [hN, inf_comm]; exact normalizer_map_inf_range Φ hΦ U
  have e2 : pCoreOf 2 (Φ.range ⊓ (N₁ ⊓ N₂)) = U.map Φ := by
    rw [e1, CFSG.Quasithin.H13.F431.pCoreOf_map_of_injective Φ hΦ,
      pCoreOf_normalizer_sylow hD.borel.sylow]
  refine ⟨?_, ?_, ?_, ?_⟩
  · show Nat.card ↥(CFSG.Quasithin.centerOf (pCoreOf 2 (Φ.range ⊓ (N₁ ⊓ N₂)))) = q
    rw [e2, centerOf_map_of_injective Φ hΦ, Subgroup.card_map_of_injective hΦ]
    exact hO.card_Z
  · have e3 : Φ.range ⊓ N₁ = (Subgroup.normalizer (R₁ : Set P)).map Φ := by
      rw [h₁, inf_comm]; exact normalizer_map_inf_range Φ hΦ R₁
    rw [e3, CFSG.Quasithin.H13.F431.pCoreOf_map_of_injective Φ hΦ, hD.borel.core₁,
      Subgroup.card_map_of_injective hΦ]
    exact hO.card_R₁
  · have e3 : Φ.range ⊓ N₂ = (Subgroup.normalizer (R₂ : Set P)).map Φ := by
      rw [h₂, inf_comm]; exact normalizer_map_inf_range Φ hΦ R₂
    rw [e3, CFSG.Quasithin.H13.F431.pCoreOf_map_of_injective Φ hΦ, hD.borel.core₂,
      Subgroup.card_map_of_injective hΦ, ← hD.frame.card_eq]
    exact hO.card_R₁
  · rw [e2, Subgroup.card_map_of_injective hΦ]
    exact burnsideF4d_Y2_card_U Φ hD hO

theorem burnsideF4d_Y2_mem_iff_stab {E : Type} [Group E] {Gp : Subgroup E} [Gp.Normal]
    (hinj : Function.Injective (burnsideF4d_rho Gp)) (M : Subgroup E)
    (hM : (burnsideF4d_rho Gp).range ⊓ autStab (M.subgroupOf Gp) = M.map (burnsideF4d_rho Gp))
    (e : E) : e ∈ M ↔ burnsideF4d_rho Gp e ∈ autStab (M.subgroupOf Gp) := by
  constructor
  · intro he
    have : burnsideF4d_rho Gp e ∈ M.map (burnsideF4d_rho Gp) := ⟨e, he, rfl⟩
    rw [← hM] at this
    exact this.2
  · intro he
    have : burnsideF4d_rho Gp e ∈
        (burnsideF4d_rho Gp).range ⊓ autStab (M.subgroupOf Gp) := ⟨⟨e, rfl⟩, he⟩
    rw [hM] at this
    exact (Subgroup.mem_map_iff_mem hinj).mp this

theorem burnsideF4d_Y2_setup {f : ℕ} (hf : 2 ≤ f) {E : Type} [Group E] [Finite E]
    {Gp M₁ M₂ : Subgroup E} (h : HypF_4_4g .L3 2 f Gp M₁ M₂) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (Φ : projectiveSL 3 F →* E)
      (R₁ R₂ : Subgroup (projectiveSL 3 F)) (s₁ s₂ : projectiveSL 3 F),
      Nat.card F = 2 ^ f ∧ Function.Injective Φ ∧ Φ.range = Gp ∧
      L3DData (projUnitriangular 3 F) R₁ R₂ (P3.torus3 F) s₁ s₂ ∧
      L3OutHyp Φ (projUnitriangular 3 F) R₁ R₂ (Nat.card F) ∧
      M₁ = Subgroup.normalizer ((R₁.map Φ : Subgroup E) : Set E) ∧
      M₂ = Subgroup.normalizer ((R₂.map Φ : Subgroup E) : Set E) := by
  obtain ⟨TD, hyam⟩ := burnsideF4d_Y1_yam h
  have hmodel := burnsideF4d_Y1_lieModel h
  haveI := h.normal
  have hinj : Function.Injective (burnsideF4d_rho Gp) :=
    burnsideF4d_rho_injective h.centralizer_trivial
  obtain ⟨F, hFf, hFfin, hFchar, E', hFcard, hP⟩ :=
    l3Amalgam_borel hmodel (burnsideF4d_amalgamExt h TD hyam)
  have hq4 : 4 ≤ Nat.card F := by
    rw [hFcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hdata := l3DData_projectiveSL hq4
  obtain ⟨R₁, R₂, s₁, s₂, hdat, hRv, h1, h2⟩ : ∃ (R₁ R₂ : Subgroup (projectiveSL 3 F))
      (s₁ s₂ : projectiveSL 3 F), L3DData (projUnitriangular 3 F) R₁ R₂ (P3.torus3 F) s₁ s₂ ∧
      ((R₁ = V1 ∧ R₂ = V2) ∨ (R₁ = V2 ∧ R₂ = V1)) ∧
      (M₁.subgroupOf Gp).map E'.toMonoidHom = Subgroup.normalizer (R₁ : Set (projectiveSL 3 F)) ∧
      (M₂.subgroupOf Gp).map E'.toMonoidHom =
        Subgroup.normalizer (R₂ : Set (projectiveSL 3 F)) := by
    rcases hP with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨_, _, _, _, hdata, Or.inl ⟨rfl, rfl⟩, h1, h2⟩
    · exact ⟨_, _, _, _, hdata.swap, Or.inr ⟨rfl, rfl⟩, h1, h2⟩
  haveI : Finite (projectiveSL 3 F) := Finite.of_equiv ↥Gp E'.toEquiv
  obtain ⟨Φ, hΦdef⟩ : ∃ Φ : projectiveSL 3 F →* E, ∀ p, Φ p = ((E'.symm p : ↥Gp) : E) :=
    ⟨Gp.subtype.comp E'.symm.toMonoidHom, fun p => rfl⟩
  have hΦinj : Function.Injective Φ := fun a b hab =>
    E'.symm.injective (Subtype.ext ((hΦdef a).symm.trans (hab.trans (hΦdef b))))
  have hΦapp : ∀ d : ↥Gp, Φ (E' d) = (d : E) := fun d => by
    rw [hΦdef, MulEquiv.symm_apply_apply]
  have hrange : Φ.range = Gp := by
    ext x
    constructor
    · rintro ⟨p, rfl⟩
      rw [hΦdef]
      exact (E'.symm p).2
    · intro hx
      exact ⟨E' ⟨x, hx⟩, hΦapp ⟨x, hx⟩⟩
  obtain ⟨ρ, hρcongr, hρinj⟩ : ∃ ρ : E →* MulAut (projectiveSL 3 F),
      (∀ e, ρ e = MulAut.congr E' (burnsideF4d_rho Gp e)) ∧ Function.Injective ρ :=
    ⟨(MulAut.congr E').toMonoidHom.comp (burnsideF4d_rho Gp), fun e => rfl,
      (MulAut.congr E').injective.comp hinj⟩
  have hρapp : ∀ (e : E) (p : projectiveSL 3 F),
      ρ e p = E' (burnsideF4d_rho Gp e (E'.symm p)) := fun e p => by
    rw [hρcongr]; rfl
  have hΦρ : ∀ (e : E) (p : projectiveSL 3 F), Φ (ρ e p) = e * Φ p * e⁻¹ := by
    intro e p
    rw [hρapp, hΦapp, burnsideF4d_rho_apply, hΦdef]
  have hN1 := burnsideF4d_N1_eq h hyam
  have hN2 := burnsideF4d_N2_eq h hyam
  have hiff1 := burnsideF4d_Y2_mem_iff_stab hinj M₁ hN1
  have hiff2 := burnsideF4d_Y2_mem_iff_stab hinj M₂ hN2
  have hsemi1 : ∀ e ∈ M₁, ρ e ∈ semilinearAutGroup 3 F := by
    intro e he
    have hst := autStab_transport E' h1 hdat.borel.core₁ ((hiff1 e).mp he)
    rw [hρcongr]
    rcases hRv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact P3.mem_semilinear_of_map_V1 fun g hg => (hst g).mp hg
    · exact P3.mem_semilinear_of_map_V2 fun g hg => (hst g).mp hg
  have hsemi2 : ∀ e ∈ M₂, ρ e ∈ semilinearAutGroup 3 F := by
    intro e he
    have hst := autStab_transport E' h2 hdat.borel.core₂ ((hiff2 e).mp he)
    rw [hρcongr]
    rcases hRv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact P3.mem_semilinear_of_map_V2 fun g hg => (hst g).mp hg
    · exact P3.mem_semilinear_of_map_V1 fun g hg => (hst g).mp hg
  have hE : ∀ e : E, ρ e ∈ semilinearAutGroup 3 F := by
    have hle : (⊤ : Subgroup E) ≤ (semilinearAutGroup 3 F).comap ρ := by
      rw [← h.gen]
      exact sup_le (fun e he => hsemi1 e he) (fun e he => hsemi2 e he)
    exact fun e => hle (Subgroup.mem_top e)
  have hO := P3.l3OutHyp_of_action hf hFcard ρ hρinj Φ hΦinj hΦρ hE hRv
  have hconj : ∀ (e : E) (X : Subgroup (projectiveSL 3 F)),
      e ∈ Subgroup.normalizer ((X.map Φ : Subgroup E) : Set E) ↔ ∀ p, p ∈ X ↔ ρ e p ∈ X := by
    intro e X
    rw [Subgroup.mem_normalizer_iff]
    constructor
    · intro hh p
      have := hh (Φ p)
      rw [Subgroup.mem_map_iff_mem hΦinj, ← hΦρ, Subgroup.mem_map_iff_mem hΦinj] at this
      exact this
    · intro hh y
      by_cases hy : y ∈ Φ.range
      · obtain ⟨p, rfl⟩ := hy
        rw [Subgroup.mem_map_iff_mem hΦinj, ← hΦρ, Subgroup.mem_map_iff_mem hΦinj]
        exact hh p
      · have h1 : y ∉ X.map Φ := fun hyX => hy (Subgroup.map_le_range Φ X hyX)
        have h2 : e * y * e⁻¹ ∉ X.map Φ := by
          intro hmem
          obtain ⟨q', -, hq'⟩ := hmem
          apply hy
          refine ⟨ρ e⁻¹ q', ?_⟩
          rw [hΦρ, hq']
          group
        exact ⟨fun hh' => absurd hh' h1, fun hh' => absurd hh' h2⟩
  have key : ∀ (M : Subgroup E) (r : Subgroup (projectiveSL 3 F)),
      (∀ e : E, e ∈ M ↔ burnsideF4d_rho Gp e ∈ autStab (M.subgroupOf Gp)) →
      (M.subgroupOf Gp).map E'.toMonoidHom = Subgroup.normalizer (r : Set (projectiveSL 3 F)) →
      pCoreOf 2 (Subgroup.normalizer (r : Set (projectiveSL 3 F))) = r →
      M = Subgroup.normalizer ((r.map Φ : Subgroup E) : Set E) := by
    intro M r hM hP hcore
    set S : Subgroup ↥Gp := r.map E'.symm.toMonoidHom with hS
    have hnS : (Subgroup.normalizer (r : Set (projectiveSL 3 F))).map E'.symm.toMonoidHom =
        Subgroup.normalizer (S : Set ↥Gp) := by
      ext g
      rw [Subgroup.mem_map_equiv, hS, mem_normalizer_map_equiv E'.symm r g]
    have hPS : M.subgroupOf Gp = Subgroup.normalizer (S : Set ↥Gp) := by
      rw [← hnS, ← hP, Subgroup.map_map]
      ext g
      simp
    have hcoreS : pCoreOf 2 (Subgroup.normalizer (S : Set ↥Gp)) = S := by
      rw [← hnS, CFSG.Quasithin.H13.F431.pCoreOf_map_of_injective E'.symm.toMonoidHom
        E'.symm.injective, hcore]
    have hmemS : ∀ x : ↥Gp, x ∈ S ↔ E' x ∈ r := fun x => by
      rw [hS, Subgroup.mem_map_equiv]
      simp
    ext e
    rw [hM e, hPS, mem_autStab_iff_of_normalizer hcoreS, hconj]
    constructor
    · intro H p
      have h3 := H (E'.symm p)
      rw [hmemS, hmemS, MulEquiv.apply_symm_apply, ← hρapp] at h3
      exact h3
    · intro H x
      have h3 := H (E' x)
      rw [hρapp, MulEquiv.symm_apply_apply] at h3
      rw [hmemS, hmemS]
      exact h3
  exact ⟨F, hFf, hFfin, hFchar, Φ, R₁, R₂, s₁, s₂, hFcard, hΦinj, hrange, hdat, hO,
    key M₁ R₁ hiff1 h1 hdat.borel.core₁, key M₂ R₂ hiff2 h2 hdat.borel.core₂⟩

theorem burnsideF4d_Y2_pCore_le {f : ℕ} (hf : 2 ≤ f) {E : Type} [Group E] [Finite E]
    {Gp M₁ M₂ : Subgroup E} (h : CFSG.ASVolI.ChF.HypF_4_4g .L3 2 f Gp M₁ M₂) :
    pCoreOf 2 (M₁ ⊓ M₂) ≤ Gp := by
  obtain ⟨F, hFf, hFfin, hFchar, Φ, R₁, R₂, s₁, s₂, hFcard, hΦ, hrange, hD, hO, h₁, h₂⟩ :=
    burnsideF4d_Y2_setup hf h
  haveI : Finite (projectiveSL 3 F) := Finite.of_injective Φ hΦ
  haveI := h.normal
  haveI : Φ.range.Normal := by rw [hrange]; infer_instance
  rw [(burnsideF4d_Y2_pCore_eq Φ hΦ hD hO h₁ h₂).2, ← hrange]
  exact Subgroup.map_le_range Φ _

theorem burnsideF4d_Y2_card_Z {f : ℕ} (hf : 2 ≤ f) {E : Type} [Group E] [Finite E]
    {Gp M₁ M₂ : Subgroup E} (h : CFSG.ASVolI.ChF.HypF_4_4g .L3 2 f Gp M₁ M₂) :
    Nat.card ↥(CFSG.ASVolI.ChF.ctr (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)))) = 2 ^ f := by
  obtain ⟨F, hFf, hFfin, hFchar, Φ, R₁, R₂, s₁, s₂, hFcard, hΦ, hrange, hD, hO, h₁, h₂⟩ :=
    burnsideF4d_Y2_setup hf h
  haveI : Finite (projectiveSL 3 F) := Finite.of_injective Φ hΦ
  haveI := h.normal
  haveI : Φ.range.Normal := by rw [hrange]; infer_instance
  have hN := (burnsideF4d_Y2_pCore_eq Φ hΦ hD hO h₁ h₂).1
  have := (burnsideF4d_Y2_cards Φ hΦ hD hO hN h₁ h₂).1
  rw [hrange] at this
  exact this.trans hFcard


end Y2

section PCore

variable {E : Type} [Group E] [Finite E] {Gp : Subgroup E} [Gp.Normal]

theorem burnsideF4d_pCoreOf_inf_eq (K : Subgroup E) (hle : pCoreOf 2 K ≤ Gp) :
    pCoreOf 2 (Gp ⊓ K) = pCoreOf 2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm
  · have hKN : K ≤ Subgroup.normalizer ((Gp ⊓ K : Subgroup E) : Set E) := by
      intro k hk
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · rintro ⟨hx, hxK⟩
        exact ⟨Subgroup.Normal.conj_mem inferInstance x hx k, K.mul_mem (K.mul_mem hk hxK) (K.inv_mem hk)⟩
      · rintro ⟨hx, hxK⟩
        refine ⟨?_, ?_⟩
        · have := Subgroup.Normal.conj_mem (inferInstance : Gp.Normal) _ hx k⁻¹
          simpa [mul_assoc] using this
        · have := K.mul_mem (K.mul_mem (K.inv_mem hk) hxK) hk
          simpa [mul_assoc] using this
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      (CFSG.LieType.BorelTits.pCoreOf_le 2 _ |>.trans inf_le_right)
      (hKN.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
  · exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      (le_inf hle (CFSG.LieType.BorelTits.pCoreOf_le 2 K))
      ((inf_le_right).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K)

theorem burnsideF4d_pCoreOf_le_of_odd (hodd : Odd Gp.index) (K : Subgroup E) :
    pCoreOf 2 K ≤ Gp := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro x hx
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K))
    ⟨x, hx⟩
  have hx2 : orderOf x = 2 ^ k := by
    rw [← Subgroup.orderOf_mk x hx]; exact hk
  have h1 : orderOf (QuotientGroup.mk x : E ⧸ Gp) ∣ 2 ^ k :=
    hx2 ▸ orderOf_dvd_of_pow_eq_one (by rw [← QuotientGroup.mk_pow, pow_orderOf_eq_one]; rfl)
  have h2 : orderOf (QuotientGroup.mk x : E ⧸ Gp) ∣ Gp.index := by
    rw [Subgroup.index]
    exact orderOf_dvd_natCard _
  have h3 : Nat.Coprime (2 ^ k) Gp.index := Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
  have h4 : orderOf (QuotientGroup.mk x : E ⧸ Gp) = 1 :=
    Nat.eq_one_of_dvd_coprimes h3 h1 h2
  exact (QuotientGroup.eq_one_iff x).mp (orderOf_eq_one_iff.mp h4)

end PCore

section Trans

open CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion CFSG.ASVolI.ChF
  CFSG.Quasithin.H13.F431.L3

variable {E : Type} [Group E] {M₁ M₂ : Subgroup E} {Y : Type} [Group Y] {M : Type} [Group M]

theorem burnsideF4d_GiOne_eq (Gp : Subgroup E) (β : Cpl M₁ M₂ Y) (ε : Y →* M) :
    GiOne Gp β ε = subImg (burnsideF4d_bOne β ε) (Gp ⊓ M₁) := by
  unfold GiOne subImg burnsideF4d_bOne
  exact Subgroup.map_map ((Gp ⊓ M₁).subgroupOf M₁) (epsG β ε) (f1 (c := β))

theorem burnsideF4d_GiTwo_eq (Gp : Subgroup E) (β : Cpl M₁ M₂ Y) (ε : Y →* M) :
    GiTwo Gp β ε = subImg (burnsideF4d_bTwo β ε) (Gp ⊓ M₂) := by
  unfold GiTwo subImg burnsideF4d_bTwo
  exact Subgroup.map_map ((Gp ⊓ M₂).subgroupOf M₂) (epsG β ε) (f2 (c := β))

theorem burnsideF4d_MiOne_eq (β : Cpl M₁ M₂ Y) (ε : Y →* M) :
    MiOne β ε = subImg (burnsideF4d_bOne β ε) M₁ := by
  rw [subImg_self]
  unfold MiOne burnsideF4d_bOne
  exact (MonoidHom.range_comp _ _).symm

theorem burnsideF4d_MiTwo_eq (β : Cpl M₁ M₂ Y) (ε : Y →* M) :
    MiTwo β ε = subImg (burnsideF4d_bTwo β ε) M₂ := by
  rw [subImg_self]
  unfold MiTwo burnsideF4d_bTwo
  exact (MonoidHom.range_comp _ _).symm

theorem burnsideF4d_inter_eq (β : Cpl M₁ M₂ Y) (hβ : β.IsFaithful) (ε : Y →* M)
    (hε : Function.Injective (epsG β ε)) :
    MiOne β ε ⊓ MiTwo β ε = subImg (burnsideF4d_bOne β ε) (M₁ ⊓ M₂) := by
  let T := burnsideF4d_amalgIsoM β hβ ε hε
  ext x
  change x ∈ MiOne β ε ⊓ MiTwo β ε ↔ x ∈ subImg T.b₁ (M₁ ⊓ M₂)
  rw [T.mem_H, mem_subImg]
  constructor
  · rintro ⟨g, h1, h2, rfl⟩
    exact ⟨g, h1, ⟨h1, h2⟩, rfl⟩
  · rintro ⟨g, h1, ⟨h1', h2⟩, rfl⟩
    exact ⟨g, h1, h2, rfl⟩

end Trans

section Trans2

open CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion CFSG.ASVolI.ChF
  CFSG.Quasithin.H13.F431.L3

variable {E : Type} [Group E] {M₁ M₂ : Subgroup E} {Y : Type} [Group Y] {M : Type} [Group M]

theorem burnsideF4d_map_inclusion_subgroupOf (Y' : Subgroup E) (hY : Y' ≤ M₁ ⊓ M₂) :
    (Y'.subgroupOf (M₁ ⊓ M₂)).map (RankTwoAmalgam.ofSubgroups M₁ M₂).α1 = Y'.subgroupOf M₁ := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    let x' : ↥M₁ := x
    exact ⟨⟨(x' : E), ⟨x'.2, (hY hx).2⟩⟩, hx, rfl⟩

theorem burnsideF4d_SinM_eq (Gp : Subgroup E) (β : Cpl M₁ M₂ Y) (ε : Y →* M) :
    SinM Gp β ε = subImg (burnsideF4d_bOne β ε) (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) := by
  have hY : pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ≤ M₁ ⊓ M₂ :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_right
  unfold SinM Sp subImg burnsideF4d_bOne
  rw [burnsideF4d_map_inclusion_subgroupOf _ hY]
  exact Subgroup.map_map ((pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))).subgroupOf M₁) (epsG β ε) (f1 (c := β))

theorem burnsideF4d_SinM_eq_pCore [Finite E] (Gp : Subgroup E) [Gp.Normal] (β : Cpl M₁ M₂ Y)
    (hβ : β.IsFaithful) (ε : Y →* M) (hε : Function.Injective (epsG β ε))
    (hle : pCoreOf 2 (M₁ ⊓ M₂) ≤ Gp) :
    SinM Gp β ε = pCoreOf 2 (MiOne β ε ⊓ MiTwo β ε) := by
  rw [burnsideF4d_SinM_eq, burnsideF4d_inter_eq β hβ ε hε,
    burnsideF4d_pCoreOf_inf_eq (Gp := Gp) (M₁ ⊓ M₂) hle]
  exact (subImg_pCoreOf (burnsideF4d_amalgIsoM β hβ ε hε).inj₁ (inf_le_left : M₁ ⊓ M₂ ≤ M₁)).symm

end Trans2

section OddL3

open CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion CFSG.ASVolI.ChF
  CFSG.Quasithin.H13.F431.L3

theorem burnsideF4d_L3_odd {f : ℕ} (hf : 2 ≤ f) {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    {Y : Type} [Group Y] {β : Cpl M₁ M₂ Y} {M : Type} [Group M] {ε : Y →* M} {z : M}
    (hyp : HypF_4_31 .L3 f Gp M₁ M₂ β ε z) : Odd Gp.index := by
  by_contra hnodd
  haveI := hyp.amalgam.finite
  haveI := hyp.finite_M
  have hyp4 := hyp.amalgam.toHypF_4_4g
  haveI := hyp4.normal
  obtain ⟨TD, hyam⟩ := burnsideF4d_Y1_yam hyp4
  have hmodel := burnsideF4d_Y1_lieModel hyp4
  have hinj : Function.Injective (burnsideF4d_rho Gp) :=
    burnsideF4d_rho_injective hyp4.centralizer_trivial
  let X := burnsideF4d_lieExtE hyp4 hyam
  have hK : Nat.card ↥X.K = Nat.card E := by
    have : X.K = (burnsideF4d_rho Gp).range := burnsideF4d_K_eq hyp4 hyam
    rw [this, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
  have hnodd' : ¬ Odd (Nat.card ↥X.K / Nat.card ↥Gp) := by
    rw [hK]
    have := Subgroup.card_mul_index Gp
    have hpos : 0 < Nat.card ↥Gp := Nat.card_pos
    rw [show Nat.card E / Nat.card ↥Gp = Gp.index by
      rw [← this, Nat.mul_div_cancel_left _ hpos]]
    exact hnodd
  obtain ⟨O⟩ := f431L3OutLie f hf ↥Gp hmodel X.toLieAmalgamExt hnodd'
  obtain ⟨O1⟩ := O.nonempty_transport X.amalgIso
  obtain ⟨Og⟩ := O1.nonempty_transport (burnsideF4d_amalgIsoM β hyp.faithful ε hyp.inj)
  have hle : pCoreOf 2 (M₁ ⊓ M₂) ≤ Gp := burnsideF4d_Y2_pCore_le hf hyp4
  have hS : SinM Gp β ε = pCoreOf 2 (MiOne β ε ⊓ MiTwo β ε) :=
    burnsideF4d_SinM_eq_pCore Gp β hyp.faithful ε hyp.inj hle
  have hz : z ∈ centerOf Og.S := by
    have h1 := hyp.z_mem.2 rfl
    rw [Og.S_eq, ← hS]
    exact h1
  have hz1 : z ≠ 1 := hyp.z_inv.1
  have hnc := burnsideF4d_Out_not_mem_commutator Og hz hz1 hyp.hb
  have hO2 : oTwoRes (⊤ : Subgroup M) = ⊤ :=
    hyp.he.resolve_right (by rintro ⟨h1, -⟩; omega)
  exact hnc (burnsideF4d_mem_commutator_of_oTwoRes hO2 Og.f_sq)

end OddL3

section OPP

open CFSG.ASVolI.ChF

variable {E : Type} [Group E]

theorem burnsideF4d_oPPrime_map {A B : Type} [Group A] [Group B] (φ : A →* B)
    (hφ : Function.Injective φ) (p : ℕ) (X : Subgroup A) :
    oPPrime p (X.map φ) = (oPPrime p X).map φ := by
  unfold oPPrime
  rw [MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨hy, k, hk⟩
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    exact ⟨x, ⟨hx, k, by rw [← hk, orderOf_injective φ hφ x]⟩, rfl⟩
  · rintro ⟨x, ⟨hx, k, hk⟩, rfl⟩
    exact ⟨Subgroup.mem_map_of_mem φ hx, k, by rw [orderOf_injective φ hφ x, hk]⟩

theorem burnsideF4d_subImg_oPPrime {Mb G : Type} [Group Mb] [Group G] {N : Subgroup Mb}
    (b : ↥N →* G) (hb : Function.Injective b) {X : Subgroup Mb} (hX : X ≤ N) (p : ℕ) :
    oPPrime p (subImg b X) = subImg b (oPPrime p X) := by
  unfold subImg
  rw [burnsideF4d_oPPrime_map b hb]
  congr 1
  have h1 : oPPrime p X = (oPPrime p (X.subgroupOf N)).map N.subtype := by
    rw [← burnsideF4d_oPPrime_map N.subtype N.subtype_injective,
      Subgroup.map_subgroupOf_eq_of_le hX]
  rw [h1, CFSG.Quasithin.H13.F431.L3.subgroupOf_map_subtype_self]

theorem burnsideF4d_le_normalizer_oPPrime (H : Subgroup E) :
    H ≤ Subgroup.normalizer (oPPrime 2 H : Set E) := by
  have key : ∀ g ∈ H, ∀ x ∈ oPPrime 2 H, g * x * g⁻¹ ∈ oPPrime 2 H := by
    intro g hg x hx
    unfold oPPrime at hx ⊢
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨hyH, k, hk⟩ := hy
      refine Subgroup.subset_closure ⟨H.mul_mem (H.mul_mem hg hyH) (H.inv_mem hg), k, ?_⟩
      rw [← hk]
      exact (MulEquiv.orderOf_eq (MulAut.conj g) y)
    | one => simpa using Subgroup.one_mem _
    | mul a b _ _ ha hb =>
      have : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
      rw [this]; exact Subgroup.mul_mem _ ha hb
    | inv a _ ha =>
      have : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
      rw [this]; exact Subgroup.inv_mem _ ha
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact key g hg x
  · intro hx
    have := key g⁻¹ (H.inv_mem hg) _ hx
    simpa [mul_assoc] using this

theorem burnsideF4d_oPPrime_le (H : Subgroup E) : oPPrime 2 H ≤ H :=
  (Subgroup.closure_le H).mpr fun _ hx => hx.1

variable [Finite E]

theorem burnsideF4d_pCoreOf_oPPrime (H : Subgroup E) :
    pCoreOf 2 (oPPrime 2 H) = pCoreOf 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm
  · exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans (burnsideF4d_oPPrime_le H))
      ((burnsideF4d_le_normalizer_oPPrime H).trans
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
  · have hle : pCoreOf 2 H ≤ oPPrime 2 H := by
      intro y hy
      obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H) ⟨y, hy⟩
      exact Subgroup.subset_closure ⟨CFSG.LieType.BorelTits.pCoreOf_le 2 H hy, k, by
        rw [← Subgroup.orderOf_mk y hy]; exact hk⟩
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hle
      ((burnsideF4d_oPPrime_le H).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H)

end OPP

section DatumFacts

open CFSG.Quasithin.H13.F431.L3

variable {G : Type} [Group G] [Finite G] {M₁ M₂ : Subgroup G}

theorem burnsideF4d_exists_Q₁_not_Z (D : L3Datum M₁ M₂) : ∃ x ∈ D.Q₁, x ∉ D.Z := by
  by_contra h
  push Not at h
  have hle : D.Q₁ ≤ D.Q₂ := fun x hx => by
    have hxZ := h x hx
    have : x ∈ D.Q₁ ⊓ D.Q₂ := by rw [D.frame.inter]; exact hxZ
    exact this.2
  exact D.frame.Q_ne (Subgroup.eq_of_le_of_card_ge hle (le_of_eq D.frame.card_eq.symm))

theorem burnsideF4d_exists_Q₂_not_Z (D : L3Datum M₁ M₂) : ∃ x ∈ D.Q₂, x ∉ D.Z := by
  by_contra h
  push Not at h
  have hle : D.Q₂ ≤ D.Q₁ := fun x hx => by
    have hxZ := h x hx
    have : x ∈ D.Q₁ ⊓ D.Q₂ := by rw [D.frame.inter]; exact hxZ
    exact this.1
  exact D.frame.Q_ne (Subgroup.eq_of_le_of_card_ge hle (le_of_eq D.frame.card_eq)).symm

theorem burnsideF4d_Q₁_eq (D : L3Datum M₁ M₂) : D.Q₁ = pCoreOf 2 M₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm
  · refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (D.frame.Q₁_le.trans D.S_le_M₁) ?_
      (D.S_pgroup.to_le D.frame.Q₁_le)
    intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact fun hx => D.Q₁_norm m hm x hx
    · intro hx
      have := D.Q₁_norm m⁻¹ (M₁.inv_mem hm) _ hx
      simpa [mul_assoc] using this
  · intro r hr
    have hSyl : IsSylowTwoOf D.S M₁ := ⟨D.S_le_M₁, D.S_pgroup, D.S_index⟩
    have hrS : r ∈ D.S := F7.isSylowTwoOf_pCoreOf_le hSyl hr
    obtain ⟨x₀, hx₀Q, hx₀Z⟩ := burnsideF4d_exists_Q₁_not_Z D
    have hx₀1 : x₀ ≠ 1 := fun h => hx₀Z (h ▸ D.Z.one_mem)
    obtain ⟨m, hm, hmz⟩ := D.cov₁ x₀ hx₀Q hx₀1
    have hrm : m * r * m⁻¹ ∈ pCoreOf 2 M₁ :=
      (Subgroup.mem_normalizer_iff.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M₁ hm) r).mp hr
    have hrmS : m * r * m⁻¹ ∈ D.S := F7.isSylowTwoOf_pCoreOf_le hSyl hrm
    have h' : (m * r * m⁻¹) * (m * x₀ * m⁻¹) = (m * x₀ * m⁻¹) * (m * r * m⁻¹) :=
      (D.mem_Z.mp hmz).2 _ hrmS
    have hcomm : r * x₀ = x₀ * r := by
      calc r * x₀ = m⁻¹ * ((m * r * m⁻¹) * (m * x₀ * m⁻¹)) * m := by group
        _ = m⁻¹ * ((m * x₀ * m⁻¹) * (m * r * m⁻¹)) * m := by rw [h']
        _ = x₀ * r := by group
    exact D.frame.cent₁ x₀ hx₀Q hx₀Z r hrS hcomm

theorem burnsideF4d_Q₂_eq (D : L3Datum M₁ M₂) (hSyl : IsSylowTwoOf D.S M₂) :
    D.Q₂ = pCoreOf 2 M₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm
  · refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (D.frame.Q₂_le.trans D.S_le_M₂) ?_
      (D.S_pgroup.to_le D.frame.Q₂_le)
    intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact fun hx => D.Q₂_norm m hm x hx
    · intro hx
      have := D.Q₂_norm m⁻¹ (M₂.inv_mem hm) _ hx
      simpa [mul_assoc] using this
  · intro r hr
    have hrS : r ∈ D.S := F7.isSylowTwoOf_pCoreOf_le hSyl hr
    obtain ⟨x₀, hx₀Q, hx₀Z⟩ := burnsideF4d_exists_Q₂_not_Z D
    have hx₀1 : x₀ ≠ 1 := fun h => hx₀Z (h ▸ D.Z.one_mem)
    obtain ⟨m, hm, hmz⟩ := D.cov₂ x₀ hx₀Q hx₀1
    have hrm : m * r * m⁻¹ ∈ pCoreOf 2 M₂ :=
      (Subgroup.mem_normalizer_iff.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M₂ hm) r).mp hr
    have hrmS : m * r * m⁻¹ ∈ D.S := F7.isSylowTwoOf_pCoreOf_le hSyl hrm
    have h' : (m * r * m⁻¹) * (m * x₀ * m⁻¹) = (m * x₀ * m⁻¹) * (m * r * m⁻¹) :=
      (D.mem_Z.mp hmz).2 _ hrmS
    have hcomm : r * x₀ = x₀ * r := by
      calc r * x₀ = m⁻¹ * ((m * r * m⁻¹) * (m * x₀ * m⁻¹)) * m := by group
        _ = m⁻¹ * ((m * x₀ * m⁻¹) * (m * r * m⁻¹)) * m := by rw [h']
        _ = x₀ * r := by group
    exact D.frame.cent₂ x₀ hx₀Q hx₀Z r hrS hcomm


end DatumFacts

section Setup

open CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion CFSG.ASVolI.ChF
  CFSG.Quasithin.H13.F431.L3

variable {E : Type} [Group E] [Finite E] {Gp M₁ M₂ : Subgroup E} [Gp.Normal]
  {Y : Type} [Group Y] {M : Type} [Group M]

theorem burnsideF4d_Qhat_one (hodd : Odd Gp.index) (β : Cpl M₁ M₂ Y) (hβ : β.IsFaithful)
    (ε : Y →* M) (hε : Function.Injective (epsG β ε)) :
    pCoreOf 2 (oPPrime 2 (GiOne Gp β ε)) = pCoreOf 2 (MiOne β ε) := by
  have hb : Function.Injective (burnsideF4d_bOne β ε) := hε.comp (f1_injective β hβ)
  have hle : pCoreOf 2 M₁ ≤ Gp := burnsideF4d_pCoreOf_le_of_odd hodd M₁
  have hE : pCoreOf 2 (oPPrime 2 (Gp ⊓ M₁)) = pCoreOf 2 M₁ := by
    rw [burnsideF4d_pCoreOf_oPPrime, burnsideF4d_pCoreOf_inf_eq M₁ hle]
  rw [burnsideF4d_GiOne_eq, burnsideF4d_MiOne_eq,
    burnsideF4d_subImg_oPPrime _ hb (inf_le_right : Gp ⊓ M₁ ≤ M₁),
    subImg_pCoreOf hb ((burnsideF4d_oPPrime_le _).trans inf_le_right),
    subImg_pCoreOf hb (le_refl M₁), hE]

theorem burnsideF4d_Qhat_two (hodd : Odd Gp.index) (β : Cpl M₁ M₂ Y) (hβ : β.IsFaithful)
    (ε : Y →* M) (hε : Function.Injective (epsG β ε)) :
    pCoreOf 2 (oPPrime 2 (GiTwo Gp β ε)) = pCoreOf 2 (MiTwo β ε) := by
  have hb : Function.Injective (burnsideF4d_bTwo β ε) := hε.comp (f2_injective β hβ)
  have hle : pCoreOf 2 M₂ ≤ Gp := burnsideF4d_pCoreOf_le_of_odd hodd M₂
  have hE : pCoreOf 2 (oPPrime 2 (Gp ⊓ M₂)) = pCoreOf 2 M₂ := by
    rw [burnsideF4d_pCoreOf_oPPrime, burnsideF4d_pCoreOf_inf_eq M₂ hle]
  rw [burnsideF4d_GiTwo_eq, burnsideF4d_MiTwo_eq,
    burnsideF4d_subImg_oPPrime _ hb (inf_le_right : Gp ⊓ M₂ ≤ M₂),
    subImg_pCoreOf hb ((burnsideF4d_oPPrime_le _).trans inf_le_right),
    subImg_pCoreOf hb (le_refl M₂), hE]

end Setup

section Setup2

open CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion CFSG.ASVolI.ChF
  CFSG.Quasithin.H13.F431.L3

theorem burnsideF4d_L3_setup {f : ℕ} (hf : 2 ≤ f) {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    {Y : Type} [Group Y] {β : Cpl M₁ M₂ Y} {M : Type} [Group M] {ε : Y →* M} {z : M}
    (hyp : HypF_4_31 .L3 f Gp M₁ M₂ β ε z) :
    ∃ D : L3Datum (MiOne β ε) (MiTwo β ε), D.Good ∧ z ∈ D.Z ∧ D.S = SinM Gp β ε ∧
      D.Q₁ = pCoreOf 2 (oPPrime 2 (GiOne Gp β ε)) ∧
      D.Q₂ = pCoreOf 2 (oPPrime 2 (GiTwo Gp β ε)) := by
  haveI := hyp.amalgam.finite
  haveI := hyp.finite_M
  haveI := hyp.amalgam.toHypF_4_4g.normal
  have hodd : Odd Gp.index := burnsideF4d_L3_odd hf hyp
  obtain ⟨D⟩ := burnsideF4d_L3_datumM hf hyp hodd
  have hS : SinM Gp β ε = pCoreOf 2 (MiOne β ε ⊓ MiTwo β ε) :=
    burnsideF4d_SinM_eq_pCore Gp β hyp.faithful ε hyp.inj
      (burnsideF4d_pCoreOf_le_of_odd hodd _)
  have hDS : D.S = SinM Gp β ε := by rw [D.S_eq, hS]
  have hz : z ∈ D.Z := by
    have h1 := hyp.z_mem.2 rfl
    show z ∈ centerOf D.S
    rw [hDS]
    exact h1
  have hz1 : z ≠ 1 := hyp.z_inv.1
  have hG : D.Good := L3Datum.Good.of_hyp hz hz1 hyp.hb
  refine ⟨D, hG, hz, hDS, ?_, ?_⟩
  · rw [burnsideF4d_Qhat_one hodd β hyp.faithful ε hyp.inj, burnsideF4d_Q₁_eq D]
  · rw [burnsideF4d_Qhat_two hodd β hyp.faithful ε hyp.inj,
      burnsideF4d_Q₂_eq D (F7.isSylowTwoOf_mono_right hG.sylow_top D.S_le_M₂ le_top)]

end Setup2

section Cards

open CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion CFSG.ASVolI.ChF
  CFSG.Quasithin.H13.F431.L3


end Cards

section TwoLeF

open CFSG.ASVolI.ChF

theorem burnsideF4d_L3_two_le_f {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    {Y : Type} [Group Y] {β : Cpl M₁ M₂ Y} {M : Type} [Group M] {ε : Y →* M} {z : M}
    (hyp : HypF_4_31 .L3 f Gp M₁ M₂ β ε z) : 2 ≤ f := by
  have h1 : 1 ≤ f := by
    have := hyp.amalgam.model
    exact this.2.1
  have h2 : f ≠ 1 := fun h => hyp.not_L32 ⟨rfl, h⟩
  omega

end TwoLeF

section TwoElt

variable {E : Type} [Group E] [Finite E] {Gp : Subgroup E} [Gp.Normal]


end TwoElt

end F4dBaseRest

section F4dPartZ1

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion CFSG.ASVolI.ChF
  CFSG.Quasithin.H13.F431.L3

section Z1Basic

variable {G : Type} [Group G]


theorem burnsideF4d_Z1_orderOf_of_mem {P : Subgroup G} (hP : IsPGroup 2 P) {x : G} (hx : x ∈ P) :
    ∃ k : ℕ, orderOf x = 2 ^ k := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hP) ⟨x, hx⟩
  exact ⟨k, by rw [← Subgroup.orderOf_mk x hx]; exact hk⟩

theorem burnsideF4d_Z1_le_oPPrime {P K : Subgroup G} (hP : IsPGroup 2 P) (hPK : P ≤ K) :
    P ≤ oPPrime 2 K := by
  intro x hx
  obtain ⟨k, hk⟩ := burnsideF4d_Z1_orderOf_of_mem hP hx
  exact Subgroup.subset_closure ⟨hPK hx, k, hk⟩

theorem burnsideF4d_Z1_normalizer_oPPrime {K : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ Subgroup.normalizer (oPPrime 2 K : Set G) := by
  apply mem_normalizer_of_conjSub_eq
  have h1 : conjSub g (oPPrime 2 K) = oPPrime 2 (conjSub g K) :=
    (burnsideF4d_oPPrime_map (MulAut.conj g).toMonoidHom (MulAut.conj g).injective 2 K).symm
  rw [h1, conjSub_eq_of_mem_normalizer hg]

theorem burnsideF4d_Z1_mem_normalizer_inf (Gp : Subgroup G) [Gp.Normal] {N : Subgroup G} {n : G}
    (hn : n ∈ N) : n ∈ Subgroup.normalizer ((Gp ⊓ N : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  simp only [Subgroup.mem_inf]
  constructor
  · rintro ⟨hy, hyN⟩
    exact ⟨Subgroup.Normal.conj_mem inferInstance y hy n,
      N.mul_mem (N.mul_mem hn hyN) (N.inv_mem hn)⟩
  · rintro ⟨hy, hyN⟩
    refine ⟨?_, ?_⟩
    · have := Subgroup.Normal.conj_mem (inferInstance : Gp.Normal) _ hy n⁻¹
      simpa [mul_assoc] using this
    · have := N.mul_mem (N.mul_mem (N.inv_mem hn) hyN) hn
      simpa [mul_assoc] using this

end Z1Basic

section Z1Datum

variable {G : Type} [Group G] [Finite G] {M₁ M₂ : Subgroup G} {D : L3Datum M₁ M₂}


end Z1Datum

section Z1Count

variable {G : Type} [Group G] [Finite G]


variable {M₁ M₂ : Subgroup G} {D : L3Datum M₁ M₂}


end Z1Count

section Z1Transport

variable {X M : Type} [Group X] [Group M] {N : Subgroup X}


end Z1Transport

section Z1Main


end Z1Main

end F4dPartZ1

section F4dPartZ2

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.Quasithin.H13.F431.L3

section Dihedral

variable {G : Type} [Group G]


end Dihedral

section Cases

variable {G : Type} [Group G] [Finite G] {M₁ M₂ : Subgroup G} {D : L3Datum M₁ M₂}


end Cases


end F4dPartZ2

section F4dPartZ3

section Z3Group


theorem burnsideF4d_Z3_solvable_of_normal {G : Type} [Group G] [Finite G] {A N : Subgroup G}
    [N.Normal] (hN : Group.IsSolvable ↥(A ⊓ N)) (hodd : Odd (N.relIndex A)) :
    Group.IsSolvable ↥A := by
  let ι : ↥(N.subgroupOf A) →* ↥(A ⊓ N) :=
    { toFun := fun x => ⟨(x.1 : G), x.1.2, x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hι : Function.Injective ι := by
    intro a b h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : ↥(A ⊓ N) => (x : G)) h
  haveI : Group.IsSolvable ↥(N.subgroupOf A) := Group.isSolvable_of_isSolvable_injective hι
  haveI : Group.IsSolvable (↥A ⧸ N.subgroupOf A) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  exact Group.isSolvable_of_ker_le_range (N.subgroupOf A).subtype
    (QuotientGroup.mk' (N.subgroupOf A))
    (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

end Z3Group

section Z3Core

open CFSG.BenderSuzuki

theorem burnsideF4d_Z3_solvable_of_borel {G : Type} [Group G] [Finite G] {M₀ K : Subgroup G}
    (hK : K ≤ M₀ ⊓ involutionCore G)
    (hB : Group.IsSolvable ↥(((M₀ ⊓ involutionCore G).subgroupOf (involutionCore G)).map
      (QuotientGroup.mk' (twoPrimeCore (involutionCore G))))) : Group.IsSolvable ↥K := by
  set L := involutionCore G
  set T := twoPrimeCore L
  have hTsolv : Group.IsSolvable ↥T := by
    have hodd : Odd (Nat.card T) :=
      Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := L))
    exact CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  let g : ↥K →* ↥(((M₀ ⊓ L).subgroupOf L).map (QuotientGroup.mk' T)) :=
    { toFun := fun c => ⟨QuotientGroup.mk' T ⟨c, (hK c.2).2⟩,
        ⟨⟨c, (hK c.2).2⟩, ⟨(hK c.2).1, (hK c.2).2⟩, rfl⟩⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hmem : ∀ k : ↥g.ker, (⟨k.1.1, (hK k.1.2).2⟩ : L) ∈ T := by
    intro k
    have h := k.2
    rw [MonoidHom.mem_ker] at h
    have h' := congrArg Subtype.val h
    exact (QuotientGroup.eq_one_iff _).mp h'
  let θ : ↥g.ker →* ↥T :=
    { toFun := fun k => ⟨⟨k.1.1, (hK k.1.2).2⟩, hmem k⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hθ : Function.Injective θ := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : T => ((x : L) : G)) hab
  haveI : Group.IsSolvable ↥g.ker := Group.isSolvable_of_isSolvable_injective hθ
  exact Group.isSolvable_of_ker_le_range g.ker.subtype g (by rw [Subgroup.range_subtype])


end Z3Core

section Z3Datum

open CFSG.BenderSuzuki CFSG.Quasithin.H13.F431.L3 CFSG.Semidihedral.ParameterFive


end Z3Datum

section Z3Range

open CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion CFSG.ASVolI.ChF


end Z3Range

section Z3Final

open CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion CFSG.ASVolI.ChF
  CFSG.Quasithin.H13.F431.L3


end Z3Final

end F4dPartZ3

section F4dPartZ4

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.Quasithin.H13.F431.L3

section ConjDatum

variable {M : Type} [Group M] [Finite M] {M₁ M₂ : Subgroup M}


end ConjDatum

section ExistsConj

variable {M : Type} [Group M] [Finite M] {M₁ M₂ : Subgroup M}

theorem burnsideF4d_Z4_exists_conj (D : L3Datum M₁ M₂) (hG : D.Good) {B' : Subgroup M}
    (hB'H : B' ≤ M₁ ⊓ M₂) (hB'odd : Odd (Nat.card ↥B'))
    (hcard : ∃ k : ℕ, Nat.card ↥(M₁ ⊓ M₂) = 2 ^ k * Nat.card ↥B') :
    ∃ n ∈ D.S, B' = conjSub n D.B := by
  have hdisj : ∀ x ∈ D.S, x ∈ B' → x = 1 := fun x hx hxB =>
    eq_one_of_pgroup_of_odd D.S_pgroup hB'odd hx hxB
  have hcardH : Nat.card ↥(M₁ ⊓ M₂) = Nat.card ↥D.S * Nat.card ↥B' := by
    obtain ⟨k, hk⟩ := hcard
    obtain ⟨a, ha⟩ := D.S_pgroup.exists_card_eq
    have h1 : Nat.card ↥(M₁ ⊓ M₂) = Nat.card ↥D.S * Nat.card ↥D.B := D.card_H
    rw [ha] at h1 ⊢
    have h2 : 2 ^ a * Nat.card ↥D.B = 2 ^ k * Nat.card ↥B' := h1.symm.trans hk
    have hcB : Nat.Coprime (2 ^ k) (Nat.card ↥D.B) :=
      Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr D.B_odd)
    have hcB' : Nat.Coprime (2 ^ a) (Nat.card ↥B') :=
      Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hB'odd)
    have hka : k ≤ a :=
      (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp
        (hcB.dvd_of_dvd_mul_right (Dvd.intro _ h2.symm))
    have hak : a ≤ k :=
      (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp
        (hcB'.dvd_of_dvd_mul_right (Dvd.intro _ h2))
    have hkeq : k = a := le_antisymm hka hak
    subst hkeq
    rw [h1]
    exact h2
  have hodd : ¬ 2 ∣ D.S.relIndex (M₁ ⊓ M₂) := by
    intro h2
    apply D.S_index
    rw [← Subgroup.relIndex_mul_relIndex D.S (M₁ ⊓ M₂) M₁ D.S_le_H inf_le_left]
    exact h2.mul_right _
  obtain ⟨r, hr, hB'r⟩ := Lin2.exists_conj_of_complements D.S_le_H
    (L3Datum.normalizer_S_eq hG).ge D.S_pgroup hodd D.B_le hB'H
    ((Subgroup.eq_bot_iff_forall _).mpr fun x hx => D.B_inf_S hx.1 hx.2)
    ((Subgroup.eq_bot_iff_forall _).mpr fun x hx => hdisj x hx.1 hx.2)
    D.mul_SB (exists_mul_eq_of_card D.S_le_H hB'H hdisj hcardH)
  refine ⟨r⁻¹, D.S.inv_mem hr, ?_⟩
  ext y
  rw [hB'r, Lin2.mem_conjR, mem_conjSub, inv_inv]

end ExistsConj

section HallTransport

open CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

variable {E : Type} [Group E] {M₁ M₂ : Subgroup E} {Y : Type} [Group Y] {M : Type} [Group M]

theorem burnsideF4d_Z4_imB_eq (β : Cpl M₁ M₂ Y) (ε : Y →* M) {K : Subgroup E}
    (hK : K ≤ M₁ ⊓ M₂) : imB β ε K = subImg (burnsideF4d_bOne β ε) K := by
  unfold imB subImg bM bmap burnsideF4d_bOne
  rw [← burnsideF4d_map_inclusion_subgroupOf K hK]
  exact (Subgroup.map_map (K.subgroupOf (M₁ ⊓ M₂)) ((epsG β ε).comp (f1 (c := β)))
    (RankTwoAmalgam.ofSubgroups M₁ M₂).α1).symm

theorem burnsideF4d_Z4_imB_hall (β : Cpl M₁ M₂ Y) (hβ : β.IsFaithful) (ε : Y →* M)
    (hε : Function.Injective (epsG β ε)) {Bbar : Subgroup E}
    (hB : IsHallTwoPrime Bbar (M₁ ⊓ M₂)) :
    imB β ε Bbar ≤ MiOne β ε ⊓ MiTwo β ε ∧ Odd (Nat.card ↥(imB β ε Bbar)) ∧
      ∃ k : ℕ, Nat.card ↥(MiOne β ε ⊓ MiTwo β ε) = 2 ^ k * Nat.card ↥(imB β ε Bbar) := by
  obtain ⟨hle, hodd, k, hk⟩ := hB
  have hb : Function.Injective (burnsideF4d_bOne β ε) := hε.comp (f1_injective β hβ)
  have e1 : imB β ε Bbar = subImg (burnsideF4d_bOne β ε) Bbar := burnsideF4d_Z4_imB_eq β ε hle
  have e2 := burnsideF4d_inter_eq β hβ ε hε
  have hBM : Bbar ≤ M₁ := hle.trans inf_le_left
  refine ⟨?_, ?_, k, ?_⟩
  · rw [e1, e2]
    exact subImg_mono _ hle
  · rw [e1, card_subImg _ hb hBM]
    exact hodd
  · rw [e1, e2, card_subImg _ hb hBM, card_subImg _ hb (inf_le_left : M₁ ⊓ M₂ ≤ M₁)]
    have := Subgroup.relIndex_mul_card Bbar (M₁ ⊓ M₂)
    rw [inf_of_le_left hle, hk] at this
    exact this.symm

end HallTransport

section Parts

open CFSG.Quasithin.H13.F431.L3.L3Datum


end Parts

section Main

open CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion


end Main

end F4dPartZ4

section F4dPartZ5

section Z5

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.Quasithin.H13.F431.U42.Am CFSG.Quasithin.RankTwoAmalgam
  CFSG.Quasithin.RankTwoAmalgam.Completion CFSG.ASVolI.ChF


end Z5

end F4dPartZ5

section F4dPartZ6

section Z6

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion CFSG.ASVolI.ChF
  CFSG.Quasithin.H13.F431.L3


end Z6

end F4dPartZ6

section F4dPartZ7

section Z7

open CFSG.Open CFSG.ASVolI.ChF


end Z7

end F4dPartZ7

end CFSG.ASVolI

