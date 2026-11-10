module
public import CFSG.Milestones.ASVolI.I2GUniversal
public import CFSG.Quasithin.Vol2.KGNatReal
public import CFSG.Quasithin.Vol2.KGNatSp4Flag
public import CFSG.Quasithin.Vol2.KGNatSL2Nat
public import CFSG.Quasithin.Vol2.Ch11G2Q8Real
public import CFSG.Quasithin.Vol2.Ch11G2Q8N13
public import CFSG.Quasithin.MS93.M15Omega5
public import CFSG.Quasithin.Vol2.Ch3B513NSpC
public import CFSG.Quasithin.Vol2.Ch3B513NC1SL2
public import CFSG.Quasithin.MS93.M15G2
public import CFSG.Quasithin.Vol2.KGNatComm
public import CFSG.Quasithin.Background.JonesParshallSp4Perfect
public import CFSG.Quasithin.Background.A1aFStar
public import CFSG.Quasithin.Background.A1bBasic
public import CFSG.Quasithin.Vol2.Ch11G2Q8SiegelM
public import CFSG.Quasithin.Vol2.Ch11G2Q8InvLong
public import CFSG.Quasithin.Vol2.Ch11G2Q8Point
public import CFSG.Quasithin.H13.VolIAltCoverG2
public import CFSG.Quasithin.H13.VolIAltCoverG2Field
public import CFSG.Quasithin.H13.VolIAltCoverSix
public import CFSG.Quasithin.Background.B5FinSp
public import CFSG.Quasithin.Background.B5FinSpCore
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.ClassicalGroups
public import CFSG.LieType.SteinbergBRSemidirectSL2
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3NativeBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Native
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Containment
public import CFSG.Quasithin.Background.A3Structure312
public import CFSG.Quasithin.Background.A3Structure319
public import CFSG.Quasithin.Background.A3Structure36BCase3
public import CFSG.Quasithin.Background.A3Structure36BCases
public import CFSG.Quasithin.Background.A3Structure36BCommon
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.A3Structure36BStar
public import CFSG.Quasithin.Background.B1More13A
public import CFSG.Quasithin.Background.B1More13Defs
public import CFSG.Quasithin.Background.B1MoreEleven
public import CFSG.Quasithin.Background.B5CompA
public import CFSG.Quasithin.Background.B5CompB
public import CFSG.Quasithin.Background.B5FinOut
public import CFSG.Quasithin.Background.B6
public import CFSG.Quasithin.Background.B6Example
public import CFSG.Quasithin.Background.E2Hyp
public import CFSG.Quasithin.Background.E2SolvTwo
public import CFSG.Quasithin.Background.F9FiveStruct
public import CFSG.Quasithin.Background.F9G2
public import CFSG.Quasithin.Background.F9Geometry
public import CFSG.Quasithin.Background.FFC5Dich
public import CFSG.Quasithin.Background.FFC5Main
public import CFSG.Quasithin.Background.G64ExtSq
public import CFSG.Quasithin.Background.G64NatTop
public import CFSG.Quasithin.Background.HConj
public import CFSG.Quasithin.Background.InternalSecData
public import CFSG.Quasithin.Background.InternalSecIso
public import CFSG.Quasithin.Background.SmithB51SL3A
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112ListC
public import CFSG.Quasithin.EmptyFaithful.S142Statements
public import CFSG.Quasithin.H13.A5S1326
public import CFSG.Quasithin.H13.A5Top
public import CFSG.Quasithin.H13.L1332Inputs
public import CFSG.Quasithin.Vol2.Ch10StatementsE
public import CFSG.Quasithin.Vol2.Ch11SecA02NatFix
public import CFSG.Quasithin.Vol2.Ch11SecA02Setup
public import CFSG.Quasithin.Vol2.Ch11SecA03Basic
public import CFSG.Quasithin.Vol2.Ch11SecA04Glue
public import CFSG.Quasithin.Vol2.Ch11SecA11Exists
public import CFSG.Quasithin.Vol2.Ch11SecA11Ord
public import CFSG.Quasithin.Vol2.Ch11SecA14Conj
public import CFSG.Quasithin.Vol2.Ch11SecAFacts03
public import CFSG.Quasithin.Vol2.Ch11SecAFactsDelta
public import CFSG.Quasithin.Vol2.Ch11SecAViN13
public import CFSG.Quasithin.Vol2.Ch11SecCFacts4
public import CFSG.Quasithin.Vol2.Ch11SecSFacts2
public import CFSG.Quasithin.Vol2.Ch11SecSFacts3
public import CFSG.Quasithin.Vol2.Ch11SecSG2Sp4
public import CFSG.Quasithin.Vol2.Ch11SecSI3
public import CFSG.Quasithin.Vol2.Ch11SecSObl
public import CFSG.Quasithin.Vol2.Ch1Faithful
public import CFSG.Quasithin.Vol2.Ch3B513NC1Nat
public import CFSG.Quasithin.Vol2.KGNatSL2Borel
public import CFSG.Quasithin.Vol2.KGNatSL2H
public import CFSG.Quasithin.Vol2.KGNatSp4Sim
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Transvection.Statement

public section
namespace CFSG.ASVolI
open CFSG.Open


open CFSG.Quasithin CFSG.ASVolI.ChIJK in
theorem burnsideI23x_realizesVia {V : Type} [CommGroup V] {L : Subgroup (MulAut V)}
    {W0 : Subgroup V} {D : FFModel} {π : D.Gam →* ↥L}
    {β : V →* ↥D.sec ⧸ D.ker.subgroupOf D.sec} (h : I23SectionMap D L W0 π β)
    (hW0 : W0 ≤ fixV L) : D.RealizesVia L ⊤ W0 π := by
  obtain ⟨hπ, hβs, hβk, hkerle, hsecinv, hkerinv, hequiv⟩ := h
  refine ⟨hπ, le_top, hkerle, fun _ _ _ => Subgroup.mem_top _, ?_, hsecinv, hkerinv,
    β.comp (⊤ : Subgroup V).subtype, ?_, ?_, ?_⟩
  · intro g z hz
    rw [mem_fixV.1 (hW0 hz) g g.2]
    exact hz
  · intro y
    obtain ⟨v, hv⟩ := hβs y
    exact ⟨⟨v, Subgroup.mem_top v⟩, hv⟩
  · intro u
    show β (u : V) = 1 ↔ _
    rw [← MonoidHom.mem_ker, hβk]
  · intro γ u m hu hm hum
    exact hequiv γ (u : V) m hm hum

open CFSG.Quasithin CFSG.ASVolI.ChIJK CFSG.Quasithin.Vol2.KGNat in
theorem burnsideI23x_isCoord {m : ℕ} {F : Type} [Field F] {M : Type} [AddCommGroup M]
    [Module F M] (LM : LinModel (i23NaturalModel m F) F M)
    {V : Type} [CommGroup V] {L : Subgroup (MulAut V)} {W0 : Subgroup V}
    {π : (i23NaturalModel m F).Gam →* ↥L}
    {β : V →* ↥(i23NaturalModel m F).sec ⧸
      (i23NaturalModel m F).ker.subgroupOf (i23NaturalModel m F).sec}
    (h : I23SectionMap (i23NaturalModel m F) L W0 π β) :
    IsCoord LM L W0 π (fun v => Multiplicative.toAdd (LM.e (β v))) := by
  obtain ⟨hπ, hβs, hβk, hkerle, hsecinv, hkerinv, hequiv⟩ := h
  refine ⟨fun u u' => ?_, fun u => ?_, fun x => ?_, fun γ u => ?_, hπ⟩
  · simp only [map_mul]
    rfl
  · rw [← hβk, MonoidHom.mem_ker, ← LM.e.map_eq_one_iff]
    exact ⟨fun h0 => congrArg Multiplicative.ofAdd h0, fun h1 => congrArg Multiplicative.toAdd h1⟩
  · obtain ⟨q, hq⟩ := LM.e.surjective (Multiplicative.ofAdd x)
    obtain ⟨v, hv⟩ := hβs q
    exact ⟨v, by simp only [hv, hq]; rfl⟩
  · obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (β u)
    have hact := hsecinv γ y y.2
    have h1 := hequiv γ u y hact hy.symm
    show Multiplicative.toAdd (LM.e (β ((π γ : MulAut V) u))) = _
    rw [h1, LM.e_act γ y hact, ← hy]


open CFSG.Quasithin CFSG.ASVolI.ChIJK CFSG.Quasithin.Vol2.KGNat CFSG.Quasithin.Vol2.Ch11.SecA
  CFSG.Quasithin.Vol2.Ch11.G2Q8 in
open CFSG.Quasithin CFSG.ASVolI.ChIJK CFSG.Quasithin.Vol2.KGNat CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.Quasithin.JonesParshall in


open CFSG.Quasithin CFSG.ASVolI.ChIJK CFSG.Quasithin.Vol2.KGNat CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.Quasithin.JonesParshall in

open CFSG.Quasithin CFSG.ASVolI.ChIJK CFSG.Quasithin.Vol2.KGNat CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.Quasithin.JonesParshall in


open CFSG.Quasithin CFSG.ASVolI.ChIJK CFSG.Quasithin.Vol2.KGNat CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.Quasithin.JonesParshall CFSG.Assembly.LowTwoRank in
open CFSG.Quasithin CFSG.ASVolI.ChIJK CFSG.Quasithin.Vol2.KGNat CFSG.Assembly.LowTwoRank in
@[expose] noncomputable def burnsideI23x_LM1 (F : Type) [Field F] :
    LinModel (i23NaturalModel 1 F) F (Fin 2 → F) :=
  linModelNat (StatedSL 2 F)


open CFSG.Quasithin CFSG.Quasithin.Vol2.KGNat CFSG.Assembly.LowTwoRank CFSG.CGT.Timmesfeld75
  CFSG.Quasithin.Vol2.Ch11.SecA in

open CFSG.Quasithin CFSG.ASVolI.ChIJK CFSG.Quasithin.Vol2.KGNat in
theorem burnsideI23x_fixV_eq {m : ℕ} {F : Type} [Field F] {M : Type} [AddCommGroup M] [Module F M]
    (LM : LinModel (i23NaturalModel m F) F M)
    {V : Type} [CommGroup V] {L : Subgroup (MulAut V)} {W0 : Subgroup V}
    {π : (i23NaturalModel m F).Gam →* ↥L}
    {β : V →* ↥(i23NaturalModel m F).sec ⧸
      (i23NaturalModel m F).ker.subgroupOf (i23NaturalModel m F).sec}
    (h : I23SectionMap (i23NaturalModel m F) L W0 π β) (hW0 : W0 ≤ fixV L)
    (hnofix : ∀ x : M, (∀ γ : (i23NaturalModel m F).Gam, LM.lin γ x = x) → x = 0) :
    fixV L = W0 := by
  have hf := burnsideI23x_isCoord LM h
  refine le_antisymm (fun v hv => ?_) hW0
  have h0 : Multiplicative.toAdd (LM.e (β v)) = 0 := by
    apply hnofix
    intro γ
    rw [← hf.act γ v, mem_fixV.1 hv (π γ : MulAut V) (π γ).2]
  exact (hf.ker v).1 h0


open CFSG.Quasithin CFSG.Quasithin.Vol2.KGNat CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.Quasithin.JonesParshall in


structure burnsideI23x_SD (F : Type) [Field F] (N : Type) [AddCommGroup N] [Module F N] where
  B : N →ₗ[F] N →ₗ[F] F
  Q0 : N → F
  Q0_add : ∀ x y, Q0 (x + y) = Q0 x + Q0 y + B x y
  Q0_smul : ∀ (c : F) (x : N), Q0 (c • x) = c ^ 2 * Q0 x
  alt : ∀ x, B x x = 0
  nondeg : ∀ x, (∀ y, B x y = 0) → x = 0

namespace burnsideI23x_SD

variable {F : Type} [Field F] {N : Type} [AddCommGroup N] [Module F N]

@[expose] def Qw (S : burnsideI23x_SD F N) (w : N × F) : F := S.Q0 w.1 + w.2 ^ 2


end burnsideI23x_SD

@[expose] noncomputable def burnsideI23x_sqrt (F : Type) [Field F] [Finite F] [CharP F 2] : F ≃+* F :=
  (frobeniusEquiv F 2).symm

theorem burnsideI23x_sqrt_sq {F : Type} [Field F] [Finite F] [CharP F 2] (a : F) :
    (burnsideI23x_sqrt F a) ^ 2 = a := by
  have h := (frobeniusEquiv F 2).apply_symm_apply a
  rwa [frobeniusEquiv_apply] at h

theorem burnsideI23x_sqrt_of_sq {F : Type} [Field F] [Finite F] [CharP F 2] (a : F) :
    burnsideI23x_sqrt F (a ^ 2) = a := by
  have h := (frobeniusEquiv F 2).symm_apply_apply a
  rwa [frobeniusEquiv_apply] at h

theorem burnsideI23x_sq_injective {F : Type} [Field F] [CharP F 2] {a b : F} (h : a ^ 2 = b ^ 2) :
    a = b := by
  apply frobenius_inj F 2
  rw [frobenius_def, frobenius_def]
  exact h

namespace burnsideI23x_SD

variable {F : Type} [Field F] [Finite F] [CharP F 2] {N : Type} [AddCommGroup N] [Module F N]
  (S : burnsideI23x_SD F N)

@[expose] def Symp (M : N ≃ₗ[F] N) : Prop := ∀ x y, S.B (M x) (M y) = S.B x y

@[expose] noncomputable def lf (M : N ≃ₗ[F] N) (x : N) : F :=
  burnsideI23x_sqrt F (S.Q0 x + S.Q0 (M x))

theorem lf_sq (M : N ≃ₗ[F] N) (x : N) : (S.lf M x) ^ 2 = S.Q0 x + S.Q0 (M x) :=
  burnsideI23x_sqrt_sq _

theorem two_eq_zero_F : (2 : F) = 0 := CharP.cast_eq_zero F 2

theorem add_self_F (a : F) : a + a = 0 := by
  rw [← two_mul, two_eq_zero_F, zero_mul]

theorem lf_add {M : N ≃ₗ[F] N} (hM : S.Symp M) (x y : N) :
    S.lf M (x + y) = S.lf M x + S.lf M y := by
  unfold lf
  rw [← map_add]
  congr 1
  rw [S.Q0_add, map_add, S.Q0_add, hM x y]
  have h := add_self_F (S.B x y)
  linear_combination h

theorem lf_smul (M : N ≃ₗ[F] N) (c : F) (x : N) : S.lf M (c • x) = c * S.lf M x := by
  unfold lf
  rw [map_smul, S.Q0_smul, S.Q0_smul, ← mul_add]
  conv_lhs => rw [show c ^ 2 * (S.Q0 x + S.Q0 (M x)) = c ^ 2 * (S.Q0 x + S.Q0 (M x)) from rfl]
  rw [map_mul, burnsideI23x_sqrt_of_sq]


theorem lf_symm {M : N ≃ₗ[F] N} (x : N) : S.lf M.symm (M x) = S.lf M x := by
  unfold lf
  rw [LinearEquiv.symm_apply_apply, add_comm]

theorem lf_apply_symm {M : N ≃ₗ[F] N} (x : N) : S.lf M (M.symm x) = S.lf M.symm x := by
  unfold lf
  rw [LinearEquiv.apply_symm_apply, add_comm]

@[expose] noncomputable def lift {M : N ≃ₗ[F] N} (hM : S.Symp M) : (N × F) ≃ₗ[F] (N × F) where
  toFun w := (M w.1, w.2 + S.lf M w.1)
  map_add' w w' := by
    refine Prod.ext (map_add M _ _) ?_
    show w.2 + w'.2 + S.lf M (w.1 + w'.1) = w.2 + S.lf M w.1 + (w'.2 + S.lf M w'.1)
    rw [S.lf_add hM]
    ring
  map_smul' c w := by
    refine Prod.ext (map_smul M _ _) ?_
    show c * w.2 + S.lf M (c • w.1) = c * (w.2 + S.lf M w.1)
    rw [S.lf_smul]
    ring
  invFun w := (M.symm w.1, w.2 + S.lf M.symm w.1)
  left_inv w := by
    refine Prod.ext (M.symm_apply_apply _) ?_
    show w.2 + S.lf M w.1 + S.lf M.symm (M w.1) = w.2
    rw [S.lf_symm]
    have := add_self_F (S.lf M w.1)
    linear_combination this
  right_inv w := by
    refine Prod.ext (M.apply_symm_apply _) ?_
    show w.2 + S.lf M.symm w.1 + S.lf M (M.symm w.1) = w.2
    rw [S.lf_apply_symm]
    have := add_self_F (S.lf M.symm w.1)
    linear_combination this

theorem lift_apply {M : N ≃ₗ[F] N} (hM : S.Symp M) (w : N × F) :
    S.lift hM w = (M w.1, w.2 + S.lf M w.1) := rfl

theorem Qw_lift {M : N ≃ₗ[F] N} (hM : S.Symp M) (w : N × F) : S.Qw (S.lift hM w) = S.Qw w := by
  show S.Q0 (M w.1) + (w.2 + S.lf M w.1) ^ 2 = S.Q0 w.1 + w.2 ^ 2
  have h := S.lf_sq M w.1
  have h3 : (2 : F) = 0 := two_eq_zero_F
  linear_combination h + (S.Q0 (M w.1) + w.2 * S.lf M w.1) * h3

end burnsideI23x_SD

namespace burnsideI23x_SD

variable {F : Type} [Field F] [Finite F] [CharP F 2] {N : Type} [AddCommGroup N] [Module F N]
  (S : burnsideI23x_SD F N)

theorem lift_unique {M : N ≃ₗ[F] N} (hM : S.Symp M) (g : N × F → N × F)
    (hg1 : ∀ w, (g w).1 = M w.1) (hgQ : ∀ w, S.Qw (g w) = S.Qw w) (w : N × F) :
    g w = S.lift hM w := by
  refine Prod.ext (hg1 w) ?_
  show (g w).2 = w.2 + S.lf M w.1
  apply burnsideI23x_sq_injective
  have h1 := hgQ w
  have h2 := S.lf_sq M w.1
  have h3 := two_eq_zero_F (F := F)
  have h4 : S.Q0 (g w).1 + (g w).2 ^ 2 = S.Q0 w.1 + w.2 ^ 2 := h1
  rw [hg1 w] at h4
  linear_combination h4 - h2 - (S.Q0 (M w.1) + w.2 * S.lf M w.1) * h3


end burnsideI23x_SD

namespace burnsideI23x_SD

variable {F : Type} [Field F] [Finite F] [CharP F 2] {N : Type} [AddCommGroup N] [Module F N]
  (S : burnsideI23x_SD F N)

@[expose] noncomputable def liftMul {M : N ≃ₗ[F] N} (hM : S.Symp M) :
    MulAut (Multiplicative (N × F)) :=
  (S.lift hM).toAddEquiv.toMultiplicative

theorem toAdd_liftMul {M : N ≃ₗ[F] N} (hM : S.Symp M) (w : Multiplicative (N × F)) :
    Multiplicative.toAdd (S.liftMul hM w) = S.lift hM (Multiplicative.toAdd w) := rfl


@[expose] noncomputable def liftHom {Γ : Type} [Group Γ] (A : Γ →* (N ≃ₗ[F] N))
    (hA : ∀ γ, S.Symp (A γ)) : Γ →* MulAut (Multiplicative (N × F)) where
  toFun γ := S.liftMul (hA γ)
  map_one' := by
    refine MulEquiv.ext fun w => Multiplicative.toAdd.injective ?_
    rw [toAdd_liftMul]
    exact (S.lift_unique (hA 1) (fun w => w) (fun w => by simp) (fun _ => rfl)
      (Multiplicative.toAdd w)).symm
  map_mul' γ δ := by
    refine MulEquiv.ext fun w => Multiplicative.toAdd.injective ?_
    show Multiplicative.toAdd (S.liftMul (hA (γ * δ)) w) =
      Multiplicative.toAdd (S.liftMul (hA γ) (S.liftMul (hA δ) w))
    rw [toAdd_liftMul, toAdd_liftMul, toAdd_liftMul]
    refine (S.lift_unique (hA (γ * δ)) (fun w => S.lift (hA γ) (S.lift (hA δ) w))
      (fun w => by rw [map_mul]; rfl) (fun w => ?_) (Multiplicative.toAdd w)).symm
    rw [S.Qw_lift, S.Qw_lift]

theorem liftHom_apply {Γ : Type} [Group Γ] (A : Γ →* (N ≃ₗ[F] N)) (hA : ∀ γ, S.Symp (A γ))
    (γ : Γ) (w : N × F) :
    S.liftHom A hA γ (Multiplicative.ofAdd w) = Multiplicative.ofAdd (S.lift (hA γ) w) := rfl

end burnsideI23x_SD
namespace burnsideI23x_SD

variable {F : Type} [Field F] [Finite F] [CharP F 2] {N : Type} [AddCommGroup N] [Module F N]
  (S : burnsideI23x_SD F N)

theorem lf_zero (M : N ≃ₗ[F] N) : S.lf M 0 = 0 := by
  have h := S.lf_sq M 0
  have h0 : S.Q0 0 = 0 := by
    have := S.Q0_smul (0 : F) 0
    simpa using this
  rw [map_zero, h0, add_zero] at h
  exact pow_eq_zero_iff (two_ne_zero) |>.1 h

@[expose] def radSub (S : burnsideI23x_SD F N) : Subgroup (Multiplicative (N × F)) where
  carrier := {w | (Multiplicative.toAdd w).1 = 0}
  one_mem' := rfl
  mul_mem' := fun {a b} ha hb => by
    show (Multiplicative.toAdd a + Multiplicative.toAdd b).1 = 0
    rw [Prod.fst_add]
    show (Multiplicative.toAdd a).1 + (Multiplicative.toAdd b).1 = 0
    rw [ha, hb, add_zero]
  inv_mem' := fun {a} ha => by
    show (-(Multiplicative.toAdd a)).1 = 0
    rw [Prod.fst_neg]
    show -(Multiplicative.toAdd a).1 = 0
    rw [ha, neg_zero]

theorem mem_radSub {w : Multiplicative (N × F)} : w ∈ S.radSub ↔ (Multiplicative.toAdd w).1 = 0 :=
  Iff.rfl

@[expose] def projHom : Multiplicative (N × F) →* Multiplicative N where
  toFun w := Multiplicative.ofAdd (Multiplicative.toAdd w).1
  map_one' := rfl
  map_mul' _ _ := rfl

theorem projHom_surjective : Function.Surjective (projHom (F := F) (N := N)) := fun x =>
  ⟨Multiplicative.ofAdd (Multiplicative.toAdd x, 0), rfl⟩

theorem projHom_ker : (projHom (F := F) (N := N)).ker = S.radSub := by
  ext w
  rw [MonoidHom.mem_ker, mem_radSub]
  exact ⟨fun h => congrArg Multiplicative.toAdd h, fun h => congrArg Multiplicative.ofAdd h⟩

theorem sq_eq_one_W (w : Multiplicative (N × F)) : w ^ 2 = 1 := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one, ← Nat.cast_smul_eq_nsmul F, Nat.cast_ofNat, two_eq_zero_F, zero_smul]

end burnsideI23x_SD

open CFSG.Quasithin CFSG.ASVolI.ChIJK in
theorem burnsideI23x_univ_iso {F : Type} [Field F] [Finite F] [CharP F 2] {N : Type}
    [AddCommGroup N] [Module F N] [Finite N] (S : burnsideI23x_SD F N)
    {Γ : Type} [Group Γ] (A : Γ →* (N ≃ₗ[F] N)) (hA : ∀ γ, S.Symp (A γ))
    {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {L : Subgroup (MulAut V)} {W0 : Subgroup V} (huniv : IsUniversalCovering L W0)
    (π : Γ →* ↥L) (hπ : Function.Bijective π) (f : V →* Multiplicative N)
    (hfs : Function.Surjective f) (hfk : f.ker = W0)
    (hfπ : ∀ (γ : Γ) (v : V), f ((π γ : MulAut V) v) =
      Multiplicative.ofAdd (A γ (Multiplicative.toAdd (f v))))
    (hbound : Nat.card W0 ≤ Nat.card F)
    (hgen : ∀ w : Multiplicative (N × F), w ∈ Subgroup.closure
      {x | ∃ (γ : Γ) (y : Multiplicative (N × F)), x = S.liftHom A hA γ y * y⁻¹}) :
    ∃ ψ : V ≃* Multiplicative (N × F),
      (∀ (γ : Γ) (v : V), ψ ((π γ : MulAut V) v) = S.liftHom A hA γ (ψ v)) ∧
      ∀ v : V, (Multiplicative.toAdd (ψ v)).1 = Multiplicative.toAdd (f v) := by
  classical
  let eΓ : Γ ≃* ↥L := MulEquiv.ofBijective π hπ
  let ρ' : ↥L →* MulAut (Multiplicative (N × F)) := (S.liftHom A hA).comp eΓ.symm.toMonoidHom
  have hρ' : ∀ γ w, ρ' (π γ) w = S.liftHom A hA γ w := by
    intro γ w
    show S.liftHom A hA (eΓ.symm (π γ)) w = _
    have : eΓ.symm (π γ) = γ := eΓ.symm_apply_apply γ
    rw [this]
  let fe : V ⧸ W0 ≃* Multiplicative N :=
    (QuotientGroup.quotientMulEquivOfEq hfk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hfs)
  have hfe : ∀ v : V, fe (QuotientGroup.mk v) = f v := fun v => rfl
  let ψ' : Multiplicative (N × F) →* V ⧸ W0 := fe.symm.toMonoidHom.comp (burnsideI23x_SD.projHom)
  have hψ'v : ∀ (w : Multiplicative (N × F)) (v : V), ψ' w = QuotientGroup.mk v ↔
      Multiplicative.ofAdd (Multiplicative.toAdd w).1 = f v := by
    intro w v
    constructor
    · intro h
      have h1 := congrArg fe h
      have h2 : fe (ψ' w) = Multiplicative.ofAdd (Multiplicative.toAdd w).1 :=
        fe.apply_symm_apply _
      rw [h2, hfe] at h1
      exact h1
    · intro h
      show fe.symm (Multiplicative.ofAdd (Multiplicative.toAdd w).1) = QuotientGroup.mk v
      rw [h, ← hfe v, MulEquiv.symm_apply_apply]
  have hfix' : ∀ w ∈ S.radSub, ∀ g : ↥L, ρ' g w = w := by
    intro w hw g
    obtain ⟨γ, rfl⟩ := hπ.2 g
    rw [hρ']
    apply Multiplicative.toAdd.injective
    show S.lift (hA γ) (Multiplicative.toAdd w) = Multiplicative.toAdd w
    have hw1 : (Multiplicative.toAdd w).1 = 0 := hw
    refine Prod.ext ?_ ?_
    · show A γ (Multiplicative.toAdd w).1 = (Multiplicative.toAdd w).1
      rw [hw1, map_zero]
    · show (Multiplicative.toAdd w).2 + S.lf (A γ) (Multiplicative.toAdd w).1 =
        (Multiplicative.toAdd w).2
      rw [hw1, S.lf_zero, add_zero]
  have hgen' : Subgroup.closure
      {w : Multiplicative (N × F) | ∃ (g : ↥L) (v : Multiplicative (N × F)),
        w = ρ' g v * v⁻¹} = ⊤ := by
    rw [eq_top_iff]
    intro w _
    refine Subgroup.closure_mono ?_ (hgen w)
    rintro _ ⟨γ, y, rfl⟩
    exact ⟨π γ, y, by rw [hρ']⟩
  have hψs : Function.Surjective ψ' := fun q => by
    obtain ⟨w, hw⟩ := burnsideI23x_SD.projHom_surjective (F := F) (N := N) (fe q)
    refine ⟨w, ?_⟩
    show fe.symm (burnsideI23x_SD.projHom w) = q
    rw [hw, MulEquiv.symm_apply_apply]
  have hker : ψ'.ker = S.radSub := by
    ext w
    rw [MonoidHom.mem_ker]
    show fe.symm (burnsideI23x_SD.projHom w) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, ← MonoidHom.mem_ker, S.projHom_ker]
  have hequiv : ∀ (g : ↥L) (v' : Multiplicative (N × F)) (v : V), ψ' v' = QuotientGroup.mk v →
      ψ' (ρ' g v') = QuotientGroup.mk ((g : MulAut V) v) := by
    intro g v' v hv
    obtain ⟨γ, rfl⟩ := hπ.2 g
    rw [hρ', hψ'v]
    rw [hψ'v] at hv
    have h1 : (Multiplicative.toAdd (S.liftHom A hA γ v')).1 = A γ (Multiplicative.toAdd v').1 := rfl
    rw [h1, hfπ]
    have h2 : (Multiplicative.toAdd v').1 = Multiplicative.toAdd (f v) := by
      rw [← hv]
      rfl
    rw [h2]
  obtain ⟨θ, hθs, hθe, hθψ⟩ := huniv.2.2 (Multiplicative (N × F)) ρ' S.radSub ψ'
    (fun w => burnsideI23x_SD.sq_eq_one_W (F := F) (N := N) w) hfix' hgen' hψs hker hequiv
  have hcardV : Nat.card V = Nat.card W0 * Nat.card N := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup W0, mul_comm]
    congr 1
    exact Nat.card_congr fe.toEquiv
  have hcardW : Nat.card (Multiplicative (N × F)) = Nat.card N * Nat.card F := by
    rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (N × F) ≃ N × F), Nat.card_prod]
  have hle1 : Nat.card (Multiplicative (N × F)) ≤ Nat.card V := Nat.card_le_card_of_surjective _ hθs
  have hle2 : Nat.card V ≤ Nat.card (Multiplicative (N × F)) := by
    rw [hcardV, hcardW, mul_comm (Nat.card N)]
    exact Nat.mul_le_mul_right _ hbound
  have hbij : Function.Bijective θ := hθs.bijective_of_nat_card_le hle2
  refine ⟨MulEquiv.ofBijective θ hbij, fun γ v => ?_, fun v => ?_⟩
  · show θ ((π γ : MulAut V) v) = S.liftHom A hA γ (θ v)
    rw [hθe, hρ']
  · have h1 := hθψ v
    rw [hψ'v] at h1
    have h2 := congrArg Multiplicative.toAdd h1
    exact h2
section HypSD

variable {F : Type} [Field F] [CharP F 2] (ι : Type) [Fintype ι] [DecidableEq ι]


end HypSD
namespace burnsideI23x_SD

section Gen

variable {F : Type} [Field F] [Finite F] [CharP F 2] {N : Type} [AddCommGroup N] [Module F N]
  (S : burnsideI23x_SD F N) {Γ : Type} [Group Γ] (A : Γ →* (N ≃ₗ[F] N))
  (hA : ∀ γ, S.Symp (A γ))

include hA in
@[expose] def GenW : Prop :=
  ∀ w : N × F, w ∈ AddSubgroup.closure {y | ∃ (γ : Γ) (x : N × F), y = S.lift (hA γ) x - x}

theorem vanish_of_gen (hgen : S.GenW A hA) {M : Type} [AddCommGroup M] (h : (N × F) →+ M)
    (hv : ∀ (γ : Γ) (x : N × F), h (S.lift (hA γ) x - x) = 0) (w : N × F) : h w = 0 := by
  have hle : AddSubgroup.closure {y | ∃ (γ : Γ) (x : N × F), y = S.lift (hA γ) x - x} ≤ h.ker :=
    (AddSubgroup.closure_le _).2 (by rintro y ⟨γ, x, rfl⟩; exact hv γ x)
  exact hle (hgen w)

include hA in
theorem B_symp_apply (γ : Γ) (x y : N) : S.B x (A γ y) = S.B (A γ⁻¹ x) y := by
  have h := hA γ (A γ⁻¹ x) y
  have e : A γ (A γ⁻¹ x) = x := by
    have := congrArg (fun f : N ≃ₗ[F] N => f x)
      (show A γ * A γ⁻¹ = 1 by rw [← map_mul, mul_inv_cancel, map_one])
    simpa using this
  rw [e] at h
  exact h

theorem fix_iff (hgen : S.GenW A hA) (w : N × F) :
    (∀ γ, S.lift (hA γ) w = w) ↔ w.1 = 0 := by
  constructor
  · intro hw
    have hx : ∀ γ, A γ w.1 = w.1 := fun γ => congrArg Prod.fst (hw γ)
    apply S.nondeg
    intro y
    let h : (N × F) →+ F :=
      { toFun := fun v => S.B w.1 v.1
        map_zero' := by simp
        map_add' := fun a b => by simp }
    have hv : ∀ (γ : Γ) (x : N × F), h (S.lift (hA γ) x - x) = 0 := by
      intro γ x
      show S.B w.1 (S.lift (hA γ) x - x).1 = 0
      have : (S.lift (hA γ) x - x).1 = A γ x.1 - x.1 := rfl
      rw [this, map_sub, S.B_symp_apply A hA, hx γ⁻¹, sub_self]
    exact S.vanish_of_gen A hA hgen h hv (y, 0)
  · intro h γ
    refine Prod.ext ?_ ?_
    · show A γ w.1 = w.1
      rw [h, map_zero]
    · show w.2 + S.lf (A γ) w.1 = w.2
      rw [h, S.lf_zero, add_zero]

end Gen

end burnsideI23x_SD
namespace burnsideI23x_SD

section Comm

variable {F : Type} [Field F] [Finite F] [CharP F 2] {N : Type} [AddCommGroup N] [Module F N]
  (S : burnsideI23x_SD F N) {Γ : Type} [Group Γ] (A : Γ →* (N ≃ₗ[F] N))
  (hA : ∀ γ, S.Symp (A γ))

theorem lift_fst (γ : Γ) (w : N × F) : (S.lift (hA γ) w).1 = A γ w.1 := rfl

include hA in
theorem comm_scalar (hEnd : ∀ φ : N →+ N, (∀ γ x, φ (A γ x) = A γ (φ x)) → ∃ c : F, ∀ x, φ x = c • x)
    (hgen : S.GenW A hA) (D : (N × F) →+ (N × F))
    (hDc : ∀ γ w, D (S.lift (hA γ) w) = S.lift (hA γ) (D w))
    (hDK : ∀ w : N × F, w.1 = 0 → (D w).1 = 0) : ∃ d : F, ∀ w, D w = d • w := by
  let δ : N →+ N := (AddMonoidHom.fst N F).comp (D.comp (AddMonoidHom.inl N F))
  have hδ : ∀ γ x, δ (A γ x) = A γ (δ x) := by
    intro γ x
    have h1 := congrArg Prod.fst (hDc γ (x, 0))
    have h3 : S.lift (hA γ) (x, 0) = (A γ x, 0) + (0, S.lf (A γ) x) := by
      refine Prod.ext ?_ ?_ <;> simp [S.lift_apply]
    rw [h3, map_add, Prod.fst_add, hDK (0, S.lf (A γ) x) rfl, add_zero, S.lift_fst A hA] at h1
    exact h1
  obtain ⟨d, hd⟩ := hEnd δ hδ
  refine ⟨d, ?_⟩
  let D2 : (N × F) →+ (N × F) :=
    { toFun := fun w => D w - d • w
      map_zero' := by simp
      map_add' := fun a b => by simp [smul_add]; abel }
  have hD2fst : ∀ w, (D2 w).1 = 0 := by
    intro w
    show (D w - d • w).1 = 0
    have hw : w = (w.1, 0) + (0, w.2) := by ext <;> simp
    have h1 : (D w).1 = δ w.1 := by
      conv_lhs => rw [hw, map_add, Prod.fst_add, hDK (0, w.2) rfl, add_zero]
      rfl
    rw [Prod.fst_sub, h1, hd, Prod.smul_fst, sub_self]
  have hD2c : ∀ γ w, D2 (S.lift (hA γ) w) = S.lift (hA γ) (D2 w) := by
    intro γ w
    show D (S.lift (hA γ) w) - d • S.lift (hA γ) w = S.lift (hA γ) (D w - d • w)
    rw [hDc, map_sub, map_smul]
  let h : (N × F) →+ F := (AddMonoidHom.snd N F).comp D2
  have hv : ∀ (γ : Γ) (x : N × F), h (S.lift (hA γ) x - x) = 0 := by
    intro γ x
    show (D2 (S.lift (hA γ) x - x)).2 = 0
    rw [map_sub, hD2c]
    have h0 : (D2 x).1 = 0 := hD2fst x
    have : S.lift (hA γ) (D2 x) = D2 x := by
      refine Prod.ext ?_ ?_
      · rw [S.lift_fst A hA, h0, map_zero]
      · show (D2 x).2 + S.lf (A γ) (D2 x).1 = (D2 x).2
        rw [h0, S.lf_zero, add_zero]
    rw [this, sub_self]
    rfl
  intro w
  have h2 : (D2 w).2 = 0 := S.vanish_of_gen A hA hgen h hv w
  have h3 : D2 w = 0 := Prod.ext (hD2fst w) h2
  exact sub_eq_zero.1 h3

end Comm

end burnsideI23x_SD
namespace burnsideI23x_SD

section Normalizer

variable {F : Type} [Field F] [Finite F] [CharP F 2] {N : Type} [AddCommGroup N] [Module F N]
  (S : burnsideI23x_SD F N) {Γ : Type} [Group Γ] (A : Γ →* (N ≃ₗ[F] N))
  (hA : ∀ γ, S.Symp (A γ))

structure NormW (g : (N × F) ≃+ (N × F)) : Prop where
  fwd : ∀ γ, ∃ γ', ∀ w, g (S.lift (hA γ) w) = S.lift (hA γ') (g w)
  bwd : ∀ γ, ∃ γ', ∀ w, g (S.lift (hA γ') w) = S.lift (hA γ) (g w)


variable {S A hA}

theorem NormW.map_rad {g : (N × F) ≃+ (N × F)} (hn : NormW S A hA g) (hgen : S.GenW A hA)
    {w : N × F} (hw : w.1 = 0) : (g w).1 = 0 := by
  rw [← S.fix_iff A hA hgen]
  intro γ
  obtain ⟨γ', h⟩ := hn.bwd γ
  rw [← h w, (S.fix_iff A hA hgen w).2 hw γ']

theorem NormW.symm_rad {g : (N × F) ≃+ (N × F)} (hn : NormW S A hA g) (hgen : S.GenW A hA)
    {w : N × F} (hw : w.1 = 0) : (g.symm w).1 = 0 := by
  rw [← S.fix_iff A hA hgen]
  intro γ
  obtain ⟨γ', h⟩ := hn.fwd γ
  apply g.injective
  rw [h, g.apply_symm_apply, (S.fix_iff A hA hgen w).2 hw γ']

variable (S A hA)


variable {S A hA}


end Normalizer

end burnsideI23x_SD
namespace burnsideI23x_SD

section Sigma

variable {F : Type} [Field F] [Finite F] [CharP F 2] {N : Type} [AddCommGroup N] [Module F N]
  {S : burnsideI23x_SD F N} {Γ : Type} [Group Γ] {A : Γ →* (N ≃ₗ[F] N)}
  {hA : ∀ γ, S.Symp (A γ)}

theorem scalar_faithful {c d : F} (h : ∀ w : N × F, c • w = d • w) : c = d := by
  have := congrArg Prod.snd (h (0, 1))
  simpa using this

theorem NormW.scalar_conj {g : (N × F) ≃+ (N × F)} (hn : NormW S A hA g)
    (hEnd : ∀ φ : N →+ N, (∀ γ x, φ (A γ x) = A γ (φ x)) → ∃ c : F, ∀ x, φ x = c • x)
    (hgen : S.GenW A hA) (a : F) : ∃ d : F, ∀ w, g (a • g.symm w) = d • w := by
  let D : (N × F) →+ (N × F) :=
    { toFun := fun w => g (a • g.symm w)
      map_zero' := by simp
      map_add' := fun x y => by simp [smul_add] }
  refine S.comm_scalar A hA hEnd hgen D (fun γ w => ?_) (fun w hw => ?_)
  · obtain ⟨γ', h⟩ := hn.bwd γ
    show g (a • g.symm (S.lift (hA γ) w)) = S.lift (hA γ) (g (a • g.symm w))
    have h1 : g.symm (S.lift (hA γ) w) = S.lift (hA γ') (g.symm w) := by
      apply g.injective
      rw [h, g.apply_symm_apply, g.apply_symm_apply]
    rw [h1, ← map_smul, h]
  · show (g (a • g.symm w)).1 = 0
    apply hn.map_rad hgen
    rw [Prod.smul_fst, hn.symm_rad hgen hw, smul_zero]

theorem NormW.exists_sigma {g : (N × F) ≃+ (N × F)} (hn : NormW S A hA g)
    (hEnd : ∀ φ : N →+ N, (∀ γ x, φ (A γ x) = A γ (φ x)) → ∃ c : F, ∀ x, φ x = c • x)
    (hgen : S.GenW A hA) : ∃ σ : F ≃+* F, ∀ (a : F) (w : N × F), g (a • w) = σ a • g w := by
  choose σ0 hσ0 using fun a => hn.scalar_conj hEnd hgen a
  have hs : ∀ (a : F) (w : N × F), g (a • w) = σ0 a • g w := by
    intro a w
    have := hσ0 a (g w)
    rwa [g.symm_apply_apply] at this
  have hadd : ∀ a b : F, σ0 (a + b) = σ0 a + σ0 b := by
    intro a b
    apply scalar_faithful (N := N)
    intro w
    have h1 := hs (a + b) (g.symm w)
    rw [add_smul, map_add, hs, hs, g.apply_symm_apply] at h1
    rw [add_smul]
    exact h1.symm
  have hmul : ∀ a b : F, σ0 (a * b) = σ0 a * σ0 b := by
    intro a b
    apply scalar_faithful (N := N)
    intro w
    have h1 := hs (a * b) (g.symm w)
    rw [mul_smul, hs, hs, g.apply_symm_apply] at h1
    rw [mul_smul]
    exact h1.symm
  have hone : σ0 1 = 1 := by
    apply scalar_faithful (N := N)
    intro w
    have h1 := hs 1 (g.symm w)
    rw [one_smul, g.apply_symm_apply] at h1
    rw [one_smul]
    exact h1.symm
  let σr : F →+* F :=
    { toFun := σ0
      map_one' := hone
      map_mul' := hmul
      map_zero' := by
        have := hadd 0 0
        simpa using this
      map_add' := hadd }
  have hinj : Function.Injective σr := fun a b hab => by
    have h1 : σ0 a = σ0 b := hab
    have h2 : ∀ w : N × F, a • w = b • w := fun w => by
      apply g.injective
      rw [hs, hs, h1]
    exact scalar_faithful (N := N) h2
  exact ⟨RingEquiv.ofBijective σr ⟨hinj, Finite.injective_iff_surjective.1 hinj⟩,
    fun a w => hs a w⟩

end Sigma

end burnsideI23x_SD
namespace burnsideI23x_SD

section Form

variable {F : Type} [Field F] [Finite F] [CharP F 2] {N : Type} [AddCommGroup N] [Module F N]
  {S : burnsideI23x_SD F N} {Γ : Type} [Group Γ] {A : Γ →* (N ≃ₗ[F] N)}
  {hA : ∀ γ, S.Symp (A γ)}


end Form

end burnsideI23x_SD
namespace burnsideI23x_SD

section Form2

variable {F : Type} [Field F] [Finite F] [CharP F 2] {N : Type} [AddCommGroup N] [Module F N]
  {S : burnsideI23x_SD F N} {Γ : Type} [Group Γ] {A : Γ →* (N ≃ₗ[F] N)}
  {hA : ∀ γ, S.Symp (A γ)}


end Form2

end burnsideI23x_SD
namespace burnsideI23x_SD

section Normalizer3

variable {F : Type} [Field F] [Finite F] [CharP F 2] {N : Type} [AddCommGroup N] [Module F N]
  {S : burnsideI23x_SD F N} {Γ : Type} [Group Γ] {A : Γ →* (N ≃ₗ[F] N)}
  {hA : ∀ γ, S.Symp (A γ)}


end Normalizer3

end burnsideI23x_SD
namespace burnsideI23x_SD

section GW

variable {F : Type} [Field F] [Finite F] [CharP F 2] {N : Type} [AddCommGroup N] [Module F N]
  {S : burnsideI23x_SD F N} {Γ : Type} [Group Γ] {A : Γ →* (N ≃ₗ[F] N)}
  {hA : ∀ γ, S.Symp (A γ)} {U : Type} [CommGroup U]


end GW

end burnsideI23x_SD


namespace burnsideI23x_SD

section CC

variable {F : Type} [Field F] [Finite F] [CharP F 2] {N : Type} [AddCommGroup N] [Module F N]
  [Finite N] [Nontrivial N] {S : burnsideI23x_SD F N} {Γ : Type} [Group Γ]
  {A : Γ →* (N ≃ₗ[F] N)} {hA : ∀ γ, S.Symp (A γ)} {U : Type} [CommGroup U]


end CC

end burnsideI23x_SD
namespace burnsideI23x_SD

section CC2

variable {F : Type} [Field F] [Finite F] [CharP F 2] {N : Type} [AddCommGroup N] [Module F N]
  [Finite N] [Nontrivial N] {S : burnsideI23x_SD F N} {Γ : Type} [Group Γ]
  {A : Γ →* (N ≃ₗ[F] N)} {hA : ∀ γ, S.Symp (A γ)} {U : Type} [CommGroup U]


end CC2

end burnsideI23x_SD

namespace burnsideI23x_SD

section CC3

variable {F : Type} [Field F] [Finite F] [CharP F 2] {N : Type} [AddCommGroup N] [Module F N]
  [Finite N] [Nontrivial N] {S : burnsideI23x_SD F N} {Γ : Type} [Group Γ]
  {A : Γ →* (N ≃ₗ[F] N)} {hA : ∀ γ, S.Symp (A γ)} {U : Type} [CommGroup U]


end CC3

end burnsideI23x_SD
namespace burnsideI23x_SD

section Tv

variable {F : Type} [Field F] [Finite F] [CharP F 2] {N : Type} [AddCommGroup N] [Module F N]
  (S : burnsideI23x_SD F N)

theorem B_comm (x y : N) : S.B x y = S.B y x := by
  have h := S.alt (x + y)
  simp only [map_add, LinearMap.add_apply, S.alt, zero_add, add_zero] at h
  have h2 := add_self_F (S.B y x)
  linear_combination h - h2


theorem Q0_add_smul (x e : N) (a : F) :
    S.Q0 (x + a • e) = S.Q0 x + a ^ 2 * S.Q0 e + a * S.B x e := by
  rw [S.Q0_add, S.Q0_smul]
  simp [map_smul]

@[expose] def tvLin (e : N) (c : F) : N →ₗ[F] N where
  toFun x := x + (c * S.B x e) • e
  map_add' x y := by
    simp only [map_add, LinearMap.add_apply, mul_add, add_smul]
    abel
  map_smul' a x := by
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply, smul_add, smul_smul]
    rw [mul_left_comm]

theorem tvLin_apply (e : N) (c : F) (x : N) : S.tvLin e c x = x + (c * S.B x e) • e := rfl

theorem tvLin_invol (e : N) (c : F) (x : N) : S.tvLin e c (S.tvLin e c x) = x := by
  rw [tvLin_apply, tvLin_apply]
  simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, S.alt,
    mul_zero, add_zero, zero_smul]
  have h := add_self_F (c * S.B x e)
  have : x + (c * S.B x e) • e + (c * S.B x e) • e = x := by
    rw [add_assoc, ← add_smul, h, zero_smul, add_zero]
  exact this

@[expose] def tvEquiv (e : N) (c : F) : N ≃ₗ[F] N :=
  LinearEquiv.ofInvolutive (S.tvLin e c) (fun x => S.tvLin_invol e c x)

theorem tvEquiv_apply (e : N) (c : F) (x : N) : S.tvEquiv e c x = x + (c * S.B x e) • e := rfl


end Tv

end burnsideI23x_SD
namespace burnsideI23x_SD

section TvLift

variable {F : Type} [Field F] [Finite F] [CharP F 2] {N : Type} [AddCommGroup N] [Module F N]
  (S : burnsideI23x_SD F N)

@[expose] noncomputable def tvκ (e : N) (c : F) : F :=
  burnsideI23x_sqrt F (c + c ^ 2 * S.Q0 e)

theorem tvκ_sq (e : N) (c : F) : S.tvκ e c ^ 2 = c + c ^ 2 * S.Q0 e :=
  burnsideI23x_sqrt_sq _

theorem lf_tv (e : N) (c : F) (x : N) :
    S.lf (S.tvEquiv e c) x = S.B x e * S.tvκ e c := by
  unfold lf tvκ
  rw [tvEquiv_apply, Q0_add_smul]
  have h : S.Q0 x + (S.Q0 x + (c * S.B x e) ^ 2 * S.Q0 e + c * S.B x e * S.B x e) =
      (S.B x e) ^ 2 * (c + c ^ 2 * S.Q0 e) := by
    have h2 := add_self_F (S.Q0 x)
    linear_combination h2
  rw [h, map_mul, burnsideI23x_sqrt_of_sq]


theorem exists_B_eq_one {e : N} (he : e ≠ 0) : ∃ x : N, S.B x e = 1 := by
  have h : ∃ y, S.B e y ≠ 0 := by
    by_contra hcon
    exact he (S.nondeg e (fun y => by_contra fun hy => hcon ⟨y, hy⟩))
  obtain ⟨y, hy⟩ := h
  refine ⟨(S.B e y)⁻¹ • y, ?_⟩
  rw [map_smul, LinearMap.smul_apply, smul_eq_mul, S.B_comm y e]
  exact inv_mul_cancel₀ hy

end TvLift

end burnsideI23x_SD
namespace burnsideI23x_SD

section TvGen

variable {F : Type} [Field F] [Finite F] [CharP F 2] {N : Type} [AddCommGroup N] [Module F N]
  [Nontrivial N] (S : burnsideI23x_SD F N) {Γ : Type} (lin : Γ → N →ₗ[F] N)

@[expose] def GenW' : Prop :=
  ∀ w : N × F, w ∈ AddSubgroup.closure
    {y | ∃ (γ : Γ) (x : N), y = (lin γ x - x, burnsideI23x_sqrt F (S.Q0 x + S.Q0 (lin γ x)))}

theorem genW'_of_tv (htv : ∀ (e : N) (c : F), e ≠ 0 → ∃ γ, ∀ x, lin γ x = S.tvEquiv e c x)
    {a : F} (ha0 : a ≠ 0) (ha1 : a ≠ 1) : GenW' S lin := by
  classical
  set C : AddSubgroup (N × F) := AddSubgroup.closure
    {y | ∃ (γ : Γ) (x : N), y = (lin γ x - x, burnsideI23x_sqrt F (S.Q0 x + S.Q0 (lin γ x)))}
    with hC
  have hsmul : ∀ (b : F) (y : N × F), y ∈ C → b • y ∈ C := by
    intro b y hy
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨γ, x, rfl⟩ := hy
      apply AddSubgroup.subset_closure
      refine ⟨γ, b • x, ?_⟩
      refine Prod.ext ?_ ?_
      · show b • (lin γ x - x) = lin γ (b • x) - b • x
        rw [map_smul, smul_sub]
      · show b * burnsideI23x_sqrt F (S.Q0 x + S.Q0 (lin γ x)) =
          burnsideI23x_sqrt F (S.Q0 (b • x) + S.Q0 (lin γ (b • x)))
        rw [map_smul, S.Q0_smul, S.Q0_smul, ← mul_add, map_mul, burnsideI23x_sqrt_of_sq]
    | zero => simp
    | add y₁ y₂ _ _ h1 h2 => rw [smul_add]; exact C.add_mem h1 h2
    | neg y _ h => rw [smul_neg]; exact C.neg_mem h
  have hvec : ∀ (e : N) (c : F), e ≠ 0 → ((c • e, S.tvκ e c) : N × F) ∈ C := by
    intro e c he
    obtain ⟨γ, hγ⟩ := htv e c he
    obtain ⟨x, hx⟩ := S.exists_B_eq_one he
    apply AddSubgroup.subset_closure
    refine ⟨γ, x, ?_⟩
    have h1 := hγ x
    refine Prod.ext ?_ ?_
    · show c • e = lin γ x - x
      rw [h1, S.tvEquiv_apply, hx, mul_one]
      abel
    · show S.tvκ e c = burnsideI23x_sqrt F (S.Q0 x + S.Q0 (lin γ x))
      rw [h1]
      have := S.lf_tv e c x
      unfold lf at this
      rw [this, hx, one_mul]
  obtain ⟨e₀, he₀⟩ := exists_ne (0 : N)
  have hδ : a * S.tvκ e₀ 1 - S.tvκ e₀ a ≠ 0 := by
    intro hcon
    have h' : a * S.tvκ e₀ 1 = S.tvκ e₀ a := sub_eq_zero.1 hcon
    have hsq : (a * S.tvκ e₀ 1) ^ 2 = S.tvκ e₀ a ^ 2 := by rw [h']
    rw [mul_pow, S.tvκ_sq, S.tvκ_sq] at hsq
    have h2 : a * (a - 1) = 0 := by linear_combination hsq
    rcases mul_eq_zero.1 h2 with h | h
    · exact ha0 h
    · exact ha1 (sub_eq_zero.1 h)
  have hK : ∀ d : F, ((0 : N), d) ∈ C := by
    intro d
    have h1 := hsmul a _ (hvec e₀ 1 he₀)
    have h2 := hvec e₀ a he₀
    have h3 : ((a * S.tvκ e₀ 1 - S.tvκ e₀ a) • ((0 : N), (1 : F))) ∈ C := by
      have := C.sub_mem h1 h2
      convert this using 1
      refine Prod.ext ?_ ?_
      · show (a * S.tvκ e₀ 1 - S.tvκ e₀ a) • (0 : N) = (a • (1 : F) • e₀ - a • e₀)
        rw [one_smul, sub_self, smul_zero]
      · show (a * S.tvκ e₀ 1 - S.tvκ e₀ a) * 1 = a * S.tvκ e₀ 1 - S.tvκ e₀ a
        ring
    have h4 := hsmul ((a * S.tvκ e₀ 1 - S.tvκ e₀ a)⁻¹ * d) _ h3
    convert h4 using 1
    refine Prod.ext ?_ ?_
    · show (0 : N) = _
      simp
    · show d = _
      show d = ((a * S.tvκ e₀ 1 - S.tvκ e₀ a)⁻¹ * d) * ((a * S.tvκ e₀ 1 - S.tvκ e₀ a) * 1)
      field_simp
  intro w
  by_cases hw : w.1 = 0
  · have : w = ((0 : N), w.2) := Prod.ext hw rfl
    rw [this]
    exact hK _
  · have h1 := hvec w.1 1 hw
    have h2 := hK (w.2 - S.tvκ w.1 1)
    have := C.add_mem h1 h2
    convert this using 1
    refine Prod.ext ?_ ?_
    · show w.1 = (1 : F) • w.1 + 0
      rw [one_smul, add_zero]
    · show w.2 = S.tvκ w.1 1 + (w.2 - S.tvκ w.1 1)
      ring

end TvGen

end burnsideI23x_SD
namespace burnsideI23x_SD

section TvEnd

variable {F : Type} [Field F] [Finite F] [CharP F 2] {N : Type} [AddCommGroup N] [Module F N]
  [Nontrivial N] (S : burnsideI23x_SD F N) {Γ : Type} (lin : Γ → N →ₗ[F] N)


end TvEnd

end burnsideI23x_SD
section LinHom

variable {D : CFSG.Quasithin.FFModel} {K M : Type} [Field K] [AddCommGroup M] [Module K M]
  {W : Type*} [CommGroup W] {H : Subgroup (MulAut W)} {Z : Subgroup W} {π : D.Gam →* ↥H}
  {f : W → M} (LM : CFSG.Quasithin.Vol2.KGNat.LinModel D K M)

open CFSG.Quasithin CFSG.ASVolI.ChIJK CFSG.Quasithin.Vol2.KGNat in
theorem burnsideI23x_lin_mul (hf : IsCoord LM H Z π f) (γ δ : D.Gam) (x : M) :
    LM.lin (γ * δ) x = LM.lin γ (LM.lin δ x) := by
  obtain ⟨w, rfl⟩ := hf.surj x
  rw [← hf.act, ← hf.act, ← hf.act, map_mul]
  rfl

open CFSG.Quasithin CFSG.ASVolI.ChIJK CFSG.Quasithin.Vol2.KGNat in
theorem burnsideI23x_lin_one (hf : IsCoord LM H Z π f) (x : M) : LM.lin 1 x = x := by
  obtain ⟨w, rfl⟩ := hf.surj x
  rw [← hf.act, map_one]
  rfl

open CFSG.Quasithin CFSG.ASVolI.ChIJK CFSG.Quasithin.Vol2.KGNat in
@[expose] noncomputable def burnsideI23x_linHom (hf : IsCoord LM H Z π f) :
    D.Gam →* (M ≃ₗ[K] M) where
  toFun γ := LinearEquiv.ofLinear (LM.lin γ) (LM.lin γ⁻¹)
    (LinearMap.ext fun x => by
      simp only [LinearMap.comp_apply, LinearMap.id_apply]
      rw [← burnsideI23x_lin_mul LM hf, mul_inv_cancel, burnsideI23x_lin_one LM hf])
    (LinearMap.ext fun x => by
      simp only [LinearMap.comp_apply, LinearMap.id_apply]
      rw [← burnsideI23x_lin_mul LM hf, inv_mul_cancel, burnsideI23x_lin_one LM hf])
  map_one' := LinearEquiv.ext fun x => burnsideI23x_lin_one LM hf x
  map_mul' γ δ := LinearEquiv.ext fun x => burnsideI23x_lin_mul LM hf γ δ x


end LinHom

namespace burnsideI23x_SD

section GenBridge

variable {F : Type} [Field F] [Finite F] [CharP F 2] {N : Type} [AddCommGroup N] [Module F N]
  (S : burnsideI23x_SD F N) {Γ : Type} [Group Γ] (A : Γ →* (N ≃ₗ[F] N))
  (hA : ∀ γ, S.Symp (A γ)) (lin : Γ → N →ₗ[F] N)

include hA in
theorem GenW'.toGenW (hAlin : ∀ γ x, A γ x = lin γ x) (h : S.GenW' lin) : S.GenW A hA := by
  intro w
  refine AddSubgroup.closure_mono ?_ (h w)
  rintro _ ⟨γ, x, rfl⟩
  refine ⟨γ, (x, 0), ?_⟩
  refine Prod.ext ?_ ?_
  · show lin γ x - x = A γ x - x
    rw [hAlin]
  · show burnsideI23x_sqrt F (S.Q0 x + S.Q0 (lin γ x)) = 0 + S.lf (A γ) x - 0
    unfold lf
    rw [hAlin]
    simp

end GenBridge

end burnsideI23x_SD
namespace burnsideI23x_SD

section GenMul

variable {F : Type} [Field F] [Finite F] [CharP F 2] {N : Type} [AddCommGroup N] [Module F N]
  (S : burnsideI23x_SD F N) {Γ : Type} [Group Γ] (A : Γ →* (N ≃ₗ[F] N))
  (hA : ∀ γ, S.Symp (A γ))

include hA in
theorem genW_mul (hgen : S.GenW A hA) : ∀ w : Multiplicative (N × F), w ∈ Subgroup.closure
    {x | ∃ (γ : Γ) (y : Multiplicative (N × F)), x = S.liftHom A hA γ y * y⁻¹} := by
  intro w
  have h := hgen (Multiplicative.toAdd w)
  have key : ∀ a : N × F, a ∈ AddSubgroup.closure
      {y | ∃ (γ : Γ) (x : N × F), y = S.lift (hA γ) x - x} →
      Multiplicative.ofAdd a ∈ Subgroup.closure
        {x | ∃ (γ : Γ) (y : Multiplicative (N × F)), x = S.liftHom A hA γ y * y⁻¹} := by
    intro a ha
    induction ha using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨γ, x, rfl⟩ := hy
      apply Subgroup.subset_closure
      exact ⟨γ, Multiplicative.ofAdd x, by rw [S.liftHom_apply, ofAdd_sub, div_eq_mul_inv]⟩
    | zero => exact Subgroup.one_mem _
    | add a b _ _ h1 h2 => exact Subgroup.mul_mem _ h1 h2
    | neg a _ h => exact Subgroup.inv_mem _ h
  exact key _ h

end GenMul

end burnsideI23x_SD

open CFSG.Quasithin CFSG.ASVolI.ChIJK CFSG.Quasithin.Vol2.KGNat in
theorem burnsideI23x_plumb {m : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
    {M : Type} [AddCommGroup M] [Module F M] [Finite M] [Nontrivial M]
    (LM : LinModel (i23NaturalModel m F) F M) (S : burnsideI23x_SD F M)
    (hsymp : ∀ γ x y, S.B (LM.lin γ x) (LM.lin γ y) = S.B x y)
    (hfaith : ∀ γ, (∀ x, LM.lin γ x = x) → γ = 1)
    (hgenM : S.GenW' LM.lin)
    (hbound : ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
      ∀ (L : Subgroup (MulAut V)) (W0 : Subgroup V) (π : (i23NaturalModel m F).Gam →* ↥L),
        (i23NaturalModel m F).RealizesVia L ⊤ W0 π → W0 = fixV L → commV L = ⊤ →
        Nat.card W0 ≤ Nat.card F)
    {U : Type} [CommGroup U] [Finite U] (hU : ∀ u : U, u ^ 2 = 1)
    {L : Subgroup (MulAut U)} {K : Subgroup U} (huniv : IsUniversalCovering L K)
    {marking : (i23NaturalModel m F).Gam →* ↥L}
    {β : U →* ↥(i23NaturalModel m F).sec ⧸
      (i23NaturalModel m F).ker.subgroupOf (i23NaturalModel m F).sec}
    (hsec : I23SectionMap (i23NaturalModel m F) L K marking β) :
    ∃ (A : (i23NaturalModel m F).Gam →* (M ≃ₗ[F] M)) (hA : ∀ γ, S.Symp (A γ))
      (ψ : U ≃* Multiplicative (M × F)),
      (∀ γ x, A γ x = LM.lin γ x) ∧ S.GenW A hA ∧ Function.Surjective marking ∧
      fixV L = K ∧
      (∀ (γ : (i23NaturalModel m F).Gam) (u : U),
        ψ ((marking γ : MulAut U) u) = S.liftHom A hA γ (ψ u)) ∧
      (∀ u : U, (Multiplicative.toAdd (ψ u)).1 = Multiplicative.toAdd (LM.e (β u))) := by
  classical
  have hf := burnsideI23x_isCoord LM hsec
  set A := burnsideI23x_linHom LM hf with hAdef
  have hAlin : ∀ γ x, A γ x = LM.lin γ x := fun γ x => rfl
  have hA : ∀ γ, S.Symp (A γ) := fun γ x y => hsymp γ x y
  have hgen : S.GenW A hA := burnsideI23x_SD.GenW'.toGenW S A hA LM.lin hAlin hgenM
  have hKfix : K ≤ fixV L := huniv.1
  have hcommtop : commV L = ⊤ := huniv.2.1
  have hnofix : ∀ x : M, (∀ γ, LM.lin γ x = x) → x = 0 := by
    intro x hx
    have := (S.fix_iff A hA hgen (x, 0)).1 (fun γ => by
      refine Prod.ext (hx γ) ?_
      show 0 + S.lf (A γ) x = 0
      unfold burnsideI23x_SD.lf
      rw [hAlin, hx γ, burnsideI23x_SD.add_self_F, map_zero, zero_add])
    exact this
  have hfixV : fixV L = K := burnsideI23x_fixV_eq LM hsec hKfix hnofix
  have hinj : Function.Injective marking := by
    rw [injective_iff_map_eq_one]
    intro γ hγ
    apply hfaith
    intro x
    obtain ⟨v, rfl⟩ := hf.surj x
    rw [← hf.act, hγ]
    rfl
  have hbij : Function.Bijective marking := ⟨hinj, hsec.1⟩
  have hbound' := hbound U hU L K marking (burnsideI23x_realizesVia hsec hKfix) hfixV.symm
    hcommtop
  let fMul : U →* Multiplicative M := LM.e.toMonoidHom.comp β
  have hfs : Function.Surjective fMul := LM.e.surjective.comp hsec.2.1
  have hfk : fMul.ker = K := by
    ext v
    rw [MonoidHom.mem_ker, ← hsec.2.2.1, MonoidHom.mem_ker]
    exact LM.e.map_eq_one_iff
  have hfπ : ∀ (γ : (i23NaturalModel m F).Gam) (v : U), fMul ((marking γ : MulAut U) v) =
      Multiplicative.ofAdd (A γ (Multiplicative.toAdd (fMul v))) := fun γ v => by
    have := hf.act γ v
    exact congrArg Multiplicative.ofAdd this
  obtain ⟨ψ, hψ1, hψ2⟩ := burnsideI23x_univ_iso S A hA hU huniv marking hbij fMul hfs hfk hfπ
    hbound' (S.genW_mul A hA hgen)
  exact ⟨A, hA, ψ, hAlin, hgen, hsec.1, hfixV, hψ1, hψ2⟩
namespace burnsideI23x_SD

section Torus

variable {F : Type} [Field F] [Finite F] [CharP F 2] {N : Type} [AddCommGroup N] [Module F N]
  (S : burnsideI23x_SD F N)

@[expose] def torusLin (e e' : N) (b : F) : N →ₗ[F] N where
  toFun x := x + ((b - 1) * S.B x e') • e + ((b⁻¹ - 1) * S.B x e) • e'
  map_add' x y := by
    simp only [map_add, LinearMap.add_apply, mul_add, add_smul]
    abel
  map_smul' a x := by
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply, smul_add,
      smul_smul]
    rw [mul_left_comm (b - 1), mul_left_comm (b⁻¹ - 1)]

theorem torusLin_apply (e e' : N) (b : F) (x : N) :
    S.torusLin e e' b x = x + ((b - 1) * S.B x e') • e + ((b⁻¹ - 1) * S.B x e) • e' := rfl


end Torus

end burnsideI23x_SD

namespace burnsideI23x_SD

section Torus2

variable {F : Type} [Field F] [Finite F] [CharP F 2] {N : Type} [AddCommGroup N] [Module F N]
  (S : burnsideI23x_SD F N)

theorem torusLin_comp_inv {e e' : N} (hee : S.B e e' = 1) {b : F} (hb : b ≠ 0) (x : N) :
    S.torusLin e e' b (S.torusLin e e' b⁻¹ x) = x := by
  have h1 : S.B e' e = 1 := by rw [S.B_comm]; exact hee
  rw [torusLin_apply S e e' b (S.torusLin e e' b⁻¹ x), torusLin_apply S e e' b⁻¹ x]
  simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, S.alt,
    hee, h1, mul_zero, add_zero, zero_add, mul_one, inv_inv]
  have hbb : b * b⁻¹ = 1 := mul_inv_cancel₀ hb
  have c1 : (b⁻¹ - 1) * S.B x e' + (b - 1) * (S.B x e' + (b⁻¹ - 1) * S.B x e') = 0 := by
    linear_combination (S.B x e') * hbb
  have c2 : (b - 1) * S.B x e + (b⁻¹ - 1) * (S.B x e + (b - 1) * S.B x e) = 0 := by
    linear_combination (S.B x e) * hbb
  have e1 : x + ((b⁻¹ - 1) * S.B x e') • e + ((b - 1) * S.B x e) • e' +
      ((b - 1) * (S.B x e' + (b⁻¹ - 1) * S.B x e')) • e +
      ((b⁻¹ - 1) * (S.B x e + (b - 1) * S.B x e)) • e' =
      x + (((b⁻¹ - 1) * S.B x e') + ((b - 1) * (S.B x e' + (b⁻¹ - 1) * S.B x e'))) • e +
      (((b - 1) * S.B x e) + ((b⁻¹ - 1) * (S.B x e + (b - 1) * S.B x e))) • e' := by
    module
  rw [e1, c1, c2]
  simp

@[expose] def torusEquiv {e e' : N} (hee : S.B e e' = 1) {b : F} (hb : b ≠ 0) : N ≃ₗ[F] N :=
  LinearEquiv.ofLinear (S.torusLin e e' b) (S.torusLin e e' b⁻¹)
    (LinearMap.ext fun x => S.torusLin_comp_inv hee hb x)
    (LinearMap.ext fun x => by
      have := S.torusLin_comp_inv hee (inv_ne_zero hb) x
      rwa [inv_inv] at this)


end Torus2

end burnsideI23x_SD
namespace burnsideI23x_SD

section Irred

variable {F : Type} [Field F] [Finite F] [CharP F 2] {N : Type} [AddCommGroup N] [Module F N]
  (S : burnsideI23x_SD F N) {Γ : Type} (lin : Γ → N →ₗ[F] N)


end Irred

end burnsideI23x_SD
@[expose] def burnsideI23x_B1 (F : Type) [Field F] : (Fin 2 → F) →ₗ[F] (Fin 2 → F) →ₗ[F] F :=
  LinearMap.mk₂ F (fun x y => x 0 * y 1 + x 1 * y 0)
    (fun x x' y => by simp only [Pi.add_apply]; ring)
    (fun c x y => by simp only [Pi.smul_apply, smul_eq_mul]; ring)
    (fun x y y' => by simp only [Pi.add_apply]; ring)
    (fun c x y => by simp only [Pi.smul_apply, smul_eq_mul]; ring)

theorem burnsideI23x_B1_apply (F : Type) [Field F] (x y : Fin 2 → F) :
    burnsideI23x_B1 F x y = x 0 * y 1 + x 1 * y 0 := rfl

@[expose] def burnsideI23x_sd1 (F : Type) [Field F] [CharP F 2] : burnsideI23x_SD F (Fin 2 → F) where
  B := burnsideI23x_B1 F
  Q0 x := x 0 * x 1
  Q0_add x y := by
    rw [burnsideI23x_B1_apply]
    simp only [Pi.add_apply]
    ring
  Q0_smul c x := by
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  alt x := by
    rw [burnsideI23x_B1_apply]
    have h : (2 : F) = 0 := CharP.cast_eq_zero F 2
    linear_combination (x 0 * x 1) * h
  nondeg x hx := by
    funext i
    fin_cases i
    · have h := hx (Pi.single 1 1)
      rw [burnsideI23x_B1_apply] at h
      simpa using h
    · have h := hx (Pi.single 0 1)
      rw [burnsideI23x_B1_apply] at h
      simpa using h

theorem burnsideI23x_sd1_B (F : Type) [Field F] [CharP F 2] (x y : Fin 2 → F) :
    (burnsideI23x_sd1 F).B x y = x 0 * y 1 + x 1 * y 0 := rfl

theorem burnsideI23x_sd1_Q0 (F : Type) [Field F] [CharP F 2] (x : Fin 2 → F) :
    (burnsideI23x_sd1 F).Q0 x = x 0 * x 1 := rfl

open CFSG.Quasithin CFSG.ASVolI.ChIJK CFSG.Quasithin.Vol2.KGNat CFSG.Assembly.LowTwoRank in
open scoped Matrix in
theorem burnsideI23x_hsymp1 (F : Type) [Field F] [CharP F 2] (γ : ↥(StatedSL 2 F))
    (x y : Fin 2 → F) :
    (burnsideI23x_sd1 F).B ((burnsideI23x_LM1 F).lin γ x) ((burnsideI23x_LM1 F).lin γ y) =
      (burnsideI23x_sd1 F).B x y := by
  obtain ⟨A, rfl⟩ := (specialLinearGroupEquivStatedSL 2 F).surjective γ
  have hdet := A.2
  rw [Matrix.det_fin_two] at hdet
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  show (burnsideI23x_sd1 F).B ((A : Matrix (Fin 2) (Fin 2) F) *ᵥ x)
    ((A : Matrix (Fin 2) (Fin 2) F) *ᵥ y) = _
  rw [burnsideI23x_sd1_B, burnsideI23x_sd1_B]
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  linear_combination (x 0 * y 1 + x 1 * y 0) * hdet +
    ((x 0 * y 1 + x 1 * y 0) * ((A : Matrix (Fin 2) (Fin 2) F) 0 1 * (A : Matrix (Fin 2) (Fin 2) F) 1 0) +
      (A : Matrix (Fin 2) (Fin 2) F) 0 0 * (A : Matrix (Fin 2) (Fin 2) F) 1 0 * x 0 * y 0 +
      (A : Matrix (Fin 2) (Fin 2) F) 0 1 * (A : Matrix (Fin 2) (Fin 2) F) 1 1 * x 1 * y 1) * h2

open CFSG.Quasithin CFSG.ASVolI.ChIJK CFSG.Quasithin.Vol2.KGNat CFSG.Assembly.LowTwoRank in
open scoped Matrix in
theorem burnsideI23x_hfaith1 (F : Type) [Field F] (γ : ↥(StatedSL 2 F))
    (h : ∀ x, (burnsideI23x_LM1 F).lin γ x = x) : γ = 1 := by
  obtain ⟨A, rfl⟩ := (specialLinearGroupEquivStatedSL 2 F).surjective γ
  have hA : A = 1 := by
    ext i j
    have := congrFun (h (Pi.single j 1)) i
    have h2 : ((A : Matrix (Fin 2) (Fin 2) F) *ᵥ (Pi.single j 1 : Fin 2 → F)) i =
        (Pi.single j 1 : Fin 2 → F) i := this
    simp only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true] at h2
    rw [Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply]
    rw [h2]
  rw [hA, map_one]

open CFSG.Quasithin CFSG.ASVolI.ChIJK CFSG.Quasithin.Vol2.KGNat CFSG.Assembly.LowTwoRank in
open scoped Matrix in
theorem burnsideI23x_htv1 (F : Type) [Field F] [Finite F] [CharP F 2] (e : Fin 2 → F) (c : F) :
    ∃ γ : ↥(StatedSL 2 F), ∀ x, (burnsideI23x_LM1 F).lin γ x =
      (burnsideI23x_sd1 F).tvEquiv e c x := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hdet : (!![1 + c * e 0 * e 1, c * e 0 * e 0; c * e 1 * e 1, 1 + c * e 0 * e 1] :
      Matrix (Fin 2) (Fin 2) F).det = 1 := by
    rw [Matrix.det_fin_two_of]
    linear_combination (c * e 0 * e 1) * h2
  refine ⟨specialLinearGroupEquivStatedSL 2 F ⟨_, hdet⟩, fun x => ?_⟩
  show (!![1 + c * e 0 * e 1, c * e 0 * e 0; c * e 1 * e 1, 1 + c * e 0 * e 1] :
      Matrix (Fin 2) (Fin 2) F) *ᵥ x = _
  rw [burnsideI23x_SD.tvEquiv_apply, burnsideI23x_sd1_B]
  ext i
  fin_cases i
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring
namespace burnsideI23x_SD

section LineSub

variable {F : Type} [Field F] [Finite F] [CharP F 2] {N : Type} [AddCommGroup N] [Module F N]
  (S : burnsideI23x_SD F N)


end LineSub

end burnsideI23x_SD
namespace burnsideI23x_SD

section UCg3

variable {F : Type} [Field F] [Finite F] [CharP F 2] {N : Type} [AddCommGroup N] [Module F N]
  {S : burnsideI23x_SD F N} {Γ : Type} [Group Γ] {A : Γ →* (N ≃ₗ[F] N)}
  {hA : ∀ γ, S.Symp (A γ)} {U : Type} [CommGroup U]


end UCg3

end burnsideI23x_SD
theorem burnsideI23x_exists_ne_zero_one {F : Type} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 2 ≤ n) : ∃ a : F, a ≠ 0 ∧ a ≠ 1 := by
  by_contra hcon
  have hall : ∀ a : F, a = 0 ∨ a = 1 := fun a => by
    by_cases h0 : a = 0
    · exact Or.inl h0
    · by_cases h1 : a = 1
      · exact Or.inr h1
      · exact absurd ⟨a, h0, h1⟩ hcon
  have h2 : Nat.card F ≤ 2 := by
    classical
    have : Fintype F := Fintype.ofFinite F
    rw [Nat.card_eq_fintype_card]
    calc Fintype.card F ≤ Fintype.card Bool :=
          Fintype.card_le_of_injective (fun a => decide (a = 1)) (fun a b h => by
            rcases hall a with rfl | rfl <;> rcases hall b with rfl | rfl <;> simp_all)
      _ = 2 := rfl
  have h4 : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  omega


open CFSG.Quasithin CFSG.ASVolI.ChIJK CFSG.Quasithin.Vol2.KGNat CFSG.Assembly.LowTwoRank in
theorem burnsideI23x_hbound1 {n : ℕ} (hn : 2 ≤ n) {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 2 ^ n) :
    ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
      ∀ (L : Subgroup (MulAut V)) (W0 : Subgroup V)
        (π : (i23NaturalModel 1 F).Gam →* ↥L),
        (i23NaturalModel 1 F).RealizesVia L ⊤ W0 π → W0 = fixV L → commV L = ⊤ →
        Nat.card W0 ≤ Nat.card F := by
  intro V _ _ hV L W0 π hreal hW0 hcomm
  subst hW0
  have hcommOf : XMod.commOf ↥L (⊤ : Subgroup V) = ⊤ := by
    rw [CFSG.Quasithin.MS93.xmodCommOf_top_eq]
    exact hcomm
  have hreal' : (FFModel.nat (StatedSL 2 F)).Realizes L ⊤ (fixV L ⊓ ⊤) := by
    rw [inf_top_eq]
    exact ⟨π, hreal⟩
  have := CFSG.Quasithin.B513N.card_fixV_le_of_sl2 hV L ⊤ (fun x _ v _ => Subgroup.mem_top _)
    hcommOf hn hF hreal'
  rw [inf_top_eq, ← hF] at this
  exact this

namespace burnsideI23x_SD

section UCo

variable {F : Type} [Field F] [Finite F] [CharP F 2] {N : Type} [AddCommGroup N] [Module F N]
  {S : burnsideI23x_SD F N} {U : Type} [CommGroup U]


end UCo

end burnsideI23x_SD

namespace burnsideI23x_SD

section UCoPoint

variable {F : Type} [Field F] [Finite F] [CharP F 2] {N : Type} [AddCommGroup N] [Module F N]
  {S : burnsideI23x_SD F N} {U : Type} [CommGroup U]


end UCoPoint

end burnsideI23x_SD

namespace burnsideI23x_SD

section UCoFix

variable {F : Type} [Field F] [Finite F] [CharP F 2] {N : Type} [AddCommGroup N] [Module F N]
  {S : burnsideI23x_SD F N} {Γ : Type} [Group Γ] {A : Γ →* (N ≃ₗ[F] N)}
  {hA : ∀ γ, S.Symp (A γ)} {U : Type} [CommGroup U]


end UCoFix

end burnsideI23x_SD

namespace burnsideI23x_SD

section UCoFix2

variable {F : Type} [Field F] [Finite F] [CharP F 2] {N : Type} [AddCommGroup N] [Module F N]
  {S : burnsideI23x_SD F N} {Γ : Type} [Group Γ] {A : Γ →* (N ≃ₗ[F] N)}
  {hA : ∀ γ, S.Symp (A γ)} {U : Type} [CommGroup U]


end UCoFix2

end burnsideI23x_SD

namespace burnsideI23x_SD

section RootClassify

variable {F : Type} [Field F] [Finite F] [CharP F 2] {N : Type} [AddCommGroup N] [Module F N]
  (S : burnsideI23x_SD F N)


end RootClassify

end burnsideI23x_SD

namespace burnsideI23x_SD

section RootClassify2

variable {F : Type} [Field F] [Finite F] [CharP F 2] {N : Type} [AddCommGroup N] [Module F N]
  {S : burnsideI23x_SD F N} {Γ : Type} [Group Γ] {A : Γ →* (N ≃ₗ[F] N)}
  {hA : ∀ γ, S.Symp (A γ)} {U : Type} [CommGroup U]


end RootClassify2

end burnsideI23x_SD

namespace burnsideI23x_SD

section RootClause

variable {F : Type} [Field F] [Finite F] [CharP F 2] {N : Type} [AddCommGroup N] [Module F N]
  {S : burnsideI23x_SD F N} {Γ : Type} [Group Γ] {A : Γ →* (N ≃ₗ[F] N)}
  {hA : ∀ γ, S.Symp (A γ)} {U : Type} [CommGroup U]


end RootClause

end burnsideI23x_SD

namespace burnsideI23x_SD

section RootClause2

variable {F : Type} [Field F] [Finite F] [CharP F 2] {N : Type} [AddCommGroup N] [Module F N]
  {S : burnsideI23x_SD F N} {Γ : Type} [Group Γ] {A : Γ →* (N ≃ₗ[F] N)}
  {hA : ∀ γ, S.Symp (A γ)} {U : Type} [CommGroup U]


end RootClause2

end burnsideI23x_SD

namespace burnsideI23x_SD

section RootClause3

variable {F : Type} [Field F] [Finite F] [CharP F 2] {N : Type} [AddCommGroup N] [Module F N]
  {S : burnsideI23x_SD F N} {Γ : Type} [Group Γ] {A : Γ →* (N ≃ₗ[F] N)}
  {hA : ∀ γ, S.Symp (A γ)} {U : Type} [CommGroup U]


end RootClause3

end burnsideI23x_SD

namespace burnsideI23x_SD

section RootClause4

variable {F : Type} [Field F] [Finite F] [CharP F 2] {N : Type} [AddCommGroup N] [Module F N]
  {S : burnsideI23x_SD F N} {Γ : Type} [Group Γ] {A : Γ →* (N ≃ₗ[F] N)}
  {hA : ∀ γ, S.Symp (A γ)} {U : Type} [CommGroup U]


end RootClause4

end burnsideI23x_SD


namespace burnsideI23x_SD

section ExistsLift

variable {F : Type} [Field F] [Finite F] [CharP F 2] {N : Type} [AddCommGroup N] [Module F N]
  [Finite N] (S : burnsideI23x_SD F N)


end ExistsLift

end burnsideI23x_SD
namespace burnsideI23x_SD

section PhiHom

variable {F : Type} [Field F] [Finite F] [CharP F 2] {N : Type} [AddCommGroup N] [Module F N]
  [Finite N] {S : burnsideI23x_SD F N} {Γ : Type} [Group Γ] {A : Γ →* (N ≃ₗ[F] N)}
  {hA : ∀ γ, S.Symp (A γ)} {ι : Type} [Fintype ι] [DecidableEq ι]


variable (S A hA)


variable {S A hA}


end PhiHom

end burnsideI23x_SD


namespace burnsideI23x_SD

section PhiRange

variable {F : Type} [Field F] [Finite F] [CharP F 2] {N : Type} [AddCommGroup N] [Module F N]
  [Finite N] {S : burnsideI23x_SD F N} {Γ : Type} [Group Γ] {A : Γ →* (N ≃ₗ[F] N)}
  {hA : ∀ γ, S.Symp (A γ)} {ι : Type} [Fintype ι] [DecidableEq ι]


end PhiRange

end burnsideI23x_SD

namespace burnsideI23x_SD

section PiOmega

variable {F : Type} [Field F] [Finite F] [CharP F 2] {N : Type} [AddCommGroup N] [Module F N]
  [Finite N] {S : burnsideI23x_SD F N} {Γ : Type} [Group Γ] {A : Γ →* (N ≃ₗ[F] N)}
  {hA : ∀ γ, S.Symp (A γ)} {ι : Type} [Fintype ι] [DecidableEq ι]


end PiOmega

end burnsideI23x_SD
namespace burnsideI23x_SD

section Transport

variable {F : Type} [Field F] {W W' : Type} [AddCommGroup W] [Module F W] [AddCommGroup W']
  [Module F W'] {V : Type} [CommGroup V]


end Transport

end burnsideI23x_SD

namespace burnsideI23x_SD

section OrthMarked

variable {F : Type} [Field F] [Finite F] [CharP F 2] {N : Type} [AddCommGroup N] [Module F N]
  {S : burnsideI23x_SD F N} {Γ : Type} [Group Γ] {A : Γ →* (N ≃ₗ[F] N)}
  {hA : ∀ γ, S.Symp (A γ)} {U : Type} [CommGroup U]


end OrthMarked

end burnsideI23x_SD


open CFSG.Quasithin CFSG.ASVolI.ChIJK CFSG.Quasithin.Vol2.KGNat CFSG.Quasithin.Vol2.Ch11.SecA
  CFSG.Assembly.LowTwoRank in
open CFSG.Quasithin CFSG.ASVolI.ChIJK CFSG.Quasithin.Vol2.KGNat CFSG.Quasithin.Vol2.Ch11.SecA
  CFSG.Quasithin.Vol2.Ch11.G2Q8 in

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChIJK CFSG.Quasithin.Vol2.KGNat
  CFSG.Assembly.LowTwoRank in


open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.MS93 CFSG.ASVolI.ChIJK
  CFSG.Quasithin.Vol2.KGNat CFSG.Assembly.LowTwoRank CFSG.Quasithin.Explicit in

open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.MS93 CFSG.ASVolI.ChIJK
  CFSG.Quasithin.Vol2.KGNat CFSG.Assembly.LowTwoRank CFSG.Quasithin.Explicit in

open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.MS93 CFSG.ASVolI.ChIJK
  CFSG.Quasithin.Vol2.KGNat CFSG.Assembly.LowTwoRank CFSG.Quasithin.Explicit in
namespace burnsideI23x_SD

section Siegel

variable {F : Type} [Field F] [Finite F] [CharP F 2] {N : Type} [AddCommGroup N] [Module F N]
  (S : burnsideI23x_SD F N)


end Siegel

end burnsideI23x_SD

namespace burnsideI23x_SD

section IrredIso

variable {F : Type} [Field F] [Finite F] [CharP F 2] {N : Type} [AddCommGroup N] [Module F N]
  [Finite N] (S : burnsideI23x_SD F N) {Γ : Type} (lin : Γ → N →ₗ[F] N)


end IrredIso

end burnsideI23x_SD
open CFSG.Quasithin CFSG.ASVolI.ChIJK CFSG.Quasithin.Vol2.KGNat CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.Quasithin.JonesParshall CFSG.Assembly.LowTwoRank in

open CFSG.Quasithin CFSG.ASVolI.ChIJK CFSG.Quasithin.Vol2.KGNat CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.Quasithin.JonesParshall in
open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.MS93 CFSG.ASVolI.ChIJK
  CFSG.Quasithin.Vol2.KGNat CFSG.Assembly.LowTwoRank in


open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.JonesParshall CFSG.Quasithin.MS93
  CFSG.ASVolI.ChIJK CFSG.Quasithin.Vol2.KGNat CFSG.Quasithin.Vol2.Ch11.SecA
  CFSG.Assembly.LowTwoRank in


open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.MS93 CFSG.ASVolI.ChIJK
  CFSG.Quasithin.Vol2.KGNat CFSG.Quasithin.Vol2.Ch11.SecA CFSG.Assembly.LowTwoRank in
open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChIJK CFSG.Quasithin.Vol2.KGNat
  CFSG.Assembly.LowTwoRank in


open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK CFSG.Quasithin.MS93 in

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.Quasithin.MS93 CFSG.ASVolI.ChIJK in
open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.JonesParshall CFSG.Quasithin.MS93
  CFSG.ASVolI.ChIJK CFSG.Quasithin.Vol2.KGNat CFSG.Quasithin.Vol2.Ch11.SecA CFSG.Quasithin.Explicit
  CFSG.Quasithin.Vol2.Ch11.G2Q8 in
open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ClassicalInvolution.ModelFacts.OddCover in
open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ClassicalInvolution.ModelFacts.OddCover CFSG.QuasithinUnique.Bridge.Alt57Model in

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ClassicalInvolution.ModelFacts.OddCover CFSG.QuasithinUnique.Bridge.Alt57Model in

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ClassicalInvolution.ModelFacts.OddCover CFSG.QuasithinUnique.Bridge.Alt57Model in
open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ClassicalInvolution.ModelFacts.OddCover CFSG.QuasithinUnique.Bridge.Alt57Model
  CFSG.Quasithin.Vol2.KGNat CFSG.ASVolI.ChIJK in

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ClassicalInvolution.ModelFacts.OddCover CFSG.QuasithinUnique.Bridge.Alt57Model
  CFSG.Quasithin.Vol2.KGNat CFSG.ASVolI.ChIJK in

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ClassicalInvolution.ModelFacts.OddCover CFSG.QuasithinUnique.Bridge.Alt57Model
  CFSG.Quasithin.Vol2.KGNat CFSG.ASVolI.ChIJK in

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ClassicalInvolution.ModelFacts.OddCover CFSG.QuasithinUnique.Bridge.Alt57Model
  CFSG.Quasithin.Vol2.KGNat CFSG.ASVolI.ChIJK in

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ClassicalInvolution.ModelFacts.OddCover CFSG.QuasithinUnique.Bridge.Alt57Model
  CFSG.Quasithin.Vol2.KGNat CFSG.ASVolI.ChIJK in
open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ClassicalInvolution.ModelFacts.OddCover CFSG.QuasithinUnique.Bridge.Alt57Model
  CFSG.Quasithin.Vol2.KGNat CFSG.ASVolI.ChIJK in

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ClassicalInvolution.ModelFacts.OddCover CFSG.QuasithinUnique.Bridge.Alt57Model
  CFSG.Quasithin.Vol2.KGNat CFSG.ASVolI.ChIJK in

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ClassicalInvolution.ModelFacts.OddCover CFSG.QuasithinUnique.Bridge.Alt57Model
  CFSG.Quasithin.Vol2.KGNat CFSG.ASVolI.ChIJK in

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ClassicalInvolution.ModelFacts.OddCover CFSG.QuasithinUnique.Bridge.Alt57Model
  CFSG.Quasithin.Vol2.KGNat CFSG.ASVolI.ChIJK in

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ClassicalInvolution.ModelFacts.OddCover CFSG.QuasithinUnique.Bridge.Alt57Model
  CFSG.Quasithin.Vol2.KGNat CFSG.ASVolI.ChIJK in
open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ClassicalInvolution.ModelFacts.OddCover CFSG.QuasithinUnique.Bridge.Alt57Model
  CFSG.Quasithin.Vol2.KGNat CFSG.ASVolI.ChIJK in

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ClassicalInvolution.ModelFacts.OddCover CFSG.QuasithinUnique.Bridge.Alt57Model
  CFSG.Quasithin.Vol2.KGNat CFSG.ASVolI.ChIJK in
open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ClassicalInvolution.ModelFacts.OddCover CFSG.QuasithinUnique.Bridge.Alt57Model
  CFSG.Quasithin.Vol2.KGNat CFSG.ASVolI.ChIJK in

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ClassicalInvolution.ModelFacts.OddCover CFSG.QuasithinUnique.Bridge.Alt57Model
  CFSG.Quasithin.Vol2.KGNat CFSG.ASVolI.ChIJK in
open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ClassicalInvolution.ModelFacts.OddCover CFSG.QuasithinUnique.Bridge.Alt57Model
  CFSG.Quasithin.Vol2.KGNat CFSG.ASVolI.ChIJK in

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ClassicalInvolution.ModelFacts.OddCover CFSG.QuasithinUnique.Bridge.Alt57Model
  CFSG.Quasithin.Vol2.KGNat CFSG.ASVolI.ChIJK in
open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ClassicalInvolution.ModelFacts.OddCover CFSG.QuasithinUnique.Bridge.Alt57Model
  CFSG.Quasithin.Vol2.KGNat CFSG.ASVolI.ChIJK in
namespace burnsideI23x_SD

section SClause

variable {F : Type} [Field F] [Finite F] [CharP F 2] {N : Type} [AddCommGroup N] [Module F N]
  (S : burnsideI23x_SD F N) {U : Type} [CommGroup U]


end SClause

end burnsideI23x_SD
namespace burnsideI23x_SD

section OrthCommon

variable {F : Type} [Field F] [Finite F] [CharP F 2] {N : Type} [AddCommGroup N] [Module F N]
  {S : burnsideI23x_SD F N} {U : Type} [CommGroup U]


end OrthCommon

end burnsideI23x_SD
open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.JonesParshall CFSG.Quasithin.MS93
  CFSG.ASVolI.ChIJK CFSG.Quasithin.Vol2.KGNat CFSG.Quasithin.Vol2.Ch11.SecA CFSG.Quasithin.Explicit
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.ClassicalInvolution.ModelFacts.OddCover in
open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChIJK CFSG.Quasithin.Vol2.KGNat
  CFSG.Assembly.LowTwoRank CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.Explicit
  CFSG.Quasithin.JonesParshall CFSG.ClassicalInvolution.ModelFacts.OddCover
  CFSG.QuasithinUnique.Bridge.Alt57Model in

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in


open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
@[expose] def burnsideI23x_emb {F : Type} [Field F] (c : ZMod 2 ≃+* F) (w : Ix3 → ZMod 2) :
    Ix3 → F := fun i => c (w i)


open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
@[expose] def burnsideI23x_rx0 {R : Type} [CommRing R] (w : Ix3 → R) : Ix3 → R :=
  q6 (w (.inl 0) + w (.inr 0)) (w (.inl 1)) (w (.inl 2)) (w (.inr 0))
    (w (.inr 1) + w (.inl 2)) (w (.inr 2) + w (.inl 1))

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
@[expose] def burnsideI23x_rx1 {R : Type} [CommRing R] (w : Ix3 → R) : Ix3 → R :=
  q6 (w (.inl 0)) (w (.inl 1) + w (.inr 1)) (w (.inl 2)) (w (.inr 0) + w (.inl 2))
    (w (.inr 1)) (w (.inr 2) + w (.inl 0))

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
@[expose] def burnsideI23x_rx2 {R : Type} [CommRing R] (w : Ix3 → R) : Ix3 → R :=
  q6 (w (.inl 0)) (w (.inl 1)) (w (.inl 2) + w (.inr 2)) (w (.inr 0) + w (.inl 1))
    (w (.inr 1) + w (.inl 0)) (w (.inr 2))

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
@[expose] def burnsideI23x_ry0 {R : Type} [CommRing R] (w : Ix3 → R) : Ix3 → R :=
  q6 (w (.inl 0)) (w (.inl 1) + w (.inr 2)) (w (.inl 2) + w (.inr 1)) (w (.inr 0) + w (.inl 0))
    (w (.inr 1)) (w (.inr 2))

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
@[expose] def burnsideI23x_ry1 {R : Type} [CommRing R] (w : Ix3 → R) : Ix3 → R :=
  q6 (w (.inl 0) + w (.inr 2)) (w (.inl 1)) (w (.inl 2) + w (.inr 0)) (w (.inr 0))
    (w (.inr 1) + w (.inl 1)) (w (.inr 2))

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
@[expose] def burnsideI23x_ry2 {R : Type} [CommRing R] (w : Ix3 → R) : Ix3 → R :=
  q6 (w (.inl 0) + w (.inr 1)) (w (.inl 1) + w (.inr 0)) (w (.inl 2)) (w (.inr 0))
    (w (.inr 1)) (w (.inr 2) + w (.inl 2))

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
theorem burnsideI23x_g2Act_rx0 {F : Type} [Field F] [CharP F 2] (w : Ix3 → F) :
    g2Act (g2X ![1, 0, 0]) w = burnsideI23x_rx0 w := by
  rw [g2Act_x0]; rfl

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
theorem burnsideI23x_g2Act_rx1 {F : Type} [Field F] [CharP F 2] (w : Ix3 → F) :
    g2Act (g2X ![0, 1, 0]) w = burnsideI23x_rx1 w := by
  rw [q6_eta w, g2Act_x1q]
  simp [burnsideI23x_rx1, q6]

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
theorem burnsideI23x_g2Act_rx2 {F : Type} [Field F] [CharP F 2] (w : Ix3 → F) :
    g2Act (g2X ![0, 0, 1]) w = burnsideI23x_rx2 w := by
  rw [q6_eta w, g2Act_x2q]
  simp [burnsideI23x_rx2, q6]

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
theorem burnsideI23x_g2Act_ry0 {F : Type} [Field F] [CharP F 2] (w : Ix3 → F) :
    g2Act (g2Y ![1, 0, 0]) w = burnsideI23x_ry0 w := by
  rw [q6_eta w, g2Act_y0q]
  simp [burnsideI23x_ry0, q6]

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
theorem burnsideI23x_g2Act_ry1 {F : Type} [Field F] [CharP F 2] (w : Ix3 → F) :
    g2Act (g2Y ![0, 1, 0]) w = burnsideI23x_ry1 w := by
  rw [q6_eta w, g2Act_y1q]
  simp [burnsideI23x_ry1, q6]

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
theorem burnsideI23x_g2Act_ry2 {F : Type} [Field F] [CharP F 2] (w : Ix3 → F) :
    g2Act (g2Y ![0, 0, 1]) w = burnsideI23x_ry2 w := by
  rw [q6_eta w, g2Act_y2q]
  simp [burnsideI23x_ry2, q6]

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
theorem burnsideI23x_emb_rx0 {F : Type} [Field F] (c : ZMod 2 ≃+* F) (w : Ix3 → ZMod 2) :
    burnsideI23x_rx0 (burnsideI23x_emb c w) = burnsideI23x_emb c (burnsideI23x_rx0 w) := by
  funext i; rcases i with i | i <;> fin_cases i <;> simp [burnsideI23x_rx0, burnsideI23x_emb, q6]

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
theorem burnsideI23x_emb_rx1 {F : Type} [Field F] (c : ZMod 2 ≃+* F) (w : Ix3 → ZMod 2) :
    burnsideI23x_rx1 (burnsideI23x_emb c w) = burnsideI23x_emb c (burnsideI23x_rx1 w) := by
  funext i; rcases i with i | i <;> fin_cases i <;> simp [burnsideI23x_rx1, burnsideI23x_emb, q6]

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
theorem burnsideI23x_emb_rx2 {F : Type} [Field F] (c : ZMod 2 ≃+* F) (w : Ix3 → ZMod 2) :
    burnsideI23x_rx2 (burnsideI23x_emb c w) = burnsideI23x_emb c (burnsideI23x_rx2 w) := by
  funext i; rcases i with i | i <;> fin_cases i <;> simp [burnsideI23x_rx2, burnsideI23x_emb, q6]

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
theorem burnsideI23x_emb_ry0 {F : Type} [Field F] (c : ZMod 2 ≃+* F) (w : Ix3 → ZMod 2) :
    burnsideI23x_ry0 (burnsideI23x_emb c w) = burnsideI23x_emb c (burnsideI23x_ry0 w) := by
  funext i; rcases i with i | i <;> fin_cases i <;> simp [burnsideI23x_ry0, burnsideI23x_emb, q6]

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
theorem burnsideI23x_emb_ry1 {F : Type} [Field F] (c : ZMod 2 ≃+* F) (w : Ix3 → ZMod 2) :
    burnsideI23x_ry1 (burnsideI23x_emb c w) = burnsideI23x_emb c (burnsideI23x_ry1 w) := by
  funext i; rcases i with i | i <;> fin_cases i <;> simp [burnsideI23x_ry1, burnsideI23x_emb, q6]

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
theorem burnsideI23x_emb_ry2 {F : Type} [Field F] (c : ZMod 2 ≃+* F) (w : Ix3 → ZMod 2) :
    burnsideI23x_ry2 (burnsideI23x_emb c w) = burnsideI23x_emb c (burnsideI23x_ry2 w) := by
  funext i; rcases i with i | i <;> fin_cases i <;> simp [burnsideI23x_ry2, burnsideI23x_emb, q6]

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.ASVolI.ChIJK in

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
structure burnsideI23x_ZE {F : Type} [Field F] [CharP F 2] (c : ZMod 2 ≃+* F) where
  g : ↥(cayleyGroup F)
  f : (Ix3 → ZMod 2) → (Ix3 → ZMod 2)
  hf : ∀ w, g2Act g (burnsideI23x_emb c w) = burnsideI23x_emb c (f w)

namespace burnsideI23x_ZE

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
@[expose] def mul {F : Type} [Field F] [CharP F 2] {c : ZMod 2 ≃+* F} (A B : burnsideI23x_ZE c) :
    burnsideI23x_ZE c where
  g := A.g * B.g
  f := fun w => A.f (B.f w)
  hf := fun w => by rw [g2Act_mul_apply, B.hf, A.hf]

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in

end burnsideI23x_ZE
namespace burnsideI23x_ZE

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
@[expose] noncomputable def x0 {F : Type} [Field F] [CharP F 2] (c : ZMod 2 ≃+* F) : burnsideI23x_ZE c where
  g := g2X (![1, 0, 0] : Fin 3 → F)
  f := burnsideI23x_rx0
  hf := fun w => by rw [burnsideI23x_g2Act_rx0, burnsideI23x_emb_rx0]

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
@[expose] noncomputable def x1 {F : Type} [Field F] [CharP F 2] (c : ZMod 2 ≃+* F) : burnsideI23x_ZE c where
  g := g2X (![0, 1, 0] : Fin 3 → F)
  f := burnsideI23x_rx1
  hf := fun w => by rw [burnsideI23x_g2Act_rx1, burnsideI23x_emb_rx1]

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
@[expose] noncomputable def x2 {F : Type} [Field F] [CharP F 2] (c : ZMod 2 ≃+* F) : burnsideI23x_ZE c where
  g := g2X (![0, 0, 1] : Fin 3 → F)
  f := burnsideI23x_rx2
  hf := fun w => by rw [burnsideI23x_g2Act_rx2, burnsideI23x_emb_rx2]

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
@[expose] noncomputable def y0 {F : Type} [Field F] [CharP F 2] (c : ZMod 2 ≃+* F) : burnsideI23x_ZE c where
  g := g2Y (![1, 0, 0] : Fin 3 → F)
  f := burnsideI23x_ry0
  hf := fun w => by rw [burnsideI23x_g2Act_ry0, burnsideI23x_emb_ry0]

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
@[expose] noncomputable def y1 {F : Type} [Field F] [CharP F 2] (c : ZMod 2 ≃+* F) : burnsideI23x_ZE c where
  g := g2Y (![0, 1, 0] : Fin 3 → F)
  f := burnsideI23x_ry1
  hf := fun w => by rw [burnsideI23x_g2Act_ry1, burnsideI23x_emb_ry1]

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
@[expose] noncomputable def y2 {F : Type} [Field F] [CharP F 2] (c : ZMod 2 ≃+* F) : burnsideI23x_ZE c where
  g := g2Y (![0, 0, 1] : Fin 3 → F)
  f := burnsideI23x_ry2
  hf := fun w => by rw [burnsideI23x_g2Act_ry2, burnsideI23x_emb_ry2]

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in

end burnsideI23x_ZE
open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK CFSG.ClassicalInvolution.ModelFacts.OddCover in

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in

namespace burnsideI23x_ZE

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK CFSG.ClassicalInvolution.ModelFacts.OddCover in

end burnsideI23x_ZE
namespace burnsideI23x_ZE

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in

end burnsideI23x_ZE

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK CFSG.Quasithin.Vol2.KGNat CFSG.Quasithin.Vol2.Ch11.SecA in

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK CFSG.Quasithin.Vol2.KGNat CFSG.Quasithin.Vol2.Ch11.SecA in

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK CFSG.ClassicalInvolution.ModelFacts.OddCover in

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK CFSG.ClassicalInvolution.ModelFacts.OddCover in

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK CFSG.Quasithin.Vol2.KGNat CFSG.Quasithin.Vol2.Ch11.SecA CFSG.QuasithinUnique in

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK CFSG.Quasithin.Vol2.KGNat CFSG.Quasithin.Vol2.Ch11.SecA in

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK CFSG.Quasithin.Vol2.KGNat CFSG.Quasithin.Vol2.Ch11.SecA in

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK CFSG.Quasithin.Vol2.KGNat CFSG.Quasithin.Vol2.Ch11.SecA in

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.Quasithin.MS93 CFSG.ASVolI.ChIJK in

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.JonesParshall CFSG.Quasithin.MS93
  CFSG.ASVolI.ChIJK CFSG.Quasithin.Vol2.KGNat CFSG.Quasithin.Vol2.Ch11.SecA CFSG.Quasithin.Explicit
  CFSG.Quasithin.Vol2.Ch11.G2Q8 in

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK CFSG.ClassicalInvolution.ModelFacts.OddCover in

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK CFSG.ClassicalInvolution.ModelFacts.OddCover
  CFSG.QuasithinUnique.Bridge.Alt57Model in

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK CFSG.ClassicalInvolution.ModelFacts.OddCover in

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK CFSG.ClassicalInvolution.ModelFacts.OddCover in

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK CFSG.ClassicalInvolution.ModelFacts.OddCover in

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK CFSG.ClassicalInvolution.ModelFacts.OddCover in

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK CFSG.ClassicalInvolution.ModelFacts.OddCover in

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK CFSG.ClassicalInvolution.ModelFacts.OddCover in

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK CFSG.ClassicalInvolution.ModelFacts.OddCover in

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ClassicalInvolution.ModelFacts.OddCover CFSG.QuasithinUnique.Bridge.Alt57Model
  CFSG.Quasithin.Vol2.KGNat CFSG.ASVolI.ChIJK in

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ClassicalInvolution.ModelFacts.OddCover CFSG.QuasithinUnique.Bridge.Alt57Model
  CFSG.Quasithin.Vol2.KGNat CFSG.ASVolI.ChIJK in

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.JonesParshall CFSG.Quasithin.MS93
  CFSG.ASVolI.ChIJK CFSG.Quasithin.Vol2.KGNat CFSG.Quasithin.Vol2.Ch11.SecA CFSG.Quasithin.Explicit
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.ClassicalInvolution.ModelFacts.OddCover in
open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChIJK CFSG.Quasithin.Vol2.KGNat
  CFSG.Assembly.LowTwoRank CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.Explicit
  CFSG.Quasithin.JonesParshall CFSG.ClassicalInvolution.ModelFacts.OddCover
  CFSG.QuasithinUnique.Bridge.Alt57Model in


open CFSG.Quasithin CFSG.Quasithin.B5FinSp CFSG.ASVolI.ChIJK CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification.PresentationLocal Matrix in

open CFSG.Quasithin CFSG.Quasithin.B5FinSp CFSG.ASVolI.ChIJK CFSG.Assembly.LowTwoRank in
theorem burnsideI23x_theta_mem_comm {F : Type} [Field F] (c : ZMod 2 ≃+* F)
    (σ : Equiv.Perm (Fin 6)) (hσ : σ ∈ alternatingGroup (Fin 6)) :
    (((B5FinSp.theta c σ : ↥(StatedSp 2 F)) : GL (Fin 2 ⊕ Fin 2) F)) ∈
      ⁅StatedSp 2 F, StatedSp 2 F⁆ := by
  have hcomm : σ ∈ commutator (Equiv.Perm (Fin 6)) := by
    rw [alternatingGroup.commutator_perm_eq (by simp)]
    exact hσ
  clear hσ
  rw [commutator_def, Subgroup.commutator_def] at hcomm
  induction hcomm using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, -, b, -, rfl⟩ := hx
    have h1 := Subgroup.commutator_mem_commutator
      (H₁ := StatedSp 2 F) (H₂ := StatedSp 2 F) (B5FinSp.theta c a).2 (B5FinSp.theta c b).2
    rw [map_commutatorElement]
    exact h1
  | one => rw [map_one]; exact Subgroup.one_mem _
  | mul x y _ _ hx hy => rw [map_mul]; exact Subgroup.mul_mem _ hx hy
  | inv x _ hx => rw [map_inv]; exact Subgroup.inv_mem _ hx

open CFSG.Quasithin CFSG.Quasithin.B5FinSp CFSG.ASVolI.ChIJK CFSG.Assembly.LowTwoRank in
open scoped commutatorElement in
theorem burnsideI23x_comm_mem_theta {F : Type} [Field F] (c : ZMod 2 ≃+* F)
    (γ : GL (Fin 2 ⊕ Fin 2) F) (hγ : γ ∈ ⁅StatedSp 2 F, StatedSp 2 F⁆) :
    ∃ σ : Equiv.Perm (Fin 6), σ ∈ alternatingGroup (Fin 6) ∧
      ((B5FinSp.theta c σ : ↥(StatedSp 2 F)) : GL (Fin 2 ⊕ Fin 2) F) = γ := by
  rw [Subgroup.commutator_def] at hγ
  induction hγ using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    obtain ⟨s, hs⟩ := (B5FinSp.theta c).surjective ⟨a, ha⟩
    obtain ⟨t, ht⟩ := (B5FinSp.theta c).surjective ⟨b, hb⟩
    refine ⟨⁅s, t⁆, ?_, ?_⟩
    · rw [← alternatingGroup.commutator_perm_eq (by simp : 5 ≤ Nat.card (Fin 6)), commutator_def,
        Subgroup.commutator_def]
      exact Subgroup.subset_closure ⟨s, Subgroup.mem_top _, t, Subgroup.mem_top _, rfl⟩
    · rw [map_commutatorElement, hs, ht]
      rfl
  | one => exact ⟨1, Subgroup.one_mem _, by rw [map_one]; rfl⟩
  | mul x y _ _ hx hy =>
    obtain ⟨s, hs, rfl⟩ := hx
    obtain ⟨t, ht, rfl⟩ := hy
    exact ⟨s * t, Subgroup.mul_mem _ hs ht, by rw [map_mul]; rfl⟩
  | inv x _ hx =>
    obtain ⟨s, hs, rfl⟩ := hx
    exact ⟨s⁻¹, Subgroup.inv_mem _ hs, by rw [map_inv]; rfl⟩

open CFSG.Quasithin CFSG.Quasithin.B5FinSp CFSG.ASVolI.ChIJK CFSG.Assembly.LowTwoRank in
@[expose] noncomputable def burnsideI23x_a6ι {F : Type} [Field F] (c : ZMod 2 ≃+* F) :
    ↥(alternatingGroup (Fin 6)) →* ↥⁅StatedSp 2 F, StatedSp 2 F⁆ where
  toFun σ := ⟨((B5FinSp.theta c (σ : Equiv.Perm (Fin 6)) : ↥(StatedSp 2 F)) :
    GL (Fin 2 ⊕ Fin 2) F), burnsideI23x_theta_mem_comm c σ σ.2⟩
  map_one' := by
    apply Subtype.ext
    show ((B5FinSp.theta c (1 : Equiv.Perm (Fin 6)) : ↥(StatedSp 2 F)) : GL (Fin 2 ⊕ Fin 2) F) = 1
    rw [map_one]
    rfl
  map_mul' σ τ := by
    apply Subtype.ext
    show ((B5FinSp.theta c ((σ : Equiv.Perm (Fin 6)) * τ) : ↥(StatedSp 2 F)) :
      GL (Fin 2 ⊕ Fin 2) F) = _
    rw [map_mul]
    rfl

open CFSG.Quasithin CFSG.Quasithin.B5FinSp CFSG.ASVolI.ChIJK CFSG.Assembly.LowTwoRank in
theorem burnsideI23x_a6ι_bijective {F : Type} [Field F] (c : ZMod 2 ≃+* F) :
    Function.Bijective (burnsideI23x_a6ι c) := by
  constructor
  · intro σ τ h
    have h1 := congrArg (fun g : ↥⁅StatedSp 2 F, StatedSp 2 F⁆ => (g : GL (Fin 2 ⊕ Fin 2) F)) h
    have h2 : (B5FinSp.theta c (σ : Equiv.Perm (Fin 6))) = B5FinSp.theta c (τ : Equiv.Perm (Fin 6)) :=
      Subtype.ext h1
    exact Subtype.ext ((B5FinSp.theta c).injective h2)
  · intro γ
    obtain ⟨σ, hσ, hθ⟩ := burnsideI23x_comm_mem_theta c γ.1 γ.2
    exact ⟨⟨σ, hσ⟩, Subtype.ext hθ⟩

open CFSG.Quasithin CFSG.Quasithin.B5FinSp CFSG.ASVolI.ChIJK CFSG.Assembly.LowTwoRank
  CFSG.Quasithin.Vol2.KGNat in


open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.MS93 CFSG.ASVolI.ChIJK
  CFSG.Quasithin.Vol2.KGNat CFSG.Assembly.LowTwoRank CFSG.Quasithin.Explicit in


open CFSG.Quasithin CFSG.Quasithin.B5FinSp CFSG.ASVolI.ChIJK CFSG.Assembly.LowTwoRank
  CFSG.Quasithin.Vol2.KGNat CFSG.Quasithin.Vol2.Ch11.SecA in


open CFSG.Quasithin CFSG.Quasithin.B5FinSp CFSG.ASVolI.ChIJK CFSG.Assembly.LowTwoRank
  CFSG.Quasithin.Vol2.KGNat CFSG.Quasithin.Vol2.Ch11.SecA in


open CFSG.Quasithin CFSG.Quasithin.B5FinSp CFSG.ASVolI.ChIJK CFSG.Assembly.LowTwoRank
  CFSG.Quasithin.Vol2.KGNat CFSG.Quasithin.Vol2.Ch11.SecA in

open CFSG.Quasithin CFSG.Quasithin.B5FinSp CFSG.ASVolI.ChIJK CFSG.Assembly.LowTwoRank
  CFSG.Quasithin.Vol2.KGNat CFSG.Quasithin.Vol2.Ch11.SecA in

open CFSG.Quasithin CFSG.Quasithin.B5FinSp CFSG.ASVolI.ChIJK CFSG.Assembly.LowTwoRank
  CFSG.Quasithin.Vol2.KGNat CFSG.Quasithin.Vol2.Ch11.SecA in


open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.JonesParshall CFSG.Quasithin.MS93
  CFSG.ASVolI.ChIJK CFSG.Quasithin.Vol2.KGNat CFSG.Quasithin.Vol2.Ch11.SecA
  CFSG.Assembly.LowTwoRank in


open CFSG.Quasithin CFSG.Quasithin.B5FinSp CFSG.ASVolI.ChIJK CFSG.Assembly.LowTwoRank
  CFSG.Quasithin.Vol2.KGNat in


open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.MS93 CFSG.ASVolI.ChIJK
  CFSG.Assembly.LowTwoRank in

open CFSG.Quasithin CFSG.Quasithin.B5FinSp CFSG.ASVolI.ChIJK CFSG.Assembly.LowTwoRank
  CFSG.Quasithin.MS93 in

open CFSG.Quasithin CFSG.Quasithin.B5FinSp CFSG.ASVolI.ChIJK CFSG.Assembly.LowTwoRank
  CFSG.Quasithin.MS93 in

open CFSG.Quasithin CFSG.Quasithin.B5FinSp CFSG.ASVolI.ChIJK CFSG.Assembly.LowTwoRank
  CFSG.Quasithin.MS93 in

open CFSG.Quasithin CFSG.Quasithin.B5FinSp CFSG.ASVolI.ChIJK CFSG.Assembly.LowTwoRank
  CFSG.Quasithin.MS93 in

open CFSG.Quasithin CFSG.Quasithin.B5FinSp CFSG.ASVolI.ChIJK CFSG.Assembly.LowTwoRank
  CFSG.Quasithin.MS93 in

open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.MS93 CFSG.ASVolI.ChIJK
  CFSG.Assembly.LowTwoRank CFSG.Quasithin.Explicit in

open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.MS93 CFSG.ASVolI.ChIJK
  CFSG.Assembly.LowTwoRank CFSG.Quasithin.Explicit in

open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.MS93 CFSG.ASVolI.ChIJK
  CFSG.Assembly.LowTwoRank CFSG.Quasithin.Explicit in

open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.MS93 CFSG.ASVolI.ChIJK
  CFSG.Assembly.LowTwoRank CFSG.Quasithin.Explicit in

open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.MS93 CFSG.ASVolI.ChIJK
  CFSG.Assembly.LowTwoRank CFSG.Quasithin.Explicit in

open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.MS93 CFSG.ASVolI.ChIJK
  CFSG.Assembly.LowTwoRank CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat in


open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.JonesParshall CFSG.Quasithin.MS93
  CFSG.ASVolI.ChIJK CFSG.Quasithin.Vol2.KGNat CFSG.Quasithin.Vol2.Ch11.SecA
  CFSG.Assembly.LowTwoRank in

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChIJK CFSG.Quasithin.Vol2.KGNat
  CFSG.Assembly.LowTwoRank in


open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.H13.VolI
  CFSG.Quasithin.Vol2.KGNat in


open CFSG.Quasithin CFSG.ASVolI.ChIJK CFSG.Quasithin.Vol2.KGNat CFSG.Quasithin.JonesParshall
  CFSG.Quasithin.H13.VolI in


open CFSG.Quasithin CFSG.Quasithin.Vol2.KGNat CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.Quasithin.JonesParshall in

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChIJK CFSG.Quasithin.Vol2.KGNat
  CFSG.Assembly.LowTwoRank in


section


end

section


end


end CFSG.ASVolI
