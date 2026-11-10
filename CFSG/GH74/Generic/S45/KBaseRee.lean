module

public import CFSG.GH74.Generic.S45.KBaseGen
public import CFSG.Walter.Ree.Model.JTHyp
public import CFSG.LieType.Ree.SmallReeOuterThreeKernel
public import CFSG.GH74.Generic.Assembly
public import CFSG.GH74.Generic.FrontEnd
public import CFSG.GH74.Generic.OuterRank
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGeneralLinear
public import CFSG.Sporadic.Ly.Simple
public import CFSG.LocalAnalysis.QuasithinUnique.Setting
public import CFSG.Sporadic.LyBase
public import CFSG.Sporadic.Ly.CertificateBase
public import CFSG.Sporadic.McL
public import CFSG.Sporadic.Ly.ActionBase
public import CFSG.Sporadic.HN.LevelChainSpec
public import CFSG.Sporadic.Bridge.TableSurj
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.Sporadic.Ly.OrbitSpec
public import CFSG.Sporadic.Schreier.LyChain11
public import CFSG.Sporadic.Ly.FaithSpec
public import CFSG.Sporadic.Presentation.Ly
public import CFSG.Fischer.Uniq.CompTau
public import CFSG.Sporadic.Presentation.Common
public import CFSG.Certificates.CosetTableShort
public import CFSG.Sporadic.HN.ConjSimple
public import CFSG.Sporadic.Bridge.LyData
public import Lean.Data.Json

public section

namespace CFSG.GH74.Generic.S45

open CFSG CFSG.Blueprint CFSG.LieType.Ree Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

theorem autTwoInner_of_odd_outer {G : Type} [Group G] (h : Odd (Nat.card (Outer G))) :
    AutTwoInner G := by
  intro α hα
  obtain ⟨k, hk⟩ := hα ⟨α, mem_zpowers α⟩
  have hαk : α ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  let q : Outer G := QuotientGroup.mk α
  have hq : q ^ (2 ^ k) = 1 := by
    show (QuotientGroup.mk α : Outer G) ^ (2 ^ k) = 1
    rw [← QuotientGroup.mk_pow, hαk, QuotientGroup.mk_one]
  have h1 : orderOf q ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hq
  have h2 : orderOf q ∣ Nat.card (Outer G) := orderOf_dvd_natCard q
  have hcop : Nat.Coprime (2 ^ k) (Nat.card (Outer G)) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.2 h)
  have h3 : orderOf q = 1 := Nat.Coprime.eq_one_of_dvd (hcop.coprime_dvd_left h1) h2
  exact (QuotientGroup.eq_one_iff α).1 (orderOf_eq_one_iff.1 h3)

theorem kBase_reeGamma
    (a : ℕ) (ha : 1 ≤ a) (K : Type) [Field K] [Finite K]
    [CharP K ReeTag.G2.prime] (hK : Nat.card K = 3 ^ (2 * a + 1))
    (hs : IsSimpleGroup (ReeTag.G2.reeGamma K a)) : KBase (ReeTag.G2.reeGamma K a) := by
  obtain ⟨h, hp3, -, -⟩ := CFSG.Walter.Ree.Model.small_Ree_jtHyp a ha K hK
  have hp : h.p ≠ 2 := by rw [hp3]; norm_num
  obtain ⟨-, -, -, -, hodd, -⟩ := small_Ree_outer_three_kernel_field_complement a ha K hK
  refine kBase_of_data hs (autTwoInner_of_odd_outer hodd) h.t h.orderOf_t
    (fun x hx => h.exists_conj_eq_t hp hx) ?_
  intro S htS
  refine ⟨h.card_sylow hp S htS, fun x hx => h.mul_self_of_mem_sylow hp S htS hx,
    h.centralizer_sylow hp S htS, ?_⟩
  have h1 := h.index_sylow_normalizer hp S htS
  have h2 := Subgroup.card_mul_index
    ((S : Subgroup (ReeTag.G2.reeGamma K a)).subgroupOf
      (normalizer ((S : Subgroup (ReeTag.G2.reeGamma K a)) : Set (ReeTag.G2.reeGamma K a))))
  have h3 : Nat.card ↥((S : Subgroup (ReeTag.G2.reeGamma K a)).subgroupOf
      (normalizer ((S : Subgroup (ReeTag.G2.reeGamma K a)) : Set (ReeTag.G2.reeGamma K a)))) = 8 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe Subgroup.le_normalizer).toEquiv]
    exact h.card_sylow hp S htS
  rw [h1, h3] at h2
  omega

theorem kBase_of_reeModel
    {K : Type} [Group K] [Finite K] {f : ℕ}
    (hm : ReeTitsModel K .twistedG2 3 f) : KBase K := by
  have hsimple : IsSimpleGroup K := (CFSG.LieType.Simplicity.fam_2g2_simplicity K 3 f hm).2
  obtain ⟨-, -, -, ⟨a, ha, hfa⟩, hiso⟩ := small_Ree_model_Schreier K 3 f hm
  obtain ⟨-, a', hfa', K', _, _, hK', hw⟩ := hm
  have ha' : a' = a := by omega
  subst ha'
  have : CharP K' ReeTag.G2.prime :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_three
      (by omega) hK'
  obtain ⟨E⟩ := hiso a' K' hfa hK' hw
  have hK'' : Nat.card K' = 3 ^ (2 * a' + 1) := by rw [hK', hfa]
  have hsΓ : IsSimpleGroup (ReeTag.G2.reeGamma K' a') := E.symm.isSimpleGroup
  exact KBase.of_mulEquiv E.symm (kBase_reeGamma a' ha K' hK'' hsΓ)

end CFSG.GH74.Generic.S45
