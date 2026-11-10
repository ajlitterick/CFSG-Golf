module

public import CFSG.RankThree.PartTwo.Sec16.Item166Res2ProofTwoOut
import CFSG.RankThree.PartTwo.Sec16.Item16Tail
import CFSG.RankThree.PartTwo.Sec14.Item1411StepsProofTools
import CFSG.RankThree.PartTwo.Sec16.Item16Tail22
public import CFSG.Certificates.CentralKernel
public import CFSG.Certificates.CosetTableWalkC
public import CFSG.Certificates.FusionF2
public import CFSG.Certificates.LiftedSchreierData
public import CFSG.Certificates.WordSubgroupHom
public import CFSG.LieType.Chevalley.EvenRootCommutatorF4
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LieType.Universal.Spin.Roots
public import CFSG.LieType.Universal.SpinOmega
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianIsometry
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
public import CFSG.LocalAnalysis.SectionRank.Sporadic.TitsGen
public import CFSG.Monster.AxisCount.HSIdentBaby
public import CFSG.Monster.AxisCount.HSIdentRec0
public import CFSG.Monster.AxisCount.HSIdentRec1
public import CFSG.Monster.AxisCount.HSIdentRec2
public import CFSG.Monster.AxisCount.HSIdentRec3
public import CFSG.Monster.AxisCount.HSIdentRec4
public import CFSG.Monster.AxisCount.HSIdentRec5
public import CFSG.Monster.AxisCount.HSIdentRec6
public import CFSG.Monster.AxisCount.HSIdentRec7
public import CFSG.Monster.AxisCount.HSIdentSmall
public import CFSG.RankThree.Asc83Table.PermTables
public import CFSG.RankThree.PartTwo.Sec11.Data
public import CFSG.RankThree.PartTwo.Sec14.Item1411HJ
public import CFSG.RankThree.PartTwo.Sec14.Item148StepCases
public import CFSG.RankThree.PartTwo.Sec14.Item148StepOne
public import CFSG.RankThree.PartTwo.Sec15.Item157
public import CFSG.RankThree.PartTwo.Sec16.Item164Proof
public import CFSG.RankThree.PartTwo.Sec16.Item165StepsProofE
public import CFSG.RankThree.PartTwo.Sec16.Item166ResProofTwoPow
public import CFSG.RankThree.PartTwo.Sec17.Item1724Two
public import CFSG.RankThree.PartTwo.Sec17.Item17Q0Proof
public import CFSG.RankThree.PartTwo.Sec17.RouteProvers
public import CFSG.RankThree.PartTwo.Sec17.RouteProvers142
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.RankThree.PartTwo.Sec6.Statements
public import CFSG.RankThree.PartTwo.Toolkit.M12Local
public import CFSG.RankThree.S4Free.SuzukiEight
public import CFSG.Sporadic.Bridge.Catalogue
public import CFSG.Sporadic.Presentation.Co2Base
public import CFSG.Sporadic.Presentation.Co2Cover
public import CFSG.Sporadic.Presentation.Co2Fusion
public import CFSG.Sporadic.Presentation.Co2FusionInputs
public import CFSG.Sporadic.Presentation.McLExactData
public import CFSG.Sporadic.Presentation.McLExactInputs
public import CFSG.Sporadic.Schreier.RuLOdd
public import CFSG.Sporadic.Schreier.RuZClass
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.FinalTheorem
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import CFSG.YGroups.DCE.B433Check
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement
public import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Sec16
  CFSG.RankThree.PartTwo.Late CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement

namespace Proof168Res8Comm

section Cyclic

variable {H : Type*} [Group H]

omit [Group H] in
theorem mul_comm_of_isCyclic [Group H] {P : Subgroup H} (hP : IsCyclic P) {x y : H} (hx : x ∈ P)
    (hy : y ∈ P) : x * y = y * x := by
  have hPc : IsMulCommutative P := IsCyclic.isMulCommutative
  exact congrArg Subtype.val (hPc.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)

theorem zpowers_eq_of_orderOf [Finite H] {P : Subgroup H} (hP : IsCyclic P) {c x : H} (hcP : c ∈ P)
    (hxP : x ∈ P) (hc : orderOf c = 3) (hx : orderOf x = 3) :
    Subgroup.zpowers x = Subgroup.zpowers c := by
  have key : Subgroup.zpowers (⟨x, hxP⟩ : P) = Subgroup.zpowers (⟨c, hcP⟩ : P) := by
    rw [IsCyclic.subgroup_eq_iff_card_eq, Nat.card_zpowers, Nat.card_zpowers,
      Subgroup.orderOf_mk, Subgroup.orderOf_mk, hc, hx]
  have h1 := congrArg (Subgroup.map P.subtype) key
  rwa [MonoidHom.map_zpowers, MonoidHom.map_zpowers] at h1

theorem mem_of_le_of_ne_bot [Finite H] {P Q : Subgroup H} (hP : IsCyclic P) (hP3 : IsPGroup 3 P)
    {c : H} (hcP : c ∈ P) (hc : orderOf c = 3) (hQP : Q ≤ P) (hQ : Q ≠ ⊥) : c ∈ Q := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hQ3 : IsPGroup 3 Q := hP3.to_le hQP
  have hdvd : 3 ∣ Nat.card Q := by
    obtain ⟨k, hk⟩ := hQ3.exists_card_eq
    rcases k with _ | k
    · exact absurd (Subgroup.eq_bot_of_card_eq Q (by simpa using hk)) hQ
    · rw [hk, pow_succ]
      exact dvd_mul_left 3 _
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := Q) 3 hdvd
  have hyo : orderOf (y : H) = 3 := by rwa [Subgroup.orderOf_coe]
  have heq := zpowers_eq_of_orderOf hP hcP (hQP y.2) hc hyo
  have : Subgroup.zpowers (y : H) ≤ Q := Subgroup.zpowers_le.mpr y.2
  exact this (heq ▸ Subgroup.mem_zpowers c)

theorem mem_centralizer_of_coprime [Finite H] {P : Subgroup H} (hP : IsCyclic P)
    (hP3 : IsPGroup 3 P) {c h : H} (hcP : c ∈ P) (hc : orderOf c = 3)
    (hhP : h ∈ Subgroup.normalizer (P : Set H)) (hh3 : Nat.Coprime (orderOf h) 3)
    (hch : h * c * h⁻¹ = c) : h ∈ Subgroup.centralizer (P : Set H) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set B := Subgroup.zpowers h with hB
  have hBP : B ≤ Subgroup.normalizer (P : Set H) := Subgroup.zpowers_le.mpr hhP
  have hcop : Nat.Coprime (Nat.card B) (Nat.card P) := by
    obtain ⟨k, hk⟩ := hP3.exists_card_eq
    rw [Nat.card_zpowers, hk]
    exact Nat.Coprime.pow_right k hh3
  have hfit := CFSG.RankThree.Coprime.commutator_inf_centralizer_eq_bot
    (fun x hx y hy => mul_comm_of_isCyclic hP hx hy) hBP hcop
  have hcB : c ∈ Subgroup.centralizer (B : Set H) := by
    have hhc : h ∈ Subgroup.centralizer ({c} : Set H) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (by
        calc h * c = h * c * h⁻¹ * h := by group
          _ = c * h := by rw [hch])
    have hBc : B ≤ Subgroup.centralizer ({c} : Set H) := Subgroup.zpowers_le.mpr hhc
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact Subgroup.mem_centralizer_singleton_iff.mp (hBc hb)
  by_contra hnot
  have hne : ⁅B, P⁆ ≠ ⊥ := by
    intro h0
    exact hnot (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h0 (Subgroup.mem_zpowers h))
  have hle : ⁅B, P⁆ ≤ P := Subgroup.le_normalizer_iff_commutator_le_right.mp hBP
  have hc' := mem_of_le_of_ne_bot hP hP3 hcP hc hle hne
  have hcbot : c ∈ ⁅B, P⁆ ⊓ Subgroup.centralizer (B : Set H) := ⟨hc', hcB⟩
  rw [hfit, Subgroup.mem_bot] at hcbot
  rw [hcbot, orderOf_one] at hc
  omega

theorem mem_of_mem_normalizer (P : Sylow 3 H) {b : H} (hb : b ∈ Subgroup.normalizer (P : Set H))
    {e : ℕ} (hbe : orderOf b = 3 ^ e) : b ∈ P := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hb3 : IsPGroup 3 (Subgroup.zpowers b) := IsPGroup.of_card (n := e) (by
    rw [Nat.card_zpowers, hbe])
  have hsup := P.is_maximal' (P.isPGroup'.to_sup_of_normal_left' hb3
    (Subgroup.zpowers_le.mpr hb)) le_sup_left
  have : b ∈ (P : Subgroup H) ⊔ Subgroup.zpowers b :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers b)
  rwa [hsup] at this

theorem eq_or_eq_inv_of_mem_zpowers {c x : H} (hc : orderOf c = 3) (hx : x ∈ Subgroup.zpowers c)
    (hx1 : x ≠ 1) : x = c ∨ x = c⁻¹ := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rw [← zpow_mod_orderOf, hc] at hx1 ⊢
  have h0 : 0 ≤ k % ((3 : ℕ) : ℤ) := Int.emod_nonneg k (by norm_num)
  have h3 : k % ((3 : ℕ) : ℤ) < 3 := Int.emod_lt_of_pos k (by norm_num)
  have hc3 : c ^ 3 = 1 := by rw [← hc]; exact pow_orderOf_eq_one c
  interval_cases h : k % ((3 : ℕ) : ℤ)
  · exact absurd (zpow_zero c) hx1
  · left
    exact zpow_one c
  · right
    rw [eq_inv_iff_mul_eq_one, ← zpow_add_one]
    exact_mod_cast hc3

theorem orderOf_conj (a c : H) : orderOf (a * c * a⁻¹) = orderOf c := by
  have := (MulAut.conj a).orderOf_eq c
  rwa [MulAut.conj_apply] at this

theorem normalizer_le_centralizer_or_exists_inv [Finite H] (P : Sylow 3 H)
    (hP : IsCyclic (P : Subgroup H)) {c : H} (hcP : c ∈ P) (hc : orderOf c = 3) :
    Subgroup.normalizer (P : Set H) ≤ Subgroup.centralizer (P : Set H) ∨
      ∃ t ∈ Subgroup.normalizer (P : Set H), t * c * t⁻¹ = c⁻¹ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_cases hex : ∃ t ∈ Subgroup.normalizer (P : Set H), t * c * t⁻¹ = c⁻¹
  · exact Or.inr hex
  left
  push Not at hex
  intro n hn
  obtain ⟨e, s, hs3, hns⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos n).ne' 3 (by norm_num)
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact hs3 (dvd_zero 3)
  have h3e : 3 ^ e ≠ 0 := pow_ne_zero _ (by norm_num)
  set a := n ^ (3 ^ e) with ha
  set b := n ^ s with hb
  have haN : a ∈ Subgroup.normalizer (P : Set H) := pow_mem hn _
  have hbN : b ∈ Subgroup.normalizer (P : Set H) := pow_mem hn _
  have hao : orderOf a = s := by
    rw [ha, orderOf_pow_of_dvd h3e ⟨s, hns⟩, hns,
      Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero h3e)]
  have hbo : orderOf b = 3 ^ e := by
    rw [hb, orderOf_pow_of_dvd hs0 ⟨3 ^ e, by rw [hns, mul_comm]⟩, hns,
      Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hs0)]
  have hbP : b ∈ P := mem_of_mem_normalizer P hbN hbo
  have hbC : b ∈ Subgroup.centralizer (P : Set H) :=
    Subgroup.mem_centralizer_iff.mpr fun x hx => mul_comm_of_isCyclic hP hx hbP
  have hacP : a * c * a⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp haN c).mp hcP
  have haco : orderOf (a * c * a⁻¹) = 3 := by rw [orderOf_conj, hc]
  have hz : a * c * a⁻¹ ∈ Subgroup.zpowers c := by
    rw [← zpowers_eq_of_orderOf hP hcP hacP hc haco]
    exact Subgroup.mem_zpowers _
  have hne1 : a * c * a⁻¹ ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at haco
    omega
  have hac : a * c * a⁻¹ = c :=
    (eq_or_eq_inv_of_mem_zpowers hc hz hne1).resolve_right (hex a haN)
  have haC : a ∈ Subgroup.centralizer (P : Set H) := by
    refine mem_centralizer_of_coprime hP P.isPGroup' hcP hc haN ?_ hac
    rw [hao]
    exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hs3).symm
  have hcop : Nat.Coprime (3 ^ e) s :=
    Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hs3)
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr hcop
  have hn' : n = a ^ u * b ^ v := by
    have h1 : n = n ^ (u * ((3 ^ e : ℕ) : ℤ) + v * (s : ℤ)) := by rw [huv, zpow_one]
    rw [h1, zpow_add, mul_comm u, mul_comm v, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast]
  rw [hn']
  exact mul_mem (zpow_mem haC u) (zpow_mem hbC v)

end Cyclic

section Main

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}

theorem centralizer_ne_top (hs : Sec17Std G A c L Y₀) (h9 : Nat.card (A ⊓ L : Subgroup G) = 9) :
    Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G) ≠ ⊤ := by
  intro htop
  have hEc : ((A ⊓ L : Subgroup G) : Set G) ⊆ Subgroup.center G :=
    Subgroup.centralizer_eq_top_iff_subset.mp htop
  have : IsSimpleGroup G := hs.isSimpleGroup
  rcases (Subgroup.center G).normal_of_characteristic.eq_bot_or_eq_top with h0 | h1
  · have hE : (A ⊓ L : Subgroup G) = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have := hEc hx
      rwa [h0] at this
    rw [hE, Subgroup.card_bot] at h9
    omega
  · obtain ⟨a, b, hab⟩ := hs.nonabelian
    apply hab
    have ha : a ∈ Subgroup.center G := h1 ▸ Subgroup.mem_top a
    exact (Subgroup.mem_center_iff.mp ha b).symm

end Main

end Proof168Res8Comm

end CFSG.RankThree.PartTwo.Sec17
