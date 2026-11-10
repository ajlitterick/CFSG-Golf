module

public import CFSG.Quasithin.Vol2.Ch12Sec7L5j
public import CFSG.Quasithin.Vol2.Ch12Sec7L5h
public import CFSG.Quasithin.EmptyFaithful.S1421QA12Aut

public section

namespace CFSG.Quasithin.H13.S127.I77

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique S127.L5

variable {G : Type} [Group G] [Finite G]


abbrev Kt (L : Subgroup G) (t : G) : Subgroup G :=
  conjClosure (Lt L t) (Subgroup.centralizer ({t} : Set G))

structure Set77 (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (t : G) : Prop where
  d : D127 G T L V t
  not_le : ¬ Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (L : Set G)
  comp : IsComponentOf (Kt L t) (Subgroup.centralizer ({t} : Set G))
  center : (Subgroup.center ↥(Kt L t)).map (Kt L t).subtype = Vt L t
  psl : IsPSL 3 2 2 (↥(Kt L t) ⧸ Subgroup.center ↥(Kt L t))
  fpf : ∀ x ∈ XOf L, x ∉ Subgroup.centralizer (V : Set G) →
    V ⊓ Subgroup.centralizer ({x} : Set G) = ⊥
  exists_x : ∃ x ∈ XOf L, x ∉ Subgroup.centralizer (V : Set G)
  o2L : L ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 L

omit [Finite G] in
theorem lt_le_Kt (L : Subgroup G) (t : G) : Lt L t ≤ Kt L t := le_conjClosure _ _

theorem set77_of (h71 : Setup1271) (h74 : Lemma12_7_4) (h125 : Lemma12_7_5)
    {T L V : Subgroup G} {t : G} (h : Hyp1271 G T L V) (ht : t ∈ V)
    (h18 : (Subgroup.centralizer ({t} : Set G)).relIndex L = 18)
    (hnot : ¬ Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (L : Set G)) :
    Set77 G T L V t := by
  obtain ⟨hc, hz, hp⟩ := (h125 G T L V h t ht h18).resolve_left hnot
  obtain ⟨-, -, hO2, h3, -, hfpf⟩ := h71 G T L V h
  refine ⟨d127_of h71 h74 h ht h18, hnot, hc, hz, hp, hfpf, ?_, hO2⟩
  by_contra hno
  push Not at hno
  have hbot : autOn (XOf L) V = ⊥ := by
    rw [autOn, Subgroup.map_eq_bot_iff]
    intro y hy
    rw [MonoidHom.mem_ker]
    exact A4.conjAct_eq_one_iff.mpr (hno _ (Subgroup.mem_subgroupOf.mp hy))
  rw [hbot, Subgroup.card_bot] at h3
  norm_num at h3

namespace Set77

variable {T L V : Subgroup G} {t : G} (s : Set77 G T L V t)
include s

theorem sq_t : t ^ 2 = 1 := sq_eq_one_of_mem s.d.hyp.hyp s.d.mem

theorem le_Gt : Kt L t ≤ Subgroup.centralizer ({t} : Set G) := s.comp.1

theorem vt_le : Vt L t ≤ Kt L t := by
  rw [← s.center]
  exact Subgroup.map_subtype_le _

theorem le_centralizer_vt : Kt L t ≤ Subgroup.centralizer (Vt L t : Set G) := by
  intro k hk
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  rw [← s.center] at hv
  obtain ⟨z, hz, rfl⟩ := hv
  exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨k, hk⟩)).symm

theorem card_center : Nat.card ↥(Subgroup.center ↥(Kt L t)) = 4 := by
  rw [← Subgroup.card_map_of_injective (Kt L t).subtype_injective, s.center, s.d.card_Vt]

theorem isPGroup_center : IsPGroup 2 ↥(Subgroup.center ↥(Kt L t)) :=
  IsPGroup.of_card (n := 2) (by rw [s.card_center]; norm_num)

theorem two_le_pRank : 2 ≤ CFSG.pRank 3 (↥(Kt L t) ⧸ Subgroup.center ↥(Kt L t)) := by
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
  exact QA12.two_le_pRank_psl34 s.psl

theorem normalizer_Gt :
    Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (Kt L t : Set G) :=
  le_normalizer_of_isComponentOf (s.d.pRank_le_two s.sq_t) s.comp s.isPGroup_center
    s.two_le_pRank

theorem card_quot : Nat.card (↥(Kt L t) ⧸ Subgroup.center ↥(Kt L t)) = 20160 := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := QA12.exists_equiv_projectiveSL s.psl
  rw [Nat.card_congr e.toEquiv, RankThree.PartTwo.KFacts.L34.card_projectiveSL hF]

theorem card_Kt : Nat.card ↥(Kt L t) = 80640 := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥(Kt L t)), s.card_quot,
    s.card_center]


theorem card_pCore_Lt : Nat.card ↥(CFSG.pCore 2 ↥(Lt L t)) = 64 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdvd : Nat.card ↥(Lt L t) ∣ Nat.card ↥(Kt L t) := Subgroup.card_dvd_of_le (lt_le_Kt L t)
  rw [s.d.card_Lt, s.card_Kt] at hdvd
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥(Lt L t)))
  have hle := s.d.card_V_le
  rw [s.d.card_V, ha] at hle
  rw [ha] at hdvd ⊢
  have h2a : 2 ^ a ∣ 2 ^ 6 * 21 := by
    obtain ⟨c, hc⟩ := hdvd
    have hc' : (80640 : ℕ) = (2 ^ a * c) * 60 := by rw [hc]; ring
    exact ⟨c, by omega⟩
  have h64 : 2 ^ a ∣ 2 ^ 6 :=
    (Nat.Coprime.dvd_of_dvd_mul_right (Nat.Coprime.pow_left _ (by norm_num)) h2a)
  have ha6 : a ≤ 6 := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h64
  have : 2 ^ a ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) ha6
  omega

theorem pCore_Lt : CFSG.pCore 2 ↥(Lt L t) = V.subgroupOf (Lt L t) := by
  refine (Subgroup.eq_of_le_of_card_ge s.d.subgroupOf_le_pCore ?_).symm
  rw [s.card_pCore_Lt, Nat.card_congr (Subgroup.subgroupOfEquivOfLe s.d.v_le_lt).toEquiv,
    s.d.card_V]
  norm_num


end Set77

end CFSG.Quasithin.H13.S127.I77
