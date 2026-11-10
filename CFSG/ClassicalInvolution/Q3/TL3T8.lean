module

public import CFSG.ClassicalInvolution.Q3.TL3T6
public import CFSG.ClassicalInvolution.Q3.TL3T7

public section

namespace CFSG.ClassicalInvolution.Q3.TC.Thin

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph

section Span

variable {G : Type} [Group G]

@[expose] def pSpan (P : Set (Subgroup G)) : Subgroup G :=
  ⨆ I ∈ P, I

theorem le_pSpan {P : Set (Subgroup G)} {L : Subgroup G} (hL : L ∈ P) : L ≤ pSpan P :=
  le_biSup (fun I : Subgroup G => I) hL

theorem pSpan_le {P : Set (Subgroup G)} {H : Subgroup G} (h : ∀ L ∈ P, L ≤ H) : pSpan P ≤ H :=
  iSup₂_le h

theorem classicalInvolutionOddCore_eq_bot_of_mulEquiv {A B : Type*} [Group A] [Group B]
    [Finite A] (e : A ≃* B) (h : classicalInvolutionOddCore A = ⊥) :
    classicalInvolutionOddCore B = ⊥ := by
  refine le_antisymm (sSup_le fun N hN => ?_) bot_le
  obtain ⟨hNn, hodd⟩ := hN
  set N' : Subgroup A := N.comap e.toMonoidHom with hN'
  have hmap : N'.map e.toMonoidHom = N :=
    Subgroup.map_comap_eq_self_of_surjective e.surjective N
  have hcard : Nat.card N' = Nat.card N := by
    rw [← hmap, Subgroup.card_map_of_injective e.injective]
  have hN'n : N'.Normal := hNn.comap _
  have hle : N' ≤ classicalInvolutionOddCore A := le_sSup ⟨hN'n, hcard ▸ hodd⟩
  rw [h, le_bot_iff] at hle
  rw [← hmap, hle, Subgroup.map_bot]

end Span


variable {G : Type} [Group G] [Finite G]
variable {Ω : Set (Subgroup G)} {K : Subgroup G} (hS : ThinStd Ω K)
include hS

theorem ThinStd.maxAdj_iff_mem_orbOf {M N₀ : Subgroup G} (hN₀ : MaxAdj (nbrAdj Ω) M N₀)
    {L : Subgroup G} : MaxAdj (nbrAdj Ω) M L ↔ L ∈ orbOf (nbrAdj Ω) M N₀ := by
  have hF := hS.graphFam
  constructor
  · intro hL
    have heq : orbOf (nbrAdj Ω) M L = orbOf (nbrAdj Ω) M N₀ :=
      maxOrb_unique hF hN₀.1.1 hL.2 hN₀.2
    rw [← heq]
    exact mem_orbOf_self M L
  · intro hL
    exact ⟨adj_of_mem_orbOf hF.graph hN₀.1 hL, by rw [orbOf_eq_of_mem hL]; exact hN₀.2⟩

theorem ThinStd.pSpan_le_centralizer {M : Subgroup G} {z : G} (hz : IsUniqueInvolution M z) :
    pSpan {L : Subgroup G | MaxAdj (nbrAdj Ω) M L} ≤ Subgroup.centralizer ({z} : Set G) :=
  pSpan_le fun L hL => hS.le_centralizer_of_nbrAdj (show MaxAdj (nbrAdj Ω) M L from hL).1 hz

theorem ThinStd.conj_mem_pSpan {M : Subgroup G} {z : G} (hz : IsUniqueInvolution M z) {c : G}
    (hc : c ∈ Subgroup.centralizer ({z} : Set G)) {x : G}
    (hx : x ∈ pSpan {L : Subgroup G | MaxAdj (nbrAdj Ω) M L}) :
    c * x * c⁻¹ ∈ pSpan {L : Subgroup G | MaxAdj (nbrAdj Ω) M L} := by
  have hle : pSpan {L : Subgroup G | MaxAdj (nbrAdj Ω) M L} ≤
      (pSpan {L : Subgroup G | MaxAdj (nbrAdj Ω) M L}).comap (MulAut.conj c).toMonoidHom := by
    refine pSpan_le fun L hL l hl => ?_
    have hmax := hS.maxAdj_conj_of_mem (show MaxAdj (nbrAdj Ω) M L from hL) hz hc
    have h1 : c * l * c⁻¹ ∈ conjSub c L := conj_mem_conjSub hl
    have h2 := le_pSpan (P := {L : Subgroup G | MaxAdj (nbrAdj Ω) M L}) hmax h1
    simpa using h2
  have := hle hx
  simpa using this

theorem ThinStd.exists_conj_maxOrb {M L L' : Subgroup G} (hL : MaxAdj (nbrAdj Ω) M L)
    (hL' : MaxAdj (nbrAdj Ω) M L') :
    ∃ x ∈ pSpan {L : Subgroup G | MaxAdj (nbrAdj Ω) M L}, conjSub x L = L' := by
  have hF := hS.graphFam
  have hset : {I : Subgroup G | MaxAdj (nbrAdj Ω) M I} = orbOf (nbrAdj Ω) M L := by
    ext I
    exact hS.maxAdj_iff_mem_orbOf hL
  obtain ⟨a, ha, haL⟩ := orbOf_subset_gen hF.graph hL.1 ((hS.maxAdj_iff_mem_orbOf hL).mp hL')
  refine ⟨a, ?_, haL⟩
  rw [hset]
  exact ha

theorem ThinStd.le_Qz_of_normal {M : Subgroup G} {z : G} (hz : IsUniqueInvolution M z)
    {Q : Subgroup G} (hQX : Q ≤ pSpan {L : Subgroup G | MaxAdj (nbrAdj Ω) M L})
    (hQn : ∀ x ∈ pSpan {L : Subgroup G | MaxAdj (nbrAdj Ω) M L}, ∀ q ∈ Q, x * q * x⁻¹ ∈ Q)
    (hQ2 : IsPGroup 2 Q) : Q ≤ Qz z := by
  have hXC := hS.pSpan_le_centralizer hz
  have hXn : ((pSpan {L : Subgroup G | MaxAdj (nbrAdj Ω) M L}).subgroupOf
      (Subgroup.centralizer ({z} : Set G))).Normal :=
    ⟨fun x hx c => Subgroup.mem_subgroupOf.mpr
      (hS.conj_mem_pSpan hz c.2 (Subgroup.mem_subgroupOf.mp hx))⟩
  have hQn' : (Q.subgroupOf (pSpan {L : Subgroup G | MaxAdj (nbrAdj Ω) M L})).Normal :=
    ⟨fun q hq x => Subgroup.mem_subgroupOf.mpr (hQn x x.2 q (Subgroup.mem_subgroupOf.mp hq))⟩
  exact CFSG.RankThreeEvenClassification.Helpers.subnormal_pSubgroup_le_pCoreOf 2
    (CFSG.Open.IsSubnormal.step hQX hQn' (CFSG.Open.IsSubnormal.step hXC hXn
      (CFSG.Open.IsSubnormal.refl _))) hQ2

theorem ThinStd.oddCore_pSpan_eq_bot {M : Subgroup G} {z : G} (hz : IsUniqueInvolution M z)
    (hO : classicalInvolutionOddCore ↥(Subgroup.centralizer ({z} : Set G)) = ⊥) :
    classicalInvolutionOddCore ↥(pSpan {L : Subgroup G | MaxAdj (nbrAdj Ω) M L}) = ⊥ := by
  set C := Subgroup.centralizer ({z} : Set G) with hC
  set X := pSpan {L : Subgroup G | MaxAdj (nbrAdj Ω) M L} with hX
  have hXC : X ≤ C := hS.pSpan_le_centralizer hz
  have hXn : (X.subgroupOf C).Normal :=
    ⟨fun x hx c => Subgroup.mem_subgroupOf.mpr
      (hS.conj_mem_pSpan hz c.2 (Subgroup.mem_subgroupOf.mp hx))⟩
  have hsub : IsSubnormal (X.subgroupOf C) ⊤ :=
    IsSubnormal.step le_top (by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer le_top]
      intro y _
      exact Subgroup.mem_normalizer_iff.mpr fun n =>
        ⟨fun hn => hXn.conj_mem n hn y, fun hn => by
          have := hXn.conj_mem _ hn y⁻¹
          simpa [mul_assoc] using this⟩) (IsSubnormal.refl ⊤)
  have h1 := Q3.oddCore_eq_bot_of_isSubnormal hsub hO
  exact classicalInvolutionOddCore_eq_bot_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hXC) h1

theorem ThinStd.indep_conj {M : Subgroup G} (h : Indep Ω M) (g : G) :
    Indep Ω (conjSub g M) := by
  intro N N' hN hN' hne hadj
  have hF := hS.graphFam
  have h1 := maxAdj_conj hF hN g⁻¹
  have h2 := maxAdj_conj hF hN' g⁻¹
  rw [conjSub_inv_conjSub] at h1 h2
  refine h _ _ h1 h2 (fun heq => hne ?_) (hF.graph.conj g⁻¹ hadj)
  have := congrArg (conjSub g) heq
  rwa [conjSub_conjSub_inv, conjSub_conjSub_inv] at this

end CFSG.ClassicalInvolution.Q3.TC.Thin

namespace CFSG.ClassicalInvolution.Q3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph

section Cit3


end Cit3

end CFSG.ClassicalInvolution.Q3
