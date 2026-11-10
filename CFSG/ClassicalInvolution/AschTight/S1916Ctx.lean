module

public import CFSG.ClassicalInvolution.AschTight.S1916Help
public import CFSG.ClassicalInvolution.AschTight.S1916Sec

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S1916

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

variable {G : Type} [Group G] {p f : ℕ} [Fact p.Prime] [Finite G]

structure Ctx12 (p f : ℕ) [Fact p.Prime] (K : Subgroup G) (z : G) (S : Sylow 2 G)
    (W L : Subgroup G) (t : G) : Prop where
  data : Sec19DataT p f K z S W L t (L ⊓ W)
  inv : ∀ s ∈ (S : Subgroup G), conjSub s W = W
  ab : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x
  eta : ∃ η ∈ etaG (CoreAssembly.conjClass K),
    (∀ s ∈ (S : Subgroup G), ∀ U ∈ η, conjSub s U ∈ η) ∧ W = ⨆ U ∈ η, U
  rel : (K ⊔ sec19Y K z).relIndex (sec19X K z) = 2
  wrY : ∀ P : Subgroup G, IsSylow2In P (W ⊔ sec19Y K z) → IsWreathed P
  quat : IsQuaternionSub ((S : Subgroup G) ⊓ sec19Y K z)
  card : Nat.card ↥((S : Subgroup G) ⊓ sec19Y K z) = Nat.card ↥((S : Subgroup G) ⊓ K)
  f1 : ∀ x : G, IsPGroup 2 (Subgroup.zpowers x) → x ∈ Subgroup.normalizer (sec19Y K z : Set G) →
    (∀ q ∈ (S : Subgroup G) ⊓ sec19Y K z, x * q = q * x) →
      ∀ y ∈ sec19Y K z, ⁅x, y⁆ ∈ oddCoreOf (sec19Y K z)
  wrRV : IsWreathed (((S : Subgroup G) ⊓ K) ⊔ (L ⊓ W))

variable {K : Subgroup G} {z : G} {S : Sylow 2 G} {W L : Subgroup G} {t : G}

theorem Ctx12.hd (c : Ctx12 p f K z S W L t) : Sec19Data p f K z S W := c.data.toSec19Data


theorem Ctx12.exists_not_mem (c : Ctx12 p f K z S W L t) :
    ∃ v ∈ L ⊓ W, v ∉ K ⊔ sec19Y K z := by
  have hd := c.hd
  refine exists_not_mem_of_isWreathed (S := (S : Subgroup G))
    (fun u hu huM => (sd_inf_sup_R_Q hd) ▸ ⟨hu, huM⟩) (sd_commute_R_Q hd)
    (inf_le_right.trans hd.hWS) (fun v hv => mem_normalizer_inf_of_mem
      (hd.hWS hv.2) (sd_normalizer_eq hd ▸ hd.hSz (hd.hWS hv.2))) c.wrRV
    (S.isPGroup'.to_le inf_le_left) (sd_isUniqueInvolution_R hd) (sd_noncomm_R hd)

theorem Ctx12.L_ne_K (c : Ctx12 p f K z S W L t) : L ≠ K := by
  intro h
  apply c.data.ne
  subst h
  exact c.data.invL.eq (isUniqueInvolution_of_tight c.hd.tight.toTightBranch)

theorem isSylow2In_inf_of_half {M C U : Subgroup G} (hU2 : IsPGroup 2 U) (hUM : U ≤ M ⊓ C)
    (hcard : ∀ T : Subgroup G, IsSylow2In T M → Nat.card T = 2 * Nat.card U)
    (hno : ∀ T : Subgroup G, IsSylow2In T M → ¬ T ≤ C) : IsSylow2In U (M ⊓ C) := by
  refine ⟨hUM, hU2, fun V' hV'MC hV'2 hle => ?_⟩
  obtain ⟨T, hT, hV'T⟩ := IsSylow2In.exists_ge hV'2 (hV'MC.trans inf_le_left)
  rcases eq_or_eq_of_natCard_eq_two_mul hle hV'T (hcard T hT) with h | h
  · exact h
  · exfalso
    apply hno T hT
    rw [← h]
    exact hV'MC.trans inf_le_right

theorem Ctx12.card_R [IsSimpleGroup G] (c : Ctx12 p f K z S W L t) :
    Nat.card ↥((S : Subgroup G) ⊓ K) = 2 * Nat.card ↥(L ⊓ W) := by
  have hΩ := hypOmegaMod_of_tightD c.hd.tight
  obtain ⟨R', hR', hVR', -, hidx⟩ := c.data.memV
  have hR'card : Nat.card R' = 2 * Nat.card ↥(L ⊓ W) := by
    have h1 := Subgroup.relIndex_mul_card (H := L ⊓ W) (K := R')
    rw [hidx, inf_eq_left.mpr hVR'] at h1
    exact h1.symm
  obtain ⟨M, hM, hR'M⟩ := exists_isSylow2In_of_mem_RSet hR'
  rw [← hR'card, hΩ.natCard_isSylow2In hM hR'M,
    hΩ.natCard_isSylow2In (CoreAssembly.mem_conjClass_self K) (sd_isSylow2In_R c.hd)]

theorem Ctx12.isSylow2In_V [IsSimpleGroup G] (c : Ctx12 p f K z S W L t) :
    IsSylow2In (L ⊓ W) (L ⊓ Subgroup.centralizer ({z} : Set G)) := by
  have hd := c.hd
  have ht := hd.tight
  have hΩ := hypOmegaMod_of_tightD ht
  refine isSylow2In_inf_of_half (S.isPGroup'.to_le (inf_le_right.trans hd.hWS))
    (inf_le_inf_left _ (hd.hWS.trans hd.hSz)) (fun T hT => ?_) (fun T hT hTz => ?_)
  · rw [hΩ.natCard_isSylow2In c.data.memL hT, ← hΩ.natCard_isSylow2In
      (CoreAssembly.mem_conjClass_self K) (sd_isSylow2In_R hd), c.card_R]
  · have hTN : T ≤ Subgroup.normalizer (K : Set G) := by
      rw [sd_normalizer_eq hd]
      exact hTz
    have hedge : L ∈ omegaNbr (CoreAssembly.conjClass K) K :=
      ⟨c.data.memL, c.L_ne_K, T, mem_RSet_of_isSylow2In c.data.memL hT, hT.1, hTN⟩
    exact ht.edgeless K (CoreAssembly.mem_conjClass_self K) L c.data.memL (Or.inl hedge)


end CFSG.ClassicalInvolution.Disconnected.AschTight.S1916
