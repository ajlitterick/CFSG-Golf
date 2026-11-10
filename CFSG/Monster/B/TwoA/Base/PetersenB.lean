
module

public import CFSG.Monster.B.TwoA.Base.ConjSub
public import CFSG.Monster.B.TwoA.Base.PairSpace
public import CFSG.Monster.B.TwoA.Base.RankThreeBase

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B CFSG.Monster.VisQuot CFSG.Monster.ScalarKernel CFSG.Monster.B.Co2
  CFSG.Monster.Lifts CFSG.Monster.VisCert CFSG.Sporadic.Mathieu

open scoped Pointwise


@[expose] def kmon
    (p : AutPerm) (hp : p ∈ Ppair) : Kstab v0 :=
  ⟨QuotientGroup.mk (gO 0 * PO p), (mk_mem_Kstab_iff_monomial 0 p).2 ⟨hp, Ceq.zero_mem⟩⟩


theorem PairSpace.map_monomial
    {U : Submodule (ZMod 2) (Wv v0)}
    {A : Finset (Set.powersetCard (Fin 24) 2)} (hU : PairSpace U A) {a : C} {p : AutPerm}
    (hk : (QuotientGroup.mk (gO a * PO p) : OLq) ∈ Kstab v0) :
    PairSpace (U.map (wAct v0 ⟨_, hk⟩)) (p • A) := by
  have hp := ((mk_mem_Kstab_iff_monomial a p).1 hk).1
  have hw : wAct v0 ⟨_, hk⟩ wFr = wFr := monomial_mem_Mfr hk
  refine ⟨fun D hD => ?_, fun z => ?_⟩
  · obtain ⟨D', hD', rfl⟩ := Finset.mem_smul_finset.1 hD
    obtain ⟨x, y, h, rfl⟩ := hU.pairs D' hD'
    exact ⟨_, _, h.perm hp, autPerm_smul_duad p h.ne⟩
  · constructor
    · rintro ⟨u, hu, rfl⟩
      rcases (hU.mem_iff u).1 hu with rfl | rfl | ⟨x, y, h, hD, b, rfl⟩
      · exact .inl (map_zero _)
      · exact .inr (.inl hw)
      · refine .inr (.inr ⟨_, _, h.perm hp, ?_, _, wAct_monomial_pairW hk h b⟩)
        have h1 : p • duad x y h.ne ∈ p • A := Finset.smul_mem_smul_finset hD
        rwa [autPerm_smul_duad] at h1
    · rintro (rfl | rfl | ⟨x', y', h', hD', b', rfl⟩)
      · exact ⟨0, U.zero_mem, map_zero _⟩
      · exact ⟨wFr, hU.wFr_mem, hw⟩
      · obtain ⟨D, hD, hpD⟩ := Finset.mem_smul_finset.1 hD'
        obtain ⟨x, y, h, rfl⟩ := hU.pairs D hD
        rw [autPerm_smul_duad, duad_eq_duad_iff] at hpD
        refine ⟨pairW x y h (b' + (a : Fin 24 → ZMod 2) x + (a : Fin 24 → ZMod 2) y),
          hU.pairW_mem h hD _, ?_⟩
        rw [wAct_monomial_pairW hk h, pairW_eq_iff]
        exact ⟨hpD, (by decide : ∀ b s t : ZMod 2, b + s + t + s + t = b) _ _ _⟩

theorem PairSpace.le_iff
    {U U' : Submodule (ZMod 2) (Wv v0)}
    {A B : Finset (Set.powersetCard (Fin 24) 2)} (hU : PairSpace U A) (hU' : PairSpace U' B) :
    U ≤ U' ↔ A ⊆ B := by
  constructor
  · intro hle D hD
    obtain ⟨x, y, h, rfl⟩ := hU.pairs D hD
    rcases (hU'.mem_iff _).1 (hle (hU.pairW_mem h hD 0)) with h1 | h1 | ⟨x', y', h', hB, b', h1⟩
    · exact absurd h1 (pairW_ne_zero h 0)
    · exact absurd h1 (pairW_ne_wFr h 0)
    · rw [pairW_eq_iff] at h1
      rcases h1.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hB
      · rw [duad_comm]
        exact hB
  · intro hAB z hz
    rcases (hU.mem_iff z).1 hz with rfl | rfl | ⟨x, y, h, hD, b, rfl⟩
    · exact U'.zero_mem
    · exact hU'.wFr_mem
    · exact hU'.pairW_mem h (hAB hD) b

end CFSG.Monster.B.TwoA
