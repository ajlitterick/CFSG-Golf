module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporLat
public import CFSG.Quasithin.Background.E2TwoProofSporJ1
public import CFSG.Quasithin.Background.E2TwoProofSporJ2

import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5CalL0

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1.SporLat Subgroup
open CFSG.Quasithin.E2P.SporB
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)


theorem asch54SporGenAt_j1 :
    Asch54SporGenAt .J1 := by
  have hOut : Nat.card (Outer ↥CFSG.Sporadic.J1.J) = 1 :=
    (Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence
      CFSG.Sporadic.J1.nativeEquiv.symm).toEquiv).trans CFSG.Sporadic.Schreier.at_j1_schreier.1
  refine asch54SporGenAt_of_list_of_card_outer_eq_one
    (CFSG.Sporadic.Bridge.J1.nonempty_mulEquiv.map fun f =>
      f.symm.trans CFSG.Sporadic.J1.nativeEquiv)
    CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput hOut j1_sylow j1_all
    (fun j _ => j1_S_le_Y j) j1_cards j1_card_J (a := 16) (b := 1)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem asch54SporGenAt_j2 :
    Asch54SporGenAt .J2 := by
  have hL : j2Ctx.D.Om.map (fun o => o.lbl.size) = #[1, 3, 9, 15, 3] := j2_Om_size
  have hN : j2Ctx.D.O.lbl.size = 4725 := j2_O_size
  have hk : j2Ctx.k = 7 := rfl
  have hS : IsSylowTwoOf j2Ctx.S ⊤ := by
    refine K1.isSylowTwoOf_top_iff.mpr ⟨j2Ctx.S_isPGroup, ?_⟩
    have h1 := Subgroup.card_mul_index j2Ctx.S
    rw [j2Ctx.S_card, j2Ctx.hΓ, hN, hk] at h1
    have h2 : j2Ctx.S.index = 4725 := by omega
    rw [h2]
    norm_num
  have hOut : Nat.card (Outer ↥CFSG.Sporadic.J2.J) ≤ 2 :=
    CFSG.Sporadic.Schreier.outer_card_le_of_equiv CFSG.Sporadic.Schreier.AT_J2_Schreier.1
      CFSG.Sporadic.J2.nativeEquiv.symm
  refine asch54SporGenAt_of_list
    (CFSG.Sporadic.Bridge.J2.nonempty_mulEquiv.map fun f =>
      f.symm.trans CFSG.Sporadic.J2.nativeEquiv)
    (fun X _ _ hX => (isCalL0_nonabelian_not_sectionalTwoRankLE X hX).1)
    CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput hOut hS (lat_all j2Ctx hL)
    (fun j _ => j2Ctx.S_le_Y j) (lat_card j2Ctx hL) (by rw [j2Ctx.hΓ, hN]) (a := 2) (b := 3)
    (by decide +kernel) ?_ ?_
  · rw [hk]
    decide +kernel
  · rw [hk]
    decide +kernel

end CFSG.LocalAnalysis.WeakClosure81

end
