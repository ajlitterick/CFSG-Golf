module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Asc77.AscT3CIITransfer
public import CFSG.ClassicalInvolution.Asc77.AscT3CIIX
public import CFSG.ClassicalInvolution.Asc77.AscT3CLateSwap

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

theorem Std20.r10a_X_le_C {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
    {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}
    (d : Std20 p f K K' J S R R' W V z t) :
    sec20X (CoreAssembly.conjClass K) z K K' ≤ Subgroup.centralizer ({z} : Set G) := by
  have hK : ∀ {L : Subgroup G}, IsUniqueInvolution L z → L ≤ Subgroup.centralizer ({z} : Set G) :=
    fun hL k hk => by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have := hL.conj_eq (conjSub_eq_self_of_mem hk)
      calc k * z = (k * z * k⁻¹) * k := by group
        _ = z * k := by rw [this]
  exact sup_le (sup_le (iSup₂_le fun _ hU => hU.2) (hK d.viol.hzK)) (hK d.late_hzK')

variable (p f : ℕ) [Fact p.Prime]

@[expose] def Res10aInv : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K K' J : Subgroup G) (S : Sylow 2 G)
    (R R' W V : Subgroup G) (z t : G), Std20 p f K K' J S R R' W V z t →
      Concl20_3 K K' V z → Concl20_4 S K K' J z → Concl20_5 S K K' z → Concl20_7 S K K' z →
        Concl20_8 S K' R → Concl20_9 S K K' R R' z → 8 < Nat.card R →
          ∃ a ∈ (S : Subgroup G), a * a = 1 ∧ a ∉ sec20X (CoreAssembly.conjClass K) z K K' ∧
            InducesFAut K R a ∧ InducesFAut K' R' a


end CFSG.ClassicalInvolution.Asc77.T3CII
