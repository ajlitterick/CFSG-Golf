
module

public import CFSG.Sporadic.FischerOddCore.Fi24R2Order
public import CFSG.Sporadic.FischerOddCore.Fi24R2CheckBase
public import CFSG.Sporadic.FischerOddCore.Fi23T2Card
public import CFSG.Sporadic.FischerOddCore.Fi24Cent
public meta import CFSG.Sporadic.FischerOddCore.Fi22CentData
public meta import CFSG.Monster.B.Fischer.Fi22OuterCheck
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import CFSG.Sporadic.FischerOddCore.Fi22Cent
public meta import CFSG.Sporadic.FischerOddCore.Fi22ExtSylowCheck
public meta import CFSG.Sporadic.FischerOddCore.Fi22ExtData
public meta import Certificates.Data.CFSGNative.FischerOddCore.Checks
public meta import CFSG.Sporadic.FischerOddCore.Fi22ExtCheck
public meta import CFSG.Monster.B.Fischer.Fi22CoverCheck
public meta import CFSG.Monster.B.Fischer.Fi22OrderCheck
public meta import CFSG.Monster.B.Fischer.Fi22GraphCheck
public meta import CFSG.Sporadic.FischerOddCore.Fi22CentCheck
public meta import CFSG.Monster.B.Fischer.Fi22GraphBoundCheck
public meta import CFSG.Sporadic.FischerOddCore.Fi22RelBoundCheck
public meta import CFSG.Sporadic.FischerOddCore.Fi22CentOrderCheck
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentInitial.SolvableCoreComponents

@[expose] public noncomputable section

namespace CFSG.Sporadic.FischerOddCore

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG CFSG.LocalCores
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native
open CFSG.Sporadic.Fi24.Native
open CFSG.Sporadic.Fi24 (R J M MR tR D24 jR)

attribute [local instance] CFSG.Sporadic.Fi24.rAction

section Generic

theorem not_isComponent_of_selfCentralizing {L : Type*} [Group L] [Finite L] {Q : Subgroup L}
    (hQn : Q.Normal) (hQ2 : IsPGroup 2 Q) (hQc : Subgroup.centralizer (Q : Set L) ≤ Q)
    (B : Subgroup L) : ¬ IsComponent B :=
  not_isComponent_of_surj_selfCentralizing (MonoidHom.id L) Function.surjective_id
    (fun x hx => by rw [show x = 1 from hx, one_mul]) hQn hQ2 hQc B


theorem comap_selfCentralizing {L M : Type*} [Group L] [Group M] (ρ : L →* M)
    (hρ : Function.Surjective ρ) {N : Subgroup M}
    (hNc : Subgroup.centralizer (N : Set M) ≤ N) :
    Subgroup.centralizer ((N.comap ρ : Subgroup L) : Set L) ≤ N.comap ρ := by
  intro y hy
  show ρ y ∈ N
  apply hNc
  rw [Subgroup.mem_centralizer_iff]
  intro m hm
  obtain ⟨x, rfl⟩ := hρ m
  have := Subgroup.mem_centralizer_iff.1 hy x hm
  rw [← map_mul, ← map_mul, this]


theorem card_fix_conj {G : Type*} [Group G] [MulAction G (Fin 306936)] (c g : G) :
    Nat.card {k : Fin 306936 // (c * g * c⁻¹) • k = k} = Nat.card {k : Fin 306936 // g • k = k} :=
  Nat.card_congr
    { toFun := fun k => ⟨c⁻¹ • k.1, by
        have h := k.2
        rw [mul_smul, mul_smul] at h
        exact eq_inv_smul_iff.2 h⟩
      invFun := fun k => ⟨c • k.1, by rw [mul_smul, mul_smul, inv_smul_smul, k.2]⟩
      left_inv := fun k => Subtype.ext (smul_inv_smul c k.1)
      right_inv := fun k => Subtype.ext (inv_smul_smul c k.1) }

end Generic

theorem fi24R2_mem_M :
    fi24R2 ∈ M := (Fi24.fi23EquivM.symm fi23U3).2

theorem fi23EquivM_fi24R2 :
    Fi24.fi23EquivM ⟨fi24R2, fi24R2_mem_M⟩ = fi23U3 :=
  MulEquiv.apply_symm_apply _ _

theorem fi24R2_ne_one :
    fi24R2 ≠ 1 := fun h => by
  have h1 : Fi24.fi23EquivM.symm fi23U3 = 1 := Subtype.ext h
  rw [MulEquiv.map_eq_one_iff] at h1
  exact fi23U3_facts.2 h1

theorem smul_val_of_rep {G : Type*} [Group G] {n : ℕ} [MulAction G (Fin n)] {T : Table} {g : G}
    (hT : Rep n T g) (k : Fin n) : (g • k).val = ap T k.val := by
  rw [hT k.val k.isLt, idx_of_lt g k.isLt]


abbrev fi24C :
    Subgroup J := Subgroup.centralizer ({fi24R2} : Set J)

theorem fi24R2_mem_C :

    fi24R2 ∈ fi24C := (Subgroup.mem_centralizer_singleton_iff (G := J)).2 rfl

theorem fi24C_smul_fixed
    (c : fi24C) (k : Fin 306936) (hk : fi24R2 • k = k) :
    fi24R2 • ((c : J) • k) = (c : J) • k := by
  have hc : (c : J) * fi24R2 = fi24R2 * (c : J) :=
    (Subgroup.mem_centralizer_singleton_iff (G := J)).1 c.2
  rw [smul_smul, ← hc, mul_smul, hk]


end CFSG.Sporadic.FischerOddCore
