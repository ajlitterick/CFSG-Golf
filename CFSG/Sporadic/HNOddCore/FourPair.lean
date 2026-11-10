
module

public import CFSG.Sporadic.HNOddCore.FourPairBase

public import CFSG.Sporadic.HNOddCore.FourPairB
public meta import CFSG.Sporadic.HNSchreier.ThreeCheck
public meta import CFSG.Sporadic.HNOddCore.InvData
public meta import CFSG.Sporadic.HNSchreier.LocalCheck
public meta import CFSG.Sporadic.HNOddCore.CCheck
public meta import CFSG.Sporadic.HNOddCore.InvArrays
public meta import Certificates.Data.CFSGNative.ONSchreier.Tools
public meta import CFSG.Sporadic.HNSchreier.OrbitCheck
public meta import Certificates.Data.CFSGNative.ONSchreier.Vectors
public meta import CFSG.Sporadic.HNSchreier.SeedsCheck
public meta import CFSG.Sporadic.HNSchreier.PrimCheck
public meta import CFSG.Sporadic.HNSchreier.LocalData
public meta import CFSG.Sporadic.HNSchreier.MaskCheck
public meta import Certificates.Data.CFSGNative.Perm.Chain

public noncomputable section

namespace CFSG.Sporadic.HNOddCore

open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native CFSG.ONSchreier
open CFSG.ONSchreier.Native CFSG.Sporadic.HNOddCore.Native Equiv

instance Qbar_normal_inst :
    (Qbar.subgroupOf rho4.range).Normal := Qbar_normal

abbrev Qr :
    Subgroup rho4.range := Qbar.subgroupOf rho4.range

@[expose] def qrEquiv :
    Fin 256 ≃ Qr :=
  qbEquiv.trans (Subgroup.subgroupOfEquivOfLe Qbar_le_range).symm.toEquiv

theorem qrEquiv_val
    (m : Fin 256) : ((qrEquiv m : rho4.range) : Perm (Fin 800)) = qb m := rfl

@[expose] def psiQ :
    MulAut Qr →* Perm (Fin 256) :=
  (Equiv.permCongrHom qrEquiv.symm).toMonoidHom.comp (MulAut.toPerm Qr)

@[expose] def kappa :
    rho4.range →* Perm (Fin 256) := psiQ.comp (MulAut.conjNormal (H := Qr))

theorem kappa_apply
    (x : rho4.range) (m : Fin 256) :
    kappa x m = qrEquiv.symm (MulAut.conjNormal (H := Qr) x (qrEquiv m)) := rfl

theorem kappa_injective_aut :
    Function.Injective psiQ := by
  intro f g h
  have h1 := (Equiv.permCongrHom qrEquiv.symm).injective h
  exact MulEquiv.toEquiv_injective h1

@[expose] def rhoGenR
    (g : Fin 11) : rho4.range := ⟨rhoGen g, rhoGen_mem g.2⟩

theorem closure_rhoGenR :
    Subgroup.closure (Set.range rhoGenR) = ⊤ :=
  closure_preimage_eq_top (fun g : Fin 11 => rhoGen_mem g.2) range_eq_closure_rhoGen

theorem kappa_gen_inv
    (g : Fin 11) : kappa (rhoGenR g)⁻¹ = pk g := by
  apply Equiv.ext
  intro m
  apply Fin.ext
  rw [← prep_pk g.2 m, kappa_apply]
  have hlt := colPerm_lt g.2 m.2
  have e : MulAut.conjNormal (rhoGenR g)⁻¹ (qrEquiv m) = qrEquiv ⟨_, hlt⟩ := by
    apply Subtype.ext
    apply Subtype.ext
    rw [MulAut.conjNormal_apply, Subgroup.coe_mul, Subgroup.coe_mul, inv_inv, InvMemClass.coe_inv,
      qrEquiv_val, qrEquiv_val, mul_assoc]
    exact colPerm_spec g.2 m.2
  rw [e, Equiv.symm_apply_apply]

theorem kappa_gen
    (g : Fin 11) : kappa (rhoGenR g) = (pk g)⁻¹ := by
  rw [← kappa_gen_inv, map_inv, inv_inv]

theorem card_kappa_range :
    Nat.card kappa.range = 14400 := by
  rw [range_eq_closure kappa closure_rhoGenR]
  have e : Subgroup.closure (Set.range fun g => kappa (rhoGenR g)) =
      Subgroup.closure (Set.range fun g : Fin 11 => pk g) := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      rintro _ ⟨g, rfl⟩
      show kappa (rhoGenR g) ∈ _
      rw [kappa_gen]
      exact Subgroup.inv_mem _ (Subgroup.subset_closure ⟨g, rfl⟩)
    · rw [Subgroup.closure_le]
      rintro _ ⟨g, rfl⟩
      show pk g ∈ _
      rw [← inv_inv (pk g), ← kappa_gen]
      exact Subgroup.inv_mem _ (Subgroup.subset_closure ⟨g, rfl⟩)
  have hO : ∀ k < colPerms.size, PRep 256 colPerms[k]! (pk k) := fun k hk =>
    prep_pk (by rw [← q_parts.2.2.2.1]; exact hk)
  have e2 : Subgroup.closure (Set.range fun g : Fin 11 => pk g) = arrGen 256 colPerms := by
    rw [arrGen_eq hO]
    congr 1
    ext σ
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨⟨g, by rw [q_parts.2.2.2.1]; exact g.2⟩, rfl⟩
    · rintro ⟨⟨k, hk⟩, rfl⟩
      exact ⟨⟨k, by rw [← q_parts.2.2.2.1]; exact hk⟩, rfl⟩
  rw [e, e2,
    card_arrGen_of_chainCheck (by norm_num) (by decide) q_parts.2.2.2.2.2.2.2.2.2.2.2]
  decide

theorem card_conj_range :
    Nat.card (MulAut.conjNormal (G := rho4.range) (H := Qr)).range = 14400 := by
  rw [← card_kappa_range, kappa, MonoidHom.range_comp,
    Subgroup.card_map_of_injective kappa_injective_aut]

theorem card_Qr :
    Nat.card Qr = 256 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe Qbar_le_range).toEquiv, card_Qbar]

theorem Qr_le_ker :
    Qr ≤ (MulAut.conjNormal (G := rho4.range) (H := Qr)).ker := by
  intro x hx
  rw [MonoidHom.mem_ker]
  apply MulEquiv.ext
  intro h
  apply Subtype.ext
  rw [MulAut.conjNormal_apply, MulAut.one_apply]
  apply Subtype.ext
  show (x : Perm (Fin 800)) * ((h : rho4.range) : Perm (Fin 800)) * (x : Perm (Fin 800))⁻¹ =
    ((h : rho4.range) : Perm (Fin 800))
  rw [Qbar_comm (x := (x : Perm (Fin 800))) (y := ((h : rho4.range) : Perm (Fin 800))) hx h.2,
    mul_assoc, mul_inv_cancel, mul_one]

theorem ker_conj :
    (MulAut.conjNormal (G := rho4.range) (H := Qr)).ker = Qr := by
  have h1 := (MulAut.conjNormal (G := rho4.range) (H := Qr)).ker.card_mul_index
  rw [Subgroup.index_ker, card_conj_range, card_rho4_range] at h1
  refine (Subgroup.eq_of_le_of_card_ge Qr_le_ker ?_).symm
  rw [card_Qr]
  omega

theorem centralizer_Qbar :
    Subgroup.centralizer (Qbar : Set (Perm (Fin 800))) ⊓ rho4.range = Qbar := by
  apply le_antisymm
  · rintro x ⟨hc, hr⟩
    have hx : (⟨x, hr⟩ : rho4.range) ∈ Qr := by
      rw [← ker_conj, MonoidHom.mem_ker]
      apply MulEquiv.ext
      intro h
      apply Subtype.ext
      rw [MulAut.conjNormal_apply, MulAut.one_apply]
      apply Subtype.ext
      show x * ((h : rho4.range) : Perm (Fin 800)) * x⁻¹ = ((h : rho4.range) : Perm (Fin 800))
      rw [(Subgroup.mem_centralizer_iff.1 hc ((h : rho4.range) : Perm (Fin 800)) h.2).symm,
        mul_assoc, mul_inv_cancel, mul_one]
    exact hx
  · intro x hx
    refine ⟨Subgroup.mem_centralizer_iff.2 fun y hy => Qbar_comm hy hx, Qbar_le_range hx⟩

abbrev Q4 :
    Subgroup C4 := Qr.comap rho4.rangeRestrict

theorem Q4_normal :
    Q4.Normal := Subgroup.Normal.comap Qbar_normal _

theorem mem_Q4
    {x : C4} : x ∈ Q4 ↔ rho4 x ∈ Qbar := Iff.rfl

theorem card_Q4 :
    Nat.card Q4 = 512 := by
  have hK : rho4.rangeRestrict.ker ≤ Q4 := Subgroup.ker_le_comap _ _
  have h := card_ker_mul_card_map rho4.rangeRestrict hK
  rw [Subgroup.map_comap_eq_self_of_surjective rho4.rangeRestrict_surjective, card_Qr,
    MonoidHom.ker_rangeRestrict, ker_rho4, Nat.card_zpowers, orderOf_t4C] at h
  omega

theorem Q4_isPGroup :
    IsPGroup 2 Q4 := IsPGroup.of_card (n := 9) (by rw [card_Q4]; norm_num)

theorem centralizer_Q4_le :
    Subgroup.centralizer (Q4 : Set C4) ≤ Q4 := by
  intro x hx
  rw [mem_Q4, ← centralizer_Qbar]
  refine ⟨Subgroup.mem_centralizer_iff.2 fun q hq => ?_, ⟨x, rfl⟩⟩
  obtain ⟨y, hy⟩ := Qbar_le_range hq
  have hyQ : y ∈ Q4 := by
    rw [mem_Q4, hy]
    exact hq
  have := Subgroup.mem_centralizer_iff.1 hx y hyQ
  rw [← hy, ← map_mul, ← map_mul, this]


end CFSG.Sporadic.HNOddCore
