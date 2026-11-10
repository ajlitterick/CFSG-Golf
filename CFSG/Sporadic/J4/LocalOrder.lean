module

public import CFSG.Sporadic.J4.GlobalSpec
public import CFSG.Perm.ChainSpec
import Certificates.Data.CFSGNative.J4.Tables
import Certificates.Data.CFSGNative.J4.Chain
import Certificates.Data.CFSGNative.J4.Cert
import Certificates.Data.CFSGNative.Perm.Chain
import Certificates.Data.CFSGNative.Th.Tables

public section

namespace CFSG.Sporadic.J4

open Native Matrix CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native

theorem smul_mem_of_inv_gens {G Y : Type*} [Group G] [Finite G] [MulAction G Y] {s : Set G}
    {S : Set Y} (hs : ∀ g ∈ s, ∀ v ∈ S, g⁻¹ • v ∈ S) :
    ∀ g ∈ Subgroup.closure s, ∀ v ∈ S, g • v ∈ S := by
  intro g hg
  rw [← Subgroup.closure_inv] at hg
  have hg' : g ∈ Submonoid.closure s⁻¹ := by
    rw [← Subgroup.closure_toSubmonoid_of_finite]
    exact hg
  clear hg
  induction hg' using Submonoid.closure_induction with
  | mem x hx =>
    intro v hv
    have := hs x⁻¹ hx v hv
    rwa [inv_inv] at this
  | one => intro v hv; rwa [one_smul]
  | mul x y _ _ hx hy => intro v hv; rw [mul_smul]; exact hx _ (hy v hv)

@[expose] noncomputable def vecO (p : ℕ) : Row := toRow (O0.pts[p]!).toVec

noncomputable abbrev posImg (g p : ℕ) : ℕ :=
  vfind O0.pts O0.slots O0.bits (frApply tx0[g]! O0.pts[p]!) - 1

structure O0Facts : Prop where
  ok : vorbOK tx0 (rdV2 bs0.keys 24) O0 15180 = true
  mat : MatFacts

section O0

variable (hO : O0Facts)
include hO

theorem tx0_size : tx0.size = 3 := by rw [tx0, Array.size_map]; exact hO.mat.locSize

theorem o0_size : O0.pts.size = 15180 := by
  have h := hO.ok
  unfold vorbOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  exact h.1.1.1.1.1

theorem o0_at {q : ℕ} (hq : q < 15180) : vorbAt tx0 O0 q = true := by
  have h := hO.ok
  unfold vorbOK at h
  rw [Bool.and_eq_true, List.all_eq_true] at h
  exact h.2 q (List.mem_range.2 hq)

theorem o0_wf {q : ℕ} (hq : q < 15180) : (O0.pts[q]!).wf = true := by
  have h := o0_at hO hq
  unfold vorbAt at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1

theorem o0_find {q : ℕ} (hq : q < 15180) : vfind O0.pts O0.slots O0.bits O0.pts[q]! = q + 1 := by
  have h := o0_at hO hq
  unfold vorbAt at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1.2

theorem posImg_spec {g p : ℕ} (hg : g < 3) (hp : p < 15180) :
    posImg g p < 15180 ∧ O0.pts[posImg g p]! = frApply tx0[g]! O0.pts[p]! := by
  have h := o0_at hO hp
  unfold vorbAt at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  have := h.1.2 g (by rw [tx0_size hO]; exact hg)
  simp only [bne_iff_ne, ne_eq, decide_eq_true_eq, V2.beq_iff] at this
  obtain ⟨⟨h0, hle⟩, heq⟩ := this
  rw [o0_size hO] at hle
  refine ⟨?_, heq⟩
  show vfind O0.pts O0.slots O0.bits (frApply tx0[g]! O0.pts[p]!) - 1 < 15180
  omega

theorem tx0_get {g : ℕ} (hg : g < 3) : tx0[g]! = frTable ((locMats ())[g]?.getD idRows) := by
  have hs := hO.mat.locSize
  rw [tx0, getElem!_pos _ g (by rw [Array.size_map, hs]; exact hg), Array.getElem_map,
    Array.getElem?_eq_getElem (by rw [hs]; exact hg), Option.getD_some]

theorem xJ_inv_smul_vecO {g p : ℕ} (hg : g < 3) (hp : p < 15180) :
    (xJ g)⁻¹ • vecO p = vecO (posImg g p) := by
  rw [← ofRow_inj, xJ_inv_smul hO.mat]
  show (O0.pts[p]!).toVec ᵥ* _ = (O0.pts[posImg g p]!).toVec
  rw [(posImg_spec hO hg hp).2, tx0_get hO hg, frApply_toVec_eq_vecMul]

theorem vecO_injective {p q : ℕ} (hp : p < 15180) (hq : q < 15180) (h : vecO p = vecO q) :
    p = q := by
  have e : O0.pts[p]! = O0.pts[q]! := V2.eq_of_toVec_eq (o0_wf hO hp) (o0_wf hO hq) h
  have := o0_find hO hp
  rw [e, o0_find hO hq] at this
  omega

noncomputable abbrev o0Set : Set Row := vecO '' Set.Iio 15180

theorem smul_mem_o0Set : ∀ g ∈ Hj, ∀ v ∈ o0Set, g • v ∈ o0Set := by
  refine smul_mem_of_inv_gens fun g hg v hv => ?_
  obtain ⟨p, hp, rfl⟩ := hv
  have hk : ∃ k < 3, g = xJ k := by
    rcases hg with h | h | h
    · exact ⟨0, by norm_num, h⟩
    · exact ⟨1, by norm_num, h⟩
    · exact ⟨2, by norm_num, h⟩
  obtain ⟨k, hk, rfl⟩ := hk
  exact ⟨_, (posImg_spec hO hk hp).1, (xJ_inv_smul_vecO hO hk hp).symm⟩

end O0

@[expose] noncomputable def o0Sub (hO : O0Facts) : SubMulAction Hj Row where
  carrier := o0Set
  smul_mem' g _ hv := smul_mem_o0Set hO g.1 g.2 _ hv

@[expose] noncomputable def o0Equiv (hO : O0Facts) : Fin 15180 ≃ o0Sub hO :=
  Equiv.ofBijective (fun p => ⟨vecO p, ⟨p, p.isLt, rfl⟩⟩)
    ⟨fun p q h => Fin.ext (vecO_injective hO p.isLt q.isLt (congrArg Subtype.val h)), by
      rintro ⟨v, ⟨p, hp, rfl⟩⟩
      exact ⟨⟨p, hp⟩, rfl⟩⟩

noncomputable instance o0Action : MulAction Hj (Fin 15180) where
  smul g p := by
    classical
    exact if h : O0Facts then (o0Equiv h).symm (g • o0Equiv h p) else p
  one_smul p := by
    classical
    show (if h : O0Facts then (o0Equiv h).symm ((1 : Hj) • o0Equiv h p) else p) = p
    split
    · rw [one_smul, Equiv.symm_apply_apply]
    · rfl
  mul_smul g h p := by
    classical
    show (if hF : O0Facts then (o0Equiv hF).symm ((g * h) • o0Equiv hF p) else p) =
      (if hF : O0Facts then (o0Equiv hF).symm (g • o0Equiv hF
        (if hF : O0Facts then (o0Equiv hF).symm (h • o0Equiv hF p) else p)) else
        (if hF : O0Facts then (o0Equiv hF).symm (h • o0Equiv hF p) else p))
    split
    · rw [Equiv.apply_symm_apply, mul_smul]
    · rfl

section Act

variable (hO : O0Facts)
include hO

theorem vecO_smul (g : Hj) (p : Fin 15180) : vecO (g • p : Fin 15180) = (g : J) • vecO p := by
  have : (g • p : Fin 15180) = (o0Equiv hO).symm (g • o0Equiv hO p) := by
    classical
    show (if h : O0Facts then (o0Equiv h).symm (g • o0Equiv h p) else p) = _
    rw [dite_eq_left hO]
  have e := congrArg Subtype.val (congrArg (o0Equiv hO) this)
  rw [Equiv.apply_symm_apply] at e
  exact e

theorem idxO_eq_iff {g : Hj} {p q : ℕ} (hp : p < 15180) (hq : q < 15180) :
    idx 15180 g p = q ↔ (g : J) • vecO p = vecO q := by
  rw [idx, dite_eq_left hp]
  constructor
  · intro h
    have := vecO_smul hO g ⟨p, hp⟩
    rw [h] at this
    exact this.symm
  · intro h
    have e := vecO_smul hO g ⟨p, hp⟩
    rw [h] at e
    exact vecO_injective hO (g • (⟨p, hp⟩ : Fin 15180)).isLt hq e

noncomputable abbrev gq (k : ℕ) : Hj := if hk : k < 3 then ⟨(xJ k)⁻¹, Hj.inv_mem (xJ_mem hk)⟩ else 1


end Act

noncomputable abbrev gens0 : Array Table := tx0.map (posTable O0)

noncomputable abbrev invs0 : Array Table := gens0.map (invT 15180)

noncomputable abbrev gensT (l : ℤ) : Table :=
  if 0 < l then gens0[l.toNat - 1]?.getD (idT 15180) else invs0[(-l).toNat - 1]?.getD (idT 15180)


noncomputable abbrev gensG (l : ℤ) : Hj :=
  if 0 < l then gq (l.toNat - 1) else (gq ((-l).toNat - 1))⁻¹


section Chain

variable (hF : J4NativeFacts)
include hF

theorem J4NativeFacts.o0Facts : O0Facts := ⟨hF.o0, hF.mat⟩


theorem eq_one_of_fix_qIdx0 {g : J} (hg0 : idx nPts g 0 = 0)
    (hgq : ∀ t < qIdx0.size, idx nPts g qIdx0[t]! = qIdx0[t]!) : g = 1 := by
  refine eq_one_of_fix_tuple hF.orbitFacts (qIdx0_lt hF) hF.sig ?_ hF.basis hg0 hgq
  intro t ht
  have h := hF.blt
  rw [Array.all_eq_true] at h
  rw [getElem!_pos basisIdx t ht]
  exact of_decide_eq_true (h t ht)

theorem vecAt_qIdx0 {t : ℕ} (ht : t < qLen) : vecAt qIdx0[t]! = vecO t := by
  have h := hF.q
  rw [List.all_eq_true] at h
  have := h t (List.mem_range.2 ht)
  rw [Bool.and_eq_true, V2.beq_iff] at this
  unfold vecAt vecO
  rw [this.2]

theorem hsep0 : ∀ g : Hj, (∀ t < (Array.range qLen).size,
    idx 15180 g (Array.range qLen)[t]! = (Array.range qLen)[t]!) → g = 1 := by
  intro g hg
  have hq := hF.qsize
  apply Subtype.ext
  apply eq_one_of_fix_qIdx0 hF (idx_Hj hF g.2)
  intro t ht
  have ht' : t < qLen := by rw [← hq]; exact ht
  have hfix := hg t (by rw [Array.size_range]; exact ht')
  rw [getElem!_pos _ t (by rw [Array.size_range]; exact ht'), Array.getElem_range] at hfix
  have hO := hF.o0Facts
  have h25 : t < 15180 := by unfold qLen at ht'; omega
  rw [idxO_eq_iff hO h25 h25] at hfix
  have hlt := qIdx0_lt hF t ht
  rw [idx_eq_iff hF.orbitFacts hlt hlt, vecAt_qIdx0 hF ht']
  exact hfix


end Chain

theorem card_Hj (hF : J4Facts) : Nat.card Hj = 501397585920 := hF.cardHj

end CFSG.Sporadic.J4
