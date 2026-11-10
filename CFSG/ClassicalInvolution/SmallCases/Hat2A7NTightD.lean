module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7NTightC

public section

namespace CFSG.ClassicalInvolution.Hat2A7N

open CFSG.Open CFSG.ClassicalInvolution.Hat2A7

section Sylow

variable {F : Type} [Group F] [Finite F] {K : Subgroup F} {z : F}

theorem TightSettingN.conj_mem_Zset_of_sylow (S : TightSettingN F K z) {T : Subgroup F}
    (hT : IsPGroup 2 T) (Qs : Sylow 2 ↥K)
    (hQT : (Qs : Subgroup ↥K).map K.subtype ≤ T) {g : F}
    (hg : ((Qs : Subgroup ↥K).map K.subtype).map (MulAut.conj g).toMonoidHom ≤ T) :
    g * z * g⁻¹ ∈ Zset K z := by
  have hKz := S.tight.classical
  have hzQ : z ∈ (Qs : Subgroup ↥K).map K.subtype := hKz.mem_sylow Qs
  have hgz : g * z * g⁻¹ ∈ classOf z := ⟨g, rfl⟩
  have hgzQ : g * z * g⁻¹ ∈ ((Qs : Subgroup ↥K).map K.subtype).map (MulAut.conj g).toMonoidHom :=
    ⟨z, hzQ, rfl⟩
  by_cases hne : ((Qs : Subgroup ↥K).map K.subtype).map (MulAut.conj g).toMonoidHom =
      (Qs : Subgroup ↥K).map K.subtype
  ·
    rw [hne] at hgzQ
    have hgzK : g * z * g⁻¹ ∈ K := by
      obtain ⟨y, _, hy⟩ := hgzQ
      rw [← hy]; exact y.2
    have : g * z * g⁻¹ = z := hKz.eq_of_orderOf_eq_two hgzK
      (orderOf_eq_two_of_mem_classOf S.tight hgz)
    rw [this]
    exact S.self_mem_Zset
  · have hcomm := commute_of_conj_sylow hKz.orderOf_eq_two hKz.le_centralizer S.tight.tight Qs
      (exists_quaternion_sylow_of_witness hKz.witness Qs) hzQ hT hQT hg hne
    have hcentK : ∀ q' ∈ ((Qs : Subgroup ↥K).map K.subtype).map (MulAut.conj g).toMonoidHom,
        ∀ k ∈ K, k * q' = q' * k := by
      intro q' hq' k hk
      have hq'z : z * q' = q' * z := (hcomm q' hq' z hzQ).symm
      have hq'N : q' ∈ Subgroup.normalizer (K : Set F) := S.tight.tight (by
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        rw [hh]; exact hq'z)
      have htriv := oddQuotAut_conjOn_eq_one hKz.witness Qs hq'N (fun q hq => by
        have := hcomm q' hq' (q : F) ⟨q, hq, rfl⟩
        exact this)
      exact centralizes_of_oddQuotAut_eq_one hKz.perfect (S.P1 K z (IsConjSubgroup.refl K) hKz)
        hq'N htriv k hk
    have hKw : memb K z z ≤ Subgroup.centralizer ({g * z * g⁻¹} : Set F) := by
      rw [memb_self S.tight]
      intro k hk
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]; exact (hcentK _ hgzQ k hk).symm
    have hLw : memb K z (g * z * g⁻¹) ≤ Subgroup.centralizer ({g * z * g⁻¹} : Set F) :=
      (S.tight.memb hgz).classical.le_centralizer
    have h := S.commOrEq_of_le_centralizer (orderOf_eq_two_of_mem_classOf S.tight hgz)
      (isCommProd_of_mem_classOf hgz) (mem_classOf_self z) hgz hKw hLw
    rw [memb_self S.tight] at h
    exact ⟨hgz, h⟩

end Sylow

section Strong

variable {F : Type} [Group F] [Finite F] {K : Subgroup F} {z : F}

omit [Finite F] in
theorem TightSettingN.Zset_rebase_eq (S : TightSettingN F K z) {x : F} (hx : x ∈ classOf z) :
    Zset (memb K z x) x =
      {u | u ∈ classOf z ∧ CommOrEq (memb K z x) (memb K z u)} := by
  ext u
  have hclass : classOf x = classOf z := classOf_eq_of_mem hx
  constructor
  · rintro ⟨hu, hc⟩
    have hu' : u ∈ classOf z := by rwa [hclass] at hu
    rw [memb_memb S.tight hx hu'] at hc
    exact ⟨hu', hc⟩
  · rintro ⟨hu, hc⟩
    refine ⟨by rw [hclass]; exact hu, ?_⟩
    rw [memb_memb S.tight hx hu]
    exact hc

omit [Finite F] in
theorem TightSettingN.Zset_rebase (S : TightSettingN F K z) {w : F} (hw : w ∈ Zset K z) :
    Zset (memb K z w) w = Zset K z := by
  rw [S.Zset_rebase_eq hw.1]
  ext u
  constructor
  · rintro ⟨hu, hc⟩
    refine ⟨hu, ?_⟩
    have h1 : CommOrEq (memb K z z) (memb K z w) := by rw [memb_self S.tight]; exact hw.2
    have := S.commOrEq_trans (mem_classOf_self z) hw.1 hu h1 hc
    rwa [memb_self S.tight] at this
  · rintro ⟨hu, hc⟩
    refine ⟨hu, ?_⟩
    have h1 : CommOrEq (memb K z w) (memb K z z) := by rw [memb_self S.tight]; exact hw.2.symm
    have h2 : CommOrEq (memb K z z) (memb K z u) := by rw [memb_self S.tight]; exact hc
    exact S.commOrEq_trans hw.1 (mem_classOf_self z) hu h1 h2


theorem TightSettingN.mem_normalizer_of_sylow (S : TightSettingN F K z) {R : Subgroup F}
    (hR : ABGLocalTools.IsSylowOf 2 R (cliqueSub K z)) {T : Subgroup F} (hT : IsPGroup 2 T)
    (hRT : R ≤ T) : ∀ s ∈ T, s ∈ Subgroup.normalizer (Zset K z) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have key : ∀ s ∈ T, ∀ n ∈ Zset K z, s * n * s⁻¹ ∈ Zset K z := by
    intro s hs n hn
    have hSyl := hR.inf_of_le_normalizer (memb_le_cliqueSub hn) (S.cliqueSub_le_normalizer hn)
    obtain ⟨Qs, hQs⟩ := hSyl
    have hQT : (Qs : Subgroup ↥(memb K z n)).map (memb K z n).subtype ≤ T := by
      rw [hQs]; exact inf_le_left.trans hRT
    have hconj : ((Qs : Subgroup ↥(memb K z n)).map (memb K z n).subtype).map
        (MulAut.conj s).toMonoidHom ≤ T := by
      rintro _ ⟨y, hy, rfl⟩
      exact T.mul_mem (T.mul_mem hs (hQT hy)) (T.inv_mem hs)
    have := (S.rebase hn.1).conj_mem_Zset_of_sylow hT Qs hQT hconj
    rwa [S.Zset_rebase hn] at this
  intro s hs
  rw [Subgroup.mem_set_normalizer_iff]
  intro n
  refine ⟨key s hs n, fun hsn => ?_⟩
  have := key s⁻¹ (T.inv_mem hs) _ hsn
  simpa [mul_assoc] using this


end Strong

end CFSG.ClassicalInvolution.Hat2A7N
