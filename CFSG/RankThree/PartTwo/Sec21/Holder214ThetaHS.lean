module

public import CFSG.RankThree.PartTwo.Sec21.Holder214ThetaA8
public import CFSG.RankThree.Native.HSMcLAut
public import Certificates.Certificate799102

public section

namespace CFSG.RankThree.PartTwo.Sec21.Holder214Theta

open CFSG.Assembly (IsElemAbelian)
open CFSG.Blueprint
open CFSG.RankThree.PartTwo.KFacts
open CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Monster.B.Mathieu CFSG.Monster.B.Fischer CFSG.RankThree.Native CFSG.RankThree.PartOne
open Equiv Hering214Even
open scoped commutatorElement

section General

variable {G G' : Type*} [Group G] [Group G']

theorem F3At.congr_inf {K C K' C' E : Subgroup G} (h : K ⊓ C = K' ⊓ C') :
    F3At K E C ↔ F3At K' E C' := by
  rw [F3At, F3At, h]

theorem F3At.of_map_injective {f : G →* G'} (hf : Function.Injective f) {K E C : Subgroup G}
    (h : F3At (K.map f) (E.map f) (C.map f)) : F3At K E C := by
  have hD : ⁅K.map f ⊓ C.map f, K.map f ⊓ C.map f⁆ = ⁅K ⊓ C, K ⊓ C⁆.map f := by
    rw [← Subgroup.map_inf_eq _ _ _ hf, Subgroup.map_commutator]
  rw [F3At, hD] at h
  refine ⟨(Subgroup.map_le_map_iff_of_injective hf).mp h.1, fun P hP hPD hDN => ?_⟩
  have h' := h.2 (P.map f) (hP.map f) (Subgroup.map_mono hPD)
    ((Subgroup.map_mono hDN).trans (Subgroup.le_normalizer_map f))
  exact (Subgroup.map_eq_bot_iff_of_injective _ hf).mp h'

theorem map_centralizer_of_injective {f : G →* G'} (hf : Function.Injective f)
    (U : Subgroup G) :
    (Subgroup.centralizer (U : Set G)).map f =
      Subgroup.centralizer ((U.map f : Subgroup G') : Set G') ⊓ f.range := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_iff.mpr ?_,
      MonoidHom.mem_range.mpr ⟨y, rfl⟩⟩
    rintro _ ⟨u, hu, rfl⟩
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hy u hu]
  · intro hx
    obtain ⟨hxC, hxR⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨y, rfl⟩ := MonoidHom.mem_range.mp hxR
    refine ⟨y, Subgroup.mem_centralizer_iff.mpr fun u hu => hf ?_, rfl⟩
    rw [map_mul, map_mul]
    exact Subgroup.mem_centralizer_iff.mp hxC (f u) ⟨u, hu, rfl⟩

theorem map_conj_eq_self_of_mem {H : Subgroup G} {g : G} (hg : g ∈ H) :
    H.map (MulAut.conj g).toMonoidHom = H := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact H.mul_mem (H.mul_mem hg hy) (H.inv_mem hg)
  · intro hx
    refine ⟨g⁻¹ * x * g, H.mul_mem (H.mul_mem (H.inv_mem hg) hx) hg, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

theorem commutator_self_le (H : Subgroup G) : ⁅H, H⁆ ≤ H :=
  Subgroup.commutator_le.mpr fun x hx y hy => by
    rw [commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem hx hy) (H.inv_mem hx)) (H.inv_mem hy)


end General

section Kit

variable {n : ℕ}


variable {gD : Array (Array ℕ)} {ps : List ℕ} {cD : ArrCert} {c c' : Array ℕ}
  {C C' : Perm (Fin n)}


end Kit

noncomputable def hsC1 : Perm (Fin 100) := permOfArr 100 hsThC1

noncomputable def hsC2 : Perm (Fin 100) := permOfArr 100 hsThC2

noncomputable def hsV1 : Perm (Fin 100) := permOfArr 100 hsThV1

noncomputable def hsV2 : Perm (Fin 100) := permOfArr 100 hsThV2

noncomputable def hsV3 : Perm (Fin 100) := permOfArr 100 hsThV3

noncomputable def hsW (i : ℕ) : Perm (Fin 100) := permOfArr 100 (hsThArr (5 + i))

noncomputable def hsE0 : Subgroup (Perm (Fin 100)) := Subgroup.closure {hsC1, hsC2}


theorem hs_basic :
    hsC1 ∈ hs100P ∧ hsC2 ∈ hs100P ∧ hsC1 ^ 3 = 1 ∧ hsC2 ^ 3 = 1 ∧ hsC1 * hsC2 = hsC2 * hsC1 ∧
      hsC1 ≠ 1 ∧ hsC2 ≠ 1 ∧ hsC2 ≠ hsC1 ∧ hsC2 ≠ hsC1 ^ 2 ∧ hsV3 = hsV1 * hsV2 ∧
      (∀ i < 4, hsW i ∈ hs100P ∧ hsW i * hsV1 = hsV1 * hsW i ∧ hsW i * hsV2 = hsV2 * hsW i) ∧
      ⁅hsW 0, hsW 1⁆ = hsC1 ∧ ⁅hsW 2, hsW 3⁆ = hsC2 :=
  Certificates.certificate799102.1

theorem hsV3_eq : hsV3 = hsV1 * hsV2 := hs_basic.2.2.2.2.2.2.2.2.2.1

theorem card_hsE0 : Nat.card hsE0 = 9 := by
  obtain ⟨-, -, h3, h3', hc, h1, h2, h21, h22, -⟩ := hs_basic
  exact Asc83Table.card_closure_pair_eq_nine h3 h3' hc h1
    (Asc83Table.not_mem_zpowers_of_ne h3 h2 h21 h22)

theorem hsE0_le_P : hsE0 ≤ hs100P := by
  rw [hsE0, Subgroup.closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
  exact ⟨hs_basic.1, hs_basic.2.1⟩

noncomputable def hsBasis : Asc83Table.E9Basis ↥hs100P :=
  have h := hs_basic
  { a := ⟨hsC1, h.1⟩
    b := ⟨hsC2, h.2.1⟩
    ha := Subtype.ext h.2.2.1
    hb := Subtype.ext h.2.2.2.1
    hab := Subtype.ext h.2.2.2.2.1
    card := Asc83Table.card_closure_pair_eq_nine (Subtype.ext h.2.2.1) (Subtype.ext h.2.2.2.1)
      (Subtype.ext h.2.2.2.2.1) (fun e => h.2.2.2.2.2.1 (congrArg Subtype.val e))
      (Asc83Table.not_mem_zpowers_of_ne (Subtype.ext h.2.2.1)
        (fun e => h.2.2.2.2.2.2.1 (congrArg Subtype.val e))
        (fun e => h.2.2.2.2.2.2.2.1 (congrArg Subtype.val e))
        (fun e => h.2.2.2.2.2.2.2.2.1 (congrArg Subtype.val e))) }

theorem exists_conj_eq_of_card_nine_hs {A B : Subgroup (Perm (Fin 100))} (hA : A ≤ hs100P)
    (hB : B ≤ hs100P) (hA9 : Nat.card A = 9) (hB9 : Nat.card B = 9) :
    ∃ g ∈ hs100P, A.map (MulAut.conj g).toMonoidHom = B := by
  have hsyl : ∀ K : Subgroup (Perm (Fin 100)), K ≤ hs100P → Nat.card K = 9 →
      IsPGroup 3 (K.subgroupOf hs100P) ∧ ¬ 3 ∣ (K.subgroupOf hs100P).index := by
    intro K hK hK9
    have hc : Nat.card (K.subgroupOf hs100P) = 9 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK).toEquiv, hK9]
    refine ⟨IsPGroup.of_card (n := 2) (by rw [hc]; norm_num), fun h3 => ?_⟩
    have h := Subgroup.index_mul_card (H := K.subgroupOf hs100P)
    rw [hc, card_hs100P] at h
    have h' : (K.subgroupOf hs100P).index = 4928000 := by omega
    rw [h'] at h3
    norm_num at h3
  obtain ⟨hAp, hAi⟩ := hsyl A hA hA9
  obtain ⟨hBp, hBi⟩ := hsyl B hB hB9
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq hs100P (hAp.toSylow hAi) (hBp.toSylow hBi)
  have h := congrArg (fun S : Sylow 3 hs100P => (S : Subgroup hs100P)) hg
  simp only [Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe, Subgroup.pointwise_smul_def] at h
  have h' : (A.subgroupOf hs100P).map (MulAut.conj g).toMonoidHom = B.subgroupOf hs100P := h
  refine ⟨g, g.2, ?_⟩
  have h2 := congrArg (Subgroup.map hs100P.subtype) h'
  rw [Subgroup.map_map, Subgroup.subgroupOf_map_subtype, inf_of_le_left hB] at h2
  have hcomp : hs100P.subtype.comp (MulAut.conj g).toMonoidHom =
      (MulAut.conj (g : Perm (Fin 100))).toMonoidHom.comp hs100P.subtype :=
    MonoidHom.ext fun _ => rfl
  rw [← h2, hcomp, ← Subgroup.map_map, Subgroup.subgroupOf_map_subtype, inf_of_le_left hA]

theorem eq_v_of_centralizes {u : Perm (Fin 100)} (huR : u ∈ hs100R) (hu2 : u ^ 2 = 1)
    (hu1 : u * hsC1 = hsC1 * u) (hu2' : u * hsC2 = hsC2 * u) :
    u = 1 ∨ u = hsV1 ∨ u = hsV2 ∨ u = hsV3 :=
  Certificates.certificate799102.2.1 u huR hu2 hu1 hu2'

theorem hsW_mem {U : Subgroup (Perm (Fin 100))}
    (hUV : ∀ u ∈ U, u = 1 ∨ u = hsV1 ∨ u = hsV2 ∨ u = hsV3) {i : ℕ} (hi : i < 4) :
    hsW i ∈ hs100P ⊓ Subgroup.centralizer (U : Set (Perm (Fin 100))) := by
  obtain ⟨hP, h1, h2⟩ := hs_basic.2.2.2.2.2.2.2.2.2.2.1 i hi
  refine Subgroup.mem_inf.mpr ⟨hP, Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
  rcases hUV u hu with rfl | rfl | rfl | rfl
  · rw [one_mul, mul_one]
  · exact h1.symm
  · exact h2.symm
  · rw [hsV3_eq]
    exact ((Commute.mul_right h1 h2 : Commute (hsW i) (hsV1 * hsV2)).eq).symm

theorem hsE0_le_D {U : Subgroup (Perm (Fin 100))}
    (hUV : ∀ u ∈ U, u = 1 ∨ u = hsV1 ∨ u = hsV2 ∨ u = hsV3) :
    hsE0 ≤ ⁅hs100P ⊓ Subgroup.centralizer (U : Set (Perm (Fin 100))),
      hs100P ⊓ Subgroup.centralizer (U : Set (Perm (Fin 100)))⁆ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h01, h23⟩ := hs_basic
  rw [hsE0, Subgroup.closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
  refine ⟨?_, ?_⟩
  · rw [← h01]
    exact Subgroup.commutator_mem_commutator (hsW_mem hUV (by norm_num))
      (hsW_mem hUV (by norm_num))
  · rw [← h23]
    exact Subgroup.commutator_mem_commutator (hsW_mem hUV (by norm_num))
      (hsW_mem hUV (by norm_num))

theorem inf_centralizer_eq {U : Subgroup (Perm (Fin 100))} {S : Set (Perm (Fin 100))}
    (hSU : S ⊆ U) (hU : ∀ u ∈ U, ∀ x : Perm (Fin 100), (∀ s ∈ S, s * x = x * s) → u * x = x * u) :
    hs100P ⊓ Subgroup.centralizer (U : Set (Perm (Fin 100))) =
      hs100P ⊓ Subgroup.centralizer S := by
  ext x
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, SetLike.mem_coe]
  exact ⟨fun h => ⟨h.1, fun s hs => h.2 s (hSU hs)⟩, fun h => ⟨h.1, fun u hu => hU u hu x h.2⟩⟩

theorem f3At_hs_e0 {U : Subgroup (Perm (Fin 100))} (hUR : U ≤ hs100R)
    (hU2 : ∀ u ∈ U, u ^ 2 = 1) (hU1 : U ≠ ⊥)
    (hcomm : ∀ u ∈ U, u * hsC1 = hsC1 * u ∧ u * hsC2 = hsC2 * u) :
    F3At hs100P hsE0 (Subgroup.centralizer (U : Set (Perm (Fin 100)))) := by
  have hUV : ∀ u ∈ U, u = 1 ∨ u = hsV1 ∨ u = hsV2 ∨ u = hsV3 := fun u hu =>
    eq_v_of_centralizes (hUR hu) (hU2 u hu) (hcomm u hu).1 (hcomm u hu).2
  refine ⟨hsE0_le_D hUV, fun Q hQ hQD hDN => ?_⟩
  have sq1 : ∀ v ∈ U, v * v = 1 := fun v hv => by rw [← sq]; exact hU2 v hv
  have hc3 : ∀ x : Perm (Fin 100), hsV1 * x = x * hsV1 → hsV2 * x = x * hsV2 →
      hsV3 * x = x * hsV3 := fun x h1 h2 => by
    rw [hsV3_eq, mul_assoc, h2, ← mul_assoc, h1, mul_assoc]
  have hS : ∀ {S : Set (Perm (Fin 100))}, S ⊆ U →
      (∀ u ∈ U, ∀ x : Perm (Fin 100), (∀ s ∈ S, s * x = x * s) → u * x = x * u) →
      (∀ Q : Subgroup (Perm (Fin 100)), IsPGroup 2 Q →
        Q ≤ ⁅hs100P ⊓ Subgroup.centralizer S, hs100P ⊓ Subgroup.centralizer S⁆ →
        ⁅hs100P ⊓ Subgroup.centralizer S, hs100P ⊓ Subgroup.centralizer S⁆ ≤
          Subgroup.normalizer (Q : Set (Perm (Fin 100))) → Q = ⊥) → Q = ⊥ := by
    intro S hSU hU h
    rw [inf_centralizer_eq hSU hU] at hQD hDN
    exact h Q hQ hQD hDN
  have h12 : hs100P ⊓ Subgroup.centralizer {hsV1, hsV2} =
      hs100P ⊓ Subgroup.centralizer {hsV1} ⊓ Subgroup.centralizer {hsV2} := by
    ext x
    simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Set.mem_insert_iff,
      Set.mem_singleton_iff, forall_eq_or_imp, forall_eq, and_assoc]
  by_cases h1 : hsV1 ∈ U <;> by_cases h2 : hsV2 ∈ U
  · refine hS (S := {hsV1, hsV2}) (Set.insert_subset_iff.2 ⟨h1, Set.singleton_subset_iff.2 h2⟩)
      (fun u hu x hx => ?_) ?_
    · have hx1 := hx hsV1 (Set.mem_insert _ _)
      have hx2 := hx hsV2 (Set.mem_insert_of_mem _ rfl)
      rcases hUV u hu with rfl | rfl | rfl | rfl
      · rw [one_mul, mul_one]
      · exact hx1
      · exact hx2
      · exact hc3 x hx1 hx2
    · rw [h12]
      exact Certificates.certificate799102.2.2.2.2.2
  · have h3 : hsV3 ∉ U := fun h3 => h2 (by
      have := U.mul_mem h1 h3
      rwa [hsV3_eq, ← mul_assoc, sq1 _ h1, one_mul] at this)
    refine hS (S := {hsV1}) (Set.singleton_subset_iff.2 h1) (fun u hu x hx => ?_)
      Certificates.certificate799102.2.2.1
    rcases hUV u hu with rfl | rfl | rfl | rfl
    · rw [one_mul, mul_one]
    · exact hx _ rfl
    · exact absurd hu h2
    · exact absurd hu h3
  · have h3 : hsV3 ∉ U := fun h3 => h1 (by
      have := U.mul_mem h3 h2
      rwa [hsV3_eq, mul_assoc, sq1 _ h2, mul_one] at this)
    refine hS (S := {hsV2}) (Set.singleton_subset_iff.2 h2) (fun u hu x hx => ?_)
      Certificates.certificate799102.2.2.2.1
    rcases hUV u hu with rfl | rfl | rfl | rfl
    · rw [one_mul, mul_one]
    · exact absurd hu h1
    · exact hx _ rfl
    · exact absurd hu h3
  · obtain ⟨⟨u, hu⟩, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hU1
    have hu1' : u ≠ 1 := fun h => hu1 (Subtype.ext h)
    have h3 : hsV3 ∈ U := by
      rcases hUV u hu with rfl | rfl | rfl | rfl
      · exact absurd rfl hu1'
      · exact absurd hu h1
      · exact absurd hu h2
      · exact hu
    refine hS (S := {hsV3}) (Set.singleton_subset_iff.2 h3) (fun u hu x hx => ?_)
      Certificates.certificate799102.2.2.2.2.1
    rcases hUV u hu with rfl | rfl | rfl | rfl
    · rw [one_mul, mul_one]
    · exact absurd hu h1
    · exact absurd hu h2
    · exact hx _ rfl

theorem f3At_hs {E U : Subgroup (Perm (Fin 100))} (hEP : E ≤ hs100P) (hE : Nat.card E = 9)
    (hUR : U ≤ hs100R) (hU2 : ∀ u ∈ U, u ^ 2 = 1) (hU1 : U ≠ ⊥)
    (hcomm : ∀ u ∈ U, ∀ e ∈ E, u * e = e * u) :
    F3At hs100P E (Subgroup.centralizer (U : Set (Perm (Fin 100)))) := by
  obtain ⟨g, hgP, hg⟩ := exists_conj_eq_of_card_nine_hs hsE0_le_P hEP card_hsE0 hE
  have hU'm : (U.comap (MulAut.conj g).toMonoidHom).map (MulAut.conj g).toMonoidHom = U :=
    Subgroup.map_comap_eq_self_of_surjective (f := (MulAut.conj g).toMonoidHom)
      (MulAut.conj g).surjective U
  have hgc : ∀ c ∈ hsE0, MulAut.conj g c ∈ E := fun c hc => hg ▸ ⟨c, hc, rfl⟩
  have hF := (f3At_hs_e0 (U := U.comap (MulAut.conj g).toMonoidHom) ?_ ?_ ?_ ?_).map
    (MulAut.conj g)
  · rwa [map_conj_eq_self_of_mem hgP, hg, map_centralizer_equiv, hU'm] at hF
  · intro x hx
    have hxR : MulAut.conj g x ∈ hs100R := hUR hx
    have hgR := hs100P_le_R hgP
    have e : x = g⁻¹ * MulAut.conj g x * g := by
      rw [MulAut.conj_apply]
      group
    rw [e]
    exact hs100R.mul_mem (hs100R.mul_mem (hs100R.inv_mem hgR) hxR) hgR
  · intro x hx
    exact (MulAut.conj g).injective (by rw [map_pow, map_one]; exact hU2 _ hx)
  · intro h
    exact hU1 (by rw [← hU'm, h, Subgroup.map_bot])
  · intro x hx
    have hc1 := hgc _ (Subgroup.subset_closure (Set.mem_insert _ _))
    have hc2 := hgc _ (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))
    exact ⟨(MulAut.conj g).injective (by rw [map_mul, map_mul]; exact hcomm _ hx _ hc1),
      (MulAut.conj g).injective (by rw [map_mul, map_mul]; exact hcomm _ hx _ hc2)⟩


theorem evenThetaFacts_hs100P : EvenThetaFacts ↥hs100P := by
  obtain ⟨-, -, ⟨ψ, hψ, -⟩, -, -, -, -, hcardR⟩ := automorphism_model_of hs100R_eq_sup
    hs100U_sq hs100U_not_mem_P (fun p hp => hs100U_conj_mem hp) centralizer_hs100P
    outer_card_hs100P
  have hZ : Subgroup.center ↥hs100P = ⊥ := center_eq_bot_of_centralizer centralizer_hs100P
  have hAut : Nat.card (MulAut ↥hs100P) ≤ 2 * Nat.card ↥hs100P := by
    rw [← Nat.card_congr ψ.toEquiv, hcardR]
  set ι : MulAut ↥hs100P →* Perm (Fin 100) := hs100R.subtype.comp ψ.symm.toMonoidHom with hι
  have hιinj : Function.Injective ι := hs100R.subtype_injective.comp ψ.symm.injective
  have hψc : ∀ p : ↥hs100P, ψ ⟨p, hs100P_le_R p.2⟩ = MulAut.conj p := fun p =>
    MulEquiv.ext fun q => Subtype.ext (by rw [hψ]; rfl)
  have hιc : ∀ p : ↥hs100P, ι (MulAut.conj p) = p := fun p => by
    rw [hι, MonoidHom.comp_apply, ← hψc p]
    simp
  have hInn : (MulAut.conj : ↥hs100P →* MulAut ↥hs100P).range.map ι = hs100P := by
    ext x
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨σ, hσ, rfl⟩
      obtain ⟨p, rfl⟩ := MonoidHom.mem_range.mp hσ
      rw [hιc]
      exact p.2
    · intro hx
      exact ⟨MulAut.conj ⟨x, hx⟩, MonoidHom.mem_range.mpr ⟨⟨x, hx⟩, rfl⟩, hιc ⟨x, hx⟩⟩
  have hrange : ι.range = hs100R := by
    ext x
    rw [MonoidHom.mem_range]
    constructor
    · rintro ⟨σ, rfl⟩
      exact (ψ.symm σ).2
    · intro hx
      exact ⟨ψ ⟨x, hx⟩, by simp [hι]⟩
  refine ⟨hZ, fun σ hσ => ?_, exists_e9_of_e9Basis hsBasis (MulEquiv.refl _), ?_⟩
  · obtain ⟨y, rfl⟩ := KS14.exists_conj_of_card_mulAut_le hZ hAut σ
      ⟨1, by rw [pow_one]; exact hσ⟩
    exact MonoidHom.mem_range.mpr ⟨y, rfl⟩
  · intro Ē Ū hĒ _ hĒ9 hŪ hŪ1 _ hcomm
    have hF := f3At_hs (E := Ē.map ι) (U := Ū.map ι) ((Subgroup.map_mono hĒ).trans hInn.le)
      (by rw [Subgroup.card_map_of_injective hιinj, hĒ9])
      ((Subgroup.map_le_range ι Ū).trans hrange.le)
      (by
        rintro _ ⟨u, hu, rfl⟩
        rw [← map_pow, hŪ.2 u hu, map_one])
      (fun h => hŪ1 ((Subgroup.map_eq_bot_iff_of_injective _ hιinj).mp h))
      (by
        rintro _ ⟨u, hu, rfl⟩ _ ⟨e, he, rfl⟩
        rw [← map_mul, ← map_mul, hcomm u hu e he])
    have hF' : F3At ((MulAut.conj : ↥hs100P →* MulAut ↥hs100P).range.map ι) (Ē.map ι)
        ((Subgroup.centralizer (Ū : Set (MulAut ↥hs100P))).map ι) := by
      rw [hInn, map_centralizer_of_injective hιinj, hrange]
      refine (F3At.congr_inf ?_).mpr hF
      rw [inf_comm _ hs100R, ← inf_assoc, inf_of_le_left hs100P_le_R]
    exact F3At.of_map_injective hιinj hF'


theorem evenThetaFacts_of_hs {X : Type} [Group X] (hX : Nonempty (X ≃* NativeSporadic.HS)) :
    EvenThetaFacts X := by
  obtain ⟨e⟩ := hX
  exact evenThetaFacts_of_mulEquiv (e.trans hs100Equiv) evenThetaFacts_hs100P

end CFSG.RankThree.PartTwo.Sec21.Holder214Theta
