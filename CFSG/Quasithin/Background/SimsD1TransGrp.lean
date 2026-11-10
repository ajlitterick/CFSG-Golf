module

public import CFSG.Quasithin.Background.D1Statement
public import CFSG.LocalAnalysis.SectionRank.NativeKGroup
public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.Quasithin.SimsD1.TransGrp

open CFSG.Open CFSG.QuasithinUnique

section General

variable {A B : Type*} [Group A] [Group B]

theorem map_comap_of_le_map (f : A →* B) {H : Subgroup A} {K : Subgroup B} (h : K ≤ H.map f) :
    (K.comap f).map f = K :=
  Subgroup.map_comap_eq_self (h.trans (Subgroup.map_le_range f H))

theorem exists_map_eq_of_le_map (f : A →* B) {H : Subgroup A} {K : Subgroup B}
    (h : K ≤ H.map f) : ∃ L : Subgroup A, L.map f = K :=
  ⟨K.comap f, map_comap_of_le_map f h⟩

theorem comap_le_of_le_map (f : A →* B) (hf : Function.Injective f) {H : Subgroup A}
    {K : Subgroup B} (h : K ≤ H.map f) : K.comap f ≤ H := by
  have := Subgroup.comap_mono (f := f) h
  rwa [Subgroup.comap_map_eq_self_of_injective hf] at this

theorem mem_centralizer_map_iff (f : A →* B) (hf : Function.Injective f) (X : Subgroup A)
    (a : A) :
    f a ∈ Subgroup.centralizer ((X.map f : Subgroup B) : Set B) ↔
      a ∈ Subgroup.centralizer (X : Set A) := by
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h x hx
    apply hf
    rw [map_mul, map_mul]
    exact h (f x) ⟨x, hx, rfl⟩
  · rintro h _ ⟨x, hx, rfl⟩
    rw [← map_mul, ← map_mul, h x hx]

theorem mem_normalizer_map_iff (f : A →* B) (hf : Function.Injective f) (X : Subgroup A)
    (a : A) :
    f a ∈ Subgroup.normalizer ((X.map f : Subgroup B) : Set B) ↔
      a ∈ Subgroup.normalizer (X : Set A) := by
  have h := Subgroup.comap_normalizer_eq_of_le_range (H := X.map f) (f := f)
    (Subgroup.map_le_range f X)
  rw [Subgroup.comap_map_eq_self_of_injective hf] at h
  rw [← Subgroup.mem_comap, h]

theorem map_inf_centralizer_eq (f : A →* B) (hf : Function.Injective f) (K X : Subgroup A) :
    (K ⊓ Subgroup.centralizer (X : Set A)).map f =
      K.map f ⊓ Subgroup.centralizer ((X.map f : Subgroup B) : Set B) := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_inf]
  constructor
  · rintro ⟨a, ⟨haK, haC⟩, rfl⟩
    exact ⟨⟨a, haK, rfl⟩, (mem_centralizer_map_iff f hf X a).2 haC⟩
  · rintro ⟨⟨a, haK, rfl⟩, hC⟩
    exact ⟨a, ⟨haK, (mem_centralizer_map_iff f hf X a).1 hC⟩, rfl⟩

theorem le_normalizer_map_iff (f : A →* B) (hf : Function.Injective f) (H X : Subgroup A) :
    H.map f ≤ Subgroup.normalizer ((X.map f : Subgroup B) : Set B) ↔
      H ≤ Subgroup.normalizer (X : Set A) := by
  rw [Subgroup.map_le_iff_le_comap]
  exact ⟨fun h a ha => (mem_normalizer_map_iff f hf X a).1 (h ha),
    fun h a ha => (mem_normalizer_map_iff f hf X a).2 (h ha)⟩


theorem pCoreOf_map_eq (f : A →* B) (hf : Function.Injective f) (p : ℕ) (K : Subgroup A) :
    pCoreOf p (K.map f) = (pCoreOf p K).map f := by
  let e : ↥K ≃* ↥(K.map f) := K.equivMapOfInjective f hf
  have h1 := CFSG.LieType.BorelTits.map_pCore_mulEquiv p e
  unfold pCoreOf
  rw [← h1, Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem isPGroup_map_iff (f : A →* B) (hf : Function.Injective f) (p : ℕ) (K : Subgroup A) :
    IsPGroup p ↥(K.map f) ↔ IsPGroup p ↥K :=
  ⟨fun h => h.of_equiv (K.equivMapOfInjective f hf).symm,
    fun h => h.of_equiv (K.equivMapOfInjective f hf)⟩

theorem isElemAbelian_map_iff (f : A →* B) (hf : Function.Injective f) (p : ℕ)
    (K : Subgroup A) : IsElemAbelian p (K.map f) ↔ IsElemAbelian p K :=
  ⟨fun h => by
    simpa [Subgroup.comap_map_eq_self_of_injective hf] using IsElemAbelian.comap h hf,
    fun h => h.map f⟩

theorem isMaxElemAbelian_map_iff (f : A →* B) (hf : Function.Injective f) (H C : Subgroup A) :
    IsMaxElemAbelian (H.map f) (C.map f) ↔ IsMaxElemAbelian H C := by
  constructor
  · rintro ⟨hCH, hCE, hmax⟩
    refine ⟨(Subgroup.map_le_map_iff_of_injective hf).1 hCH,
      (isElemAbelian_map_iff f hf 2 C).1 hCE, fun K hKH hKE => ?_⟩
    have h := hmax (K.map f) (Subgroup.map_mono hKH) ((isElemAbelian_map_iff f hf 2 K).2 hKE)
    rwa [Subgroup.card_map_of_injective hf, Subgroup.card_map_of_injective hf] at h
  · rintro ⟨hCH, hCE, hmax⟩
    refine ⟨Subgroup.map_mono hCH, (isElemAbelian_map_iff f hf 2 C).2 hCE, fun K hKH hKE => ?_⟩
    have h1 := map_comap_of_le_map f hKH
    have hKE' : IsElemAbelian 2 (K.comap f) :=
      (isElemAbelian_map_iff f hf 2 (K.comap f)).1 (by rw [h1]; exact hKE)
    have h2 := hmax (K.comap f) (comap_le_of_le_map f hf hKH) hKE'
    rw [Subgroup.card_map_of_injective hf]
    calc Nat.card ↥K = Nat.card ↥((K.comap f).map f) := by rw [h1]
      _ = Nat.card ↥(K.comap f) := Subgroup.card_map_of_injective hf
      _ ≤ Nat.card ↥C := h2

theorem eq_map_comap_of_isMaxElemAbelian (f : A →* B) {H : Subgroup A} {D : Subgroup B}
    (hD : IsMaxElemAbelian (H.map f) D) : D = (D.comap f).map f :=
  (map_comap_of_le_map f hD.1).symm

theorem isMaxElemAbelian_map_iff_exists (f : A →* B) (hf : Function.Injective f)
    (H : Subgroup A) (D : Subgroup B) :
    IsMaxElemAbelian (H.map f) D ↔ ∃ C : Subgroup A, IsMaxElemAbelian H C ∧ C.map f = D := by
  constructor
  · intro hD
    refine ⟨D.comap f, ?_, (eq_map_comap_of_isMaxElemAbelian f hD).symm⟩
    have := hD
    rw [eq_map_comap_of_isMaxElemAbelian f hD] at this
    exact (isMaxElemAbelian_map_iff f hf H _).1 this
  · rintro ⟨C, hC, rfl⟩
    exact (isMaxElemAbelian_map_iff f hf H C).2 hC

theorem thompsonJ_map_eq (f : A →* B) (hf : Function.Injective f) (H : Subgroup A) :
    thompsonJ (H.map f) = (thompsonJ H).map f := by
  unfold thompsonJ
  rw [Subgroup.map_iSup]
  simp only [Subgroup.map_iSup]
  refine le_antisymm (iSup₂_le fun D hD => ?_) (iSup₂_le fun C hC => ?_)
  · obtain ⟨C, hC, rfl⟩ := (isMaxElemAbelian_map_iff_exists f hf H D).1 hD
    exact le_iSup₂_of_le C hC le_rfl
  · exact le_iSup₂_of_le (C.map f) ((isMaxElemAbelian_map_iff f hf H C).2 hC) le_rfl


theorem centerOf_map_eq (f : A →* B) (hf : Function.Injective f) (K : Subgroup A) :
    centerOf (K.map f) = (centerOf K).map f :=
  (map_inf_centralizer_eq f hf K K).symm

theorem relIndex_map_eq (f : A →* B) (hf : Function.Injective f) (K L : Subgroup A) :
    (K.map f).relIndex (L.map f) = K.relIndex L :=
  Subgroup.relIndex_map_map_of_injective K L hf

theorem twoResidual_map_eq (f : A →* B) (hf : Function.Injective f) (H : Subgroup A) :
    twoResidual (H.map f) = (twoResidual H).map f := by
  ext y
  constructor
  · intro hy
    obtain ⟨x, hxH, rfl⟩ : y ∈ H.map f := twoResidual_le _ hy
    refine ⟨x, mem_twoResidual_iff.2 fun N hNH hHN hpow => ?_, rfl⟩
    refine (Subgroup.mem_map_iff_mem hf).1
      (mem_twoResidual_iff.1 hy (N.map f) (Subgroup.map_mono hNH)
        ((le_normalizer_map_iff f hf H N).2 hHN) ?_)
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨k, hk⟩ := hpow z hz
    exact ⟨k, by rw [← map_pow]; exact ⟨_, hk, rfl⟩⟩
  · rintro ⟨x, hx, rfl⟩
    rw [mem_twoResidual_iff]
    intro N' hN'H hHN' hpow
    obtain ⟨N, rfl⟩ := exists_map_eq_of_le_map f hN'H
    refine ⟨x, ?_, rfl⟩
    refine mem_twoResidual_iff.1 hx N ((Subgroup.map_le_map_iff_of_injective hf).1 hN'H)
      ((le_normalizer_map_iff f hf H N).1 hHN') (fun z hz => ?_)
    obtain ⟨k, hk⟩ := hpow (f z) ⟨z, hz, rfl⟩
    exact ⟨k, (Subgroup.mem_map_iff_mem hf).1 (by rwa [← map_pow] at hk)⟩


theorem isSylowTwoOf_map_iff (f : A →* B) (hf : Function.Injective f) (S H : Subgroup A) :
    IsSylowTwoOf (S.map f) (H.map f) ↔ IsSylowTwoOf S H := by
  unfold IsSylowTwoOf
  rw [Subgroup.map_le_map_iff_of_injective hf, isPGroup_map_iff f hf]
  have h : ((S.map f).subgroupOf (H.map f)).index = (S.subgroupOf H).index :=
    relIndex_map_eq f hf S H
  rw [h]

theorem exists_isSylowTwoOf_of_map (f : A →* B) (hf : Function.Injective f) (H : Subgroup A)
    {S' : Subgroup B} (h : IsSylowTwoOf S' (H.map f)) :
    ∃ S : Subgroup A, S.map f = S' ∧ IsSylowTwoOf S H := by
  obtain ⟨S, rfl⟩ := exists_map_eq_of_le_map f h.1
  exact ⟨S, rfl, (isSylowTwoOf_map_iff f hf S H).1 h⟩

theorem isMaxSubgroupIn_map_iff (f : A →* B) (hf : Function.Injective f) (H N : Subgroup A) :
    IsMaxSubgroupIn (H.map f) (N.map f) ↔ IsMaxSubgroupIn H N := by
  unfold IsMaxSubgroupIn
  rw [Subgroup.map_lt_map_iff_of_injective hf]
  refine and_congr_right fun _ => ?_
  constructor
  · intro h K hNK hKH
    exact Subgroup.map_injective hf
      (h (K.map f) ((Subgroup.map_lt_map_iff_of_injective hf).2 hNK) (Subgroup.map_mono hKH))
  · intro h K' hNK hKH
    obtain ⟨K, rfl⟩ := exists_map_eq_of_le_map f hKH
    rw [Subgroup.map_lt_map_iff_of_injective hf] at hNK
    rw [h K hNK ((Subgroup.map_le_map_iff_of_injective hf).1 hKH)]

theorem maxOver_map_eq (f : A →* B) (hf : Function.Injective f) (H X : Subgroup A) :
    maxOver (H.map f) (X.map f) = Subgroup.map f '' maxOver H X := by
  ext N'
  constructor
  · rintro ⟨hmax, hX⟩
    obtain ⟨N, rfl⟩ := exists_map_eq_of_le_map f hmax.1.le
    exact ⟨N, ⟨(isMaxSubgroupIn_map_iff f hf H N).1 hmax,
      (Subgroup.map_le_map_iff_of_injective hf).1 hX⟩, rfl⟩
  · rintro ⟨N, ⟨hmax, hX⟩, rfl⟩
    exact ⟨(isMaxSubgroupIn_map_iff f hf H N).2 hmax, Subgroup.map_mono hX⟩

theorem isUniqueMaxOver_map_iff (f : A →* B) (hf : Function.Injective f) (H T M : Subgroup A) :
    IsUniqueMaxOver (H.map f) (T.map f) (M.map f) ↔ IsUniqueMaxOver H T M := by
  unfold IsUniqueMaxOver
  rw [maxOver_map_eq f hf, ← Set.image_singleton,
    (Subgroup.map_injective hf).image_injective.eq_iff]


theorem charTwo_map_iff (f : A →* B) (hf : Function.Injective f) (H : Subgroup A) :
    CharTwo (H.map f) ↔ CharTwo H := by
  unfold CharTwo
  rw [pCoreOf_map_eq f hf, ← map_inf_centralizer_eq f hf,
    Subgroup.map_le_map_iff_of_injective hf]


end General

section Iso


end Iso

section SQTK


end SQTK

end CFSG.Quasithin.SimsD1.TransGrp
