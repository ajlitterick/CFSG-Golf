module

public import CFSG.Quasithin.Background.HLUCode24Gen
public import CFSG.Quasithin.Background.HZCoc24Pack
public import CFSG.Quasithin.AppendixH.H16.MaskChief

public section

namespace CFSG.ASVolI.H16.SxPack

open CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.LU24
  CFSG.Quasithin.H.Coc24Pack

@[expose] def allLt (f : ℕ → Bool) (n : ℕ) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun k acc => Bool.rec false acc (f k)) n


theorem of_allLt {f : ℕ → Bool} : ∀ {n : ℕ}, allLt f n = true → ∀ k < n, f k = true
  | 0, _, k, hk => absurd hk (Nat.not_lt_zero k)
  | n + 1, h, k, hk => by
    have h' : Bool.rec false (allLt f n) (f n) = true := h
    cases hf : f n
    · rw [hf] at h'
      exact absurd h' Bool.false_ne_true
    · rw [hf] at h'
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
      · exact of_allLt h' k hk
      · exact hf


@[expose] def g1K : ℕ := 897641350104222698714232081601768518

@[expose] def g2K : ℕ := 187140310991371938096741885074749127

@[expose] def tK : ℕ := 210612956321353997592989794072419700

@[expose] def tiK : ℕ := 100398093789040343632513102951832020

theorem codes_dec : sxG1Arr = dec g1K ∧ sxG2Arr = dec g2K ∧ sxTArr = dec tK ∧ sxTInv = dec tiK := by
  unfold dec
  decide +kernel

@[expose] def ksK (i : ℕ) : ℕ := wK [g1K, g2K] (ksWord6 i)

theorem ks6Arr_dec (i : ℕ) : ks6Arr i = dec (ksK i) := by
  rw [ks6Arr, codes_dec.1, codes_dec.2.1, ksK, ← wArr_dec]
  rfl

theorem ks6_list : (List.range 6).map ks6Arr = ((List.range 6).map ksK).map dec := by
  rw [List.map_map]
  exact List.map_congr_left fun i _ => ks6Arr_dec i

@[expose] def conjB (S S' : ℕ → ℕ) (i : ℕ) : Bool :=
  Bool.rec false
    (Nat.beq (cK (cK tiK (ksK i)) tK) (wK ((List.range 6).map ksK) (subW (S' i))))
    (Nat.beq (cK (cK tK (ksK i)) tiK) (wK ((List.range 6).map ksK) (subW (S i))))

theorem conj_of_conjB (S S' : ℕ → ℕ) (h : allLt (conjB S S') 6 = true) : ∀ i < 6,
    cArr (cArr sxTArr (ks6Arr i)) sxTInv = wArr ((List.range 6).map ks6Arr) (subW (S i)) ∧
      cArr (cArr sxTInv (ks6Arr i)) sxTArr = wArr ((List.range 6).map ks6Arr) (subW (S' i)) := by
  intro i hi
  have hb' := of_allLt h i hi
  unfold conjB at hb'
  obtain ⟨_, _, hT, hTi⟩ := codes_dec
  rw [ks6_list, hT, hTi, ks6Arr_dec, wArr_dec, wArr_dec, cArr_dec, cArr_dec, cArr_dec, cArr_dec]
  cases h1 : Nat.beq (cK (cK tK (ksK i)) tiK) (wK ((List.range 6).map ksK) (subW (S i)))
  · rw [h1] at hb'
    exact absurd hb' Bool.false_ne_true
  · rw [h1] at hb'
    exact ⟨dec_inj (Nat.eq_of_beq_eq_true h1), dec_inj (Nat.eq_of_beq_eq_true hb')⟩


end CFSG.ASVolI.H16.SxPack
