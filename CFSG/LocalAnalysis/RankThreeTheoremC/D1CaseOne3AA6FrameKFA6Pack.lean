module

public import CFSG.Permutation.FinPackAll6
public import CFSG.Permutation.FinPackComm
public import Mathlib.GroupTheory.SpecificGroups.Alternating
import CFSG.Mathlib.Decide.Nodup

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFA6Pack

open Equiv Finset CFSG.Permutation.FinPack

@[expose] def ID6 : ℕ := 5517840

theorem enc_one6 : enc (1 : Perm (Fin 6)) = ID6 := by decide +kernel

theorem enc_mul6 (σ τ : Perm (Fin 6)) : enc (σ * τ) = mulK 6 (enc σ) (enc τ) :=
  enc_mul (by norm_num) σ τ

theorem eq_one_iff (σ : Perm (Fin 6)) : σ = 1 ↔ Nat.beq (enc σ) ID6 = true := by
  rw [Nat.beq_eq, ← enc_one6]
  exact ⟨fun h => h ▸ rfl, enc_inj (by norm_num)⟩

theorem commute_iff (σ τ : Perm (Fin 6)) :
    σ * τ = τ * σ ↔ Nat.beq (mulK 6 (enc σ) (enc τ)) (mulK 6 (enc τ) (enc σ)) = true := by
  rw [Nat.beq_eq, ← enc_mul6, ← enc_mul6]
  exact ⟨congrArg enc, enc_inj (by norm_num)⟩


@[expose] def xP : Perm (Fin 6) := swap 0 1 * swap 1 2

@[expose] def yP : Perm (Fin 6) := swap 1 2 * swap 2 3 * swap 3 4 * swap 4 5


@[expose] noncomputable def centB (c : ℕ) : Bool :=
  !(Nat.beq (mulK 6 c 5517345) (mulK 6 5517345 c) && Nat.beq (mulK 6 c 1393440) (mulK 6 1393440 c))
    || Nat.beq c ID6


@[expose] noncomputable def cntK (f : ℕ → Bool) (L : List ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0 (fun a _ r => Bool.rec (motive := fun _ => ℕ) r (Nat.succ r) (f a)) L

theorem cntK_eq (f : ℕ → Bool) (L : List ℕ) : cntK f L = (L.filter f).length := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    change Bool.rec (motive := fun _ => ℕ) (cntK f L) (Nat.succ (cntK f L)) (f a) = _
    rw [List.filter_cons]
    cases f a <;> simp [ih]

theorem evenCodes6_nodup : evenCodes6.Nodup :=
  CFSG.Decide.nodup_of_bitsetNodup (fun c => lo6 c % 3106) (by decide +kernel)

theorem evenCodes6_length : evenCodes6.length = 360 := by decide +kernel

theorem card_even : (univ.filter fun g : Perm (Fin 6) => Perm.sign g = 1).card = 360 := by
  have h1 := two_mul_card_alternatingGroup (α := Fin 6)
  rw [Fintype.card_perm, Fintype.card_fin] at h1
  have h2 : Fintype.card (alternatingGroup (Fin 6)) =
      (univ.filter fun g : Perm (Fin 6) => Perm.sign g = 1).card := by
    rw [← Fintype.card_subtype]
    exact Fintype.card_congr (Equiv.subtypeEquivRight fun g => Perm.mem_alternatingGroup)
  have h3 : Nat.factorial 6 = 720 := rfl
  omega

theorem pc6_injective : Function.Injective (pc6 : Perm (Fin 6) → ℕ) := fun σ τ h =>
  enc_inj (by norm_num) (by rw [← lo6_pc6, h, lo6_pc6])

theorem image_even :
    (univ.filter fun g : Perm (Fin 6) => Perm.sign g = 1).image pc6 = evenCodes6.toFinset := by
  refine Finset.eq_of_subset_of_card_le (fun c hc => ?_) ?_
  · obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 hc
    exact List.mem_toFinset.2 (memK_iff.1 (pc6_mem_even g (Finset.mem_filter.1 hg).2))
  · rw [Finset.card_image_of_injective _ pc6_injective, card_even,
      List.toFinset_card_of_nodup evenCodes6_nodup, evenCodes6_length]

theorem card_even_filter (f : ℕ → Bool) :
    (univ.filter fun g : Perm (Fin 6) => Perm.sign g = 1 ∧ f (enc g) = true).card =
      cntK (fun c => f (lo6 c)) evenCodes6 := by
  have hL : (evenCodes6.filter (fun c => f (lo6 c))).length =
      (evenCodes6.toFinset.filter (fun c => f (lo6 c) = true)).card := by
    rw [← List.toFinset_card_of_nodup (evenCodes6_nodup.filter _), List.toFinset_filter]
  rw [cntK_eq, hL, ← image_even, Finset.filter_image,
    Finset.card_image_of_injective _ pc6_injective, Finset.filter_filter]
  simp only [lo6_pc6]

@[expose] noncomputable def invB (c : ℕ) : Bool :=
  !(Nat.beq (mulK 6 c c) ID6 && !(Nat.beq c ID6)) ||
    !(Nat.beq (Nat.mod (cntK (fun q => commLaneK 6 (lo6 q) c) evenCodes6) 9) 0)


end CFSG.LocalAnalysis.RankThreeTheoremC.KFA6Pack
