module

public import CFSG.Certificates.Kernel.Spor.OrdSound
public import CFSG.Certificates.Kernel.Misc.PermClosSound
import all CFSG.Certificates.Kernel.Spor.OrdSound

public section

namespace CFSG.KC.CosetLat

open CFSG.KC.Ord CFSG.KS.Ord
open CFSG.KC.Misc.Clos (ClosEnc)

@[expose] def matCode (p d w : ℕ) (A : Matrix (Fin d) (Fin d) (ZMod p)) : ℕ :=
  ∑ i : Fin d, ∑ j : Fin d, (A i j).val * 2 ^ (w * (d * i.val + j.val))

noncomputable def entL {p d : ℕ} (A : Matrix (Fin d) (Fin d) (ZMod p)) (t : ℕ) : ℕ :=
  if h : t < d * d then
    (A ⟨t / d, (Nat.div_lt_iff_lt_mul (Nat.pos_of_ne_zero fun h0 => by simp [h0] at h)).2 h⟩
      ⟨t % d, Nat.mod_lt _ (Nat.pos_of_ne_zero fun h0 => by simp [h0] at h)⟩).val
  else 0

theorem entL_idx {p d : ℕ} (A : Matrix (Fin d) (Fin d) (ZMod p)) (i j : Fin d) :
    entL A (d * i.val + j.val) = (A i j).val := by
  have hlt := idx_lt i.isLt j.isLt
  obtain ⟨e1, e2⟩ := dm_eq (d := d) (i := i.val) j.isLt
  unfold entL
  rw [dif_pos hlt]
  have key : ∀ a b : Fin d, a = i → b = j → (A a b).val = (A i j).val := by
    rintro _ _ rfl rfl
    rfl
  exact key _ _ (Fin.ext e1) (Fin.ext e2)

private theorem matCode_eq_pk {p d : ℕ} (w : ℕ) (A : Matrix (Fin d) (Fin d) (ZMod p)) :
    matCode p d w A = pk w (d * d) (entL A) := by
  rw [pk_rows, matCode, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [entL_idx]

theorem entL_lt {p d : ℕ} [NeZero p] (A : Matrix (Fin d) (Fin d) (ZMod p)) (t : ℕ) :
    entL A t < p := by
  unfold entL
  split
  · exact ZMod.val_lt _
  · exact Nat.pos_of_ne_zero (NeZero.ne p)

theorem ordMat_matCode {p d w : ℕ} [NeZero p] (hp : p ≤ 2 ^ w)
    (A : Matrix (Fin d) (Fin d) (ZMod p)) :
    Canon p d w (matCode p d w A) ∧ ordMat p d w (d * w) (matCode p d w A) = A := by
  rw [matCode_eq_pk]
  have hg : ∀ t < d * d, entL A t < p := fun t _ => entL_lt A t
  refine ⟨canon_pk hg hp, ?_⟩
  funext i j
  rw [ordMat_pk (fun t ht => Nat.lt_of_lt_of_le (hg t ht) hp), entL_idx, ZMod.natCast_zmod_val]


end CFSG.KC.CosetLat

end
