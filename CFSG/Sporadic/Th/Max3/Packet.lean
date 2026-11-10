
module

public import CFSG.Sporadic.Th.Max3.PacketBase1
import all CFSG.Sporadic.Th.Max3.PacketBase
import all CFSG.Sporadic.Th.Max3.PacketBase1

public import CFSG.Sporadic.Th.Max3.Core
public import Certificates.Certificate10090
public meta import CFSG.Sporadic.Th.Max3.Data
public import Certificates.Certificate10090Base

public section

namespace CFSG.Sporadic.Th.Max3

open CFSG.Sporadic.Th.Native CFSG.Certificates

namespace Packet

end Packet

namespace Packet

theorem isRows_letter
    (l : ℤ) : IsRows (letterRows l) (signedLetter l) := by
  unfold letterRows signedLetter
  by_cases h1 : l = 1
  · subst h1
    simpa using isRows_x
  by_cases h2 : l = -1
  · subst h2
    simpa using (show IsRows rowsX x⁻¹ by rw [x_inv]; exact isRows_x)
  by_cases h3 : l = 2
  · subst h3
    simpa using isRows_y
  by_cases h4 : l = -2
  · subst h4
    simpa using (show IsRows (powRows rowsY 5) y⁻¹ by rw [y_inv]; exact isRows_y.pow 5)
  simpa [h1, h2, h3, h4] using IsRows.one

theorem isRows_signedWord
    (w : List ℤ) : IsRows (signedWordRows w) (signedWordProd w) := by
  refine IsRows.prod ?_
  induction w with
  | nil => exact List.Forall₂.nil
  | cons l w ih => exact List.Forall₂.cons (isRows_letter l) ih

private theorem native_packet_facts :
    eqRows (signedWordRows coreZWord) rowsZ = true ∧
    ∀ i : Fin 8, eqRows (signedWordRows (coreGeneratorWords i))
      (mulRows (rowsQ i) (powRows rowsZ (qPShift i).val)) = true :=
  Certificates.certificate10090

end Packet

theorem zP_eq_z :
    zP = z := by
  obtain ⟨h, -⟩ := Packet.native_packet_facts
  exact (Packet.isRows_signedWord _).eq_of_eqRows isRows_z h

theorem qP_eq
    (i : Fin 8) : qP i = q i * z ^ (qPShift i).val := by
  obtain ⟨-, h⟩ := Packet.native_packet_facts
  exact (Packet.isRows_signedWord _).eq_of_eqRows ((isRows_q i).mul (isRows_z.pow _)) (h i)


namespace Packet

theorem z_pow_mul_q
    (i : Fin 8) (n : ℕ) : z ^ n * q i = q i * z ^ n :=
  pow_mul_of_comm (z_mul_q i) n

theorem twist_mul
    (i j : Fin 8) (a b : ℕ) :
    q i * z ^ a * (q j * z ^ b) = q i * q j * z ^ (a + b) := by
  calc q i * z ^ a * (q j * z ^ b) = q i * (z ^ a * q j) * z ^ b := by simp only [mul_assoc]
    _ = q i * (q j * z ^ a) * z ^ b := by rw [z_pow_mul_q]
    _ = q i * q j * z ^ (a + b) := by rw [pow_add]; simp only [mul_assoc]

end Packet

theorem zP_mul_self :
    zP * zP = 1 := by
  rw [zP_eq_z]
  exact z_mul_self

theorem relP :
    ExtraspecialNF.Rel zP qP c where
  z_sq := zP_mul_self
  z_comm i := by
    rw [zP_eq_z, qP_eq]
    calc z * (q i * z ^ (qPShift i).val) = (z * q i) * z ^ (qPShift i).val :=
          (mul_assoc _ _ _).symm
      _ = q i * (z * z ^ (qPShift i).val) := by rw [z_mul_q i, mul_assoc]
      _ = q i * (z ^ (qPShift i).val * z) := by rw [← pow_succ', pow_succ]
      _ = q i * z ^ (qPShift i).val * z := (mul_assoc _ _ _).symm
  q_sq i := by
    rw [qP_eq, Packet.twist_mul, q_mul_self, one_mul, ← two_mul, pow_mul, sq, z_mul_self, one_pow]
  comm i j := by
    rw [qP_eq, qP_eq, zP_eq_z, Packet.twist_mul, Packet.twist_mul, q_mul_q i j]
    have hexp : (c i j).val + ((qPShift i).val + (qPShift j).val) =
        ((qPShift j).val + (qPShift i).val) + (c i j).val := by omega
    simp only [mul_assoc, ← pow_add, hexp]

theorem closure_eq_Q :
    Subgroup.closure (insert zP (Set.range qP)) = Q := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro g (rfl | ⟨i, rfl⟩)
    · rw [zP_eq_z]
      exact z_mem_Q
    · rw [qP_eq]
      exact Q.mul_mem (q_mem_Q i) (Subgroup.pow_mem _ z_mem_Q _)
  · rw [show Q = Subgroup.closure (insert z (Set.range q)) from rfl, Subgroup.closure_le]
    rintro g (rfl | ⟨i, rfl⟩)
    · rw [← zP_eq_z]
      exact Subgroup.subset_closure (Set.mem_insert _ _)
    · have e : q i = qP i * (z ^ (qPShift i).val)⁻¹ := by rw [qP_eq, mul_inv_cancel_right]
      rw [e]
      refine mul_mem (Subgroup.subset_closure (Set.mem_insert_of_mem _ ⟨i, rfl⟩)) (inv_mem ?_)
      rw [← zP_eq_z]
      exact Subgroup.pow_mem _ (Subgroup.subset_closure (Set.mem_insert _ _)) _


namespace Packet

end Packet


theorem mem_Q_iff_EP
    (g : J) : g ∈ Q ↔ ∃ k, EP k = g := by
  rw [← closure_eq_Q, ExtraspecialNF.mem_closure_iff relP]
  constructor
  · rintro ⟨s, v, rfl⟩
    obtain ⟨k, hk⟩ := Packet.bits_surjective (Fin.cons s v)
    refine ⟨k, ?_⟩
    rw [EP_eq_nf, hk]
    rfl
  · rintro ⟨k, rfl⟩
    exact ⟨_, _, (EP_eq_nf k).symm⟩

namespace Packet


theorem mk_conj_eq
    {t : J} (ht : ∀ g ∈ Q, t * g * t⁻¹ ∈ Q) (hz : t * z = z * t) {g h : Q}
    (e : (QuotientGroup.mk g : Q ⧸ Subgroup.center Q) = QuotientGroup.mk h) :
    (QuotientGroup.mk ⟨t * g * t⁻¹, ht g g.2⟩ : Q ⧸ Subgroup.center Q) =
      QuotientGroup.mk ⟨t * h * t⁻¹, ht h h.2⟩ := by
  rw [QuotientGroup.eq, center_Q, Subgroup.mem_subgroupOf] at e ⊢
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 e
  refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
  have hc : z ^ k ∈ Subgroup.centralizer ({t} : Set J) :=
    Subgroup.zpow_mem _ (Subgroup.mem_centralizer_iff.2 (by simpa using hz)) k
  have hc' : t * z ^ k = z ^ k * t := by simpa using Subgroup.mem_centralizer_iff.1 hc t rfl
  have hk' : z ^ k = (g : J)⁻¹ * (h : J) := hk
  show z ^ k = (t * g * t⁻¹)⁻¹ * (t * h * t⁻¹)
  calc z ^ k = t * z ^ k * t⁻¹ := by rw [hc', mul_inv_cancel_right]
    _ = (t * g * t⁻¹)⁻¹ * (t * h * t⁻¹) := by rw [hk']; group

end Packet


theorem theta_apply_nf
    (s : ZMod 2) (v : Fin 8 → ZMod 2) :
    theta (Multiplicative.ofAdd v) = QuotientGroup.mk ⟨nf s v, nf_mem_Q s v⟩ := by
  have hv : Matrix.mulVec B1 (Matrix.mulVec B1 v) = v := by
    rw [Matrix.mulVec_mulVec, Packet.B1_mul_B1, Matrix.one_mulVec]
  obtain ⟨t, ht⟩ := conj_nf_zero x xz xv x_conj_q (Matrix.mulVec B1 v)
  have hw : (fun k => ∑ i, Matrix.mulVec B1 v i * xv i k) =
      Matrix.mulVec B1 (Matrix.mulVec B1 v) := by
    funext k
    simp [Matrix.mulVec, dotProduct, B1, mul_comm]
  rw [hw, hv] at ht
  have h1 := theta_B1 (Matrix.mulVec B1 v)
  rw [hv] at h1
  rw [h1, congrArg QuotientGroup.mk (Subtype.ext ht :
    (⟨x * nf 0 (Matrix.mulVec B1 v) * x⁻¹, x_conj_mem_Q (nf_mem_Q 0 _)⟩ : Q) =
      ⟨nf t v, nf_mem_Q t v⟩)]
  exact (ExtraspecialNF.theta_apply_eq_mk symplectic_rel t v).symm.trans
    (ExtraspecialNF.theta_apply_eq_mk symplectic_rel s v)


theorem zP_ne_one :
    zP ≠ 1 := by
  rw [zP_eq_z]
  exact z_ne_one


end CFSG.Sporadic.Th.Max3
