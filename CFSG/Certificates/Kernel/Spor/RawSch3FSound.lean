module

public import Certificates.Data.Kernel.Spor.RawSch3F
public import CFSG.Certificates.Kernel.Spor.RawSiftK

public section

namespace CFSG.KS.Raw.Orb

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

theorem permOK_right {n w P Q : Nat} (h : permOK n w (mask w) (n * w) P Q = true) :
    ∀ z < n, pg w (mask w) Q z < n ∧ pg w (mask w) P (pg w (mask w) Q z) = z := by
  obtain ⟨-, -, f⟩ := permOK_facts h
  intro z hz
  let g : Fin n → Fin n := fun i => ⟨pg w (mask w) P i, (f i i.2).1⟩
  have hinj : Function.Injective g := by
    intro a b hab
    have h1 : pg w (mask w) P a = pg w (mask w) P b := congrArg Fin.val hab
    have h2 := congrArg (pg w (mask w) Q) h1
    rw [(f a a.2).2, (f b b.2).2] at h2
    exact Fin.ext h2
  obtain ⟨i, hi⟩ := Finite.surjective_of_injective hinj ⟨z, hz⟩
  have hiz : pg w (mask w) P i = z := congrArg Fin.val hi
  rw [← hiz, (f i i.2).2]
  exact ⟨i.2, rfl⟩


theorem sift2_of_fields {n w i : Nat} {LR TR TRI : Nat → Nat} {BP G k1 k2 : Nat}
    (hsz : szOK n w = true)
    (hb2 : pg w (mask w) BP (i + 1 + 1) < n)
    (e1 : rpos w (mask w) (n * w) (LR (i + 1)) (pg w (mask w) G (pg w (mask w) BP (i + 1))) = k1)
    (hk1 : k1 < rcnt (LR (i + 1)))
    (e2 : rpos w (mask w) (n * w) (LR (i + 1 + 1))
      (pg w (mask w) (TRI (roff n (n * w) (LR (i + 1)) + k1))
        (pg w (mask w) G (pg w (mask w) BP (i + 1 + 1)))) = k2)
    (hk2 : k2 < rcnt (LR (i + 1 + 1)))
    (hp1 : permOK n w (mask w) (n * w) (TR (roff n (n * w) (LR (i + 1)) + k1))
      (TRI (roff n (n * w) (LR (i + 1)) + k1)) = true)
    (hp2 : permOK n w (mask w) (n * w) (TR (roff n (n * w) (LR (i + 1 + 1)) + k2))
      (TRI (roff n (n * w) (LR (i + 1 + 1)) + k2)) = true)
    (hE : ∀ x < n, pg w (mask w) G x = pg w (mask w) (TR (roff n (n * w) (LR (i + 1)) + k1))
      (pg w (mask w) (TR (roff n (n * w) (LR (i + 1 + 1)) + k2)) x)) :
    siftK n w (mask w) (n * w) (pidn n w) LR TRI BP (0 + 1 + 1) (i + 1) G = true := by
  obtain ⟨hn24, hw⟩ := szOK_facts hsz
  have hn : n < 2 ^ 32 := by omega
  have hw0 : 0 < w := PF.w_pos hw
  simp only [siftK_succ, siftK_zero, strictB_eq, bIf_eq, Nat.blt_eq, Nat.add_eq,
    Nat.succ_eq_add_one]
  rw [e1, if_pos hk1, PF.pg_pcomp hn hb2, e2, if_pos hk2]
  simp only [hsz, Bool.true_and, ↓reduceIte, Nat.beq_eq]
  refine PF.eq_of_fields hw0 (PF.pcomp_shr _ _ hn hw0) (PF.pidn_shr hn24 hw) (fun x hx => ?_)
  rw [PF.pg_pcomp hn hx, PF.pg_pcomp hn hx, PF.pg_pidn hn24 hw hx, hE x hx]
  obtain ⟨-, -, f1⟩ := permOK_facts hp1
  obtain ⟨-, -, f2⟩ := permOK_facts hp2
  rw [(f1 _ (f2 x hx).1).2, (f2 x hx).2]

theorem t3K_facts {n w kS BP i T D h j : Nat} {S SI LR TR TRI U : Nat → Nat}
    (ht : t3K n w (mask w) (n * w) S SI LR TR TRI U kS BP i T D h j = true) {s th k k1 k2 : Nat}
    (es : letterK S SI kS (stAt T j) = s) (eth : TR (roff n (n * w) (LR i) + h) = th)
    (ek : rpos w (mask w) (n * w) (LR i) (pg w (mask w) s (rpt w (mask w) (LR i) h)) = k)
    (ek1 : rpos w (mask w) (n * w) (LR (i + 1)) (pg w (mask w) (TRI (roff n (n * w) (LR i) + k))
      (pg w (mask w) s (pg w (mask w) th (pg w (mask w) BP (i + 1))))) = k1)
    (ek2 : rpos w (mask w) (n * w) (LR (i + 1 + 1))
      (pg w (mask w) (TRI (roff n (n * w) (LR (i + 1)) + k1))
        (pg w (mask w) (TRI (roff n (n * w) (LR i) + k))
          (pg w (mask w) s (pg w (mask w) th (pg w (mask w) BP (i + 1 + 1)))))) = k2) :
    k < rcnt (LR i) ∧ k1 < rcnt (LR (i + 1)) ∧ k2 < rcnt (LR (i + 1 + 1)) ∧
      pcomp n w (mask w) s th = pcomp n w (mask w) (TR (roff n (n * w) (LR i) + k)) (U (k1 * D + k2)) := by
  unfold t3K at ht
  simp only [strictB_eq, bAnd_iff, Nat.blt_eq, Nat.beq_eq, Nat.add_eq, Nat.mul_eq,
    Nat.succ_eq_add_one] at ht
  subst es eth
  rw [ek] at ht
  rw [ek1] at ht
  rw [ek2] at ht
  exact ht


theorem t3K_of_sch3F {n w kS BP i T D NSi CH : Nat} {S SI LR TR TRI U : Nat → Nat}
    (hc : rcnt (LR i) ≤ NSi * CH)
    (h : ∀ s < NSi, sch3F n w (mask w) (n * w) S SI LR TR TRI U kS BP i T D (s * CH) CH = true) :
    ∀ hh < rcnt (LR i), ∀ j < Nat.shiftRight (stCnt T) (nat_lit 1),
      t3K n w (mask w) (n * w) S SI LR TR TRI U kS BP i T D hh j = true := by
  intro hh hhc j hj
  have hCH : 0 < CH := by
    rcases Nat.eq_zero_or_pos CH with h0 | h0
    · rw [h0, Nat.mul_zero] at hc
      omega
    · exact h0
  have hs := h (hh / CH) ((Nat.div_lt_iff_lt_mul hCH).2 (by omega))
  unfold sch3F at hs
  simp only [strictB_eq] at hs
  have h1 := allN_iff.1 hs (hh % CH) (Nat.mod_lt _ hCH)
  have e : Nat.add (hh / CH * CH) (hh % CH) = hh := by
    have := Nat.div_add_mod hh CH
    rw [Nat.mul_comm] at this
    exact this
  simp only [e, bIf_eq] at h1
  rw [if_pos (Nat.blt_eq.mpr hhc)] at h1
  exact allN_iff.1 h1 j hj


end CFSG.KS.Raw.Orb

end
