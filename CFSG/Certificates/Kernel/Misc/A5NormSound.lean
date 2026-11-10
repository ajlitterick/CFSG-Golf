module

public import Certificates.Data.Kernel.Misc.A5Norm
public import Certificates.Data.A5GL42Norm
public import CFSG.Certificates.Kernel.Misc.Sp4CenSound
import CFSG.Certificates.Kernel.LocalQTPermSound

public section

namespace CFSG.KC.Misc.A5Norm

open Matrix CFSG.KD.A5Norm CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc.GL4
open Certificates.A5GL42


theorem incF_spec : ∀ (l : List ℕ) (p : ℕ), incF l p = true → (∀ x ∈ l, p < x) ∧ l.Nodup
  | [], _, _ => by simp
  | a :: l, p, h => by
    change andB (Nat.blt p a) (incF l a) = true at h
    rw [andB_iff, Nat.blt_eq] at h
    obtain ⟨h1, h2⟩ := incF_spec l a h.2
    refine ⟨fun x hx => ?_, List.nodup_cons.2 ⟨fun ha => absurd (h1 a ha) (lt_irrefl a), h2⟩⟩
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h.1
    · exact lt_trans h.1 (h1 x hx)

theorem incL_nodup : ∀ l : List ℕ, incL l = true → l.Nodup
  | [], _ => List.nodup_nil
  | a :: l, h => by
    obtain ⟨h1, h2⟩ := incF_spec l a h
    exact List.nodup_cons.2 ⟨fun ha => absurd (h1 a ha) (lt_irrefl a), h2⟩

theorem card_eq {cs : List ℕ} (hlt : ∀ c ∈ cs, c < 65536) (hinc : incL cs = true) :
    (cs.map ofCode).toFinset.card = cs.length := by
  rw [List.toFinset_card_of_nodup, List.length_map]
  exact (incL_nodup cs hinc).map_on fun a ha b hb e => ofCode_inj (hlt a ha) (hlt b hb) e


end CFSG.KC.Misc.A5Norm

end
