module

public import CFSG.Quasithin.Vol2.Ch12Sec7GzSKap
public import CFSG.Quasithin.Vol2.Ch12Sec7GzSMdl
public import CFSG.Quasithin.Vol2.Ch12Sec7GzSPhi
public import Certificates.Data.S1277Cand

public section

namespace CFSG.Quasithin.H13.I1277

open Certificates.Data.S1277Struct Certificates.Data.S1277Cand Certificates.Data.S1277Bfs

section Lift

variable {G : Type} [Group G] {K Q : Subgroup G} {T : KTab} {κ : G → Nat}

def ModelInv (T : KTab) : Prop :=
  ∀ n ∈ klist T, invN T n ∈ klist T ∧ mulN T n (invN T n) = oneN T

theorem ModelInv.mk' {T : KTab}
    (h : ∀ n ∈ klist T, invN T n ∈ klist T ∧ mulN T n (invN T n) = oneN T) : ModelInv T := h

theorem ModelInv.elim {T : KTab} (h : ModelInv T) :
    ∀ n ∈ klist T, invN T n ∈ klist T ∧ mulN T n (invN T n) = oneN T := h

theorem KCod.comm (hκ : KCod K T κ) (hinv : ModelInv T) {a b : G} (ha : a ∈ K) (hb : b ∈ K) :
    κ (a * b * a⁻¹ * b⁻¹) = commN T (κ a) (κ b) := by
  have h1 : a * b ∈ K := K.mul_mem ha hb
  have h2 : a * b * a⁻¹ ∈ K := K.mul_mem h1 (K.inv_mem ha)
  unfold commN
  rw [hκ.mul _ h2 _ (K.inv_mem hb), hκ.mul _ h1 _ (K.inv_mem ha), hκ.mul _ ha _ hb,
    hκ.inv hinv ha, hκ.inv hinv hb]


end Lift

end CFSG.Quasithin.H13.I1277

end
