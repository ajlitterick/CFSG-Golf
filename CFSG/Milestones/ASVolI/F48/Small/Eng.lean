module

public import CFSG.Milestones.ASVolI.F48.Small.Core

public section

namespace CFSG.ASVolI

open CFSG.Quasithin CFSG.CosetTable

section Sem

variable {N n : ℕ} {X : Subgroup (Equiv.Perm (Fin N))}

@[expose] def burnsideF48s_eRec (G : Fin n → ↥X) (LS LSi : List (List ℕ)) : Prop :=
  ∀ i : Fin n, RepL (LS.getD i []) ((G i : ↥X) : Equiv.Perm (Fin N)) ∧
    RepL (LSi.getD i []) (((G i)⁻¹ : ↥X) : Equiv.Perm (Fin N))

variable {G : Fin n → ↥X} {LS LSi : List (List ℕ)}

theorem burnsideF48s_e_ev_invW {H : Type*} [Group H] (h : Fin n → H) (w : List (Fin n × Bool)) :
    burnsideF48s_ev h (burnsideF48s_eInvW w) = (burnsideF48s_ev h w)⁻¹ := by
  induction w with
  | nil => simp [burnsideF48s_eInvW]
  | cons l w ih =>
    have e : burnsideF48s_eInvW (l :: w) = burnsideF48s_eInvW w ++ [(l.1, !l.2)] := by
      simp [burnsideF48s_eInvW]
    rw [e, burnsideF48s_ev_append, ih, burnsideF48s_ev_cons, burnsideF48s_ev_cons,
      burnsideF48s_ev_nil, mul_one, mul_inv_rev]
    obtain ⟨i, b⟩ := l
    cases b <;> simp


theorem burnsideF48s_e_getD_mem {α : Type*} (l : List α) {i : ℕ} (hi : i < l.length) (d : α) :
    l.getD i d ∈ l := by
  rw [List.getD_eq_getElem _ _ hi]
  exact List.getElem_mem _


end Sem

section Model

variable {N n : ℕ} {X : Subgroup (Equiv.Perm (Fin N))}

structure burnsideF48s_EModel (G : Fin n → ↥X) (LS LSi : List (List ℕ)) (P1 P2 K : Subgroup ↥X)
    (P1W P2W KW R1 R2 : List (List (Fin n × Bool))) : Prop where
  rep : burnsideF48s_eRec G LS LSi
  sup : P1 ⊔ P2 = ⊤
  K_le : K ≤ P1 ⊓ P2
  cov1 : ∀ z ∈ P1, ∃ i < P1W.length, z = burnsideF48s_ev G (P1W.getD i [])
  cov2 : ∀ z ∈ P2, ∃ j < P2W.length, z = burnsideF48s_ev G (P2W.getD j [])
  covK : ∀ z ∈ K, ∃ l < KW.length, z = burnsideF48s_ev G (KW.getD l [])
  let1 : ∀ i < P1W.length, ∀ l ∈ P1W.getD i [], G l.1 ∈ P1
  let2 : ∀ j < P2W.length, ∀ l ∈ P2W.getD j [], G l.1 ∈ P2
  memK : ∀ l < KW.length, burnsideF48s_ev G (KW.getD l []) ∈ K
  rel1 : ∀ r ∈ R1, (∀ l ∈ r, G l.1 ∈ P1) ∧ burnsideF48s_ev G r = 1
  rel2 : ∀ r ∈ R2, (∀ l ∈ r, G l.1 ∈ P2) ∧ burnsideF48s_ev G r = 1


variable {G : Fin n → ↥X} {LS LSi : List (List ℕ)} {P1 P2 K : Subgroup ↥X}
  {P1W P2W KW R1 R2 TW U V W : List (List (Fin n × Bool))} {m : ℕ}

theorem burnsideF48s_EModel.mem1 (hM : burnsideF48s_EModel G LS LSi P1 P2 K P1W P2W KW R1 R2)
    {i : ℕ} (hi : i < P1W.length) : burnsideF48s_ev G (P1W.getD i []) ∈ P1 :=
  burnsideF48s_ev_mem G _ (hM.let1 i hi)

theorem burnsideF48s_EModel.mem2 (hM : burnsideF48s_EModel G LS LSi P1 P2 K P1W P2W KW R1 R2)
    {j : ℕ} (hj : j < P2W.length) : burnsideF48s_ev G (P2W.getD j []) ∈ P2 :=
  burnsideF48s_ev_mem G _ (hM.let2 j hj)


end Model

section Core


end Core

section QE

open CFSG.Open CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
open CFSG.ASVolI.ChF


end QE

section Sylow

open CFSG.Open CFSG.ASVolI.ChF


end Sylow

end CFSG.ASVolI
