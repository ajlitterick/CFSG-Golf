module

import CFSG.Quasithin.Background.HModelType
import CFSG.Quasithin.Background.SmithB45MatIndM24Gen
public import CFSG.CharacterTheory.SteinbergBYNortonCriterion
public import Certificates.Data.SmithB45MatIndM23
public import Certificates.Data.SmithB45MatIndM24

public section

namespace CFSG.Quasithin.H.ModelIrr

open CFSG.Monster.Code CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.ModelType

section Generic

variable {V : Type*} [CommGroup V]

@[expose] def IrredAct (L : Subgroup (MulAut V)) : Prop :=
  ∀ U : Subgroup V, (∀ g ∈ L, ∀ u ∈ U, g u ∈ U) → U = ⊥ ∨ U = ⊤

theorem irredAct_of_map {W : Type*} [CommGroup W] (e : V ≃* W) {L : Subgroup (MulAut V)}
    {X : Subgroup (MulAut W)} (hX : L.map (MulAut.congr e).toMonoidHom = X) (h : IrredAct X) :
    IrredAct L := by
  intro U hU
  have hinv : ∀ g ∈ X, ∀ u ∈ U.map e.toMonoidHom, g u ∈ U.map e.toMonoidHom := by
    intro g hg u hu
    rw [← hX] at hg
    obtain ⟨l, hl, rfl⟩ := hg
    obtain ⟨u0, hu0, rfl⟩ := hu
    refine ⟨l u0, hU l hl u0 hu0, ?_⟩
    simp [congrHom_apply]
  rcases h _ hinv with h0 | h0
  · exact Or.inl ((Subgroup.map_eq_bot_iff_of_injective U
      (f := e.toMonoidHom) e.injective).1 h0)
  · right
    rw [← Subgroup.comap_map_eq_self_of_injective (f := e.toMonoidHom) e.injective U, h0,
      Subgroup.comap_top]

end Generic

section Bits

variable {n : ℕ}

@[expose] def toSubspace (U : Subgroup (Multiplicative (Fin n → ZMod 2))) :
    Submodule (ZMod 2) (Fin n → ZMod 2) where
  carrier := {v | Multiplicative.ofAdd v ∈ U}
  add_mem' := fun {x y} hx hy => by
    have e : Multiplicative.ofAdd (x + y) = Multiplicative.ofAdd x * Multiplicative.ofAdd y :=
      ofAdd_add x y
    show Multiplicative.ofAdd (x + y) ∈ U
    rw [e]
    exact U.mul_mem hx hy
  zero_mem' := by
    show Multiplicative.ofAdd (0 : Fin n → ZMod 2) ∈ U
    rw [ofAdd_zero]
    exact U.one_mem
  smul_mem' := fun c {x} hx => by
    show Multiplicative.ofAdd (c • x) ∈ U
    have hc : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
    rcases hc c with h0 | h0
    · rw [h0, zero_smul, ofAdd_zero]
      exact U.one_mem
    · rw [h0, one_smul]
      exact hx

theorem mem_toSubspace (U : Subgroup (Multiplicative (Fin n → ZMod 2))) (v : Fin n → ZMod 2) :
    v ∈ toSubspace U ↔ Multiplicative.ofAdd v ∈ U := Iff.rfl

theorem irredAct_of_gens {ι : Type*} (X : Subgroup (MulAut (Multiplicative (Fin n → ZMod 2))))
    (gens : ι → MulAut (Multiplicative (Fin n → ZMod 2))) (hgens : ∀ i, gens i ∈ X)
    (h : ∀ U : Submodule (ZMod 2) (Fin n → ZMod 2),
      (∀ i, ∀ u ∈ U, Multiplicative.toAdd (gens i (Multiplicative.ofAdd u)) ∈ U) →
        U = ⊥ ∨ U = ⊤) :
    IrredAct X := by
  intro U hU
  have hinv : ∀ i, ∀ u ∈ toSubspace U,
      Multiplicative.toAdd (gens i (Multiplicative.ofAdd u)) ∈ toSubspace U := by
    intro i u hu
    exact (mem_toSubspace U _).2 (by rw [ofAdd_toAdd]; exact hU _ (hgens i) _ hu)
  rcases h _ hinv with h0 | h0
  · left
    rw [eq_bot_iff]
    intro u hu
    have h1 : Multiplicative.toAdd u ∈ toSubspace U :=
      (mem_toSubspace U _).2 (by rw [ofAdd_toAdd]; exact hu)
    rw [h0, Submodule.mem_bot] at h1
    rw [Subgroup.mem_bot]
    exact Multiplicative.toAdd.injective h1
  · right
    rw [eq_top_iff]
    intro u _
    have h1 : Multiplicative.toAdd u ∈ toSubspace U := by rw [h0]; trivial
    have h2 := (mem_toSubspace U _).1 h1
    rwa [ofAdd_toAdd] at h2

end Bits

section Endo

variable {V : Type*} [CommGroup V]


end Endo

section Std

open CFSG.Quasithin.B45Mat CFSG.Quasithin.B45Mat.Ind CFSG.Quasithin.B45Mat.M22
  CFSG.QuasithinUnique.Setup.X3E CFSG.CharacterTheory.SteinbergBY

private theorem toLin'_mulAutMat (n : ℕ) (f : MulAut (Multiplicative (Fin n → ZMod 2)))
    (u : Fin n → ZMod 2) :
    Matrix.toLin' (mulAutMat n f) u = Multiplicative.toAdd (f (Multiplicative.ofAdd u)) := by
  simp only [mulAutMat, MonoidHom.coe_mk, OneHom.coe_mk]
  rw [Matrix.toLin'_toMatrix']
  rfl


private theorem irredAct_rho11_autPerm :
    IrredAct (rho11 AutPerm le_rfl).range := by
  refine irredAct_of_gens _ (fun z => rho11 AutPerm le_rfl (m24g z)) (fun z => ⟨_, rfl⟩) ?_
  intro U hU
  refine irredPair_m24Std (t := 2) (by norm_num) U ?_
  intro z (u : Fin 11 → ZMod 2) hu
  show lin 11 (m24Std 2 z) u ∈ U
  rw [lin_m24Std_cocode z, toLin'_mulAutMat]
  exact hU z u hu


end Std

section Facts


theorem centralizer_eq_bot_of_cocode22
    {V : Type*} [CommGroup V] {H : Subgroup (MulAut V)}
    (h : MathieuCocode22 H ⊤ ⊥) : Subgroup.centralizer (H : Set (MulAut V)) = ⊥ := by
  obtain ⟨e, he⟩ := cocode22_std h
  exact centralizer_eq_bot_of_map e (by rw [he]; exact centralizer_rho10_mog22)

variable {V : Type} [CommGroup V] {L : Subgroup (MulAut V)}


theorem cocode24_facts
    (h : MathieuCocode24 L ⊤ ⊥) :
    Nat.card V = 2 ^ 11 ∧ IrredAct L ∧ Subgroup.centralizer (L : Set (MulAut V)) = ⊥ := by
  obtain ⟨e, he⟩ := cocode24_std h
  exact ⟨(stmtH13Card V L).1 (Or.inl h), irredAct_of_map e he irredAct_rho11_autPerm,
    centralizer_eq_bot_of_cocode24 h⟩

end Facts

end CFSG.Quasithin.H.ModelIrr
