module

public import CFSG.Quasithin.Background.B3Four1

public section

namespace CFSG.Quasithin.B3

variable {n : ℕ} {k : Mod}


theorem conjAut_eq_map_conj {W : Type*} [CommGroup W] (g : MulAut W) (A : Subgroup (MulAut W)) :
    B1.conjAut g A = A.map (MulAut.conj g).toMonoidHom := by
  ext x
  rw [B1.mem_conjAut, Subgroup.mem_map_equiv]
  simp

theorem exists_conj_le_sylow_sub {G : Type*} [Group G] [Finite G] {H T A : Subgroup G}
    (hTH : T ≤ H) (hTp : IsPGroup 2 T) (hidx : ¬ 2 ∣ (T.subgroupOf H).index) (hAH : A ≤ H)
    (hAp : IsPGroup 2 A) : ∃ g ∈ H, cj g A ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card).1 hTp
  have hTY : IsPGroup 2 ↥(T.subgroupOf H) := by
    apply IsPGroup.of_card (n := m)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTH).toEquiv, hm]
  let TS : Sylow 2 ↥H := hTY.toSylow hidx
  obtain ⟨j, hj⟩ := (IsPGroup.iff_card).1 hAp
  have hAY : IsPGroup 2 ↥(A.subgroupOf H) := by
    apply IsPGroup.of_card (n := j)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAH).toEquiv, hj]
  obtain ⟨g, hg⟩ := exists_conj_le_sylow TS (A.subgroupOf H) hAY
  refine ⟨g.1, g.2, fun x hx => ?_⟩
  have ha : (g.1)⁻¹ * x * g.1 ∈ A := mem_cj.1 hx
  have haH : (g.1)⁻¹ * x * g.1 ∈ H := hAH ha
  have hmem : (g * ⟨(g.1)⁻¹ * x * g.1, haH⟩ * g⁻¹ : ↥H) ∈ cj g (A.subgroupOf H) := by
    rw [mem_cj]
    have e : (g⁻¹ * (g * ⟨(g.1)⁻¹ * x * g.1, haH⟩ * g⁻¹) * g : ↥H) =
        ⟨(g.1)⁻¹ * x * g.1, haH⟩ := by group
    rw [e, Subgroup.mem_subgroupOf]
    exact ha
  have h2 : ((g * ⟨(g.1)⁻¹ * x * g.1, haH⟩ * g⁻¹ : ↥H) : G) ∈ T := hg hmem
  simpa [mul_assoc] using h2


structure Std (n : ℕ) (b : Bool) : Prop where
  five : 5 ≤ n
  hTl : subOK n (Tl n) = true
  hEA : chkEA n (Tl n) (Dl n) = true
  hT0 : subOK n (Tgl n b) = true
  hsub : ∀ t ∈ Tgl n b, t ∈ Tl n
  hTH : Tgrp n b ≤ Hg n b
  hp : IsPGroup 2 (Tgrp n b)
  hidx : ¬ 2 ∣ ((Tgrp n b).subgroupOf (Hg n b)).index


open Classical in
@[expose] noncomputable def SP (n : ℕ) (k : Mod) (b : Bool)
    (P : Set (Subgroup (MulAut (Mod.V n k)))) : List (List Tab) :=
  (offsH n k b).filter (fun K => decide ((subOf n K).map (Mod.act n k) ∈ P))


end CFSG.Quasithin.B3
