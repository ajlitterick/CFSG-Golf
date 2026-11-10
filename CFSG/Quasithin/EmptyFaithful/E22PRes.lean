module

public import CFSG.Quasithin.EmptyFaithful.E22PA6

public section

namespace CFSG.Quasithin.E2.E22N

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Vol2.Ch11.SecB

@[expose] def TypeOneRes (Y : Type) [Group Y] : Prop :=
  IsPSL 3 2 1 Y ∨ IsAlt 6 Y ∨
    (∃ p e : ℕ, p.Prime ∧ 3 < p ∧ (e = 1 ∨ e = 2) ∧ (p ^ e % 8 = 1 ∨ p ^ e % 8 = 7) ∧
      IsPSL 2 p e Y) ∨
    ∃ (s : Bool) (p : ℕ), p.Prime ∧ p ≠ 2 ∧ (s = true → p % 4 = 3) ∧ (s = false → p % 4 = 1) ∧
      IsPSLEps3 s p 1 Y

theorem TypeOneRes.of_mulEquiv {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y')
    (h : TypeOneRes Y') : TypeOneRes Y := by
  rcases h with h | h | ⟨p, f, hp, hp3, hf, hpf, h⟩ | ⟨s, p, hp, hp2, h4, h4', h⟩
  · exact Or.inl (CFSG.SectionRank.statedClassicalModel_of_mulEquiv e h)
  · obtain ⟨e'⟩ : Nonempty (Y' ≃* alternatingGroup (Fin 6)) := h
    exact Or.inr (Or.inl ⟨e.trans e'⟩)
  · exact Or.inr (Or.inr (Or.inl
      ⟨p, f, hp, hp3, hf, hpf, CFSG.SectionRank.statedClassicalModel_of_mulEquiv e h⟩))
  · refine Or.inr (Or.inr (Or.inr ⟨s, p, hp, hp2, h4, h4', ?_⟩))
    cases s with
    | true => exact CFSG.SectionRank.statedClassicalModel_of_mulEquiv e h
    | false => exact CFSG.SectionRank.statedClassicalModel_of_mulEquiv e h

theorem TypeOneRes.toTypeOne {Y : Type} [Group Y] (h : TypeOneRes Y) : TypeOne Y := by
  rcases h with h | h | ⟨p, f, hp, hp3, hf, hpf, h⟩ | ⟨s, p, hp, hp2, -, -, h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · refine Or.inr (Or.inr (Or.inl ⟨p, f, hp, by omega, ?_, h⟩))
    have h2 := hp.two_le
    rcases hf with rfl | rfl
    · rw [pow_one] at hpf ⊢
      omega
    · nlinarith
  · exact Or.inr (Or.inr (Or.inr ⟨s, p, hp, hp2, h⟩))

@[expose] def E114OneRes : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T : Subgroup G), SQTKGroup G →
    IsSimpleGroup (ASInputs.FStar G) → quasithinIsSylowTwo T →
    CFSG.generalizedFitting G ⊔ T = ⊤ →
      TypeOneRes (ASInputs.FStar G) → E1.nParam (⊤ : Subgroup G) ≤ 1


theorem nParam_sup_le_one_of_res (h114 : E114OneRes) {X : Type} [Group X] [Finite X]
    [IsSimpleGroup X] (hnab : ∃ a b : X, a * b ≠ b * a) (hSQ : SQTKGroup X)
    (hT : TypeOneRes X) {B : Subgroup (MulAut X)} (hB : IsPGroup 2 B)
    (hBI : IsSylowIn 2 (B ⊓ (MulAut.conj : X →* MulAut X).range)
      (MulAut.conj : X →* MulAut X).range) :
    E1.nParam ((MulAut.conj : X →* MulAut X).range ⊔ B) ≤ 1 := by
  set I := (MulAut.conj : X →* MulAut X).range with hI
  set Z := I ⊔ B with hZdef
  have hIn : I.Normal := normal_range_conj X
  have hSQI : SQTKGroup ↥I :=
    sqtkGroup_of_mulEquiv (rangeConjEquiv (center_eq_bot_of_nonabelian' hnab)).symm hSQ
  have hSQZ : SQTKGroup ↥Z := InternalSec.sqtkGroup_of_two_pow le_sup_left
    (fun y _ k hk => hIn.conj_mem k hk y) (pow_mem_of_mem_sup hB) hSQI
  set e := generalizedFittingEquiv hnab B with he
  have hFs : IsSimpleGroup (ASInputs.FStar ↥Z) := e.isSimpleGroup
  have hFT : TypeOneRes (ASInputs.FStar ↥Z) := TypeOneRes.of_mulEquiv e hT
  have key : E1.nParam (⊤ : Subgroup ↥Z) ≤ 1 :=
    h114 ↥Z (B.subgroupOf Z) hSQZ hFs (isSylowTwo_sup hB hBI)
      (generalizedFitting_sup_sup hnab B) hFT
  rw [E1.nParam_subgroupOf]
  exact key


@[expose] def TypeOneResNoA6 (Y : Type) [Group Y] : Prop :=
  IsPSL 3 2 1 Y ∨
    (∃ p e : ℕ, p.Prime ∧ 3 < p ∧ (e = 1 ∨ e = 2) ∧ (p ^ e % 8 = 1 ∨ p ^ e % 8 = 7) ∧
      IsPSL 2 p e Y) ∨
    ∃ (s : Bool) (p : ℕ), p.Prime ∧ p ≠ 2 ∧ (s = true → p % 4 = 3) ∧ (s = false → p % 4 = 1) ∧
      IsPSLEps3 s p 1 Y

@[expose] def E114OneResNoA6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T : Subgroup G), SQTKGroup G →
    IsSimpleGroup (ASInputs.FStar G) → quasithinIsSylowTwo T →
    CFSG.generalizedFitting G ⊔ T = ⊤ →
      TypeOneResNoA6 (ASInputs.FStar G) → E1.nParam (⊤ : Subgroup G) ≤ 1

theorem e114OneRes_of_noA6 (h : E114OneResNoA6) : E114OneRes := by
  intro G _ _ T hSQ hFs hT hFT hty
  rcases hty with h1 | h6 | h2 | h3
  · exact h G T hSQ hFs hT hFT (Or.inl h1)
  · exact nParam_le_one_of_alt6 h6
  · exact h G T hSQ hFs hT hFT (Or.inr (Or.inl h2))
  · exact h G T hSQ hFs hT hFT (Or.inr (Or.inr h3))


end CFSG.Quasithin.E2.E22N
