module

public import CFSG.GH74.RouteH
public import CFSG.GH74.GLS.AssemblyComponents
public import CFSG.GH74.GLS.AssemblyBridge
public import CFSG.LocalAnalysis.ComponentInitial.SmallLinearIsomorphisms

public section

namespace CFSG.GH74.GLS

open Subgroup Blueprint Assembly.LowTwoRank

namespace C23List

variable {G : Type} [Group G]

theorem of_psl2 {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (h5 : 5 ≤ p ^ f)
    (h : LieModel G .PSL 2 p f) : C23List G :=
  Or.inl ⟨p, f, hp, hp2, hf, Or.inl ⟨h5, h⟩⟩

theorem of_psl3 {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (h : LieModel G .PSL 3 p f) : C23List G :=
  Or.inl ⟨p, f, hp, hp2, hf, Or.inr (Or.inl h)⟩

theorem of_psu3 {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (h : LieModel G .PSU 3 p f) : C23List G :=
  Or.inl ⟨p, f, hp, hp2, hf, Or.inr (Or.inr (Or.inl h))⟩

theorem of_psp4 {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (h3 : 3 < p ^ f)
    (h : LieModel G .PSp 2 p f) : C23List G :=
  Or.inl ⟨p, f, hp, hp2, hf, Or.inr (Or.inr (Or.inr (Or.inl ⟨h3, Or.inl h⟩)))⟩

theorem of_g2 {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (h3 : 3 < p ^ f)
    (h : LieModel G .G2 0 p f) : C23List G :=
  Or.inl ⟨p, f, hp, hp2, hf, Or.inr (Or.inr (Or.inr (Or.inl ⟨h3, Or.inr h⟩)))⟩

theorem of_trialityD4 {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (h : LieModel G .trialityD4 0 p f) : C23List G :=
  Or.inl ⟨p, f, hp, hp2, hf, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))⟩

theorem of_psl4 {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (h3 : 3 < p ^ f)
    (h8 : p ^ f % 8 ≠ 1) (h : LieModel G .PSL 4 p f) : C23List G :=
  Or.inl ⟨p, f, hp, hp2, hf, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h3, Or.inl ⟨h8, h⟩⟩))))⟩

theorem of_psu4 {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (h3 : 3 < p ^ f)
    (h8 : p ^ f % 8 ≠ 7) (h : LieModel G .PSU 4 p f) : C23List G :=
  Or.inl ⟨p, f, hp, hp2, hf, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h3, Or.inr ⟨h8, h⟩⟩))))⟩

theorem of_twistedG2 {f : ℕ} (h : LieModel G .twistedG2 0 3 f) : C23List G :=
  Or.inr (Or.inl ⟨f, h⟩)

theorem of_alt7 (h : Nonempty (G ≃* alternatingGroup (Fin 7))) : C23List G :=
  Or.inr (Or.inr (Or.inl h))

theorem of_alt9 (h : Nonempty (G ≃* alternatingGroup (Fin 9))) : C23List G :=
  Or.inr (Or.inr (Or.inr (Or.inl h)))

theorem of_alt10 (h : Nonempty (G ≃* alternatingGroup (Fin 10))) : C23List G :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))

theorem of_alt11 (h : Nonempty (G ≃* alternatingGroup (Fin 11))) : C23List G :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))

theorem of_M11 (h : NativeSporadic.IsSporadic G .M11) : C23List G :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))

theorem of_U34 (h : LieModel G .PSU 3 2 2) : C23List G :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))

theorem of_M12 (h : NativeSporadic.IsSporadic G .M12) : C23List G :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))

theorem of_J1 (h : NativeSporadic.IsSporadic G .J1) : C23List G :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))

theorem of_McL (h : NativeSporadic.IsSporadic G .McL) : C23List G :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inl h))))))))))

theorem of_Ly (h : NativeSporadic.IsSporadic G .Ly) : C23List G :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inl h)))))))))))

theorem of_ONan (h : NativeSporadic.IsSporadic G .ONan) : C23List G :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr h)))))))))))

theorem of_psl2_four (h : LieModel G .PSL 2 2 2) : C23List G := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨e⟩ := CFSG.LocalAnalysis.ComponentInitial.PSL2_four_alternating_five_model G h
  obtain ⟨e5⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five (ZMod 5)
    (Or.inr (Nat.card_zmod 5))
  exact of_psl2 Nat.prime_five (by decide) le_rfl (by norm_num)
    (Or.inl ⟨by decide, ⟨Nat.prime_five, le_rfl, le_rfl, by decide, by decide⟩, ZMod 5,
      inferInstance, inferInstance, by rw [Nat.card_zmod, pow_one], ⟨e.trans e5.symm⟩⟩)

end C23List

namespace C2StarList

variable {G : Type} [Group G]

theorem toC23List (h : C2StarList G) : C23List G := by
  rcases h with ⟨p, f, hp, hp2, hf, h⟩ | ⟨f, h⟩ | h | h | h | h | h | h | h | h
  · have hodd : Odd (p ^ f) := (hp.eq_two_or_odd'.resolve_left hp2).pow
    rcases h with ⟨h3, h | h | h⟩ | h | h | h | ⟨h3, ⟨h8, h⟩ | ⟨h8, h⟩⟩
    · obtain ⟨k, hk⟩ := hodd
      exact C23List.of_psl2 hp hp2 hf (by omega) h
    · exact C23List.of_psp4 hp hp2 hf h3 h
    · exact C23List.of_g2 hp hp2 hf h3 h
    · exact C23List.of_psl3 hp hp2 hf h
    · exact C23List.of_psu3 hp hp2 hf h
    · exact C23List.of_trialityD4 hp hp2 hf h
    · exact C23List.of_psl4 hp hp2 hf h3 h8 h
    · exact C23List.of_psu4 hp hp2 hf h3 h8 h
  · exact C23List.of_twistedG2 h
  · exact C23List.of_U34 h
  · exact C23List.of_alt7 h
  · exact C23List.of_M11 h
  · exact C23List.of_M12 h
  · exact C23List.of_J1 h
  · exact C23List.of_McL h
  · exact C23List.of_Ly h
  · exact C23List.of_ONan h

theorem of_psp4 {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h3 : 3 < p ^ f)
    (h : LieModel G .PSp 2 p f) : C2StarList G := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | hf
    · simp at h3
    · exact hf
  exact Or.inl ⟨p, f, hp, hp2, hf, Or.inl ⟨h3, Or.inr (Or.inl h)⟩⟩

theorem of_psl4 {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h3 : 3 < p ^ f)
    (h8 : p ^ f % 8 ≠ 1) (h : LieModel G .PSL 4 p f) : C2StarList G := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | hf
    · simp at h3
    · exact hf
  exact Or.inl ⟨p, f, hp, hp2, hf, Or.inr (Or.inr (Or.inr (Or.inr ⟨h3, Or.inl ⟨h8, h⟩⟩)))⟩

theorem of_psu4 {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h3 : 3 < p ^ f)
    (h8 : p ^ f % 8 ≠ 7) (h : LieModel G .PSU 4 p f) : C2StarList G := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | hf
    · simp at h3
    · exact hf
  exact Or.inl ⟨p, f, hp, hp2, hf, Or.inr (Or.inr (Or.inr (Or.inr ⟨h3, Or.inr ⟨h8, h⟩⟩)))⟩

theorem of_McL (h : NativeSporadic.IsSporadic G .McL) : C2StarList G :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))

theorem of_Ly (h : NativeSporadic.IsSporadic G .Ly) : C2StarList G :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))

end C2StarList


theorem L2Meets.mono {G : Type} [Group G] {P Q : Assembly.GroupProp}
    (h : ∀ (K : Type) [Group K], P K → Q K) : L2Meets G P → L2Meets G Q := by
  rintro ⟨x, hx, K, hK, hP⟩
  exact ⟨x, hx, K, hK, h _ hP⟩


end CFSG.GH74.GLS
