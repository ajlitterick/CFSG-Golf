module

public import CFSG.Quasithin.Background.F6SQTK
public import CFSG.LocalAnalysis.QuasithinUnique.QTKECore

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits

namespace F6

theorem perm_three_sq_key : ∀ g : Equiv.Perm (Fin 3), g ^ 2 = 1 →
    (∀ c : Equiv.Perm (Fin 3), (g * (c * g * c⁻¹)) ^ 2 = 1) → g = 1 := by
  decide +kernel

theorem perm_three_pow_six : ∀ g : Equiv.Perm (Fin 3), g ^ 6 = 1 := by
  decide +kernel

theorem sq_eq_one_of_mem_pCore_perm_three {g : Equiv.Perm (Fin 3)}
    (hg : g ∈ Open.pCore 2 (Equiv.Perm (Fin 3))) : g ^ 2 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup (G := Equiv.Perm (Fin 3)) 2) ⟨g, hg⟩
  have hk' : g ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk')
  have h6 : orderOf g ∣ 6 := orderOf_dvd_of_pow_eq_one (perm_three_pow_six g)
  have hj1 : j ≤ 1 := by
    by_contra hj1
    have : 2 ^ 2 ∣ 6 := (pow_dvd_pow 2 (by omega)).trans (hj ▸ h6)
    omega
  have : orderOf g ∣ 2 := by
    rw [hj]
    exact (pow_dvd_pow 2 hj1).trans (by norm_num)
  exact orderOf_dvd_iff_pow_eq_one.mp this

theorem pCore_perm_three_eq_bot : Open.pCore 2 (Equiv.Perm (Fin 3)) = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  have hn : (Open.pCore 2 (Equiv.Perm (Fin 3))).Normal := CFSG.LieType.BorelTits.pCore_normal 2
  exact perm_three_sq_key g (sq_eq_one_of_mem_pCore_perm_three hg) fun c =>
    sq_eq_one_of_mem_pCore_perm_three ((Open.pCore 2 _).mul_mem hg (hn.conj_mem g hg c))


abbrev SymThreeSq := Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)

theorem signMatched_mul_mem : ∀ a b : SymThreeSq, (a.1 ^ 3 = 1 ↔ a.2 ^ 3 = 1) →
    (b.1 ^ 3 = 1 ↔ b.2 ^ 3 = 1) → ((a * b).1 ^ 3 = 1 ↔ (a * b).2 ^ 3 = 1) := by
  decide +kernel

theorem signMatched_inv_mem : ∀ a : SymThreeSq, (a.1 ^ 3 = 1 ↔ a.2 ^ 3 = 1) →
    (a⁻¹.1 ^ 3 = 1 ↔ a⁻¹.2 ^ 3 = 1) := by
  decide +kernel

@[expose] def signMatched : Subgroup SymThreeSq where
  carrier := {x | x.1 ^ 3 = 1 ↔ x.2 ^ 3 = 1}
  mul_mem' := fun {a b} ha hb => signMatched_mul_mem a b ha hb
  one_mem' := Iff.rfl
  inv_mem' := fun {a} ha => signMatched_inv_mem a ha

instance : DecidablePred (· ∈ signMatched) := fun x =>
  inferInstanceAs (Decidable (x.1 ^ 3 = 1 ↔ x.2 ^ 3 = 1))


theorem swap_pair_mul : ∀ u v : Equiv.Perm (Fin 3), (u = 1 ∨ u = Equiv.swap 1 2) →
    (v = 1 ∨ v = Equiv.swap 1 2) → (u * v = 1 ∨ u * v = Equiv.swap 1 2) := by
  decide +kernel

theorem swap_pair_inv : ∀ u : Equiv.Perm (Fin 3), (u = 1 ∨ u = Equiv.swap 1 2) →
    (u⁻¹ = 1 ∨ u⁻¹ = Equiv.swap 1 2) := by
  decide +kernel

@[expose] def signMatchedLeft : Subgroup ↥signMatched where
  carrier := {x | x.1.2 = 1 ∨ x.1.2 = Equiv.swap 1 2}
  mul_mem' := fun {a b} ha hb => swap_pair_mul a.1.2 b.1.2 ha hb
  one_mem' := Or.inl rfl
  inv_mem' := fun {a} ha => swap_pair_inv a.1.2 ha

@[expose] def signMatchedRight : Subgroup ↥signMatched where
  carrier := {x | x.1.1 = 1 ∨ x.1.1 = Equiv.swap 1 2}
  mul_mem' := fun {a b} ha hb => swap_pair_mul a.1.1 b.1.1 ha hb
  one_mem' := Or.inl rfl
  inv_mem' := fun {a} ha => swap_pair_inv a.1.1 ha

instance : DecidablePred (· ∈ signMatchedLeft) := fun x =>
  inferInstanceAs (Decidable (x.1.2 = 1 ∨ x.1.2 = Equiv.swap 1 2))

instance : DecidablePred (· ∈ signMatchedRight) := fun x =>
  inferInstanceAs (Decidable (x.1.1 = 1 ∨ x.1.1 = Equiv.swap 1 2))

instance : DecidablePred (· ∈ signMatchedLeft ⊓ signMatchedRight) := fun x =>
  decidable_of_iff (x ∈ signMatchedLeft ∧ x ∈ signMatchedRight) Subgroup.mem_inf.symm


theorem perm_three_cube_mul : ∀ u v : Equiv.Perm (Fin 3), u ^ 3 = 1 → v ^ 3 = 1 →
    (u * v) ^ 3 = 1 := by
  decide +kernel


@[expose] def signMatchedThree : Subgroup ↥signMatched where
  carrier := {x | x.1.1 ^ 3 = 1 ∧ x.1.2 ^ 3 = 1}
  mul_mem' := fun {a b} ha hb =>
    ⟨perm_three_cube_mul _ _ ha.1 hb.1, perm_three_cube_mul _ _ ha.2 hb.2⟩
  one_mem' := ⟨one_pow 3, one_pow 3⟩
  inv_mem' := fun {a} ha => ⟨by simp [inv_pow, ha.1], by simp [inv_pow, ha.2]⟩

instance : DecidablePred (· ∈ signMatchedThree) := fun x =>
  inferInstanceAs (Decidable (x.1.1 ^ 3 = 1 ∧ x.1.2 ^ 3 = 1))


end F6

end CFSG.Quasithin
