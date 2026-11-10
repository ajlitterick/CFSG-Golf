module

public import CFSG.Quasithin.Vol2.KGFactC31RuRefCheck
public import CFSG.Quasithin.Vol2.KGFactC31ArrChain
public import CFSG.Quasithin.Vol2.KGFactC31BadScan
public import CFSG.Sporadic.Schreier.RuCentralizer
public import CFSG.Sporadic.Schreier.RuConj

public section

namespace CFSG.Quasithin.KGC31.Ru

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
  CFSG.Sporadic.RuSchreier CFSG.Quasithin.KGC31 CFSG.Certificates

@[expose] noncomputable def g6G : List (Equiv.Perm (Fin 4060)) :=
  [ruA0, ruA1, ruC0, ruC1, ruNs0, ruNs1]

@[expose] noncomputable def wG (w : List ℤ) : Equiv.Perm (Fin 4060) := evalSigned g6G w

theorem ruNs0_mem' : ruNs0 ∈ ruP := ruP.mul_mem (ruP.mul_mem ruH_mem ruN0_mem) (ruP.inv_mem ruH_mem)

theorem ruNs1_mem' : ruNs1 ∈ ruP := ruP.mul_mem (ruP.mul_mem ruH_mem ruN1_mem) (ruP.inv_mem ruH_mem)

theorem g6G_mem : ∀ g ∈ g6G, g ∈ ruP := by
  intro g hg
  simp only [g6G, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ruA0_mem
  · exact ruA1_mem
  · exact ruC0_mem
  · exact ruC1_mem
  · exact ruNs0_mem'
  · exact ruNs1_mem'

theorem wG_mem (w : List ℤ) : wG w ∈ ruP := evalSigned_mem g6G_mem w

theorem rep_getD_six {t₀ t₁ t₂ t₃ t₄ t₅ : Array ℕ}
    {g₀ g₁ g₂ g₃ g₄ g₅ : Equiv.Perm (Fin 4060)} (h₀ : Rep 4060 t₀ g₀) (h₁ : Rep 4060 t₁ g₁)
    (h₂ : Rep 4060 t₂ g₂) (h₃ : Rep 4060 t₃ g₃) (h₄ : Rep 4060 t₄ g₄) (h₅ : Rep 4060 t₅ g₅) :
    ∀ h < 6, Rep 4060 #[t₀, t₁, t₂, t₃, t₄, t₅][h]! ([g₀, g₁, g₂, g₃, g₄, g₅].getD h 1) := by
  intro h hh
  interval_cases h
  · simpa using h₀
  · simpa using h₁
  · simpa using h₂
  · simpa using h₃
  · simpa using h₄
  · simpa using h₅

theorem rep_g6 :
    ∀ h < 6, Rep 4060 g6A[h]! (g6G.getD h 1) :=
  rep_getD_six rep_ruA0 rep_ruA1 rep_ruC0 rep_ruC1 rep_ruNs0 rep_ruNs1

theorem rep_g6I :
    ∀ h < 6, Rep 4060 g6IA[h]! (g6G.getD h 1)⁻¹ := by
  intro h hh
  have e : g6IA[h]! = ruInv g6A[h]! := by
    rw [g6IA, getElem!_pos (g6A.map ruInv) h (by simpa [g6A] using hh), Array.getElem_map,
      getElem!_pos g6A h (by simpa [g6A] using hh)]
  rw [e]
  exact rep_invCand_of_rep (rep_g6 h hh)

theorem rep_wA {w : List ℤ} (hw : lettersOK 6 w = true) :
    Rep 4060 (wA w) (wG w) :=
  rep_wordA_evalSigned rep_g6 rep_g6I w hw

theorem rep_ruInv' {t : Array ℕ} {g : Equiv.Perm (Fin 4060)} (ht : Rep 4060 t g) :
    Rep 4060 (ruInv t) g⁻¹ :=
  rep_invCand_of_rep ht

theorem evalSigned_mem_of_letters {G : Type*} [Group G] {H : Subgroup G} {gens : List G} :
    ∀ {w : List ℤ}, (∀ l ∈ w, gens.getD (l.natAbs - 1) 1 ∈ H) → evalSigned gens w ∈ H
  | [], _ => H.one_mem
  | l :: w, h => by
    rw [evalSigned_cons]
    refine H.mul_mem ?_ (evalSigned_mem_of_letters fun l' hl' => h l' (List.mem_cons_of_mem _ hl'))
    split
    · exact h l List.mem_cons_self
    · exact H.inv_mem (h l List.mem_cons_self)

theorem wG_memC {w : List ℤ} (hw : w.all (fun l => l.natAbs == 3 || l.natAbs == 4) = true) :
    wG w ∈ ruC := by
  refine evalSigned_mem_of_letters fun l hl => ?_
  have h := List.all_eq_true.mp hw l hl
  rw [Bool.or_eq_true, beq_iff_eq, beq_iff_eq] at h
  rcases h with h | h <;> rw [h]
  · exact ruC0_memC
  · exact ruC1_memC

theorem wG_memN {w : List ℤ} (hw : w.all (fun l => l.natAbs == 5 || l.natAbs == 6) = true) :
    wG w ∈ ruN := by
  refine evalSigned_mem_of_letters fun l hl => ?_
  have h := List.all_eq_true.mp hw l hl
  rw [Bool.or_eq_true, beq_iff_eq, beq_iff_eq] at h
  rcases h with h | h <;> rw [h]
  · exact ruNs0_memN
  · exact ruNs1_memN

theorem rep_getD_two' {t₀ t₁ : Array ℕ} {g₀ g₁ : Equiv.Perm (Fin 4060)}
    (h₀ : Rep 4060 t₀ g₀) (h₁ : Rep 4060 t₁ g₁) :
    ∀ h < 2, Rep 4060 #[t₀, t₁][h]! ([g₀, g₁].getD h 1) := by
  intro h hh
  interval_cases h
  · simpa using h₀
  · simpa using h₁

theorem rep_getD_two_inv' {t₀ t₁ : Array ℕ} {g₀ g₁ : Equiv.Perm (Fin 4060)}
    (h₀ : Rep 4060 t₀ g₀⁻¹) (h₁ : Rep 4060 t₁ g₁⁻¹) :
    ∀ h < 2, Rep 4060 #[t₀, t₁][h]! ([g₀, g₁].getD h 1)⁻¹ := by
  intro h hh
  interval_cases h
  · simpa using h₀
  · simpa using h₁

theorem ab_gens :
    (∀ h < 2, Rep 4060 (#[ruA0A, ruA1A] : Array (Array ℕ))[h]! ([ruA0, ruA1].getD h 1)) ∧
      ∀ h < 2, Rep 4060 (#[ruInv ruA0A, ruInv ruA1A] : Array (Array ℕ))[h]!
        ([ruA0, ruA1].getD h 1)⁻¹ :=
  ⟨rep_getD_two' rep_ruA0 rep_ruA1, rep_getD_two_inv' (rep_ruInv' rep_ruA0) (rep_ruInv' rep_ruA1)⟩

theorem rep_abA {w : List ℤ} (hw : lettersOK 2 w = true) :
    Rep 4060 (abA w) (evalSigned [ruA0, ruA1] w) :=
  rep_wordA_evalSigned ab_gens.1 ab_gens.2 w hw

theorem evalSigned_ab_mem (w : List ℤ) : evalSigned [ruA0, ruA1] w ∈ ruP :=
  evalSigned_mem (fun g hg => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · exact ruA0_mem
    · exact ruA1_mem) w

theorem rep_conjA {h t : Array ℕ} {hg tg : Equiv.Perm (Fin 4060)} (hh : Rep 4060 h hg)
    (ht : Rep 4060 t tg) : Rep 4060 (conjA h t) (hg * tg * hg⁻¹) :=
  rep_compA (rep_compA hh ht) (rep_ruInv' hh)


theorem length_fixedList_eq {t : Array ℕ} {g : Equiv.Perm (Fin 4060)} (ht : Rep 4060 t g) :
    (fixedList 4060 t).length = (fixSet g).ncard := by
  rw [← ncard_finSet (pointList_fixedList t), finSet_fixedList ht]


theorem normsA_iff {k : ℕ} {v : Fin k → Equiv.Perm (Fin 4060)} {sp : List (Array ℕ)}
    {bv : List (Array ℕ)} (hbv : List.Forall₂ (Rep 4060) bv (List.ofFn v)) (hsp : sp = spanA bv)
    {bs : List (Array ℕ)} {gs : List (Equiv.Perm (Fin 4060))}
    (hbs : List.Forall₂ (Rep 4060) bs gs) {t ti : Array ℕ} {g : Equiv.Perm (Fin 4060)}
    (ht : Rep 4060 t g) (hti : Rep 4060 ti g⁻¹) :
    normsA t ti bs sp = true ↔ ∀ b ∈ gs, ∃ c, eElt v c = g * b * g⁻¹ := by
  subst hsp
  rw [normsA, List.all_eq_true]
  constructor
  · intro h b hb
    obtain ⟨u, hu, hub⟩ := KGC31.exists_left_of_forall₂ hbs hb
    exact (inA_spanA_iff hbv (rep_cjA ht hti hub)).mp (h u hu)
  · intro h u hu
    obtain ⟨b, hb, hub⟩ := KGC31.exists_right_of_forall₂ hbs hu
    exact (inA_spanA_iff hbv (rep_cjA ht hti hub)).mpr (h b hb)


end CFSG.Quasithin.KGC31.Ru

end
