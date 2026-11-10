module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotCores
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotRoots

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective ne_succ')
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore centralizerPerfectCore_anti)
open CFSG.SeitzReduction.UnitaryPilot (modelToG modelToG_mono modelToG_map_conj)

section Tori

variable (K : Type) [Field K] {n : ℕ}

@[expose] noncomputable def diagTorusSp (P : Subgroup (Fin n → Kˣ)) : Subgroup (StatedSp n K) :=
  P.map (diagSp K n)


@[expose] def planeTorusParam (I : Finset (Fin n)) : Subgroup (Fin n → Kˣ) where
  carrier := {t | ∀ i ∈ I, t i = 1}
  one_mem' := fun _ _ => rfl
  mul_mem' := fun {t s} ht hs i hi => by
    simp only [Pi.mul_apply, ht i hi, hs i hi, mul_one]
  inv_mem' := fun {t} ht i hi => by
    simp only [Pi.inv_apply, ht i hi, inv_one]

@[expose] noncomputable def planeTorusSp (I : Finset (Fin n)) : Subgroup (StatedSp n K) :=
  diagTorusSp K (planeTorusParam K I)

variable {K}


theorem diagTorusSp_mono {P Q : Subgroup (Fin n → Kˣ)} (h : P ≤ Q) :
    diagTorusSp K P ≤ diagTorusSp K Q :=
  map_mono h


theorem leviTorusSp_eq_diagTorusSp (J : Finset (Fin n)) :
    leviTorusSp K J = diagTorusSp K (leviTorusParam K J) :=
  rfl


theorem mem_planeTorusParam {I : Finset (Fin n)} {t : Fin n → Kˣ} :
    t ∈ planeTorusParam K I ↔ ∀ i ∈ I, t i = 1 :=
  Iff.rfl

theorem planeTorusSp_anti {I N : Finset (Fin n)} (h : I ⊆ N) :
    planeTorusSp K N ≤ planeTorusSp K I :=
  diagTorusSp_mono fun _ ht i hi => ht i (h hi)

theorem rootTorusSp_eq_planeTorusSp (k : Fin n) :
    rootTorusSp K k = planeTorusSp K ({k}ᶜ : Finset (Fin n)) := by
  ext x
  constructor
  · rintro ⟨κ, rfl⟩
    refine ⟨Pi.mulSingle k κ, fun i hi => ?_, rfl⟩
    have hik : i ≠ k := by simpa using hi
    simp [hik]
  · rintro ⟨t, ht, rfl⟩
    refine ⟨t k, ?_⟩
    rw [rootTorusHom_apply]
    congr 1
    funext i
    by_cases hik : i = k
    · subst hik
      simp
    · rw [Pi.mulSingle_eq_of_ne hik, ht i (by simpa using hik)]

theorem leviTorusParam_tail_eq (a : ℕ) :
    leviTorusParam K (Finset.univ.filter fun j : Fin n => a ≤ j.val) =
      planeTorusParam K (Finset.univ.filter fun j : Fin n => a ≤ j.val) := by
  ext t
  rw [mem_leviTorusParam, mem_planeTorusParam]
  constructor
  · intro ht
    have key : ∀ d : ℕ, ∀ j : Fin n, a ≤ j.val → j.val + d + 1 = n → t j = 1 := by
      intro d
      induction d with
      | zero =>
        intro j hj hjn
        exact (ht j (by simpa using hj)).2 (by omega)
      | succ d ih =>
        intro j hj hjn
        have h1 : j.val + 1 < n := by omega
        rw [(ht j (by simpa using hj)).1 h1]
        exact ih ⟨j.val + 1, h1⟩ (by simp; omega) (by simp; omega)
    intro j hj
    have hj' : a ≤ j.val := by simpa using hj
    exact key (n - 1 - j.val) j hj' (by omega)
  · intro ht j hj
    have hj' : a ≤ j.val := by simpa using hj
    refine ⟨fun h => ?_, fun _ => ht j hj⟩
    rw [ht j hj, ht ⟨j.val + 1, h⟩ (by simp; omega)]

theorem leviTorusSp_tail_eq_planeTorusSp (a : ℕ) :
    leviTorusSp K (Finset.univ.filter fun j : Fin n => a ≤ j.val) =
      planeTorusSp K (Finset.univ.filter fun j : Fin n => a ≤ j.val) := by
  rw [leviTorusSp_eq_diagTorusSp, leviTorusParam_tail_eq, planeTorusSp]

end Tori

section Perm

variable {K : Type} [Field K] {n : ℕ}


end Perm

section TorusCores

variable {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] {n : ℕ}
  (e : L ≃* StatedSp n K)

@[expose] noncomputable def torusCore (P : Subgroup (Fin n → Kˣ)) : Subgroup G :=
  centralizerPerfectCore (modelToG e (diagTorusSp K P))

@[expose] noncomputable def planeCore (I : Finset (Fin n)) : Subgroup G :=
  centralizerPerfectCore (modelToG e (planeTorusSp K I))

theorem planeCore_def (I : Finset (Fin n)) :
    planeCore e I = centralizerPerfectCore (modelToG e (planeTorusSp K I)) :=
  rfl

theorem pieceCore_eq_torusCore (J : Finset (Fin n)) :
    pieceCore e J = torusCore e (leviTorusParam K J) :=
  rfl


theorem pieceCore_tail_eq (a : ℕ) :
    pieceCore e (Finset.univ.filter fun j : Fin n => a ≤ j.val) =
      planeCore e (Finset.univ.filter fun j : Fin n => a ≤ j.val) := by
  rw [pieceCore_def, planeCore_def, leviTorusSp_tail_eq_planeTorusSp]


end TorusCores

section Pair

variable {K : Type} [Field K] {n : ℕ}

variable (K) in
@[expose] def pairTorusParam (a b : Fin n) : Subgroup (Fin n → Kˣ) where
  carrier := {t | t a = t b}
  one_mem' := rfl
  mul_mem' := fun {t s} ht hs => by
    change t a * s a = t b * s b
    rw [ht.out, hs.out]
  inv_mem' := fun {t} ht => by
    change (t a)⁻¹ = (t b)⁻¹
    rw [ht.out]

theorem mem_pairTorusParam {a b : Fin n} {t : Fin n → Kˣ} :
    t ∈ pairTorusParam K a b ↔ t a = t b :=
  Iff.rfl

theorem leviTorusParam_singleton_of_lt {j : Fin n} (h : j.val + 1 < n) :
    leviTorusParam K {j} = pairTorusParam K j ⟨j.val + 1, h⟩ := by
  ext t
  rw [mem_leviTorusParam, mem_pairTorusParam]
  constructor
  · intro ht
    exact (ht j (Finset.mem_singleton_self j)).1 h
  · intro ht i hi
    rw [Finset.mem_singleton] at hi
    subst hi
    exact ⟨fun _ => ht, fun h' => absurd h' (by omega)⟩


end Pair

section Transport


end Transport

end CFSG.SeitzReduction.SymplecticPilot
