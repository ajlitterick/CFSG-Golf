module

public import CFSG.Quasithin.Vol2.Ch11SecBNPE22Cases
public import CFSG.Quasithin.Vol2.Ch11SecBNPStar
public import CFSG.Quasithin.Background.A3Structure36ABasic

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open

theorem isSubnormal_of_open {G : Type} [Group G] {A B : Subgroup G}
    (hAB : CFSG.Open.IsSubnormal A B) (hB : B.IsSubnormal) : A.IsSubnormal :=
  hAB.mathlib hB

theorem nonabelian_of_perfect_surjective {A B : Type} [Group A] [Group B] [Group.IsPerfect A]
    [Nontrivial B] (f : A →* B) (hf : Function.Surjective f) : ∃ a b : B, a * b ≠ b * a := by
  by_contra h
  push Not at h
  have hker : commutator A ≤ f.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv,
      h (f a) (f b)]
    group
  rw [Group.IsPerfect.commutator_eq_top] at hker
  obtain ⟨x, y, hxy⟩ := exists_pair_ne B
  obtain ⟨a, rfl⟩ := hf x
  obtain ⟨b, rfl⟩ := hf y
  apply hxy
  rw [hker (Subgroup.mem_top a), hker (Subgroup.mem_top b)]


end CFSG.Quasithin.Vol2.Ch11.SecB
