module

public import CFSG.Sporadic.Fi22.Uniqueness
public import CFSG.Sporadic.Fi22.FischerOpen
public import CFSG.Sporadic.Fi23.Uniqueness
public import CFSG.Sporadic.Fi23.FischerOpen
public import CFSG.Sporadic.Fi24.Fischer
public import CFSG.Sporadic.Fi24.FischerOpen
public import CFSG.Sporadic.Fi24.EdgeSwapCert
public import CFSG.Fischer.Polar.Facts
public import CFSG.Sporadic.Fi22.LH.Facts

public section

namespace CFSG.Fischer

open CFSG.Blueprint.Fischer CFSG.Open

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Facts

variable {tr cs : Set (Set Sporadic.Fi23.D23)} {r : tr} (hTF : Fi23Facts tr cs r)
  (hfix22 : ∀ g : Sporadic.Fi22.J, g ^ 2 = 1 → g ≠ 1 →
    Nat.card {x : Sporadic.Fi22.D // g * (x : Sporadic.Fi22.J) * g⁻¹ = x} ∈
      ({54, 182, 694} : Set ℕ))
  (hcent22 : ∀ (χ : Sporadic.Fi22.D) (σ : Equiv.Perm Sporadic.Fi22.D),
    (∀ g : Sporadic.Fi22.J, g * χ = χ * g →
      σ * Pair.conjPerm Sporadic.Fi22.pair_D g = Pair.conjPerm Sporadic.Fi22.pair_D g * σ) →
    σ = 1 ∨ σ = Pair.conjPerm Sporadic.Fi22.pair_D (χ : Sporadic.Fi22.J))
  {d1 t2 : Sporadic.Fi23.J} (hd1 : d1 ∈ LocalClass Sporadic.Fi23.D23 Sporadic.Fi23.d)
  (hcover : ∀ g : Sporadic.Fi23.J, g ^ 2 = 1 → g ≠ 1 →
    IsConj Sporadic.Fi23.d g ∨ IsConj (Sporadic.Fi23.d * d1) g ∨ IsConj t2 g)

include hTF hfix22 hcent22 hd1 hcover in
theorem full_of_facts :
    ∀ k : Fin 3, Subgroup.center (Carrier k) = ⊥ ∧ IsSimpleGroup (commutator (Carrier k)) ∧
      ∃ D : Set (Carrier k), HasType k (Carrier k) D ∧
        (∀ E : Set (Carrier k), Pair (Carrier k) E → E = D) ∧ LocalStructure k D ∧
        ∀ (X : Type) [Group X] (E : Set X), Pair X E →
          Subgroup.center X = ⊥ → IsSimpleGroup (commutator X) → HasType k X E →
          ∃ iso : X ≃* Carrier k, iso '' E = D := by
  have hFF := Sporadic.Fi22.fi22Facts polarFacts hyperovalFacts
  intro k
  match k with
  | 0 =>
    obtain ⟨h1, h2, h3, h4, h5⟩ := Sporadic.Fi22.existence_carrier
    exact ⟨h1, h2, _, h3, h4, h5, fun X _ E hP hZ hS hT =>
      Sporadic.Fi22.fischer_uniqueness_zero polarFacts X E hP hZ hS hT⟩
  | 1 =>
    obtain ⟨h1, h2, h3, h4, h5⟩ := Sporadic.Fi23.existence_carrier
    exact ⟨h1, h2, _, h3, h4, h5, fun X _ E hP hZ hS hT =>
      Sporadic.Fi23.fischer_uniqueness_one polarFacts hyperovalFacts hFF X E hP hZ hS hT⟩
  | 2 =>
    obtain ⟨h1, h2, h3, h4, h5⟩ := Sporadic.Fi24.existence_carrier polarFacts hyperovalFacts hFF
      hTF hfix22 hcent22 Sporadic.Fi24.edgeSwap_a hd1 hcover
    exact ⟨h1, h2, _, h3, h4, h5, fun X _ E hP hZ hS hT =>
      Sporadic.Fi24.fischer_uniqueness_two polarFacts hyperovalFacts hFF hTF hfix22 hcent22
        Sporadic.Fi24.edgeSwap_a hd1 hcover X E hP hZ hS hT⟩


end Facts

end CFSG.Fischer
