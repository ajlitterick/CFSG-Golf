module

public import CFSG.LocalAnalysis.ComponentClassification.MinimalNormal

public section

open CFSG.Open

namespace CFSG.ComponentClassification.ElementaryAbelianModule

abbrev moduleStructure {G : Type*} [CommGroup G]
    (prime : ℕ) (hpower : ∀ element : G, element ^ prime = 1) :
    Module (ZMod prime) (Additive G) :=
  AddCommGroup.zmodModule (n := prime) fun element => by
    change prime • Additive.ofMul (Additive.toMul element) = Additive.ofMul (1 : G)
    rw [← ofMul_pow, hpower]

@[expose] noncomputable def linearAutomorphism {G : Type*} [CommGroup G]
    (prime : ℕ) [Module (ZMod prime) (Additive G)] (automorphism : MulAut G) :
    Additive G ≃ₗ[ZMod prime] Additive G := by
  let additiveEquivalence := MulEquiv.toAdditive automorphism
  exact LinearEquiv.ofBijective
    (AddMonoidHom.toZModLinearMap prime additiveEquivalence.toAddMonoidHom)
      additiveEquivalence.bijective

theorem linearAutomorphism_apply {G : Type*} [CommGroup G]
    (prime : ℕ) [Module (ZMod prime) (Additive G)]
    (automorphism : MulAut G) (element : Additive G) :
    linearAutomorphism prime automorphism element =
      Additive.ofMul (automorphism (Additive.toMul element)) := rfl

@[expose] noncomputable def linearAction {G H : Type*} [Group G] [CommGroup H]
    (prime : ℕ) [Module (ZMod prime) (Additive H)] (action : G →* MulAut H) :
    G →* (Additive H ≃ₗ[ZMod prime] Additive H) := by
  refine
    { toFun := fun element => linearAutomorphism prime (action element)
      map_one' := ?_
      map_mul' := ?_ }
  · apply LinearEquiv.ext
    intro member
    rw [linearAutomorphism_apply, map_one]
    rfl
  · intro left right
    apply LinearEquiv.ext
    intro member
    rw [linearAutomorphism_apply, map_mul]
    rfl

theorem linearAction_apply {G H : Type*} [Group G] [CommGroup H]
    (prime : ℕ) [Module (ZMod prime) (Additive H)] (action : G →* MulAut H)
    (actor : G) (element : Additive H) :
    linearAction prime action actor element = Additive.ofMul ((action actor) (Additive.toMul element)) :=
  rfl


theorem card_eq_pow_finrank {G : Type*} [CommGroup G] [Finite G]
    (prime : ℕ) [Fact prime.Prime] [Module (ZMod prime) (Additive G)] :
    Nat.card G = prime ^ Module.finrank (ZMod prime) (Additive G) := by
  have hcard := Module.natCard_eq_pow_finrank (K := ZMod prime) (V := Additive G)
  have hadditiveCard : Nat.card (Additive G) = Nat.card G :=
    (Nat.card_congr (Additive.ofMul : G ≃ Additive G)).symm
  rw [hadditiveCard] at hcard
  simpa using hcard

abbrev subgroupCommGroup {G : Type*} [Group G]
    (subgroup : Subgroup G) (hcommutative : IsMulCommutative subgroup) : CommGroup subgroup :=
  { subgroup.toGroup with mul_comm := isMulCommutative_iff.mp hcommutative }


end CFSG.ComponentClassification.ElementaryAbelianModule
