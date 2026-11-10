module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import Certificates.Data.S1277Struct

public section

namespace CFSG.Quasithin.H13.I1277

open CFSG.Quasithin.H13.S127.Mod Certificates.Data.S1277Struct
open scoped IsMulCommutative

structure KCod {G : Type} [Group G] (K : Subgroup G) (T : KTab) (κ : G → Nat) : Prop where
  mul : ∀ x ∈ K, ∀ y ∈ K, κ (x * y) = mulN T (κ x) (κ y)
  inj : ∀ x ∈ K, ∀ y ∈ K, κ x = κ y → x = y
  mem : ∀ x ∈ K, κ x ∈ klist T
  surj : ∀ n ∈ klist T, ∃ x ∈ K, κ x = n
  one : κ 1 = oneN T

section KCod

variable {G : Type} [Group G] {K : Subgroup G} {T : KTab} {κ : G → Nat}

theorem KCod.inv (hκ : KCod K T κ)
    (hinv : ∀ n ∈ klist T, invN T n ∈ klist T ∧ mulN T n (invN T n) = oneN T)
    {x : G} (hx : x ∈ K) : κ x⁻¹ = invN T (κ x) := by
  obtain ⟨hmem, hmul⟩ := hinv _ (hκ.mem x hx)
  obtain ⟨y, hy, hyκ⟩ := hκ.surj _ hmem
  have h1 : κ (x * y) = κ 1 := by rw [hκ.mul x hx y hy, hyκ, hmul, hκ.one]
  have h2 : x * y = 1 := hκ.inj _ (K.mul_mem hx hy) _ K.one_mem h1
  have h3 : y = x⁻¹ := eq_inv_of_mul_eq_one_right h2
  rw [← hyκ, h3]


end KCod

end CFSG.Quasithin.H13.I1277

end
