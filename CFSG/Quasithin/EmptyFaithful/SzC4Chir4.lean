module

public import CFSG.Quasithin.EmptyFaithful.SzC4ChirX
public import CFSG.Quasithin.EmptyFaithful.SzC4Sl4Gen
public import CFSG.Quasithin.Vol2.Ch12Sec2OrbitG2Cert

public section

namespace CFSG.Quasithin.SzC4

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.FLc
open CFSG.Quasithin.A38c10
open scoped commutatorElement Pointwise

theorem parabData1 : ParabData (QI 4 {1}) Rrad1 gb1 where
  R_le := Rrad1_le_QI
  R_norm := fun _ hx _ hr => Rrad1_normal hx hr
  R_two := IsPGroup.of_card (n := 3) (by rw [card_Rrad1]; norm_num)
  max := le_Rrad1_of_normal2
  gb_mem := gb1_mem
  gb_pow := gb1_pow
  comm := comm_Rrad1

theorem parabData3 : ParabData (QI 4 {3}) Rrad3 gb3 where
  R_le := Rrad3_le_QI
  R_norm := fun _ hx _ hr => Rrad3_normal hx hr
  R_two := IsPGroup.of_card (n := 3) (by rw [card_Rrad3]; norm_num)
  max := le_Rrad3_of_normal2
  gb_mem := gb3_mem
  gb_pow := gb3_pow
  comm := comm_Rrad3

theorem CmT_pow : CmT ^ 7 = 1 := by decide

@[expose] def eRrad1Hom : Multiplicative (Fin 1 → Fin 3 → ZMod 2) →* ↥Rrad1 where
  toFun x := ⟨r1 (Multiplicative.toAdd x 0), r1_mem_Rrad1 _⟩
  map_one' := Subtype.ext r1_zero
  map_mul' _ _ := Subtype.ext (r1_mul _ _).symm

@[expose] def eRrad3Hom : Multiplicative (Fin 1 → Fin 3 → ZMod 2) →* ↥Rrad3 where
  toFun x := ⟨s3 (Multiplicative.toAdd x 0), s3_mem_Rrad3 _⟩
  map_one' := Subtype.ext s3_zero
  map_mul' _ _ := Subtype.ext (s3_mul _ _).symm

@[expose] noncomputable def eRrad1 : Multiplicative (Fin 1 → Fin 3 → ZMod 2) ≃* ↥Rrad1 :=
  MulEquiv.ofBijective eRrad1Hom
    ⟨fun x y hxy => by
      have := r1_injective (congrArg Subtype.val hxy)
      apply Multiplicative.toAdd.injective
      funext i
      have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      exact this, fun r => by
      obtain ⟨v, hv⟩ := mem_Rrad1_iff.1 r.2
      exact ⟨Multiplicative.ofAdd (fun _ => v), Subtype.ext hv.symm⟩⟩

@[expose] noncomputable def eRrad3 : Multiplicative (Fin 1 → Fin 3 → ZMod 2) ≃* ↥Rrad3 :=
  MulEquiv.ofBijective eRrad3Hom
    ⟨fun x y hxy => by
      have := s3_injective (congrArg Subtype.val hxy)
      apply Multiplicative.toAdd.injective
      funext i
      have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      exact this, fun r => by
      obtain ⟨u, hu⟩ := mem_Rrad3_iff.1 r.2
      exact ⟨Multiplicative.ofAdd (fun _ => u), Subtype.ext hu.symm⟩⟩

theorem eRrad1_apply (x : Multiplicative (Fin 1 → Fin 3 → ZMod 2)) :
    ((eRrad1 x : ↥Rrad1) : SLt 4) = r1 (Multiplicative.toAdd x 0) := rfl

theorem eRrad3_apply (x : Multiplicative (Fin 1 → Fin 3 → ZMod 2)) :
    ((eRrad3 x : ↥Rrad3) : SLt 4) = s3 (Multiplicative.toAdd x 0) := rfl

theorem chi_Rrad1 (A : ChiAPI) :
    A.chi ↥Rrad1 (conjOn Rrad1 gb1 parabData1.gb_normalizes) = A.chiMat CmT := by
  have hF : Fintype.card (ZMod 2) = 2 := ZMod.card 2
  have h := A.chi_vecAut hF 1 CmT CmT_pow
  rw [Nat.cast_one, one_mul] at h
  rw [← h]
  refine (A.chi_congr eRrad1 (A.vecAut 1 CmT CmT_pow) _ fun x => ?_)
  apply Subtype.ext
  rw [conjOn_apply, eRrad1_apply, eRrad1_apply, A.vecAut_apply, conj_r1]

theorem chi_Rrad3 (A : ChiAPI) :
    A.chi ↥Rrad3 (conjOn Rrad3 gb3 parabData3.gb_normalizes) = A.chiMat Cm := by
  have hF : Fintype.card (ZMod 2) = 2 := ZMod.card 2
  have h := A.chi_vecAut hF 1 Cm Cm_pow
  rw [Nat.cast_one, one_mul] at h
  rw [← h]
  refine (A.chi_congr eRrad3 (A.vecAut 1 Cm Cm_pow) _ fun x => ?_)
  apply Subtype.ext
  rw [conjOn_apply, eRrad3_apply, eRrad3_apply, A.vecAut_apply, conj_s3]

variable {G : Type} [Group G] [Finite G]

theorem exists_lift_order_seven {L : Subgroup G} {α : ↥L →* SLt 4}
    (hker : α.ker = CFSG.pCore 2 ↥L) (hsurj : Function.Surjective α) {gb : SLt 4}
    (hgb : gb ^ 7 = 1) : ∃ l : ↥L, α l = gb ∧ l ^ 7 = 1 := by
  obtain ⟨l₀, hl₀⟩ := hsurj gb
  have hk := ker_eq_open hker
  have h7 : l₀ ^ 7 ∈ α.ker := by
    rw [MonoidHom.mem_ker, map_pow, hl₀]
    exact hgb
  rw [hk] at h7
  obtain ⟨b, hb⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥L) 2) ⟨_, h7⟩
  have hb' : (l₀ ^ 7) ^ 2 ^ b = 1 := by
    simpa using congrArg (fun y : ↥(CFSG.Open.pCore 2 ↥L) => (y : ↥L)) hb
  have hcop : Nat.Coprime (2 ^ b) 7 := Nat.Coprime.pow_left b (by norm_num)
  obtain ⟨j, -, hj⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop (by norm_num)
  have hmj : 2 ^ b * j = 7 * (2 ^ b * j / 7) + 1 := by
    have := Nat.div_add_mod (2 ^ b * j) 7
    omega
  refine ⟨l₀ ^ (2 ^ b * j), ?_, ?_⟩
  · rw [map_pow, hl₀, hmj, pow_succ, pow_mul, hgb, one_pow, one_mul]
  · calc (l₀ ^ (2 ^ b * j)) ^ 7 = ((l₀ ^ 7) ^ 2 ^ b) ^ j := by
          rw [← pow_mul, ← pow_mul, ← pow_mul]
          congr 1
          ring
      _ = 1 := by rw [hb', one_pow]


end CFSG.Quasithin.SzC4
