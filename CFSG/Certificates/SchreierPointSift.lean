module

public import CFSG.Certificates.SchreierChainData

public section

namespace CFSG.Certificates

@[expose] def schreierPointSiftSucceeds {n : ℕ} (levels : List (Fin n × SchreierOrbitState n))
    (h : Equiv.Perm (Fin n)) : Bool :=
  (schreierSiftResidual levels h).isSome

theorem schreierPointSiftSucceeds_eq_true_iff {n : ℕ}
    (levels : List (Fin n × SchreierOrbitState n)) (h : Equiv.Perm (Fin n)) :
    schreierPointSiftSucceeds levels h = true ↔ ∃ r, schreierSiftResidual levels h = some r := by
  simp [schreierPointSiftSucceeds, Option.isSome_iff_exists]

theorem schreierPointSiftSucceeds_of_siftSucceeds {n : ℕ}
    {levels : List (Fin n × SchreierOrbitState n)} {h : Equiv.Perm (Fin n)}
    (hs : schreierSiftSucceeds levels h = true) : schreierPointSiftSucceeds levels h = true :=
  (schreierPointSiftSucceeds_eq_true_iff levels h).2
    ⟨1, (schreierSiftSucceeds_eq_true_iff levels h).1 hs⟩

namespace RawSchreierDatum

@[expose] def pointSift {n : ℕ} (Q : RawSchreierDatum n) (h : Equiv.Perm (Fin n))
    (i : ℕ) : Bool :=
  schreierPointSiftSucceeds (Q.siftLevels Q.orbitTables i) h


@[expose] def pointCheck {n : ℕ} (Q : RawSchreierDatum n) : Bool :=
  let initialOK := (List.finRange Q.originalCount).all fun j =>
    schreierPermEq (Q.strong.get (Fin.castLE Q.originalCount_le j)) (Q.original.get j)
  let wordsOK := (List.finRange Q.strongCount).all fun j =>
    if hj : Q.originalCount ≤ j.val then
      schreierPermEq (Q.strong.get j) (Q.derivationValue j hj)
    else true
  let tables := Q.orbitTables
  let schreierOK := (List.finRange Q.baseCount).all fun i =>
    let q := tables.get i
    (List.finRange n).all fun x =>
      match q.transversal? x with
      | none => true
      | some tx => (Q.levelSteps i.val).all fun s =>
        match q.transversal? (s x) with
        | none => false
        | some ty =>
          schreierPointSiftSucceeds (Q.siftLevels tables (i.val + 1)) (ty⁻¹ * s * tx)
  initialOK && wordsOK && schreierOK

private theorem point_row_check {n : ℕ} (q : SchreierOrbitState n)
    (steps : List (Equiv.Perm (Fin n))) (levels : List (Fin n × SchreierOrbitState n))
    (x : Fin n) :
    (match q.transversal? x with
      | none => true
      | some tx => steps.all fun s =>
        match q.transversal? (s x) with
        | none => false
        | some ty => schreierPointSiftSucceeds levels (ty⁻¹ * s * tx)) = true ↔
      ∀ tx, q.transversal? x = some tx → ∀ s ∈ steps, ∃ ty,
        q.transversal? (s x) = some ty ∧
          schreierPointSiftSucceeds levels (ty⁻¹ * s * tx) = true := by
  cases hx : q.transversal? x with
  | none => simp
  | some tx =>
    simp only [List.all_eq_true, Option.some.injEq, forall_eq']
    apply forall_congr'
    intro s
    apply forall_congr'
    intro _
    cases q.transversal? (s x) <;> simp

theorem pointCheck_eq_true_iff {n : ℕ} (Q : RawSchreierDatum n) :
    Q.pointCheck = true ↔
      (∀ j : Fin Q.originalCount,
        Q.strong.get (Fin.castLE Q.originalCount_le j) = Q.original.get j) ∧
      (∀ (j : Fin Q.strongCount) (hj : Q.originalCount ≤ j.val),
        Q.strong.get j = Q.derivationValue j hj) ∧
      (∀ (i : Fin Q.baseCount) (x : Fin n) (tx : Equiv.Perm (Fin n)),
        (Q.orbitTables.get i).transversal? x = some tx →
        ∀ s ∈ Q.levelSteps i.val, ∃ ty : Equiv.Perm (Fin n),
          (Q.orbitTables.get i).transversal? (s x) = some ty ∧
          schreierPointSiftSucceeds (Q.siftLevels Q.orbitTables (i.val + 1))
            (ty⁻¹ * s * tx) = true) := by
  simp [pointCheck, List.all_eq_true, schreierPermEq_eq_true_iff, point_row_check, and_assoc]

end RawSchreierDatum

@[expose] def ValidPointSchreier {n : ℕ} (Q : RawSchreierDatum n) : Prop :=
  Q.pointCheck = true

instance instDecidableValidPointSchreier {n : ℕ} (Q : RawSchreierDatum n) :
    Decidable (ValidPointSchreier Q) :=
  inferInstanceAs (Decidable (Q.pointCheck = true))

theorem validPointSchreier_iff {n : ℕ} (Q : RawSchreierDatum n) :
    ValidPointSchreier Q ↔
      (∀ j : Fin Q.originalCount,
        Q.strong.get (Fin.castLE Q.originalCount_le j) = Q.original.get j) ∧
      (∀ (j : Fin Q.strongCount) (hj : Q.originalCount ≤ j.val),
        Q.strong.get j = Q.derivationValue j hj) ∧
      (∀ (i : Fin Q.baseCount) (x : Fin n) (tx : Equiv.Perm (Fin n)),
        (Q.orbitSearch i).transversal? x = some tx →
        ∀ s ∈ Q.levelSteps i.val, ∃ ty : Equiv.Perm (Fin n),
          (Q.orbitSearch i).transversal? (s x) = some ty ∧
          schreierPointSiftSucceeds (Q.siftLevels Q.orbitTables (i.val + 1))
            (ty⁻¹ * s * tx) = true) := by
  simpa only [ValidPointSchreier, RawSchreierDatum.orbitTables_get] using Q.pointCheck_eq_true_iff

theorem ValidSchreier.validPointSchreier {n : ℕ} {Q : RawSchreierDatum n}
    (hQ : ValidSchreier Q) : ValidPointSchreier Q := by
  obtain ⟨h1, h2, -, h4⟩ := (validSchreier_iff Q).1 hQ
  refine (validPointSchreier_iff Q).2 ⟨h1, h2, fun i x tx hx s hs => ?_⟩
  obtain ⟨ty, hty, hsift⟩ := h4 i x tx hx s hs
  exact ⟨ty, hty, schreierPointSiftSucceeds_of_siftSucceeds hsift⟩

structure CompactTransversalCode (n k : ℕ) where
  parent : Fin n → Option (Fin n × SchreierLetter k)

@[expose] def CompactTransversalCode.word {n k : ℕ} (c : CompactTransversalCode n k) :
    ℕ → Fin n → List (SchreierLetter k)
  | 0, _ => []
  | fuel + 1, x =>
    match c.parent x with
    | none => []
    | some (p, a) => a :: c.word fuel p


end CFSG.Certificates
