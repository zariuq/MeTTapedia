import Mettapedia.GSLT.LanguageDef.Gauthier.Skeleton

namespace Mettapedia.GSLT.LanguageDef.GauthierE2Fuel

open Mettapedia.GSLT.LanguageDef

-- Simultaneous one-step fuel persistence for the E2 evaluator family.
set_option maxHeartbeats 2000000 in
theorem evaluatorFamily_succ : ∀ fuel : Nat,
    (∀ sig program x y world values,
      GauthierE2.eval fuel sig program x y world = some values →
        GauthierE2.eval (fuel + 1) sig program x y world = some values) ∧
    (∀ sig body iterations x₁ x₂ world values,
      GauthierE2.loopIter fuel sig body iterations x₁ x₂ world = some values →
        GauthierE2.loopIter (fuel + 1) sig body iterations x₁ x₂ world = some values) ∧
    (∀ sig first second iterations x₁ x₂ world values,
      GauthierE2.loop2Iter fuel sig first second iterations x₁ x₂ world = some values →
        GauthierE2.loop2Iter (fuel + 1) sig first second iterations x₁ x₂ world = some values) ∧
    (∀ sig first second iterations x₁ x₂ world values,
      GauthierE2.loop2sndIter fuel sig first second iterations x₁ x₂ world = some values →
        GauthierE2.loop2sndIter (fuel + 1) sig first second iterations x₁ x₂ world = some values) ∧
    (∀ sig predicate target seen candidate world values,
      GauthierE2.comprSearch fuel sig predicate target seen candidate world = some values →
        GauthierE2.comprSearch (fuel + 1) sig predicate target seen candidate world = some values) := by
  intro fuel
  induction fuel with
  | zero =>
      simp [GauthierE2.eval, GauthierE2.loopIter, GauthierE2.loop2Iter,
        GauthierE2.loop2sndIter, GauthierE2.comprSearch]
  | succ fuel inductionHypothesis =>
      obtain ⟨evalIH, loopIH, loop2IH, loop2sndIH, comprIH⟩ := inductionHypothesis
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro sig program x y world values success
        cases program with
        | node id children =>
          rw [GauthierE2.eval] at success ⊢
          split at success
          · contradiction
          · split at success <;>
              simp_all (config := { maxSteps := 1000000 }) [Option.bind_eq_some_iff] <;>
              aesop
      · intro sig body iterations x₁ x₂ world values success
        cases iterations with
        | zero => simpa only [GauthierE2.loopIter] using success
        | succ iterations =>
          rw [GauthierE2.loopIter] at success ⊢
          cases hEval : GauthierE2.eval fuel sig body x₁ x₂ world with
          | none => simp [hEval] at success
          | some next₁ =>
            cases hIncrement : GauthierE2.singletonHeadIncr x₂ with
            | none => simp [hEval, hIncrement] at success
            | some next₂ =>
              have hLoop :
                  GauthierE2.loopIter fuel sig body iterations next₁ next₂ world =
                    some values := by
                simpa [hEval, hIncrement] using success
              have hEval' := evalIH sig body x₁ x₂ world next₁ hEval
              have hLoop' :=
                loopIH sig body iterations next₁ next₂ world values hLoop
              simp [hEval', hLoop']
      · intro sig first second iterations x₁ x₂ world values success
        cases iterations with
        | zero => simpa only [GauthierE2.loop2Iter] using success
        | succ iterations =>
          rw [GauthierE2.loop2Iter] at success ⊢
          cases hFirst : GauthierE2.eval fuel sig first x₁ x₂ world with
          | none => simp [hFirst] at success
          | some next₁ =>
            cases hSecond : GauthierE2.eval fuel sig second x₁ x₂ world with
            | none => simp [hFirst, hSecond] at success
            | some next₂ =>
              have hLoop :
                  GauthierE2.loop2Iter fuel sig first second iterations next₁ next₂ world =
                    some values := by
                simpa [hFirst, hSecond] using success
              have hFirst' := evalIH sig first x₁ x₂ world next₁ hFirst
              have hSecond' := evalIH sig second x₁ x₂ world next₂ hSecond
              have hLoop' :=
                loop2IH sig first second iterations next₁ next₂ world values hLoop
              simp [hFirst', hSecond', hLoop']
      · intro sig first second iterations x₁ x₂ world values success
        cases iterations with
        | zero => simpa only [GauthierE2.loop2sndIter] using success
        | succ iterations =>
          rw [GauthierE2.loop2sndIter] at success ⊢
          cases hFirst : GauthierE2.eval fuel sig first x₁ x₂ world with
          | none => simp [hFirst] at success
          | some next₁ =>
            cases hSecond : GauthierE2.eval fuel sig second x₁ x₂ world with
            | none => simp [hFirst, hSecond] at success
            | some next₂ =>
              have hLoop :
                  GauthierE2.loop2sndIter fuel sig first second iterations next₁ next₂ world =
                    some values := by
                simpa [hFirst, hSecond] using success
              have hFirst' := evalIH sig first x₁ x₂ world next₁ hFirst
              have hSecond' := evalIH sig second x₁ x₂ world next₂ hSecond
              have hLoop' :=
                loop2sndIH sig first second iterations next₁ next₂ world values hLoop
              simp [hFirst', hSecond', hLoop']
      · intro sig predicate target seen candidate world values success
        rw [GauthierE2.comprSearch] at success ⊢
        cases hEval : GauthierE2.eval fuel sig predicate candidate [0] world with
        | none => simp [hEval] at success
        | some predicateValues =>
          cases hHead : GauthierE2.head? predicateValues with
          | none => simp [hEval, hHead] at success
          | some predicateHead =>
            have hEval' :=
              evalIH sig predicate candidate [0] world predicateValues hEval
            by_cases hAccept : predicateHead ≤ 0
            · by_cases hEnough : seen ≥ target
              · have hResult : candidate = values := by
                  simpa [hEval, hHead, hAccept, hEnough] using success
                simpa [hEval', hHead, hAccept, hEnough] using congrArg some hResult
              · cases hIncrement : GauthierE2.singletonHeadIncr candidate with
                | none => simp [hEval, hEnough, hIncrement] at success
                | some nextCandidate =>
                  have hSearch :
                      GauthierE2.comprSearch fuel sig predicate target (seen + 1)
                          nextCandidate world = some values := by
                    simpa [hEval, hHead, hAccept, hEnough, hIncrement] using success
                  have hSearch' :=
                    comprIH sig predicate target (seen + 1) nextCandidate world values hSearch
                  simp [hEval', hHead, hAccept, hEnough, hSearch']
            · cases hIncrement : GauthierE2.singletonHeadIncr candidate with
              | none => simp [hEval, hHead, hAccept, hIncrement] at success
              | some nextCandidate =>
                have hSearch :
                    GauthierE2.comprSearch fuel sig predicate target seen
                        nextCandidate world = some values := by
                  simpa [hEval, hHead, hAccept, hIncrement] using success
                have hSearch' :=
                  comprIH sig predicate target seen nextCandidate world values hSearch
                simp [hEval', hHead, hAccept, hSearch']

/-- A successful E2 evaluation persists when one unit of fuel is added. -/
theorem eval_succ_of_some {fuel : Nat} {sig} {program} {x y} {world} {values}
    (success : GauthierE2.eval fuel sig program x y world = some values) :
    GauthierE2.eval (fuel + 1) sig program x y world = some values :=
  (evaluatorFamily_succ fuel).1 sig program x y world values success

/-- A successful E2 evaluation persists under any additive fuel extension. -/
theorem eval_add_of_some {fuel : Nat} (extra : Nat) {sig} {program} {x y} {world} {values}
    (success : GauthierE2.eval fuel sig program x y world = some values) :
    GauthierE2.eval (fuel + extra) sig program x y world = some values := by
  induction extra with
  | zero => simpa using success
  | succ extra inductionHypothesis =>
      simpa [Nat.add_assoc] using eval_succ_of_some inductionHypothesis

/-- Order-form fuel persistence for successful E2 evaluations. -/
theorem eval_mono_of_some {smaller larger : Nat} (fuelOrder : smaller ≤ larger)
    {sig} {program} {x y} {world} {values}
    (success : GauthierE2.eval smaller sig program x y world = some values) :
    GauthierE2.eval larger sig program x y world = some values := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le fuelOrder
  exact eval_add_of_some extra success

/-- A successful one-register loop persists under any fuel increase. -/
theorem loopIter_mono_of_some {smaller larger : Nat} (fuelOrder : smaller ≤ larger)
    {sig} {body} {iterations} {x₁ x₂} {world} {values}
    (success : GauthierE2.loopIter smaller sig body iterations x₁ x₂ world = some values) :
    GauthierE2.loopIter larger sig body iterations x₁ x₂ world = some values := by
  induction fuelOrder with
  | refl => exact success
  | @step larger fuelOrder inductionHypothesis =>
      exact (evaluatorFamily_succ larger).2.1 sig body iterations x₁ x₂ world values
        inductionHypothesis

/-- A successful two-register loop persists under any fuel increase. -/
theorem loop2Iter_mono_of_some {smaller larger : Nat} (fuelOrder : smaller ≤ larger)
    {sig} {first second} {iterations} {x₁ x₂} {world} {values}
    (success :
      GauthierE2.loop2Iter smaller sig first second iterations x₁ x₂ world = some values) :
    GauthierE2.loop2Iter larger sig first second iterations x₁ x₂ world = some values := by
  induction fuelOrder with
  | refl => exact success
  | @step larger fuelOrder inductionHypothesis =>
      exact (evaluatorFamily_succ larger).2.2.1 sig first second iterations x₁ x₂ world
        values inductionHypothesis

/-- Successful E2 results are unique even when witnessed at different fuels. -/
theorem eval_some_unique {firstFuel secondFuel : Nat} {sig} {program} {x y} {world}
    {firstValues secondValues : List Int}
    (firstSuccess :
      GauthierE2.eval firstFuel sig program x y world = some firstValues)
    (secondSuccess :
      GauthierE2.eval secondFuel sig program x y world = some secondValues) :
    firstValues = secondValues := by
  let commonFuel := max firstFuel secondFuel
  have firstAtCommon :
      GauthierE2.eval commonFuel sig program x y world = some firstValues :=
    eval_mono_of_some (Nat.le_max_left _ _) firstSuccess
  have secondAtCommon :
      GauthierE2.eval commonFuel sig program x y world = some secondValues :=
    eval_mono_of_some (Nat.le_max_right _ _) secondSuccess
  rw [firstAtCommon] at secondAtCommon
  exact Option.some.inj secondAtCommon

/-- A successful scalar observation from the E2 memo evaluator persists with more fuel. -/
theorem term_mono_of_some {smaller larger : Nat} (fuelOrder : smaller ≤ larger)
    {sig} {program} {seedValue value}
    (success : GauthierE2.term smaller sig program seedValue = some value) :
    GauthierE2.term larger sig program seedValue = some value := by
  simp [GauthierE2.term, GauthierE2.termWithWorld,
    Option.bind_eq_some_iff] at success ⊢
  obtain ⟨values, hEval, hHead⟩ := success
  exact ⟨values, eval_mono_of_some fuelOrder hEval, hHead⟩

/-- Successful scalar E2 observations are independent of the sufficient fuel witness. -/
theorem term_some_unique {firstFuel secondFuel : Nat} {sig} {program} {seedValue}
    {firstValue secondValue : Int}
    (firstSuccess : GauthierE2.term firstFuel sig program seedValue = some firstValue)
    (secondSuccess : GauthierE2.term secondFuel sig program seedValue = some secondValue) :
    firstValue = secondValue := by
  let commonFuel := max firstFuel secondFuel
  have firstAtCommon := term_mono_of_some (Nat.le_max_left firstFuel secondFuel) firstSuccess
  have secondAtCommon := term_mono_of_some (Nat.le_max_right firstFuel secondFuel) secondSuccess
  rw [firstAtCommon] at secondAtCommon
  exact Option.some.inj secondAtCommon

#print axioms evaluatorFamily_succ
#print axioms eval_mono_of_some
#print axioms loopIter_mono_of_some
#print axioms loop2Iter_mono_of_some
#print axioms term_some_unique

end Mettapedia.GSLT.LanguageDef.GauthierE2Fuel
