import Mettapedia.GSLT.LanguageDef.RegexRequestCompleteness
import Mettapedia.OSLF.MeTTaIL.ContextualBindingExtension

/-!
# Authored regex evaluation correspondence

The finite-depth observations of the declared `LanguageDef` rules are compared
with independently structural regex requests. The interpreter is the actual
ordered-premise contextual engine, with data-only scalar comparisons.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RegexAuthoredComparison

open Mettapedia.Computability.RegularLanguages
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.ContextualStep

private theorem rewriteAt_plain (fuel : Nat) (source : Pattern) :
    rewriteAt (engineBasePremises RegexTheory.scalarRelations) RegexTheory.theory (fuel + 1) source =
      RegexTheory.theory.rewrites.flatMap fun selected =>
        (matchPattern selected.left source).flatMap fun initial =>
          (premisesUsing (engineBasePremises RegexTheory.scalarRelations) RegexTheory.theory
            (rewriteAt (engineBasePremises RegexTheory.scalarRelations) RegexTheory.theory fuel)
            selected.premises initial).map fun final => applyBindings final selected.right := by
  simp only [rewriteAt]
  apply List.flatMap_congr
  intro selected member
  simp only [applyRuleUsing,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic]
  apply List.flatMap_congr
  intro initial _
  apply List.map_congr_left
  intro final _
  exact RegexTheory.applyBindingsForRule_plain selected member final

private theorem theory_rewrites : RegexTheory.theory.rewrites = RegexTheory.rewrites := rfl
private theorem boolean_false : RegexTheory.boolean false = .apply "rx:false" [] := rfl
private theorem boolean_true : RegexTheory.boolean true = .apply "rx:true" [] := rfl

attribute [local simp] List.map_flatMap List.flatMap_map
  theory_rewrites boolean_false boolean_true RegexTheory.rewrites
  RegexTheory.orFF RegexTheory.orFT RegexTheory.orTF RegexTheory.orTT
  RegexTheory.andFF RegexTheory.andFT RegexTheory.andTF RegexTheory.andTT
  RegexTheory.nullableZero RegexTheory.nullableEpsilon RegexTheory.nullableLiteral RegexTheory.nullableAny
  RegexTheory.nullableUnion RegexTheory.nullableConcat RegexTheory.nullableStar
  RegexTheory.derivativeZero RegexTheory.derivativeEpsilon RegexTheory.derivativeLiteralEq
  RegexTheory.derivativeLiteralNe RegexTheory.derivativeAny RegexTheory.derivativeUnion
  RegexTheory.derivativeConcatNullable RegexTheory.derivativeConcatNonnullable RegexTheory.derivativeStar
  RegexTheory.matchNil RegexTheory.matchCons
  RegexTheory.rewriteSchema RegexTheory.capture RegexTheory.constructor
  RegexTheory.nullable RegexTheory.derivative RegexTheory.matchRequest RegexTheory.disjoin RegexTheory.conjoin
  RegexTheory.scalar RegexTheory.encode RegexTheory.word
  matchPattern matchArgs mergeBindings premisesUsing premiseStepUsing applyBindings

private theorem disjoin_rewriteAt (left right : Bool) (fuel : Nat) :
    rewriteAt (engineBasePremises RegexTheory.scalarRelations) RegexTheory.theory (fuel + 1)
      (RegexTheory.disjoin (RegexTheory.boolean left) (RegexTheory.boolean right)) =
        [RegexTheory.boolean (left || right)] := by
  rw [rewriteAt_plain]
  cases left <;> cases right <;> simp

private theorem conjoin_rewriteAt (left right : Bool) (fuel : Nat) :
    rewriteAt (engineBasePremises RegexTheory.scalarRelations) RegexTheory.theory (fuel + 1)
      (RegexTheory.conjoin (RegexTheory.boolean left) (RegexTheory.boolean right)) =
        [RegexTheory.boolean (left && right)] := by
  rw [rewriteAt_plain]
  cases left <;> cases right <;> simp

private abbrev ExactAt (fuel : Nat) : Prop := ∀ request : Request,
    rewriteAt (engineBasePremises RegexTheory.scalarRelations) RegexTheory.theory fuel
      (encodeRequest request) = (boundedResult fuel request).toList.map (encodeResult request)

private theorem nullable_zero_exact (fuel : Nat) :
    rewriteAt (engineBasePremises RegexTheory.scalarRelations) RegexTheory.theory (fuel + 1)
      (RegexTheory.nullable (RegexTheory.encode 0)) = [RegexTheory.boolean false] := by
  rw [rewriteAt_plain]
  simp

private theorem nullable_epsilon_exact (fuel : Nat) :
    rewriteAt (engineBasePremises RegexTheory.scalarRelations) RegexTheory.theory (fuel + 1)
      (RegexTheory.nullable (RegexTheory.encode 1)) = [RegexTheory.boolean true] := by
  rw [rewriteAt_plain]
  simp

private theorem nullable_literal_exact (fuel : Nat) (a : String) :
    rewriteAt (engineBasePremises RegexTheory.scalarRelations) RegexTheory.theory (fuel + 1)
      (RegexTheory.nullable (RegexTheory.encode (literal a))) = [RegexTheory.boolean false] := by
  rw [rewriteAt_plain]
  simp [literal]

private theorem nullable_any_exact (fuel : Nat) :
    rewriteAt (engineBasePremises RegexTheory.scalarRelations) RegexTheory.theory (fuel + 1)
      (RegexTheory.nullable (RegexTheory.encode any)) = [RegexTheory.boolean false] := by
  rw [rewriteAt_plain]
  simp [any]

private theorem nullable_star_exact (fuel : Nat) (p : Regex String) :
    rewriteAt (engineBasePremises RegexTheory.scalarRelations) RegexTheory.theory (fuel + 1)
      (RegexTheory.nullable (RegexTheory.encode p.star)) = [RegexTheory.boolean true] := by
  rw [rewriteAt_plain]
  simp

private theorem nullable_union_exact (fuel : Nat) (ih : ExactAt fuel) (p q : Regex String) :
    rewriteAt (engineBasePremises RegexTheory.scalarRelations) RegexTheory.theory (fuel + 1)
      (RegexTheory.nullable (RegexTheory.encode (p + q))) =
        (boundedResult (fuel + 1) (.nullable (p + q))).toList.map RegexTheory.boolean := by
  have nullIH (r : Regex String) :
      rewriteAt (engineBasePremises RegexTheory.scalarRelations) RegexTheory.theory fuel
        (.apply "rx:nullable" [RegexTheory.encode r]) =
          (boundedResult fuel (.nullable r)).toList.map RegexTheory.boolean := ih (.nullable r)
  have orIH (left right : Bool) :
      rewriteAt (engineBasePremises RegexTheory.scalarRelations) RegexTheory.theory fuel
        (.apply "rx:or" [RegexTheory.boolean left, RegexTheory.boolean right]) =
          (boundedResult fuel (.disjoin left right)).toList.map RegexTheory.boolean := ih (.disjoin left right)
  cases hp : boundedResult fuel (.nullable p) with
  | none =>
    rw [rewriteAt_plain]
    simp [boundedResult, nullIH, hp]
  | some left =>
    cases hq : boundedResult fuel (.nullable q) with
    | none =>
      rw [rewriteAt_plain]
      simp [boundedResult, nullIH, hp, hq]
    | some right =>
      rw [rewriteAt_plain]
      simp [boundedResult, nullIH, orIH, hp, hq]
      exact List.map_eq_flatMap.symm
private theorem nullable_concat_exact (fuel : Nat) (ih : ExactAt fuel) (p q : Regex String) :
    rewriteAt (engineBasePremises RegexTheory.scalarRelations) RegexTheory.theory (fuel + 1)
      (RegexTheory.nullable (RegexTheory.encode (p * q))) =
        (boundedResult (fuel + 1) (.nullable (p * q))).toList.map RegexTheory.boolean := by
  have nullIH (r : Regex String) :
      rewriteAt (engineBasePremises RegexTheory.scalarRelations) RegexTheory.theory fuel
        (.apply "rx:nullable" [RegexTheory.encode r]) =
          (boundedResult fuel (.nullable r)).toList.map RegexTheory.boolean := ih (.nullable r)
  have andIH (left right : Bool) :
      rewriteAt (engineBasePremises RegexTheory.scalarRelations) RegexTheory.theory fuel
        (.apply "rx:and" [RegexTheory.boolean left, RegexTheory.boolean right]) =
          (boundedResult fuel (.conjoin left right)).toList.map RegexTheory.boolean := ih (.conjoin left right)
  cases hp : boundedResult fuel (.nullable p) with
  | none =>
    rw [rewriteAt_plain]
    simp [boundedResult, nullIH, hp]
  | some left =>
    cases hq : boundedResult fuel (.nullable q) with
    | none =>
      rw [rewriteAt_plain]
      simp [boundedResult, nullIH, hp, hq]
    | some right =>
      rw [rewriteAt_plain]
      simp [boundedResult, nullIH, andIH, hp, hq]
      exact List.map_eq_flatMap.symm

private theorem nullable_succ_exact (fuel : Nat) (ih : ExactAt fuel) (p : Regex String) :
    rewriteAt (engineBasePremises RegexTheory.scalarRelations) RegexTheory.theory (fuel + 1)
      (RegexTheory.nullable (RegexTheory.encode p)) =
        (boundedResult (fuel + 1) (.nullable p)).toList.map RegexTheory.boolean := by
  cases p with
  | zero => exact nullable_zero_exact fuel
  | epsilon => exact nullable_epsilon_exact fuel
  | char atom =>
    cases atom with
    | literal a => exact nullable_literal_exact fuel a
    | any => exact nullable_any_exact fuel
  | plus p q => exact nullable_union_exact fuel ih p q
  | comp p q => exact nullable_concat_exact fuel ih p q
  | star p => exact nullable_star_exact fuel p

private theorem derivative_zero_exact (fuel : Nat) (a : String) :
    rewriteAt (engineBasePremises RegexTheory.scalarRelations) RegexTheory.theory (fuel + 1)
      (RegexTheory.derivative (RegexTheory.scalar a) (RegexTheory.encode 0)) = [RegexTheory.encode 0] := by
  rw [rewriteAt_plain]
  simp

private theorem derivative_epsilon_exact (fuel : Nat) (a : String) :
    rewriteAt (engineBasePremises RegexTheory.scalarRelations) RegexTheory.theory (fuel + 1)
      (RegexTheory.derivative (RegexTheory.scalar a) (RegexTheory.encode 1)) = [RegexTheory.encode 0] := by
  rw [rewriteAt_plain]
  simp

private theorem derivative_any_exact (fuel : Nat) (a : String) :
    rewriteAt (engineBasePremises RegexTheory.scalarRelations) RegexTheory.theory (fuel + 1)
      (RegexTheory.derivative (RegexTheory.scalar a) (RegexTheory.encode any)) = [RegexTheory.encode 1] := by
  rw [rewriteAt_plain]
  simp [any]

private theorem derivative_literal_exact (fuel : Nat) (actual expected : String) :
    rewriteAt (engineBasePremises RegexTheory.scalarRelations) RegexTheory.theory (fuel + 1)
      (RegexTheory.derivative (RegexTheory.scalar actual) (RegexTheory.encode (literal expected))) =
        [RegexTheory.encode (if expected = actual then 1 else 0)] := by
  rw [rewriteAt_plain]
  by_cases same : expected = actual <;>
    simp [literal, RegexTheory.scalarRelations, engineBasePremises,
      Mettapedia.OSLF.MeTTaIL.Engine.premiseStepWithEnv,
      Mettapedia.OSLF.MeTTaIL.Engine.relationQueryStep,
      Mettapedia.OSLF.MeTTaIL.Engine.builtinRelationTuples,
      Mettapedia.OSLF.MeTTaIL.Engine.matchRelationArgs,
      Mettapedia.OSLF.MeTTaIL.Engine.matchRelationArgument,
      Bindings.lookup, same]

private theorem derivative_union_exact (fuel : Nat) (ih : ExactAt fuel) (a : String) (p q : Regex String) :
    rewriteAt (engineBasePremises RegexTheory.scalarRelations) RegexTheory.theory (fuel + 1)
      (RegexTheory.derivative (RegexTheory.scalar a) (RegexTheory.encode (p + q))) =
        (boundedResult (fuel + 1) (.derivative a (p + q))).toList.map RegexTheory.encode := by
  have derIH (r : Regex String) :
      rewriteAt (engineBasePremises RegexTheory.scalarRelations) RegexTheory.theory fuel
        (.apply "rx:derivative" [.apply a [], RegexTheory.encode r]) =
          (boundedResult fuel (.derivative a r)).toList.map RegexTheory.encode := ih (.derivative a r)
  cases hp : boundedResult fuel (.derivative a p) with
  | none =>
    rw [rewriteAt_plain]
    simp [boundedResult, derIH, hp]
  | some dp =>
    cases hq : boundedResult fuel (.derivative a q) <;>
      rw [rewriteAt_plain] <;>
      simp [boundedResult, derIH, hp, hq]

private theorem derivative_star_exact (fuel : Nat) (ih : ExactAt fuel) (a : String) (p : Regex String) :
    rewriteAt (engineBasePremises RegexTheory.scalarRelations) RegexTheory.theory (fuel + 1)
      (RegexTheory.derivative (RegexTheory.scalar a) (RegexTheory.encode p.star)) =
        (boundedResult (fuel + 1) (.derivative a p.star)).toList.map RegexTheory.encode := by
  have derIH :
      rewriteAt (engineBasePremises RegexTheory.scalarRelations) RegexTheory.theory fuel
        (.apply "rx:derivative" [.apply a [], RegexTheory.encode p]) =
          (boundedResult fuel (.derivative a p)).toList.map RegexTheory.encode := ih (.derivative a p)
  cases hp : boundedResult fuel (.derivative a p) <;>
    rw [rewriteAt_plain] <;>
    simp [boundedResult, derIH, hp]

private theorem derivative_concat_unavailable (fuel : Nat) (ih : ExactAt fuel) (a : String) (p q : Regex String)
    (hn : boundedResult fuel (.nullable p) = none) :
    rewriteAt (engineBasePremises RegexTheory.scalarRelations) RegexTheory.theory (fuel + 1)
      (RegexTheory.derivative (RegexTheory.scalar a) (RegexTheory.encode (p * q))) =
        (boundedResult (fuel + 1) (.derivative a (p * q))).toList.map RegexTheory.encode := by
  have nullIH :
      rewriteAt (engineBasePremises RegexTheory.scalarRelations) RegexTheory.theory fuel
        (.apply "rx:nullable" [RegexTheory.encode p]) =
          (boundedResult fuel (.nullable p)).toList.map RegexTheory.boolean := ih (.nullable p)
  rw [rewriteAt_plain]
  simp [boundedResult, nullIH, hn]

private theorem derivative_concat_nonnullable (fuel : Nat) (ih : ExactAt fuel) (a : String) (p q : Regex String)
    (hn : boundedResult fuel (.nullable p) = some false) :
    rewriteAt (engineBasePremises RegexTheory.scalarRelations) RegexTheory.theory (fuel + 1)
      (RegexTheory.derivative (RegexTheory.scalar a) (RegexTheory.encode (p * q))) =
        (boundedResult (fuel + 1) (.derivative a (p * q))).toList.map RegexTheory.encode := by
  have nullIH :
      rewriteAt (engineBasePremises RegexTheory.scalarRelations) RegexTheory.theory fuel
        (.apply "rx:nullable" [RegexTheory.encode p]) =
          (boundedResult fuel (.nullable p)).toList.map RegexTheory.boolean := ih (.nullable p)
  have derIH (r : Regex String) :
      rewriteAt (engineBasePremises RegexTheory.scalarRelations) RegexTheory.theory fuel
        (.apply "rx:derivative" [.apply a [], RegexTheory.encode r]) =
          (boundedResult fuel (.derivative a r)).toList.map RegexTheory.encode := ih (.derivative a r)
  cases hp : boundedResult fuel (.derivative a p) <;>
    rw [rewriteAt_plain] <;>
    simp [boundedResult, nullIH, derIH, hn, hp]

private theorem derivative_concat_nullable (fuel : Nat) (ih : ExactAt fuel) (a : String) (p q : Regex String)
    (hn : boundedResult fuel (.nullable p) = some true) :
    rewriteAt (engineBasePremises RegexTheory.scalarRelations) RegexTheory.theory (fuel + 1)
      (RegexTheory.derivative (RegexTheory.scalar a) (RegexTheory.encode (p * q))) =
        (boundedResult (fuel + 1) (.derivative a (p * q))).toList.map RegexTheory.encode := by
  have nullIH :
      rewriteAt (engineBasePremises RegexTheory.scalarRelations) RegexTheory.theory fuel
        (.apply "rx:nullable" [RegexTheory.encode p]) =
          (boundedResult fuel (.nullable p)).toList.map RegexTheory.boolean := ih (.nullable p)
  have derIH (r : Regex String) :
      rewriteAt (engineBasePremises RegexTheory.scalarRelations) RegexTheory.theory fuel
        (.apply "rx:derivative" [.apply a [], RegexTheory.encode r]) =
          (boundedResult fuel (.derivative a r)).toList.map RegexTheory.encode := ih (.derivative a r)
  cases hp : boundedResult fuel (.derivative a p) with
  | none =>
    rw [rewriteAt_plain]
    simp [boundedResult, nullIH, derIH, hn, hp]
  | some dp =>
    cases hq : boundedResult fuel (.derivative a q) <;>
      rw [rewriteAt_plain] <;>
      simp [boundedResult, nullIH, derIH, hn, hp, hq]

private theorem derivative_concat_exact (fuel : Nat) (ih : ExactAt fuel) (a : String) (p q : Regex String) :
    rewriteAt (engineBasePremises RegexTheory.scalarRelations) RegexTheory.theory (fuel + 1)
      (RegexTheory.derivative (RegexTheory.scalar a) (RegexTheory.encode (p * q))) =
        (boundedResult (fuel + 1) (.derivative a (p * q))).toList.map RegexTheory.encode := by
  cases hn : boundedResult fuel (.nullable p) with
  | none => exact derivative_concat_unavailable fuel ih a p q hn
  | some empty =>
    cases empty with
    | false => exact derivative_concat_nonnullable fuel ih a p q hn
    | true => exact derivative_concat_nullable fuel ih a p q hn

private theorem derivative_succ_exact (fuel : Nat) (ih : ExactAt fuel) (a : String) (p : Regex String) :
    rewriteAt (engineBasePremises RegexTheory.scalarRelations) RegexTheory.theory (fuel + 1)
      (RegexTheory.derivative (RegexTheory.scalar a) (RegexTheory.encode p)) =
        (boundedResult (fuel + 1) (.derivative a p)).toList.map RegexTheory.encode := by
  cases p with
  | zero => exact derivative_zero_exact fuel a
  | epsilon => exact derivative_epsilon_exact fuel a
  | char atom =>
    cases atom with
    | literal expected => exact derivative_literal_exact fuel a expected
    | any => exact derivative_any_exact fuel a
  | plus p q => exact derivative_union_exact fuel ih a p q
  | comp p q => exact derivative_concat_exact fuel ih a p q
  | star p => exact derivative_star_exact fuel ih a p

private theorem match_nil_exact (fuel : Nat) (ih : ExactAt fuel) (p : Regex String) :
    rewriteAt (engineBasePremises RegexTheory.scalarRelations) RegexTheory.theory (fuel + 1)
      (RegexTheory.matchRequest (RegexTheory.encode p) (RegexTheory.word [])) =
        (boundedResult (fuel + 1) (.matchWord p [])).toList.map RegexTheory.boolean := by
  have nullIH :
      rewriteAt (engineBasePremises RegexTheory.scalarRelations) RegexTheory.theory fuel
        (.apply "rx:nullable" [RegexTheory.encode p]) =
          (boundedResult fuel (.nullable p)).toList.map RegexTheory.boolean := ih (.nullable p)
  rw [rewriteAt_plain]
  simp [boundedResult, nullIH]
  exact List.map_eq_flatMap.symm

private theorem match_cons_exact (fuel : Nat) (ih : ExactAt fuel) (p : Regex String)
    (a : String) (rest : List String) :
    rewriteAt (engineBasePremises RegexTheory.scalarRelations) RegexTheory.theory (fuel + 1)
      (RegexTheory.matchRequest (RegexTheory.encode p) (RegexTheory.word (a :: rest))) =
        (boundedResult (fuel + 1) (.matchWord p (a :: rest))).toList.map RegexTheory.boolean := by
  have derIH :
      rewriteAt (engineBasePremises RegexTheory.scalarRelations) RegexTheory.theory fuel
        (.apply "rx:derivative" [.apply a [], RegexTheory.encode p]) =
          (boundedResult fuel (.derivative a p)).toList.map RegexTheory.encode := ih (.derivative a p)
  have matchIH (next : Regex String) :
      rewriteAt (engineBasePremises RegexTheory.scalarRelations) RegexTheory.theory fuel
        (.apply "rx:match" [RegexTheory.encode next, RegexTheory.word rest]) =
          (boundedResult fuel (.matchWord next rest)).toList.map RegexTheory.boolean := ih (.matchWord next rest)
  cases hn : boundedResult fuel (.derivative a p) with
  | none =>
    rw [rewriteAt_plain]
    simp [boundedResult, derIH, hn]
  | some next =>
    rw [rewriteAt_plain]
    simp [boundedResult, derIH, matchIH, hn]
    exact List.map_eq_flatMap.symm

/-- The actual declared-rule interpreter has exactly the finite-depth
structural observations, including the empty result at insufficient depth. -/
theorem rewriteAt_exact (fuel : Nat) (request : Request) :
    rewriteAt (engineBasePremises RegexTheory.scalarRelations) RegexTheory.theory fuel
      (encodeRequest request) = (boundedResult fuel request).toList.map (encodeResult request) := by
  induction fuel generalizing request with
  | zero => rfl
  | succ fuel ih =>
    cases request with
    | disjoin left right => exact disjoin_rewriteAt left right fuel
    | conjoin left right => exact conjoin_rewriteAt left right fuel
    | nullable p => exact nullable_succ_exact fuel ih p
    | derivative a p => exact derivative_succ_exact fuel ih a p
    | matchWord p input =>
      cases input with
      | nil => exact match_nil_exact fuel ih p
      | cons a rest => exact match_cons_exact fuel ih p a rest

/-- The codec preserves the distinction between all typed results of a request. -/
theorem encodeResult_injective (request : Request) : Function.Injective (encodeResult request) := by
  cases request with
  | derivative a p => exact RegexTheory.encode_injective
  | disjoin left right => exact RegexTheory.boolean_injective
  | conjoin left right => exact RegexTheory.boolean_injective
  | nullable p => exact RegexTheory.boolean_injective
  | matchWord p input => exact RegexTheory.boolean_injective

/-- Forward execution and reflection for every admitted request and every raw
output. Reflection does not assume the output has already been decoded. -/
theorem step_iff_rootMeaning (request : Request) (output : Pattern) :
    RegexTheory.Step (encodeRequest request) output ↔ RootMeaning request output := by
  change Step (engineBasePremises RegexTheory.scalarRelations) RegexTheory.theory
    (encodeRequest request) output ↔ RootMeaning request output
  rw [← exists_mem_rewriteAt_iff_step]
  constructor
  · rintro ⟨fuel, member⟩
    rw [rewriteAt_exact] at member
    obtain ⟨result, success, outputEq⟩ := List.mem_map.mp member
    exact ⟨result, outputEq.symm,
      (evidence_iff_boundedResult request result).mpr ⟨fuel, Option.mem_toList.mp success⟩⟩
  · rintro ⟨result, outputEq, event⟩
    obtain ⟨fuel, success⟩ := (evidence_iff_boundedResult request result).mp event
    refine ⟨fuel, ?_⟩
    rw [rewriteAt_exact, success]
    simpa only [Option.toList_some, List.map_singleton, List.mem_singleton] using outputEq

/-- The authored rewrite relation retains exactly the structural firing results. -/
theorem step_iff_evidence (request : Request) (result : Result request) :
    RegexTheory.Step (encodeRequest request) (encodeResult request result) ↔
      Nonempty (Evidence request result) := by
  rw [step_iff_rootMeaning]
  constructor
  · rintro ⟨other, same, event⟩
    have identical := encodeResult_injective request same
    cases identical
    exact event
  · intro event
    exact ⟨result, rfl, event⟩

/-- Every well-formed request has an actual authored step to its unique result. -/
theorem step_referenceResult (request : Request) :
    RegexTheory.Step (encodeRequest request) (encodeResult request (referenceResult request)) :=
  (step_iff_evidence request _).mpr ⟨completeEvidence request⟩

/-- A successful raw step cannot invent a terminal value or change the result. -/
theorem step_output_eq {request : Request} {output : Pattern}
    (event : RegexTheory.Step (encodeRequest request) output) :
    output = encodeResult request (referenceResult request) :=
  (rootMeaning_iff_reference request output).mp ((step_iff_rootMeaning request output).mp event)

theorem step_result_unique {request : Request} {first second : Pattern}
    (left : RegexTheory.Step (encodeRequest request) first)
    (right : RegexTheory.Step (encodeRequest request) second) : first = second :=
  (step_output_eq left).trans (step_output_eq right).symm

/-- The actual list interpreter also preserves multiplicity: one admitted
request has at most one returned result at every finite derivation depth. -/
theorem rewriteAt_length_le_one (fuel : Nat) (request : Request) :
    (rewriteAt (engineBasePremises RegexTheory.scalarRelations) RegexTheory.theory fuel
      (encodeRequest request)).length ≤ 1 := by
  rw [rewriteAt_exact, List.length_map]
  cases boundedResult fuel request <;> simp

/-- Whole-word evaluation in the authored theory reflects acceptance and rejection. -/
theorem match_steps_iff (p : Regex String) (input : List String) (result : Bool) :
    RegexTheory.Step (RegexTheory.matchRequest (RegexTheory.encode p) (RegexTheory.word input))
      (RegexTheory.boolean result) ↔ fullMatch p input = result :=
  (step_iff_evidence (.matchWord p input) result).trans (RegexDerivatives.Match.correct p input result)

theorem match_accepts_iff (p : Regex String) (input : List String) :
    RegexTheory.Step (RegexTheory.matchRequest (RegexTheory.encode p) (RegexTheory.word input))
      (RegexTheory.boolean true) ↔ input ∈ language p := by
  rw [match_steps_iff, fullMatch_correct]

theorem match_rejects_iff (p : Regex String) (input : List String) :
    RegexTheory.Step (RegexTheory.matchRequest (RegexTheory.encode p) (RegexTheory.word input))
      (RegexTheory.boolean false) ↔ input ∉ language p := by
  rw [match_steps_iff, Bool.eq_false_iff]
  exact not_congr (fullMatch_correct p input)

theorem nullable_steps_iff (p : Regex String) (result : Bool) :
    RegexTheory.Step (RegexTheory.nullable (RegexTheory.encode p)) (RegexTheory.boolean result) ↔
      p.matchEpsilon = result :=
  (step_iff_evidence (.nullable p) result).trans (RegexDerivatives.Nullable.correct p result)

theorem derivative_steps_iff (a : String) (p result : Regex String) :
    RegexTheory.Step (RegexTheory.derivative (RegexTheory.scalar a) (RegexTheory.encode p))
      (RegexTheory.encode result) ↔ derivative a p = result :=
  (step_iff_evidence (.derivative a p) result).trans (RegexDerivatives.Derivative.correct a p result)

end Mettapedia.GSLT.LanguageDef.RegexAuthoredComparison
