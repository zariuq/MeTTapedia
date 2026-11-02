import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralConversionSearchProjection

/-!
# Exact comparison checking with certified outer recipes

When the prefix and reversed suffix already have checked endpoints, validating
their composite with a middle recipe is exactly validating the middle recipe.
The existing comparison producer retains the complete returned certificate.
Its Boolean validation can therefore be rewritten without decoding the two
already certified outer recipes again. Neither executable function is changed.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation

namespace StructuralConversionCode.Code

variable {Head : Type} {RootCode : Nat → Type} [DecidableEq Head]
  (headEq : Head → Head → Prop) [DecidableRel headEq]
  (decodeRoot : {n : Nat} → RootCode n → Option (Tm Head n × Tm Head n))

theorem check_trans_sandwich {n : Nat} {leadingCode middleCode trailingCode : Code Head RootCode n}
    {left first second right : Tm Head n}
    (prefixChecked : leadingCode.check headEq decodeRoot left first = true)
    (suffixChecked : trailingCode.check headEq decodeRoot right second = true) :
    (Code.trans leadingCode (.trans middleCode (.symm trailingCode))).check headEq decodeRoot left right =
      middleCode.check headEq decodeRoot first second := by
  have prefixDecoded := of_decide_eq_true prefixChecked
  have suffixDecoded := of_decide_eq_true suffixChecked
  change decide (joinEndpoints (leadingCode.decode headEq decodeRoot)
      (joinEndpoints (middleCode.decode headEq decodeRoot)
        (reverseEndpoints (trailingCode.decode headEq decodeRoot))) = some (left,right)) =
    decide (middleCode.decode headEq decodeRoot = some (first,second))
  rw [prefixDecoded,suffixDecoded]
  apply decide_eq_decide.mpr
  cases middleDecoded : middleCode.decode headEq decodeRoot with
  | none => simp only [joinEndpoints, reduceCtorEq]
  | some endpoints =>
      rcases endpoints with ⟨a,b⟩
      by_cases firstSame : a = first <;> by_cases secondSame : b = second <;>
        simp [reverseEndpoints, joinEndpoints, firstSame, secondSame, eq_comm]
      all_goals first
        | exact fun same => secondSame same.symm
        | exact fun _ same => secondSame same.symm

end StructuralConversionCode.Code

namespace StructuralConversionSearch

open StructuralConversionCode
variable {Head : Type} [DecidableEq Head] {root : RootComputation Head}
  (headEq : Head → Head → Prop) [DecidableRel headEq]
  (decoder : RootDecoder root)
  (findRoot : {n : Nat} → Tm Head n → Option (decoder.Code n))

theorem compare_eq_middle_check (fuel : Nat) {n : Nat} (left right : Tm Head n) :
    compare decoder findRoot (headEq := headEq) fuel left right = (do
      let first := produce decoder.decode findRoot fuel left
      let second := produce decoder.decode findRoot fuel right
      let middle ← compareShape first.term second.term
      let recipe := Code.trans first.recipe (.trans middle (.symm second.recipe))
      if middle.check headEq decoder.decode first.term second.term then some recipe else none) := by
  dsimp only [compare]
  cases matched : compareShape (RootCode := decoder.Code)
      (produce decoder.decode findRoot fuel left).term (produce decoder.decode findRoot fuel right).term with
  | none => simp only [Option.bind_eq_bind, Option.bind_none]
  | some middle =>
      simp only [Option.bind_eq_bind, Option.bind_some]
      rw [Code.check_trans_sandwich headEq decoder.decode
        (produce_checked headEq decoder.decode findRoot fuel left)
        (produce_checked headEq decoder.decode findRoot fuel right)]

/-- Comparison observes projected normal terms while preserving the complete
returned recipe, including both original produced outer recipes. -/
theorem compare_eq_projected_middle_check (fuel : Nat) {n : Nat} (left right : Tm Head n) :
    compare decoder findRoot (headEq := headEq) fuel left right = (do
      let first := termProjection decoder.decode findRoot fuel left
      let second := termProjection decoder.decode findRoot fuel right
      let middle ← compareShape first second
      let recipe := Code.trans (produce decoder.decode findRoot fuel left).recipe
        (.trans middle (.symm (produce decoder.decode findRoot fuel right).recipe))
      if middle.check headEq decoder.decode first second then some recipe else none) := by
  simpa only [produce_term] using compare_eq_middle_check headEq decoder findRoot fuel left right

end StructuralConversionSearch

#print axioms StructuralConversionCode.Code.check_trans_sandwich
#print axioms StructuralConversionSearch.compare_eq_middle_check
#print axioms StructuralConversionSearch.compare_eq_projected_middle_check

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
