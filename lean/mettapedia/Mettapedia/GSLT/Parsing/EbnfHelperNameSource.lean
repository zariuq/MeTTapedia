import Mettapedia.GSLT.Parsing.EbnfRepetitionSource

/-!
# EBNF helper-name allocation laws and selected source steps

Helper names use a width-separated prefix and a least-significant-bit-first
counter. The counter's arithmetic meaning is independent of its implementation.
The selected operational rules below are extracted from the live authored
lowering and executed by the existing Pattern matcher and substitution.

This proves the name allocator's collision laws for a supplied name-width
bound, and checks its counter/allocation source clauses. It does not yet prove
that the complete grammar/lexical width scan supplies that bound, nor that the
whole lowering or C evaluator realizes these laws on every input.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.EbnfHelperNameSource

open Algorithms.MeTTa.Simple.Parser (SExpr)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open EbnfRepetitionSource (app loweringSyntax equation? closeEquation? translatedEquation?)
open SourceSExprPatternCodec (encode encodeList)
open SourceSExprPatternInstantiation (pattern patternList instantiate? instantiateList?)

/-- Binary words retain their representation, including leading zeroes. -/
def nextBits : List Bool → List Bool
  | [] => [true]
  | false :: tail => true :: tail
  | true :: tail => false :: nextBits tail

/-- Independent positional interpretation; the first bit has weight one. -/
def value : List Bool → Nat
  | [] => 0
  | bit :: tail => (if bit then 1 else 0) + 2 * value tail

theorem nextBits_value (bits : List Bool) : value (nextBits bits) = value bits + 1 := by
  induction bits with
  | nil => rfl
  | cons bit tail ih =>
      cases bit <;> simp [nextBits, value, ih] <;> omega

def bitsAfter (initial : List Bool) : Nat → List Bool
  | 0 => initial
  | count + 1 => nextBits (bitsAfter initial count)

theorem bitsAfter_value (initial : List Bool) (count : Nat) :
    value (bitsAfter initial count) = value initial + count := by
  induction count with
  | zero => simp [bitsAfter]
  | succ count ih => simp [bitsAfter, nextBits_value, ih, Nat.add_assoc]

theorem bitsAfter_injective (initial : List Bool) :
    Function.Injective (bitsAfter initial) := by
  intro first second equal
  have sameValue := congrArg value equal
  simpa only [bitsAfter_value, Nat.add_left_cancel_iff] using sameValue

def digit (bit : Bool) : Nat := if bit then 49 else 48

@[simp] private theorem repr_prefix : Nat.repr 35 = "35" := rfl
@[simp] private theorem repr_zero_bit : Nat.repr 48 = "48" := rfl
@[simp] private theorem repr_one_bit : Nat.repr 49 = "49" := rfl

theorem digit_injective : Function.Injective digit := by
  intro first second equal
  cases first <;> cases second <;> simp_all [digit]

def helperName (width : Nat) (initial : List Bool) (occurrence : Nat) : List Nat :=
  List.replicate (width + 1) 35 ++ (bitsAfter initial occurrence).map digit

/-- Occurrences, not source spans or expression equality, separate helpers. -/
theorem helperName_injective (width : Nat) (initial : List Bool) :
    Function.Injective (helperName width initial) := by
  intro first second equal
  apply bitsAfter_injective initial
  apply (List.map_injective_iff.mpr digit_injective)
  exact List.append_cancel_left equal

/-- All names within the supplied bound remain outside the helper namespace,
including unresolved references and names containing the prefix character. -/
theorem helperName_not_existing (width : Nat) (initial : List Bool)
    (occurrence : Nat) (existing : List Nat) (bounded : existing.length ≤ width) :
    helperName width initial occurrence ≠ existing := by
  intro equal
  have lengths := congrArg List.length equal
  simp only [helperName, List.length_append, List.length_replicate,
    List.length_map] at lengths
  omega

theorem helpers_distinct (width : Nat) (initial : List Bool)
    (first second : Nat) (different : first ≠ second) :
    helperName width initial first ≠ helperName width initial second :=
  fun equal => different (helperName_injective width initial equal)

/-- A too-short fixed prefix really can capture a user-supplied name. -/
theorem fixed_prefix_can_collide :
    ([35, 35] ++ [48] : List Nat) = [35, 35, 48] := rfl

/-- Equal numeric values need not be equal binary words. The allocator does
not rely on the false converse of positional interpretation. -/
theorem positional_value_does_not_reflect_words :
    value [false] = value [false, false] ∧ ([false] : List Bool) ≠ [false, false] := by
  decide

theorem dropping_carry_changes_the_counter :
    nextBits [true, true] ≠ [false, true] := by decide

def text : List Nat → SExpr
  | [] => app "bnf-v1:text-nil" []
  | cp :: tail => app "bnf-v1:text-cons" [.atom (toString cp), text tail]

def bitsText (bits : List Bool) : SExpr := text (bits.map digit)

theorem bitsText_injective : Function.Injective bitsText := by
  intro first
  induction first with
  | nil =>
      intro second equal
      cases second <;> simp_all [bitsText, text, app]
  | cons bit tail ih =>
      intro second equal
      cases second with
      | nil => simp [bitsText, text, app] at equal
      | cons other rest =>
          cases bit <;> cases other <;> simp [bitsText, text, digit, app] at equal ⊢
          all_goals apply ih; exact equal

theorem text_length_eq (first second : List Nat) (equal : text first = text second) :
    first.length = second.length := by
  induction first generalizing second with
  | nil => cases second <;> simp_all [text, app]
  | cons cp tail ih =>
      cases second with
      | nil => simp [text, app] at equal
      | cons other rest =>
          have fields : toString cp = toString other ∧ text tail = text rest := by
            simpa [text, app] using equal
          simpa using congrArg Nat.succ (ih rest fields.2)

theorem text_append_cancel (fixed first second : List Nat)
    (equal : text (fixed ++ first) = text (fixed ++ second)) : text first = text second := by
  induction fixed with
  | nil => exact equal
  | cons cp tail ih =>
      apply ih
      simpa [text, app] using equal

def helperText (width : Nat) (initial : List Bool) (occurrence : Nat) : SExpr :=
  text (helperName width initial occurrence)

/-- The collision law holds for the actual structured MeTTa text shape,
not just for an unencoded list of abstract names. -/
theorem helperText_injective (width : Nat) (initial : List Bool) :
    Function.Injective (helperText width initial) := by
  intro first second equal
  apply bitsAfter_injective initial
  apply bitsText_injective
  exact text_append_cancel _ _ _ equal

theorem helperText_not_existing (width : Nat) (initial : List Bool)
    (occurrence : Nat) (existing : List Nat) (bounded : existing.length ≤ width) :
    helperText width initial occurrence ≠ text existing := by
  intro equal
  have lengths := text_length_eq _ _ equal
  simp only [helperName, List.length_append, List.length_replicate,
    List.length_map] at lengths
  omega

def nextCall (bits : List Bool) : SExpr := app "ebnf-v1:next-bits" [bitsText bits]

def counterRules? : Option (List RewriteRule) :=
  [7, 8, 9].mapM (translatedEquation? loweringSyntax)

theorem counter_present : counterRules?.isSome = true := rfl

def counter : LanguageDef :=
  { name := "EbnfSourceHelperCounter", types := [], terms := [], equations := [],
    rewrites := counterRules?.get counter_present }

private def observedRules : List RewriteRule := [
  { name := "counter-empty", typeContext := [], premises := [],
    left := pattern (nextCall []), right := pattern (bitsText [true]) },
  { name := "counter-zero", typeContext := [], premises := [],
    left := pattern (app "ebnf-v1:next-bits"
      [app "bnf-v1:text-cons" [.atom "48", .atom "?tail"]]),
    right := pattern (app "bnf-v1:text-cons" [.atom "49", .atom "?tail"]) },
  { name := "counter-one", typeContext := [], premises := [],
    left := pattern (app "ebnf-v1:next-bits"
      [app "bnf-v1:text-cons" [.atom "49", .atom "?tail"]]),
    right := pattern (app "bnf-v1:text-cons"
      [.atom "48", app "ebnf-v1:next-bits" [.atom "?tail"]]) }]

private theorem counter_rules_exact : counter.rewrites = observedRules := rfl

theorem counter_empty_source :
    rewriteStep counter (encode (nextCall [])) = [encode (bitsText [true])] := by
  simp [rewriteStep, counter_rules_exact, observedRules, applyRule, nextCall,
    bitsText, text, digit, app, pattern, patternList, SourceIntegerProvider.sourceVariableToken,
    encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM, applyBindings]

theorem counter_zero_source (tail : List Bool) :
    rewriteStep counter (encode (nextCall (false :: tail))) =
      [encode (bitsText (true :: tail))] := by
  simp [rewriteStep, counter_rules_exact, observedRules, applyRule, nextCall,
    bitsText, text, digit, app, pattern, patternList, SourceIntegerProvider.sourceVariableToken,
    encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM, applyBindings]

/-- The actual carry clause returns an explicit recursive call in the tail;
this theorem does not silently normalize that call by a second evaluator. -/
theorem counter_one_source (tail : List Bool) :
    rewriteStep counter (encode (nextCall (true :: tail))) =
      [encode (app "bnf-v1:text-cons" [.atom "48", nextCall tail])] := by
  simp [rewriteStep, counter_rules_exact, observedRules, applyRule, nextCall,
    bitsText, text, digit, app, pattern, patternList, SourceIntegerProvider.sourceVariableToken,
    encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM, applyBindings]

def unary : Nat → SExpr
  | 0 => app "ebnf-v1:z" []
  | count + 1 => app "ebnf-v1:s" [unary count]

private theorem prefix_zero_equation : equation? loweringSyntax 5 =
    some (app "ebnf-v1:prefix" [unary 0], text [35]) := rfl

private theorem prefix_successor_equation : equation? loweringSyntax 6 =
    some (app "ebnf-v1:prefix" [app "ebnf-v1:s" [.atom "?n"]],
      app "bnf-v1:text-cons" [.atom "35", app "ebnf-v1:prefix" [.atom "?n"]]) := rfl

theorem prefix_zero_source : closeEquation? loweringSyntax 5 [] =
    some (app "ebnf-v1:prefix" [unary 0], text [35]) := by
  simp [closeEquation?, prefix_zero_equation, unary, text, app, instantiate?, instantiateList?,
    SourceIntegerProvider.sourceVariableToken]

theorem prefix_successor_source (width : Nat) :
    closeEquation? loweringSyntax 6 [("?n", unary width)] =
      some (app "ebnf-v1:prefix" [unary (width + 1)],
        app "bnf-v1:text-cons" [.atom "35", app "ebnf-v1:prefix" [unary width]]) := by
  simp [closeEquation?, prefix_successor_equation, unary, app, instantiate?, instantiateList?,
    SourceIntegerProvider.sourceVariableToken]

def state (prefixWord bits helpers origins owner : SExpr) : SExpr :=
  app "ebnf-v1:state" [prefixWord, bits, helpers, origins, owner]

def installCall (name kind span expression allocationState : SExpr) : SExpr :=
  app "ebnf-v1:install-helper" [name, kind, span, expression, allocationState]

private theorem allocate_group_equation : equation? loweringSyntax 61 =
    some (app "ebnf-v1:allocate-group"
      [app "ebnf-v1:result" [.atom "?expr", state (.atom "?prefix") (.atom "?bits")
        (.atom "?helpers") (.atom "?origins") (.atom "?origin")], .atom "?span"],
      installCall (app "bnf-v1:text-append" [.atom "?prefix", .atom "?bits"])
        (.atom "group") (.atom "?span") (.atom "?expr")
        (state (.atom "?prefix") (app "ebnf-v1:next-bits" [.atom "?bits"])
          (.atom "?helpers") (.atom "?origins") (.atom "?origin"))) := rfl

/-- The authored allocator installs the old counter name and advances the
counter in its state. Opaque source ownership and span payloads survive. -/
theorem allocate_group_source (prefixWord bits helpers origins owner expression span : SExpr) :
    closeEquation? loweringSyntax 61
      [("?prefix", prefixWord), ("?bits", bits), ("?helpers", helpers),
        ("?origins", origins), ("?origin", owner), ("?expr", expression), ("?span", span)] =
      some (app "ebnf-v1:allocate-group"
        [app "ebnf-v1:result" [expression, state prefixWord bits helpers origins owner], span],
        installCall (app "bnf-v1:text-append" [prefixWord, bits]) (.atom "group") span expression
          (state prefixWord (app "ebnf-v1:next-bits" [bits]) helpers origins owner)) := by
  simp [closeEquation?, allocate_group_equation, state, installCall, app,
    instantiate?, instantiateList?, SourceIntegerProvider.sourceVariableToken]

def installed (name kind span expression prefixWord bits helpers origins owner : SExpr) : SExpr :=
  app "ebnf-v1:result" [app "bnf-v1:reference" [name, span],
    state prefixWord bits
      (app "bnf-v1:entries-cons" [app "bnf-v1:rule" [name, expression, span], helpers])
      (app "ebnf-v1:origins-cons"
        [app "ebnf-v1:helper-origin" [name, kind, owner, span], origins]) owner]

private theorem install_equation : equation? loweringSyntax 69 =
    some (installCall (.atom "?name") (.atom "?kind") (.atom "?span") (.atom "?expr")
      (state (.atom "?prefix") (.atom "?bits") (.atom "?helpers") (.atom "?origins") (.atom "?origin")),
      installed (.atom "?name") (.atom "?kind") (.atom "?span") (.atom "?expr")
        (.atom "?prefix") (.atom "?bits") (.atom "?helpers") (.atom "?origins") (.atom "?origin")) := rfl

theorem install_source (name kind span expression prefixWord bits helpers origins owner : SExpr) :
    closeEquation? loweringSyntax 69
      [("?name", name), ("?kind", kind), ("?span", span), ("?expr", expression),
        ("?prefix", prefixWord), ("?bits", bits), ("?helpers", helpers),
        ("?origins", origins), ("?origin", owner)] =
      some (installCall name kind span expression (state prefixWord bits helpers origins owner),
        installed name kind span expression prefixWord bits helpers origins owner) := by
  simp [closeEquation?, install_equation, installed, state, installCall, app,
    instantiate?, instantiateList?, SourceIntegerProvider.sourceVariableToken]

#print axioms nextBits_value
#print axioms helperName_injective
#print axioms helperName_not_existing
#print axioms helperText_injective
#print axioms helperText_not_existing
#print axioms counter_empty_source
#print axioms counter_zero_source
#print axioms counter_one_source
#print axioms allocate_group_source
#print axioms install_source

end Mettapedia.GSLT.Parsing.EbnfHelperNameSource
