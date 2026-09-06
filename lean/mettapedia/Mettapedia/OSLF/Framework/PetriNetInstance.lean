import Mettapedia.OSLF.MeTTaIL.Syntax
import Mettapedia.OSLF.MeTTaIL.Match
import Mettapedia.OSLF.MeTTaIL.Engine
import Mettapedia.OSLF.MeTTaIL.ContextualStep
import Mettapedia.OSLF.Framework.TypeSynthesis
import Mettapedia.OSLF.Formula
import Mettapedia.GSLT.LanguageDef.TwoNTTCoherence

/-!
# Petri Net OSLF Instance

Third example instantiation of the OSLF pipeline. A binder-free language
validating that multiset (bag) matching works correctly without any
abstraction or substitution machinery.

## Petri Net

A simple Petri net with four places (A, B, C, D) and two transitions:

```
        T1: {A, B} → {C, D}       T2: {C} → {A}
```

Markings are multisets of place-tokens. A transition fires by consuming
tokens from input places and producing tokens at output places. The
`rest` variable captures remaining tokens unchanged.

## Pipeline

```
validatedPetriNet : ValidatedLanguageDef
    ↓ presentation-derived equations and E;R;E
langGSLT petriNet : GSLT
    ↓ quotient predicates and native types
petriOSLF : OSLFTypeSystem  (with proven Galois connection)
```

## Why This Language Matters

- **No binders**: validates bag matching without substitution/alpha issues
- **Multiple transitions**: tests non-deterministic choice
- **Multiplicity-sensitive**: {A, A, B} can fire T1 once, leaving {A, C, D}
- **Reachability reasoning**: demonstrates ◇/□ for marking reachability

## References

- Petri, "Kommunikation mit Automaten" (1962)
- Meredith & Stay, "Operational Semantics in Logical Form"
-/

namespace Mettapedia.OSLF.Framework.PetriNetInstance

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.OSLF.Formula
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.GSLT.LanguageDef.TwoNTTCoherence
open Mettapedia.GSLT.LanguageDef.WellSorted

/-! ## Language Definition -/

/-- Place-token constructors are separate from the bag-valued marking
carrier.  This prevents the collection representation from being an implicit
host convention: the presentation itself says which values are permutable
with multiplicity retained. -/
def placeARule : GrammarRule :=
  { label := "A", category := "Place", params := [],
    syntaxPattern := [.terminal "A"] }

def placeBRule : GrammarRule :=
  { label := "B", category := "Place", params := [],
    syntaxPattern := [.terminal "B"] }

def placeCRule : GrammarRule :=
  { label := "C", category := "Place", params := [],
    syntaxPattern := [.terminal "C"] }

def placeDRule : GrammarRule :=
  { label := "D", category := "Place", params := [],
    syntaxPattern := [.terminal "D"] }

/-- A marking is a bag of places.  The bag declaration derives permutation
invariance while retaining multiplicity; it does not add idempotence. -/
def markingRule : GrammarRule :=
  { label := "MarkingBag", category := "Marking",
    params := [.simple "tokens" (.collection .hashBag (.base "Place"))],
    syntaxPattern :=
      [.terminal "{", .nonTerminal "tokens", .separator ",", .terminal "}"] }

def transitionT1 : RewriteRule :=
  { name := "T1",
    typeContext := [],
    premises := [],
    left := .collection .hashBag [.apply "A" [], .apply "B" []] (some "rest"),
    right := .collection .hashBag [.apply "C" [], .apply "D" []] (some "rest") }

def transitionT2 : RewriteRule :=
  { name := "T2",
    typeContext := [],
    premises := [],
    left := .collection .hashBag [.apply "C" []] (some "rest"),
    right := .collection .hashBag [.apply "A" []] (some "rest") }

/-- A simple Petri net with four places and two transitions.

    - **Types**: `["Place", "Marking"]`
    - **Places**: `A`, `B`, `C`, `D` (nullary constructors)
    - **Transitions**:
      - `T1`: `{A | B | rest} ~> {C | D | rest}` (consume A+B, produce C+D)
      - `T2`: `{C | rest} ~> {A | rest}` (consume C, produce A)

    Markings are represented as hash-bags of place tokens. -/
def petriNet : LanguageDef := {
  name := "PetriNet",
  types := ["Place", "Marking"],
  terms := [
    placeARule,
    placeBRule,
    placeCRule,
    placeDRule,
    markingRule
  ],
  equations := [],
  rewrites := [
    transitionT1,
    transitionT2
  ]
}

private theorem petriNet_rewrites_validate :
    ∀ rewrite ∈ petriNet.rewrites,
      LanguageDef.validateRewrite petriNet rewrite = [] := by
  intro rewrite rewriteMember
  simp [petriNet] at rewriteMember
  rcases rewriteMember with rfl | rfl
  all_goals
    simp [LanguageDef.validateRewrite, petriNet,
      transitionT1, transitionT2,
      placeARule, placeBRule, placeCRule, placeDRule, markingRule,
      LanguageDef.validatePatternConstructors,
      LanguageDef.validateRulePatterns, LanguageDef.patternFvarNames,
      LanguageDef.patternBinderNames,
      Pattern.constructorRefs, Pattern.constructorRefsList,
      Pattern.freeFvarNames,
      Pattern.isWellScoped, Pattern.isWellScopedAt,
      Pattern.isWellScopedListAt, LanguageDef.typeNames]

/-- The equation-bearing Petri presentation passes the ordinary structural
admission gate before it is interpreted as a GSLT. -/
theorem petriNet_validate : petriNet.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_concreteSyntaxAndRewrites
  · rfl
  · decide
  · decide
  · decide
  · intro term hterm
    simp [petriNet] at hterm
    rcases hterm with rfl | rfl | rfl | rfl | rfl <;>
      simp [placeARule, placeBRule, placeCRule, placeDRule, markingRule,
        petriNet, LanguageDef.typeNames, TypeDecl.plain]
  · intro term hterm param hparam typeName htypeName
    simp [petriNet] at hterm
    rcases hterm with rfl | rfl | rfl | rfl | rfl <;>
      simp_all [placeARule, placeBRule, placeCRule, placeDRule, markingRule,
        petriNet, LanguageDef.typeNames, TypeDecl.plain, TermParam.typeExpr,
        TypeExpr.baseNames]
  · decide
  · exact petriNet_rewrites_validate

/-- The admitted source object used by later GSLT/NTT transformations. -/
def validatedPetriNet :
    Mettapedia.GSLT.LanguageDef.ValidatedLanguageDef :=
  ⟨petriNet, petriNet_validate⟩

theorem petriNet_usesBags : petriNet.usesCollection .hashBag = true := by
  decide

theorem petriNet_not_equationFree : petriNet.isEquationFree = false := by
  decide

/-- All one-step transition firings of `petriNet`.  Both transition rules
have no contextual premises, so contextual depth one is exact. -/
def petriNetReducts (marking : Pattern) : List Pattern :=
  rewriteAt (engineBasePremises RelationEnv.empty) petriNet 1 marking

/-! ## OSLF Pipeline Instantiation -/

/-- The OSLF type system for the Petri net.
    Galois connection ◇ ⊣ □ is proven automatically. -/
def petriOSLF := langOSLF petriNet "Marking"

/-- The Galois connection for the Petri net. -/
theorem petriGalois :
    GaloisConnection (langDiamond petriNet) (langBox petriNet) :=
  langGalois petriNet

/-! ## Helper Constructors -/

/-- Token at place A -/
def tokA : Pattern := .apply "A" []

/-- Token at place B -/
def tokB : Pattern := .apply "B" []

/-- Token at place C -/
def tokC : Pattern := .apply "C" []

/-- Token at place D -/
def tokD : Pattern := .apply "D" []

/-- Marking: bag of tokens -/
def marking (tokens : List Pattern) : Pattern :=
  .collection .hashBag tokens none

/-- Simple display for Petri net markings -/
private def markingToString : Pattern → String
  | .apply "A" [] => "A"
  | .apply "B" [] => "B"
  | .apply "C" [] => "C"
  | .apply "D" [] => "D"
  | .collection .hashBag elems _ =>
    "{" ++ String.intercalate ", " (elems.map markingToString) ++ "}"
  | p => repr p |>.pretty

private instance : ToString Pattern := ⟨markingToString⟩

/-! ## Equation-aware generated native type -/

theorem petriNet_markingCarrier :
    CollectionCarrierRule petriNet markingRule .hashBag where
  authored := by simp [petriNet]
  selfSorted := ⟨"tokens", .base "Place", rfl⟩

theorem petriNet_AB_sorted :
    SortedAt petriNet (marking [tokA, tokB]) "Marking" := by
  refine ⟨FreeTypeContext.empty, [], ?_⟩
  apply HasType.collectionConstructor
      (rule := markingRule) (parameterName := "tokens")
      (elementType := .base "Place")
  · simp [petriNet]
  · rfl
  · apply ElementsHaveType.cons
    · exact HasType.constructor
        (rule := placeARule) (by simp [petriNet])
        (by simp [UsesBareCollection, placeARule])
        ArgumentsHaveTypes.nil
    · apply ElementsHaveType.cons
      · exact HasType.constructor
          (rule := placeBRule) (by simp [petriNet])
          (by simp [UsesBareCollection, placeBRule])
          ArgumentsHaveTypes.nil
      · exact ElementsHaveType.nil [] (.base "Place")

theorem petriNet_CD_sorted :
    SortedAt petriNet (marking [tokC, tokD]) "Marking" := by
  refine ⟨FreeTypeContext.empty, [], ?_⟩
  apply HasType.collectionConstructor
      (rule := markingRule) (parameterName := "tokens")
      (elementType := .base "Place")
  · simp [petriNet]
  · rfl
  · apply ElementsHaveType.cons
    · exact HasType.constructor
        (rule := placeCRule) (by simp [petriNet])
        (by simp [UsesBareCollection, placeCRule])
        ArgumentsHaveTypes.nil
    · apply ElementsHaveType.cons
      · exact HasType.constructor
          (rule := placeDRule) (by simp [petriNet])
          (by simp [UsesBareCollection, placeDRule])
          ArgumentsHaveTypes.nil
      · exact ElementsHaveType.nil [] (.base "Place")

/-- Source permutation is an equation of the presentation, not a property
silently granted by the host matcher. -/
theorem petriNet_BA_equivalent_AB :
    (langGSLT petriNet).Equiv
      (marking [tokB, tokA]) (marking [tokA, tokB]) := by
  exact (equationSetoid _ petriNet).iseqv.symm
    (equationEquiv_bag_perm petriNet_markingCarrier petriNet_AB_sorted
      (List.Perm.swap tokA tokB []).symm)

/-- Target permutation is likewise visible to the semantic equation theory. -/
theorem petriNet_CD_equivalent_DC :
    (langGSLT petriNet).Equiv
      (marking [tokC, tokD]) (marking [tokD, tokC]) := by
  exact equationEquiv_bag_perm petriNet_markingCarrier petriNet_CD_sorted
    (List.Perm.swap tokC tokD []).symm

private theorem petriNet_rewrites_noncontextual
    (rule : RewriteRule) (member : rule ∈ petriNet.rewrites) :
    NoncontextualPremises rule.premises := by
  simp [petriNet] at member
  rcases member with rfl | rfl
  · exact .nil
  · exact .nil

/-- For this premise-free presentation, the executable one-step list is exact
for the declarative authored relation at every input. -/
theorem petriNet_rawStep_iff_mem_reducts (source target : Pattern) :
    langReduces petriNet source target ↔ target ∈ petriNetReducts source := by
  constructor
  · intro step
    have root :=
      (step_iff_rootStep_of_noncontextualRules
        (relEnv := RelationEnv.empty)
        (rulesNoncontextual := petriNet_rewrites_noncontextual)
        (source := source) (target := target)).mp step
    obtain ⟨rule, ruleMember, initial, matched, final, premises,
      targetEquality⟩ := root
    apply mem_rewriteAt_iff_stepAt.mpr
    exact .rule ruleMember matched
      ((premisesAt_engineBase_iff_mem_applyPremisesWithEnv
        (fuel := 0) (petriNet_rewrites_noncontextual rule ruleMember)).mpr
          premises)
      targetEquality
  · intro member
    exact ⟨1, mem_rewriteAt_iff_stepAt.mp member⟩

/-- The authored rule produces `{C,D}` from `{A,B}` before equation
saturation. -/
theorem petriNet_AB_rawStep_CD :
    langReduces petriNet (marking [tokA, tokB])
      (marking [tokC, tokD]) := by
  unfold langReduces langReducesUsing
  let bindings : Bindings :=
    [("rest", .collection .hashBag [] none)]
  refine step_of_rule (rule := transitionT1)
    (initialBindings := bindings) (finalBindings := bindings)
    ?_ ?_ .nil ?_ ?_
  · simp [petriNet]
  · simp [bindings, transitionT1, marking, tokA, tokB,
      matchPatternForRule, matchPattern, matchBag, mergeBindings]
    refine ⟨[], by simp [matchArgs], bindings, ?_, ?_⟩
    · refine ⟨[], by simp [matchArgs], ?_⟩
      rfl
    · rfl
  · simp [bindings, transitionT1, applyPremisesWithEnv]
  · simp [bindings, transitionT1, marking, tokC, tokD,
      applyBindingsForRule, applyBindings]

/-- Positive `E;R;E` canary: both endpoints may change representatives while
the middle arrow remains the single authored transition. -/
theorem petriNet_BA_semanticStep_DC :
    langSemanticReduces petriNet (marking [tokB, tokA])
      (marking [tokD, tokC]) := by
  exact ⟨marking [tokA, tokB], marking [tokC, tokD],
    petriNet_BA_equivalent_AB, petriNet_AB_rawStep_CD,
    petriNet_CD_equivalent_DC⟩

/-- Negative control: the permuted target is absent from the authored raw
step.  Its semantic reachability above genuinely uses the equation theory. -/
theorem petriNet_BA_not_rawStep_DC :
    ¬ langReduces petriNet (marking [tokB, tokA])
      (marking [tokD, tokC]) := by
  rw [petriNet_rawStep_iff_mem_reducts]
  change marking [tokD, tokC] ∉
    rewriteAt (engineBasePremises RelationEnv.empty) petriNet 1
      (marking [tokB, tokA])
  simp [rewriteAt, petriNet, transitionT1, transitionT2, marking,
    tokA, tokB, tokC, tokD, applyRuleUsing, matchPatternForRule,
    matchPattern, matchBag, mergeBindings, premisesUsing,
    applyBindingsForRule, applyBindings]

/-- Native type generated from the Petri GSLT for the equation class of the
target marking. -/
def petriDCNativeType : GSLTNativeType (langGSLT petriNet) :=
  exactTargetNativeType (langGSLT petriNet) (marking [tokD, tokC])

/-- The generic GSLT-to-NTT construction instantiated on the admitted Petri
presentation's semantics modulo equations. -/
def petriGeneratedNTT : GeneratedNTT :=
  generateNTT (langGSLT validatedPetriNet.language)

/-- The equation-hidden transition inhabits the native type generated by the
sole equation-aware OSLF construction. -/
theorem petriNet_BA_satisfies_DC_nativeType :
    (gsltOSLF (langGSLT petriNet)).satisfies (S := ())
      (marking [tokB, tokA]) petriDCNativeType.pred := by
  exact (satisfies_exactTargetNativeType_iff_step
    (langGSLT petriNet) (marking [tokB, tokA])
      (marking [tokD, tokC])).2 petriNet_BA_semanticStep_DC

/-- The same equation-sensitive inhabitance fact stated through the literal
result of the generic GSLT-to-NTT constructor. -/
theorem petriGeneratedNTT_accepts_BA_to_DC :
    petriGeneratedNTT.2.satisfies (S := ())
      (marking [tokB, tokA]) petriDCNativeType.pred := by
  exact petriNet_BA_satisfies_DC_nativeType

/-! ## Executable Demos -/

-- Demo 1: Fire T1 on [A, B] → [C, D]
#eval! do
  let m := marking [tokA, tokB]
  let reducts := petriNetReducts m
  IO.println ("Demo 1: Fire T1 on {A, B}")
  IO.println s!"  reducts ({reducts.length}):"
  for r in reducts do
    IO.println s!"    -> {r}"

-- Demo 2: [A, A, B] — T1 fires, consuming one A and one B
-- Non-deterministic: which A is consumed?
#eval! do
  let m := marking [tokA, tokA, tokB]
  let reducts := petriNetReducts m
  IO.println ("Demo 2: Fire on {A, A, B}")
  IO.println s!"  reducts ({reducts.length}):"
  for r in reducts do
    IO.println s!"    -> {r}"

-- Demo 3: [C] — only T2 fires: [C] → [A]
#eval! do
  let m := marking [tokC]
  let reducts := petriNetReducts m
  IO.println ("Demo 3: Fire on {C}")
  IO.println s!"  reducts ({reducts.length}):"
  for r in reducts do
    IO.println s!"    -> {r}"

-- Demo 4: Multi-step: [A, B] →* (T1 then T2 on C)
#eval! do
  let m := marking [tokA, tokB]
  let nf := normalizeFirst petriNet 1 100 m
  IO.println ("Demo 4: Multi-step from {A, B}")
  IO.println s!"  normal form: {nf}"

-- Demo 5: [D] is a dead marking — nothing can fire
#eval! do
  let m := marking [tokD]
  let reducts := petriNetReducts m
  IO.println ("Demo 5: {D} is dead")
  IO.println s!"  reducts ({reducts.length}): expected 0"
  assert! reducts.isEmpty

-- Demo 6: Formula — can [A, B] reduce? (◇⊤ should be sat)
#eval! do
  let m := marking [tokA, tokB]
  let noAtoms : AtomCheck := fun _ _ => false
  let result := check (petriNetReducts) noAtoms 50 m (.dia .top)
  IO.println ("Demo 6: Can {A, B} reduce?")
  IO.println s!"  check (◇⊤) = {result}"

-- Demo 7: Formula — can [D] reduce? (◇⊤ should be unsat)
#eval! do
  let m := marking [tokD]
  let noAtoms : AtomCheck := fun _ _ => false
  let result := check (petriNetReducts) noAtoms 50 m (.dia .top)
  IO.println ("Demo 7: Can {D} reduce?")
  IO.println s!"  check (◇⊤) = {result}"

-- Demo 8: Non-determinism — [A, B, C] has both T1 and T2 applicable
#eval! do
  let m := marking [tokA, tokB, tokC]
  let reducts := petriNetReducts m
  IO.println ("Demo 8: {A, B, C} — both transitions applicable")
  IO.println s!"  reducts ({reducts.length}):"
  for r in reducts do
    IO.println s!"    -> {r}"

/-! ## Structural Theorems -/

/-- Place tokens are pairwise distinct. -/
theorem A_ne_B : tokA ≠ tokB := by decide
theorem A_ne_C : tokA ≠ tokC := by decide
theorem C_ne_D : tokC ≠ tokD := by decide

/-- {D} is a dead marking: no transition matches (proven via negation). -/
theorem D_is_dead : petriNetReducts (marking [tokD]) = [] := by
  simp [petriNetReducts, rewriteAt, petriNet, transitionT1, transitionT2,
    marking, tokD, applyRuleUsing,
    matchPatternForRule, matchPattern, matchBag, mergeBindings,
    premisesUsing, applyBindingsForRule, applyBindings]

/-- {A, B} has exactly one reduct via T1. -/
theorem AB_has_one_reduct :
    (petriNetReducts (marking [tokA, tokB])).length = 1 := by
  simp [petriNetReducts, rewriteAt, petriNet, transitionT1, transitionT2,
    marking, tokA, tokB, applyRuleUsing,
    matchPatternForRule, matchPattern, matchArgs, matchBag, mergeBindings,
    premisesUsing, applyBindingsForRule, applyBindings]

-- Verification: OSLF pipeline type-checks
#check petriOSLF
#check petriGalois

#print axioms petriNet_markingCarrier
#print axioms petriNet_validate
#print axioms petriNet_BA_equivalent_AB
#print axioms petriNet_CD_equivalent_DC
#print axioms petriNet_rawStep_iff_mem_reducts
#print axioms petriNet_BA_semanticStep_DC
#print axioms petriNet_BA_not_rawStep_DC
#print axioms petriNet_BA_satisfies_DC_nativeType
#print axioms petriGeneratedNTT_accepts_BA_to_DC

end Mettapedia.OSLF.Framework.PetriNetInstance
