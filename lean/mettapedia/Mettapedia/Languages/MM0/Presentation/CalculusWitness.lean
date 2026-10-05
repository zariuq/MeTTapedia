import Mettapedia.Languages.MM0.Presentation.Calculus
import Mettapedia.Languages.MM0.Kernel.ProofChecking

/-!
# Submitted MM0 witnesses as certificates

An MM0 proof witness becomes a certificate of the MM0 calculus node for node:

* a hypothesis at a position becomes the hypothesis rule over a membership
  chain of that length;
* a theorem application becomes the theorem rule over a lookup leaf, an
  instance leaf, and the translations of its children;
* a conversion becomes the conversion rule over a conversion leaf and the
  translation of its child.

The translation is an elaborator: it fills the rule arguments, such as the
declaration, the instance and the conversion result, and it is not trusted.
The checker verifies every one of them through the rules and the authored
programs. A uniform fuel for the computed leaves is the only annotation it adds.

The kernel checks a witness for an expression exactly when, with enough fuel,
the shared checker accepts its translation for the corresponding judgment.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Presentation.Calculus.Witness

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.InferenceComputedLeaves
open Mettapedia.GSLT.LanguageDef.Authored
open Mettapedia.GSLT.LanguageDef.DeterministicEquations
open Mettapedia.GSLT.LanguageDef.FirstOrderRules
open Mettapedia.Languages.MM0.Kernel

/-! ## Rule nodes -/

/-- **A rule node is accepted** exactly when its arguments fit the rule, the
goal is the rule's conclusion at them, and the children prove its premises. -/
theorem check_node_iff {Query : Type} (evaluate : Query → Option Pattern) {r : FORule}
    (member : r ∈ rules) (args : List Pattern) (children : List (CompactProof Query))
    (goal : Pattern) :
    check formMM0 evaluate goal (.node ⟨⟨r.id⟩, args⟩ children) = true ↔
      args.length = r.vars.length ∧ (∀ a ∈ args, argumentValidAt 0 a = true) ∧
        goal = r.instConclusion args ∧
          checkChildren formMM0 evaluate (r.instPremises args) children = true := by
  have key : ∀ premises conclusion,
      instantiateRule? formMM0 ⟨⟨r.id⟩, args⟩ = some (premises, conclusion) ↔
        args.length = r.vars.length ∧ (∀ a ∈ args, argumentValidAt 0 a = true) ∧
          premises = r.instPremises args ∧ conclusion = r.instConclusion args :=
    fun premises conclusion => instantiateRule?_eq_some_iff_application.trans
      (ruleApplication_iff formMM0 rules presents.package r member (presents.lookup member)
        args premises conclusion)
  simp only [check]
  constructor
  · intro accepted
    cases application : instantiateRule? formMM0 ⟨⟨r.id⟩, args⟩ with
    | none => simp [application] at accepted
    | some result =>
        obtain ⟨premises, conclusion⟩ := result
        simp only [application, Bool.and_eq_true, decide_eq_true_eq] at accepted
        obtain ⟨length, valid, rfl, rfl⟩ := (key _ _).mp application
        exact ⟨length, valid, accepted.1.symm, accepted.2⟩
  · rintro ⟨length, valid, rfl, children⟩
    rw [(key _ _).mpr ⟨length, valid, rfl, rfl⟩]
    simp [children]

theorem check_computed_iff {Query : Type} (evaluate : Query → Option Pattern) (query : Query)
    (goal : Pattern) :
    check formMM0 evaluate goal (.computed query) = true ↔ evaluate query = some goal := by
  simp [check]

/-! ## Translation -/

variable (T : Theory)

def junkExpression : Preterm := .var 0
def junkDeclaration : TheoremDecl := ⟨[], [], .var 0⟩
def junkInstance : TheoremInstance := ⟨[], .var 0⟩
def junkConversion : ConversionResult := ⟨.var 0, .var 0, 0⟩

/-- Certificates of the MM0 calculus of a theory. -/
abbrev Certificate := CompactProof (family T).Leaf

def ruleNode (r : FORule) (args : List Pattern) (children : List (Certificate T)) :
    Certificate T :=
  .node ⟨⟨r.id⟩, args⟩ children

/-- The membership chain for the hypothesis at a position. -/
def hypothesisChain : Nat → List Preterm → Certificate T
  | _, [] => ruleNode T rHypothesisHere [] []
  | 0, first :: rest =>
      ruleNode T rHypothesisHere [expressionPattern first, itemsPattern (rest.map encode)] []
  | index + 1, first :: rest =>
      ruleNode T rHypothesisThere
        [expressionPattern (rest[index]?.getD junkExpression), expressionPattern first,
          itemsPattern (rest.map encode)]
        [hypothesisChain index rest]

mutual

/-- **The certificate of a witness.** -/
def translate (fuel : Nat) (context : Context) (hypotheses : List Preterm) :
    ProofWitness → Certificate T
  | .hyp index =>
      ruleNode T rHypothesis
        [contextPattern context, expressionsPattern hypotheses,
          expressionPattern (hypotheses[index]?.getD junkExpression)]
        [hypothesisChain T index hypotheses]
  | .theoremApp index arguments children =>
      let declaration := (T.theoremSignature index).getD junkDeclaration
      let result := (declaration.instantiate? T.termSignature context arguments).getD junkInstance
      ruleNode T rTheorem
        [contextPattern context, expressionsPattern hypotheses, indexPattern index,
          theoremPattern declaration, expressionsPattern arguments,
          expressionsPattern result.hypotheses, expressionPattern result.conclusion]
        [.computed ⟨Operation.lookup, ⟨index, declaration, fuel⟩⟩,
          .computed ⟨Operation.instantiate, ⟨(context, declaration, arguments), result, fuel⟩⟩,
          translateAll fuel context hypotheses children result.hypotheses]
  | .conversion witness child =>
      let result := (witness.conversion? T.termSignature T.definitionSignature context).getD
        junkConversion
      ruleNode T rConversion
        [contextPattern context, expressionsPattern hypotheses, expressionPattern result.left,
          expressionPattern result.right, indexPattern result.sort]
        [.computed ⟨Operation.convert, ⟨(context, witness), result, fuel⟩⟩,
          translate fuel context hypotheses child]

/-- The certificate of a list of witnesses for the expressions they should
prove. -/
def translateAll (fuel : Nat) (context : Context) (hypotheses : List Preterm) :
    List ProofWitness → List Preterm → Certificate T
  | [], _ => ruleNode T rAllNil [contextPattern context, expressionsPattern hypotheses] []
  | child :: children, expressions =>
      ruleNode T rAllCons
        [contextPattern context, expressionsPattern hypotheses,
          expressionPattern (expressions.head?.getD junkExpression),
          itemsPattern (expressions.tail.map encode)]
        [translate fuel context hypotheses child,
          translateAll fuel context hypotheses children expressions.tail]

end

/-! ## Hypothesis chains -/

variable {T}

theorem hypothesisChain_accepted : ∀ (index : Nat) (hypotheses : List Preterm) {expression : Preterm},
    hypotheses[index]? = some expression →
      check formMM0 (family T).evaluate (hypothesisJ expression hypotheses)
        (hypothesisChain T index hypotheses) = true
  | _, [], _, found => by simp at found
  | 0, first :: rest, expression, found => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at found
      subst found
      refine (check_node_iff _ (r := rHypothesisHere) (by simp [rules]) _ _ _).mpr
        ⟨rfl, ?_, ?_, ?_⟩
      · simp [expressionPattern, termPattern_argumentValid, itemsPattern_argumentValid]
      · rw [(inst_rHypothesisHere _ _).2]; rfl
      · rw [(inst_rHypothesisHere _ _).1]; simp [checkChildren]
  | index + 1, first :: rest, expression, found => by
      simp only [List.getElem?_cons_succ] at found
      refine (check_node_iff _ (r := rHypothesisThere) (by simp [rules]) _ _ _).mpr
        ⟨rfl, ?_, ?_, ?_⟩
      · simp [expressionPattern, termPattern_argumentValid, itemsPattern_argumentValid]
      · rw [(inst_rHypothesisThere _ _ _).2, found]; rfl
      · rw [(inst_rHypothesisThere _ _ _).1, found]
        simp only [Option.getD_some, checkChildren, Bool.and_true]
        exact hypothesisChain_accepted index rest found

theorem hypothesisChain_sound : ∀ (index : Nat) (hypotheses : List Preterm) {expression : Preterm},
    check formMM0 (family T).evaluate (hypothesisJ expression hypotheses)
        (hypothesisChain T index hypotheses) = true →
      hypotheses[index]? = some expression
  | _, [], _, accepted => by
      simp only [hypothesisChain, ruleNode] at accepted
      have shape := (check_node_iff _ (r := rHypothesisHere) (by simp [rules]) [] [] _).mp accepted
      simp [rHypothesisHere] at shape
  | 0, first :: rest, expression, accepted => by
      obtain ⟨-, -, same, -⟩ :=
        (check_node_iff _ (r := rHypothesisHere) (by simp [rules]) _ _ _).mp accepted
      rw [(inst_rHypothesisHere _ _).2] at same
      simp only [hypothesisJ, jHypothesis, Pattern.apply.injEq, List.cons.injEq, and_true,
        true_and] at same
      simp [expressionPattern_injective same.1]
  | index + 1, first :: rest, expression, accepted => by
      obtain ⟨-, -, same, children⟩ :=
        (check_node_iff _ (r := rHypothesisThere) (by simp [rules]) _ _ _).mp accepted
      rw [(inst_rHypothesisThere _ _ _).2] at same
      rw [(inst_rHypothesisThere _ _ _).1] at children
      simp only [hypothesisJ, jHypothesis, Pattern.apply.injEq, List.cons.injEq, and_true,
        true_and] at same
      simp only [checkChildren, Bool.and_true] at children
      have found := hypothesisChain_sound index rest children
      rw [List.getElem?_cons_succ, found, ← expressionPattern_injective same.1]

/-! ## From kernel checking to acceptance -/

theorem accepted_of_checks {context : Context} {hypotheses : List Preterm}
    {witness : ProofWitness} {expression : Preterm}
    (checked : ProofWitness.Checks T.termSignature T.definitionSignature T.theoremSignature
      context hypotheses witness expression) :
    ∃ needed, ∀ fuel, needed ≤ fuel →
      check formMM0 (family T).evaluate (derivesJ context hypotheses expression)
        (translate T fuel context hypotheses witness) = true := by
  induction checked using ProofWitness.Checks.rec
      (motive_2 := fun children expressions _ => ∃ needed, ∀ fuel, needed ≤ fuel →
        check formMM0 (family T).evaluate (allJ context hypotheses expressions)
          (translateAll T fuel context hypotheses children expressions) = true) with
  | hyp found =>
      refine ⟨0, fun fuel _ => ?_⟩
      refine (check_node_iff _ (r := rHypothesis) (by simp [rules]) _ _ _).mpr ⟨rfl, ?_, ?_, ?_⟩
      · simp [contextPattern, expressionsPattern, expressionPattern, termPattern_argumentValid]
      · rw [(inst_rHypothesis _ _ _).2, found]; rfl
      · rw [(inst_rHypothesis _ _ _).1, found]
        simp only [Option.getD_some, checkChildren, Bool.and_true]
        exact hypothesisChain_accepted _ _ found
  | @theoremApp index declaration arguments children instantiation found instantiated _ ih =>
      obtain ⟨neededLookup, lookupRuns⟩ := (lookupComputation T).runs_of_relation found
      obtain ⟨neededInstance, instanceRuns⟩ :=
        (instanceComputation T).runs_of_relation (query := (context, declaration, arguments))
          instantiated
      obtain ⟨neededChildren, childrenAccepted⟩ := ih
      refine ⟨max neededLookup (max neededInstance neededChildren), fun fuel enough => ?_⟩
      have lookupEq : (T.theoremSignature index).getD junkDeclaration = declaration := by
        rw [found]; rfl
      have instanceEq :
          (declaration.instantiate? T.termSignature context arguments).getD junkInstance =
            instantiation := by
        rw [instantiated.eval]; rfl
      simp only [translate, lookupEq, instanceEq]
      refine (check_node_iff _ (r := rTheorem) (by simp [rules]) _ _ _).mpr ⟨rfl, ?_, ?_, ?_⟩
      · simp [contextPattern, expressionsPattern, expressionPattern, indexPattern, theoremPattern,
          termPattern_argumentValid]
      · rw [(inst_rTheorem _ _ _ _ _ _ _).2]; rfl
      · rw [(inst_rTheorem _ _ _ _ _ _ _).1]
        simp only [checkChildren, Bool.and_eq_true, Bool.and_true, check_computed_iff]
        refine ⟨AuthoredFamily.evaluate_of_runs (F := family T) (index := Operation.lookup)
            (lookupRuns fuel (le_trans (Nat.le_max_left _ _) enough)),
          AuthoredFamily.evaluate_of_runs (F := family T) (index := Operation.instantiate)
            (instanceRuns fuel (le_trans (le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))
              enough)),
          childrenAccepted fuel (le_trans (le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))
            enough)⟩
  | @conversion witness child left right sort converted _ ih =>
      obtain ⟨neededConversion, conversionRuns⟩ :=
        (conversionComputation T).runs_of_relation (query := (context, witness))
          (answer := ⟨left, right, sort⟩) converted
      obtain ⟨neededChild, childAccepted⟩ := ih
      refine ⟨max neededConversion neededChild, fun fuel enough => ?_⟩
      have conversionEq :
          (witness.conversion? T.termSignature T.definitionSignature context).getD
            junkConversion = ⟨left, right, sort⟩ := by
        rw [converted.eval]; rfl
      simp only [translate, conversionEq]
      refine (check_node_iff _ (r := rConversion) (by simp [rules]) _ _ _).mpr ⟨rfl, ?_, ?_, ?_⟩
      · simp [contextPattern, expressionsPattern, expressionPattern, indexPattern,
          termPattern_argumentValid]
      · rw [(inst_rConversion _ _ _ _ _).2]; rfl
      · rw [(inst_rConversion _ _ _ _ _).1]
        simp only [checkChildren, Bool.and_eq_true, Bool.and_true, check_computed_iff]
        exact ⟨AuthoredFamily.evaluate_of_runs (F := family T) (index := Operation.convert)
            (conversionRuns fuel (le_trans (Nat.le_max_left _ _) enough)),
          childAccepted fuel (le_trans (Nat.le_max_right _ _) enough)⟩
  | nil =>
      refine ⟨0, fun fuel _ => ?_⟩
      refine (check_node_iff _ (r := rAllNil) (by simp [rules]) _ _ _).mpr ⟨rfl, ?_, ?_, ?_⟩
      · simp [contextPattern, expressionsPattern, termPattern_argumentValid]
      · rw [(inst_rAllNil _ _).2]; rfl
      · rw [(inst_rAllNil _ _).1]; simp [checkChildren]
  | @cons child children first rest _ _ ihChild ihTail =>
      obtain ⟨neededChild, childAccepted⟩ := ihChild
      obtain ⟨neededTail, tailAccepted⟩ := ihTail
      refine ⟨max neededChild neededTail, fun fuel enough => ?_⟩
      refine (check_node_iff _ (r := rAllCons) (by simp [rules]) _ _ _).mpr ⟨rfl, ?_, ?_, ?_⟩
      · simp [contextPattern, expressionsPattern, expressionPattern, termPattern_argumentValid,
          itemsPattern_argumentValid]
      · rw [(inst_rAllCons _ _ _ _).2]; rfl
      · rw [(inst_rAllCons _ _ _ _).1]
        simp only [checkChildren, Bool.and_eq_true, Bool.and_true, List.head?_cons,
          Option.getD_some, List.tail_cons]
        exact ⟨childAccepted fuel (le_trans (Nat.le_max_left _ _) enough),
          tailAccepted fuel (le_trans (Nat.le_max_right _ _) enough)⟩

/-! ## From acceptance to kernel checking -/

mutual

theorem checks_of_accepted {fuel : Nat} {context : Context} {hypotheses : List Preterm} :
    ∀ (witness : ProofWitness) {expression : Preterm},
      check formMM0 (family T).evaluate (derivesJ context hypotheses expression)
          (translate T fuel context hypotheses witness) = true →
        ProofWitness.Checks T.termSignature T.definitionSignature T.theoremSignature
          context hypotheses witness expression
  | .hyp index, expression, accepted => by
      obtain ⟨-, -, same, children⟩ :=
        (check_node_iff _ (r := rHypothesis) (by simp [rules]) _ _ _).mp accepted
      rw [(inst_rHypothesis _ _ _).2] at same
      rw [(inst_rHypothesis _ _ _).1] at children
      simp only [derivesJ, jDerives, Pattern.apply.injEq, List.cons.injEq, true_and,
        and_true] at same
      simp only [checkChildren, Bool.and_true] at children
      have found := hypothesisChain_sound index hypotheses children
      rw [← expressionPattern_injective same] at found
      exact .hyp found
  | .theoremApp index arguments children, expression, accepted => by
      simp only [translate] at accepted
      obtain ⟨-, -, same, premises⟩ :=
        (check_node_iff _ (r := rTheorem) (by simp [rules]) _ _ _).mp accepted
      rw [(inst_rTheorem _ _ _ _ _ _ _).2] at same
      rw [(inst_rTheorem _ _ _ _ _ _ _).1] at premises
      simp only [derivesJ, jDerives, Pattern.apply.injEq, List.cons.injEq, true_and,
        and_true] at same
      simp only [checkChildren, Bool.and_eq_true, Bool.and_true, check_computed_iff] at premises
      obtain ⟨lookupReturned, instanceReturned, childrenAccepted⟩ := premises
      have found := (AuthoredFamily.evaluate_eq_some (F := family T) lookupReturned).1
      have instantiated := (AuthoredFamily.evaluate_eq_some (F := family T) instanceReturned).1
      have list := checksList_of_accepted children childrenAccepted
      rw [expressionPattern_injective same]
      exact .theoremApp found instantiated list
  | .conversion witness child, expression, accepted => by
      simp only [translate] at accepted
      obtain ⟨-, -, same, premises⟩ :=
        (check_node_iff _ (r := rConversion) (by simp [rules]) _ _ _).mp accepted
      rw [(inst_rConversion _ _ _ _ _).2] at same
      rw [(inst_rConversion _ _ _ _ _).1] at premises
      simp only [derivesJ, jDerives, Pattern.apply.injEq, List.cons.injEq, true_and,
        and_true] at same
      simp only [checkChildren, Bool.and_eq_true, Bool.and_true, check_computed_iff] at premises
      obtain ⟨conversionReturned, childAccepted⟩ := premises
      have converted := (AuthoredFamily.evaluate_eq_some (F := family T) conversionReturned).1
      have derived := checks_of_accepted child childAccepted
      rw [expressionPattern_injective same]
      exact .conversion converted derived

theorem checksList_of_accepted {fuel : Nat} {context : Context} {hypotheses : List Preterm} :
    ∀ (children : List ProofWitness) {expressions : List Preterm},
      check formMM0 (family T).evaluate (allJ context hypotheses expressions)
          (translateAll T fuel context hypotheses children expressions) = true →
        ProofWitness.ChecksList T.termSignature T.definitionSignature T.theoremSignature
          context hypotheses children expressions
  | [], expressions, accepted => by
      simp only [translateAll, ruleNode] at accepted
      obtain ⟨-, -, same, -⟩ :=
        (check_node_iff _ (r := rAllNil) (by simp [rules]) _ _ _).mp accepted
      rw [(inst_rAllNil _ _).2] at same
      simp only [allJ, jAll, Pattern.apply.injEq, List.cons.injEq, true_and, and_true] at same
      rw [expressionsPattern_eq_nil same.symm]
      exact .nil
  | child :: children, expressions, accepted => by
      simp only [translateAll, ruleNode] at accepted
      obtain ⟨-, -, same, premises⟩ :=
        (check_node_iff _ (r := rAllCons) (by simp [rules]) _ _ _).mp accepted
      rw [(inst_rAllCons _ _ _ _).2] at same
      rw [(inst_rAllCons _ _ _ _).1] at premises
      simp only [allJ, jAll, Pattern.apply.injEq, List.cons.injEq, true_and, and_true] at same
      obtain ⟨first, rest, rfl, firstSame, restSame⟩ := expressionsPattern_eq_cons same.symm
      simp only [checkChildren, Bool.and_eq_true, Bool.and_true, List.head?_cons,
        Option.getD_some, List.tail_cons] at premises
      exact .cons (checks_of_accepted child premises.1) (checksList_of_accepted children premises.2)

end

/-! ## The witness-preserving contract -/

/-- **The kernel checks a submitted witness for an expression exactly when the
shared checker accepts its translation**, with enough fuel for the computed
leaves. -/
theorem checks_iff_accepted (context : Context) (hypotheses : List Preterm)
    (witness : ProofWitness) (expression : Preterm) :
    ProofWitness.Checks T.termSignature T.definitionSignature T.theoremSignature
        context hypotheses witness expression ↔
      ∃ fuel, check formMM0 (family T).evaluate (derivesJ context hypotheses expression)
        (translate T fuel context hypotheses witness) = true := by
  constructor
  · intro checked
    obtain ⟨needed, accepted⟩ := accepted_of_checks checked
    exact ⟨needed, accepted needed le_rfl⟩
  · rintro ⟨fuel, accepted⟩
    exact checks_of_accepted witness accepted

/-- The same with the kernel's own checking function. -/
theorem proof_eq_some_iff_accepted (context : Context) (hypotheses : List Preterm)
    (witness : ProofWitness) (expression : Preterm) :
    ProofWitness.proof? T.termSignature T.definitionSignature T.theoremSignature
        context hypotheses witness = some expression ↔
      ∃ fuel, check formMM0 (family T).evaluate (derivesJ context hypotheses expression)
        (translate T fuel context hypotheses witness) = true :=
  (ProofWitness.proof_eq_some_iff _ _ _ _ _ _ _).trans
    (checks_iff_accepted context hypotheses witness expression)

end Mettapedia.Languages.MM0.Presentation.Calculus.Witness
