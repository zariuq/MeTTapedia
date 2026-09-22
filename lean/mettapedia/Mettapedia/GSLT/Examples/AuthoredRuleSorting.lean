import Mettapedia.GSLT.LanguageDef.AuthoredRuleSorting
import Mettapedia.GSLT.LanguageDef.SchemaTyping
import Mettapedia.GSLT.LanguageDef.WellSortedChecker
import Mettapedia.Languages.MeTTa.HE.HELanguageDef
import Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Pattern.Core
import Mettapedia.Languages.Metamath.LanguageDefDSL

/-!
# Which authored rules are sorted by their own declarations

A language definition declares its sorts, its constructors, and -- on every rule
-- a context typing that rule's variables.  `WellSorted.HasType` says what it
means for a pattern to respect those declarations, and `checkHasType` decides
it, soundly and completely.  Nothing obliges a language to satisfy either:
`RewritesWellSorted` is a proposition that no authored language discharges, and
`LanguageDef.validate` does not ask for it.

So the question "do the shipped languages mean what they declare?" has an answer
and nobody had computed it.  This module computes it, and isolates the cause of
each failure.

**The answer is three different things.**  The largest shipped language is
entirely sorted.  The other three fail for three unrelated reasons, two of which
are properties of the decision procedure rather than of any language:

* no collection pattern carrying a rest variable is ever sorted, in any
  language, because the rest has no declared type to check it against;
* no explicit substitution is ever sorted, because the executable checker
  rejects the schema former outright while the declarative judgment admits it;
* a variable absent from its rule's declared context has no type to be checked
  at.

Each is paired with a control: for the first, the same shipped left-hand side
with its rest removed *is* sorted; for the third, the same shipped rule with its
variable declared *is* sorted.  Without those the failures would not distinguish
a missing declaration from an unsortable rule.
-/

namespace Mettapedia.GSLT.LanguageDef.AuthoredRuleSorting

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted

set_option autoImplicit false
set_option maxRecDepth 100000

/-! ## The census -/

/-- **The HE runtime core is entirely sorted by its own declarations**: all
fifty-eight rules, every variable declared, every constructor at its authored
arity.  This is the positive result the other three rows are measured against. -/
theorem mettaHE_all_rules_sorted :
    sortedCount Mettapedia.Languages.MeTTa.HE.LanguageDef.mettaHE = 58
      ∧ Mettapedia.Languages.MeTTa.HE.LanguageDef.mettaHE.rewrites.length = 58 := by
  refine ⟨by decide +kernel, by decide +kernel⟩

/-- The intrinsic pure fragment sorts two of its three rules. -/
theorem twoSortDependent_sorted_count :
    sortedCount Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Pattern.Core.twoSortDependent = 2
      ∧ Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Pattern.Core.twoSortDependent.rewrites.length = 3 := by
  refine ⟨by decide +kernel, by decide +kernel⟩

/-- **The reflective calculus sorts neither of its rules** -- including the
communication rule, which is the principal instance the whole construction is
built toward. -/
theorem rhoCalc_no_rule_sorted :
    sortedCount rhoCalc = 0 ∧ rhoCalc.rewrites.length = 2 := by
  refine ⟨by decide +kernel, by decide +kernel⟩

/-- The authored Metamath rules sort none of their hundred and ten. -/
theorem metamathCore_no_rule_sorted :
    sortedCount Mettapedia.Languages.Metamath.LanguageDefDSL.metamathCore = 0
      ∧ Mettapedia.Languages.Metamath.LanguageDefDSL.metamathCore.rewrites.length
          = 110 := by
  refine ⟨by decide +kernel, by decide +kernel⟩

/-! ## Cause one: a rest variable has no declared type

This is not a fact about any particular language.  The checker's collection case
ends in `rest.isNone`, so a collection pattern carrying a rest is rejected
before its elements are examined at all. -/

/-- The witnesses below index the rule list, so pin what they index.  The
rule's name is its first field; spelling it that way avoids the authoring DSL's
reserved token. -/
theorem rhoCalc_first_rule_is_communication :
    (rhoCalc.rewrites[0]?).map (·.1) = some "Comm" := by decide +kernel

/-- The reflective calculus' communication rule is the first it declares. -/
theorem rhoComm_left_not_sorted :
    (rhoCalc.rewrites[0]?).map (fun rule =>
        checkHasType rhoCalc (FreeTypeContext.ofList rule.typeContext) []
          rule.left (.base "Proc"))
      = some false := by decide +kernel

/-- **And the rest is the entire obstruction.**  The same shipped left-hand
side, with its rest removed and nothing else changed, is sorted at `Proc` --
so the rule's constructors, arities, binder and declared variables are all
already right. -/
theorem rhoComm_left_sorted_without_its_rest :
    (rhoCalc.rewrites[0]?).map (fun rule =>
        checkHasType rhoCalc (FreeTypeContext.ofList rule.typeContext) []
          (dropRest rule.left) (.base "Proc"))
      = some true := by decide +kernel

/-! ## Cause two: the executable checker rejects explicit substitution

The declarative judgment has a `subst` rule; the decision procedure returns
`false` for the former outright.  That is deliberate -- completeness is stated
only for object patterns -- but it means a rule whose side is a schema
substitution can never be accepted, whatever it says. -/

/-- The one unsorted rule of the intrinsic pure fragment is its beta rule. -/
theorem twoSortDependent_unsorted_rule_is_beta :
    ((Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Pattern.Core.twoSortDependent.rewrites.filter
        (fun rule => !checkRewriteWellSorted
          Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Pattern.Core.twoSortDependent rule))[0]?).map (·.1)
      = some "BetaPi" := by decide +kernel

/-- The beta rule's *left*-hand side is sorted; only its right-hand side is
not, and only because of the former above. -/
theorem twoSortDependent_beta_left_sorted_right_not :
    ((Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Pattern.Core.twoSortDependent.rewrites.filter
        (fun rule => !checkRewriteWellSorted
          Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Pattern.Core.twoSortDependent rule))[0]?).map
      (fun rule =>
        (checkHasType Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Pattern.Core.twoSortDependent
            (FreeTypeContext.ofList rule.typeContext) [] rule.left (.base "Tm"),
         checkHasType Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Pattern.Core.twoSortDependent
            (FreeTypeContext.ofList rule.typeContext) [] rule.right (.base "Tm")))
      = some (true, false) := by decide +kernel

/-! ## Cause three: an undeclared variable has no type

The authoring form the Metamath rules are written in emits no variable context,
so every one of their variables is undeclared.  Nothing else about them is
wrong. -/

/-- And what the Metamath witnesses index. -/
theorem metamath_first_rule_is_beginLower :
    (Mettapedia.Languages.Metamath.LanguageDefDSL.metamathCore.rewrites[0]?).map
      (·.1) = some "BeginLower" := by decide +kernel

/-- The first Metamath rule, as shipped: both sides unsorted at their own sort
because `db` is undeclared. -/
theorem metamath_first_rule_unsorted_as_shipped :
    (Mettapedia.Languages.Metamath.LanguageDefDSL.metamathCore.rewrites[0]?).map
      (fun rule =>
        (checkHasType Mettapedia.Languages.Metamath.LanguageDefDSL.metamathCore
            (FreeTypeContext.ofList rule.typeContext) []
            rule.left (.base "LowerState"),
         checkHasType Mettapedia.Languages.Metamath.LanguageDefDSL.metamathCore
            (FreeTypeContext.ofList rule.typeContext) []
            rule.right (.base "LowerState")))
      = some (false, false) := by decide +kernel

/-- **And declaring the variable is the entire repair.**  The same shipped
rule, checked in a context that types `db`, is sorted at `LowerState` on both
sides -- so the hundred and ten rules are not ill-formed, they are
undeclared. -/
theorem metamath_first_rule_sorted_once_declared :
    (Mettapedia.Languages.Metamath.LanguageDefDSL.metamathCore.rewrites[0]?).map
      (fun rule =>
        (checkHasType Mettapedia.Languages.Metamath.LanguageDefDSL.metamathCore
            (FreeTypeContext.ofList [("db", .base "Database")]) []
            rule.left (.base "LowerState"),
         checkHasType Mettapedia.Languages.Metamath.LanguageDefDSL.metamathCore
            (FreeTypeContext.ofList [("db", .base "Database")]) []
            rule.right (.base "LowerState")))
      = some (true, true) := by decide +kernel


/-! ## What the declarative judgment does and does not say about a rest

The two collection cases of `HasType` both bind the rest variable and neither
uses it.  So the declarative judgment is permissive exactly where the decision
procedure is restrictive: `HasType` accepts every rest, `checkHasType` refuses
every rest, and **neither consults a declaration.** -/

/-! ## The reflective calculus' communication rule is sorted

Its left-hand side, as shipped, with its own declared variable context. -/

/-- The left-hand side the reflective calculus declares for communication. -/
def communicationLeft : Pattern :=
  .collection .hashBag
    [.apply "PInput" [.fvar "n", .lambda none (.fvar "p")],
     .apply "POutput" [.fvar "n", .fvar "q"]]
    (some "rest")

/-- The variable context it declares. -/
def communicationContext : List (String × TypeExpr) :=
  [("n", .base "Name"), ("p", .base "Proc"), ("q", .base "Proc")]

/-- Both are the shipped rule's, not a retyping of it. -/
theorem communication_is_shipped :
    (rhoCalc.rewrites[0]?).map (·.left) = some communicationLeft
      ∧ (rhoCalc.rewrites[0]?).map (·.typeContext) = some communicationContext := by
  refine ⟨by decide +kernel, by decide +kernel⟩

/-- The rest-free skeleton checks at `Proc`, through the declared parallel
constructor's collection parameter. -/
theorem communication_skeleton_checks :
    checkHasType rhoCalc (FreeTypeContext.ofList communicationContext) []
      (dropRest communicationLeft) (.base "Proc") = true := by decide +kernel

/-- **So the communication rule's left-hand side is sorted at `Proc`** -- the
first such result for the principal instance.  It is obtained by deciding the
rest-free skeleton and transporting along `hasType_rest_irrelevant`, so no step
of it is hand-written. -/
theorem communicationLeft_hasType :
    HasType rhoCalc (FreeTypeContext.ofList communicationContext) []
      communicationLeft (.base "Proc") :=
  hasType_rest_irrelevant (checkHasType_sound communication_skeleton_checks)

/-- **And that is not yet enough.**  The same judgment types a collection whose
rest is declared nowhere at all, in the empty context.  So `HasType` alone
cannot be the sorting condition for a rule's sides: it cannot tell a declared
rest from an undeclared one, because it never looks. -/
theorem hasType_admits_a_wholly_undeclared_rest :
    HasType rhoCalc (FreeTypeContext.ofList []) []
      (.collection .hashBag [] (some "nowhere-declared"))
      (.collection .hashBag (.base "Proc")) :=
  .collection (ElementsHaveType.nil [] (.base "Proc"))

/-! ## The missing side condition

A rest variable is a metavariable of the rule, so it is declared where the
rule's other variables are declared, and at the type its own collection has.
Nothing prevents writing that today -- `TypeExpr.collection` exists and
`typeContext` is a list of exactly such declarations.  What is missing is that
nothing requires or reads it. -/

/-- **As shipped, the communication rule's rest is undeclared.** -/
theorem communication_rest_is_undeclared :
    ¬ topRestDeclared (FreeTypeContext.ofList communicationContext)
      (.base "Proc") communicationLeft := by decide +kernel

/-- **And declaring it is the whole repair** -- one entry in the context the
rule already carries, in a type former the language already has. -/
theorem communication_rest_declared_once_added :
    topRestDeclared
      (FreeTypeContext.ofList
        (communicationContext ++ [("rest", .collection .hashBag (.base "Proc"))]))
      (.base "Proc") communicationLeft := by decide +kernel

end Mettapedia.GSLT.LanguageDef.AuthoredRuleSorting
