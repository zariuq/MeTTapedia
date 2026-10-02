import Mettapedia.GSLT.LanguageDef.BagNormalFormSection
import Mettapedia.GSLT.LanguageDef.ClosedTermChecker
import Mettapedia.OSLF.MeTTaIL.GeneratedRuleValidation

/-!
# A bag with no declared algebra

A contact carried by a bag that declares no algebra.  Its only static law is
permutation of components: nested bags are not spliced, a singleton bag is not
its component, and there is no unit.

The presentation is a bag theory in the permutation-only mode, so the normal
form of a bag is the sorted bag of the normal forms of its components, and it
is a section of the static equivalence.  Two orders of one bag have one
representative.  A singleton bag and its component have different
representatives, hence are not equivalent: what identifies them in a process
calculus is the declared algebra, not the bag.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Interaction.Controls.PermutationBag

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.BagNormalForm
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.StructuralMorphism
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.PatternCode

/-- The constructors: two constants, two prefixes, and a bag with no declared
algebra. -/
def terms : List GrammarRule := [
    { label := "A", category := "Proc", params := [], syntaxPattern := [] },
    { label := "B", category := "Proc", params := [], syntaxPattern := [] },
    { label := "In", category := "Proc",
      params := [.simple "body" (.base "Proc")], syntaxPattern := [.nonTerminal "body"] },
    { label := "Out", category := "Proc",
      params := [.simple "body" (.base "Proc")], syntaxPattern := [.nonTerminal "body"] },
    { label := "Par", category := "Proc",
      params := [.simple "ps" (.collection .hashBag (.base "Proc"))],
      syntaxPattern := [.nonTerminal "ps"] }
  ]

/-- An input and an output side by side in a bag meet and release their
bodies. -/
def syncRule : RewriteRule where
  name := "Sync"
  typeContext := [("x", .base "Proc"), ("y", .base "Proc")]
  premises := []
  left := .collection .hashBag [.apply "In" [.fvar "x"], .apply "Out" [.fvar "y"]]
    (some "rest")
  right := .collection .hashBag [.fvar "x", .fvar "y"] (some "rest")

/-- The presentation. -/
def permutationBag : LanguageDef :=
  { name := "PermutationBag"
    types := ["Proc"]
    terms := terms
    equations := []
    rewrites := [syncRule] }

theorem syncRule_validates :
    LanguageDef.validateRewrite permutationBag syncRule = [] := by
  apply LanguageDef.validateRewrite_eq_nil_of_premiseFree <;>
    first
      | rfl
      | decide
      | rule_patterns [syncRule, permutationBag, terms]

/-- The presentation passes the declaration gate. -/
theorem permutationBag_validate_eq_nil : permutationBag.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorAndRewrites
  · rfl
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide +kernel
  · intro rewrite membership
    obtain rfl : rewrite = syncRule := List.mem_singleton.mp membership
    exact syncRule_validates

theorem permutationBag_executionFlowErrors_eq_nil :
    permutationBag.executionFlowErrors [] = [] := by
  apply LanguageDef.executionFlowErrors_eq_nil_of_premiseFree
  · rfl
  · intro rule membership
    obtain rfl : rule = syncRule := List.mem_singleton.mp membership
    rfl
  · intro rule membership name nameMembership
    obtain rfl : rule = syncRule := List.mem_singleton.mp membership
    simp [syncRule, Pattern.freeFvarNames] at nameMembership ⊢
    tauto

/-- The bag constructor. -/
def bagConstructor : GrammarRule := terms[4]

/-- The interactive presentation: processes meet in the bag. -/
def presentation : InteractivePresentation where
  presentation := ⟨permutationBag, permutationBag_validate_eq_nil⟩
  interactingSort := ⟨TypeDecl.plain "Proc", List.Mem.head _⟩
  contactConstructor := ⟨bagConstructor, List.getElem_mem (by decide)⟩
  interactionRewrite := ⟨syncRule, List.Mem.head _⟩
  contactRepresentation := .collection .hashBag
  representsContact := by rfl
  interactionHeaded := by
    simp [InteractionHeaded, syncRule]

/-- The presentation as an iGSLT. -/
def theory : IGSLT where
  presentation := presentation
  baseInteraction := isBaseRewrite_of_premises_eq_nil rfl
  executionProfile :=
    { relationModes := []
      admitted :=
        { lang := permutationBag
          admitted := LanguageDef.executionAdmissionErrors_eq_nil_of_emptyModes _
            permutationBag_validate_eq_nil permutationBag_executionFlowErrors_eq_nil }
      exactLanguage := rfl }

/-- The presentation is a bag theory in the permutation-only mode. -/
theorem permutationBag_bagTheory : BagTheory permutationBag bagConstructor none :=
  bagTheory_of_check (by decide +kernel)

/-- Its canonical section. -/
def canonicalSection : ComputableCanonicalSection theory :=
  bagCanonicalSection theory permutationBag_bagTheory

/-- The constant `A`. -/
def termA : Pattern := .apply "A" []

/-- The constant `B`. -/
def termB : Pattern := .apply "B" []

/-- `A` as a closed process. -/
def closedA : presentation.Term := ClosedTerm.ofCheck termA (by decide +kernel)

/-- `{A | B}` as a closed process. -/
def pairAB : presentation.Term :=
  ClosedTerm.ofCheck (.collection .hashBag [termA, termB] none) (by decide +kernel)

/-- `{B | A}` as a closed process. -/
def pairBA : presentation.Term :=
  ClosedTerm.ofCheck (.collection .hashBag [termB, termA] none) (by decide +kernel)

/-- `{A}` as a closed process. -/
def singletonA : presentation.Term :=
  ClosedTerm.ofCheck (.collection .hashBag [termA] none) (by decide +kernel)

/-- **Two orders of one bag have one representative.** -/
theorem pair_orders_normalize_alike :
    canonicalSection.normalize pairAB = canonicalSection.normalize pairBA := by
  apply Subtype.ext
  show normalForm none (.collection .hashBag [termA, termB] none) =
    normalForm none (.collection .hashBag [termB, termA] none)
  rw [normalForm_bag, normalForm_bag]
  exact normalizeBag_perm none (List.Perm.swap _ _ _)

/-- The two orders are equivalent. -/
theorem pair_orders_equivalent : theory.toGSLT.equations.r pairAB pairBA :=
  (canonicalSection.equivalent_iff_normalize_eq _ _).mpr pair_orders_normalize_alike

/-- **A singleton bag is not its component.**  With no declared algebra the
singleton law is absent: the two have different representatives and are not
equivalent. -/
theorem singleton_not_equivalent : ¬ theory.toGSLT.equations.r singletonA closedA := by
  intro equivalent
  have same := congrArg Subtype.val (canonicalSection.complete equivalent)
  have left : (canonicalSection.normalize singletonA).1 =
      .collection .hashBag [termA] none := by
    show normalForm none (.collection .hashBag [termA] none) = _
    simp [normalForm, normalizeBag, termA]
  have right : (canonicalSection.normalize closedA).1 = termA := by
    show normalForm none termA = termA
    simp [normalForm, termA]
  rw [left, right] at same
  simp [termA] at same

end Mettapedia.GSLT.LanguageDef.Interaction.Controls.PermutationBag
