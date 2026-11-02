import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.Typed
import Mettapedia.GSLT.LanguageDef.BagNormalFormSection

/-!
# The canonical section of a calculus with restriction

On the closed terms of a presented calculus with restriction, the canonical form is a computable section of the static
equivalence (`blockCanonicalSection`): every term is equivalent to its canonical form inside the closed carrier, and
equivalent terms have one canonical form.

A sorted chain from a closed term stays among closed terms (`closed_of_sorted`): each term on it has the sort, is an
object, and so has canonical binder metadata. So the canonical form's chain lies in the carrier's own equivalence
(`presented_of_sorted`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RestrictionBlocks

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.ConstructorCategory (LangSort)
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.BagNormalForm (closed_of_admissible)

variable {language : LanguageDef} {block : Block}

/-- The empty context is a context of base sorts. -/
theorem emptyContext_base : BaseContext FreeTypeContext.empty [] :=
  ⟨fun _ _ found => by simp [FreeTypeContext.empty] at found, fun _ member => by simp at member⟩

variable [laws : BlockLanguage language block]

include laws in
/-- **A sorted chain from a closed term ends at a closed term.** -/
theorem closed_of_sorted {sort : LangSort language} {first second : Pattern}
    (firstClosed : ClosedTermWellSorted language sort first)
    (chain : SortedEquiv language FreeTypeContext.empty [] (.base sort.1) first second) :
    ClosedTermWellSorted language sort second := by
  have typed : HasType language FreeTypeContext.empty [] second (.base sort.1) := chain.typed_iff.mp firstClosed.1
  have object : isObjectPattern second = true := by
    rw [← equationEquiv_isObject (block := block) chain.toEquationEquiv]
    exact firstClosed.2.2.2.1
  exact closed_of_admissible ⟨typed, (metadata_of_typed (block := block) _ typed object).1 ⟨_, rfl⟩, object⟩

end Mettapedia.GSLT.LanguageDef.RestrictionBlocks

namespace Mettapedia.GSLT.LanguageDef

open RestrictionBlocks
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted

/-- **A sorted chain between closed terms is the carrier's own equivalence**: every term on it is closed. -/
theorem presented_of_sorted {presentation : InteractivePresentation} {block : Block}
    [laws : BlockLanguage presentation.presentation.language block] {first second : Pattern}
    (chain : SortedEquiv presentation.presentation.language FreeTypeContext.empty []
      (.base presentation.interactingLangSort.1) first second) :
    ∀ (firstClosed : ClosedTermWellSorted presentation.presentation.language presentation.interactingLangSort first)
      (secondClosed : ClosedTermWellSorted presentation.presentation.language presentation.interactingLangSort second),
      (presentedEquationSetoid defaultBasePremises presentation).r ⟨first, firstClosed⟩ ⟨second, secondClosed⟩ := by
  induction chain with
  | rel _ _ step => exact fun _ _ => .rel _ _ step.step
  | refl => exact fun _ _ => .refl _
  | symm _ _ _ recurse => exact fun firstClosed secondClosed => .symm _ _ (recurse secondClosed firstClosed)
  | trans _ _ _ left _ recurseLeft recurseRight =>
      intro firstClosed secondClosed
      have middleClosed := closed_of_sorted (block := block) firstClosed left
      exact .trans _ _ _ (recurseLeft firstClosed middleClosed) (recurseRight middleClosed secondClosed)

/-- **The canonical section of a calculus with restriction.** On the closed interacting terms of an iGSLT whose
presentation is a calculus with restriction, the canonical form is a computable section of the static equivalence. -/
def blockCanonicalSection (theory : IGSLT) (block : Block)
    [laws : BlockLanguage theory.presentation.presentation.language block] : ComputableCanonicalSection theory where
  normalize term := ⟨canon block term.1, closed_of_sorted (block := block) term.2 (canon_sound emptyContext_base term.2.1).2⟩
  equivalent term :=
    Relation.EqvGen.symm _ _ (presented_of_sorted (block := block) (canon_sound emptyContext_base term.2.1).2 term.2 _)
  complete := by
    intro left right equivalent
    apply Subtype.ext
    exact canon_complete (block := block) left.2.2.2.2.1 (equationEquiv_of_presentedEquationSetoid equivalent)

/-- The section computes the canonical form of the underlying pattern. -/
@[simp] theorem blockCanonicalSection_normalize_val (theory : IGSLT) (block : Block)
    [laws : BlockLanguage theory.presentation.presentation.language block] (term : theory.toGSLT.Term) :
    ((blockCanonicalSection theory block).normalize term).1 = canon block term.1 :=
  rfl

end Mettapedia.GSLT.LanguageDef
