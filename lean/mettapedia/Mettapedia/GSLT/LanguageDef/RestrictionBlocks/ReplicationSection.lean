import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.Section
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationObjects
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationSimulation

/-!
# The canonical section of a calculus with replication

On the closed terms of a presented calculus with restriction and replication, the canonical form with replication is a
computable section of the static equivalence (`replicationCanonicalSection`): every term is equivalent to its canonical
form inside the closed carrier, and equivalent terms have one canonical form.

A closed term and its canonical form are related by a chain of laws through object terms (`objectChain_canonR`). A
chain through object terms from a closed term stays among closed terms (`closed_of_objectChain`): each term on it has
the sort, is an object, and so has canonical binder metadata. So the chain lies in the carrier's own equivalence
(`presented_of_objectChain`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RestrictionBlocks

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.ConstructorCategory (LangSort)
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.BagNormalForm (closed_of_admissible)

/-- **The ends of a chain through object terms are both object terms or neither.** -/
theorem ObjectChain.isObject_eq {language : LanguageDef} {free : FreeTypeContext} {bound : List TypeExpr}
    {type : TypeExpr} {first second : Pattern} (chain : ObjectChain language free bound type first second) :
    isObjectPattern first = isObjectPattern second := by
  induction chain with
  | rel _ _ step => exact step.2.1.trans step.2.2.symm
  | refl => rfl
  | symm _ _ _ recurse => exact recurse.symm
  | trans _ _ _ _ _ first second => exact first.trans second

variable {language : LanguageDef} {block : ReplicationBlock} [laws : ReplicationLanguage language block]

include laws in
/-- **A chain through object terms from a closed term ends at a closed term.** -/
theorem closed_of_objectChain {sort : LangSort language} {first second : Pattern}
    (firstClosed : ClosedTermWellSorted language sort first)
    (chain : ObjectChain language FreeTypeContext.empty [] (.base sort.1) first second) :
    ClosedTermWellSorted language sort second := by
  have typed : HasType language FreeTypeContext.empty [] second (.base sort.1) :=
    chain.toSortedEquiv.typed_iff.mp firstClosed.1
  have object : isObjectPattern second = true := by
    rw [← chain.isObject_eq]
    exact firstClosed.2.2.2.1
  exact closed_of_admissible
    ⟨typed, (metadata_of_typed (block := block.toBlock) _ typed object).1 ⟨_, rfl⟩, object⟩

include laws in
/-- **A closed term is related to its canonical form by a chain through object terms.** -/
theorem objectChain_canonR {sort : LangSort language} {process : Pattern}
    (closed : ClosedTermWellSorted language sort process) :
    ObjectChain language FreeTypeContext.empty [] (.base sort.1) process (canonR block process) := by
  have sound := canonR_sound (block := block) emptyContext_base closed.1
  exact objectChain_of_equationEquiv (block := block) emptyContext_base closed.1 sound.1 closed.2.2.2.1
    (isObject_canonR closed.2.2.2.1) sound.2.toEquationEquiv

include laws in
/-- **The canonical form of a closed term is a closed term.** -/
theorem closed_canonR {sort : LangSort language} {process : Pattern}
    (closed : ClosedTermWellSorted language sort process) :
    ClosedTermWellSorted language sort (canonR block process) :=
  closed_of_objectChain (block := block) closed (objectChain_canonR closed)

end Mettapedia.GSLT.LanguageDef.RestrictionBlocks

namespace Mettapedia.GSLT.LanguageDef

open RestrictionBlocks
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted

/-- **A chain through object terms between closed terms is the carrier's own equivalence**: every term on it is
closed. -/
theorem presented_of_objectChain {presentation : InteractivePresentation} {block : ReplicationBlock}
    [laws : ReplicationLanguage presentation.presentation.language block] {first second : Pattern}
    (chain : ObjectChain presentation.presentation.language FreeTypeContext.empty []
      (.base presentation.interactingLangSort.1) first second) :
    ∀ (firstClosed : ClosedTermWellSorted presentation.presentation.language presentation.interactingLangSort first)
      (secondClosed : ClosedTermWellSorted presentation.presentation.language presentation.interactingLangSort second),
      (presentedEquationSetoid defaultBasePremises presentation).r ⟨first, firstClosed⟩ ⟨second, secondClosed⟩ := by
  induction chain with
  | rel _ _ step => exact fun _ _ => .rel _ _ step.1.step
  | refl => exact fun _ _ => .refl _
  | symm _ _ _ recurse => exact fun firstClosed secondClosed => .symm _ _ (recurse secondClosed firstClosed)
  | trans _ _ _ left _ recurseLeft recurseRight =>
      intro firstClosed secondClosed
      have middleClosed := closed_of_objectChain (block := block) firstClosed left
      exact .trans _ _ _ (recurseLeft firstClosed middleClosed) (recurseRight middleClosed secondClosed)

/-- **The canonical section of a calculus with replication.** On the closed interacting terms of an iGSLT whose
presentation is a calculus with restriction and replication, the canonical form with replication is a computable
section of the static equivalence. -/
def replicationCanonicalSection (theory : IGSLT) (block : ReplicationBlock)
    [laws : ReplicationLanguage theory.presentation.presentation.language block] :
    ComputableCanonicalSection theory where
  normalize term := ⟨canonR block term.1, closed_canonR (block := block) term.2⟩
  equivalent term :=
    Relation.EqvGen.symm _ _ (presented_of_objectChain (block := block) (objectChain_canonR term.2) term.2 _)
  complete := by
    intro left right equivalent
    apply Subtype.ext
    exact canonR_complete (block := block) left.2.2.2.2.1 right.2.2.2.2.1
      (restrictionsBind_of_typed (block := block) _ left.2.1) (equationEquiv_of_presentedEquationSetoid equivalent)

/-- The section computes the canonical form with replication of the underlying pattern. -/
@[simp] theorem replicationCanonicalSection_normalize_val (theory : IGSLT) (block : ReplicationBlock)
    [laws : ReplicationLanguage theory.presentation.presentation.language block] (term : theory.toGSLT.Term) :
    ((replicationCanonicalSection theory block).normalize term).1 = canonR block term.1 :=
  rfl

end Mettapedia.GSLT.LanguageDef
