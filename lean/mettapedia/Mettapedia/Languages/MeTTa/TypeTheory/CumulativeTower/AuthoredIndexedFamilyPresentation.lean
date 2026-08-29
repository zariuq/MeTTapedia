import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.AuthoredDeclarationSignature
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.DeclarationHostedJudgments
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.IndexedFamilyDeclaration

/-!
# Source-directed presentations of native indexed families

An indexed-family `Candidate` is already an extensional semantic object.  Its
constant lookup is not a finite source inventory, and its proposition-valued
computation support cannot recover authored equation occurrences.  This module
therefore makes the finite authored inventory primary and derives the candidate
presentation from two exact comparisons:

* equality of finite constant lookup with the candidate signature; and
* fibrewise equivalence of authored equation occurrences with native receipts.

The resulting `PresentedCandidate` can form a declaration host immediately.
It becomes a computational host only after the independent preservation family
is supplied.  No source decoder, universal checker, or new typing calculus is
introduced.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
namespace AuthoredIndexedFamilyPresentation

open AuthoredDeclarationSignature
open DeclarationHostedJudgments
open Presentation
open Presentation.Declaration
open Presentation.Declaration.IndexedFamily

private theorem rootComputation_eq_of_step_eq
    (first second : RootComputation Tower.Head)
    (stepEquation :
      @RootComputation.step Tower.Head first =
        @RootComputation.step Tower.Head second) : first = second := by
  cases first with
  | mk firstStep firstRename firstSubstitute =>
      cases second with
      | mk secondStep secondRename secondSubstitute =>
          dsimp at stepEquation
          cases stepEquation
          rfl

private theorem signature_eq
    (first second : Signature Tower.Head)
    (entries : first.entries = second.entries)
    (computation : first.computation = second.computation) :
    first = second := by
  cases first
  cases second
  cases entries
  cases computation
  rfl

/-! ## Source-directed candidate -/

/-- A formed native family together with its actual authored source and exact
proof-fibre comparison.  Extensional signature equality alone is deliberately
insufficient for this package. -/
structure PresentedCandidate where
  source : SourceDocument
  candidate : Candidate Tower.rules
  interpretation : interpret source = candidate.signature
  receiptEquiv :
    ∀ {n : Nat} {left right : Tower.Tm n},
      EquationOccurrence (equationSchemas (elaborate source)) left right ≃
        candidate.computation.Evidence left right

namespace PresentedCandidate

def toFormationHost (presented : PresentedCandidate) : FormationHost where
  source := presented.source
  formed := by
    rw [presented.interpretation]
    exact presented.candidate.formed

/-- Exact receipt adequacy does not grant reduction authority.  Promotion to a
computational host additionally consumes the candidate's preservation law. -/
def toComputationalHost (presented : PresentedCandidate)
    (preserves :
      presented.candidate.signature.DeclaredPreserves Tower.rules) :
    ComputationalHost where
  source := presented.source
  wellFormed := by
    rw [presented.interpretation]
    exact presented.candidate.formed.withPreservation preserves

/-- Fibrewise receipt equivalence implies equality of logical computation
support.  The converse is refuted below at the authored-source layer. -/
theorem computation_support_eq (presented : PresentedCandidate) :
    (equationComputation
        (equationSchemas (elaborate presented.source))).support =
      presented.candidate.computation.support := by
  apply rootComputation_eq_of_step_eq
  funext n left right
  apply propext
  constructor
  · rintro ⟨occurrence⟩
    exact ⟨presented.receiptEquiv occurrence⟩
  · rintro ⟨receipt⟩
    exact ⟨presented.receiptEquiv.symm receipt⟩

@[simp] theorem toFormationHost_source (presented : PresentedCandidate) :
    presented.toFormationHost.source = presented.source := rfl

end PresentedCandidate

/-! ## Finite authored inventory -/

/-- Finite source data and the two comparisons from which a presented native
family is derived.  Constants and equations may be interleaved in
`declarations`; their authored order is retained by quotation. -/
structure AuthoredCandidateInventory where
  declarations : List SourceDeclaration
  candidate : Candidate Tower.rules
  entries :
    (Signature.ofList (constantDeclarations declarations)).entries =
      candidate.signature.entries
  receiptEquiv :
    ∀ {n : Nat} {left right : Tower.Tm n},
      EquationOccurrence (equationSchemas declarations) left right ≃
        candidate.computation.Evidence left right

namespace AuthoredCandidateInventory

def source (inventory : AuthoredCandidateInventory) : SourceDocument :=
  sourceCodec.quote inventory.declarations

@[simp] theorem elaborate_source (inventory : AuthoredCandidateInventory) :
    elaborate inventory.source = inventory.declarations := by
  simp [source]

/-- The finite constant comparison and proof-fibre equivalence determine the
entire extensional signature interpretation. -/
theorem interpretation (inventory : AuthoredCandidateInventory) :
    interpret inventory.source = inventory.candidate.signature := by
  unfold source
  rw [interpret_quote]
  apply signature_eq
  · exact inventory.entries
  · calc
      (semanticSignature inventory.declarations).computation =
          (equationComputation
            (equationSchemas inventory.declarations)).support := rfl
      _ = inventory.candidate.computation.support := by
        apply rootComputation_eq_of_step_eq
        funext n left right
        apply propext
        constructor
        · rintro ⟨occurrence⟩
          exact ⟨inventory.receiptEquiv occurrence⟩
        · rintro ⟨receipt⟩
          exact ⟨inventory.receiptEquiv.symm receipt⟩
      _ = inventory.candidate.signature.computation :=
        inventory.candidate.computationSupport.symm

noncomputable def toPresentedCandidate
    (inventory : AuthoredCandidateInventory) : PresentedCandidate where
  source := inventory.source
  candidate := inventory.candidate
  interpretation := inventory.interpretation
  receiptEquiv :=
    (EquationOccurrence.schemaEquiv
      (congrArg equationSchemas inventory.elaborate_source)).trans
        inventory.receiptEquiv

end AuthoredCandidateInventory

/-! ## Negative source boundary -/

/-- No function can recover every authored declaration inventory from its
extensional signature.  In particular, a native `Candidate` cannot be used as
the hidden source generator for this interface. -/
theorem no_signature_source_decoder :
    ¬ ∃ decode : Signature Tower.Head → List SourceDeclaration,
      ∀ declarations : List SourceDeclaration,
        decode (semanticSignature declarations) = declarations := by
  rintro ⟨decode, leftInverse⟩
  apply semanticSignature_not_injective
  intro first second sameSignature
  rw [← leftInverse first, ← leftInverse second, sameSignature]

#print axioms PresentedCandidate.computation_support_eq
#print axioms AuthoredCandidateInventory.interpretation
#print axioms AuthoredCandidateInventory.toPresentedCandidate
#print axioms no_signature_source_decoder

end AuthoredIndexedFamilyPresentation
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
