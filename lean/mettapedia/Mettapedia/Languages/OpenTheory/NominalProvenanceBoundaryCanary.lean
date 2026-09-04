import Mettapedia.Languages.OpenTheory.NominalProvenanceBoundary

/-!
# Alpha-collision control for nominal OpenTheory provenance

Two identity functions differing only in their binder spelling check to one
canonical term.  The pinned provenance representation nevertheless retains
the two distinct source terms.  This is the smallest concrete witness that an
article reader cannot discard nominal source evidence and later reconstruct it
from canonical theorem state.
-/

namespace Mettapedia.Languages.OpenTheory.NominalProvenanceBoundaryCanary

open Mettapedia.Languages.OpenTheory

def canonicalIdentity : CanonicalTerm :=
  ⟨.abs Examples.individual (.bound 0),
    .function Examples.individual Examples.individual,
    by simp [DBTerm.inferType]⟩

theorem identityX_checked :
    Examples.identityX.check = some canonicalIdentity := by
  rw [SourceTerm.check_eq_some_iff]
  simp [Examples.identityX, canonicalIdentity, SourceTerm.toDB,
    boundIndex, sourceVarSame, Examples.x]

theorem identityY_checked :
    Examples.identityY.check = some canonicalIdentity := by
  rw [SourceTerm.check_eq_some_iff]
  simp [Examples.identityY, canonicalIdentity, SourceTerm.toDB,
    boundIndex, sourceVarSame, Examples.y]

theorem identity_sources_different :
    Examples.identityX ≠ Examples.identityY := by
  simp [Examples.identityX, Examples.identityY, Examples.x, Examples.y,
    Name.global]

def identityXCheckedSource : CheckedSourceTerm :=
  ⟨Examples.identityX, .function Examples.individual Examples.individual,
    by simp [Examples.identityX, SourceTerm.inferType]⟩

def identityYCheckedSource : CheckedSourceTerm :=
  ⟨Examples.identityY, .function Examples.individual Examples.individual,
    by simp [Examples.identityY, SourceTerm.inferType]⟩

theorem identityXCheckedSource_canonical :
    identityXCheckedSource.canonical = canonicalIdentity := by
  apply CanonicalTerm.ext_term
  simp [identityXCheckedSource, CheckedSourceTerm.canonical,
    canonicalIdentity, Examples.identityX, SourceTerm.toDB, boundIndex,
    sourceVarSame, Examples.x]

theorem identityYCheckedSource_canonical :
    identityYCheckedSource.canonical = canonicalIdentity := by
  apply CanonicalTerm.ext_term
  simp [identityYCheckedSource, CheckedSourceTerm.canonical,
    canonicalIdentity, Examples.identityY, SourceTerm.toDB, boundIndex,
    sourceVarSame, Examples.y]

/-- Forgetting the source representative is genuinely non-injective. -/
theorem checkedSourceTerm_canonical_not_injective :
    ¬ Function.Injective CheckedSourceTerm.canonical := by
  intro injective
  have checkedSourceEquality :
      identityXCheckedSource = identityYCheckedSource :=
    injective
      (identityXCheckedSource_canonical.trans
        identityYCheckedSource_canonical.symm)
  have sourceEquality := congrArg CheckedSourceTerm.source
    checkedSourceEquality
  exact identity_sources_different sourceEquality

/-- No algorithm seeing only the canonical term can recover every checked
source representative. -/
theorem no_exact_source_recovery :
    ¬ ∃ recover, ExactSourceRecovery recover :=
  no_exactSourceRecovery_of_check_collision identityX_checked
    identityY_checked identity_sources_different

/-- In particular, canonical predicate state cannot reproduce exact pinned
type-operator provenance for both alpha variants. -/
theorem no_exact_type_operator_provenance_recovery :
    ¬ ∃ recover, ExactTypeOperatorProvenanceRecovery recover :=
  no_exactTypeOperatorProvenanceRecovery_of_check_collision
    identityX_checked identityY_checked identity_sources_different

/-- Retaining the source representative records the intended provenance
without guessing a binder spelling. -/
theorem retained_source_has_exact_provenance :
    identityXCheckedSource.typeOperatorProvenance [] =
      .defined Examples.identityX [] := by
  rfl

end Mettapedia.Languages.OpenTheory.NominalProvenanceBoundaryCanary
