import Mettapedia.Languages.OpenTheory.Definitions

/-!
# Nominal source evidence at the OpenTheory article boundary

Alpha-canonical theorem state is sufficient for theorem-rule replay, but the
pinned definition mechanisms store nominal source terms inside symbol
provenance.  This module states the resulting information boundary without
choosing a complete article-object representation.
-/

namespace Mettapedia.Languages.OpenTheory

/-- Retained source evidence supplies the exact provenance payload used by a
type-operator definition. -/
def CheckedSourceTerm.typeOperatorProvenance (term : CheckedSourceTerm)
    (typeVariables : List Name) : TypeOpProvenance :=
  .defined term.source typeVariables

/-- A hypothetical recovery procedure is exact when it recovers every named
source term from every successful canonical check. -/
def ExactSourceRecovery (recover : CanonicalTerm → SourceTerm) : Prop :=
  ∀ source canonical, source.check = some canonical →
    recover canonical = source

/-- Any two distinct source representatives with one canonical image rule out
exact recovery from canonical state alone. -/
theorem no_exactSourceRecovery_of_check_collision
    {left right : SourceTerm} {canonical : CanonicalTerm}
    (leftChecked : left.check = some canonical)
    (rightChecked : right.check = some canonical)
    (different : left ≠ right) :
    ¬ ∃ recover, ExactSourceRecovery recover := by
  rintro ⟨recover, exact⟩
  have recoversLeft := exact left canonical leftChecked
  have recoversRight := exact right canonical rightChecked
  exact different (recoversLeft.symm.trans recoversRight)

/-- Recovering exact type-definition provenance from only a canonical
predicate would have to reproduce every nominal predicate representative. -/
def ExactTypeOperatorProvenanceRecovery
    (recover : CanonicalTerm → List Name → TypeOpProvenance) : Prop :=
  ∀ source canonical typeVariables,
    source.check = some canonical →
      recover canonical typeVariables =
        .defined source typeVariables

/-- A canonical collision of distinct sources also rules out exact recovery of
the pinned type-operator provenance. -/
theorem no_exactTypeOperatorProvenanceRecovery_of_check_collision
    {left right : SourceTerm} {canonical : CanonicalTerm}
    (leftChecked : left.check = some canonical)
    (rightChecked : right.check = some canonical)
    (different : left ≠ right) :
    ¬ ∃ recover, ExactTypeOperatorProvenanceRecovery recover := by
  rintro ⟨recover, exact⟩
  have leftProvenance := exact left canonical [] leftChecked
  have rightProvenance := exact right canonical [] rightChecked
  have provenanceEquality :
      TypeOpProvenance.defined left [] =
        TypeOpProvenance.defined right [] :=
    leftProvenance.symm.trans rightProvenance
  exact different (TypeOpProvenance.defined.inj provenanceEquality).1

/-- Distinct nominal sources induce distinct defined type-operator provenance
when the declared variable list is fixed. -/
theorem typeOperatorProvenance_ne_of_source_ne
    {left right : SourceTerm} (different : left ≠ right)
    (typeVariables : List Name) :
    TypeOpProvenance.defined left typeVariables ≠
      TypeOpProvenance.defined right typeVariables := by
  intro provenanceEquality
  exact different (TypeOpProvenance.defined.inj provenanceEquality).1

/-- Distinct definition sources likewise induce distinct constant provenance. -/
theorem constantProvenance_ne_of_source_ne
    {left right : SourceTerm} (different : left ≠ right) :
    ConstProvenance.defined left ≠ ConstProvenance.defined right := by
  intro provenanceEquality
  exact different (ConstProvenance.defined.inj provenanceEquality)

end Mettapedia.Languages.OpenTheory
