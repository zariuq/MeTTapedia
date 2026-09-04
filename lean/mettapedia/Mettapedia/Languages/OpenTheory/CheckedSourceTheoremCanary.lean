import Mettapedia.Languages.OpenTheory.CheckedSourceTheorem

/-!
# Controls for source-retaining OpenTheory definition checking

The positive and negative controls below exercise the source-retaining
constant-definition square.  The final pair records why retaining source
syntax is substantive: alpha-equivalent definitions have the same canonical
term while inducing distinct provenance-bearing constants.
-/

namespace Mettapedia.Languages.OpenTheory.CheckedSourceTheoremCanary

open Mettapedia.Languages.OpenTheory

def booleanValue : Const :=
  .mk (Name.global "checkedBooleanValue") .undefined

def closedBoolean : CheckedSourceTerm :=
  ⟨.const booleanValue Ty.bool, Ty.bool, by simp [SourceTerm.inferType]⟩

/-- A closed checked term is admitted, retaining its exact source syntax. -/
theorem closedBoolean_admitted :
    checkCheckedConstantDefinition (Name.global "definedCheckedBoolean")
        closedBoolean =
      some (makeCheckedConstantDefinition
        (Name.global "definedCheckedBoolean") closedBoolean) := by
  simp [checkCheckedConstantDefinition, closedBoolean,
    CheckedSourceTerm.canonical, DBTerm.hasNoFreeVariables,
    DBTerm.typeVariables, Ty.typeVariables, Ty.typeVariablesList, Ty.bool]

def openIndividual : CheckedSourceTerm :=
  CheckedSourceTerm.ofVariable
    ⟨Name.global "freeIndividual", Examples.individual⟩

/-- A checked but open term is rejected as a constant definition. -/
theorem openIndividual_rejected :
    checkCheckedConstantDefinition (Name.global "badCheckedDefinition")
      openIndividual = none := by
  simp [checkCheckedConstantDefinition, openIndividual,
    CheckedSourceTerm.ofVariable, CheckedSourceTerm.canonical,
    SourceTerm.toDB, boundIndex, DBTerm.hasNoFreeVariables]

/-- The positive control also commutes with the independently defined pinned
source checker. -/
theorem closedBoolean_commutes :
    (checkCheckedConstantDefinition
        (Name.global "definedCheckedBoolean") closedBoolean).map
        CheckedConstantDefinitionResult.canonical =
      checkConstantDefinition
        (Name.global "definedCheckedBoolean") closedBoolean.source :=
  checkCheckedConstantDefinition_commutes _ _

def identityX : CheckedSourceTerm :=
  ⟨Examples.identityX,
    .function Examples.individual Examples.individual,
    by simp [Examples.identityX, SourceTerm.inferType]⟩

def identityY : CheckedSourceTerm :=
  ⟨Examples.identityY,
    .function Examples.individual Examples.individual,
    by simp [Examples.identityY, SourceTerm.inferType]⟩

/-- Binder spelling is erased by the canonical projection. -/
theorem identities_have_same_canonical_term :
    identityX.canonical = identityY.canonical := by
  apply CanonicalTerm.ext_term
  simp [identityX, identityY, CheckedSourceTerm.canonical,
    Examples.identityX, Examples.identityY, SourceTerm.toDB,
    boundIndex, sourceVarSame, Examples.x, Examples.y]

/-- The same alpha class nevertheless defines distinct provenance-bearing
constants when its named source representatives differ. -/
theorem alpha_equal_definitions_retain_distinct_provenance :
    (makeCheckedConstantDefinition (Name.global "identity") identityX).constant ≠
      (makeCheckedConstantDefinition
        (Name.global "identity") identityY).constant := by
  intro constantsEqual
  have provenanceEqual :
      ConstProvenance.defined identityX.source =
        ConstProvenance.defined identityY.source := by
    exact Const.mk.inj constantsEqual |>.2
  have sourcesEqual : identityX.source = identityY.source :=
    ConstProvenance.defined.inj provenanceEqual
  simp [identityX, identityY, Examples.identityX, Examples.identityY,
    Examples.x, Examples.y, Name.global] at sourcesEqual

end Mettapedia.Languages.OpenTheory.CheckedSourceTheoremCanary
