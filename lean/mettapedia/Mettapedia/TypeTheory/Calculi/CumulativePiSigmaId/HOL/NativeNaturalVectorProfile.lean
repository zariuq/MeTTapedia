import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateExtension
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeNaturalEqualityCode
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeNaturalGuardedContexts
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeVectorGuardedElimination

/-!
# A shared reading of the original Nat and Vec schema table

Both families use the same number and result carriers and the same zero and
successor terms. The encoded Vec construction retains its element/vector
carriers. All four original addresses have retained computation proofs.
The ordered premise list contains the two natural-row premises followed by
the seven encoded-vector premises; repeated formulas are not deduplicated.

This profile supports the selected fixed-carrier readings. It is not a
universe-polymorphic interpretation or a new source normalization policy.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalVectorProfile
open Mettapedia.Logic
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality.Annotated NativeNaturalVectorFamilies
local infixr:60 " ⇒ " => HOL.Ty.arr
universe u v
variable {Base : Type u} {Const : HOL.Ty Base → Type v}


variable (raw : HOL.RawVectorConstructors.Signature Base Const) (vectorInterface : NativeVectorComputationRows.EncodedConstructor.Interface raw)
  (naturalSelection : HOL.ClosedTerm Const (HOL.SelectionProofs.Selection (raw.number ⇒ vectorInterface.result)))

def natural : NativeNaturalPredicateReading.Operations Base Const where
  number := raw.number
  result := vectorInterface.result
  zero := raw.zero
  successor := raw.successor
  selection := naturalSelection

def vector := NativeVectorComputationRows.EncodedConstructor.operations raw vectorInterface

def lexical : AnnotatedPredicateReading.LexicalReading Tower.Head Base Const where
  constCode? name := if name = natEliminateName then
    some ⟨_, (natural raw vectorInterface naturalSelection).eliminator⟩
    else (NativeVectorComputationRows.GuardedFamily.lexical (vector raw vectorInterface)).constCode? name
  headCode? head := if head = .sort motiveLevel then
    some ⟨_, HOL.PredicateProducts.full (vectorInterface.result ⇒ .prop)⟩
    else (NativeVectorComputationRows.GuardedFamily.lexical (vector raw vectorInterface)).headCode? head

theorem original_motive_not_element : (.sort motiveLevel : Tower.Head) ≠ NativeVectorComputationRows.GuardedFamily.elementHead := by decide
theorem original_motive_not_instantiated : (.sort motiveLevel : Tower.Head) ≠ NativeVectorComputationRows.GuardedFamily.motiveHead := by decide
theorem element_not_motive : NativeVectorComputationRows.GuardedFamily.elementHead ≠ NativeVectorComputationRows.GuardedFamily.motiveHead := by decide

theorem vector_lexical : AnnotatedPredicateReading.LexicalMap (NativeVectorComputationRows.GuardedFamily.lexical (vector raw vectorInterface))
    (lexical raw vectorInterface naturalSelection) (fun head => head) := by
  constructor
  · intro name type code found
    have distinct : name ≠ natEliminateName := by
      intro same
      subst name
      simp [NativeVectorComputationRows.GuardedFamily.lexical, NativeVectorComputationRows.Operations.lexicalReading, natEliminateName, vecName,
        natName, zeroName, succName, vnilName, vconsName, vecEliminateName] at found
    simpa only [lexical, if_neg distinct] using found
  · intro head type code found
    have distinct : head ≠ .sort motiveLevel := by
      intro same
      subst head
      simp only [NativeVectorComputationRows.GuardedFamily.lexical, if_neg original_motive_not_element,
        if_neg original_motive_not_instantiated] at found
      cases found
    simpa only [lexical, if_neg distinct] using found

  · intro operator result code found
    cases found

theorem natural_lexical : AnnotatedPredicateReading.LexicalMap (NativeNaturalPredicateReading.lexicalReading (natural raw vectorInterface naturalSelection))
    (lexical raw vectorInterface naturalSelection) (fun head => head) := by
  constructor
  · intro name type code found
    by_cases nat : name = natName
    · subst name
      simpa [NativeNaturalPredicateReading.lexicalReading, lexical, natural, vector, NativeVectorComputationRows.GuardedFamily.lexical, NativeVectorComputationRows.Operations.lexicalReading,
        NativeVectorComputationRows.EncodedConstructor.operations, natName, natEliminateName, vecName] using found
    by_cases zero : name = zeroName
    · subst name
      simpa [NativeNaturalPredicateReading.lexicalReading, lexical, natural, vector, NativeVectorComputationRows.GuardedFamily.lexical, NativeVectorComputationRows.Operations.lexicalReading,
        NativeVectorComputationRows.EncodedConstructor.operations, zeroName, natName, natEliminateName, vecName] using found
    by_cases succ : name = succName
    · subst name
      simpa [NativeNaturalPredicateReading.lexicalReading, lexical, natural, vector, NativeVectorComputationRows.GuardedFamily.lexical, NativeVectorComputationRows.Operations.lexicalReading,
        NativeVectorComputationRows.EncodedConstructor.operations, succName, zeroName, natName, natEliminateName, vecName] using found
    by_cases elim : name = natEliminateName
    · subst name
      simpa [NativeNaturalPredicateReading.lexicalReading, lexical, natEliminateName, natName, zeroName, succName] using found
    simp [NativeNaturalPredicateReading.lexicalReading, nat, zero, succ, elim] at found
  · intro head type code found
    by_cases same : head = .sort motiveLevel
    · subst head
      simpa [NativeNaturalPredicateReading.lexicalReading, lexical, natural] using found
    simp [NativeNaturalPredicateReading.lexicalReading, same] at found

  · intro operator result code found
    cases found

theorem guarded_natural_lexical : AnnotatedPredicateReading.LexicalMap (NativeNaturalPredicateReading.GuardedContexts.lexical (natural raw vectorInterface naturalSelection))
    (lexical raw vectorInterface naturalSelection) (fun head => head) := by
  constructor
  · exact (natural_lexical raw vectorInterface naturalSelection).constants
  · intro head type code found
    by_cases same : head = NativeVectorComputationRows.GuardedFamily.motiveHead
    · subst head
      change (if NativeVectorComputationRows.GuardedFamily.motiveHead = NativeVectorComputationRows.GuardedFamily.motiveHead then
        some (⟨(vectorInterface.result ⇒ .prop) ⇒ .prop, HOL.PredicateProducts.full (vectorInterface.result ⇒ .prop)⟩ :
          (carrier : HOL.Ty Base) × HOL.ClosedTerm Const carrier) else none) = some ⟨type, code⟩ at found
      simpa only [if_pos rfl, lexical, NativeVectorComputationRows.GuardedFamily.lexical,
        if_neg original_motive_not_instantiated.symm, if_neg element_not_motive.symm, ite_true,
        vector, NativeVectorComputationRows.EncodedConstructor.operations] using found
    have different : head ≠ NativeNaturalPredicateReading.GuardedContexts.levelMap (.sort motiveLevel) := same
    simp [NativeNaturalPredicateReading.GuardedContexts.lexical, different] at found

  · intro operator result code found
    cases found

def closedAssumptions : List (HOL.ClosedFormula Const) :=
  NativeNaturalPredicateReading.AnnotatedConversion.closedAssumptions (natural raw vectorInterface naturalSelection) ++
    NativeVectorComputationRows.EncodedConstructor.closedAssumptions raw vectorInterface

def naturalExtension : AnnotatedPredicateReading.ReadingExtension (NativeNaturalPredicateReading.lexicalReading (natural raw vectorInterface naturalSelection))
    (lexical raw vectorInterface naturalSelection)
    (NativeNaturalPredicateReading.AnnotatedConversion.closedAssumptions (natural raw vectorInterface naturalSelection))
    (closedAssumptions raw vectorInterface naturalSelection) where
  lexical := natural_lexical raw vectorInterface naturalSelection
  hypotheses := HOL.ProofSyntax.OccurrenceMap.appendRight _ _

def vectorExtension : AnnotatedPredicateReading.ReadingExtension (vector raw vectorInterface).lexicalReading
    (lexical raw vectorInterface naturalSelection)
    (NativeVectorComputationRows.EncodedConstructor.closedAssumptions raw vectorInterface) (closedAssumptions raw vectorInterface naturalSelection) where
  lexical := by
    constructor
    · intro name type code found
      exact (vector_lexical raw vectorInterface naturalSelection).constants _ _ _
        ((NativeVectorComputationRows.GuardedFamily.extends_computation (vector raw vectorInterface)).constants _ _ _ found)
    · intro head type code found
      cases found
    · intro operator result code found
      cases found
  hypotheses := HOL.ProofSyntax.OccurrenceMap.appendLeft _ _

variable [DecidableEq Base] (profile : Programs.ComputationProfiles.Selection)

def naturalTemplate (row : NativeNaturalPredicateReading.AnnotatedConversion.Row) :=
  (naturalExtension raw vectorInterface naturalSelection).template
    (NativeNaturalPredicateReading.AnnotatedConversion.EqualityCode.RootTable.template (natural raw vectorInterface naturalSelection) profile row)

def vectorTemplate (row : NativeVectorComputationRows.Row) :=
  (vectorExtension raw vectorInterface naturalSelection).template (NativeVectorComputationRows.EncodedConstructor.template raw vectorInterface profile row)

omit [DecidableEq Base] in
theorem vectorTemplate_free (row : NativeVectorComputationRows.Row) :
    (vectorTemplate raw vectorInterface naturalSelection profile row).proof.FunctionExtensionalityFree := by
  have oldFree : (NativeVectorComputationRows.EncodedConstructor.template raw vectorInterface profile row).proof.FunctionExtensionalityFree := by
    apply NativeVectorComputationRows.EncodedConstructor.entries_free raw vectorInterface profile row.address
      ⟨NativeVectorComputationRows.EncodedConstructor.template raw vectorInterface profile row, by cases row <;> rfl⟩
    cases row <;> rfl
  exact (vectorExtension raw vectorInterface naturalSelection).template_free _ oldFree

def entries : AnnotatedPredicateReading.Roots.Table (lexical raw vectorInterface naturalSelection)
    (closedAssumptions raw vectorInterface naturalSelection) (Programs.Annotated.church profile).constantType Checking.table :=
  fun address => ((naturalExtension raw vectorInterface naturalSelection).entries
    (NativeNaturalPredicateReading.AnnotatedConversion.EqualityCode.RootTable.entries
      (natural raw vectorInterface naturalSelection) profile) address).orElse (fun _ =>
    (vectorExtension raw vectorInterface naturalSelection).entries
      (NativeVectorComputationRows.EncodedConstructor.entries raw vectorInterface profile) address)

omit [DecidableEq Base] in
theorem entries_present (address : Fin Checking.table.length) :
    (entries raw vectorInterface naturalSelection profile address).isSome = true := by
  fin_cases address <;> rfl

omit [DecidableEq Base] in
theorem family_tables_disjoint (address : Fin Checking.table.length) :
    (NativeNaturalPredicateReading.AnnotatedConversion.EqualityCode.RootTable.entries
      (natural raw vectorInterface naturalSelection) profile address).isNone = true ∨
    (NativeVectorComputationRows.EncodedConstructor.entries raw vectorInterface profile address).isNone = true := by
  fin_cases address
  · exact Or.inr rfl
  · exact Or.inr rfl
  · exact Or.inl rfl
  · exact Or.inl rfl

omit [DecidableEq Base] in
theorem entries_free (address : Fin Checking.table.length) (row)
    (known : entries raw vectorInterface naturalSelection profile address = some row) :
    row.template.proof.FunctionExtensionalityFree := by
  unfold entries at known
  cases found : (naturalExtension raw vectorInterface naturalSelection).entries
      (NativeNaturalPredicateReading.AnnotatedConversion.EqualityCode.RootTable.entries
        (natural raw vectorInterface naturalSelection) profile) address with
  | none =>
      rw [found] at known
      exact (vectorExtension raw vectorInterface naturalSelection).entries_free _
        (NativeVectorComputationRows.EncodedConstructor.entries_free raw vectorInterface profile) address row known
  | some prior =>
      rw [found] at known
      cases known
      exact (naturalExtension raw vectorInterface naturalSelection).entries_free _
        (NativeNaturalPredicateReading.AnnotatedConversion.EqualityCode.RootTable.entries_free
          (natural raw vectorInterface naturalSelection) profile) address row found

#print axioms natural_lexical
#print axioms vector_lexical
#print axioms guarded_natural_lexical
#print axioms entries_present
#print axioms entries_free
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalVectorProfile
