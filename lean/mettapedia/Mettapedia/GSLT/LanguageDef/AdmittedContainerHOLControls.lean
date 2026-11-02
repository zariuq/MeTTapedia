import Mettapedia.GSLT.LanguageDef.AdmittedContainerHOL
import Mettapedia.GSLT.LanguageDef.IndexedContainerParameterGuardControls
import Mettapedia.GSLT.LanguageDef.IndexedInductiveHOLTermControls

/-!
# Retained constructor proof controls

Primitive field evidence is constructed with beta, reflexivity and Boolean
introduction. The shared producer supplies the complete field and result
proofs. The admitted-vector controls retain the original declaration source.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.GSLT.LanguageDef.AdmittedContainerHOLControls
open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.IndexedContainerPositionTerms
open Mettapedia.TypeTheory.IndexedPolynomial.Description
open Mettapedia.TypeTheory

namespace Parameter
open IndexedContainerParameterGuardControls
open IndexedContainerPositionTermsControls (number Symbol zero successor)

def low : ClosedTerm Symbol number := two
def high : ClosedTerm Symbol number := .app successor low
def arguments : FiniteConstructorEncoding.Arguments Symbol [] (reading.fields pairCode) :=
  (low, high, PUnit.unit)

def firstProof : ProofSyntax Symbol [] (.app
    (Mettapedia.Logic.HOL.subst (reading.parameterSubst (context := []) closedParameters) (guards.value ())) low) := by
  apply ProofSyntax.impE (.eqPropER (.beta low _))
  exact .orIL (.eqRefl low)

def secondProof : ProofSyntax Symbol [] (.app
    (Mettapedia.Logic.HOL.subst (reading.parameterSubst (context := [()]) (Subst.cons low closedParameters))
      (guards.value ())) high) := by
  apply ProofSyntax.impE (.eqPropER (.beta high _))
  exact .orIR (.eqRefl high)

def evidence : guards.Evidence [] pairCode closedParameters arguments :=
  ⟨firstProof, secondProof, PUnit.unit⟩

theorem evidence_free : guards.EvidenceFree [] pairCode closedParameters arguments evidence := by
  change firstProof.FunctionExtensionalityFree ∧ secondProof.FunctionExtensionalityFree ∧ True
  simp only [firstProof, secondProof, ProofSyntax.FunctionExtensionalityFree, and_self]

def fieldProof := guards.introduce pairCode closedParameters arguments evidence
theorem fieldProof_free : fieldProof.FunctionExtensionalityFree := guards.introduce_free _ _ _ _ evidence_free

def resultProof := reading.resultProof (assumptions := []) pairCode closedParameters arguments
theorem resultProof_free : resultProof.FunctionExtensionalityFree := reading.resultProof_free _ _ _

def codes : List (IndexedPositiveContainer.Code interface registry 0 []) := [pairCode]
def numeral : Nat → ClosedTerm Symbol number
  | 0 => zero
  | n + 1 => .app successor (numeral n)
def occurrence : Fin ((codes.map reading.fields).length) := ⟨0, by decide⟩

def payloadProof := guards.payloadProof codes closedParameters numeral occurrence arguments evidence
def shapeProof := guards.shapeProof codes closedParameters numeral occurrence arguments evidence
def indexedProof := guards.resultGuardProof codes closedParameters numeral occurrence arguments evidence

theorem payloadProof_free : payloadProof.FunctionExtensionalityFree := guards.payloadProof_free _ _ _ _ _ _ evidence_free
theorem shapeProof_free : shapeProof.FunctionExtensionalityFree := guards.shapeProof_free _ _ _ _ _ _ evidence_free
theorem indexedProof_free : indexedProof.FunctionExtensionalityFree := guards.resultGuardProof_free _ _ _ _ _ _ evidence_free

theorem indexed_source : reading.indexTerm pairCode closedParameters arguments = (.top : ClosedFormula Symbol) := rfl

#print axioms fieldProof_free
#print axioms indexedProof_free
end Parameter

namespace AdmittedVector
noncomputable section
open IndexedInductiveNatVec
open IndexedInductiveHOLTerms.Controls (SortCode Symbol number element arithmetic)
open PositiveInductiveBlockBridge

noncomputable def block := Direct.admitted 0 (Vectors.admitted Bool)
theorem registered : block.WellRegistered := Direct.admitted_registered 0 (Vectors.admitted Bool)
noncomputable abbrev registry := IndexedPositiveContainer.Unindexed.liftRegistry Direct.registry (Vectors.interface Bool)

def reading : Reading (Vectors.interface Bool) registry Symbol where
  indices := arithmetic.reading Bool
  number := number
  one := .app (.const .successor) (.const .zero)
  shapeType _ _ found := by
    simp only [registry, IndexedPositiveContainer.Unindexed.liftRegistry, Direct.registry, Option.map_none] at found
    cases found
  count _ _ found _ := by
    simp only [registry, IndexedPositiveContainer.Unindexed.liftRegistry, Direct.registry, Option.map_none] at found
    cases found

def guards : FieldGuards reading where
  value _ := .lam .top
  shape _ _ found _ := by
    simp only [registry, IndexedPositiveContainer.Unindexed.liftRegistry, Direct.registry, Option.map_none] at found
    cases found

def nilCode : IndexedPositiveContainer.Code (Vectors.interface Bool) registry 0 [] := .result .zero
def consCode : IndexedPositiveContainer.Code (Vectors.interface Bool) registry 0 [] :=
  .data .length (.data .payload (.recursive (.variable (.there .here))
    (.result (.successor (.variable (.there .here))))))
def codes := [nilCode, consCode]
theorem codes_admitted : codes = AdmittedContainerHOL.codes block registered := rfl
def nilOccurrence : Fin ((codes.map reading.fields).length) := ⟨0, by decide⟩
def consOccurrence : Fin ((codes.map reading.fields).length) := ⟨1, by decide⟩
theorem nil_selected : codeAt reading codes nilOccurrence = nilCode := rfl
theorem cons_selected : codeAt reading codes consOccurrence = consCode := rfl

theorem names : block.constructors.map (·.name) = ["Nil", "Cons"] := rfl
theorem source_admitted : IndexedInductive.admit? (Vectors.source Bool) = some (Vectors.admitted Bool) :=
  Vectors.source_admitted Bool
theorem nil_original : nilCode = .result (.zero : Vectors.IndexExpr []) := rfl
theorem cons_original : consCode =
    .data .length (.data .payload (.recursive (.variable (.there .here))
      (.result (.successor (.variable (.there .here)))))) := rfl

abbrev context : Ctx SortCode := [element, number]
def substitution : Subst Symbol [] context := fun impossible => nomatch impossible
def arguments : FiniteConstructorEncoding.Arguments Symbol context (reading.fields consCode) :=
  (.var (.vs .vz), .var .vz, PUnit.unit)
def evidence : guards.Evidence [] consCode substitution arguments :=
  ⟨.impE (.eqPropER (.beta _ _)) .topI,
   .impE (.eqPropER (.beta _ _)) .topI, PUnit.unit⟩
theorem evidence_free : guards.EvidenceFree [] consCode substitution arguments evidence := by
  change _ ∧ _ ∧ True
  simp only [evidence, ProofSyntax.FunctionExtensionalityFree, and_self]

def numeral : Nat → Term Symbol context number
  | 0 => .const .zero
  | n + 1 => .app (.const .successor) (numeral n)
def payloadProof := guards.payloadProof codes substitution
  numeral consOccurrence arguments evidence
def indexedProof := guards.resultGuardProof codes substitution
  numeral consOccurrence arguments evidence
def computationProof := reading.resultProof (assumptions := []) consCode substitution arguments

theorem payloadProof_free : payloadProof.FunctionExtensionalityFree :=
  guards.payloadProof_free _ _ _ _ _ _ evidence_free
theorem indexedProof_free : indexedProof.FunctionExtensionalityFree :=
  guards.resultGuardProof_free _ _ _ _ _ _ evidence_free
theorem computationProof_free : computationProof.FunctionExtensionalityFree :=
  reading.resultProof_free _ _ _
theorem result_is_successor : reading.indexTerm consCode substitution arguments =
    (.app (.const .successor) (.var (.vs .vz)) : Term Symbol context number) := by
  simp [Reading.indexTerm, cons_original, reading, arithmetic, IndexedInductiveHOLTerms.Arithmetic.reading,
    IndexedInductiveHOLTerms.Arithmetic.term, IndexedInductiveHOLTerms.Arithmetic.reference,
    IndexedInductiveHOLTerms.Arithmetic.sort, Subst.cons, arguments, Mettapedia.Logic.HOL.subst]
theorem nil_result_is_zero : reading.indexTerm nilCode substitution PUnit.unit =
    (.const .zero : Term Symbol context number) := by
  simp [Reading.indexTerm, nil_original, reading, arithmetic, IndexedInductiveHOLTerms.Arithmetic.reading,
    IndexedInductiveHOLTerms.Arithmetic.term, Mettapedia.Logic.HOL.subst]
theorem constructor_occurrences_distinct : nilOccurrence ≠ consOccurrence := by decide
theorem cons_has_one_child : (reading.compile consCode substitution).length = 1 := rfl

#print axioms indexedProof_free
#print axioms result_is_successor
end
end AdmittedVector
end Mettapedia.GSLT.LanguageDef.AdmittedContainerHOLControls
