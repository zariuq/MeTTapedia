import Mettapedia.Languages.HOLLight.AdmittedConstructorCompilation
import Mettapedia.GSLT.LanguageDef.IndexedInductiveHOLRealization
import Mettapedia.GSLT.LanguageDef.ArithmeticReadingInterpretation
import Mettapedia.Logic.HOL.CurriedPredicateInterpretation

/-!
# Agreement of interpreted and generated admitted Vector programs

The native programs are generated independently from the admitted constructor
inventory. Their agreement with the original retained proof is checked at
arbitrary closed arithmetic operations, including compound numeral wrappers.
This is the admitted Bool Vector panel, not a claim about all datatype blocks.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Languages.HOLLight.AdmittedConstructorCoherence
open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open Mettapedia.GSLT.LanguageDef
open HOL HOL.IndexedContainerPositionTerms
open AdmittedContainerHOLControls
noncomputable section
variable (operations : AdmittedConstructorCompilation.Arithmetic)

abbrev context : Ctx AtomicTy := [operations.element, operations.number]
def reading := IndexedInductiveHOLRealization.reading operations Bool

def guards : FieldGuards (reading operations) where
  value _ := .lam .top
  shape _ _ found _ := by
    simp only [IndexedInductiveHOLRealization.registry,
      Mettapedia.TypeTheory.IndexedPositiveContainer.Unindexed.liftRegistry,
      PositiveInductiveBlockBridge.Direct.registry, Option.map_none] at found
    cases found

def arguments : FiniteConstructorEncoding.Arguments Symbol (context operations)
    ((reading operations).fields AdmittedVector.consCode) :=
  (.var (.vs .vz), .var .vz, PUnit.unit)
def substitution : Subst Symbol [] (context operations) := fun impossible => nomatch impossible

def numeral : Nat → Term Symbol (context operations) operations.number
  | 0 => weakenCtx _ operations.zero
  | n + 1 => .app (weakenCtx _ operations.successor) (numeral n)
def occurrence : Fin ((AdmittedVector.codes.map (reading operations).fields).length) :=
  ⟨1, by change 1 < 2; decide⟩
def payload := payloadTerm (reading operations) AdmittedVector.codes (occurrence operations) (arguments operations)
def index := (reading operations).indexTerm AdmittedVector.consCode (substitution operations) (arguments operations)
def inventory := (guards operations).constructors AdmittedVector.codes (substitution operations) (numeral operations)

theorem payload_agrees :
    (AdmittedConstructorCompilation.interpretation operations).term
      (payloadTerm AdmittedVector.reading AdmittedVector.codes AdmittedVector.consOccurrence AdmittedVector.arguments) =
      payload operations := rfl

theorem index_agrees :
    (AdmittedConstructorCompilation.interpretation operations).term
      (AdmittedVector.reading.indexTerm AdmittedVector.consCode AdmittedVector.substitution AdmittedVector.arguments) =
      index operations := by
  apply ArithmeticReadingInterpretation.term_agrees operations
    (context := [.payload, .length]) (Γ := AdmittedVector.context)
    (sourceTheta := Subst.cons (.var .vz) (Subst.cons (.var (.vs .vz)) AdmittedVector.substitution))
    (targetTheta := Subst.cons (.var .vz) (Subst.cons (.var (.vs .vz)) (substitution operations)))
    (expression := .successor (.variable (.there .here)))
  intro reference
  cases reference with
  | there prior =>
      cases prior with
      | here => rfl
      | there impossible => cases impossible

theorem allowed_agrees (selected : Fin (AdmittedVector.codes.map AdmittedVector.reading.fields).length) :
    HEq ((AdmittedConstructorCompilation.interpretation operations).term
      ((AdmittedVector.guards.constructors AdmittedVector.codes AdmittedVector.substitution
        AdmittedVector.numeral).allowed selected))
      ((inventory operations).allowed ⟨selected.val, by simpa only [inventory, FieldGuards.constructors,
        List.length_map] using selected.isLt⟩) := by
  fin_cases selected <;> rfl

theorem fields_agree (selected : Fin (AdmittedVector.codes.map AdmittedVector.reading.fields).length) :
    (((AdmittedVector.codes.map AdmittedVector.reading.fields).get selected).map
      (Ty.substitute (AdmittedConstructorCompilation.interpretation operations).types)) =
      (inventory operations).fields.get ⟨selected.val, by
        simpa only [inventory, FieldGuards.constructors, List.length_map] using selected.isLt⟩ := by
  fin_cases selected <;> rfl

theorem results_agree (selected : Fin (AdmittedVector.codes.map AdmittedVector.reading.fields).length) :
    HEq ((AdmittedConstructorCompilation.interpretation operations).term
      ((AdmittedVector.guards.constructors AdmittedVector.codes AdmittedVector.substitution
        AdmittedVector.numeral).result selected))
      ((inventory operations).result ⟨selected.val, by simpa only [inventory, FieldGuards.constructors,
        List.length_map] using selected.isLt⟩) := by
  fin_cases selected
  · apply heq_of_eq
    change (ArithmeticReadingInterpretation.interpretation operations).term
      (HOL.subst AdmittedVector.substitution
        (ArithmeticReadingInterpretation.sourceArithmetic.term (context := []) .zero)) =
      HOL.subst (substitution operations) (operations.term (context := []) .zero)
    apply ArithmeticReadingInterpretation.term_agrees operations (context := [])
    intro reference
    cases reference
  · apply heq_of_eq
    apply congrArg Term.lam
    apply congrArg Term.lam
    change (ArithmeticReadingInterpretation.interpretation operations).term
      (HOL.subst (Subst.lift (Subst.lift AdmittedVector.substitution))
        (ArithmeticReadingInterpretation.sourceArithmetic.term (context := [.payload, .length])
          (.successor (.variable (.there .here))))) =
      HOL.subst (Subst.lift (Subst.lift (substitution operations)))
        (operations.term (context := [.payload, .length]) (.successor (.variable (.there .here))))
    apply ArithmeticReadingInterpretation.term_agrees operations
      (context := [.payload, .length])
    intro reference
    cases reference with
    | there prior =>
        cases prior with
        | here => rfl
        | there impossible => cases impossible

theorem resultConditions_agree
    (selected : Fin (AdmittedVector.codes.map AdmittedVector.reading.fields).length) :
    HEq ((AdmittedConstructorCompilation.interpretation operations).term
      ((AdmittedVector.guards.constructors AdmittedVector.codes AdmittedVector.substitution
        AdmittedVector.numeral).resultCondition
          (AdmittedVector.reading.indexTerm AdmittedVector.consCode AdmittedVector.substitution AdmittedVector.arguments)
          selected))
      ((inventory operations).resultCondition (index operations) ⟨selected.val, by
        simpa only [inventory, FieldGuards.constructors, List.length_map] using selected.isLt⟩) := by
  have allowed := allowed_agrees operations selected
  have results := results_agree operations selected
  apply CurriedPredicates.conjoin_interpret_as _ _ _ (fields_agree operations selected)
  · exact allowed
  · have compared := CurriedPredicates.equalTo_interpret_as
      (AdmittedConstructorCompilation.interpretation operations) _ _ (fields_agree operations selected) _
      (AdmittedVector.reading.indexTerm AdmittedVector.consCode AdmittedVector.substitution AdmittedVector.arguments)
      _ results
    rw [index_agrees] at compared
    exact compared

theorem guard_agrees :
    (AdmittedConstructorCompilation.interpretation operations).term
      ((AdmittedVector.guards.constructors AdmittedVector.codes AdmittedVector.substitution AdmittedVector.numeral).resultGuard
        (payloadTerm AdmittedVector.reading AdmittedVector.codes AdmittedVector.consOccurrence AdmittedVector.arguments)
        (AdmittedVector.reading.indexTerm AdmittedVector.consCode AdmittedVector.substitution AdmittedVector.arguments)) =
      (inventory operations).resultGuard (payload operations) (index operations) := by
  apply FiniteConstructorEncoding.guard_interpret
  · exact resultConditions_agree operations
  · exact heq_of_eq (payload_agrees operations)

def indexedProof : ProofSyntax Symbol []
    ((inventory operations).resultGuard (payload operations) (index operations)) :=
  ProofSyntax.castIndices rfl (guard_agrees operations)
    ((AdmittedConstructorCompilation.interpretation operations).proof AdmittedVector.indexedProof)

theorem indexedProof_free : (indexedProof operations).FunctionExtensionalityFree := by
  unfold indexedProof
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact (AdmittedConstructorCompilation.interpretation operations).proof_free
    AdmittedVector.indexedProof AdmittedVector.indexedProof_free

theorem compiled_indexed_conclusion :
    (AdmittedConstructorCompilation.vectorIndexed operations).proof.result.sequent.concl =
      ReverseTranslation.reverseCanonical (AdmittedConstructorCompilation.names operations)
        (HOL.ImpredicativeConnectives.expand
          ((inventory operations).resultGuard (payload operations) (index operations))) := by
  have original :
      (AdmittedConstructorCompilation.vectorIndexed operations).proof.result.sequent.concl =
        ReverseTranslation.reverseCanonical (AdmittedConstructorCompilation.names operations)
          (HOL.ImpredicativeConnectives.expand
            ((AdmittedConstructorCompilation.interpretation operations).term
              ((AdmittedVector.guards.constructors AdmittedVector.codes AdmittedVector.substitution AdmittedVector.numeral).resultGuard
                (payloadTerm AdmittedVector.reading AdmittedVector.codes AdmittedVector.consOccurrence AdmittedVector.arguments)
                (AdmittedVector.reading.indexTerm AdmittedVector.consCode AdmittedVector.substitution AdmittedVector.arguments)))) :=
    stagedProof% (AdmittedConstructorCompilation.vectorIndexed operations).conclusion_exact
  exact original.trans
    (congrArg (fun formula => ReverseTranslation.reverseCanonical
      (AdmittedConstructorCompilation.names operations) (HOL.ImpredicativeConnectives.expand formula))
      (guard_agrees operations))

universe w
theorem interpreted_source_image
    (model : HenkinModel.{0,0,w} AtomicTy Symbol) (full : model.FullDomains)
    (numbers : IndexedInductiveHOLRealization.Numbers operations model)
    (elements : Bool ≃ Ty.denote.{0,w} model.Carrier operations.element)
    (values : model.Valuation (context operations)) :
    let realization := IndexedInductiveHOLRealization.realization operations model Bool numbers
      (IndexedInductiveHOLRealization.fullElements operations model Bool elements)
    (model.denote ((AdmittedConstructorCompilation.interpretation operations).term
      ((AdmittedVector.guards.constructors AdmittedVector.codes AdmittedVector.substitution AdmittedVector.numeral).resultGuard
        (payloadTerm AdmittedVector.reading AdmittedVector.codes AdmittedVector.consOccurrence AdmittedVector.arguments)
        (AdmittedVector.reading.indexTerm AdmittedVector.consCode AdmittedVector.substitution AdmittedVector.arguments))) values).down ↔
      ∃ (selected : Fin (AdmittedVector.codes.map (reading operations).fields).length)
        (sourceIndex : IndexedInductiveNatVec.Natural.Carrier)
        (sourceShape : Mettapedia.TypeTheory.IndexedPositiveContainer.Code.Shape
          (codeAt (reading operations) AdmittedVector.codes selected) PUnit.unit sourceIndex),
        realization.index sourceIndex = model.denote (index operations) values ∧
        FiniteConstructorEncoding.payloadEquivalence model _ (model.denote (payload operations) values) =
          Mettapedia.TypeTheory.FiniteConstructorEncoding.encode (Ty.denote.{0,w} model.Carrier) _
            (encodeConstructorData realization AdmittedVector.codes selected sourceShape) := by
  dsimp only
  rw [guard_agrees]
  apply (IndexedInductiveHOLRealization.images operations model Bool numbers
    (IndexedInductiveHOLRealization.fullElements operations model Bool elements)).resultGuard_exact
      AdmittedVector.codes PUnit.unit (substitution operations) (numeral operations) full values
  intro type impossible
  exact nomatch impossible

#print axioms index_agrees
#print axioms results_agree
#print axioms guard_agrees
#print axioms indexedProof_free
#print axioms compiled_indexed_conclusion
#print axioms interpreted_source_image
end
end Mettapedia.Languages.HOLLight.AdmittedConstructorCoherence
