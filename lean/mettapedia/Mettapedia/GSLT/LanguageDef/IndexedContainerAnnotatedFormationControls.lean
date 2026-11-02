import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.IndexedContainerGuardedContexts
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorAllAnnotatedSyntax
import Mettapedia.GSLT.LanguageDef.IndexedContainerAnnotatedErasure
import Mettapedia.GSLT.LanguageDef.IndexedPositiveContainerAnnotatedMethodControls
import Mettapedia.GSLT.LanguageDef.IndexedContainerPositionTermsControls
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeVectorOpenPrefixControls

/-!
# Generated source formation and exact registered Vector controls

The actual mixed source has five fields and three induction arguments.
Its parametric declaration context has independently scoped answer and family
types. Constructor formation and its complete guarded field context are
generated from primitive source contracts. Erasure compares the original
closed-name constructor/method interfaces independently. Method formation and
complete case realization remain separate obligations.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.IndexedContainerAnnotatedFormationControls

open Mettapedia.Logic
open Mettapedia.TypeTheory
open IndexedPolynomial.Description IndexedPositiveContainer
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Presentation TypedEquality.Annotated AnnotatedPredicateReading
open NativeNaturalVectorFamilies
local infixr:60 " ⇒ " => HOL.Ty.arr

namespace Ann
export IndexedContainerAnnotated (TermEnvironment Indexing RegistrySyntax TypeSyntax)
end Ann

abbrev I := VectorControl.interface
abbrev registry := VectorControl.registry
abbrev code := IndexedPositiveContainerGuestControls.Vectors.Mixed.code
abbrev indexing : Ann.Indexing I Tower.Head := .unindexed (inferInstance : Subsingleton Unit)

def lengthTerm : {context : List I.SortCode} → {n : Nat} →
    VectorControl.LengthExpr context → Ann.TermEnvironment I Tower.Head n context → CTm Tower.Head n
  | _, _, .here, environment => environment.1
  | _, _, .there expression, environment => lengthTerm expression environment.2

theorem lengthTerm_substitute {context : List I.SortCode} {n m : Nat}
    (expression : VectorControl.LengthExpr context) (environment : Ann.TermEnvironment I Tower.Head n context)
    (images : CSub Tower.Head n m) :
    (lengthTerm expression environment).subst images =
      lengthTerm expression (IndexedContainerAnnotated.mapEnvironment (CTm.subst images) environment) := by
  induction expression with
  | here => rfl
  | there _ previous => exact previous environment.2

def containers : Ann.RegistrySyntax I registry Tower.Head where
  fieldType := by
    intro context n name entry registered output environment element
    obtain rfl := IndexedPositiveContainerGuestControls.Vectors.registered_entry registered
    exact NativeVectorAll.Annotated.vector element (lengthTerm output environment)
  bundleType := by
    intro context n name entry registered output environment element predicate field
    obtain rfl := IndexedPositiveContainerGuestControls.Vectors.registered_entry registered
    exact NativeVectorAll.Annotated.allType element predicate (lengthTerm output environment) field
  fieldType_substitute := by
    intro context n m name entry registered output environment element images
    obtain rfl := IndexedPositiveContainerGuestControls.Vectors.registered_entry registered
    rw [NativeVectorAll.Annotated.substitute_vector, lengthTerm_substitute]
  bundleType_substitute := by
    intro context n m name entry registered output environment element predicate field images
    obtain rfl := IndexedPositiveContainerGuestControls.Vectors.registered_entry registered
    rw [NativeVectorAll.Annotated.substitute_allType, lengthTerm_substitute]

namespace Formation

abbrev Base := NativeVectorOpenPrefix.BaseSort
abbrev Const := NativeVectorOpenPrefix.Const
def operations := NativeVectorOpenPrefix.operations
def profile := NativeVectorOpenPrefix.profile
def theory := Programs.Annotated.church profile
def lex := NativeVectorOpenPrefix.lex
def level : Tower.Head := .sort (.param 0)
abbrev parameterCarrier := operations.elementPredicate
abbrev baseCarriers : HOL.Ctx Base := [parameterCarrier, parameterCarrier]

def baseContext : GuardedContext theory lex baseCarriers where
  source := .snoc (.snoc .nil Programs.Annotated.Append.elementSort) Programs.Annotated.Append.elementSort
  telescope := .snoc (.snoc .nil (HOL.PredicateProducts.full parameterCarrier)) (HOL.PredicateProducts.full parameterCarrier)
  formed := .snoc (.snoc .nil ⟨.sort (.succ (.param 0)), .sort _, Programs.Annotated.Append.elementSort_typed profile⟩)
    ⟨.sort (.succ (.param 0)), .sort _, Programs.Annotated.Append.elementSort_typed profile⟩
  reading := .snoc (.snoc .nil
    (Reads.head (lex := lex) (Γ := []) (head := .sort (.param 0))
      (closed := (HOL.PredicateProducts.full parameterCarrier : HOL.ClosedTerm Const _)) (by decide +kernel)))
    (Reads.head (lex := lex) (Γ := [parameterCarrier]) (head := .sort (.param 0))
      (closed := (HOL.PredicateProducts.full parameterCarrier : HOL.ClosedTerm Const _)) (by decide +kernel))

def types : Ann.TypeSyntax I Tower.Head 2 where
  dataType | .length => .const natName | .payload => .var 1
  family := .var 0
  constructor name := .const (.str PositiveInductiveVectorTreeGuest.treeName name)

theorem length_typed {n : Nat} {target : CCtx Tower.Head n} {context : List I.SortCode}
    {environment : Ann.TermEnvironment I Tower.Head n context} {dataTypes : I.SortCode → CTm Tower.Head n}
    (typed : IndexedContainerAnnotated.EnvironmentTyped (P := theory) target dataTypes environment)
    (expression : VectorControl.LengthExpr context) :
    CTyped theory target (lengthTerm expression environment) (dataTypes .length) := by
  induction expression with
  | here => exact typed.1
  | there _ previous => exact previous typed.2

theorem primitives : IndexedContainerAnnotated.ConstructorPrimitives (P := theory) baseContext.source types indexing containers
    PUnit.unit level (fun _ => True) where
  isUniverse := .sort _
  data sort := by
    cases sort with
    | length => exact ⟨.sort Tower.zero, .sort _, Programs.Annotated.Functions.natural_typed profile⟩
    | payload => exact ⟨level, .sort _, CDerivable.var (P := theory) (Γ := baseContext.source) 1⟩
  family := by
    change CTyped theory baseContext.source (.var 0) (.head level)
    exact .var 0
  indices := True.intro
  container := by
    intro n target images morphism context name entry registered output environment typed element elementTyped
    obtain rfl := IndexedPositiveContainerGuestControls.Vectors.registered_entry registered
    have length := length_typed typed output
    exact ⟨level, .sort _, Programs.Annotated.Append.vector_typed profile elementTyped length⟩

theorem indices_admitted {parameters : Nat} {context : List I.SortCode} (description : Code I registry parameters context) :
    IndexedContainerAnnotated.IndicesAdmitted (fun _ => True) description := by
  induction description with
  | result => trivial
  | data _ _ previous => exact previous
  | recursive _ _ previous => exact ⟨True.intro, previous⟩
  | nested _ _ _ _ _ _ previous => exact ⟨True.intro, previous⟩

def identity : CSub Tower.Head 2 baseCarriers.length := CTm.ids
theorem identity_typed : CSubstMor theory baseContext.source baseContext.source identity :=
  (GuardedSubstitution.identity [] baseContext).typed

def carriers : IndexedContainerAnnotated.FieldCarriers I registry Base where
  data | .length => operations.number | .payload => operations.element
  recursive := operations.element
  nested _ _ _ := operations.vector

def generated := IndexedContainerAnnotated.guardedContext? (Programs.Annotated.levelModel profile)
  carriers primitives code (indices_admitted code) baseContext identity identity_typed PUnit.unit True.intro

theorem generated_accepted : generated.isSome = true := by decide +kernel
def context := generated.get generated_accepted

theorem generated_source_formed : CCtxFormed theory context.source := context.formed

theorem actual_five_fields : IndexedContainerAnnotated.fieldCount code = 5 := by decide +kernel

def expected : CCtx Tower.Head 7 :=
  .snoc (.snoc (.snoc (.snoc (.snoc baseContext.source (.const natName)) (.var 1)) (.var 3))
    (Programs.Annotated.Append.vector (.var 3) (.var 2))) (.var 4)

theorem source_exact : context.source = expected := by decide +kernel

def wrongCarriers : IndexedContainerAnnotated.FieldCarriers I registry Base :=
  {carriers with recursive := operations.vector}
def wrong := IndexedContainerAnnotated.guardedContext? (Programs.Annotated.levelModel profile)
  wrongCarriers primitives code (indices_admitted code) baseContext identity identity_typed PUnit.unit True.intro

theorem incompatible_carrier_refused : wrong.isNone = true := by decide +kernel

def rawRen : Ren 7 8 := ![3, 0, 2, 3, 1, 7, 7]

def codeRen : HOL.Rename Base (carriers.context code baseCarriers) NativeVectorOpenPrefix.Conversion.parameters
  | _, .vz => .vs (.vs (.vs .vz))
  | _, .vs .vz => .vz
  | _, .vs (.vs .vz) => .vs (.vs .vz)
  | _, .vs (.vs (.vs .vz)) => .vs (.vs (.vs .vz))
  | _, .vs (.vs (.vs (.vs .vz))) => .vs .vz
  | _, .vs (.vs (.vs (.vs (.vs .vz)))) => .vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))
  | _, .vs (.vs (.vs (.vs (.vs (.vs .vz))))) => .vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))

theorem ren_compatible : ∀ {type} (position : HOL.Var (carriers.context code baseCarriers) type),
    (codeRen position).toFin = rawRen position.toFin := by
  intro type position
  cases position with
  | vz => rfl
  | vs position => cases position with
    | vz => rfl
    | vs position => cases position with
      | vz => rfl
      | vs position => cases position with
        | vz => rfl
        | vs position => cases position with
          | vz => rfl
          | vs position => cases position with
            | vz => rfl
            | vs position => cases position with
              | vz => rfl
              | vs impossible => nomatch impossible

theorem source_placement : CCtxRen context.source NativeVectorOpenPrefix.context.source rawRen := by
  rw [source_exact]
  intro position
  fin_cases position <;> decide +kernel

def placement := GuardedSubstitution.ofRenaming NativeVectorOpenPrefix.roots context NativeVectorOpenPrefix.context
  rawRen codeRen ren_compatible source_placement

theorem guards_realizable (long : Bool) : context.telescope.Satisfies NativeVectorOpenPrefix.Controls.model
    (HOL.Soundness.substVal NativeVectorOpenPrefix.Controls.model (HOL.Subst.ofRename codeRen)
      (NativeVectorOpenPrefix.Controls.values long)) :=
  HOL.PredicateContexts.Telescope.Realizes.satisfies_subst NativeVectorOpenPrefix.Controls.model
    (NativeVectorOpenPrefix.Controls.model.functionsRespectEqv_of_fullDomains (HOL.HenkinModel.fullDomains_standard _ _))
    placement.guards (NativeVectorOpenPrefix.Controls.values long) (fun _ => trivial) (NativeVectorOpenPrefix.Controls.background_holds long)

theorem expected_formed : CCtxFormed theory expected :=
  .snoc (.snoc (.snoc (.snoc (.snoc baseContext.formed
    ⟨.sort Tower.zero, .sort _, Programs.Annotated.Functions.natural_typed profile⟩)
    ⟨level, .sort _, .var 1⟩) ⟨level, .sort _, .var 3⟩)
    ⟨level, .sort _, Programs.Annotated.Append.vector_typed profile (.var 3) (.var 2)⟩)
    ⟨level, .sort _, .var 4⟩

def contextCertificate : Programs.Annotated.JudgmentReplay.ContextCertificate profile 7 := by
  annotated_context_certificate 16000 expected_formed

theorem context_checked : Programs.Annotated.JudgmentReplay.checkContext profile context.source contextCertificate = true := by
  decide +kernel

end Formation

namespace Indexed

open Formation (Base Const operations profile theory lex level parameterCarrier)
abbrev I := IndexedContainerPositionTermsControls.interface
def registry : Registry I := ⟨fun _ => none⟩

def indices : IndexedContainerAnnotated.IndexSyntax I Tower.Head where
  term := lengthTerm
  substitute := by
    intro context n m expression environment images
    exact lengthTerm_substitute expression environment images
def indexing : Ann.Indexing I Tower.Head := .indexed indices

def containers : Ann.RegistrySyntax I registry Tower.Head where
  fieldType := by intro context n name entry absent; cases absent
  bundleType := by intro context n name entry absent; cases absent
  fieldType_substitute := by intro context n m name entry absent; cases absent
  bundleType_substitute := by intro context n m name entry absent; cases absent

abbrev baseCarriers : HOL.Ctx Base := [operations.number ⇒ parameterCarrier, parameterCarrier]

def familyKind : CTm Tower.Head 1 := .pi (.const natName) Programs.Annotated.Append.elementSort
def familyPredicate : HOL.Term Const [parameterCarrier] ((operations.number ⇒ parameterCarrier) ⇒ .prop) :=
  HOL.PredicateProducts.pi (HOL.PredicateProducts.full operations.number)
    (HOL.PredicateProducts.full parameterCarrier)

theorem familyKind_read : Reads lex (Γ := [parameterCarrier]) familyKind familyPredicate :=
  .product (NativeVectorValueRealizers.naturalRead operations NativeVectorOpenPrefix.compatible)
    (Reads.head (lex := lex) (Γ := [operations.number, parameterCarrier]) (head := .sort (.param 0))
      (closed := (HOL.PredicateProducts.full parameterCarrier : HOL.ClosedTerm Const _)) (by decide +kernel))

def baseContext : GuardedContext theory lex baseCarriers where
  source := .snoc (.snoc .nil Programs.Annotated.Append.elementSort) familyKind
  telescope := .snoc (.snoc .nil (HOL.PredicateProducts.full parameterCarrier)) familyPredicate
  formed := .snoc (.snoc .nil ⟨.sort (.succ (.param 0)), .sort _, Programs.Annotated.Append.elementSort_typed profile⟩)
    (CIsType.pi (Programs.Annotated.levelModel profile)
      ⟨.sort Tower.zero, .sort _, Programs.Annotated.Functions.natural_typed profile⟩
      ⟨.sort (.succ (.param 0)), .sort _, Programs.Annotated.Append.elementSort_typed profile⟩)
  reading := .snoc (.snoc .nil
    (Reads.head (lex := lex) (Γ := []) (head := .sort (.param 0))
      (closed := (HOL.PredicateProducts.full parameterCarrier : HOL.ClosedTerm Const _)) (by decide +kernel))) familyKind_read

def types : Ann.TypeSyntax I Tower.Head 2 where
  dataType | .length => .const natName | .payload => .var 1
  family := .var 0
  constructor name := .const (.str `IndexedFamily name)

theorem primitives : IndexedContainerAnnotated.ConstructorPrimitives (P := theory) baseContext.source types indexing containers
    (.const natName) level (fun _ => True) where
  isUniverse := .sort _
  data sort := by
    cases sort with
    | length => exact ⟨.sort Tower.zero, .sort _, Programs.Annotated.Functions.natural_typed profile⟩
    | payload => exact ⟨level, .sort _, CDerivable.var (P := theory) (Γ := baseContext.source) 1⟩
  family := by
    change CTyped theory baseContext.source (.var 0) (.pi (.const natName) (.head level))
    exact .var 0
  indices := by
    intro n target images morphism context expression accepted environment typed
    exact Formation.length_typed typed expression
  container := by intro n target images morphism context name entry absent; cases absent

def code : Code I registry 0 [] := .data .length (.recursive .here (.result .here))
theorem accepted : IndexedContainerAnnotated.IndicesAdmitted (fun _ => True) code := ⟨True.intro, True.intro⟩

def identity : CSub Tower.Head 2 baseCarriers.length := CTm.ids
theorem identity_typed : CSubstMor theory baseContext.source baseContext.source identity :=
  (GuardedSubstitution.identity [] baseContext).typed

def carriers : IndexedContainerAnnotated.FieldCarriers I registry Base where
  data | .length => operations.number | .payload => operations.element
  recursive := operations.element
  nested _ _ absent := by cases absent

def generated := IndexedContainerAnnotated.guardedContext? (Programs.Annotated.levelModel profile)
  carriers primitives code accepted baseContext identity identity_typed PUnit.unit True.intro
theorem generated_accepted : generated.isSome = true := by decide +kernel
def context := generated.get generated_accepted

theorem source_exact : context.source =
    .snoc (.snoc baseContext.source (.const natName)) (.app (.var 1) (.var 0)) := by decide +kernel

theorem excluded_index_refused : ¬ IndexedContainerAnnotated.IndicesAdmitted (fun _ => False) code := by
  intro invalid
  exact invalid.1

end Indexed

namespace Erasure

open IndexedContainerAnnotatedErasure

theorem length_erases {context : List I.SortCode} {n : Nat} (expression : VectorControl.LengthExpr context)
    (environment : Ann.TermEnvironment I Tower.Head n context) :
    (lengthTerm expression environment).erase = IndexedPositiveContainerGuestControls.Vectors.lengthTerm expression
      (eraseEnvironment environment) := by
  induction expression with
  | here => rfl
  | there _ previous => exact previous environment.2

theorem indexCorrespondence : IndexingCorrespondence indexing IndexedPositiveContainerGuestControls.Vectors.indexing :=
  .unindexed _ _

theorem registryCorrespondence : RegistryCorrespondence containers IndexedPositiveContainerGuestControls.Vectors.containers where
  fieldType := by
    intro context n name entry registered output environment element
    obtain rfl := IndexedPositiveContainerGuestControls.Vectors.registered_entry registered
    simp only [containers, IndexedPositiveContainerGuestControls.Vectors.containers,
      IndexedPositiveContainerGuestControls.Vectors.registrySyntax, NativeVectorAll.Annotated.erase_vector, length_erases]
  bundleType := by
    intro context n name entry registered output environment element predicate field
    obtain rfl := IndexedPositiveContainerGuestControls.Vectors.registered_entry registered
    simp only [containers, IndexedPositiveContainerGuestControls.Vectors.containers,
      IndexedPositiveContainerGuestControls.Vectors.registrySyntax, NativeVectorAll.Annotated.erase_allType, length_erases]

def originalTypes {n : Nat} : Ann.TypeSyntax I Tower.Head n where
  dataType | .length => .const natName | .payload => .const PositiveInductiveVectorTreeGuest.answerName
  family := .const PositiveInductiveVectorTreeGuest.treeName
  constructor name := .const (.str PositiveInductiveVectorTreeGuest.treeName name)

theorem original_types_erased {n : Nat} : eraseTypes (originalTypes (n := n)) = IndexedPositiveContainerGuestControls.Vectors.types := by
  unfold eraseTypes originalTypes IndexedPositiveContainerGuestControls.Vectors.types
  congr 1
  funext sort
  cases sort <;> rfl

def constructor : CTm Tower.Head 0 := IndexedContainerAnnotated.constructorType indexing containers code originalTypes PUnit.unit

theorem constructor_erased : constructor.erase = IndexedPositiveContainerGuestControls.Vectors.Mixed.expectedConstructorType := by
  have exactType := constructorType_erase indexCorrespondence registryCorrespondence code (originalTypes (n := 0)) PUnit.unit
  rw [original_types_erased] at exactType
  exact exactType.trans IndexedPositiveContainerGuestControls.Vectors.Mixed.constructor_exact

def method : CTm Tower.Head 7 := IndexedContainerAnnotated.methodBody indexing containers code originalTypes PUnit.unit (.var 6) (.var 5) []

theorem method_erased : method.erase = IndexedPositiveContainerAnnotatedMethodControls.rawMethod := by
  have exactType := methodBody_erase indexCorrespondence registryCorrespondence code (originalTypes (n := 7)) PUnit.unit (.var 6) (.var 5) []
  rw [original_types_erased] at exactType
  exact exactType

theorem whole_original_telescope : ∃ residual,
    IndexedPositiveContainerAnnotatedMethods.instantiateFields code IndexedPositiveContainerAnnotatedMethodControls.fields method = some residual ∧
    residual.erase = IndexedPositiveContainerGuestTypes.hypotheses
      IndexedPositiveContainerAnnotatedMethodControls.expectedHypotheses IndexedPositiveContainerAnnotatedMethodControls.expectedConclusion := by
  obtain ⟨residual, applied, exactType⟩ := IndexedPositiveContainerAnnotatedMethods.methodBody_specialize
    IndexedPositiveContainerGuestControls.Vectors.indexing IndexedPositiveContainerGuestControls.Vectors.containers code
    IndexedPositiveContainerGuestControls.Vectors.types PUnit.unit (.var 6) (.var 5) []
    IndexedPositiveContainerAnnotatedMethodControls.fields method method_erased
  have predicates := IndexedPositiveContainerAnnotatedMethodControls.three_complete_hypotheses
  dsimp only [IndexedPositiveContainerAnnotatedMethodControls.motive] at predicates
  have conclusion := IndexedPositiveContainerAnnotatedMethodControls.conclusion_exact
  dsimp only [IndexedPositiveContainerAnnotatedMethodControls.motive,
    IndexedPositiveContainerAnnotatedMethodControls.constructor] at conclusion
  exact ⟨residual, applied, by simpa only [List.nil_append, predicates, conclusion] using exactType⟩

end Erasure

#print axioms Formation.generated_source_formed
#print axioms Formation.incompatible_carrier_refused
#print axioms Formation.guards_realizable
#print axioms Indexed.generated_accepted
#print axioms Erasure.whole_original_telescope

end Mettapedia.GSLT.LanguageDef.IndexedContainerAnnotatedFormationControls
