import Mettapedia.Logic.HOL.ContextualInductionSchema
import Mettapedia.Languages.HOLLight.ParameterSchemaCompilation
import Mettapedia.Languages.HOLLight.RecursiveConstructorCompilation

/-!
# A reusable indexed-induction schema

The operations, root relation, motive and input are schematic variables.
The only hypothesis is a closed constructor method. A concrete producer
must construct that method and discharge it after specialization; this
module supplies no datatype-specific closure law.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.HOLLight.IndexedInductionSchemas

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open HOL ReverseTranslation.VariableSchema

abbrev number := RecursiveConstructorCompilation.number
abbrev payload := RecursiveConstructorCompilation.payload
abbrev space := RecursiveConstructorCompilation.space
abbrev index : HOL.Ty AtomicTy := .base (RecursiveConstructorCompilation.atomic "__schema_index")

abbrev context : Ctx AtomicTy := [index, space, space ⇒ index ⇒ .prop, space ⇒ index ⇒ .prop,
  payload ⇒ number ⇒ space ⇒ .prop, payload ⇒ number ⇒ .prop, number ⇒ payload ⇒ .prop,
  number ⇒ payload ⇒ (number ⇒ space) ⇒ space, space]

universe v
def signature {Const : HOL.Ty AtomicTy → Type v} : RecursiveSpacePredicate.Contextual Const context where
  number := number
  payload := payload
  space := space
  bottom := .var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))
  construct := .var (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))
  validShape := .var (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))
  active := .var (.vs (.vs (.vs (.vs (.vs .vz)))))
  validEdge := .var (.vs (.vs (.vs (.vs .vz))))

def root {Const : HOL.Ty AtomicTy → Type v} : HOL.Term Const context (space ⇒ index ⇒ .prop) :=
  .var (.vs (.vs (.vs .vz)))
def property {Const : HOL.Ty AtomicTy → Type v} : HOL.Term Const context (space ⇒ index ⇒ .prop) :=
  .var (.vs (.vs .vz))
def point {Const : HOL.Ty AtomicTy → Type v} : HOL.Term Const context space := .var (.vs .vz)
def target {Const : HOL.Ty AtomicTy → Type v} : HOL.Term Const context index := .var .vz

def lifted {Const : HOL.Ty AtomicTy → Type v} : HOL.Term Const context (space ⇒ .prop) :=
  IndexedPredicateInduction.lift root property
def strengthened {Const : HOL.Ty AtomicTy → Type v} : HOL.Term Const context (space ⇒ .prop) :=
  PredicateFixedPoint.intersection signature.least lifted
def method {Const : HOL.Ty AtomicTy → Type v} : HOL.Formula Const context :=
  signature.closedMethod strengthened lifted
def member {Const : HOL.Ty AtomicTy → Type v} : HOL.Formula Const context :=
  .app (.app (signature.memberProgram root) point) target
def assumptions {Const : HOL.Ty AtomicTy → Type v} : List (HOL.Formula Const context) := [method]
def conclusion {Const : HOL.Ty AtomicTy → Type v} : HOL.Formula Const context :=
  .imp member (.app (.app property point) target)

def parametric {Const : HOL.Ty AtomicTy → Type v} : HOL.Formula Const context :=
  signature.parametricMethod lifted

def proof : ProofSyntax Symbol assumptions conclusion :=
  .impI (signature.indexedFromClosedMethod root property point target
    (.hyp ⟨1, by simp [assumptions]⟩) (.hyp ⟨0, by simp⟩))

theorem proof_free : proof.FunctionExtensionalityFree := by
  unfold proof
  exact signature.indexedFromClosedMethod_free root property point target _ _ trivial trivial

def bridgeProof : ProofSyntax Symbol [parametric] method :=
  signature.parametricToClosed strengthened lifted (.hyp ⟨0, by simp⟩)

theorem bridgeProof_free : bridgeProof.FunctionExtensionalityFree :=
  signature.parametricToClosed_free strengthened lifted _ trivial

def parameterAssumptions : List (ParameterTerm context .prop) := assumptions
def parameterConclusion : ParameterTerm context .prop := conclusion
def expandedAssumptions := parameterAssumptions.map ImpredicativeConnectives.expand
def expandedConclusion := ImpredicativeConnectives.expand parameterConclusion
def parameterParametric : ParameterTerm context .prop := parametric
def parameterMethod : ParameterTerm context .prop := method

def names (scopeName : String) : ReverseTranslation.Naming context :=
  ReverseTranslation.Naming.cons (.global (scopeName ++ "_target"))
    (ReverseTranslation.Naming.cons (.global (scopeName ++ "_point"))
      (ReverseTranslation.Naming.cons (.global (scopeName ++ "_property"))
        (ReverseTranslation.Naming.cons (.global (scopeName ++ "_root"))
          (ReverseTranslation.Naming.cons (.global (scopeName ++ "_edge"))
            (ReverseTranslation.Naming.cons (.global (scopeName ++ "_active"))
              (ReverseTranslation.Naming.cons (.global (scopeName ++ "_shape"))
                (ReverseTranslation.Naming.cons (.global (scopeName ++ "_construct"))
                  (ReverseTranslation.Naming.cons (.global (scopeName ++ "_bottom")) ReverseTranslation.Naming.empty))))))))

local instance : DecidablePred emptyAxiomPolicy := fun _ => isFalse id

@[irreducible, noinline] def schema (scopeName : String) :
    RetainedCompilation.Compiled emptyAxiomPolicy (@names scopeName)
      (expandedAssumptions.map embed) (embed expandedConclusion) :=
  RetainedCompilation.compileWithoutFunctionExtensionality emptyAxiomPolicy proof proof_free
    (@names scopeName) ("indexed-induction-schema", 0)

@[irreducible, noinline] def bridgeSchema (scopeName : String) :
    RetainedCompilation.Compiled emptyAxiomPolicy (@names scopeName)
      ([ImpredicativeConnectives.expand parameterParametric].map embed)
      (embed (ImpredicativeConnectives.expand parameterMethod)) :=
  RetainedCompilation.compileWithoutFunctionExtensionality emptyAxiomPolicy bridgeProof bridgeProof_free
    (@names scopeName) ("indexed-constructor-method-bridge", 0)

theorem names_distinct (types : TypeSubst) (scopeName : String) :
    Instantiation.KeysDistinct types (@names scopeName) := by
  unfold names
  apply Instantiation.KeysDistinct.cons types (.global (scopeName ++ "_target"))
  · apply Instantiation.KeysDistinct.cons types (.global (scopeName ++ "_point"))
    · apply Instantiation.KeysDistinct.cons types (.global (scopeName ++ "_property"))
      · apply Instantiation.KeysDistinct.cons types (.global (scopeName ++ "_root"))
        · apply Instantiation.KeysDistinct.cons types (.global (scopeName ++ "_edge"))
          · apply Instantiation.KeysDistinct.cons types (.global (scopeName ++ "_active"))
            · apply Instantiation.KeysDistinct.cons types (.global (scopeName ++ "_shape"))
              · apply Instantiation.KeysDistinct.cons types (.global (scopeName ++ "_construct"))
                · apply Instantiation.KeysDistinct.cons types (.global (scopeName ++ "_bottom"))
                  · exact Instantiation.KeysDistinct.empty types
                  · simp [ReverseTranslation.Naming.toList]
                · simp [ReverseTranslation.Naming.toList, ReverseTranslation.Naming.cons, Name.global, String.append_right_inj]
              · simp [ReverseTranslation.Naming.toList, ReverseTranslation.Naming.cons, Name.global, String.append_right_inj]
            · simp [ReverseTranslation.Naming.toList, ReverseTranslation.Naming.cons, Name.global, String.append_right_inj]
          · simp [ReverseTranslation.Naming.toList, ReverseTranslation.Naming.cons, Name.global, String.append_right_inj]
        · simp [ReverseTranslation.Naming.toList, ReverseTranslation.Naming.cons, Name.global, String.append_right_inj]
      · simp [ReverseTranslation.Naming.toList, ReverseTranslation.Naming.cons, Name.global, String.append_right_inj]
    · simp [ReverseTranslation.Naming.toList, ReverseTranslation.Naming.cons, Name.global, String.append_right_inj]
  · simp [ReverseTranslation.Naming.toList, ReverseTranslation.Naming.cons, Name.global, String.append_right_inj]

def instantiate (types : TypeSubst) (scopeName : String) {Γ : Ctx AtomicTy}
    (targetNames : ReverseTranslation.Naming Γ)
    (theta : HOL.Subst Symbol (context.map (HOL.Ty.substitute types.baseInstance)) Γ) :=
  ParameterSchemaCompilation.specializeExpanded types (@names scopeName) @targetNames @theta
    (conclusion := parameterConclusion) (assumptions := parameterAssumptions)
    (schema scopeName) (names_distinct types scopeName) ("indexed-induction-instance", 0)

def instantiateBridge (types : TypeSubst) (scopeName : String) {Γ : Ctx AtomicTy}
    (targetNames : ReverseTranslation.Naming Γ)
    (theta : HOL.Subst Symbol (context.map (HOL.Ty.substitute types.baseInstance)) Γ) :=
  ParameterSchemaCompilation.specializeExpanded types (@names scopeName) @targetNames @theta
    (conclusion := parameterMethod) (assumptions := [parameterParametric])
    (bridgeSchema scopeName) (names_distinct types scopeName) ("indexed-method-bridge-instance", 0)

def carrierTypes (targetNumber targetPayload targetSpace targetIndex : HOL.Ty AtomicTy) : TypeSubst :=
  ⟨[(.global "__schema_number", ReverseTranslation.reverseTy targetNumber),
    (.global "__schema_payload", ReverseTranslation.reverseTy targetPayload),
    (.global "__schema_space", ReverseTranslation.reverseTy targetSpace),
    (.global "__schema_index", ReverseTranslation.reverseTy targetIndex)]⟩

theorem carrier_number (n p s i : HOL.Ty AtomicTy) :
    HOL.Ty.substitute (carrierTypes n p s i).baseInstance number = n := by
  change ((carrierTypes n p s i).apply (.var (.global "__schema_number"))).toHOL = _
  rw [TypeSubst.apply_var]
  have lookup : (carrierTypes n p s i).lookup (.global "__schema_number") =
      some (ReverseTranslation.reverseTy n) := rfl
  rw [lookup, Option.getD_some, ReverseTranslation.toHOL_reverseTy]

theorem carrier_payload (n p s i : HOL.Ty AtomicTy) :
    HOL.Ty.substitute (carrierTypes n p s i).baseInstance payload = p := by
  change ((carrierTypes n p s i).apply (.var (.global "__schema_payload"))).toHOL = _
  rw [TypeSubst.apply_var]
  have lookup : (carrierTypes n p s i).lookup (.global "__schema_payload") =
      some (ReverseTranslation.reverseTy p) := rfl
  rw [lookup, Option.getD_some, ReverseTranslation.toHOL_reverseTy]

theorem carrier_space (n p s i : HOL.Ty AtomicTy) :
    HOL.Ty.substitute (carrierTypes n p s i).baseInstance space = s := by
  change ((carrierTypes n p s i).apply (.var (.global "__schema_space"))).toHOL = _
  rw [TypeSubst.apply_var]
  have lookup : (carrierTypes n p s i).lookup (.global "__schema_space") =
      some (ReverseTranslation.reverseTy s) := rfl
  rw [lookup, Option.getD_some, ReverseTranslation.toHOL_reverseTy]

theorem carrier_index (n p s i : HOL.Ty AtomicTy) :
    HOL.Ty.substitute (carrierTypes n p s i).baseInstance index = i := by
  change ((carrierTypes n p s i).apply (.var (.global "__schema_index"))).toHOL = _
  rw [TypeSubst.apply_var]
  have lookup : (carrierTypes n p s i).lookup (.global "__schema_index") =
      some (ReverseTranslation.reverseTy i) := rfl
  rw [lookup, Option.getD_some, ReverseTranslation.toHOL_reverseTy]

structure Bindings (types : TypeSubst) (Γ : Ctx AtomicTy) where
  bottom : HOL.Term Symbol Γ (HOL.Ty.substitute types.baseInstance space)
  construct : HOL.Term Symbol Γ (HOL.Ty.substitute types.baseInstance (number ⇒ payload ⇒ (number ⇒ space) ⇒ space))
  shape : HOL.Term Symbol Γ (HOL.Ty.substitute types.baseInstance (number ⇒ payload ⇒ .prop))
  active : HOL.Term Symbol Γ (HOL.Ty.substitute types.baseInstance (payload ⇒ number ⇒ .prop))
  edge : HOL.Term Symbol Γ (HOL.Ty.substitute types.baseInstance (payload ⇒ number ⇒ space ⇒ .prop))
  root : HOL.Term Symbol Γ (HOL.Ty.substitute types.baseInstance (space ⇒ index ⇒ .prop))
  property : HOL.Term Symbol Γ (HOL.Ty.substitute types.baseInstance (space ⇒ index ⇒ .prop))
  point : HOL.Term Symbol Γ (HOL.Ty.substitute types.baseInstance space)
  target : HOL.Term Symbol Γ (HOL.Ty.substitute types.baseInstance index)

namespace Bindings
variable {types : TypeSubst} {Γ : Ctx AtomicTy} (inputs : Bindings types Γ)

def substitution : HOL.Subst Symbol (context.map (HOL.Ty.substitute types.baseInstance)) Γ :=
  HOL.Subst.cons inputs.target (HOL.Subst.cons inputs.point (HOL.Subst.cons inputs.property
    (HOL.Subst.cons inputs.root (HOL.Subst.cons inputs.edge (HOL.Subst.cons inputs.active
      (HOL.Subst.cons inputs.shape (HOL.Subst.cons inputs.construct (HOL.Subst.cons inputs.bottom
        ((fun impossible => nomatch impossible) : HOL.Subst Symbol [] Γ)))))))))

def instanceSignature : RecursiveSpacePredicate.Contextual Symbol Γ :=
  ((signature (Const := fun _ => Empty)).read (reading types)).subst inputs.substitution
def instanceRoot : HOL.Term Symbol Γ
    (HOL.Ty.substitute types.baseInstance (space ⇒ index ⇒ .prop)) := inputs.root
def instanceProperty : HOL.Term Symbol Γ
    (HOL.Ty.substitute types.baseInstance (space ⇒ index ⇒ .prop)) := inputs.property

def instanceConclusion : HOL.Formula Symbol Γ :=
  .imp (.app (.app (inputs.instanceSignature.memberProgram inputs.root) inputs.point) inputs.target)
    (.app (.app inputs.property inputs.point) inputs.target)

def instanceMethod : HOL.Formula Symbol Γ :=
  inputs.instanceSignature.closedMethod
    (PredicateFixedPoint.intersection inputs.instanceSignature.least
      (IndexedPredicateInduction.lift inputs.root inputs.property))
    (IndexedPredicateInduction.lift inputs.root inputs.property)

def instanceParametric : HOL.Formula Symbol Γ :=
  inputs.instanceSignature.parametricMethod (IndexedPredicateInduction.lift inputs.root inputs.property)

theorem image_parametric (scopeName : String) (targetNames : ReverseTranslation.Naming Γ) :
    ParameterSchemaCompilation.image types (@names scopeName) @targetNames inputs.substitution parameterParametric =
      inputs.instanceParametric := by
  rw [ParameterSchemaCompilation.image_read]
  unfold parameterParametric parametric lifted
  rw [RecursiveSpacePredicate.Contextual.read_parametricMethod,
    RecursiveSpacePredicate.Contextual.read_indexedLift,
    RecursiveSpacePredicate.Contextual.subst_parametricMethod, IndexedPredicateInduction.subst_lift]
  rfl

theorem image_method (scopeName : String) (targetNames : ReverseTranslation.Naming Γ) :
    ParameterSchemaCompilation.image types (@names scopeName) @targetNames inputs.substitution
      (method (Const := fun _ => Empty)) = inputs.instanceMethod := by
  rw [ParameterSchemaCompilation.image_read]
  unfold method strengthened lifted
  rw [RecursiveSpacePredicate.Contextual.read_closedMethod,
    RecursiveSpacePredicate.Contextual.read_predicateIntersection,
    RecursiveSpacePredicate.Contextual.read_least,
    RecursiveSpacePredicate.Contextual.read_indexedLift]
  rw [RecursiveSpacePredicate.Contextual.subst_closedMethod,
    PredicateFixedPoint.subst_intersection, RecursiveSpacePredicate.Contextual.subst_least,
    IndexedPredicateInduction.subst_lift]
  rfl

theorem image_conclusion (scopeName : String) (targetNames : ReverseTranslation.Naming Γ) :
    ParameterSchemaCompilation.image types (@names scopeName) @targetNames inputs.substitution parameterConclusion =
      inputs.instanceConclusion := by
  rw [ParameterSchemaCompilation.image_read]
  unfold parameterConclusion conclusion member
  rw [TermInterpretation.term_imp, TermInterpretation.term_app, TermInterpretation.term_app,
    RecursiveSpacePredicate.Contextual.read_memberProgram]
  simp only [HOL.subst]
  unfold RecursiveSpacePredicate.Contextual.memberProgram
  rw [CurriedGuardProgramProofs.subst_conjunctionProgram, RecursiveSpacePredicate.Contextual.subst_least]
  rfl

theorem image_assumptions (scopeName : String) (targetNames : ReverseTranslation.Naming Γ) :
    parameterAssumptions.map (ParameterSchemaCompilation.image types (@names scopeName)
      @targetNames inputs.substitution) = [inputs.instanceMethod] := by
  simp only [parameterAssumptions, assumptions, List.map_cons, List.map_nil]
  rw [inputs.image_method]

def compile (scopeName : String) (targetNames : ReverseTranslation.Naming Γ) :
    RetainedCompilation.Compiled emptyAxiomPolicy @targetNames
      ([inputs.instanceMethod].map ImpredicativeConnectives.expand)
      (ImpredicativeConnectives.expand inputs.instanceConclusion) := by
  let result := instantiate types scopeName @targetNames inputs.substitution
  exact ⟨result.proof,
    result.hypotheses_exact.trans (congrArg
      (fun formulas => ReverseTranslation.reverseHypotheses @targetNames
        (formulas.map ImpredicativeConnectives.expand)) (inputs.image_assumptions scopeName @targetNames)),
    result.conclusion_exact.trans (congrArg
      (fun formula => ReverseTranslation.reverseCanonical @targetNames (ImpredicativeConnectives.expand formula))
      (inputs.image_conclusion scopeName @targetNames))⟩

def compileBridge (scopeName : String) (targetNames : ReverseTranslation.Naming Γ) :
    RetainedCompilation.Compiled emptyAxiomPolicy @targetNames
      ([inputs.instanceParametric].map ImpredicativeConnectives.expand)
      (ImpredicativeConnectives.expand inputs.instanceMethod) := by
  let result := instantiateBridge types scopeName @targetNames inputs.substitution
  exact ⟨result.proof,
    result.hypotheses_exact.trans (congrArg
      (fun formulas => ReverseTranslation.reverseHypotheses @targetNames (formulas.map ImpredicativeConnectives.expand))
      (show [parameterParametric].map (ParameterSchemaCompilation.image types (@names scopeName)
        @targetNames inputs.substitution) = [inputs.instanceParametric] by
          simp only [List.map_cons, List.map_nil, inputs.image_parametric])),
    result.conclusion_exact.trans (congrArg
      (fun formula => ReverseTranslation.reverseCanonical @targetNames (ImpredicativeConnectives.expand formula))
      (inputs.image_method scopeName @targetNames))⟩

def family : RecursiveSpacePredicate.Contextual Symbol Γ where
  number := HOL.Ty.substitute types.baseInstance number
  payload := HOL.Ty.substitute types.baseInstance payload
  space := HOL.Ty.substitute types.baseInstance space
  bottom := inputs.bottom
  construct := inputs.construct
  validShape := inputs.shape
  active := inputs.active
  validEdge := inputs.edge

theorem family_source : inputs.instanceSignature = inputs.family := rfl

open RecursiveConstructorCompilation.Parameters (castTerm castTerm_heq)

def ofSignature (family : RecursiveSpacePredicate.Contextual Symbol Γ) {targetIndex : HOL.Ty AtomicTy}
    (root property : HOL.Term Symbol Γ (family.space ⇒ targetIndex ⇒ .prop))
    (point : HOL.Term Symbol Γ family.space) (target : HOL.Term Symbol Γ targetIndex) :
    Bindings (carrierTypes family.number family.payload family.space targetIndex) Γ where
  bottom := castTerm (carrier_space _ _ _ _).symm family.bottom
  construct := castTerm (by simp only [HOL.Ty.substitute_arr, carrier_number, carrier_payload, carrier_space]) family.construct
  shape := castTerm (by simp only [HOL.Ty.substitute_arr, HOL.Ty.substitute_prop, carrier_number, carrier_payload]) family.validShape
  active := castTerm (by simp only [HOL.Ty.substitute_arr, HOL.Ty.substitute_prop, carrier_number, carrier_payload]) family.active
  edge := castTerm (by simp only [HOL.Ty.substitute_arr, HOL.Ty.substitute_prop, carrier_number, carrier_payload, carrier_space]) family.validEdge
  root := castTerm (by simp only [HOL.Ty.substitute_arr, HOL.Ty.substitute_prop, carrier_space, carrier_index]) root
  property := castTerm (by simp only [HOL.Ty.substitute_arr, HOL.Ty.substitute_prop, carrier_space, carrier_index]) property
  point := castTerm (carrier_space _ _ _ _).symm point
  target := castTerm (carrier_index _ _ _ _).symm target

theorem ofSignature_family (family : RecursiveSpacePredicate.Contextual Symbol Γ) {targetIndex : HOL.Ty AtomicTy}
    (root property : HOL.Term Symbol Γ (family.space ⇒ targetIndex ⇒ .prop))
    (point : HOL.Term Symbol Γ family.space) (target : HOL.Term Symbol Γ targetIndex) :
    (ofSignature family root property point target).instanceSignature = family := by
  rw [family_source]
  refine RecursiveSpacePredicate.Contextual.eq_of_fields
    (carrier_number _ _ _ _) (carrier_payload _ _ _ _) (carrier_space _ _ _ _) ?_ ?_ ?_ ?_ ?_
  all_goals exact castTerm_heq _ _

private theorem method_of_equal_data
    {first second : RecursiveSpacePredicate.Contextual Symbol Γ} (same : first = second)
    {firstIndex secondIndex : HOL.Ty AtomicTy} (indexSame : firstIndex = secondIndex)
    (firstRoot firstProperty : HOL.Term Symbol Γ (first.space ⇒ firstIndex ⇒ .prop))
    (secondRoot secondProperty : HOL.Term Symbol Γ (second.space ⇒ secondIndex ⇒ .prop))
    (rootSame : HEq firstRoot secondRoot) (propertySame : HEq firstProperty secondProperty) :
    first.closedMethod
        (PredicateFixedPoint.intersection first.least (IndexedPredicateInduction.lift firstRoot firstProperty))
        (IndexedPredicateInduction.lift firstRoot firstProperty) =
      second.closedMethod
        (PredicateFixedPoint.intersection second.least (IndexedPredicateInduction.lift secondRoot secondProperty))
        (IndexedPredicateInduction.lift secondRoot secondProperty) := by
  cases same
  cases indexSame
  cases rootSame
  cases propertySame
  rfl

private theorem parametric_of_equal_data
    {first second : RecursiveSpacePredicate.Contextual Symbol Γ} (same : first = second)
    {firstIndex secondIndex : HOL.Ty AtomicTy} (indexSame : firstIndex = secondIndex)
    (firstRoot firstProperty : HOL.Term Symbol Γ (first.space ⇒ firstIndex ⇒ .prop))
    (secondRoot secondProperty : HOL.Term Symbol Γ (second.space ⇒ secondIndex ⇒ .prop))
    (rootSame : HEq firstRoot secondRoot) (propertySame : HEq firstProperty secondProperty) :
    first.parametricMethod (IndexedPredicateInduction.lift firstRoot firstProperty) =
      second.parametricMethod (IndexedPredicateInduction.lift secondRoot secondProperty) := by
  cases same
  cases indexSame
  cases rootSame
  cases propertySame
  rfl

theorem ofSignature_method (family : RecursiveSpacePredicate.Contextual Symbol Γ) {targetIndex : HOL.Ty AtomicTy}
    (root property : HOL.Term Symbol Γ (family.space ⇒ targetIndex ⇒ .prop))
    (point : HOL.Term Symbol Γ family.space) (target : HOL.Term Symbol Γ targetIndex) :
    (ofSignature family root property point target).instanceMethod =
      family.closedMethod
        (PredicateFixedPoint.intersection family.least (IndexedPredicateInduction.lift root property))
        (IndexedPredicateInduction.lift root property) := by
  exact method_of_equal_data (ofSignature_family family root property point target)
    (carrier_index _ _ _ _) _ _ root property (castTerm_heq _ _) (castTerm_heq _ _)

theorem ofSignature_parametric (family : RecursiveSpacePredicate.Contextual Symbol Γ) {targetIndex : HOL.Ty AtomicTy}
    (root property : HOL.Term Symbol Γ (family.space ⇒ targetIndex ⇒ .prop))
    (point : HOL.Term Symbol Γ family.space) (target : HOL.Term Symbol Γ targetIndex) :
    (ofSignature family root property point target).instanceParametric =
      family.parametricMethod (IndexedPredicateInduction.lift root property) := by
  exact parametric_of_equal_data (ofSignature_family family root property point target)
    (carrier_index _ _ _ _) _ _ root property (castTerm_heq _ _) (castTerm_heq _ _)

private theorem conclusion_of_equal_data
    {first second : RecursiveSpacePredicate.Contextual Symbol Γ} (same : first = second)
    {firstIndex secondIndex : HOL.Ty AtomicTy} (indexSame : firstIndex = secondIndex)
    (firstRoot firstProperty : HOL.Term Symbol Γ (first.space ⇒ firstIndex ⇒ .prop))
    (secondRoot secondProperty : HOL.Term Symbol Γ (second.space ⇒ secondIndex ⇒ .prop))
    (rootSame : HEq firstRoot secondRoot) (propertySame : HEq firstProperty secondProperty)
    (firstPoint : HOL.Term Symbol Γ first.space) (secondPoint : HOL.Term Symbol Γ second.space)
    (pointSame : HEq firstPoint secondPoint)
    (firstTarget : HOL.Term Symbol Γ firstIndex) (secondTarget : HOL.Term Symbol Γ secondIndex)
    (targetSame : HEq firstTarget secondTarget) :
    HOL.Term.imp (.app (.app (first.memberProgram firstRoot) firstPoint) firstTarget)
        (.app (.app firstProperty firstPoint) firstTarget) =
      HOL.Term.imp (.app (.app (second.memberProgram secondRoot) secondPoint) secondTarget)
        (.app (.app secondProperty secondPoint) secondTarget) := by
  cases same
  cases indexSame
  cases rootSame
  cases propertySame
  cases pointSame
  cases targetSame
  rfl

theorem ofSignature_conclusion (family : RecursiveSpacePredicate.Contextual Symbol Γ) {targetIndex : HOL.Ty AtomicTy}
    (root property : HOL.Term Symbol Γ (family.space ⇒ targetIndex ⇒ .prop))
    (point : HOL.Term Symbol Γ family.space) (target : HOL.Term Symbol Γ targetIndex) :
    (ofSignature family root property point target).instanceConclusion =
      .imp (.app (.app (family.memberProgram root) point) target) (.app (.app property point) target) := by
  exact conclusion_of_equal_data (ofSignature_family family root property point target)
    (carrier_index _ _ _ _) _ _ root property (castTerm_heq _ _) (castTerm_heq _ _)
    _ point (castTerm_heq _ _) _ target (castTerm_heq _ _)

end Bindings

#print axioms proof_free
#print axioms names_distinct
#print axioms instantiate
#print axioms schema
#print axioms carrier_index

end Mettapedia.Languages.HOLLight.IndexedInductionSchemas
