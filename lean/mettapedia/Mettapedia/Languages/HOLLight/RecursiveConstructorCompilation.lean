import Mettapedia.Logic.HOL.RecursiveSpaceConstructorProofs
import Mettapedia.Logic.HOL.ContextualRecursiveSpaceProofs
import Mettapedia.Logic.HOL.Syntax.SubstitutionExtension
import Mettapedia.Languages.HOLLight.RetainedCompilation
import Mettapedia.Languages.HOLLight.ParameterSchemaCompilation

/-!
# Native compilation of conditional recursive-space schemas

The constructor algebra and three guards are free typed parameters. The
constructor schema retains its shape and complete child-condition hypotheses;
the unfolding schema retains the supplied membership hypothesis. No datatype
equation, infinitude statement or additional inference rule is admitted here.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Languages.HOLLight.RecursiveConstructorCompilation
open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open HOL ReverseTranslation

def atomic (name : String) : AtomicTy := ⟨.var (.global name), by constructor <;> rfl⟩
def free (name : String) (type : HOL.Ty AtomicTy) : HOL.ClosedTerm Symbol type :=
  .const (.variable ⟨.global name, reverseTy type⟩ (toHOL_reverseTy type))

abbrev number : HOL.Ty AtomicTy := .base (atomic "__schema_number")
abbrev payload : HOL.Ty AtomicTy := .base (atomic "__schema_payload")
abbrev space : HOL.Ty AtomicTy := .base (atomic "__schema_space")

def signature (scopeName : String) : RecursiveSpacePredicate.Signature Symbol where
  number := number
  payload := payload
  space := space
  bottom := free (scopeName ++ "_bottom") space
  construct := free (scopeName ++ "_construct") (number ⇒ payload ⇒ (number ⇒ space) ⇒ space)
  validShape := free (scopeName ++ "_shape") (number ⇒ payload ⇒ .prop)
  active := free (scopeName ++ "_active") (payload ⇒ number ⇒ .prop)
  validEdge := free (scopeName ++ "_edge") (payload ⇒ number ⇒ space ⇒ .prop)

variable (operations : RecursiveSpacePredicate.Signature Symbol)
abbrev context : HOL.Ctx AtomicTy := [operations.number ⇒ operations.space, operations.payload, operations.number]
def tag : HOL.Term Symbol (context operations) operations.number := .var (.vs (.vs .vz))
def data : HOL.Term Symbol (context operations) operations.payload := .var (.vs .vz)
def children : HOL.Term Symbol (context operations) (operations.number ⇒ operations.space) := .var .vz

def assumptions : List (HOL.Formula Symbol (context operations)) :=
  [operations.shapeAt (tag operations) (data operations),
    operations.childConditions operations.leastIn (data operations) (children operations)]

def shapePremise : HOL.ProofSyntax Symbol (assumptions operations)
    (operations.shapeAt (tag operations) (data operations)) :=
  .hyp ⟨0, by change 0 < 2; decide⟩
def childrenPremise : HOL.ProofSyntax Symbol (assumptions operations)
    (operations.childConditions operations.leastIn (data operations) (children operations)) :=
  .hyp ⟨1, by change 1 < 2; decide⟩

def introduction : HOL.ProofSyntax Symbol (assumptions operations)
    (.app operations.leastIn (operations.constructValue (tag operations) (data operations) (children operations))) :=
  operations.constructor_intro (tag operations) (data operations) (children operations)
    (shapePremise operations) (childrenPremise operations)

theorem introduction_free : (introduction operations).FunctionExtensionalityFree :=
  operations.constructor_intro_free (tag operations) (data operations) (children operations)
    (shapePremise operations) (childrenPremise operations) True.intro True.intro

def names : Naming (context operations) :=
  Naming.cons (.global "__constructor_children")
    (Naming.cons (.global "__constructor_payload") (Naming.cons (.global "__constructor_tag") Naming.empty))

def compiledIntroduction (callerNames : Naming (context operations)) :=
  RetainedCompilation.compileWithoutFunctionExtensionality emptyAxiomPolicy
    (introduction operations) (introduction_free operations) callerNames ("recursive-constructor", 0)

def point : HOL.Term Symbol [operations.space] operations.space := .var .vz
def membership : HOL.Formula Symbol [operations.space] := .app operations.leastIn (point operations)
def unfolding : HOL.ProofSyntax Symbol [membership operations] (operations.layer operations.leastIn (point operations)) :=
  operations.unfold_member (point operations) (.hyp 0)

theorem unfolding_free : (unfolding operations).FunctionExtensionalityFree :=
  operations.unfold_member_free (Δ := [membership operations]) (point operations) (.hyp 0) True.intro

def pointNames : Naming [operations.space] := Naming.cons (.global "__constructor_point") Naming.empty

def compiledUnfolding (callerNames : Naming [operations.space]) :=
  RetainedCompilation.compileWithoutFunctionExtensionality emptyAxiomPolicy
    (unfolding operations) (unfolding_free operations) callerNames ("recursive-unfolding", 0)

def compiledMonotonicity := RetainedCompilation.compileWithoutFunctionExtensionality emptyAxiomPolicy
  operations.monotonicity operations.monotonicity_functionExtensionalityFree Naming.empty ("recursive-monotonicity", 0)

def compiledFixedPoint := RetainedCompilation.compileWithoutFunctionExtensionality emptyAxiomPolicy
  operations.fixedPoint operations.fixedPoint_functionExtensionalityFree Naming.empty ("recursive-fixed-point", 0)

theorem introduction_accepted (callerNames : Naming (context operations)) :
    (ProofSystem.checker emptyAxiomPolicy).check (compiledIntroduction operations callerNames).proof.result
      (compiledIntroduction operations callerNames).proof.certificate = true :=
  (compiledIntroduction operations callerNames).proof.accepted

theorem unfolding_accepted (callerNames : Naming [operations.space]) :
    (ProofSystem.checker emptyAxiomPolicy).check (compiledUnfolding operations callerNames).proof.result
      (compiledUnfolding operations callerNames).proof.certificate = true :=
  (compiledUnfolding operations callerNames).proof.accepted

theorem introduction_sequent (callerNames : Naming (context operations)) :
    (compiledIntroduction operations callerNames).proof.result.sequent.concl =
      reverseCanonical callerNames (HOL.ImpredicativeConnectives.expand
        (.app operations.leastIn (operations.constructValue (tag operations) (data operations) (children operations)))) :=
  (compiledIntroduction operations callerNames).conclusion_exact

theorem introduction_hypotheses (callerNames : Naming (context operations)) :
    (compiledIntroduction operations callerNames).proof.result.sequent.hyp =
      reverseHypotheses callerNames ((assumptions operations).map HOL.ImpredicativeConnectives.expand) :=
  (compiledIntroduction operations callerNames).hypotheses_exact

#print axioms introduction_accepted
#print axioms unfolding_accepted
#print axioms introduction_sequent
#print axioms introduction_hypotheses

namespace Parameters
open ReverseTranslation.VariableSchema
universe v

abbrev context : HOL.Ctx AtomicTy := [number ⇒ space, payload, number,
  payload ⇒ number ⇒ space ⇒ .prop, payload ⇒ number ⇒ .prop, number ⇒ payload ⇒ .prop,
  number ⇒ payload ⇒ (number ⇒ space) ⇒ space, space]

def signature {Const : HOL.Ty AtomicTy → Type v} : RecursiveSpacePredicate.Contextual Const context where
  number := number
  payload := payload
  space := space
  bottom := .var (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))
  construct := .var (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))
  validShape := .var (.vs (.vs (.vs (.vs (.vs .vz)))))
  active := .var (.vs (.vs (.vs (.vs .vz))))
  validEdge := .var (.vs (.vs (.vs .vz)))

def tag {Const : HOL.Ty AtomicTy → Type v} : Term Const context number := .var (.vs (.vs .vz))
def data {Const : HOL.Ty AtomicTy → Type v} : Term Const context payload := .var (.vs .vz)
def children {Const : HOL.Ty AtomicTy → Type v} : Term Const context (number ⇒ space) := .var .vz

def assumptions {Const : HOL.Ty AtomicTy → Type v} : List (Formula Const context) :=
  [signature.shapeAt tag data, signature.childConditions signature.least data children]
def conclusion {Const : HOL.Ty AtomicTy → Type v} : Formula Const context :=
  .app signature.least (signature.constructValue tag data children)

def shapePremise : ProofSyntax Symbol assumptions (signature.shapeAt tag data) := .hyp ⟨0, by decide⟩
def childrenPremise : ProofSyntax Symbol assumptions (signature.childConditions signature.least data children) := .hyp ⟨1, by decide⟩
def proof : ProofSyntax Symbol assumptions conclusion :=
  signature.constructor_intro tag data children shapePremise childrenPremise

theorem proof_free : proof.FunctionExtensionalityFree :=
  signature.constructor_intro_free tag data children shapePremise childrenPremise True.intro True.intro

def parameterAssumptions : List (ParameterTerm context .prop) := assumptions
def parameterConclusion : ParameterTerm context .prop := conclusion
def expandedAssumptions := parameterAssumptions.map ImpredicativeConnectives.expand
def expandedConclusion := ImpredicativeConnectives.expand parameterConclusion

def names (scopeName : String) : Naming context :=
  Naming.cons (.global (scopeName ++ "_children")) (Naming.cons (.global (scopeName ++ "_payload"))
    (Naming.cons (.global (scopeName ++ "_tag")) (Naming.cons (.global (scopeName ++ "_edge"))
      (Naming.cons (.global (scopeName ++ "_active")) (Naming.cons (.global (scopeName ++ "_shape"))
        (Naming.cons (.global (scopeName ++ "_construct")) (Naming.cons (.global (scopeName ++ "_bottom")) Naming.empty)))))))

def schema (scopeName : String) : RetainedCompilation.Compiled emptyAxiomPolicy (@names scopeName)
    (expandedAssumptions.map embed) (embed expandedConclusion) :=
  RetainedCompilation.compileWithoutFunctionExtensionality emptyAxiomPolicy proof proof_free (@names scopeName)
    ("parameter-constructor", 0)

theorem names_distinct (types : TypeSubst) (scopeName : String) :
    Instantiation.KeysDistinct types (@names scopeName) := by
  apply Instantiation.KeysDistinct.cons types (.global (scopeName ++ "_children"))
  · apply Instantiation.KeysDistinct.cons types (.global (scopeName ++ "_payload"))
    · apply Instantiation.KeysDistinct.cons types (.global (scopeName ++ "_tag"))
      · apply Instantiation.KeysDistinct.cons types (.global (scopeName ++ "_edge"))
        · apply Instantiation.KeysDistinct.cons types (.global (scopeName ++ "_active"))
          · apply Instantiation.KeysDistinct.cons types (.global (scopeName ++ "_shape"))
            · apply Instantiation.KeysDistinct.cons types (.global (scopeName ++ "_construct"))
              · apply Instantiation.KeysDistinct.cons types (.global (scopeName ++ "_bottom"))
                · exact Instantiation.KeysDistinct.empty types
                · simp [Naming.toList]
              · simp [Naming.toList, Naming.cons, Name.global, String.append_right_inj]
            · simp [Naming.toList, Naming.cons, Name.global, String.append_right_inj]
          · simp [Naming.toList, Naming.cons, Name.global, String.append_right_inj]
        · simp [Naming.toList, Naming.cons, Name.global, String.append_right_inj]
      · simp [Naming.toList, Naming.cons, Name.global, String.append_right_inj]
    · simp [Naming.toList, Naming.cons, Name.global, String.append_right_inj]
  · simp [Naming.toList, Naming.cons, Name.global, String.append_right_inj]

def instantiate (types : TypeSubst) (scopeName : String) {Γ : HOL.Ctx AtomicTy}
    (targetNames : Naming Γ)
    (theta : Subst Symbol (context.map (HOL.Ty.substitute types.baseInstance)) Γ) :=
  ParameterSchemaCompilation.specialize types (@names scopeName) @targetNames @theta
    (conclusion := expandedConclusion) (assumptions := expandedAssumptions)
    (schema scopeName) (names_distinct types scopeName) ("parameter-constructor-instance", 0)

variable (types : TypeSubst) {Γ : HOL.Ctx AtomicTy}
  (theta : Subst Symbol (context.map (HOL.Ty.substitute types.baseInstance)) Γ)

def instanceSignature : RecursiveSpacePredicate.Contextual Symbol Γ :=
  ((signature (Const := fun _ => Empty)).read (reading types)).subst theta
def instanceTag : Term Symbol Γ (HOL.Ty.substitute types.baseInstance number) :=
  HOL.subst theta ((reading types).term (tag (Const := fun _ => Empty)))
def instanceData : Term Symbol Γ (HOL.Ty.substitute types.baseInstance payload) :=
  HOL.subst theta ((reading types).term (data (Const := fun _ => Empty)))
def instanceChildren : Term Symbol Γ (HOL.Ty.substitute types.baseInstance (number ⇒ space)) :=
  HOL.subst theta ((reading types).term (children (Const := fun _ => Empty)))
def instanceAssumptions : List (Formula Symbol Γ) :=
  [(instanceSignature types @theta).shapeAt (instanceTag types @theta) (instanceData types @theta),
   (instanceSignature types @theta).childConditions (instanceSignature types @theta).least
     (instanceData types @theta) (instanceChildren types @theta)]
def instanceConclusion : Formula Symbol Γ := .app (instanceSignature types @theta).least
  ((instanceSignature types @theta).constructValue (instanceTag types @theta)
    (instanceData types @theta) (instanceChildren types @theta))

theorem image_conclusion (scopeName : String) (targetNames : Naming Γ) :
    ParameterSchemaCompilation.image types (@names scopeName) @targetNames @theta parameterConclusion =
      instanceConclusion types @theta := by
  rw [ParameterSchemaCompilation.image_read]
  unfold parameterConclusion conclusion instanceConclusion instanceSignature instanceTag instanceData instanceChildren
  rw [TermInterpretation.term_app, RecursiveSpacePredicate.Contextual.read_least,
    RecursiveSpacePredicate.Contextual.read_constructValue]
  change Term.app (HOL.subst theta _) (HOL.subst theta _) = _
  rw [RecursiveSpacePredicate.Contextual.subst_least, RecursiveSpacePredicate.Contextual.subst_constructValue]

theorem image_assumptions (scopeName : String) (targetNames : Naming Γ) :
    parameterAssumptions.map (ParameterSchemaCompilation.image types (@names scopeName) @targetNames @theta) =
      instanceAssumptions types @theta := by
  simp only [parameterAssumptions, assumptions, List.map_cons, List.map_nil,
    ParameterSchemaCompilation.image_read, RecursiveSpacePredicate.Contextual.read_shapeAt,
    RecursiveSpacePredicate.Contextual.read_childConditions, RecursiveSpacePredicate.Contextual.read_least,
    RecursiveSpacePredicate.Contextual.subst_shapeAt, RecursiveSpacePredicate.Contextual.subst_childConditions,
    RecursiveSpacePredicate.Contextual.subst_least, instanceAssumptions, instanceSignature,
    instanceTag, instanceData, instanceChildren]

def compile (scopeName : String) (targetNames : Naming Γ) :
    RetainedCompilation.Compiled emptyAxiomPolicy @targetNames
      ((instanceAssumptions types @theta).map ImpredicativeConnectives.expand)
      (ImpredicativeConnectives.expand (instanceConclusion types @theta)) := by
  let result := ParameterSchemaCompilation.specializeExpanded types (@names scopeName) @targetNames @theta
    (conclusion := parameterConclusion) (assumptions := parameterAssumptions)
    (schema scopeName) (names_distinct types scopeName) ("parameter-constructor-instance", 0)
  exact ⟨result.proof,
    result.hypotheses_exact.trans (congrArg (fun formulas =>
      reverseHypotheses @targetNames (formulas.map ImpredicativeConnectives.expand))
        (image_assumptions types @theta scopeName @targetNames)),
    result.conclusion_exact.trans (congrArg (fun formula =>
      reverseCanonical @targetNames (ImpredicativeConnectives.expand formula))
        (image_conclusion types @theta scopeName @targetNames))⟩

structure Bindings (types : TypeSubst) (Γ : HOL.Ctx AtomicTy) where
  bottom : Term Symbol Γ (HOL.Ty.substitute types.baseInstance space)
  construct : Term Symbol Γ (HOL.Ty.substitute types.baseInstance (number ⇒ payload ⇒ (number ⇒ space) ⇒ space))
  shape : Term Symbol Γ (HOL.Ty.substitute types.baseInstance (number ⇒ payload ⇒ .prop))
  active : Term Symbol Γ (HOL.Ty.substitute types.baseInstance (payload ⇒ number ⇒ .prop))
  edge : Term Symbol Γ (HOL.Ty.substitute types.baseInstance (payload ⇒ number ⇒ space ⇒ .prop))
  tag : Term Symbol Γ (HOL.Ty.substitute types.baseInstance number)
  data : Term Symbol Γ (HOL.Ty.substitute types.baseInstance payload)
  children : Term Symbol Γ (HOL.Ty.substitute types.baseInstance (number ⇒ space))

def carrierTypes (targetNumber targetPayload targetSpace : HOL.Ty AtomicTy) : TypeSubst :=
  ⟨[(.global "__schema_number", reverseTy targetNumber), (.global "__schema_payload", reverseTy targetPayload),
    (.global "__schema_space", reverseTy targetSpace)]⟩

theorem carrier_number (targetNumber targetPayload targetSpace : HOL.Ty AtomicTy) :
    HOL.Ty.substitute (carrierTypes targetNumber targetPayload targetSpace).baseInstance number = targetNumber := by
  change ((carrierTypes targetNumber targetPayload targetSpace).apply (.var (.global "__schema_number"))).toHOL = _
  rw [TypeSubst.apply_var]
  have lookup : (carrierTypes targetNumber targetPayload targetSpace).lookup (.global "__schema_number") =
      some (reverseTy targetNumber) := rfl
  rw [lookup, Option.getD_some, toHOL_reverseTy]

theorem carrier_payload (targetNumber targetPayload targetSpace : HOL.Ty AtomicTy) :
    HOL.Ty.substitute (carrierTypes targetNumber targetPayload targetSpace).baseInstance payload = targetPayload := by
  change ((carrierTypes targetNumber targetPayload targetSpace).apply (.var (.global "__schema_payload"))).toHOL = _
  rw [TypeSubst.apply_var]
  have lookup : (carrierTypes targetNumber targetPayload targetSpace).lookup (.global "__schema_payload") =
      some (reverseTy targetPayload) := rfl
  rw [lookup, Option.getD_some, toHOL_reverseTy]

theorem carrier_space (targetNumber targetPayload targetSpace : HOL.Ty AtomicTy) :
    HOL.Ty.substitute (carrierTypes targetNumber targetPayload targetSpace).baseInstance space = targetSpace := by
  change ((carrierTypes targetNumber targetPayload targetSpace).apply (.var (.global "__schema_space"))).toHOL = _
  rw [TypeSubst.apply_var]
  have lookup : (carrierTypes targetNumber targetPayload targetSpace).lookup (.global "__schema_space") =
      some (reverseTy targetSpace) := rfl
  rw [lookup, Option.getD_some, toHOL_reverseTy]

def castTerm {Γ : HOL.Ctx AtomicTy} {first second : HOL.Ty AtomicTy}
    (same : first = second) (term : Term Symbol Γ first) : Term Symbol Γ second := same ▸ term

theorem castTerm_heq {Γ : HOL.Ctx AtomicTy} {first second : HOL.Ty AtomicTy}
    (same : first = second) (term : Term Symbol Γ first) : HEq (castTerm same term) term := by cases same; rfl

namespace Bindings
variable {types : TypeSubst} {Γ : HOL.Ctx AtomicTy} (inputs : Bindings types Γ)

def substitution : Subst Symbol (context.map (HOL.Ty.substitute types.baseInstance)) Γ :=
  Subst.cons inputs.children (Subst.cons inputs.data (Subst.cons inputs.tag
    (Subst.cons inputs.edge (Subst.cons inputs.active (Subst.cons inputs.shape
      (Subst.cons inputs.construct (Subst.cons inputs.bottom
        ((fun impossible => nomatch impossible) : Subst Symbol [] Γ))))))))

def signature : RecursiveSpacePredicate.Contextual Symbol Γ where
  number := HOL.Ty.substitute types.baseInstance number
  payload := HOL.Ty.substitute types.baseInstance payload
  space := HOL.Ty.substitute types.baseInstance space
  bottom := inputs.bottom
  construct := inputs.construct
  validShape := inputs.shape
  active := inputs.active
  validEdge := inputs.edge

theorem signature_source : instanceSignature types inputs.substitution = inputs.signature := rfl
theorem tag_source : instanceTag types inputs.substitution = inputs.tag := rfl
theorem data_source : instanceData types inputs.substitution = inputs.data := rfl
theorem children_source : instanceChildren types inputs.substitution = inputs.children := rfl

def compile (scopeName : String) (targetNames : Naming Γ) :
    RetainedCompilation.Compiled emptyAxiomPolicy @targetNames
      ([inputs.signature.shapeAt inputs.tag inputs.data,
        inputs.signature.childConditions inputs.signature.least inputs.data inputs.children].map ImpredicativeConnectives.expand)
      (ImpredicativeConnectives.expand (.app inputs.signature.least
        (inputs.signature.constructValue inputs.tag inputs.data inputs.children))) := by
  simpa only [instanceAssumptions, instanceConclusion, signature_source, tag_source, data_source, children_source]
    using Parameters.compile types inputs.substitution scopeName @targetNames

def ofSignature (family : RecursiveSpacePredicate.Contextual Symbol Γ)
    (tag : Term Symbol Γ family.number) (data : Term Symbol Γ family.payload)
    (children : Term Symbol Γ (family.number ⇒ family.space)) :
    Bindings (carrierTypes family.number family.payload family.space) Γ where
  bottom := castTerm (carrier_space family.number family.payload family.space).symm family.bottom
  construct := castTerm (by
    simp only [HOL.Ty.substitute_arr, carrier_number, carrier_payload, carrier_space]) family.construct
  shape := castTerm (by
    simp only [HOL.Ty.substitute_arr, HOL.Ty.substitute_prop, carrier_number, carrier_payload]) family.validShape
  active := castTerm (by
    simp only [HOL.Ty.substitute_arr, HOL.Ty.substitute_prop, carrier_number, carrier_payload]) family.active
  edge := castTerm (by
    simp only [HOL.Ty.substitute_arr, HOL.Ty.substitute_prop, carrier_number, carrier_payload, carrier_space]) family.validEdge
  tag := castTerm (carrier_number family.number family.payload family.space).symm tag
  data := castTerm (carrier_payload family.number family.payload family.space).symm data
  children := castTerm (by simp only [HOL.Ty.substitute_arr, carrier_number, carrier_space]) children

theorem ofSignature_signature (family : RecursiveSpacePredicate.Contextual Symbol Γ)
    (tag : Term Symbol Γ family.number) (data : Term Symbol Γ family.payload)
    (children : Term Symbol Γ (family.number ⇒ family.space)) :
    (ofSignature family tag data children).signature = family := by
  refine RecursiveSpacePredicate.Contextual.eq_of_fields
    (carrier_number family.number family.payload family.space)
    (carrier_payload family.number family.payload family.space)
    (carrier_space family.number family.payload family.space) ?_ ?_ ?_ ?_ ?_
  all_goals exact castTerm_heq _ _

theorem ofSignature_tag (family : RecursiveSpacePredicate.Contextual Symbol Γ)
    (tag : Term Symbol Γ family.number) (data : Term Symbol Γ family.payload)
    (children : Term Symbol Γ (family.number ⇒ family.space)) :
    HEq (ofSignature family tag data children).tag tag := castTerm_heq _ _

theorem ofSignature_data (family : RecursiveSpacePredicate.Contextual Symbol Γ)
    (tag : Term Symbol Γ family.number) (data : Term Symbol Γ family.payload)
    (children : Term Symbol Γ (family.number ⇒ family.space)) :
    HEq (ofSignature family tag data children).data data := castTerm_heq _ _

theorem ofSignature_children (family : RecursiveSpacePredicate.Contextual Symbol Γ)
    (tag : Term Symbol Γ family.number) (data : Term Symbol Γ family.payload)
    (children : Term Symbol Γ (family.number ⇒ family.space)) :
    HEq (ofSignature family tag data children).children children := castTerm_heq _ _

end Bindings

private theorem assumptions_congr {Γ : HOL.Ctx AtomicTy}
    {first second : RecursiveSpacePredicate.Contextual Symbol Γ} (same : first = second)
    {firstTag : Term Symbol Γ first.number} {secondTag : Term Symbol Γ second.number}
    {firstData : Term Symbol Γ first.payload} {secondData : Term Symbol Γ second.payload}
    {firstChildren : Term Symbol Γ (first.number ⇒ first.space)}
    {secondChildren : Term Symbol Γ (second.number ⇒ second.space)}
    (tag : HEq firstTag secondTag) (data : HEq firstData secondData) (children : HEq firstChildren secondChildren) :
    [first.shapeAt firstTag firstData, first.childConditions first.least firstData firstChildren] =
      [second.shapeAt secondTag secondData, second.childConditions second.least secondData secondChildren] := by
  cases same
  cases tag
  cases data
  cases children
  rfl

private theorem conclusion_congr {Γ : HOL.Ctx AtomicTy}
    {first second : RecursiveSpacePredicate.Contextual Symbol Γ} (same : first = second)
    {firstTag : Term Symbol Γ first.number} {secondTag : Term Symbol Γ second.number}
    {firstData : Term Symbol Γ first.payload} {secondData : Term Symbol Γ second.payload}
    {firstChildren : Term Symbol Γ (first.number ⇒ first.space)}
    {secondChildren : Term Symbol Γ (second.number ⇒ second.space)}
    (tag : HEq firstTag secondTag) (data : HEq firstData secondData) (children : HEq firstChildren secondChildren) :
    Term.app first.least (first.constructValue firstTag firstData firstChildren) =
      Term.app second.least (second.constructValue secondTag secondData secondChildren) := by
  cases same
  cases tag
  cases data
  cases children
  rfl

def compileForSignature (scopeName : String) {Γ : HOL.Ctx AtomicTy} (targetNames : Naming Γ)
    (family : RecursiveSpacePredicate.Contextual Symbol Γ)
    (tag : Term Symbol Γ family.number) (data : Term Symbol Γ family.payload)
    (children : Term Symbol Γ (family.number ⇒ family.space)) :
    RetainedCompilation.Compiled emptyAxiomPolicy @targetNames
      ([family.shapeAt tag data, family.childConditions family.least data children].map ImpredicativeConnectives.expand)
      (ImpredicativeConnectives.expand (.app family.least (family.constructValue tag data children))) := by
  let inputs := Bindings.ofSignature family tag data children
  let result := inputs.compile scopeName @targetNames
  have hypothesesSame := assumptions_congr (Bindings.ofSignature_signature family tag data children)
    (Bindings.ofSignature_tag family tag data children) (Bindings.ofSignature_data family tag data children)
    (Bindings.ofSignature_children family tag data children)
  have conclusionSame := conclusion_congr (Bindings.ofSignature_signature family tag data children)
    (Bindings.ofSignature_tag family tag data children) (Bindings.ofSignature_data family tag data children)
    (Bindings.ofSignature_children family tag data children)
  exact ⟨result.proof,
    result.hypotheses_exact.trans (congrArg (fun formulas => reverseHypotheses @targetNames
      (formulas.map ImpredicativeConnectives.expand)) hypothesesSame),
    result.conclusion_exact.trans (congrArg (fun formula => reverseCanonical @targetNames
      (ImpredicativeConnectives.expand formula)) conclusionSame)⟩

#print axioms proof_free
#print axioms instantiate
#print axioms image_conclusion
#print axioms image_assumptions
#print axioms compile
#print axioms Bindings.compile
#print axioms compileForSignature
end Parameters
end Mettapedia.Languages.HOLLight.RecursiveConstructorCompilation
