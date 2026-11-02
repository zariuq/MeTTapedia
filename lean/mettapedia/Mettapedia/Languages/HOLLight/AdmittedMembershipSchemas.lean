import Mettapedia.Languages.HOLLight.AdmittedMembershipCompilation
import Mettapedia.Languages.HOLLight.RecursiveConstructorCompilation
import Mettapedia.Languages.HOLLight.ParameterSchemaCompilation
import Mettapedia.Languages.HOLLight.AdmittedMembershipFraming

/-!
# Instantiating a shared constructor schema for admitted membership

The fixed-point proof is compiled at schematic carriers and operations.
Native type and term substitution specialize that certificate. Separate parent
shape and root proofs discharge the resulting premises; a short membership
join retains the child-condition hypothesis.

The total factory constructs an accepted certificate for every operation set
in the declared interface and proves its exact source sequent, retaining the
complete child-condition hypothesis. The supplied-template interface also
checks its final sequent before returning. Neither interface supplies the
remaining induction, elimination or datatype representation comparisons.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.HOLLight.AdmittedMembershipSchemas
open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open ReverseTranslation RetainedCompilation
open AdmittedMembershipCompilation
open Mettapedia.GSLT.LanguageDef

export AdmittedMembershipCompilation (NativeContext compiledParentShape compiledParentRoot parentShape parentRoot)


def template (scopeName : String) : CheckedProof emptyAxiomPolicy :=
  (RecursiveConstructorCompilation.compiledIntroduction (RecursiveConstructorCompilation.signature scopeName)
    (RecursiveConstructorCompilation.names (RecursiveConstructorCompilation.signature scopeName))).proof

namespace Join
abbrev space := RecursiveConstructorCompilation.space
abbrev index := RecursiveConstructorCompilation.number
abbrev context : HOL.Ctx AtomicTy := [space, index, .arr space .prop, .arr space (.arr index .prop)]
def point : HOL.Term Symbol context space := .var .vz
def target : HOL.Term Symbol context index := .var (.vs .vz)
def family : HOL.Term Symbol context (.arr space .prop) := .var (.vs (.vs .vz))
def root : HOL.Term Symbol context (.arr space (.arr index .prop)) := .var (.vs (.vs (.vs .vz)))
def premises : List (HOL.Formula Symbol context) := [.app family point, .app (.app root point) target]
def leftPremise : HOL.ProofSyntax Symbol premises (.app family point) := .hyp ⟨0, by decide⟩
def rightPremise : HOL.ProofSyntax Symbol premises (.app (.app root point) target) := .hyp ⟨1, by decide⟩
def proof : HOL.ProofSyntax Symbol premises (.app (.app (HOL.CurriedGuardProgramProofs.conjunctionProgram family root) point) target) :=
  .impE (.eqPropER (HOL.CurriedGuardProgramProofs.conjunctionProgram_beta family root point target))
    (.andI leftPremise rightPremise)
theorem proof_free : proof.FunctionExtensionalityFree := by
  exact ⟨HOL.CurriedGuardProgramProofs.conjunctionProgram_beta_free family root point target, True.intro, True.intro⟩
def names (scopeName : String) : Naming context :=
  Naming.cons (.global (scopeName ++ "_join_point")) (Naming.cons (.global (scopeName ++ "_join_target"))
    (Naming.cons (.global (scopeName ++ "_join_family")) (Naming.cons (.global (scopeName ++ "_join_root")) Naming.empty)))
open ReverseTranslation.VariableSchema
def parameterPoint : ParameterTerm context space := .var .vz
def parameterTarget : ParameterTerm context index := .var (.vs .vz)
def parameterFamily : ParameterTerm context (.arr space .prop) := .var (.vs (.vs .vz))
def parameterRoot : ParameterTerm context (.arr space (.arr index .prop)) := .var (.vs (.vs (.vs .vz)))
def parameterPremises : List (ParameterTerm context .prop) :=
  [.app parameterFamily parameterPoint, .app (.app parameterRoot parameterPoint) parameterTarget]
def parameterConclusion : ParameterTerm context .prop := .app
  (.app (HOL.CurriedGuardProgramProofs.conjunctionProgram parameterFamily parameterRoot) parameterPoint) parameterTarget
def expandedPremises := parameterPremises.map HOL.ImpredicativeConnectives.expand
def expandedConclusion := HOL.ImpredicativeConnectives.expand parameterConclusion

def schema (scopeName : String) : Compiled emptyAxiomPolicy (names scopeName)
    (expandedPremises.map embed) (embed expandedConclusion) :=
  RetainedCompilation.compileWithoutFunctionExtensionality emptyAxiomPolicy proof proof_free (names scopeName)
    ("admitted-membership-join-template", 0)

def template (scopeName : String) : CheckedProof emptyAxiomPolicy := (schema scopeName).proof

theorem names_distinct (types : TypeSubst) (scopeName : String) :
    Instantiation.KeysDistinct types (names scopeName) := by
  apply Instantiation.KeysDistinct.cons types (.global (scopeName ++ "_join_point"))
  · apply Instantiation.KeysDistinct.cons types (.global (scopeName ++ "_join_target"))
    · apply Instantiation.KeysDistinct.cons types (.global (scopeName ++ "_join_family"))
      · apply Instantiation.KeysDistinct.cons types (.global (scopeName ++ "_join_root"))
        · exact Instantiation.KeysDistinct.empty types
        · simp [Naming.toList]
      · simp [Naming.toList, Naming.cons, Name.global, String.append_right_inj]
    · simp [Naming.toList, Naming.cons, Name.global, String.append_right_inj]
  · simp [Naming.toList, Naming.cons, Name.global, String.append_right_inj]

def instantiate (types : TypeSubst) (scopeName : String) {Γ : HOL.Ctx AtomicTy}
    (targetNames : Naming Γ)
    (theta : HOL.Subst Symbol (context.map (HOL.Ty.substitute types.baseInstance)) Γ) :=
  ParameterSchemaCompilation.specialize types (names scopeName) targetNames theta
    (conclusion := expandedConclusion) (assumptions := expandedPremises)
    (schema scopeName) (names_distinct types scopeName) ("admitted-membership-join-instance", 0)

structure Values (types : TypeSubst) (Γ : HOL.Ctx AtomicTy) where
  family : HOL.Term Symbol Γ (HOL.Ty.substitute types.baseInstance (.arr space .prop))
  root : HOL.Term Symbol Γ (HOL.Ty.substitute types.baseInstance (.arr space (.arr index .prop)))
  point : HOL.Term Symbol Γ (HOL.Ty.substitute types.baseInstance space)
  target : HOL.Term Symbol Γ (HOL.Ty.substitute types.baseInstance index)

namespace Values
variable {types : TypeSubst} {Γ : HOL.Ctx AtomicTy} (values : Values types Γ)

def substitution : HOL.Subst Symbol (context.map (HOL.Ty.substitute types.baseInstance)) Γ :=
  HOL.Subst.cons values.point (HOL.Subst.cons values.target (HOL.Subst.cons values.family
    (HOL.Subst.cons values.root ((fun impossible => nomatch impossible) : HOL.Subst Symbol [] Γ))))
def premises : List (HOL.Formula Symbol Γ) :=
  [.app values.family values.point, .app (.app values.root values.point) values.target]
def conclusion : HOL.Formula Symbol Γ :=
  .app (.app (HOL.CurriedGuardProgramProofs.conjunctionProgram values.family values.root) values.point) values.target

theorem image_premises (scopeName : String) (targetNames : Naming Γ) :
    parameterPremises.map (ParameterSchemaCompilation.image types (@names scopeName) @targetNames values.substitution) =
      values.premises := by
  simp only [parameterPremises, List.map_cons, List.map_nil, ParameterSchemaCompilation.image_read,
    HOL.TermInterpretation.term_app]
  rfl

theorem image_conclusion (scopeName : String) (targetNames : Naming Γ) :
    ParameterSchemaCompilation.image types (@names scopeName) @targetNames values.substitution parameterConclusion =
      values.conclusion := by
  rw [ParameterSchemaCompilation.image_read]
  unfold parameterConclusion
  rw [HOL.TermInterpretation.term_app, HOL.TermInterpretation.term_app,
    HOL.CurriedGuardProgramProofs.read_conjunctionProgram]
  change HOL.Term.app (HOL.Term.app (HOL.subst values.substitution _) (HOL.subst values.substitution _))
    (HOL.subst values.substitution _) = _
  rw [HOL.CurriedGuardProgramProofs.subst_conjunctionProgram]
  rfl

def compile (scopeName : String) (targetNames : Naming Γ) :
    RetainedCompilation.Compiled emptyAxiomPolicy @targetNames
      (values.premises.map HOL.ImpredicativeConnectives.expand)
      (HOL.ImpredicativeConnectives.expand values.conclusion) := by
  let result := ParameterSchemaCompilation.specializeExpanded types (@names scopeName) @targetNames values.substitution
    (conclusion := parameterConclusion) (assumptions := parameterPremises)
    (schema scopeName) (names_distinct types scopeName) ("admitted-membership-join-instance", 0)
  exact ⟨result.proof,
    result.hypotheses_exact.trans (congrArg (fun formulas =>
      reverseHypotheses @targetNames (formulas.map HOL.ImpredicativeConnectives.expand))
      (image_premises values scopeName @targetNames)),
    result.conclusion_exact.trans (congrArg (fun formula =>
      reverseCanonical @targetNames (HOL.ImpredicativeConnectives.expand formula))
      (image_conclusion values scopeName @targetNames))⟩

open RecursiveConstructorCompilation.Parameters (carrierTypes carrier_number carrier_space castTerm castTerm_heq)

def ofTerms {number space : HOL.Ty AtomicTy}
    (family : HOL.Term Symbol Γ (.arr space .prop))
    (root : HOL.Term Symbol Γ (.arr space (.arr number .prop)))
    (point : HOL.Term Symbol Γ space) (target : HOL.Term Symbol Γ number) :
    Values (carrierTypes number space space) Γ where
  family := castTerm (by simp only [HOL.Ty.substitute_arr, HOL.Ty.substitute_prop, carrier_space]) family
  root := castTerm (by simp only [HOL.Ty.substitute_arr, HOL.Ty.substitute_prop, carrier_number, carrier_space]) root
  point := castTerm (carrier_space number space space).symm point
  target := castTerm (carrier_number number space space).symm target

theorem ofTerms_family {number space : HOL.Ty AtomicTy}
    (family : HOL.Term Symbol Γ (.arr space .prop)) (root : HOL.Term Symbol Γ (.arr space (.arr number .prop)))
    (point : HOL.Term Symbol Γ space) (target : HOL.Term Symbol Γ number) :
    HEq (ofTerms family root point target).family family := castTerm_heq _ _
theorem ofTerms_root {number space : HOL.Ty AtomicTy}
    (family : HOL.Term Symbol Γ (.arr space .prop)) (root : HOL.Term Symbol Γ (.arr space (.arr number .prop)))
    (point : HOL.Term Symbol Γ space) (target : HOL.Term Symbol Γ number) :
    HEq (ofTerms family root point target).root root := castTerm_heq _ _
theorem ofTerms_point {number space : HOL.Ty AtomicTy}
    (family : HOL.Term Symbol Γ (.arr space .prop)) (root : HOL.Term Symbol Γ (.arr space (.arr number .prop)))
    (point : HOL.Term Symbol Γ space) (target : HOL.Term Symbol Γ number) :
    HEq (ofTerms family root point target).point point := castTerm_heq _ _
theorem ofTerms_target {number space : HOL.Ty AtomicTy}
    (family : HOL.Term Symbol Γ (.arr space .prop)) (root : HOL.Term Symbol Γ (.arr space (.arr number .prop)))
    (point : HOL.Term Symbol Γ space) (target : HOL.Term Symbol Γ number) :
    HEq (ofTerms family root point target).target target := castTerm_heq _ _

end Values

private theorem premises_congr {Γ : HOL.Ctx AtomicTy} {n m s t : HOL.Ty AtomicTy}
    (numbers : n = m) (spaces : s = t)
    {p : HOL.Term Symbol Γ (.arr s .prop)} {q : HOL.Term Symbol Γ (.arr t .prop)}
    {r : HOL.Term Symbol Γ (.arr s (.arr n .prop))} {v : HOL.Term Symbol Γ (.arr t (.arr m .prop))}
    {a : HOL.Term Symbol Γ s} {b : HOL.Term Symbol Γ t}
    {i : HOL.Term Symbol Γ n} {j : HOL.Term Symbol Γ m}
    (family : HEq p q) (root : HEq r v) (point : HEq a b) (target : HEq i j) :
    [HOL.Term.app p a, .app (.app r a) i] = [HOL.Term.app q b, .app (.app v b) j] := by
  cases numbers; cases spaces; cases family; cases root; cases point; cases target; rfl

private theorem conclusion_congr {Γ : HOL.Ctx AtomicTy} {n m s t : HOL.Ty AtomicTy}
    (numbers : n = m) (spaces : s = t)
    {p : HOL.Term Symbol Γ (.arr s .prop)} {q : HOL.Term Symbol Γ (.arr t .prop)}
    {r : HOL.Term Symbol Γ (.arr s (.arr n .prop))} {v : HOL.Term Symbol Γ (.arr t (.arr m .prop))}
    {a : HOL.Term Symbol Γ s} {b : HOL.Term Symbol Γ t}
    {i : HOL.Term Symbol Γ n} {j : HOL.Term Symbol Γ m}
    (family : HEq p q) (root : HEq r v) (point : HEq a b) (target : HEq i j) :
    HOL.Term.app (.app (HOL.CurriedGuardProgramProofs.conjunctionProgram p r) a) i =
      HOL.Term.app (.app (HOL.CurriedGuardProgramProofs.conjunctionProgram q v) b) j := by
  cases numbers; cases spaces; cases family; cases root; cases point; cases target; rfl

def compileFor {Γ : HOL.Ctx AtomicTy} {number space : HOL.Ty AtomicTy} (scopeName : String) (targetNames : Naming Γ)
    (family : HOL.Term Symbol Γ (.arr space .prop)) (root : HOL.Term Symbol Γ (.arr space (.arr number .prop)))
    (point : HOL.Term Symbol Γ space) (target : HOL.Term Symbol Γ number) :
    RetainedCompilation.Compiled emptyAxiomPolicy @targetNames
      ([HOL.Term.app family point, .app (.app root point) target].map HOL.ImpredicativeConnectives.expand)
      (HOL.ImpredicativeConnectives.expand (.app
        (.app (HOL.CurriedGuardProgramProofs.conjunctionProgram family root) point) target)) := by
  let values := Values.ofTerms family root point target
  let result := values.compile scopeName @targetNames
  have numbers := RecursiveConstructorCompilation.Parameters.carrier_number number space space
  have spaces := RecursiveConstructorCompilation.Parameters.carrier_space number space space
  have hypothesesSame := premises_congr numbers spaces (Values.ofTerms_family family root point target)
    (Values.ofTerms_root family root point target) (Values.ofTerms_point family root point target)
    (Values.ofTerms_target family root point target)
  have conclusionSame := conclusion_congr numbers spaces (Values.ofTerms_family family root point target)
    (Values.ofTerms_root family root point target) (Values.ofTerms_point family root point target)
    (Values.ofTerms_target family root point target)
  exact ⟨result.proof,
    result.hypotheses_exact.trans (congrArg (fun formulas => reverseHypotheses @targetNames
      (formulas.map HOL.ImpredicativeConnectives.expand)) hypothesesSame),
    result.conclusion_exact.trans (congrArg (fun formula => reverseCanonical @targetNames
      (HOL.ImpredicativeConnectives.expand formula)) conclusionSame)⟩
end Join

def typedReplacement {Γ : HOL.Ctx AtomicTy} {type : HOL.Ty AtomicTy}
    (names : Naming Γ) (name : String) (term : HOL.Term Symbol Γ type) :
    {entry : SourceVar × CheckedSourceTerm // entry.2.ty = entry.1.ty} :=
  let canonical := reverseCanonical names (HOL.ImpredicativeConnectives.expand term)
  ⟨(⟨.global name, canonical.ty⟩, PrimitiveTransport.checkedSource canonical), by
    exact congrArg CanonicalTerm.ty (PrimitiveTransport.checkedSource_exact canonical)⟩

variable (operations : Operations) (callerNames : Naming (NativeContext operations))

def replacements (scopeName : String) := [
  typedReplacement callerNames (scopeName ++ "_bottom") ((interpretation operations).term descriptor.bottom),
  typedReplacement callerNames (scopeName ++ "_construct") ((interpretation operations).term descriptor.construct),
  typedReplacement callerNames (scopeName ++ "_shape") ((interpretation operations).term descriptor.validShape),
  typedReplacement callerNames (scopeName ++ "_active") ((interpretation operations).term descriptor.active),
  typedReplacement callerNames (scopeName ++ "_edge") ((interpretation operations).term descriptor.validEdge),
  typedReplacement callerNames "__constructor_tag" ((interpretation operations).term tag),
  typedReplacement callerNames "__constructor_payload" ((interpretation operations).term data),
  typedReplacement callerNames "__constructor_children" ((interpretation operations).term children)]

def specializationTypes : TypeSubst :=
  ⟨[(.global "__schema_number", reverseTy operations.number),
    (.global "__schema_payload", reverseTy (HOL.Ty.substitute (types operations) descriptor.payload)),
    (.global "__schema_space", reverseTy operations.space)]⟩

def specialization (scopeName : String) : TypeCorrectTermSubstitution where
  raw := ⟨specializationTypes operations,
    (replacements operations callerNames scopeName).map Subtype.val⟩
  typeCorrect := by
    intro entry member
    obtain ⟨typed, _, rfl⟩ := List.mem_map.mp member
    exact typed.property

def applySpecialization (mapping : TypeCorrectTermSubstitution) (schema : CheckedProof emptyAxiomPolicy) : CheckedProof emptyAxiomPolicy :=
  CheckedProof.unary schema (substituteTheorem mapping schema.result)
    (PrimitiveTransport.substitutionBlock mapping schema.result ("admitted-constructor-instance", 0))
    (PrimitiveTransport.substitutionBlock_checked emptyAxiomPolicy mapping schema.result ("admitted-constructor-instance", 0))
    ("admitted-constructor-instance", 0)

def specialized (scopeName : String) (schema : CheckedProof emptyAxiomPolicy) : CheckedProof emptyAxiomPolicy :=
  applySpecialization (specialization operations callerNames scopeName) schema

def joinReplacements (scopeName : String) := [
  typedReplacement callerNames (scopeName ++ "_join_family") ((interpretation operations).term descriptor.least),
  typedReplacement callerNames (scopeName ++ "_join_root") ((interpretation operations).term rootTerm),
  typedReplacement callerNames (scopeName ++ "_join_point")
    ((interpretation operations).term (descriptor.constructValue tag data children)),
  typedReplacement callerNames (scopeName ++ "_join_target") ((interpretation operations).term target)]

def joinSpecialization (scopeName : String) : TypeCorrectTermSubstitution where
  raw := ⟨specializationTypes operations,
    (joinReplacements operations callerNames scopeName).map Subtype.val⟩
  typeCorrect := by
    intro entry member
    obtain ⟨typed, _, rfl⟩ := List.mem_map.mp member
    exact typed.property

def proveHypothesis (proved input : CheckedProof emptyAxiomPolicy)
    (sameType : proved.result.sequent.concl.ty = input.result.sequent.concl.ty) : CheckedProof emptyAxiomPolicy :=
  CheckedProof.binary proved input (HypothesisExpansion.proveHypResult proved.result input.result)
    (HypothesisExpansion.proveHypBlock proved.result input.result sameType ("admitted-parent-premise", 0))
    (HypothesisExpansion.proveHypBlock_checked emptyAxiomPolicy proved.result input.result sameType
      ("admitted-parent-premise", 0)) ("admitted-parent-premise", 0)


def memberJoin (scopeName : String) : CheckedProof emptyAxiomPolicy :=
  applySpecialization (joinSpecialization operations callerNames scopeName) (Join.template scopeName)

@[noinline] opaque compiledConstructor (scopeName : String) : Compiled emptyAxiomPolicy @callerNames
    ([ (interpretation operations).term (descriptor.shapeAt tag data),
       (interpretation operations).term conditions ].map HOL.ImpredicativeConnectives.expand)
    (HOL.ImpredicativeConnectives.expand ((interpretation operations).term
      (.app descriptor.least (descriptor.constructValue tag data children)))) := by
  let reading := interpretation operations
  let family := descriptor.read reading
  let result := RecursiveConstructorCompilation.Parameters.compileForSignature scopeName @callerNames family
    (reading.term tag) (reading.term data) (reading.term children)
  have shapeSame : family.shapeAt (reading.term tag) (reading.term data) = reading.term (descriptor.shapeAt tag data) :=
    (HOL.RecursiveSpacePredicate.Contextual.read_shapeAt descriptor reading tag data).symm
  have childSame : family.childConditions family.least (reading.term data) (reading.term children) =
      reading.term conditions := by
    unfold conditions
    rw [HOL.RecursiveSpacePredicate.Contextual.read_childConditions, HOL.RecursiveSpacePredicate.Contextual.read_least]
  have conclusionSame : HOL.Term.app family.least
      (family.constructValue (reading.term tag) (reading.term data) (reading.term children)) =
      reading.term (.app descriptor.least (descriptor.constructValue tag data children)) := by
    rw [HOL.TermInterpretation.term_app, HOL.RecursiveSpacePredicate.Contextual.read_least,
      HOL.RecursiveSpacePredicate.Contextual.read_constructValue]
  exact ⟨result.proof,
    result.hypotheses_exact.trans (congrArg (fun (formulas : List (HOL.Formula Symbol (NativeContext operations))) => reverseHypotheses @callerNames
      (formulas.map HOL.ImpredicativeConnectives.expand)) (by rw [shapeSame, childSame])),
    result.conclusion_exact.trans (congrArg (fun (formula : HOL.Formula Symbol (NativeContext operations)) => reverseCanonical @callerNames
      (HOL.ImpredicativeConnectives.expand formula)) conclusionSame)⟩

@[noinline] opaque compiledJoin (scopeName : String) : Compiled emptyAxiomPolicy @callerNames
    ([ (interpretation operations).term (.app descriptor.least (descriptor.constructValue tag data children)),
       (interpretation operations).term (.app (.app rootTerm (descriptor.constructValue tag data children)) target) ].map
      HOL.ImpredicativeConnectives.expand)
    (HOL.ImpredicativeConnectives.expand ((interpretation operations).term conclusion)) := by
  let reading := interpretation operations
  let point := reading.term (descriptor.constructValue tag data children)
  let result := Join.compileFor scopeName @callerNames (reading.term descriptor.least) (reading.term rootTerm)
    point (reading.term target)
  have hypothesesSame : [HOL.Term.app (reading.term descriptor.least) point,
      .app (.app (reading.term rootTerm) point) (reading.term target)] =
      [reading.term (.app descriptor.least (descriptor.constructValue tag data children)),
       reading.term (.app (.app rootTerm (descriptor.constructValue tag data children)) target)] := by
    rw [HOL.TermInterpretation.term_app, HOL.TermInterpretation.term_app, HOL.TermInterpretation.term_app]
  have conclusionSame : HOL.Term.app
      (.app (HOL.CurriedGuardProgramProofs.conjunctionProgram (reading.term descriptor.least) (reading.term rootTerm)) point)
      (reading.term target) = reading.term conclusion := by
    unfold conclusion
    rw [HOL.TermInterpretation.term_app, HOL.TermInterpretation.term_app,
      HOL.RecursiveSpacePredicate.Contextual.read_memberProgram]
    simp only [HOL.RecursiveSpacePredicate.Contextual.memberProgram, HOL.RecursiveSpacePredicate.Contextual.read_least]
    rfl
  exact ⟨result.proof,
    result.hypotheses_exact.trans (congrArg (fun (formulas : List (HOL.Formula Symbol (NativeContext operations))) => reverseHypotheses @callerNames
      (formulas.map HOL.ImpredicativeConnectives.expand)) hypothesesSame),
    result.conclusion_exact.trans (congrArg (fun (formula : HOL.Formula Symbol (NativeContext operations)) => reverseCanonical @callerNames
      (HOL.ImpredicativeConnectives.expand formula)) conclusionSame)⟩

def sourceSequent : Sequent :=
  ⟨reverseHypotheses callerNames
    ([conditions].map (interpretation operations).term |>.map HOL.ImpredicativeConnectives.expand),
   reverseCanonical callerNames (HOL.ImpredicativeConnectives.expand ((interpretation operations).term conclusion))⟩

structure Result where
  proof : CheckedProof emptyAxiomPolicy
  source_exact : proof.result.sequent = sourceSequent operations callerNames

def fromTemplate? (scopeName : String) (schema : CheckedProof emptyAxiomPolicy) : Option (Result operations callerNames) := do
  let specialized := specialized operations callerNames scopeName schema
  let shape := parentShape operations callerNames
  if shapeType : Ty.same shape.result.sequent.concl.ty specialized.result.sequent.concl.ty = true then
    let least := proveHypothesis shape specialized ((Ty.same_eq_true_iff _ _).mp shapeType)
    let joined := memberJoin operations callerNames scopeName
    if leastType : Ty.same least.result.sequent.concl.ty joined.result.sequent.concl.ty = true then
      let joinedLeast := proveHypothesis least joined ((Ty.same_eq_true_iff _ _).mp leastType)
      let root := parentRoot operations callerNames
      if rootType : Ty.same root.result.sequent.concl.ty joinedLeast.result.sequent.concl.ty = true then
        let complete := proveHypothesis root joinedLeast ((Ty.same_eq_true_iff _ _).mp rootType)
        if exactSource : complete.result.sequent = sourceSequent operations callerNames then
          some ⟨complete, exactSource⟩
        else none
      else none
    else none
  else none

def compileTotal (scopeName : String) : Result operations callerNames := by
  let constructor := compiledConstructor operations @callerNames scopeName
  let shape := compiledParentShape operations @callerNames
  let least := proveHypothesis shape.proof constructor.proof (shape.boolean.trans constructor.boolean.symm)
  let joined := compiledJoin operations @callerNames scopeName
  let joinedLeast := proveHypothesis least joined.proof (constructor.boolean.trans joined.boolean.symm)
  let root := compiledParentRoot operations @callerNames
  let complete := proveHypothesis root.proof joinedLeast (root.boolean.trans joined.boolean.symm)
  let condition := AdmittedMembershipFraming.conditionCode operations @callerNames
  have shapeEmpty : shape.proof.result.sequent.hyp = ∅ := shape.hypotheses_exact
  have rootEmpty : root.proof.result.sequent.hyp = ∅ := root.hypotheses_exact
  have constructorHyps : constructor.proof.result.sequent.hyp = {shape.proof.result.sequent.concl, condition} := by
    rw [constructor.hypotheses_exact, shape.conclusion_exact]
    simp only [reverseHypotheses, List.map_cons, List.map_nil, List.toFinset_cons, List.toFinset_nil,
      Finset.insert_empty, condition, AdmittedMembershipFraming.conditionCode]
  have joinedHyps : joined.proof.result.sequent.hyp = {constructor.proof.result.sequent.concl, root.proof.result.sequent.concl} := by
    rw [joined.hypotheses_exact, constructor.conclusion_exact, root.conclusion_exact]
    simp only [reverseHypotheses, List.map_cons, List.map_nil, List.toFinset_cons, List.toFinset_nil, Finset.insert_empty]
  have conditionShape : condition ≠ shape.proof.result.sequent.concl := by
    intro same
    apply AdmittedMembershipFraming.condition_ne_parentShape operations @callerNames
    exact same.trans (congrArg (fun proof : CheckedProof emptyAxiomPolicy => proof.result.sequent.concl)
      (AdmittedMembershipFraming.parentShape_eq_compiled operations @callerNames)).symm
  have conditionRoot : condition ≠ root.proof.result.sequent.concl := by
    intro same
    apply AdmittedMembershipFraming.condition_ne_parentRoot operations @callerNames
    exact same.trans (congrArg (fun proof : CheckedProof emptyAxiomPolicy => proof.result.sequent.concl)
      (AdmittedMembershipFraming.parentRoot_eq_compiled operations @callerNames)).symm
  have completeHypotheses : complete.result.sequent.hyp = {condition} :=
    AdmittedMembershipFraming.three_discharge_hypotheses shape.proof.result constructor.proof.result joined.proof.result
      root.proof.result condition shapeEmpty constructorHyps joinedHyps rootEmpty conditionShape conditionRoot
  refine ⟨complete, Sequent.ext ?_ ?_⟩
  · apply completeHypotheses.trans
    simp only [sourceSequent, reverseHypotheses, List.map_cons, List.map_nil, List.toFinset_cons,
      List.toFinset_nil, Finset.insert_empty, condition, AdmittedMembershipFraming.conditionCode]
  · exact joined.conclusion_exact

def compile? (scopeName : String) : Option (Result operations callerNames) :=
  some (compileTotal operations @callerNames scopeName)

theorem compile?_available (scopeName : String) :
    ∃ result, compile? operations @callerNames scopeName = some result :=
  ⟨compileTotal operations @callerNames scopeName, rfl⟩

theorem Result.accepted (result : Result operations callerNames) :
    (ProofSystem.checker emptyAxiomPolicy).check result.proof.result result.proof.certificate = true :=
  result.proof.accepted

theorem Result.source_conclusion (result : Result operations callerNames) :
    result.proof.result.sequent.concl = reverseCanonical callerNames
      (HOL.ImpredicativeConnectives.expand ((interpretation operations).term
        (.app (.app AdmittedContainerProofControls.Open.program AdmittedContainerProofControls.Open.value)
          AdmittedContainerProofControls.Open.index))) := by
  simpa only [sourceSequent, cons_conclusion_source] using congrArg Sequent.concl result.source_exact

theorem Result.source_hypotheses (result : Result operations callerNames) :
    result.proof.result.sequent.hyp = reverseHypotheses callerNames
      ([AdmittedContainerProofControls.Open.conditions].map (interpretation operations).term |>.map HOL.ImpredicativeConnectives.expand) := by
  simpa only [sourceSequent, cons_hypothesis_source] using congrArg Sequent.hyp result.source_exact

#print axioms Result.accepted
#print axioms Result.source_conclusion
#print axioms Result.source_hypotheses
#print axioms compileTotal
end Mettapedia.Languages.HOLLight.AdmittedMembershipSchemas
