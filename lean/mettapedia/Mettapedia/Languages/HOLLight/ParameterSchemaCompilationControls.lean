import Mettapedia.Languages.HOLLight.ParameterSchemaCompilation
import Mettapedia.Languages.HOLLight.RecursiveConstructorCompilation
import Mettapedia.Languages.HOLLight.AdmittedMembershipSchemas

/-!
# Parameter-schema specialization with collapsed source carriers

Two distinct source types become propositions. Their parameter positions and
names remain distinct. A reflexivity schema contains both parameters beneath
a higher-order binder and specializes through the actual native graph builder.
Using the same name for both source parameters fails the post-type-key test.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.HOLLight.ParameterSchemaCompilationControls
open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open ReverseTranslation VariableSchema RetainedCompilation

def first : HOL.Ty AtomicTy := .base (RecursiveConstructorCompilation.atomic "__parameter_first")
def second : HOL.Ty AtomicTy := .base (RecursiveConstructorCompilation.atomic "__parameter_second")
abbrev context : HOL.Ctx AtomicTy := [first, second]
def types : TypeSubst :=
  ⟨[(.global "__parameter_first", .bool), (.global "__parameter_second", .bool)]⟩

theorem first_image : HOL.Ty.substitute types.baseInstance first = .prop := by
  simp [first, types, RecursiveConstructorCompilation.atomic,
    TypeSubst.baseInstance, TypeSubst.lookup, Name.global]

theorem second_image : HOL.Ty.substitute types.baseInstance second = .prop := by
  simp [second, types, RecursiveConstructorCompilation.atomic,
    TypeSubst.baseInstance, TypeSubst.lookup, List.lookup_cons, Name.global]
  split <;> simp

theorem types_collide : first ≠ second ∧
    HOL.Ty.substitute types.baseInstance first = HOL.Ty.substitute types.baseInstance second := by
  refine ⟨?_, first_image.trans second_image.symm⟩
  intro same
  have different := congrArg reverseTy same
  change Ty.var (.global "__parameter_first") = Ty.var (.global "__parameter_second") at different
  exact (by decide : ("__parameter_first" : String) ≠ "__parameter_second")
    (congrArg Name.component (Ty.var.inj different))

def names : Naming context := Naming.cons (.global "x") (Naming.cons (.global "y") Naming.empty)
def targetNames : Naming (context.map (HOL.Ty.substitute types.baseInstance)) := Naming.mapTypes types names
def theta : HOL.Subst Symbol (context.map (HOL.Ty.substitute types.baseInstance))
    (context.map (HOL.Ty.substitute types.baseInstance)) := fun index => .var index

theorem keys_distinct : Instantiation.KeysDistinct types names := by
  apply Instantiation.KeysDistinct.cons types (.global "x")
  · apply Instantiation.KeysDistinct.cons types (.global "y")
    · exact Instantiation.KeysDistinct.empty types
    · simp [Naming.toList]
  · simp [Naming.toList, Naming.cons, Name.global]

def term : ParameterTerm context (.arr (.arr first (.arr second .prop)) .prop) :=
  .lam (.app (.app (.var .vz) (.var (.vs .vz))) (.var (.vs (.vs .vz))))
def conclusion : ParameterTerm context .prop := .eq term term
def sourceProof : HOL.ProofSyntax Symbol [] (embed conclusion) := .eqRefl (embed term)
theorem sourceProof_free : sourceProof.FunctionExtensionalityFree := by trivial

def schema : Compiled emptyAxiomPolicy names [] (embed conclusion) :=
  RetainedCompilation.compileWithoutFunctionExtensionality emptyAxiomPolicy sourceProof sourceProof_free names
    ("parameter-source", 0)

def compiled : Compiled emptyAxiomPolicy targetNames []
    (ParameterSchemaCompilation.image types names targetNames theta conclusion) :=
  ParameterSchemaCompilation.specialize types names targetNames theta
    (conclusion := conclusion) (assumptions := []) schema keys_distinct ("parameter-collapsed", 0)

theorem accepted : (ProofSystem.checker emptyAxiomPolicy).check
    compiled.proof.result compiled.proof.certificate = true := compiled.proof.accepted

theorem exact_conclusion : compiled.proof.result.sequent.concl =
    reverseCanonical targetNames (ParameterSchemaCompilation.image types names targetNames theta conclusion) :=
  compiled.conclusion_exact

theorem hypotheses_empty : compiled.proof.result.sequent.hyp = ∅ := by
  simpa only [reverseHypotheses_nil] using compiled.hypotheses_exact

def guardedSourceProof : HOL.ProofSyntax Symbol [embed conclusion] (embed conclusion) := .hyp ⟨0, by decide⟩
theorem guardedSourceProof_free : guardedSourceProof.FunctionExtensionalityFree := by trivial

def guardedSchema : Compiled emptyAxiomPolicy names [embed conclusion] (embed conclusion) :=
  RetainedCompilation.compileWithoutFunctionExtensionality emptyAxiomPolicy
    guardedSourceProof guardedSourceProof_free names ("parameter-guarded-source", 0)

def guarded : Compiled emptyAxiomPolicy targetNames
    [ParameterSchemaCompilation.image types names targetNames theta conclusion]
    (ParameterSchemaCompilation.image types names targetNames theta conclusion) :=
  ParameterSchemaCompilation.specialize types names targetNames theta
    (conclusion := conclusion) (assumptions := [conclusion]) guardedSchema keys_distinct ("parameter-guarded", 0)

theorem guarded_accepted : (ProofSystem.checker emptyAxiomPolicy).check
    guarded.proof.result guarded.proof.certificate = true := guarded.proof.accepted

theorem guard_retained : guarded.proof.result.sequent.hyp =
    {reverseCanonical targetNames (ParameterSchemaCompilation.image types names targetNames theta conclusion)} := by
  simpa only [reverseHypotheses, List.map_cons, List.map_nil, List.toFinset_cons, List.toFinset_nil,
    Finset.insert_empty] using guarded.hypotheses_exact

def swap : HOL.Subst Symbol [.prop, .prop] [.prop, .prop]
  | _, .vz => .var (.vs .vz)
  | _, .vs .vz => .var .vz

def swappedTheta : HOL.Subst Symbol (context.map (HOL.Ty.substitute types.baseInstance))
    (context.map (HOL.Ty.substitute types.baseInstance)) := by
  simpa only [context, List.map_cons, List.map_nil, first_image, second_image] using @swap

def swapped : Compiled emptyAxiomPolicy targetNames []
    (ParameterSchemaCompilation.image types names targetNames swappedTheta conclusion) :=
  ParameterSchemaCompilation.specialize types names targetNames swappedTheta
    (conclusion := conclusion) (assumptions := []) schema keys_distinct ("parameter-swapped", 0)

theorem swapped_accepted : (ProofSystem.checker emptyAxiomPolicy).check
    swapped.proof.result swapped.proof.certificate = true := swapped.proof.accepted

def aliasedNames : Naming context := Naming.cons (.global "same") (Naming.cons (.global "same") Naming.empty)

theorem aliased_keys_collide :
    Instantiation.key types aliasedNames (HOL.Var.vz : HOL.Var context first) =
      Instantiation.key types aliasedNames (HOL.Var.vs .vz : HOL.Var context second) := by
  simp only [Instantiation.key, aliasedNames, Naming.cons, first_image, second_image]

theorem aliased_keys_refused : ¬ Instantiation.KeysDistinct types aliasedNames := by
  intro distinct
  have impossible := distinct (HOL.Var.vz : HOL.Var context first)
    (HOL.Var.vs .vz : HOL.Var context second) aliased_keys_collide
  cases impossible

#print axioms types_collide
#print axioms keys_distinct
#print axioms accepted
#print axioms exact_conclusion
#print axioms guarded_accepted
#print axioms guard_retained
#print axioms swapped_accepted
#print axioms aliased_keys_refused

namespace Constructor
abbrev context : HOL.Ctx AtomicTy := [.arr .prop .prop, .prop, .prop,
  .arr .prop (.arr .prop (.arr .prop .prop)), .arr .prop (.arr .prop .prop),
  .arr .prop (.arr .prop .prop), .arr .prop (.arr .prop (.arr (.arr .prop .prop) .prop)), .prop]

def signature : HOL.RecursiveSpacePredicate.Contextual Symbol context where
  number := .prop
  payload := .prop
  space := .prop
  bottom := .var (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))
  construct := .var (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))
  validShape := .var (.vs (.vs (.vs (.vs .vz))))
  active := .var (.vs (.vs (.vs (.vs (.vs .vz)))))
  validEdge := .var (.vs (.vs (.vs .vz)))

def tag : HOL.Term Symbol context .prop := .var (.vs .vz)
def data : HOL.Term Symbol context .prop := .var (.vs (.vs .vz))
def children : HOL.Term Symbol context (.arr .prop .prop) := .var .vz
def names : Naming context := Naming.cons (.global "__cross_constructor_children")
  (Naming.cons (.global "__cross_constructor_payload") (Naming.cons (.global "__cross_constructor_tag")
    (Naming.cons (.global "__cross_constructor_edge") (Naming.cons (.global "__cross_constructor_active")
      (Naming.cons (.global "__cross_constructor_shape") (Naming.cons (.global "__cross_constructor_construct")
        (Naming.cons (.global "__cross_constructor_bottom") Naming.empty)))))))

def compiled := RecursiveConstructorCompilation.Parameters.compileForSignature "__cross_constructor" @names
  signature tag data children

def expected : Sequent :=
  ⟨reverseHypotheses @names ([signature.shapeAt tag data,
      signature.childConditions signature.least data children].map HOL.ImpredicativeConnectives.expand),
    reverseCanonical @names (HOL.ImpredicativeConnectives.expand
      (.app signature.least (signature.constructValue tag data children)))⟩

theorem source_exact : compiled.proof.result.sequent = expected :=
  Sequent.ext compiled.hypotheses_exact compiled.conclusion_exact

theorem accepted : (ProofSystem.checker emptyAxiomPolicy).check compiled.proof.result compiled.proof.certificate = true :=
  compiled.proof.accepted

def emptySignature : HOL.RecursiveSpacePredicate.Contextual Symbol context :=
  {signature with validShape := .lam (.lam .bot)}

def emptyCompiled := RecursiveConstructorCompilation.Parameters.compileForSignature "__empty_constructor" @names
  emptySignature tag data children

def emptyExpected : Sequent :=
  ⟨reverseHypotheses @names ([emptySignature.shapeAt tag data,
      emptySignature.childConditions emptySignature.least data children].map HOL.ImpredicativeConnectives.expand),
    reverseCanonical @names (HOL.ImpredicativeConnectives.expand
      (.app emptySignature.least (emptySignature.constructValue tag data children)))⟩

theorem empty_source_exact : emptyCompiled.proof.result.sequent = emptyExpected :=
  Sequent.ext emptyCompiled.hypotheses_exact emptyCompiled.conclusion_exact

theorem empty_accepted : (ProofSystem.checker emptyAxiomPolicy).check
    emptyCompiled.proof.result emptyCompiled.proof.certificate = true := emptyCompiled.proof.accepted

theorem complete_available (operations : AdmittedMembershipCompilation.Operations)
    (callerNames : Naming (AdmittedMembershipCompilation.NativeContext operations)) (scopeName : String) :
    ∃ result, AdmittedMembershipSchemas.compile? operations @callerNames scopeName = some result :=
  AdmittedMembershipSchemas.compile?_available operations @callerNames scopeName

#print axioms source_exact
#print axioms accepted
#print axioms empty_source_exact
#print axioms empty_accepted
#print axioms complete_available
end Constructor

end Mettapedia.Languages.HOLLight.ParameterSchemaCompilationControls
