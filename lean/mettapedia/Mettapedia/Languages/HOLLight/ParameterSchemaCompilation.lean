import Mettapedia.Languages.OpenTheory.VariableSchemaInstantiation
import Mettapedia.Languages.HOLLight.RetainedCompilation

/-!
# Total native specialization of typed parameter schemas

Parameter images are constructed by the existing checked named-term reader.
The resulting native map specializes an accepted schema with two primitive
inferences. Its hypotheses and conclusion are the exact typed HOL images.
Hypotheses retain the existing finite-set observation contract.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.ParameterSchemaCompilation
open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open ReverseTranslation VariableSchema RetainedCompilation

variable (types : TypeSubst) {Γ Δ : HOL.Ctx AtomicTy}
    (sourceNames : Naming Γ) (targetNames : Naming Δ)
    (theta : HOL.Subst Symbol (Γ.map (HOL.Ty.substitute types.baseInstance)) Δ)

def images : Instantiation.Images types Γ := fun index =>
  let canonical := reverseCanonical targetNames (theta (index.mapTypes types.baseInstance))
  ⟨PrimitiveTransport.checkedSource canonical,
    congrArg CanonicalTerm.ty (PrimitiveTransport.checkedSource_exact canonical)⟩

def mapping : TypeCorrectTermSubstitution :=
  Instantiation.mapping types sourceNames (images types targetNames theta)

theorem canonical {type : HOL.Ty AtomicTy} (term : ParameterTerm Γ type)
    (distinct : Instantiation.KeysDistinct types sourceNames) :
    (mapping types sourceNames targetNames theta).apply (reverseCanonical sourceNames (embed term)) =
      reverseCanonical targetNames
        (HOL.subst theta (mapped (mapping types sourceNames targetNames theta).raw term)) :=
  Instantiation.canonical types term sourceNames targetNames (images types targetNames theta) distinct theta
    (fun _ => PrimitiveTransport.checkedSource_exact _)

def image {type : HOL.Ty AtomicTy} (term : ParameterTerm Γ type) : HOL.Term Symbol Δ
    (HOL.Ty.substitute types.baseInstance type) :=
  HOL.subst theta (mapped (mapping types sourceNames targetNames theta).raw term)

theorem image_read {type : HOL.Ty AtomicTy} (term : ParameterTerm Γ type) :
    image types sourceNames targetNames theta term = HOL.subst theta ((reading types).term term) := by
  unfold image
  rw [mapped_read]
  rfl

theorem image_expand {type : HOL.Ty AtomicTy} (term : ParameterTerm Γ type) :
    image types sourceNames targetNames (fun index => HOL.ImpredicativeConnectives.expand (theta index))
      (HOL.ImpredicativeConnectives.expand term) =
        HOL.ImpredicativeConnectives.expand (image types sourceNames targetNames theta term) := by
  change HOL.subst (fun index => HOL.ImpredicativeConnectives.expand (theta index))
      (HOL.mapTypes types.baseInstance (fun impossible => nomatch impossible)
        (HOL.ImpredicativeConnectives.expand term)) =
    HOL.ImpredicativeConnectives.expand (HOL.subst theta
      (HOL.mapTypes types.baseInstance (fun impossible => nomatch impossible) term))
  rw [HOL.ImpredicativeConnectives.mapTypes_expand, HOL.ImpredicativeConnectives.expand_subst]

theorem hypotheses (formulas : List (ParameterTerm Γ .prop))
    (distinct : Instantiation.KeysDistinct types sourceNames) :
    (mapping types sourceNames targetNames theta).applyHypotheses
      (reverseHypotheses sourceNames (formulas.map embed)) =
        reverseHypotheses targetNames (formulas.map (image types sourceNames targetNames theta)) := by
  classical
  ext result
  constructor
  · intro inImage
    obtain ⟨_, nativeMember, rfl⟩ := Finset.mem_image.mp inImage
    obtain ⟨_, formulaMember, rfl⟩ := mem_reverseHypotheses.mp nativeMember
    obtain ⟨formula, parameterMember, rfl⟩ := List.mem_map.mp formulaMember
    apply mem_reverseHypotheses.mpr
    refine ⟨_, List.mem_map.mpr ⟨formula, parameterMember, rfl⟩, ?_⟩
    exact (canonical types sourceNames targetNames theta formula distinct).symm
  · intro inTarget
    obtain ⟨_, formulaMember, rfl⟩ := mem_reverseHypotheses.mp inTarget
    obtain ⟨formula, parameterMember, rfl⟩ := List.mem_map.mp formulaMember
    apply Finset.mem_image.mpr
    refine ⟨_, mem_reverseHypotheses.mpr ⟨_, List.mem_map.mpr ⟨formula, parameterMember, rfl⟩, rfl⟩, ?_⟩
    exact canonical types sourceNames targetNames theta formula distinct

variable {policy : AxiomPolicy} [DecidablePred policy]

def specialize {conclusion : ParameterTerm Γ .prop} {assumptions : List (ParameterTerm Γ .prop)}
    (schema : Compiled policy sourceNames (assumptions.map embed) (embed conclusion))
    (distinct : Instantiation.KeysDistinct types sourceNames) (origin : ProofExecution.Origin) :
    Compiled policy targetNames (assumptions.map (image types sourceNames targetNames theta))
      (image types sourceNames targetNames theta conclusion) := by
  let substitution := mapping types sourceNames targetNames theta
  let proof := CheckedProof.unary schema.proof (substituteTheorem substitution schema.proof.result)
    (PrimitiveTransport.substitutionBlock substitution schema.proof.result origin)
    (PrimitiveTransport.substitutionBlock_checked policy substitution schema.proof.result origin) origin
  refine ⟨proof, ?_, ?_⟩
  · change substitution.applyHypotheses schema.proof.result.sequent.hyp = _
    rw [schema.hypotheses_exact]
    exact hypotheses types sourceNames targetNames theta assumptions distinct
  · change substitution.apply schema.proof.result.sequent.concl = _
    rw [schema.conclusion_exact]
    exact canonical types sourceNames targetNames theta conclusion distinct

/-- Read raw target images while retaining the source compiler's core expansion. -/
def specializeExpanded {conclusion : ParameterTerm Γ .prop} {assumptions : List (ParameterTerm Γ .prop)}
    (schema : Compiled policy sourceNames
      ((assumptions.map HOL.ImpredicativeConnectives.expand).map embed)
      (embed (HOL.ImpredicativeConnectives.expand conclusion)))
    (distinct : Instantiation.KeysDistinct types sourceNames) (origin : ProofExecution.Origin) :
    Compiled policy targetNames
      ((assumptions.map (image types sourceNames targetNames theta)).map HOL.ImpredicativeConnectives.expand)
      (HOL.ImpredicativeConnectives.expand (image types sourceNames targetNames theta conclusion)) := by
  let expandedTheta : HOL.Subst Symbol (Γ.map (HOL.Ty.substitute types.baseInstance)) Δ :=
    fun index => HOL.ImpredicativeConnectives.expand (theta index)
  let result := specialize types sourceNames targetNames @expandedTheta schema distinct origin
  have hypothesesSame : (assumptions.map HOL.ImpredicativeConnectives.expand).map
      (image types sourceNames targetNames @expandedTheta) =
      (assumptions.map (image types sourceNames targetNames theta)).map HOL.ImpredicativeConnectives.expand := by
    simp only [List.map_map]
    apply List.map_congr_left
    intro formula _
    exact image_expand types sourceNames targetNames theta formula
  have conclusionSame := image_expand types sourceNames targetNames theta conclusion
  exact ⟨result.proof,
    result.hypotheses_exact.trans (congrArg (reverseHypotheses targetNames) hypothesesSame),
    result.conclusion_exact.trans (congrArg (reverseCanonical targetNames) conclusionSame)⟩

theorem accepted {conclusion : ParameterTerm Γ .prop} {assumptions : List (ParameterTerm Γ .prop)}
    (schema : Compiled policy sourceNames (assumptions.map embed) (embed conclusion))
    (distinct : Instantiation.KeysDistinct types sourceNames) (origin : ProofExecution.Origin) :
    (ProofSystem.checker policy).check
      (specialize types sourceNames targetNames theta schema distinct origin).proof.result
      (specialize types sourceNames targetNames theta schema distinct origin).proof.certificate = true :=
  (specialize types sourceNames targetNames theta schema distinct origin).proof.accepted

#print axioms canonical
#print axioms hypotheses
#print axioms specialize
#print axioms specializeExpanded
#print axioms accepted

end Mettapedia.Languages.HOLLight.ParameterSchemaCompilation
