import Mettapedia.GSLT.LanguageDef.IndexedVectorTreeNativeSourceReading
import Mettapedia.GSLT.LanguageDef.IndexedVectorTreeStoredFamily
import Mettapedia.Logic.HOL.PredicateContextInstantiation

/-!
# Installing the derived family in the original ambient telescope

The two source type parameters are interpreted by the represented answer
predicate and the least/root family from the same parsed inventory. The five
remaining binders stay open, with their substituted guards retained in a
target telescope. This is a represented HOL environment, not a source-term
substitution or a closed implementation of either constructor or case method.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.IndexedVectorTreeStoredFamilyEnvironment
open Mettapedia.Logic Mettapedia.Logic.HOL
open PredicateContexts
namespace Source
export IndexedVectorTreeNativeSourceReading (ambient ambientContext familyPredicate answerPredicate)
end Source
namespace Native
export IndexedContainerNativeVectorMethodReading (Base Const E N)
end Native
abbrev Base := Native.Base
abbrev Const := Native.Const
abbrev E := Native.E
abbrev N := Native.N
abbrev P := E ⇒ .prop
abbrev parameters : Ctx Base := [P,P]

private def motiveGuard : Term Const parameters
    (IndexedVectorTreeNativeSourceReading.motiveCarrier ⇒ .prop) :=
  match Source.ambientContext.telescope with
  | .snoc (.snoc (.snoc (.snoc (.snoc _ predicate) _) _) _) _ => predicate

private def solvedConstructorGuard : Term Const
    (IndexedVectorTreeNativeSourceReading.motiveCarrier :: parameters)
    (IndexedVectorTreeNativeSourceReading.solvedConstructorCarrier ⇒ .prop) :=
  match Source.ambientContext.telescope with
  | .snoc (.snoc (.snoc (.snoc _ predicate) _) _) _ => predicate

private def branchConstructorGuard : Term Const
    (IndexedVectorTreeNativeSourceReading.solvedConstructorCarrier ::
      IndexedVectorTreeNativeSourceReading.motiveCarrier :: parameters)
    (IndexedVectorTreeNativeSourceReading.branchConstructorCarrier ⇒ .prop) :=
  match Source.ambientContext.telescope with
  | .snoc (.snoc (.snoc _ predicate) _) _ => predicate

private def solvedCaseGuard : Term Const
    (IndexedVectorTreeNativeSourceReading.branchConstructorCarrier ::
      IndexedVectorTreeNativeSourceReading.solvedConstructorCarrier ::
      IndexedVectorTreeNativeSourceReading.motiveCarrier :: parameters)
    (IndexedVectorTreeNativeSourceReading.solvedCaseCarrier ⇒ .prop) :=
  match Source.ambientContext.telescope with
  | .snoc (.snoc _ predicate) _ => predicate

private def branchCaseGuard : Term Const
    (IndexedVectorTreeNativeSourceReading.solvedCaseCarrier ::
      IndexedVectorTreeNativeSourceReading.branchConstructorCarrier ::
      IndexedVectorTreeNativeSourceReading.solvedConstructorCarrier ::
      IndexedVectorTreeNativeSourceReading.motiveCarrier :: parameters)
    (IndexedVectorTreeNativeSourceReading.branchCaseCarrier ⇒ .prop) :=
  match Source.ambientContext.telescope with
  | .snoc _ predicate => predicate

private def parameterTelescope : Telescope Const parameters :=
  .snoc (.snoc .nil (PredicateProducts.full P)) (PredicateProducts.full P)

private theorem original_telescope : Source.ambientContext.telescope =
    .snoc (.snoc (.snoc (.snoc (.snoc parameterTelescope motiveGuard)
      solvedConstructorGuard) branchConstructorGuard) solvedCaseGuard) branchCaseGuard := by
  with_unfolding_all rfl

private def fullMember {Γ : Ctx Base} {type : Ty Base}
    {Δ : List (Formula Const Γ)} (value : Term Const Γ type) :
    ProofSyntax Const Δ (.app (PredicateProducts.full type) value) :=
  .impE (.eqPropER (.beta value .top)) .topI

private theorem fullMember_free {Γ : Ctx Base} {type : Ty Base}
    {Δ : List (Formula Const Γ)} (value : Term Const Γ type) :
    (fullMember (Δ := Δ) value).FunctionExtensionalityFree := by trivial

private def typeImages {Γ : Ctx Base} (answer family : Term Const Γ P) :
    Subst Const parameters Γ :=
  Subst.cons family (Subst.cons answer (fun {type} (index : Var [] type) => nomatch index))

abbrev target (Γ : Ctx Base) : Ctx Base :=
  IndexedVectorTreeNativeSourceReading.branchCaseCarrier ::
    IndexedVectorTreeNativeSourceReading.solvedCaseCarrier ::
    IndexedVectorTreeNativeSourceReading.branchConstructorCarrier ::
    IndexedVectorTreeNativeSourceReading.solvedConstructorCarrier ::
    IndexedVectorTreeNativeSourceReading.motiveCarrier :: Γ

private def openImages {Γ : Ctx Base} (answer family : Term Const Γ P) :
    Subst Const Source.ambient (target Γ) :=
  Subst.lift (σ := IndexedVectorTreeNativeSourceReading.branchCaseCarrier)
    (Subst.lift (σ := IndexedVectorTreeNativeSourceReading.solvedCaseCarrier)
      (Subst.lift (σ := IndexedVectorTreeNativeSourceReading.branchConstructorCarrier)
        (Subst.lift (σ := IndexedVectorTreeNativeSourceReading.solvedConstructorCarrier)
          (Subst.lift (σ := IndexedVectorTreeNativeSourceReading.motiveCarrier) (typeImages answer family)))))

private def openTelescope {Γ : Ctx Base} (context : Telescope Const Γ)
    (answer family : Term Const Γ P) : Telescope Const (target Γ) :=
  let images : Subst Const parameters Γ := typeImages answer family
  let motive := context.snoc (subst images motiveGuard)
  let solved := motive.snoc (subst (Subst.lift images) solvedConstructorGuard)
  let branch := solved.snoc (subst (Subst.lift (Subst.lift images)) branchConstructorGuard)
  let solvedCase := branch.snoc (subst (Subst.lift (Subst.lift (Subst.lift images))) solvedCaseGuard)
  solvedCase.snoc (subst (Subst.lift (Subst.lift (Subst.lift (Subst.lift images)))) branchCaseGuard)

private def typeRealizer {Γ : Ctx Base} (context : Telescope Const Γ)
    (answer family : Term Const Γ P) :
    parameterTelescope.Realizes (typeImages answer family) context.hypotheses :=
  let empty : (Telescope.nil (Const := Const)).Realizes
      (fun {type} (index : Var [] type) => nomatch index) context.hypotheses :=
      fun {_type} index => nomatch index
  let first : (Telescope.snoc .nil (PredicateProducts.full P)).Realizes
      (Subst.cons answer (fun {type} (index : Var [] type) => nomatch index)) context.hypotheses :=
    Telescope.Realizes.cons empty (PredicateProducts.full P) answer (fullMember answer)
  Telescope.Realizes.cons first (PredicateProducts.full P) family (fullMember family)

private theorem typeRealizer_free {Γ : Ctx Base} (context : Telescope Const Γ)
    (answer family : Term Const Γ P) :
    ∀ {type} (index : Var parameters type),
      (typeRealizer context answer family index).FunctionExtensionalityFree := by
  unfold typeRealizer
  apply Telescope.Realizes.cons_free
  · apply Telescope.Realizes.cons_free
    · intro type index; cases index
    · exact fullMember_free answer
  · exact fullMember_free family

@[irreducible] private def openRealizer {Γ : Ctx Base} (context : Telescope Const Γ)
    (answer family : Term Const Γ P) :
    Source.ambientContext.telescope.Realizes (openImages answer family)
      (openTelescope context answer family).hypotheses := by
  with_unfolding_all exact Telescope.Realizes.liftUnderGuard (Telescope.Realizes.liftUnderGuard
    (Telescope.Realizes.liftUnderGuard (Telescope.Realizes.liftUnderGuard
      (Telescope.Realizes.liftUnderGuard (typeRealizer context answer family) motiveGuard)
        solvedConstructorGuard) branchConstructorGuard) solvedCaseGuard) branchCaseGuard

private theorem openRealizer_free {Γ : Ctx Base} (context : Telescope Const Γ)
    (answer family : Term Const Γ P) :
    ∀ {type} (index : Var Source.ambient type),
      (openRealizer context answer family index).FunctionExtensionalityFree := by
  unfold openRealizer
  with_unfolding_all apply Telescope.Realizes.liftUnderGuard_free
  apply Telescope.Realizes.liftUnderGuard_free
  apply Telescope.Realizes.liftUnderGuard_free
  apply Telescope.Realizes.liftUnderGuard_free
  apply Telescope.Realizes.liftUnderGuard_free
  exact typeRealizer_free context answer family

private def sourceSolved : Var Source.ambient (E ⇒ E) := .vs (.vs (.vs .vz))

private theorem originalSolvedDomain : Source.ambientContext.telescope.domain sourceSolved =
    PredicateProducts.pi Source.answerPredicate (weaken Source.familyPredicate) := by
  with_unfolding_all rfl

private theorem openSolvedGuard {Γ : Ctx Base} (answer family : Term Const Γ P) :
    subst (openImages answer family) (Source.ambientContext.telescope.guard sourceSolved) =
      .app (PredicateProducts.pi
        (weaken (weaken (weaken (weaken (weaken answer)))))
        (weaken (weaken (weaken (weaken (weaken (weaken family)))))))
        (.var (.vs (.vs (.vs .vz)))) := by
  change Term.app (subst (openImages answer family)
    (Source.ambientContext.telescope.domain sourceSolved))
      (subst (openImages answer family) (.var sourceSolved)) = _
  rw [originalSolvedDomain, PredicateProducts.subst_pi, subst_weaken]
  rfl

@[irreducible] private def constantApplication {Γ : Ctx Base}
    {Δ : List (Formula Const Γ)} (domain codomain : Term Const Γ P)
    (function : Term Const Γ (E ⇒ E)) (value : Term Const Γ E)
    (functionTyped : ProofSyntax Const Δ (.app (PredicateProducts.pi domain (weaken codomain)) function))
    (argumentTyped : ProofSyntax Const Δ (.app domain value)) :
    ProofSyntax Const Δ (.app codomain (.app function value)) :=
  ProofSyntax.castIndices rfl
    (congrArg (fun predicate => Term.app predicate (.app function value)) (instantiate_weaken value codomain))
    (PredicateProducts.eliminate domain (weaken codomain) function value functionTyped argumentTyped)

private theorem constantApplication_free {Γ : Ctx Base}
    {Δ : List (Formula Const Γ)} (domain codomain : Term Const Γ P)
    (function : Term Const Γ (E ⇒ E)) (value : Term Const Γ E)
    (functionTyped : ProofSyntax Const Δ (.app (PredicateProducts.pi domain (weaken codomain)) function))
    (argumentTyped : ProofSyntax Const Δ (.app domain value))
    (functionFree : functionTyped.FunctionExtensionalityFree)
    (argumentFree : argumentTyped.FunctionExtensionalityFree) :
    (constantApplication domain codomain function value functionTyped argumentTyped).FunctionExtensionalityFree := by
  unfold constantApplication
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact PredicateProducts.eliminate_free _ _ _ _ _ _ functionFree argumentFree

variable {Γ : Ctx Base}
  (context : Telescope Const Γ)
  (given : VectorTreeFieldEmbedding.Inputs Const Γ N E E)
  (source : Term Const Γ P) (numbers : Term Const Γ (N ⇒ .prop))
  (zero one : ClosedTerm Const N) (successor : ClosedTerm Const (N ⇒ N))
  (tags : Nat → Term Const Γ N) (bottom : Term Const Γ E)

def answer : Term Const Γ P := given.predicate source
def family : Term Const Γ P :=
  IndexedVectorTreeStoredFamily.family given source numbers zero one successor tags bottom

/-- The five uninstalled operation binders retain their original guards. -/
def telescope := openTelescope context (answer given source)
  (family given source numbers zero one successor tags bottom)

def images : Subst Const Source.ambient (target Γ) := openImages (answer given source)
  (family given source numbers zero one successor tags bottom)

def realizes : Source.ambientContext.telescope.Realizes
    (images given source numbers zero one successor tags bottom)
    (telescope context given source numbers zero one successor tags bottom).hypotheses :=
  openRealizer context (answer given source)
    (family given source numbers zero one successor tags bottom)

theorem realizes_free : ∀ {type} (index : Var Source.ambient type),
    (realizes context given source numbers zero one successor tags bottom index).FunctionExtensionalityFree :=
  openRealizer_free context (answer given source)
    (family given source numbers zero one successor tags bottom)

theorem five_guards_retained :
    (telescope context given source numbers zero one successor tags bottom).hypotheses.length =
      Γ.length + 5 := by
  rw [Telescope.hypotheses_length]
  change Γ.length + 1 + 1 + 1 + 1 + 1 = Γ.length + 5
  omega

theorem family_parameter_bound :
    subst (images given source numbers zero one successor tags bottom) Source.familyPredicate =
      weaken (weaken (weaken (weaken (weaken
        (family given source numbers zero one successor tags bottom))))) := rfl

theorem answer_parameter_bound :
    subst (images given source numbers zero one successor tags bottom) Source.answerPredicate =
      weaken (weaken (weaken (weaken (weaken (answer given source))))) := rfl

/-- A retained source-context proof is transported using the constructed
variable-guard evidence. No constructor or case guard is discarded. -/
def transport {claim : Formula Const Source.ambient}
    (proof : ProofSyntax Const Source.ambientContext.telescope.hypotheses claim) :
    ProofSyntax Const (telescope context given source numbers zero one successor tags bottom).hypotheses
      (subst (images given source numbers zero one successor tags bottom) claim) :=
  Telescope.Realizes.transport (realizes context given source numbers zero one successor tags bottom) proof

theorem transport_free {claim : Formula Const Source.ambient}
    (proof : ProofSyntax Const Source.ambientContext.telescope.hypotheses claim)
    (free : proof.FunctionExtensionalityFree) :
    (transport context given source numbers zero one successor tags bottom proof).FunctionExtensionalityFree :=
  Telescope.Realizes.transport_free _ proof
    (realizes_free context given source numbers zero one successor tags bottom) free

def answerAt : Term Const (target Γ) P :=
  weaken (weaken (weaken (weaken (weaken (answer given source)))))

def familyAt : Term Const (target Γ) P :=
  weaken (weaken (weaken (weaken (weaken
    (family given source numbers zero one successor tags bottom)))))

def solvedVariable : Term Const (target Γ) (E ⇒ E) := .var (.vs (.vs (.vs .vz)))

private theorem solved_guard :
    subst (images given source numbers zero one successor tags bottom)
      (Source.ambientContext.telescope.guard sourceSolved) =
      .app (PredicateProducts.pi (answerAt given source)
        (weaken (familyAt given source numbers zero one successor tags bottom)))
        (solvedVariable (Γ := Γ)) :=
  openSolvedGuard (answer given source) (family given source numbers zero one successor tags bottom)

/-- The actual retained solved-constructor guard, after binding A and F. -/
def solvedMember : ProofSyntax Const
    (telescope context given source numbers zero one successor tags bottom).hypotheses
    (.app (PredicateProducts.pi (answerAt given source)
      (weaken (familyAt given source numbers zero one successor tags bottom)))
      (solvedVariable (Γ := Γ))) :=
  ProofSyntax.castIndices rfl (solved_guard given source numbers zero one successor tags bottom)
    (transport context given source numbers zero one successor tags bottom
      (Source.ambientContext.telescope.variableProof sourceSolved))

theorem solvedMember_free :
    (solvedMember context given source numbers zero one successor tags bottom).FunctionExtensionalityFree := by
  unfold solvedMember
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  apply transport_free
  simp only [Telescope.variableProof, ProofSyntax.functionExtensionalityFree_castIndices]
  trivial

/-- An admitted answer can be passed to the still-open solved constructor.
The constructor's own guard remains one of the five target hypotheses. -/
@[irreducible] def solvedApplication (value : Term Const (target Γ) E)
    (member : ProofSyntax Const
      (telescope context given source numbers zero one successor tags bottom).hypotheses
      (.app (answerAt given source) value)) :
    ProofSyntax Const (telescope context given source numbers zero one successor tags bottom).hypotheses
      (.app (familyAt given source numbers zero one successor tags bottom)
        (.app (solvedVariable (Γ := Γ)) value)) :=
  constantApplication (answerAt given source)
      (familyAt given source numbers zero one successor tags bottom)
      (solvedVariable (Γ := Γ)) value
      (solvedMember context given source numbers zero one successor tags bottom) member

theorem solvedApplication_free (value : Term Const (target Γ) E)
    (member : ProofSyntax Const
      (telescope context given source numbers zero one successor tags bottom).hypotheses
      (.app (answerAt given source) value)) (free : member.FunctionExtensionalityFree) :
    (solvedApplication context given source numbers zero one successor tags bottom value member).FunctionExtensionalityFree := by
  unfold solvedApplication
  exact constantApplication_free _ _ _ _ _ _
    (solvedMember_free context given source numbers zero one successor tags bottom) free

#print axioms realizes
#print axioms realizes_free
#print axioms transport_free
#print axioms family_parameter_bound
#print axioms five_guards_retained
#print axioms solved_guard
#print axioms solvedApplication_free

end Mettapedia.GSLT.LanguageDef.IndexedVectorTreeStoredFamilyEnvironment
