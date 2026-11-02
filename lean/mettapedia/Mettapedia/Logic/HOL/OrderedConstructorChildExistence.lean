import Mettapedia.Logic.HOL.OrderedConstructorChildProofs
import Mettapedia.Logic.HOL.ConstructorPositionSubstitution
import Mettapedia.Logic.HOL.OrderedPositionExistence

/-!
# Membership and motive evidence under one original slot witness

An existential ordered lookup is read back through the actual curried field
graph. The strengthened child condition supplies membership and the motive
inside that same slot scope. The result retains all three relations under
one existential; equal indices do not identify independently chosen slots.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.IndexedConstructorGuards.PositionPrograms

open FiniteConstructorEncoding CurriedPredicates OrderedPositionPrograms SuccessorOrder
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ Ξ : Ctx Base}
    (constructors : ConstructorPrograms Const Γ)
    (zero : ClosedTerm Const constructors.number)
    (successor : ClosedTerm Const (constructors.number ⇒ constructors.number))
    (plans : (occurrence : Fin constructors.fields.length) →
      FieldPlan Const Γ (constructors.fields.get occurrence) constructors.number constructors.index)

theorem ofSegments_subst (images : Subst Const Γ Ξ) :
    (ofSegments constructors zero successor plans).subst images =
      ofSegments (constructors.subst images) zero successor (fun occurrence => substitute images (plans occurrence)) := by
  apply congrArg PositionPrograms.mk
  funext occurrence
  exact fieldGraph_substitute zero successor _ (plans occurrence) images

def originalLookupBody (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence))
    (requested : Term Const Γ constructors.index) : Formula Const (constructors.number :: Γ) :=
  let images : Subst Const Γ (constructors.number :: Γ) := Subst.ofRename Rename.weaken
  applyArguments _
    (.app (.app (fieldGraph zero successor _ (substitute images (plans occurrence))) (.var .vz))
      (HOL.subst images requested)) (substituteArguments images _ arguments)

def originalLookupExists (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence))
    (requested : Term Const Γ constructors.index) : Formula Const Γ :=
  .ex (originalLookupBody constructors zero successor plans occurrence arguments requested)

def originalLookupExistsFromPlan {assumptions : List (Formula Const Γ)}
    (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence))
    (requested : Term Const Γ constructors.index)
    (present : ProofSyntax Const assumptions
      (lookupExists zero successor (fieldTerms _ (plans occurrence) Subst.id arguments) Subst.id requested)) :
    ProofSyntax Const assumptions (originalLookupExists constructors zero successor plans occurrence arguments requested) := by
  apply ProofSyntax.impE (ContextualTrinity.exImp ?_) present
  apply ProofSyntax.allI
  apply ProofSyntax.impI
  let images : Subst Const Γ (constructors.number :: Γ) := Subst.ofRename Rename.weaken
  let source := fieldTerms _ (plans occurrence) Subst.id arguments
  let body := compileAt zero successor source (fun entry => weaken (Subst.id entry)) (.var .vz) (weaken requested)
  let hypotheses := body :: weakenHyps assumptions
  let fields := substituteArguments images _ arguments
  let targetPlan := fieldTerms _ (substitute images (plans occurrence)) Subst.id fields
  have natural : substitute images source = targetPlan := by
    dsimp only [source, targetPlan, fields]
    rw [fieldTerms_subst, fieldTerms_substitute]
    simp only [HOL.subst, subst_id, Subst.id]
  have atSlot : ProofSyntax Const hypotheses
      (compileAt zero successor targetPlan Subst.id (.var .vz) (HOL.subst images requested)) := by
    apply ProofSyntax.castIndices rfl ?_ (.hyp (Δ := hypotheses) 0)
    change body = _
    rw [← natural, compileAt_substitute]
    simp only [body, images, subst_id, subst_ofRename]
    rfl
  exact .impE (.eqPropER (fieldGraph_beta zero successor _ (substitute images (plans occurrence))
    (.var .vz) (HOL.subst images requested) fields)) atSlot

theorem originalLookupExistsFromPlan_free {assumptions : List (Formula Const Γ)}
    (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence))
    (requested : Term Const Γ constructors.index)
    (present : ProofSyntax Const assumptions
      (lookupExists zero successor (fieldTerms _ (plans occurrence) Subst.id arguments) Subst.id requested))
    (free : present.FunctionExtensionalityFree) :
    (originalLookupExistsFromPlan constructors zero successor plans occurrence arguments requested present).FunctionExtensionalityFree := by
  unfold originalLookupExistsFromPlan
  constructor
  · apply (ContextualTrinity.exImp_free _).mpr
    constructor
    · exact fieldGraph_beta_free _ _ _ _ _ _ _
    · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
      trivial
  · exact free

variable {space : Ty Base} (bottom : Term Const Γ space)
    (construct : Term Const Γ
      (constructors.number ⇒ payloadType constructors.fields ⇒ (constructors.number ⇒ space) ⇒ space))
    (property : Term Const Γ (space ⇒ constructors.index ⇒ .prop))

def originalChildBody (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence))
    (children : Term Const Γ (constructors.number ⇒ space))
    (requested : Term Const Γ constructors.index) : Formula Const (constructors.number :: Γ) :=
  let images : Subst Const Γ (constructors.number :: Γ) := Subst.ofRename Rename.weaken
  let inventory := constructors.subst images
  let positions := ofSegments inventory zero successor (fun row => substitute images (plans row))
  let signature := positions.contextual (HOL.subst images bottom) (HOL.subst images construct)
  let child := Term.app (HOL.subst images children) (.var .vz)
  .and (originalLookupBody constructors zero successor plans occurrence arguments requested)
    (.and (.app (.app (signature.memberProgram (inventory.rootProgram (HOL.subst images construct))) child)
        (HOL.subst images requested))
      (.app (.app (HOL.subst images property) child) (HOL.subst images requested)))

def originalChildExists (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence))
    (children : Term Const Γ (constructors.number ⇒ space))
    (requested : Term Const Γ constructors.index) : Formula Const Γ :=
  .ex (originalChildBody constructors zero successor plans bottom construct property occurrence arguments children requested)

def originalChildExistsFromLookup {assumptions : List (Formula Const Γ)}
    (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence))
    (children : Term Const Γ (constructors.number ⇒ space))
    (requested : Term Const Γ constructors.index)
    (arithmetic : PeanoEvidence successor zero assumptions)
    (conditions : ProofSyntax Const assumptions
      (((ofSegments constructors zero successor plans).contextual bottom construct).childConditions
        (PredicateFixedPoint.intersection
          ((ofSegments constructors zero successor plans).contextual bottom construct).least
          (IndexedPredicateInduction.lift (constructors.rootProgram construct) property))
        (encode constructors.fields occurrence arguments) children))
    (allowed : ProofSyntax Const assumptions (applyArguments _ (constructors.allowed occurrence) arguments))
    (present : ProofSyntax Const assumptions (originalLookupExists constructors zero successor plans occurrence arguments requested)) :
    ProofSyntax Const assumptions
      (originalChildExists constructors zero successor plans bottom construct property occurrence arguments children requested) := by
  apply ProofSyntax.impE (ContextualTrinity.exImp ?_) present
  apply ProofSyntax.allI
  apply ProofSyntax.impI
  let images : Subst Const Γ (constructors.number :: Γ) := Subst.ofRename Rename.weaken
  let inventory := constructors.subst images
  let localPlans := fun row => substitute images (plans row)
  let positions := ofSegments inventory zero successor localPlans
  let body := originalLookupBody constructors zero successor plans occurrence arguments requested
  let hypotheses := body :: weakenHyps assumptions
  let fields := substituteArguments images _ arguments
  have currentAllowed : ProofSyntax Const hypotheses (applyArguments _ (inventory.allowed occurrence) fields) := by
    apply ProofSyntax.castIndices ?_ ?_ ((ProofSyntax.subst images allowed).prepend body)
    · change body :: assumptions.map (HOL.subst images) = body :: assumptions.map weaken
      apply congrArg (List.cons body)
      apply List.map_congr_left
      intro formula _
      exact subst_ofRename Rename.weaken formula
    · exact applyArguments_subst images _ (constructors.allowed occurrence) arguments
  have currentConditions : ProofSyntax Const hypotheses
      ((positions.contextual (HOL.subst images bottom) (HOL.subst images construct)).childConditions
        (PredicateFixedPoint.intersection
          (positions.contextual (HOL.subst images bottom) (HOL.subst images construct)).least
          (IndexedPredicateInduction.lift (inventory.rootProgram (HOL.subst images construct)) (HOL.subst images property)))
        (encode inventory.fields occurrence fields) (HOL.subst images children)) := by
    apply ProofSyntax.castIndices ?_ ?_ ((ProofSyntax.subst images conditions).prepend body)
    · change body :: assumptions.map (HOL.subst images) = body :: assumptions.map weaken
      apply congrArg (List.cons body)
      apply List.map_congr_left
      intro formula _
      exact subst_ofRename Rename.weaken formula
    · rw [strengthenedConditions_subst, ConstructorPrograms.rootProgram_subst,
        encode_subst, ofSegments_subst]
      rfl
  have currentArithmetic := (arithmetic.rename Rename.weaken).prepend body
  exact childAtFromLookup inventory zero successor localPlans (HOL.subst images bottom) (HOL.subst images construct)
    (HOL.subst images property) occurrence fields (HOL.subst images children) (.var .vz) (HOL.subst images requested)
    currentArithmetic currentConditions currentAllowed (.hyp (Δ := hypotheses) 0)

theorem originalChildExistsFromLookup_free {assumptions : List (Formula Const Γ)}
    (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence))
    (children : Term Const Γ (constructors.number ⇒ space))
    (requested : Term Const Γ constructors.index)
    (arithmetic : PeanoEvidence successor zero assumptions)
    (conditions : ProofSyntax Const assumptions
      (((ofSegments constructors zero successor plans).contextual bottom construct).childConditions
        (PredicateFixedPoint.intersection
          ((ofSegments constructors zero successor plans).contextual bottom construct).least
          (IndexedPredicateInduction.lift (constructors.rootProgram construct) property))
        (encode constructors.fields occurrence arguments) children))
    (allowed : ProofSyntax Const assumptions (applyArguments _ (constructors.allowed occurrence) arguments))
    (present : ProofSyntax Const assumptions (originalLookupExists constructors zero successor plans occurrence arguments requested))
    (arithmeticFree : arithmetic.Free) (conditionsFree : conditions.FunctionExtensionalityFree)
    (allowedFree : allowed.FunctionExtensionalityFree) (presentFree : present.FunctionExtensionalityFree) :
    (originalChildExistsFromLookup constructors zero successor plans bottom construct property occurrence arguments children
      requested arithmetic conditions allowed present).FunctionExtensionalityFree := by
  unfold originalChildExistsFromLookup
  constructor
  · apply (ContextualTrinity.exImp_free _).mpr
    apply childAtFromLookup_free
    · apply PeanoEvidence.prepend_free
      exact arithmetic.rename_free Rename.weaken arithmeticFree
    · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
      apply (ProofSyntax.functionExtensionalityFree_mono _ _).mpr
      exact (ProofSyntax.functionExtensionalityFree_subst _ _).mpr conditionsFree
    · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
      apply (ProofSyntax.functionExtensionalityFree_mono _ _).mpr
      exact (ProofSyntax.functionExtensionalityFree_subst _ _).mpr allowedFree
    · trivial
  · exact presentFree

#print axioms originalLookupExistsFromPlan_free
#print axioms originalChildExistsFromLookup
#print axioms originalChildExistsFromLookup_free

end Mettapedia.Logic.HOL.IndexedConstructorGuards.PositionPrograms
