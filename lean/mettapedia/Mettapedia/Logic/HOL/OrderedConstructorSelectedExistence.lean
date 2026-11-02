import Mettapedia.Logic.HOL.OrderedConstructorSelectedChildren
import Mettapedia.Logic.HOL.OrderedConstructorChildExistence

/-!
# Selected child evidence under its original existential slot

Opening a selected lookup retains its segment ordinal. The constructor's
actual child conditions then supply membership and motive evidence for the
same array application, under that one local slot. No global slot choice or
identification of equal child indices is used.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL

namespace OrderedPositionPrograms

open SuccessorOrder
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ Δ Ξ : Ctx Base} {number index : Ty Base}

theorem selectedAt_substitute (zero : ClosedTerm Const number) (successor : ClosedTerm Const (number ⇒ number))
    (ordinal : Nat) (plan : Plan Const Γ number index) (images : Subst Const Γ Δ) (later : Subst Const Δ Ξ)
    (slot : Term Const Ξ number) (target : Term Const Ξ index) :
    selectedAt zero successor ordinal (substitute images plan) later slot target =
      selectedAt zero successor ordinal plan (Subst.comp later images) slot target := by
  induction plan generalizing ordinal Ξ with
  | nil => rfl
  | cons segment rest previous =>
      rcases segment with ⟨count, childIndex⟩
      cases ordinal with
      | zero => simp only [substitute_cons, selectedAt, subst_comp]
      | succ ordinal =>
          simp only [substitute_cons, selectedAt, subst_comp, previous]
          simp only [weaken, rename_subst, Subst.comp]
          rfl

end OrderedPositionPrograms

namespace IndexedConstructorGuards.PositionPrograms

open FiniteConstructorEncoding CurriedPredicates OrderedPositionPrograms SuccessorOrder
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ : Ctx Base}
    (constructors : ConstructorPrograms Const Γ)
    (zero : ClosedTerm Const constructors.number)
    (successor : ClosedTerm Const (constructors.number ⇒ constructors.number))
    (plans : (occurrence : Fin constructors.fields.length) →
      FieldPlan Const Γ (constructors.fields.get occurrence) constructors.number constructors.index)
    {space : Ty Base} (bottom : Term Const Γ space)
    (construct : Term Const Γ
      (constructors.number ⇒ payloadType constructors.fields ⇒ (constructors.number ⇒ space) ⇒ space))
    (property : Term Const Γ (space ⇒ constructors.index ⇒ .prop))

def selectedChildBody (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence))
    (children : Term Const Γ (constructors.number ⇒ space)) (ordinal : Nat)
    (requested : Term Const Γ constructors.index) : Formula Const (constructors.number :: Γ) :=
  let images : Subst Const Γ (constructors.number :: Γ) := Subst.ofRename Rename.weaken
  let inventory := constructors.subst images
  let localPlans := fun row => substitute images (plans row)
  let signature := (ofSegments inventory zero successor localPlans).contextual (HOL.subst images bottom) (HOL.subst images construct)
  let fields := substituteArguments images _ arguments
  let child := Term.app (HOL.subst images children) (.var .vz)
  .and (selectedAt zero successor ordinal (fieldTerms _ (localPlans occurrence) Subst.id fields)
    Subst.id (.var .vz) (HOL.subst images requested))
    (.and (.app (.app (signature.memberProgram (inventory.rootProgram (HOL.subst images construct))) child)
        (HOL.subst images requested))
      (.app (.app (HOL.subst images property) child) (HOL.subst images requested)))

def selectedChildExists (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence))
    (children : Term Const Γ (constructors.number ⇒ space)) (ordinal : Nat)
    (requested : Term Const Γ constructors.index) : Formula Const Γ :=
  .ex (selectedChildBody constructors zero successor plans bottom construct property occurrence arguments children ordinal requested)

def selectedChildExistsFromLookup {assumptions : List (Formula Const Γ)}
    (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence))
    (children : Term Const Γ (constructors.number ⇒ space)) (ordinal : Nat)
    (requested : Term Const Γ constructors.index)
    (arithmetic : PeanoEvidence successor zero assumptions)
    (conditions : ProofSyntax Const assumptions
      (((ofSegments constructors zero successor plans).contextual bottom construct).childConditions
        (PredicateFixedPoint.intersection
          ((ofSegments constructors zero successor plans).contextual bottom construct).least
          (IndexedPredicateInduction.lift (constructors.rootProgram construct) property))
        (encode constructors.fields occurrence arguments) children))
    (allowed : ProofSyntax Const assumptions (applyArguments _ (constructors.allowed occurrence) arguments))
    (present : ProofSyntax Const assumptions (selectedExists zero successor ordinal
      (fieldTerms _ (plans occurrence) Subst.id arguments) Subst.id requested)) :
    ProofSyntax Const assumptions
      (selectedChildExists constructors zero successor plans bottom construct property occurrence arguments children ordinal requested) := by
  apply ProofSyntax.impE (ContextualTrinity.exImp ?_) present
  apply ProofSyntax.allI
  apply ProofSyntax.impI
  let images : Subst Const Γ (constructors.number :: Γ) := Subst.ofRename Rename.weaken
  let inventory := constructors.subst images
  let localPlans := fun row => substitute images (plans row)
  let positions := ofSegments inventory zero successor localPlans
  let source := fieldTerms _ (plans occurrence) Subst.id arguments
  let body := selectedAt zero successor ordinal source (fun entry => weaken (Subst.id entry)) (.var .vz) (weaken requested)
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
    · rw [strengthenedConditions_subst, ConstructorPrograms.rootProgram_subst, encode_subst, ofSegments_subst]
      rfl
  have atSlot : ProofSyntax Const hypotheses (selectedAt zero successor ordinal
      (fieldTerms _ (localPlans occurrence) Subst.id fields) Subst.id (.var .vz) (HOL.subst images requested)) := by
    have natural : substitute images source = fieldTerms _ (localPlans occurrence) Subst.id fields := by
      dsimp only [source, localPlans, fields]
      rw [fieldTerms_subst, fieldTerms_substitute]
      simp only [HOL.subst, subst_id, Subst.id]
    apply ProofSyntax.castIndices rfl ?_ (.hyp (Δ := hypotheses) 0)
    change body = _
    rw [← natural, selectedAt_substitute]
    simp only [body, images, Subst.id, subst_ofRename]
    rfl
  exact selectedChildAtFromLookup inventory zero successor localPlans (HOL.subst images bottom) (HOL.subst images construct)
    (HOL.subst images property) occurrence fields (HOL.subst images children) ordinal (.var .vz) (HOL.subst images requested)
    ((arithmetic.rename Rename.weaken).prepend body) currentConditions currentAllowed atSlot

theorem selectedChildExistsFromLookup_free {assumptions : List (Formula Const Γ)}
    (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence))
    (children : Term Const Γ (constructors.number ⇒ space)) (ordinal : Nat)
    (requested : Term Const Γ constructors.index)
    (arithmetic : PeanoEvidence successor zero assumptions)
    (conditions : ProofSyntax Const assumptions
      (((ofSegments constructors zero successor plans).contextual bottom construct).childConditions
        (PredicateFixedPoint.intersection
          ((ofSegments constructors zero successor plans).contextual bottom construct).least
          (IndexedPredicateInduction.lift (constructors.rootProgram construct) property))
        (encode constructors.fields occurrence arguments) children))
    (allowed : ProofSyntax Const assumptions (applyArguments _ (constructors.allowed occurrence) arguments))
    (present : ProofSyntax Const assumptions (selectedExists zero successor ordinal
      (fieldTerms _ (plans occurrence) Subst.id arguments) Subst.id requested))
    (arithmeticFree : arithmetic.Free) (conditionsFree : conditions.FunctionExtensionalityFree)
    (allowedFree : allowed.FunctionExtensionalityFree) (presentFree : present.FunctionExtensionalityFree) :
    (selectedChildExistsFromLookup constructors zero successor plans bottom construct property occurrence arguments children
      ordinal requested arithmetic conditions allowed present).FunctionExtensionalityFree := by
  unfold selectedChildExistsFromLookup
  constructor
  · apply (ContextualTrinity.exImp_free _).mpr
    apply selectedChildAtFromLookup_free
    · apply PeanoEvidence.prepend_free
      exact arithmetic.rename_free Rename.weaken arithmeticFree
    · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
      apply (ProofSyntax.functionExtensionalityFree_mono _ _).mpr
      exact (ProofSyntax.functionExtensionalityFree_subst _ _).mpr conditionsFree
    · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
      apply (ProofSyntax.functionExtensionalityFree_mono _ _).mpr
      exact (ProofSyntax.functionExtensionalityFree_subst _ _).mpr allowedFree
    · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
      trivial
  · exact presentFree

#print axioms selectedChildExistsFromLookup
#print axioms selectedChildExistsFromLookup_free

end IndexedConstructorGuards.PositionPrograms
end Mettapedia.Logic.HOL
