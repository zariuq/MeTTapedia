import Mettapedia.Logic.HOL.ConstructorGuardSubstitution
import Mettapedia.Logic.HOL.ConstructorShapeDataGuardControls

/-!
# Composed substitutions with retained premise occurrences

The row callback reads the last of two equal ambient premises. An earlier
substitution selects the outer Boolean variable; a later substitution sends
the inner variable to false and the outer variable to true. Premise reindexing
keeps the duplicate occurrences distinct, and the resulting retained proof
is interpreted under a realizable final assumption list. Swapping the later
Boolean bindings makes the target row condition false.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.ConstructorGuardSubstitutionControls

open FiniteConstructorEncoding FiniteConstructorEncoding.Controls
open IndexedConstructorGuards CurriedPredicates

abbrev first := ConstructorDataPredicates.ProgramControls.first

def premises : List (Formula Constants [.prop]) := [.var .vz, .top, .var .vz]

def targetConditions : ConstructorDataPredicates.Conditions Constants [.prop] signature :=
  fun occurrence => constant (signature.get occurrence) (.var .vz)

def readLast {Ξ : Ctx Empty} (images : Subst Constants [.prop] Ξ)
    {assumptions : List (Formula Constants Ξ)}
    (transport : ProofSyntax.OccurrenceMap (premises.map (HOL.subst images)) assumptions) :
    ProofSyntax Constants assumptions (HOL.subst images (.var .vz)) :=
  .castIndices rfl (transport.get_eq ⟨2, by simp [premises]⟩)
    (.hyp (transport.index ⟨2, by simp [premises]⟩))

theorem readLast_free {Ξ : Ctx Empty} (images : Subst Constants [.prop] Ξ)
    {assumptions : List (Formula Constants Ξ)}
    (transport : ProofSyntax.OccurrenceMap (premises.map (HOL.subst images)) assumptions) :
    (readLast images transport).FunctionExtensionalityFree :=
  (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr True.intro

def callback : ConstructorPrograms.RowImplication premises
    ConstructorShapeDataGuardControls.inventory targetConditions := by
  intro Ξ images assumptions transport occurrence arguments _allowed
  have current := constant_intro (signature.get occurrence) arguments (readLast images transport)
  exact .castIndices rfl
    (congrArg (fun predicate => applyArguments _ predicate arguments)
      (constant_subst images (signature.get occurrence) (.var .vz)).symm) current

theorem callback_free : ConstructorPrograms.RowImplication.Free callback := by
  intro Ξ images assumptions transport occurrence arguments allowed allowedFree
  unfold callback
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact constant_intro_free _ _ _ (readLast_free images transport)

def earlier : Subst Constants [.prop] [.prop, .prop]
  | _, .vz => .var (.vs .vz)

def later : Subst Constants [.prop, .prop] []
  | _, .vz => .bot
  | _, .vs .vz => .top

def wrongLater : Subst Constants [.prop, .prop] []
  | _, .vz => .top
  | _, .vs .vz => .bot

def newPremises : List (Formula Constants [.prop, .prop]) :=
  [.not (.var .vz), .var (.vs .vz), .top, .var (.vs .vz)]

def reindex : ProofSyntax.OccurrenceMap (premises.map (HOL.subst earlier)) newPremises where
  index
    | ⟨0, _⟩ => ⟨3, by decide⟩
    | ⟨1, _⟩ => ⟨2, by decide⟩
    | ⟨2, _⟩ => ⟨1, by decide⟩
  get_eq
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
    | ⟨2, _⟩ => rfl

def finalPremises : List (ClosedFormula Constants) := [.top, .not .bot, .top, .top]

def finalOccurrences : ProofSyntax.OccurrenceMap (newPremises.map (HOL.subst later)) finalPremises where
  index
    | ⟨0, _⟩ => ⟨1, by decide⟩
    | ⟨1, _⟩ => ⟨3, by decide⟩
    | ⟨2, _⟩ => ⟨2, by decide⟩
    | ⟨3, _⟩ => ⟨0, by decide⟩
  get_eq
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
    | ⟨2, _⟩ => rfl
    | ⟨3, _⟩ => rfl

def transportedCallback : ConstructorPrograms.RowImplication newPremises
    (ConstructorShapeDataGuardControls.inventory.subst earlier)
    (fun occurrence => HOL.subst earlier (targetConditions occurrence)) :=
  ConstructorPrograms.RowImplication.reindexPremises
    (ConstructorPrograms.RowImplication.substitute callback earlier) reindex

theorem transportedCallback_free : ConstructorPrograms.RowImplication.Free transportedCallback :=
  ConstructorPrograms.RowImplication.reindexPremises_free _
    (ConstructorPrograms.RowImplication.substitute_free callback callback_free earlier) reindex

def allowed : ProofSyntax Constants finalPremises
    (applyArguments [.prop, .prop]
      (HOL.subst later
        ((ConstructorShapeDataGuardControls.inventory.subst earlier).allowed first)) fields) :=
  ((ConstructorShapeDataGuardControls.sourceAllowed.prepend .top).prepend .top |>.prepend (.not .bot)).prepend .top

def finalProof : ProofSyntax Constants finalPremises
    (applyArguments [.prop, .prop]
      (HOL.subst later (HOL.subst earlier (targetConditions first))) fields) :=
  transportedCallback later finalOccurrences first fields allowed

theorem allowed_free : allowed.FunctionExtensionalityFree := by
  simpa only [allowed, ProofSyntax.prepend, ProofSyntax.functionExtensionalityFree_mono] using
    ConstructorShapeDataGuardControls.sourceAllowed_free

theorem finalProof_free : finalProof.FunctionExtensionalityFree :=
  transportedCallback_free later finalOccurrences first fields allowed allowed_free

theorem assumptions_realizable : Soundness.SatisfiesHyps model values finalPremises := by
  intro formula member
  simp only [finalPremises, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  all_goals first | trivial | exact fun impossible => impossible

theorem composed_callback_holds :
    (model.denote (applyArguments [.prop, .prop]
      (HOL.subst later (HOL.subst earlier (targetConditions first))) fields) values).down :=
  Soundness.extDerivation_sound finalProof.erase
    (model.functionsRespectEqv_of_fullDomains ConstructorDataPredicates.ProgramControls.full)
    (fun _ => ConstructorDataPredicates.ProgramControls.full _ _) assumptions_realizable

theorem duplicate_occurrences_remain_distinct :
    reindex.index ⟨0, by decide⟩ ≠ reindex.index ⟨2, by decide⟩ := by decide

theorem selected_last_occurrence :
    finalOccurrences.index (reindex.index ⟨2, by decide⟩) = ⟨3, by decide⟩ := rfl

private def rightPremiseObservation (tree : ProofSyntax.Tree Constants) : Option ProofSyntax.RuleObservation :=
  match tree with
  | .node _ _ 2 children =>
      match children ⟨1, by decide⟩ with
      | .node _ observation _ _ => some observation
  | _ => none

theorem actual_retained_occurrence :
    rightPremiseObservation finalProof.observe = some ⟨.hyp, some 3⟩ := by
  decide +kernel

theorem actual_composition_selects_outer : HOL.subst later (earlier .vz) = .top := rfl

theorem wrong_later_binding_refused :
    ¬ (model.denote (ConstructorDataPredicates.guard signature
      (fun occurrence => HOL.subst wrongLater (HOL.subst earlier (targetConditions occurrence)))
      ConstructorDataPredicates.ProgramControls.packed) values).down := by
  intro admitted
  exact (ConstructorDataPredicates.guard_on_encoded model
    ConstructorDataPredicates.ProgramControls.full signature _ first fields values).mp admitted

#print axioms transportedCallback_free
#print axioms finalProof
#print axioms finalProof_free
#print axioms assumptions_realizable
#print axioms composed_callback_holds
#print axioms duplicate_occurrences_remain_distinct
#print axioms selected_last_occurrence
#print axioms actual_retained_occurrence
#print axioms actual_composition_selects_outer
#print axioms wrong_later_binding_refused

end Mettapedia.Logic.HOL.ConstructorGuardSubstitutionControls
