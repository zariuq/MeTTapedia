import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualTransportedActivation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.OccurrenceRelabeling
import Mettapedia.OSLF.Syntax.ContextualRigidReflection
import Mathlib.Data.List.OfFn

/-!
# Rigid data travel through actual contextual preparation unchanged

This is a profile of the existing contextual activation over an arbitrary
binding signature and declaration families. It retains the actual source
rule, selected occurrence order, prepared scopes and full prior equation
store. It does not assert a solver result or replace a returned solver answer.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualRigidActivation

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily

universe uT uO
variable {S : Signature} {T : Type uT} {O : Type uO} {Local Shared : Type}
  (locals : Local → MetaArity S) (captures : Shared → MetaArity S)
  {Γ : Ctx S} {sort : S.Srt} (encode : T → Term S Γ sort)

def into {V : Type} (declaration : V → MetaArity S) (value : T) :
    Term (signature S declaration) Γ sort := Rigid.includeTerm declaration (encode value)

def rule (original : RuleInstance T) :
    RuleInstance (Term (signature S (ContextualActivatedStep.source locals captures)) Γ sort) :=
  original.map (into encode (ContextualActivatedStep.source locals captures))

def rows (label : O → T) : O → ContextualStoredRows.Row locals captures Γ sort :=
  fun occurrence => .shared (into encode captures (label occurrence))

def before (original : Configuration T O) : Configuration (Term (signature S captures) Γ sort) O :=
  OccurrenceRelabeling.configuration (into encode captures) original

def withFrame (extra : EquationStore (Term (signature S captures) Γ sort))
    (original : Configuration T O) : Configuration (Term (signature S captures) Γ sort) O :=
  ⟨extra ++ (before captures encode original).equations, original.present⟩

def outputs (label : O → T) : O → Term (signature S (ContextualActivatedStep.target locals captures)) Γ sort :=
  into encode (ContextualActivatedStep.target locals captures) ∘ label

theorem term_at (allocated : Nat) (value : T) :
    ContextualFreshening.termAt locals captures allocated
      (into encode (ContextualActivatedStep.source locals captures) value) =
        into encode (ContextualActivatedStep.target locals captures) value :=
  Rigid.instantiate_include _ _

theorem prepared_rule (occupied : Finset Nat) (selection : Selection O) (original : RuleInstance T)
    (label : O → T) :
    (ContextualActivatedStep.prepared locals captures occupied selection
      (rule locals captures encode original) (rows locals captures encode label)).rule =
        original.map (into encode (ContextualActivatedStep.target locals captures)) := by
  change (original.map (into encode (ContextualActivatedStep.source locals captures))).map
    (ContextualFreshening.termAt locals captures
      (ContextualActivationScopes.scopeAt occupied (ContextualActivationScopes.rulePort selection))) = _
  rw [OccurrenceRelabeling.rule_map_comp]
  apply congrArg (fun change => original.map change)
  funext value
  exact term_at locals captures encode _ value

theorem prepared_take (occupied : Finset Nat) (selection : Selection O) (original : RuleInstance T)
    (label : O → T) (index : Fin selection.taken.length) :
    (ContextualActivatedStep.prepared locals captures occupied selection
      (rule locals captures encode original) (rows locals captures encode label)).taken index =
        into encode (ContextualActivatedStep.target locals captures) (label (selection.taken.get index)) := by
  rw [ContextualActivatedStep.prepared_taken_view]
  exact Rigid.instantiate_include _ _

theorem prepared_read (occupied : Finset Nat) (selection : Selection O) (original : RuleInstance T)
    (label : O → T) (index : Fin selection.read.length) :
    (ContextualActivatedStep.prepared locals captures occupied selection
      (rule locals captures encode original) (rows locals captures encode label)).read index =
        into encode (ContextualActivatedStep.target locals captures) (label (selection.read.get index)) := by
  rw [ContextualActivatedStep.prepared_read_view]
  exact Rigid.instantiate_include _ _

theorem taken_list (occupied : Finset Nat) (selection : Selection O) (original : RuleInstance T)
    (label : O → T) :
    List.ofFn (ContextualActivatedStep.prepared locals captures occupied selection
      (rule locals captures encode original) (rows locals captures encode label)).taken =
        selection.taken.map (outputs locals captures encode label) := by
  calc
    _ = List.ofFn (fun index => into encode (ContextualActivatedStep.target locals captures)
        (label (selection.taken.get index))) := congrArg List.ofFn (funext (prepared_take locals captures encode occupied selection original label))
    _ = _ := by
      simpa only [List.get_eq_getElem, outputs, Function.comp_def] using
        List.ofFn_getElem_eq_map selection.taken (outputs locals captures encode label)

theorem read_list (occupied : Finset Nat) (selection : Selection O) (original : RuleInstance T)
    (label : O → T) :
    List.ofFn (ContextualActivatedStep.prepared locals captures occupied selection
      (rule locals captures encode original) (rows locals captures encode label)).read =
        selection.read.map (outputs locals captures encode label) := by
  calc
    _ = List.ofFn (fun index => into encode (ContextualActivatedStep.target locals captures)
        (label (selection.read.get index))) := congrArg List.ofFn (funext (prepared_read locals captures encode occupied selection original label))
    _ = _ := by
      simpa only [List.get_eq_getElem, outputs, Function.comp_def] using
        List.ofFn_getElem_eq_map selection.read (outputs locals captures encode label)

theorem frame (original : Configuration T O) :
    ContextualActivatedStep.frame locals captures (before captures encode original) =
      OccurrenceRelabeling.configuration (into encode (ContextualActivatedStep.target locals captures)) original := by
  apply congrArg₂ Configuration.mk
  · simp only [before, OccurrenceRelabeling.configuration,
      OccurrenceRelabeling.equations, ContextualFrameUnifier.mapProblem, List.map_map]
    apply List.map_congr_left
    intro equation _
    exact congrArg₂ Prod.mk (Rigid.instantiate_include _ _) (Rigid.instantiate_include _ _)
  · rfl

theorem problem (occupied : Finset Nat) (selection : Selection O) (original : RuleInstance T)
    (label : O → T) (state : Configuration T O) :
    ContextualActivatedStep.problem locals captures occupied selection
      (rule locals captures encode original) (rows locals captures encode label) (before captures encode state) =
        OccurrenceRelabeling.equations (into encode (ContextualActivatedStep.target locals captures))
          (selection.problem label original state) := by
  dsimp only [ContextualActivatedStep.problem]
  rw [frame, prepared_rule, taken_list, read_list]
  simpa only [Selection.problem, ContextualActivatedStep.useEquations,
    OccurrenceRelabeling.selection_values, outputs] using
    OccurrenceRelabeling.problem (into encode (ContextualActivatedStep.target locals captures))
      label original selection state

theorem problem_withFrame (extra : EquationStore (Term (signature S captures) Γ sort))
    (occupied : Finset Nat) (selection : Selection O) (original : RuleInstance T)
    (label : O → T) (state : Configuration T O) :
    ContextualActivatedStep.problem locals captures occupied selection
      (rule locals captures encode original) (rows locals captures encode label) (withFrame captures encode extra state) =
      ContextualFrameUnifier.mapProblem (ContextualSelectionViews.capturedTarget locals captures) extra ++
        ContextualActivatedStep.problem locals captures occupied selection
          (rule locals captures encode original) (rows locals captures encode label) (before captures encode state) := by
  simp only [ContextualActivatedStep.problem, ContextualActivatedStep.frame, withFrame,
    ContextualFrameUnifier.mapProblem, List.map_append, List.append_assoc]

/-- Transport into the actual returned declaration frame retains the
entire prior-and-selected equation store and the same physical fire. -/
theorem result [DecidableEq O] {W : Type} {next : W → MetaArity S}
    (change : Assignment (ContextualActivatedStep.target locals captures) next)
    (occupied : Finset Nat) (selection : Selection O) (original : RuleInstance T)
    (label : O → T) (state : Configuration T O) :
    ContextualTransportedActivation.result locals captures change occupied selection
      (rule locals captures encode original) (rows locals captures encode label) (before captures encode state) =
        OccurrenceRelabeling.configuration (into encode next) (selection.result label original state) := by
  apply congrArg₂ Configuration.mk
  · change ContextualFrameUnifier.mapProblem change
      (ContextualActivatedStep.problem locals captures occupied selection
        (rule locals captures encode original) (rows locals captures encode label) (before captures encode state)) = _
    rw [problem]
    simp only [ContextualFrameUnifier.mapProblem,
      OccurrenceRelabeling.equations, Selection.result, List.map_map]
    apply List.map_congr_left
    intro equation _
    exact congrArg₂ Prod.mk (Rigid.instantiate_include _ _) (Rigid.instantiate_include _ _)
  · rfl

theorem result_withFrame_equations [DecidableEq O] {W : Type} {next : W → MetaArity S}
    (change : Assignment (ContextualActivatedStep.target locals captures) next)
    (extra : EquationStore (Term (signature S captures) Γ sort))
    (occupied : Finset Nat) (selection : Selection O) (original : RuleInstance T)
    (label : O → T) (state : Configuration T O) :
    (ContextualTransportedActivation.result locals captures change occupied selection
      (rule locals captures encode original) (rows locals captures encode label)
      (withFrame captures encode extra state)).equations =
      ContextualFrameUnifier.mapProblem change
        (ContextualFrameUnifier.mapProblem (ContextualSelectionViews.capturedTarget locals captures) extra) ++
        OccurrenceRelabeling.equations (into encode next) (selection.problem label original state) := by
  change ContextualFrameUnifier.mapProblem change
    (ContextualActivatedStep.problem locals captures occupied selection
      (rule locals captures encode original) (rows locals captures encode label)
      (withFrame captures encode extra state)) = _
  rw [problem_withFrame, problem]
  simp only [ContextualFrameUnifier.mapProblem, List.map_append]
  apply congrArg₂ List.append
  · rfl
  · simp only [OccurrenceRelabeling.equations, List.map_map]
    apply List.map_congr_left
    intro equation _
    exact congrArg₂ Prod.mk (Rigid.instantiate_include _ _) (Rigid.instantiate_include _ _)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualRigidActivation
