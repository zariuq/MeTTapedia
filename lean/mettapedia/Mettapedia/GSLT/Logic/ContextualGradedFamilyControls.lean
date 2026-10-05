import Mettapedia.GSLT.Logic.ContextualGradedFamilyDescent
import Mettapedia.GSLT.Logic.ObservedGradedFamilyControls

/-!
# Contexts reveal an otherwise hidden selected result

Two plain terminal states agree at every ordinary finite depth. An authored
wrapping context exposes their different flags. A material family of two
alternatives passes the ordinary observer, while its selected result cannot;
the contextual observer permits the same result and its exact material
decoder. The context operation itself acts on the constructed classes and
commutes with its substitution action.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.ContextualGradedFamilyControls

open Distinction.Constructive Distinction.Constructive.Controls
open AdmissibleContextCongruence AdmissibleContextCongruence.NecessityCanaries
open Mettapedia.TypeTheory.MaterialSets
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open PowerClassFamilyDescent

def flag : Wrapped → Bool
  | .plain bit => bit
  | .wrap bit => bit

def reading : Wrapped → ℤ
  | .plain _ => 0
  | .wrap bit => if bit then 1 else 0

def presented : PresentedSystem.{0, 0, 0, 0, 0} inertGSLT unitScale where
  dynamics := canarySystem
  Obs := Unit
  value _ := reading
  value_nonneg _ state := by
    cases state with
    | plain _ => exact (show (0 : ℤ) ≤ 0 by decide)
    | wrap bit => cases bit <;> decide
  value_le_one _ state := by
    cases state with
    | plain _ => exact (show (0 : ℤ) ≤ 1 by decide)
    | wrap bit => cases bit <;> decide
  value_resp _ _ _ same := congrArg reading same
  successors _ _ := []
  successors_act member := (List.not_mem_nil member).elim
  successors_cover step := by
    obtain ⟨_, _, impossible⟩ := step
    exact impossible.elim

def vocabulary : presented.Vocabulary where
  observations := [()]
  observations_complete _ := List.mem_singleton_self _
  labels := [.id, .wrap]
  labels_complete label := by
    cases label
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_singleton_self _)

theorem plain_bisimilar : presented.GradedBisimilar (.plain false) (.plain true) := by
  refine ⟨fun left right => left = .plain false ∧ right = .plain true, ?_, ⟨rfl, rfl⟩⟩
  constructor
  · intro left right related label target step
    obtain ⟨_, _, impossible⟩ := step
    exact impossible.elim
  constructor
  · intro left right related label target step
    obtain ⟨_, _, impossible⟩ := step
    exact impossible.elim
  · rintro left right ⟨rfl, rfl⟩ observation
    rfl

theorem ordinary_readout_equal (depth : Nat) :
    ObservedGradedFamilyDescent.readout presented depth (.plain false) =
      ObservedGradedFamilyDescent.readout presented depth (.plain true) :=
  (ObservedGradedFamilyDescent.readout_eq_iff presented vocabulary depth _ _).mpr
    (presented.depthBound_eq_zero_of_gradedBisimilar vocabulary plain_bisimilar depth)

theorem contextual_readout_separates (depth : Nat) :
    ContextualGradedFamilyDescent.readout presented everyContext depth (.plain false) ≠
      ContextualGradedFamilyDescent.readout presented everyContext depth (.plain true) := by
  intro same
  have atomic := congrFun (congrFun same ⟨.wrap, trivial⟩) ⟨.atom (), Nat.zero_le depth⟩
  exact (show (0 : ℤ) ≠ 1 by decide) atomic

theorem contextual_kernel_retains_flag (depth : Nat) {left right : Wrapped}
    (same : ContextualGradedFamilyDescent.readout presented everyContext depth left =
      ContextualGradedFamilyDescent.readout presented everyContext depth right) : flag left = flag right := by
  have atomic := congrFun (congrFun same ⟨.wrap, trivial⟩) ⟨.atom (), Nat.zero_le depth⟩
  change reading (wrapPlug .wrap left) = reading (wrapPlug .wrap right) at atomic
  cases left <;> cases right <;> rename_i leftFlag rightFlag
  all_goals cases leftFlag <;> cases rightFlag
  all_goals first
    | rfl
    | exact False.elim ((show (0 : ℤ) ≠ 1 by decide) atomic)
    | exact False.elim ((show (1 : ℤ) ≠ 0 by decide) atomic)

def alternatives (_ : Wrapped) : AccessiblePointedGraph := ObservedGradedFamilyControls.alternativesGraph

def selected (source : Wrapped) : El (· ∈ ·) (HSet.mk (alternatives source)) :=
  ObservedGradedFamilyControls.selectedAlternative (flag source)

theorem ordinary_family_descends (depth : Nat) :
    FamilyInvariant (ObservedGradedFamilyDescent.readout presented depth) alternatives :=
  fun _ _ _ => rfl

theorem ordinary_selected_result_does_not_descend (depth : Nat) :
    ¬ TermCompatible (ObservedGradedFamilyDescent.readout presented depth) alternatives selected := by
  intro compatible
  exact HSet.empty_ne_quineAtom (compatible (ordinary_readout_equal depth))

theorem contextual_family_descends (depth : Nat) :
    FamilyInvariant (ContextualGradedFamilyDescent.readout presented everyContext depth) alternatives :=
  fun _ _ _ => rfl

theorem contextual_selected_result_descends (depth : Nat) :
    TermCompatible (ContextualGradedFamilyDescent.readout presented everyContext depth) alternatives selected := by
  intro left right same
  exact congrArg (fun bit => (ObservedGradedFamilyControls.selectedAlternative bit).1)
    (contextual_kernel_retains_flag depth same)

theorem contextual_selected_decoder_exact (depth : Nat) (source : Wrapped) :
    termValue alternatives selected
        (classOf (ContextualGradedFamilyDescent.readout presented everyContext depth) source) =
      (selected source).1 :=
  termValue_beta _ alternatives selected (contextual_selected_result_descends depth) source

theorem wrap_kernel (depth : Nat) {left right : Wrapped}
    (same : ContextualGradedFamilyDescent.readout presented everyContext depth left =
      ContextualGradedFamilyDescent.readout presented everyContext depth right) :
    ContextualGradedFamilyDescent.readout presented everyContext depth (wrapPlug .wrap left) =
      ContextualGradedFamilyDescent.readout presented everyContext depth (wrapPlug .wrap right) :=
  ContextualGradedFamilyDescent.context_kernel_closed presented everyContext depth trivial same

theorem wrapping_substitution_commutes (depth : Nat)
    (observed : ContextualGradedFamilyDescent.Class presented everyContext depth) :
    ContextualGradedFamilyDescent.substitutionAction presented everyContext depth
        (wrapPlug .wrap) (@wrap_kernel depth)
        (ContextualGradedFamilyDescent.contextAction presented everyContext depth .wrap trivial observed) =
      ContextualGradedFamilyDescent.contextAction presented everyContext depth .wrap trivial
        (ContextualGradedFamilyDescent.substitutionAction presented everyContext depth
          (wrapPlug .wrap) (@wrap_kernel depth) observed) :=
  ContextualGradedFamilyDescent.context_substitution presented everyContext depth .wrap trivial
    (wrapPlug .wrap) (@wrap_kernel depth) (fun _ => rfl) observed

end Mettapedia.GSLT.ContextualGradedFamilyControls
