import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.RowCompiler
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.GroundRead

/-!
# Recovering used native-pattern images in arbitrary source families

The actual left-side compiler preserves rigid constructors. Equality of two
instances therefore recovers the images of every variable used by the native
pattern. Images may still contain unresolved source names; no closed decoder
or native scope guess is used in this lemma.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalGroundingPatterns

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation
open SourceLanguage SourceLanguage.Elaboration
open RuleBuilder

theorem recover_pattern {slots holes : Nat} (pattern : Tower.Tm slots)
    (images : Fin slots → Template holes) {compiled : Template holes}
    (built : RowCompiler.pattern images pattern = some compiled)
    {X : Type} {target : X → MetaArity MSig}
    (first second : Assignment (FoArity holes) target)
    (same : instantiate first compiled = instantiate second compiled) :
    ∀ index, 0 < AlgebraicSchema.variableMultiplicity index pattern →
      instantiate first (images index) = instantiate second (images index) := by
  induction pattern generalizing holes with
  | var position =>
      cases built
      intro index used
      have equal : index = position := by
        by_contra different
        simp [AlgebraicSchema.variableMultiplicity, Ne.symm different] at used
      subst index
      exact same
  | const _ | head _ =>
      intro index used
      exact False.elim (Nat.not_lt_zero _ used)
  | app function argument ihf iha =>
      obtain ⟨left, leftBuilt, later⟩ := Option.bind_eq_some_iff.mp built
      obtain ⟨right, rightBuilt, finished⟩ := Option.bind_eq_some_iff.mp later
      cases finished
      simp only [instantiate_node, List.map_cons, List.map_nil] at same
      have parts := Toolkit.tuple3_inj same
      intro index used
      change 0 < AlgebraicSchema.variableMultiplicity index function +
        AlgebraicSchema.variableMultiplicity index argument at used
      by_cases inLeft : 0 < AlgebraicSchema.variableMultiplicity index function
      · exact ihf images leftBuilt first second parts.2.1 index inLeft
      · exact iha images rightBuilt first second parts.2.2 index (by omega)
  | refl subject ih =>
      obtain ⟨value, valueBuilt, finished⟩ := Option.bind_eq_some_iff.mp built
      cases finished
      simp only [instantiate_node, List.map_cons, List.map_nil] at same
      exact ih images valueBuilt first second (Toolkit.tuple2_inj same).2
  | _ => cases built

theorem lists_agree {holes : Nat} {X : Type} {target : X → MetaArity MSig}
    (first second : Assignment (FoArity holes) target) (values : List (Template holes))
    (agree : ∀ value ∈ values, instantiate first value = instantiate second value) :
    instantiate first (RowCompiler.listTemplate values) =
      instantiate second (RowCompiler.listTemplate values) := by
  induction values with
  | nil => simp only [RowCompiler.listTemplate, instantiate_node, List.map_nil]
  | cons value rest ih =>
      simp only [RowCompiler.listTemplate, instantiate_node, List.map_cons, List.map_nil]
      rw [agree value List.mem_cons_self, ih (fun value inside => agree value (List.mem_cons_of_mem _ inside))]

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalGroundingPatterns

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalGroundingPatterns.recover_pattern
