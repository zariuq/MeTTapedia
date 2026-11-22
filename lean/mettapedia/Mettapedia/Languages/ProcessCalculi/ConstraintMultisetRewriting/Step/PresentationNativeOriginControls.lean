import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PresentationNativeOrigins
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PresentationNativeControls

/-!
# Rule aliases do not authorize changed native publications

The controls use the existing conditional-template execution. Its two native
firings have equal rule and selection data but different publication recipes
and different results. The origin profile can permit one complete firing,
refuse the other, and refuse another key resolving to the same stored rule.
Preparation remains available independently of these refusals.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.NativeOriginControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Interface NativeOrigins ContextualConditionalTemplateControls

local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (sort : base.Srt) : DecidableEq (base.Op sort) := inferInstanceAs (DecidableEq Operation)

abbrev originState := NativeControls.state
abbrev nativeStep := (native (S := base) (O := Nat) (Γ := []) (sort := ())).toStep

noncomputable def catalogueAt (rule : RuleData originState) :
    Catalogue (S := base) (O := Nat) (Γ := []) (sort := ()) := by
  classical
  exact fun state key => if inside : state = originState then
    if key < 2 then some (inside.symm ▸ rule) else none
    else none

theorem lookup_alias (rule : RuleData originState) (key : Nat) (valid : key < 2) :
    catalogueAt rule originState key = some rule := by
  classical
  simp [catalogueAt, valid]

def permitsExactly (firing : NativeFiring originState) :
    (state : NativeState base Nat [] ()) → Nat → NativeFiring state → Prop :=
  fun _ key candidate => key = 0 ∧ HEq candidate firing

theorem actual_publication_controls (fuel : Nat) :
    ∃ (first second : NativeFiring originState)
      (admittedFirst : first.Realized) (admittedSecond : second.Realized),
      first.rule = second.rule ∧ first.selection = second.selection ∧
      (profile (catalogueAt first.rule) (permitsExactly first)).Admits ⟨0, first⟩ ∧
      ¬ (profile (catalogueAt first.rule) (permitsExactly first)).Admits ⟨1, first⟩ ∧
      ¬ (profile (catalogueAt first.rule) (permitsExactly first)).Admits ⟨0, second⟩ ∧
      (profile (catalogueAt first.rule) (permitsExactly first)).Prepares ⟨1, first⟩ ∧
      nativeStep.result first admittedFirst ≠ nativeStep.result second admittedSecond ∧
      ∃ source : SourceEvent (catalogueAt first.rule) (permitsExactly first) originState
          (nativeStep.result first admittedFirst),
        source.event.firing.origin = 0 ∧ (source.erase _ _).firing = first := by
  obtain ⟨first, second, admittedFirst, admittedSecond, sameRule, sameSelection, _, _, _, _, different⟩ :=
    PublicationControls.native_result_depends_on_recipes fuel
  have distinct : first ≠ second := by
    intro same
    subst second
    exact different rfl
  have looked := lookup_alias first.rule 0 (by decide)
  have permitted : permitsExactly first originState 0 first := ⟨rfl, HEq.rfl⟩
  have accepted : (profile (catalogueAt first.rule) (permitsExactly first)).Admits ⟨0, first⟩ :=
    ⟨admittedFirst, looked, permitted⟩
  refine ⟨first, second, admittedFirst, admittedSecond, sameRule, sameSelection, accepted, ?_, ?_, ?_, different, ?_⟩
  · intro wrong
    exact Nat.one_ne_zero wrong.2.2.1
  · intro wrong
    exact distinct (eq_of_heq wrong.2.2.2).symm
  · exact nativeStep.prepares admittedFirst
  · obtain ⟨source, erased, origin⟩ := lift_native_event (catalogueAt first.rule) (permitsExactly first) 0
      (nativeStep.event first admittedFirst) looked permitted
    exact ⟨source, origin, congrArg (fun event => event.firing) erased⟩

theorem absent_origin_refused (firing : NativeFiring originState) :
    ¬ (profile (catalogueAt firing.rule) (fun _ _ _ => True)).Admits ⟨2, firing⟩ := by
  intro admitted
  have resolved := admitted.2.1
  simp [catalogueAt] at resolved

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.NativeOriginControls
