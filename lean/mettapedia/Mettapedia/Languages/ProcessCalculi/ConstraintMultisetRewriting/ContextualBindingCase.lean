import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualBindingReduction
import Mettapedia.OSLF.Syntax.BindingVariableSpineApplications
import Mettapedia.OSLF.Syntax.BindingRenamingSlots
import Mettapedia.OSLF.Syntax.BindingRenamingInverse
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPatternReflection

/-!
# Recoverable bindings retain their selected declaration and actual body

The executable case uses the common variable-spine recognizer, finite inverse
and strengthening operation. Its result retains the selected identity, the
scope-correct body, occurrence refusal and support coverage, together with
the principal-answer proof over every future declaration family. This data
connects the worklist's actual choice to finite active-roster progress.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualBindingCase

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily

variable {S : Signature} {V : Type} [DecidableEq V] {source : V → MetaArity S}

structure Case {Γ : Ctx S} {sort : S.Srt}
    (left right : Term (signature S source) Γ sort) where
  chosen : V
  body : Term (signature S source) (source chosen).1 (source chosen).2
  absent : chosen ∉ support body
  selected : chosen ∈ support left ++ support right
  body_covered : ∀ identity ∈ support body, identity ∈ support left ++ support right
  pattern_body : ContextualPatternFragment.Pattern S source left →
    ContextualPatternFragment.Pattern S source right → ContextualPatternFragment.Pattern S source body
  recovered : ∃ rho : Ren S (source chosen).1 Γ,
    (observe left = observe (rename (S := signature S source) rho (generator source chosen)) ∧
      observe right = observe (rename (S := signature S source) rho body)) ∨
    (observe right = observe (rename (S := signature S source) rho (generator source chosen)) ∧
      observe left = observe (rename (S := signature S source) rho body))
  principal : ContextualFrameUnifier.Principal [(left, right)] (ContextualBinding.answer chosen body)

def tryLeft [DecidableEq S.Srt] : {Γ : Ctx S} → {sort : S.Srt} →
    (left right : Term (signature S source) Γ sort) → Option (Case left right)
  | _, _, .op (.inr (.mk chosen)) arguments, target => by
      exact match recognized : VariableSpines.recognize (S := signature S source) (source chosen).1 arguments with
      | none => none
      | some rho => by
          by_cases distinct : RenamingSlots.check (S := signature S source) rho = true
          · let inverse := RenamingInverse.strengthener (S := signature S source) rho
              ((RenamingSlots.check_iff rho).mp distinct)
            exact match recovered : strengthenT inverse target with
            | none => none
            | some body => by
                by_cases absent : chosen ∉ support body
                · refine some ⟨chosen, body, absent, ?_, ?_, ?_, ?_, ?_⟩
                  · exact List.mem_append_left _ List.mem_cons_self
                  · intro identity named
                    have restored := (strengthenT_eq_some_iff inverse target body).mp recovered
                    have names : support body = support target :=
                      (support_rename (S := S) rho body).symm.trans (congrArg support restored)
                    exact List.mem_append_right _ (names ▸ named)
                  · intro _ patterned
                    exact ContextualPatternFragment.recovered_body_is_pattern (S := S) (source := source)
                      rho inverse target body recovered patterned
                  · refine ⟨rho, .inl ⟨?_, ?_⟩⟩
                    · exact congrArg observe (VariableSpines.application_eq_rename_generator chosen arguments rho
                        (VariableSpines.sound _ arguments rho recognized))
                    · exact congrArg observe ((strengthenT_eq_some_iff inverse target body).mp recovered).symm
                  · rw [VariableSpines.application_eq_rename_generator chosen arguments rho
                      (VariableSpines.sound _ arguments rho recognized)]
                    apply ContextualBindingReduction.principal (S := S) (declaration := source) chosen rho inverse target
                      (ContextualBinding.answer (S := S) (declaration := source) chosen body)
                    simp only [ContextualPatternBinding.solve?, recovered]
                    simp [ContextualBinding.solve?, absent]
                · exact none
          · exact none
  | _, _, _, _ => none

def Case.swap {Γ : Ctx S} {sort : S.Srt} {left right : Term (signature S source) Γ sort}
    (binding : Case right left) : Case left right where
  chosen := binding.chosen
  body := binding.body
  absent := binding.absent
  selected := by simpa only [List.mem_append, or_comm] using binding.selected
  body_covered := fun identity named => by
    simpa only [List.mem_append, or_comm] using binding.body_covered identity named
  pattern_body := fun first second => binding.pattern_body second first
  recovered := by
    obtain ⟨rho, first | second⟩ := binding.recovered
    · exact ⟨rho, .inr first⟩
    · exact ⟨rho, .inl second⟩
  principal := by
    constructor
    · intro equation member
      have same := List.mem_singleton.mp member
      subst equation
      exact (binding.principal.sound _ (List.mem_singleton_self _)).symm
    · intro Next next candidate solved
      apply binding.principal.factors next candidate
      intro equation member
      have same := List.mem_singleton.mp member
      subst equation
      exact (solved _ (List.mem_singleton_self _)).symm

def tryTerms [DecidableEq S.Srt] {Γ : Ctx S} {sort : S.Srt}
    (left right : Term (signature S source) Γ sort) : Option (Case left right) :=
  (tryLeft left right).orElse fun _ => (tryLeft right left).map Case.swap

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualBindingCase
