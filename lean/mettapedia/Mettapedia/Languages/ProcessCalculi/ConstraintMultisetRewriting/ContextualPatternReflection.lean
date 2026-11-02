import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPatternPreservation
import Mettapedia.OSLF.Syntax.BindingRenamingInverse
import Mettapedia.OSLF.Syntax.BindingRenamingShapes

/-!
# Structural patterns reflect through object renaming and recovery

If a renamed term is a structural pattern, its original arguments were
already distinct variables. Renaming cannot turn a compound argument into
a variable, or turn a repeated variable into distinct ones. This reflection
law needs no injectivity assumption on the ambient map. It justifies pattern
preservation for a body actually recovered by strengthening.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPatternFragment

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily

variable {S : Signature} {V : Type} {source : V → MetaArity S}

theorem rename_reflects {Γ Δ : Ctx S} {sort : S.Srt}
    (term : Term (signature S source) Γ sort) (rho : Ren S Γ Δ)
    (patterned : Pattern S source (rename (S := signature S source) rho term)) : Pattern S source term := by
  classical
  refine Pattern.rec (S := S) (declaration := source)
    (motive_1 := fun {context} result value _ =>
      ∀ {originalContext : Ctx S} (original : Term (signature S source) originalContext result)
        (mapping : Ren S originalContext context),
        rename (S := signature S source) mapping original = value → Pattern S source original)
    (motive_2 := fun {arities} {context} values _ =>
      ∀ {originalContext : Ctx S} (original : Args (signature S source) arities originalContext)
        (mapping : Ren S originalContext context),
        renameArgs (S := signature S source) mapping original = values → PatternArgs S source original)
    ?_ ?_ ?_ ?_ ?_ patterned term rho rfl
  · intro context result position originalContext original mapping same
    obtain ⟨position, rfl, _⟩ := Mettapedia.OSLF.Binding.rename_eq_variable (S := signature S source) mapping original position same
    exact .object position
  · intro context result operator arguments fields checked originalContext original mapping same
    obtain ⟨originalArgs, rfl, fields⟩ := ArgumentSlots.rename_eq_operator
      (S := signature S source) mapping original (.inl operator) arguments same
    exact .rigid operator originalArgs (checked originalArgs mapping fields)
  · intro context identity arguments spineMap spine distinct originalContext original mapping same
    obtain ⟨originalArgs, rfl, fields⟩ := ArgumentSlots.rename_eq_operator
      (S := signature S source) mapping original (.inr (.mk identity)) arguments same
    have each : ∀ sort (position : Var (source identity).1 sort),
        ∃ original, argsToSub originalArgs sort position = Term.var (S := signature S source) original ∧
          mapping sort original = spineMap sort position := by
      intro sort position
      have known := spine sort position
      rw [← fields, argsToSub_renameArgs] at known
      exact Mettapedia.OSLF.Binding.rename_eq_variable (S := signature S source) mapping
        (argsToSub originalArgs sort position) (spineMap sort position) known
    let originalMap : Ren S (source identity).1 originalContext := fun sort position => (each sort position).choose
    apply Pattern.hole identity originalArgs originalMap
    · exact fun sort position => (each sort position).choose_spec.1
    · intro sort first second same
      apply distinct sort
      calc
        spineMap sort first = mapping sort (originalMap sort first) := (each sort first).choose_spec.2.symm
        _ = mapping sort (originalMap sort second) := congrArg (mapping sort) same
        _ = spineMap sort second := (each sort second).choose_spec.2
  · intro context originalContext original mapping same
    match original with
    | .nil => exact .nil
  · intro arities context binders result head tail first rest checkedHead checkedTail originalContext original mapping same
    match original with
    | .cons originalHead originalTail =>
        have parts := Args.cons.inj same
        exact .cons originalHead originalTail
          (checkedHead originalHead (liftRen mapping binders) parts.1)
          (checkedTail originalTail mapping parts.2)

theorem renameArgs_reflects : ∀ {arities : List (MetaArity S)} {Γ Δ : Ctx S}
    (arguments : Args (signature S source) arities Γ) (rho : Ren S Γ Δ),
    PatternArgs S source (renameArgs (S := signature S source) rho arguments) → PatternArgs S source arguments
  | _, _, _, .nil, _, _ => .nil
  | _, _, _, .cons (bs := binders) head tail, rho, patterned => by
      have checked := checkArgs_complete (S := S) (declaration := source)
        (renameArgs (S := signature S source) rho (.cons head tail)) patterned
      have both : check (rename (S := signature S source) (liftRen rho binders) head) = true ∧
          checkArgs (renameArgs (S := signature S source) rho tail) = true := by
        simpa only [renameArgs, checkArgs, Bool.and_eq_true] using checked
      exact .cons head tail
        (rename_reflects (S := S) (source := source) head (liftRen rho binders)
          (check_sound (S := S) (declaration := source) _ both.1))
        (renameArgs_reflects tail rho
          (checkArgs_sound (S := S) (declaration := source) _ both.2))

theorem recovered_body_is_pattern {Γ Δ : Ctx S} {sort : S.Srt}
    (rho : Ren S Γ Δ) (inverse : Strengthener (S := signature S source) rho)
    (target : Term (signature S source) Δ sort) (body : Term (signature S source) Γ sort)
    (recovered : strengthenT inverse target = some body) (patterned : Pattern S source target) :
    Pattern S source body := by
  apply rename_reflects (S := S) (source := source) body rho
  rw [rename_strengthenT (S := signature S source) inverse target body recovered]
  exact patterned

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPatternFragment
