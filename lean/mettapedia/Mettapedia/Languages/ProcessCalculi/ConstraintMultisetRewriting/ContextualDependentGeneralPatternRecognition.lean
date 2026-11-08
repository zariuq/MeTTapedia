import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentGeneralPatternReplacement

/-!
# Recognizing general pattern equations from actual scoped equations

An active equation under a local telescope is read as `F x̄ ≐ t` when its
left side is literally an application spine of the newest outer
metavariable to distinct local variables, one for each binder of `F`'s
spine, with exact declaration compatibility and the pattern's result
annotation. Recognition is computed from syntax and returns pattern data
together with an exact solution correspondence for the original scoped
equation. Repeated arguments, non-variable arguments, outer arguments, or a
different head are not recognized; such equations remain with the caller
unchanged, which is never a refutation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentGeneralPattern

open CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentPiSpine ContextualDependentScope

variable {Head : Type}

/-- The head variable and variable arguments of an application spine. -/
def readApplication {m : Nat} : Tm Head m → Option (Fin m × List (Fin m))
  | .var head => some (head, [])
  | .app function (.var argument) => (readApplication function).map fun read => (read.1, read.2 ++ [argument])
  | _ => none

variable {rules : Rules Head}

/-- Assign a list of locals to the binders of a spine, outermost first. -/
def assign {Local : Type} : {Γ : Context rules} → {type : TypeOver Γ} → (spine : Spine type) →
    List Local → Option (spine.Local → Local)
  | _, _, .stop _, [] => some Empty.elim
  | _, _, .bind _ rest, first :: others => (assign rest others).map fun later => Sum.elim (fun _ => first) later
  | _, _, _, _ => none

theorem assign_mem {Local : Type} {Γ : Context rules} {type : TypeOver Γ} (spine : Spine type) :
    ∀ (values : List Local) (map : spine.Local → Local), assign spine values = some map →
      ∀ position, map position ∈ values := by
  induction spine with
  | stop type =>
      intro values map assigned position
      exact position.elim
  | bind shape rest ih =>
      intro values map assigned position
      cases values with
      | nil => cases assigned
      | cons first others =>
          cases found : assign rest others with
          | none => simp only [assign, found] at assigned; cases assigned
          | some later =>
          simp only [assign, found] at assigned
          cases assigned
          rcases position with ⟨⟩ | position
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (ih others later found position)

theorem assign_injective {Local : Type} {Γ : Context rules} {type : TypeOver Γ} (spine : Spine type) :
    ∀ (values : List Local) (map : spine.Local → Local), assign spine values = some map →
      values.Nodup → Function.Injective map := by
  induction spine with
  | stop type =>
      intro values map assigned distinct first
      exact first.elim
  | bind shape rest ih =>
      intro values map assigned distinct
      cases values with
      | nil => cases assigned
      | cons first others =>
          cases found : assign rest others with
          | none => simp only [assign, found] at assigned; cases assigned
          | some later =>
          simp only [assign, found] at assigned
          cases assigned
          have fresh := (List.nodup_cons.mp distinct).1
          have rest_injective := ih others later found (List.nodup_cons.mp distinct).2
          intro one two same
          rcases one with ⟨⟩ | one <;> rcases two with ⟨⟩ | two
          · rfl
          · have equal : first = later two := same
            exact (fresh (equal ▸ assign_mem rest others later found two)).elim
          · have equal : later one = first := same
            exact (fresh (equal ▸ assign_mem rest others later found one)).elim
          · exact congrArg Sum.inr (rest_injective same)

/-- The local variable at a position, if it is local. -/
def localOf {Γ : Context rules} {type : TypeOver Γ} (scope : Spine type) (index : Fin scope.target.arity) :
    Option scope.Local :=
  (scope.originEquiv.symm index).elim (fun _ => none) some

variable {Γ : Context rules} {type : TypeOver Γ}

/-- Recognized pattern data, with the exact correspondence of solutions. -/
structure Recognized (spine : Spine type) {scopeType : TypeOver (extend Γ type)} (scope : Spine scopeType)
    (active : Active scope.target) where
  pattern : Pattern spine scope
  right : Term scope.target ((lifted spine).result.reindex pattern.map.hom)
  holds_iff : ∀ {Δ : Context rules} (solution : Δ ⟶ extend Γ type),
    (scope.toScoped active).Holds solution ↔ (pattern.constraint right).Holds solution

instance {n m : Nat} (source : Ctx Head n) (target : Ctx Head m) (rho : Ren n m) [DecidableEq Head] :
    Decidable (CtxRen source target rho) := by
  unfold CtxRen
  infer_instance

/-- Decidable equality of spine binders. -/
def localDecidableEq : {Γ : Context rules} → {type : TypeOver Γ} → (spine : Spine type) → DecidableEq spine.Local
  | _, _, .stop _ => fun impossible _ => impossible.elim
  | _, _, .bind _ rest => @instDecidableEqSum _ _ _ (localDecidableEq rest)

variable [DecidableEq Head]

/-- Recognize `F x̄ ≐ t` from the actual left side. -/
def recognize (spine : Spine type) {scopeType : TypeOver (extend Γ type)} (scope : Spine scopeType)
    (active : Active scope.target) : Option (Recognized spine scope active) := by
  haveI := localDecidableEq scope
  refine match read : readApplication active.left.code with
    | none => none
    | some (_, arguments) =>
      match locals : arguments.mapM (localOf scope) with
      | none => none
      | some values =>
        match assigned : assign spine values with
        | none => none
        | some args =>
          if distinct : values.Nodup then
            if compatible : CtxRen (lifted spine).target.raw scope.target.raw
                (argRen (lifted spine) scope idRen (fun position => args (spine.localReindexEquiv _ position))) then
              let pattern : Pattern spine scope :=
                ⟨args, assign_injective spine values args assigned distinct, compatible⟩
              if sameType : active.type.code = ((lifted spine).result.reindex pattern.map.hom).code ∧
                  active.type.level = ((lifted spine).result.reindex pattern.map.hom).level then
                if sameLeft : active.left.code = pattern.application.code then
                  some ⟨pattern, ⟨active.right.code, sameType.1 ▸ active.right.typed⟩, ?_⟩
                else none
              else none
            else none
          else none
  intro Δ solution
  rw [Pattern.constraint, Spine.toScoped_holds_iff, Spine.toScoped_holds_iff]
  change Equal rules (scope.reindex solution).target.raw (subst (scope.map solution).substitution active.left.code)
      (subst (scope.map solution).substitution active.right.code)
      (subst (scope.map solution).substitution active.type.code) ↔
    Equal rules (scope.reindex solution).target.raw (subst (scope.map solution).substitution pattern.application.code)
      (subst (scope.map solution).substitution active.right.code)
      (subst (scope.map solution).substitution ((lifted spine).result.reindex pattern.map.hom).code)
  rw [sameLeft, sameType.1]

end ContextualDependentGeneralPattern
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
