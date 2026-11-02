import Mettapedia.OSLF.Syntax.BindingVariableSpines
import Mettapedia.OSLF.Syntax.BindingRenamingSlots
import Mettapedia.OSLF.Syntax.ContextualRigidTerms

/-!
# The structural contextual pattern fragment on the common binding terms

Rigid constructors may contain binding fields. Every flexible occurrence in
this fragment uses distinct object variables of its declared sorts, in any
order. The executable checker characterizes that independent structural
predicate. Repeated and compound arguments remain ordinary terms; failing
this checker does not refute them or their equations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPatternFragment

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily

variable {S : Signature} {V : Type} {declaration : V → MetaArity S}

mutual
inductive Pattern (S : Signature) {V : Type} (declaration : V → MetaArity S) :
    {Γ : Ctx S} → {sort : S.Srt} → Term (signature S declaration) Γ sort → Prop
  | object {Γ : Ctx S} {sort : S.Srt} (position : Var Γ sort) :
      Pattern S declaration (.var position)
  | rigid {Γ : Ctx S} {sort : S.Srt} (operator : S.Op sort)
      (arguments : Args (signature S declaration) (S.arity operator) Γ)
      (fields : PatternArgs S declaration arguments) :
      Pattern S declaration (.op (.inl operator) arguments)
  | hole {Γ : Ctx S} (identity : V)
      (arguments : Args (signature S declaration) ((declaration identity).1.map fun sort => ([], sort)) Γ)
      (rho : Ren S (declaration identity).1 Γ)
      (spine : ∀ sort index, argsToSub arguments sort index = .var (rho sort index))
      (injective : ∀ sort, Function.Injective (rho sort)) :
      Pattern S declaration (.op (.inr (.mk identity)) arguments)

inductive PatternArgs (S : Signature) {V : Type} (declaration : V → MetaArity S) :
    {arities : List (MetaArity S)} → {Γ : Ctx S} →
    Args (signature S declaration) arities Γ → Prop
  | nil {Γ : Ctx S} : PatternArgs S declaration (Γ := Γ) .nil
  | cons {arities : List (MetaArity S)} {Γ binders : Ctx S} {sort : S.Srt}
      (head : Term (signature S declaration) (binders ++ Γ) sort)
      (tail : Args (signature S declaration) arities Γ)
      (first : Pattern S declaration head) (rest : PatternArgs S declaration tail) :
      PatternArgs S declaration (.cons head tail)
end

mutual

/-- An ordinary scoped term contains no flexible occurrences, so its
inclusion is in the structural pattern fragment for every declaration family. -/
theorem rigid_inclusion_pattern (declaration : V → MetaArity S) :
    ∀ {Γ : Ctx S} {sort : S.Srt} (term : Term S Γ sort),
      Pattern S declaration (Rigid.includeTerm declaration term)
  | _, _, .var position => .object position
  | _, _, .op operator arguments => .rigid operator _ (rigid_arguments_pattern declaration arguments)

theorem rigid_arguments_pattern (declaration : V → MetaArity S) :
    ∀ {Γ : Ctx S} {arities : List (MetaArity S)} (arguments : Args S arities Γ),
      PatternArgs S declaration (Rigid.includeArgs declaration arguments)
  | _, _, .nil => .nil
  | _, _, .cons head tail => .cons _ _ (rigid_inclusion_pattern declaration head)
      (rigid_arguments_pattern declaration tail)

end

mutual
def check : {Γ : Ctx S} → {sort : S.Srt} → Term (signature S declaration) Γ sort → Bool
  | _, _, .var _ => true
  | _, _, .op (.inl _) arguments => checkArgs arguments
  | _, _, .op (.inr (.mk identity)) arguments =>
      match VariableSpines.recognize (S := signature S declaration) (declaration identity).1 arguments with
      | none => false
      | some rho => RenamingSlots.check (S := signature S declaration) rho

def checkArgs : {arities : List (MetaArity S)} → {Γ : Ctx S} →
    Args (signature S declaration) arities Γ → Bool
  | _, _, .nil => true
  | _, _, .cons head tail => check head && checkArgs tail
end

mutual
theorem check_sound : ∀ {Γ : Ctx S} {sort : S.Srt} (term : Term (signature S declaration) Γ sort),
    check term = true → Pattern S declaration term
  | _, _, .var position, _ => Pattern.object (S := S) (declaration := declaration) position
  | _, _, .op (.inl operator) arguments, accepted => .rigid operator arguments (checkArgs_sound arguments accepted)
  | _, _, .op (.inr (.mk identity)) arguments, accepted => by
      cases recognized : VariableSpines.recognize (S := signature S declaration) (declaration identity).1 arguments with
      | none => simp only [check, recognized, Bool.false_eq_true] at accepted
      | some rho =>
          exact Pattern.hole (S := S) (declaration := declaration) identity arguments rho
            (VariableSpines.sound (S := signature S declaration) _ arguments rho recognized)
            ((RenamingSlots.check_iff (S := signature S declaration) rho).mp
              (by simpa only [check, recognized] using accepted))

theorem checkArgs_sound : ∀ {arities : List (MetaArity S)} {Γ : Ctx S}
    (arguments : Args (signature S declaration) arities Γ), checkArgs arguments = true → PatternArgs S declaration arguments
  | _, _, .nil, _ => .nil
  | _, _, .cons head tail, accepted => by
      have both : check head = true ∧ checkArgs tail = true := by
        simpa only [checkArgs, Bool.and_eq_true] using accepted
      exact .cons head tail (check_sound head both.1) (checkArgs_sound tail both.2)
end

theorem check_complete {Γ : Ctx S} {sort : S.Srt} (term : Term (signature S declaration) Γ sort)
    (proof : Pattern S declaration term) : check (S := S) (declaration := declaration) term = true := by
  refine Pattern.rec
    (motive_1 := fun value _ => check (S := S) (declaration := declaration) value = true)
    (motive_2 := fun values _ => checkArgs (S := S) (declaration := declaration) values = true)
    ?_ ?_ ?_ ?_ ?_ proof
  · intro context result position
    rfl
  · intro context result operator arguments fields checked
    exact checked
  · intro context identity arguments rho spine injective
    change (match VariableSpines.recognize (S := signature S declaration) (declaration identity).1 arguments with
      | none => false
      | some recovered => RenamingSlots.check (S := signature S declaration) recovered) = true
    rw [VariableSpines.complete (S := signature S declaration) _ arguments rho spine]
    exact (RenamingSlots.check_iff (S := signature S declaration) rho).mpr injective
  · intro context
    rfl
  · intro arities context binders result head tail first rest checkedHead checkedTail
    change (check head && checkArgs tail) = true
    rw [checkedHead, checkedTail]
    rfl

theorem checkArgs_complete : ∀ {arities : List (MetaArity S)} {Γ : Ctx S}
    (arguments : Args (signature S declaration) arities Γ), PatternArgs S declaration arguments →
      checkArgs (S := S) (declaration := declaration) arguments = true
  | _, _, .nil, .nil => rfl
  | _, _, .cons head tail, .cons _ _ first rest => by
      simp only [checkArgs, check_complete head first, checkArgs_complete tail rest, Bool.and_self]

theorem check_iff {Γ : Ctx S} {sort : S.Srt} (term : Term (signature S declaration) Γ sort) :
    check term = true ↔ Pattern S declaration term := ⟨check_sound term, check_complete term⟩

theorem checkArgs_iff {arities : List (MetaArity S)} {Γ : Ctx S}
    (arguments : Args (signature S declaration) arities Γ) :
    checkArgs arguments = true ↔ PatternArgs S declaration arguments := ⟨checkArgs_sound arguments, checkArgs_complete arguments⟩

theorem generator_pattern (identity : V) : Pattern S declaration (generator declaration identity) := by
  apply Pattern.hole (S := S) (declaration := declaration) identity _ (fun _ position => position)
  · exact argsToSub_selfArgs (T := signature S declaration) (declaration identity).1
  · exact fun _ => Function.injective_id

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPatternFragment
