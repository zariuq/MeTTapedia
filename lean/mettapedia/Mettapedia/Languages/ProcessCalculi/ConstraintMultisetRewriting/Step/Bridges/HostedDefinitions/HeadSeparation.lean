import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.BinderCoreAnswers

/-!
# Literal head separation for finite hosted equation programs

A literal tuple head survives metavariable instantiation. This is a syntactic
property of the selected fixed program; it is not an authority or sealing
contract for arbitrary surrounding equations.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage SourceLanguage.Elaboration SourceLanguage.Toolkit

def literalSymbol {X : Type} {decl : X → MetaArity MSig} {Γ : Ctx MSig} {sort : Unit} :
    Term (signature MSig decl) Γ sort → Option String
  | .op (.inl (.sym name)) _ => some name
  | _ => none

def firstSymbol {X : Type} {decl : X → MetaArity MSig} {Γ : Ctx MSig} {arity : List (MetaArity MSig)} :
    Args (signature MSig decl) arity Γ → Option String
  | .nil => none
  | .cons first _ => literalSymbol first

/-- The first literal symbol of a tuple; a variable head is deliberately unknown. -/
def literalHead {X : Type} {decl : X → MetaArity MSig} : Term (signature MSig decl) [] () → Option String
  | .op (.inl (.tup _)) arguments => firstSymbol arguments
  | _ => none

def closedHead (term : MClosed) : Option String :=
  literalHead (Rigid.includeTerm noNames term)

theorem literalSymbol_instantiate {X Y : Type} {decl : X → MetaArity MSig} {target : Y → MetaArity MSig}
    (assignment : Assignment decl target) :
    ∀ {Γ : Ctx MSig} {sort : Unit} (term : Term (signature MSig decl) Γ sort) {name : String},
      literalSymbol term = some name → literalSymbol (instantiate assignment term) = some name
  | _, _, .var _, _, headed => by simp [literalSymbol] at headed
  | _, _, .op (.inl (.sym _)) _, _, headed => headed
  | _, _, .op (.inl (.num _)) _, _, headed => by simp [literalSymbol] at headed
  | _, _, .op (.inl (.tup _)) _, _, headed => by simp [literalSymbol] at headed
  | _, _, .op (.inl .lam) _, _, headed => by simp [literalSymbol] at headed
  | _, _, .op (.inl .hold) _, _, headed => by simp [literalSymbol] at headed
  | _, _, .op (.inl .run) _, _, headed => by simp [literalSymbol] at headed
  | _, _, .op (.inr _) _, _, headed => by simp [literalSymbol] at headed

theorem firstSymbol_instantiate {X Y : Type} {decl : X → MetaArity MSig} {target : Y → MetaArity MSig}
    (assignment : Assignment decl target) :
    ∀ {Γ : Ctx MSig} {arity : List (MetaArity MSig)} (arguments : Args (signature MSig decl) arity Γ)
      {name : String}, firstSymbol arguments = some name →
      firstSymbol (instantiateArgs assignment arguments) = some name
  | _, _, .nil, _, headed => by cases headed
  | _, _, .cons first _, _, headed => literalSymbol_instantiate assignment first headed

theorem literalHead_instantiate {X Y : Type} {decl : X → MetaArity MSig} {target : Y → MetaArity MSig}
    (assignment : Assignment decl target) {term : Term (signature MSig decl) [] ()} {name : String}
    (headed : literalHead term = some name) : literalHead (instantiate assignment term) = some name := by
  cases term with
  | var impossible => nomatch impossible
  | op operator arguments =>
      cases operator with
      | inr hole => simp [literalHead] at headed
      | inl operator =>
          cases operator with
          | tup n => exact firstSymbol_instantiate assignment arguments headed
          | _ => simp [literalHead] at headed

theorem literalSymbol_include {X : Type} (decl : X → MetaArity MSig) {Γ : Ctx MSig} {sort : Unit}
    (term : Term MSig Γ sort) :
    literalSymbol (Rigid.includeTerm decl term) = literalSymbol (Rigid.includeTerm noNames term) := by
  cases term with
  | var index => rfl
  | op operator arguments => cases operator <;> rfl

theorem literalHead_include {X : Type} (decl : X → MetaArity MSig) (term : MClosed) :
    literalHead (Rigid.includeTerm decl term) = closedHead term := by
  cases term with
  | var impossible => nomatch impossible
  | op operator arguments =>
      cases operator with
      | tup n =>
          cases n with
          | zero => cases arguments; rfl
          | succ n =>
              cases arguments with
              | cons first rest => exact literalSymbol_include decl first
      | _ => rfl

theorem literalHead_of_reads {κ : Keys MSig} {store : List (Constraint κ [] ())}
    {term : Data κ [] ()} {value : MClosed} {name : String}
    (headed : literalHead term = some name) (read : Reads store term value) : closedHead value = some name := by
  obtain ⟨X, target, assignment, _, same⟩ := read
  have h := literalHead_instantiate assignment headed
  rw [same, literalHead_include] at h
  exact h

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions
