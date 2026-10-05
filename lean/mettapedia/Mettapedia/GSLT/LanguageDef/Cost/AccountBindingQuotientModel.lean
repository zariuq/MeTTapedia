import Mettapedia.GSLT.LanguageDef.Cost.AccountBindingQuotientSubstitution

/-!
# Binding operators on relative account classes

Every source operator descends at its original binder-indexed arity.
The operation/substitution law compares the raw full environment beneath
each binder with the actual lift in the quotient substitution clone.
Accounts remain local to their supplied expression positions.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Cost.AccountBindingQuotientModel

open _root_.CategoryTheory
open Mettapedia.OSLF.Binding
open BindingSubstitutionAlgebra
open FreeBindingTerms
open RawAccountBindingExtension
open RawAccountBindingLaws
open AccountBindingCongruence
open AccountBindingQuotientSubstitution

universe u

variable {S : Signature} (Q : BindingCloneAlgebra.Algebra.{u} S)
  (accountSort : S.Srt) (base : Over Q)

/-- Map each complete raw argument to its class at that argument's actual
binder-extended context. -/
def projectArguments {arities : List (List S.Srt × S.Srt)} {Γ : Ctx S}
    (args : Arguments Q accountSort base arities Γ) :
    FamilyArgs S (Carrier Q accountSort base) arities Γ :=
  Arguments.map Q accountSort base (fun {_Γ _sort} value => project Q accountSort base value) args

/-- Representatives retain all argument positions and declared binders. -/
noncomputable def representativeArgs :
    {arities : List (List S.Srt × S.Srt)} → {Γ : Ctx S} →
    FamilyArgs S (Carrier Q accountSort base) arities Γ →
      Arguments Q accountSort base arities Γ
  | _, _, .nil => .nil
  | _, _, .cons head tail => .cons (Quotient.out head) (representativeArgs tail)

theorem projectArguments_representative :
    ∀ {arities : List (List S.Srt × S.Srt)} {Γ : Ctx S}
      (args : FamilyArgs S (Carrier Q accountSort base) arities Γ),
      projectArguments Q accountSort base (representativeArgs Q accountSort base args) = args
  | _, _, .nil => rfl
  | _, _, .cons head tail => congrArg₂ FamilyArgs.cons
      (Quotient.out_eq head) (projectArguments_representative tail)

noncomputable def representativeArgs_project :
    ∀ {arities : List (List S.Srt × S.Srt)} {Γ : Ctx S}
      (args : Arguments Q accountSort base arities Γ),
      ArgumentDerivation Q accountSort base
        (representativeArgs Q accountSort base (projectArguments Q accountSort base args)) args
  | _, _, .nil => .nil
  | _, _, .cons head tail => by
      classical
      exact .cons (Classical.choice (Quotient.exact (Quotient.out_eq
        (project Q accountSort base head)))) (representativeArgs_project tail)

/-- Interpret a source operator without changing its argument sorts or
moving any account outside an argument's binders. -/
noncomputable def operation {Γ : Ctx S} {sort : S.Srt} (op : S.Op sort)
    (args : FamilyArgs S (Carrier Q accountSort base) (S.arity op) Γ) :
    Carrier Q accountSort base Γ sort :=
  project Q accountSort base (.operation op (representativeArgs Q accountSort base args))

theorem operation_project {Γ : Ctx S} {sort : S.Srt} (op : S.Op sort)
    (args : Arguments Q accountSort base (S.arity op) Γ) :
    operation Q accountSort base op (projectArguments Q accountSort base args) =
      project Q accountSort base (.operation op args) :=
  project_derivation Q accountSort base (.operation op
    (representativeArgs_project Q accountSort base args))

theorem operation_represented {Γ : Ctx S} {sort : S.Srt} (op : S.Op sort)
    (args : FamilyArgs S (Carrier Q accountSort base) (S.arity op) Γ)
    (rawArgs : Arguments Q accountSort base (S.arity op) Γ)
    (agree : projectArguments Q accountSort base rawArgs = args) :
    operation Q accountSort base op args =
      project Q accountSort base (.operation op rawArgs) := by
  rw [← agree]
  exact operation_project Q accountSort base op rawArgs

theorem project_substituteArguments {Γ Δ : Ctx S}
    (env : Environment S (Carrier Q accountSort base) Γ Δ) :
    ∀ {arities : List (List S.Srt × S.Srt)}
      (args : FamilyArgs S (Carrier Q accountSort base) arities Γ),
      projectArguments Q accountSort base
        (substituteArguments Q accountSort base (representativeEnv Q accountSort base env)
          (representativeArgs Q accountSort base args)) =
      (AccountBindingQuotientSubstitution.algebra Q accountSort base).substituteArgs env args
  | _, .nil => rfl
  | _, .cons (bs := binders) head tail => by
      apply congrArg₂ FamilyArgs.cons
      · have represented := substitute_represented Q accountSort base
          ((AccountBindingQuotientSubstitution.algebra Q accountSort base).liftEnvironment
            env binders)
          (RawAccountBindingLaws.liftEnvironment Q accountSort base
            (representativeEnv Q accountSort base env) binders)
          (liftEnvironment_represented Q accountSort base env binders) head
        have outEq := Quotient.out_eq head
        change project Q accountSort base (.substitute _ (Quotient.out head)) = _
        exact (congrArg (substituteRaw Q accountSort base
          (RawAccountBindingLaws.liftEnvironment Q accountSort base
            (representativeEnv Q accountSort base env) binders)) outEq).trans represented.symm
      · exact project_substituteArguments env tail

/-- Every authored operator is compatible with arbitrary marked semantic
substitution, lifted beneath its own binder lists. -/
theorem operation_substitute {Γ Δ : Ctx S} {sort : S.Srt}
    (env : Environment S (Carrier Q accountSort base) Γ Δ)
    (op : S.Op sort)
    (args : FamilyArgs S (Carrier Q accountSort base) (S.arity op) Γ) :
    substitute Q accountSort base env (operation Q accountSort base op args) =
      operation Q accountSort base op
        ((AccountBindingQuotientSubstitution.algebra Q accountSort base).substituteArgs env args) := by
  exact (project_equation Q accountSort base
    (.substituteOperation (representativeEnv Q accountSort base env) op
      (representativeArgs Q accountSort base args))).trans
    (operation_represented Q accountSort base op _ _
      (project_substituteArguments Q accountSort base env args)).symm

/-- A full binding clone, before its source observation and account action
are packaged into the relative model category. -/
noncomputable def algebra : BindingCloneAlgebra.Algebra.{u} S where
  substitution := AccountBindingQuotientSubstitution.algebra Q accountSort base
  operation := operation Q accountSort base
  operation_substitute := operation_substitute Q accountSort base

end Mettapedia.GSLT.LanguageDef.Cost.AccountBindingQuotientModel
