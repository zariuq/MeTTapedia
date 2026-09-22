import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeDeclarationSpineSubstitution

/-!
# Checked native contractions returning a declared branch argument

The List nil case, identity reflexivity case, and relational List nil case
return an original branch argument. Declaration-spine recovery computes its
certificate at the instantiated declared type; replay restores the original
displayed type. Recursive cons cases additionally require construction of the
recursive branch applications and are not handled by this module.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeJudgmentReplay.BranchReturnComputation

open Presentation NativeIndexedFamilies DeclarationSpineReplay

def listNil {n : Nat} (contextCode : ContextCode n)
    (element motive nilCase consCase displayed : Tower.Tm n) (code : Code n) : Option (Code n) :=
  returnArgument contextCode
    (Intrinsic.eliminateApp element motive nilCase consCase (Intrinsic.nilApp element)) displayed code 2

theorem listNil_declared {n : Nat} (element motive nilCase consCase : Tower.Tm n) :
    declaredType (Intrinsic.eliminateApp element motive nilCase consCase (Intrinsic.nilApp element)) =
      some (.app motive (Intrinsic.nilApp element)) := by
  exact declaredType_subst Intrinsic.nilIotaLeft
    (Intrinsic.nilSchemaSubstitution element motive nilCase consCase)
    (type := Intrinsic.nilIotaResultType) (by decide +kernel)

theorem listNil_selected {n : Nat} (element motive nilCase consCase : Tower.Tm n) :
    (declaredArguments
      (Intrinsic.eliminateApp element motive nilCase consCase (Intrinsic.nilApp element))).bind
      (fun entries => entries[2]?) = some (nilCase, .app motive (Intrinsic.nilApp element)) := by
  exact selectedArgument_subst (Intrinsic.nilSchemaSubstitution element motive nilCase consCase)
    (subject := Intrinsic.nilIotaLeft) (argument := .var 1)
    (type := Intrinsic.nilIotaResultType) 2 (by decide +kernel)

theorem listNil_checked {n : Nat} {context : Tower.Ctx n} {contextCode : ContextCode n}
    {element motive nilCase consCase displayed : Tower.Tm n} {code : Code n}
    (accepted : check context
      (Intrinsic.eliminateApp element motive nilCase consCase (Intrinsic.nilApp element))
      displayed contextCode code = true) :
    ∃ output, listNil contextCode element motive nilCase consCase displayed code = some output ∧
      check context nilCase displayed contextCode output = true :=
  returnArgument_checked 2 accepted (listNil_declared ..) (listNil_selected ..)

#print axioms listNil_declared
#print axioms listNil_selected
#print axioms listNil_checked

def identity {n : Nat} (contextCode : ContextCode n)
    (element point motive reflCase displayed : Tower.Tm n) (code : Code n) : Option (Code n) :=
  returnArgument contextCode
    (Intrinsic.identityEliminateApp element point motive reflCase point (.refl point)) displayed code 3

theorem identity_checked {n : Nat} {context : Tower.Ctx n} {contextCode : ContextCode n}
    {element point motive reflCase displayed : Tower.Tm n} {code : Code n}
    (accepted : check context
      (Intrinsic.identityEliminateApp element point motive reflCase point (.refl point))
      displayed contextCode code = true) :
    ∃ output, identity contextCode element point motive reflCase displayed code = some output ∧
      check context reflCase displayed contextCode output = true := by
  apply returnArgument_checked 3 accepted
  · exact declaredType_subst Intrinsic.identityIotaLeft
      (Intrinsic.identitySchemaSubstitution element point motive reflCase)
      (type := Intrinsic.identityIotaResultType) (by decide +kernel)
  · exact selectedArgument_subst (Intrinsic.identitySchemaSubstitution element point motive reflCase)
      (subject := Intrinsic.identityIotaLeft) (argument := .var 0)
      (type := Intrinsic.identityIotaResultType) 3 (by decide +kernel)

def relNil {n : Nat} (contextCode : ContextCode n)
    (source target relation motive nilCase consCase displayed : Tower.Tm n)
    (code : Code n) : Option (Code n) :=
  returnArgument contextCode
    (IntrinsicRelator.eliminateApp source target relation motive nilCase consCase
      (Intrinsic.nilApp source) (Intrinsic.nilApp target)
      (IntrinsicRelator.nilRelApp source target relation)) displayed code 4

theorem relNil_checked {n : Nat} {context : Tower.Ctx n} {contextCode : ContextCode n}
    {source target relation motive nilCase consCase displayed : Tower.Tm n} {code : Code n}
    (accepted : check context
      (IntrinsicRelator.eliminateApp source target relation motive nilCase consCase
        (Intrinsic.nilApp source) (Intrinsic.nilApp target)
        (IntrinsicRelator.nilRelApp source target relation)) displayed contextCode code = true) :
    ∃ output, relNil contextCode source target relation motive nilCase consCase displayed code = some output ∧
      check context nilCase displayed contextCode output = true := by
  apply returnArgument_checked 4 accepted
  · exact declaredType_subst IntrinsicRelator.nilIotaLeft
      (FormationSensitiveNativeRelatorElimination.parameterSubstitution source target relation motive nilCase consCase)
      (type := IntrinsicRelator.nilIotaResultType) (by decide +kernel)
  · exact selectedArgument_subst
      (FormationSensitiveNativeRelatorElimination.parameterSubstitution source target relation motive nilCase consCase)
      (subject := IntrinsicRelator.nilIotaLeft) (argument := .var 1)
      (type := IntrinsicRelator.nilIotaResultType) 4 (by decide +kernel)

#print axioms identity_checked
#print axioms relNil_checked

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeJudgmentReplay.BranchReturnComputation
