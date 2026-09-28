import Mettapedia.Languages.Agda.Native.Selection

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Native.Production.Controls

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.Agda.Structural
open Statics

def setType : RawTy 0 := (universeType 0 1).code
def setGoal : AdministrativeStatics.Judgment := .core (typed .nil (universeTerm 0) setType)

def localA : TypeParameter 1 := ⟨0, .var .zero⟩
def localArrow : TypeParameter 1 := piType localA (.noBind localA)
def identityType : TypeParameter 0 := piType (universeType 0 0) (.bind localArrow)
def identityTerm : RawTm 0 := lam (lam (.var .zero))
def identityGoal : AdministrativeStatics.Judgment := .core (typed .nil identityTerm identityType.code)

def constantType : TypeParameter 0 := piType (universeType 0 0) (.noBind (universeType 0 1))
def constantTerm : RawTm 0 := lamNoAbs (universeTerm 0)
def constantGoal : AdministrativeStatics.Judgment := .core (typed .nil constantTerm constantType.code)

def identityFormation : AdministrativeStatics.Judgment := .core (formed .nil identityType.code)
def wrongUniverse : AdministrativeStatics.Judgment :=
  .core (typed .nil (universeTerm 0) (universeType 0 0).code)
def malformedContext : RawContext 1 :=
  .snoc .nil (el (set (levelClosed 0)) (defined "unadmitted"))
def variableInMalformedContext : AdministrativeStatics.Judgment :=
  .core (typed malformedContext (.var .zero) (ContextGeometry.lookup malformedContext .zero))

def functionContext : RawContext 1 :=
  .snoc .nil (piType (universeType 0 1) (.noBind (universeType 0 1))).code
def applicationGoal : AdministrativeStatics.Judgment :=
  .core (typed functionContext (app (.var .zero) (universeTerm 0)) (universeType 1 1).code)
def wrongArgument : AdministrativeStatics.Judgment :=
  .core (typed functionContext (app (.var .zero) (universeTerm 1)) (universeType 1 1).code)
def appendedGoal : AdministrativeStatics.Judgment :=
  .core (typed functionContext
    (eliminate (.var .zero) (append nil (cons (apply (universeTerm 0)) nil)))
    (universeType 1 1).code)
def unsupportedProjection : AdministrativeStatics.Judgment :=
  .core (typed functionContext
    (eliminate (.var .zero) (cons (proj "field") nil)) (universeType 1 1).code)

/-- Executable controls exercise the compiled producer. The generic soundness
proof covers every successful run; these controls also check operational
behavior on positive, negative, and resource-exhaustion examples. -/
def controls : List (String × Bool) := [
  ("Set", (run 4 setGoal).isEstablished),
  ("dependent identity", (run 20 identityGoal).isEstablished),
  ("nonbinding lambda", (run 12 constantGoal).isEstablished),
  ("dependent Pi formation", (run 20 identityFormation).isEstablished),
  ("exhaustion", (run 1 identityGoal).isIncomplete),
  ("wrong universe", (run 20 wrongUniverse).isIncomplete),
  ("malformed context", (run 20 variableInMalformedContext).isIncomplete),
  ("application spine", (run 20 applicationGoal).isEstablished),
  ("appended spine", (run 20 appendedGoal).isEstablished),
  ("incorrect argument type", (run 20 wrongArgument).isIncomplete),
  ("unsupported projection", (run 20 unsupportedProjection).isIncomplete)]

#eval do
  for (label, passed) in controls do
    unless passed = true do throw (IO.userError ("Structural producer control failed: " ++ label))
  IO.println s!"{controls.length} structural producer controls passed"

theorem set_checked : (run 4 setGoal).isEstablished = true := by decide
theorem identity_checked : (run 20 identityGoal).isEstablished = true := by decide
theorem nonbinding_checked : (run 12 constantGoal).isEstablished = true := by decide
theorem identity_type_checked : (run 20 identityFormation).isEstablished = true := by decide
theorem exhausted_stays_incomplete : (run 1 identityGoal).isIncomplete = true := by decide
theorem wrong_universe_not_accepted : (run 20 wrongUniverse).isEstablished = false := by decide
theorem malformed_context_not_accepted :
    (run 20 variableInMalformedContext).isEstablished = false := by decide
#print axioms run
#print axioms identity_checked
#print axioms malformed_context_not_accepted

end Mettapedia.Languages.Agda.Native.Production.Controls
