import Mettapedia.Languages.Agda.Adequacy.Computation
import Mettapedia.Languages.Agda.Specification.Examples
import Mettapedia.OSLF.Syntax.ContextualMetavariableAssignment

/-!
# Binding and source-computation controls

These examples exercise the proved source-to-structural maps, rather than
identifying the two computations by definition. The final controls apply a
metavariable to three dependency arguments while preserving an ambient
variable beneath a further binder.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Adequacy.Controls

open Mettapedia.OSLF.Binding
open Structural (sig scope)

def identityPath (argument : Specification.Term 0) :
    Path (Structural.eliminate (embedTerm Specification.Examples.identity)
      (embedSpine (Specification.Spine.singleton argument))) (embedTerm argument) :=
  realizeApply (Specification.Examples.identity_apply argument)

def capturePath :
    Path
      (Structural.eliminate (Structural.lam (Structural.lam (.var (.succ .zero))))
        (Structural.cons (Structural.apply (.var .zero)) Structural.nil))
      (Structural.lam (.var (.succ .zero)) : Structural.Tm [.term]) :=
  realizeApply Specification.Examples.capture_preserved

theorem captureTarget_distinct :
    (Structural.lam (.var (.succ .zero)) : Structural.Tm [.term]) ≠
      Structural.lam (.var .zero) := by
  intro impossible
  cases impossible

def constantFunction : Specification.Term 0 :=
  .lam (.bind (.lam (.bind (Specification.Term.bvar (1 : Fin 2)))))

def orderedTwoArguments (first second : Specification.Term 0) :
    Path
      (Structural.eliminate
        (embedTerm constantFunction)
        (embedSpine (.cons (.apply first) (Specification.Spine.singleton second))))
      (embedTerm first) :=
  realizeApply (Specification.Examples.constant_two_arguments first second)

def substitutionComputes (argument : Specification.Term 0) :
    Path
      (bind (embedSub (Specification.Substitution.single Specification.Examples.identity))
        (embedTerm (.var (0 : Fin 1) (Specification.Spine.singleton argument.weaken))))
      (embedTerm argument) :=
  realizeSubstitute (Specification.Examples.substitute_applied_variable argument)

abbrev tripleMetas : List (MetaArity sig) := [([.term, .term, .term], .term)]

def capturedBody : Structural.Tm [.term, .term, .term, .term] :=
  Structural.lam (.var (.succ (.succ (.succ (.succ .zero)))))

def tripleValuation : ContextualAssignment sig tripleMetas [.term]
  | ⟨0, _⟩ => capturedBody

def tripleArguments : Sub sig [.term, .term, .term] [.term]
  | _, .zero => Structural.natLiteral 11
  | _, .succ .zero => Structural.natLiteral 22
  | _, .succ (.succ .zero) => Structural.natLiteral 33

/-- Dependency arguments and the captured ambient context are distinct. -/
theorem ternary_preserves_ambient :
    ContextualAssignment.apply tripleValuation 0 tripleArguments (fun _ v => .var v) =
      (Structural.lam (.var (.succ .zero)) : Structural.Tm [.term]) := rfl

theorem ternary_does_not_capture :
    ContextualAssignment.apply tripleValuation 0 tripleArguments (fun _ v => .var v) ≠
      (Structural.lam (.var .zero) : Structural.Tm [.term]) := by
  intro impossible
  cases impossible

def selectSecond : ContextualAssignment sig tripleMetas []
  | ⟨0, _⟩ => .var (.succ .zero)

def closedArguments : Sub sig [.term, .term, .term] []
  | _, .zero => Structural.natLiteral 11
  | _, .succ .zero => Structural.natLiteral 22
  | _, .succ (.succ .zero) => Structural.natLiteral 33

theorem ternary_retains_argument_order :
    ContextualAssignment.apply selectSecond 0 closedArguments (fun _ v => nomatch v) =
      Structural.natLiteral 22 := rfl

theorem ternary_wrong_order_rejected :
    ContextualAssignment.apply selectSecond 0 closedArguments (fun _ v => nomatch v) ≠
      Structural.natLiteral 11 := by
  intro impossible
  cases impossible


def dependencySpine {Γ : Ctx sig} (first second third : Structural.Tm Γ) : Structural.Spine Γ :=
  Structural.cons (Structural.apply first)
    (Structural.cons (Structural.apply second)
      (Structural.cons (Structural.apply third) Structural.nil))

/-- All three parameters occur beneath a binder, along with captured data. -/
def allDependencies : ContextualAssignment sig tripleMetas [.term]
  | ⟨0, _⟩ => Structural.lam
      (Structural.eliminate (.var (.succ (.succ (.succ (.succ .zero)))))
        (dependencySpine (.var (.succ .zero)) (.var (.succ (.succ .zero)))
          (.var (.succ (.succ (.succ .zero))))))

def allDependencyResult (first second third : Nat) : Structural.Tm [.term] :=
  Structural.lam (Structural.eliminate (.var (.succ .zero))
    (dependencySpine (Structural.natLiteral first) (Structural.natLiteral second)
      (Structural.natLiteral third)))

theorem ternary_all_dependencies :
    ContextualAssignment.apply allDependencies 0 tripleArguments (fun _ v => .var v) =
      allDependencyResult 11 22 33 := rfl

theorem ternary_first_last_swap_rejected :
    ContextualAssignment.apply allDependencies 0 tripleArguments (fun _ v => .var v) ≠
      allDependencyResult 33 22 11 := by
  intro impossible
  cases impossible

end Mettapedia.Languages.Agda.Adequacy.Controls
