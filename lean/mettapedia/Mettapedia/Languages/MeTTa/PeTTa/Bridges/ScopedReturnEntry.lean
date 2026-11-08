import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedReturnSyntax
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedClosedEquationSource

/-!
# Protected return recipes at actual fresh clause entry

An accepted source head equation connects each actual argument to the same
fresh recipe used by the selected body. Only the protected argument needs a
fixed read; other arguments may be open or interpreted. The return syntax
certificate is transported by the actual common clause renamer, not rebuilt
under an unrelated formal-only environment.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedReturnEntry

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open EagerDFS.Destination
open HE.Spec.Type.RuntimeRefinement (renameTypeVars)

theorem fresh_recipe_read (control : Control) (head : String) (arguments : List Atom)
    (destination : Atom) (older : List Goal) (occurrence : Nat) (equation : SpaceSemantics.Equation)
    (next : Control) (index : Nat) (argument recipe : Atom)
    (selected : ClauseChoice.attempt control head arguments destination older occurrence equation = some next)
    (actual : arguments[index]? = some argument) (formal : equation.arguments[index]? = some recipe)
    (environment : Environment) (solved : Solves environment next.bindings) :
    read environment (renameTypeVars (ClauseChoice.rename control occurrence (ClauseChoice.clauseAtoms equation)) recipe) =
      read environment argument := by
  have fields := ClauseChoice.attempt_preserves_caller control head arguments destination older occurrence equation next selected
  rw [fields.2.2.2] at solved
  have linked := ((solves_append_equation _ _ _ _).mp solved).2
  simp only [ClauseChoice.freshPattern, ClauseChoice.pattern, renameTypeVars, List.map_cons,
    ScopedClosedEquationSource.read_expression, List.map_cons, Atom.expression.injEq, List.cons.injEq] at linked
  have positions := congrArg (fun values : List Atom => values[index]?) linked.2
  simp only [List.getElem?_map, actual, formal, Option.map_some] at positions
  exact (Option.some.inj positions).symm

theorem fresh_recipe_fixed (control : Control) (head : String) (arguments : List Atom)
    (destination : Atom) (older : List Goal) (occurrence : Nat) (equation : SpaceSemantics.Equation)
    (next : Control) (index : Nat) (argument recipe value : Atom)
    (selected : ClauseChoice.attempt control head arguments destination older occurrence equation = some next)
    (actual : arguments[index]? = some argument) (formal : equation.arguments[index]? = some recipe)
    (fixed : ProtectedSlots.Fixed control.bindings argument value) :
    ProtectedSlots.Fixed next.bindings
      (renameTypeVars (ClauseChoice.rename control occurrence (ClauseChoice.clauseAtoms equation)) recipe) value := by
  intro environment solved
  rw [fresh_recipe_read control head arguments destination older occurrence equation next index argument recipe
    selected actual formal environment solved]
  apply fixed environment
  rw [(ClauseChoice.attempt_preserves_caller control head arguments destination older occurrence equation next selected).2.2.2] at solved
  exact ((solves_append_equation _ _ _ _).mp solved).1

/-- The actual selected source occurrence earns a single shared fresh return
recipe, its protected observation, and the original caller suffix together.
No successful body evaluation or returned value is a premise. -/
theorem selected_return_contract (control : Control) (head : String) (arguments : List Atom)
    (destination : Atom) (older : List Goal) (occurrence : Nat) (equation : SpaceSemantics.Equation)
    (next : Control) (index : Nat) (argument recipe value : Atom) (inspectionFuel : Nat)
    (selected : ClauseChoice.attempt control head arguments destination older occurrence equation = some next)
    (actual : arguments[index]? = some argument) (formal : equation.arguments[index]? = some recipe)
    (fixed : ProtectedSlots.Fixed control.bindings argument value)
    (checked : ScopedReturnSyntax.checksSurfaceReturn recipe inspectionFuel equation.body = true) :
    let fresh := renameTypeVars (ClauseChoice.rename control occurrence (ClauseChoice.clauseAtoms equation)) recipe
    ProtectedSlots.Fixed next.bindings fresh value ∧
      ScopedReturnSyntax.Returns fresh (ClauseChoice.freshBody control occurrence equation) ∧
      next.goals = .evaluate (ClauseChoice.freshBody control occurrence equation) destination :: older ∧
      RefinementTransport.Extends control.bindings next.bindings := by
  dsimp only
  refine ⟨fresh_recipe_fixed control head arguments destination older occurrence equation next index argument recipe value
    selected actual formal fixed, ?_, ?_, ?_⟩
  · exact (ScopedReturnSyntax.checksSurfaceReturn_sound recipe inspectionFuel equation.body checked).rename _
  · exact (ClauseChoice.attempt_preserves_caller control head arguments destination older occurrence equation next selected).2.2.1
  · rw [(ClauseChoice.attempt_preserves_caller control head arguments destination older occurrence equation next selected).2.2.2]
    exact RefinementTransport.append_extends _ _

theorem selected_ground_return_contract (control : Control) (head : String) (arguments : List Atom)
    (destination : Atom) (older : List Goal) (occurrence : Nat) (equation : SpaceSemantics.Equation)
    (next : Control) (index : Nat) (argument recipe : Atom) (inspectionFuel : Nat) (environment : Environment)
    (selected : ClauseChoice.attempt control head arguments destination older occurrence equation = some next)
    (actual : arguments[index]? = some argument) (formal : equation.arguments[index]? = some recipe)
    (resolved : resolve control.bindings = some environment)
    (ground : (encode (read environment argument)).isGround)
    (checked : ScopedReturnSyntax.checksSurfaceReturn recipe inspectionFuel equation.body = true) :
    let fresh := renameTypeVars (ClauseChoice.rename control occurrence (ClauseChoice.clauseAtoms equation)) recipe
    ProtectedSlots.Fixed next.bindings fresh (read environment argument) ∧
      ScopedReturnSyntax.Returns fresh (ClauseChoice.freshBody control occurrence equation) ∧
      next.goals = .evaluate (ClauseChoice.freshBody control occurrence equation) destination :: older ∧
      RefinementTransport.Extends control.bindings next.bindings :=
  selected_return_contract control head arguments destination older occurrence equation next index argument recipe
    (read environment argument) inspectionFuel selected actual formal
    (ProtectedSlots.fixed_of_resolved resolved argument ground) checked

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedReturnEntry
