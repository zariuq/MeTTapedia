import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.FunctionVariables.ExampleTwiceAsWritten

/-!
# `twice` as written, under the clause by the declared type of the variable

The text of `ExampleTwice`, under `Clause.declared holds`: an argument of a call through a variable is
held when the type declared for that variable holds the parameter, and evaluated otherwise. Here the
declared types are given by `holds`; the surface has no function types yet from which to read them.

* A declared type that holds nothing (`holdsNothing`): the program is the program by value
  (`nothing_program`), and a run ends, quiescent, with the bag `{(S (S Z))}` (`nothing_answers`).
* A declared type that holds the parameter (`holdsAll`): the program is the one that calls the tuple as
  it stands (`all_program`), and a run ends, quiescent, with the bag `{(S (inc Z))}` (`all_answers`): the
  inner call is passed as text to `inc`, which holds nothing. Under this clause the declaration of the
  variable decides, not the function the variable is bound to.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.FunctionVariables.ExampleDeclared

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Elaboration Toolkit
open ExampleTwice (D supply sp byValue surface query)

/-- The declared type of every variable holds nothing. -/
def holdsNothing : Name mkeys → ℕ → Bool := fun _ _ => false

/-- The declared type of every variable holds every parameter. -/
def holdsAll : Name mkeys → ℕ → Bool := fun _ _ => true

/-- **A declared type that holds nothing gives the program by value.** -/
theorem nothing_program : elaborateH (.declared holdsNothing) byValue surface = ExampleTwice.program := rfl

/-- **A declared type that holds the parameter gives the program that calls the tuple as it stands.** -/
theorem all_program :
    elaborateH (.declared holdsAll) byValue surface = ExampleTwiceAsWritten.program := rfl

/-- **Declared, holding nothing**: a run ends, quiescent, with the bag `{(S (S Z))}`. -/
theorem nothing_answers : ∃ C : Config mkeys [] () MTy,
    Runs D (elaborateH (.declared holdsNothing) byValue surface) supply (Config.initial sp query) C ∧
      Config.Quiescent (D := D) (elaborateH (.declared holdsNothing) byValue surface) supply C ∧
      Config.answers (D := D) C = {{ExampleTwice.answer}} := by
  rw [nothing_program]
  exact ExampleTwice.runs_answers

/-- **Declared, holding the parameter**: a run ends, quiescent, with the bag `{(S (inc Z))}`. -/
theorem all_answers : ∃ C : Config mkeys [] () MTy,
    Runs D (elaborateH (.declared holdsAll) byValue surface) supply (Config.initial sp query) C ∧
      Config.Quiescent (D := D) (elaborateH (.declared holdsAll) byValue surface) supply C ∧
      Config.answers (D := D) C = {{ExampleTwiceAsWritten.answer}} := by
  rw [all_program]
  exact ExampleTwiceAsWritten.runs_answers

#print axioms nothing_program
#print axioms all_program
#print axioms nothing_answers
#print axioms all_answers

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.FunctionVariables.ExampleDeclared
