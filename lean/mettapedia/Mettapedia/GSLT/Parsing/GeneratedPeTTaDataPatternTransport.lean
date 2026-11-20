import Mettapedia.GSLT.Parsing.GeneratedPeTTaDataPatternExecution

/-!
# Variable transport and instantiation of native constructor code

The emitter preserves the complete variable-occurrence list, and commutes
with the source machine's clause renaming. Instantiation requires an
operational law: a variable can hold an expression value, so substituting
into code is not the same syntax as compiling an instantiated template.

Both compilation orders reach the same full return configuration in the
existing machine. Their finite administrative prefixes can differ; all
subsequent caller observations coincide after those prefixes. This does not
identify equal initial fuel cutoffs or supply a theory-growth realization.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.GeneratedPeTTaDataPattern

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.ProcessCalculi.MORK (Subst atomFreeVars)

mutual
  theorem atomCode_freeVars (template : Atom) :
      atomFreeVars (atomCode template) = atomFreeVars template := by
    cases template with
    | var name => rfl
    | symbol name => rfl
    | grounded held => rfl
    | expression items => exact listCode_freeVars items
  termination_by sizeOf template

  theorem listCode_freeVars (templates : List Atom) :
      atomFreeVars (listCode templates) = atomFreeVars (.expression templates) := by
    cases templates with
    | nil => rfl
    | cons first rest =>
        simp only [listCode, atomFreeVars, atomFreeVars.atomFreeVarsList,
          List.nil_append, List.append_nil, atomCode_freeVars first, listCode_freeVars rest]
  termination_by sizeOf templates
end

mutual
  theorem atomCode_rename (use : Nat) (template : Atom) :
      atomCode (Unifying.rename use template) = Unifying.rename use (atomCode template) := by
    cases template with
    | var name => rfl
    | symbol name => rfl
    | grounded held => rfl
    | expression items => exact listCode_rename use items
  termination_by sizeOf template

  theorem listCode_rename (use : Nat) (templates : List Atom) :
      listCode (Unifying.rename.renameList use templates) =
        Unifying.rename use (listCode templates) := by
    cases templates with
    | nil => rfl
    | cons first rest =>
        simp only [Unifying.rename.renameList, listCode, Unifying.rename,
          atomCode_rename use first, listCode_rename use rest]
  termination_by sizeOf templates
end

/-- Instantiating before compilation, or letting compiled constructor code
read those bindings, reaches the same actual return boundary. Every caller
therefore has the same remaining run, including its effects and suspension. -/
theorem instantiation_continuations (registry : SpaceSemantics.Program)
    (base : Unifying.Configuration) (bindings : Subst)
    (valid : Unifying.Idempotent bindings) (template : Atom) (frames : List Unifying.Frame) :
    ∃ firstWork secondWork, ∀ remaining,
      Unifying.run registry (firstWork + remaining)
          {base with control := .evaluate bindings (atomCode template), frames} =
      Unifying.run registry (secondWork + remaining)
          {base with
            control := .evaluate bindings (atomCode (Unifying.resolve bindings template))
            frames} := by
  have first := atomCode_under_frames registry base bindings valid template frames
  have second := atomCode_under_frames registry base bindings valid
    (Unifying.resolve bindings template) frames
  rw [Unifying.resolve_idem valid template] at second
  obtain ⟨firstWork, firstRun⟩ := Unifying.steps_run_suffix first
  obtain ⟨secondWork, secondRun⟩ := Unifying.steps_run_suffix second
  exact ⟨firstWork, secondWork, fun remaining =>
    (firstRun remaining).trans (secondRun remaining).symm⟩

example : atomFreeVars (atomCode (.expression [.symbol "cons", .var "x", .var "x"])) =
    ["x", "x"] := by
  rw [atomCode_freeVars]
  rfl

/-- A variable holding an expression is a value, not code for constructing
that value. A proposed strict substitution law would identify these. -/
example :
    atomCode (Unifying.resolve [("x", .expression [.symbol "cons", .symbol "a"])] (.var "x")) ≠
      Unifying.resolve [("x", .expression [.symbol "cons", .symbol "a"])]
        (atomCode (.var "x")) := by
  decide +kernel

#print axioms atomCode_freeVars
#print axioms atomCode_rename
#print axioms instantiation_continuations

end Mettapedia.GSLT.Parsing.GeneratedPeTTaDataPattern
