import Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement
import Mettapedia.Tools.KernelReflexivity

/-!
# Type-variable renaming by structural recursion

`renameTypeVars` recurses through `List.map`, so Lean compiles it by
well-founded recursion and the kernel cannot evaluate it on closed atoms.
`renameTypeVarsStructural` walks the nested list with its own structural
companion; the two functions are equal.
-/

namespace Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

mutual

/-- Rename every type-variable leaf; structural on the atom. -/
def renameTypeVarsStructural (ρ : String → String) : Atom → Atom
  | .symbol name => .symbol name
  | .var name => .var (ρ name)
  | .grounded value => .grounded value
  | .expression atoms => .expression (renameTypeVarsStructuralList ρ atoms)

/-- `renameTypeVarsStructural` on each element of a list. -/
def renameTypeVarsStructuralList (ρ : String → String) : List Atom → List Atom
  | [] => []
  | atom :: atoms => renameTypeVarsStructural ρ atom :: renameTypeVarsStructuralList ρ atoms

end

/-- The structural renaming is `renameTypeVars` itself. -/
theorem renameTypeVarsStructural_eq : @renameTypeVarsStructural = @renameTypeVars := by
  funext ρ atom
  induction atom using Atom.rec (motive_2 := fun atoms =>
      renameTypeVarsStructuralList ρ atoms = atoms.map (renameTypeVars ρ)) with
  | symbol name => simp [renameTypeVarsStructural, renameTypeVars]
  | var name => simp [renameTypeVarsStructural, renameTypeVars]
  | grounded value => simp [renameTypeVarsStructural, renameTypeVars]
  | expression atoms ih => simp [renameTypeVarsStructural, renameTypeVars, ih]
  | nil => simp [renameTypeVarsStructuralList]
  | cons atom atoms ihAtom ihAtoms => simp [renameTypeVarsStructuralList, ihAtom, ihAtoms]

example : renameTypeVarsStructural (· ++ "'")
    (.expression [.symbol "->", .var "a", .expression [.symbol "List", .var "b"]]) =
      .expression [.symbol "->", .var "a'", .expression [.symbol "List", .var "b'"]] := by
  kernel_reflexivity

/-- The well-founded definition does not reduce in the kernel. -/
example : True := by
  fail_if_success
    have : renameTypeVars (· ++ "'") (.expression [.var "a"]) = .expression [.var "a'"] := by
      kernel_reflexivity
  trivial

end Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement
