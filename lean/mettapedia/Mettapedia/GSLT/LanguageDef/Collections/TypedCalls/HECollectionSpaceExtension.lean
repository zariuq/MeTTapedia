import Mettapedia.Languages.MeTTa.HE.CollectionStdlibSource
import Mettapedia.Languages.MeTTa.HE.EquationFrontierExtension
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERangeSourceProtocol
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeSourcePorts
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.ScopedSubtypeReads

/-!
# Extending the range source with the actual collection equations

Added equations have different fixed heads, and their declaration subjects
do not replace the existing range dependencies. Complete old frontiers are
preserved with their physical prefix positions and contextual records. This
is an explicit extension theorem, not an identification with all stdlib rows.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionSpaceExtension

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Steps
open CollectionStdlibSource

def space : Space := Space.ofList (HERangeSourceProgram.space.atoms ++ extensionRows)

theorem extension_row_rejected (live : List Atom) (before : Bindings) (name : String)
    (arguments : List Atom) (position : Nat) (row : Atom)
    (protectedHead : name ∈ ["range", "if", "empty"])
    (present : row ∈ extensionRows) :
    EquationRowResultsRel live (.expression (.symbol name :: arguments)) before position row [] := by
  simp only [extensionRows, authoredRows, nativeTypeRows, instructionTypeRows,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with ((rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) |
    (rfl | rfl | rfl)) | (rfl | rfl | rfl | rfl | rfl | rfl)
  all_goals first
    | exact HERangeEquationFrontiers.annotation_irrelevant _ _ _ _ _ _
    | apply HERangeEquationFrontiers.different_head_miss
      simp only [List.mem_cons, List.not_mem_nil, or_false] at protectedHead
      rcases protectedHead with rfl | rfl | rfl <;> decide

theorem old_frontier (live : List Atom) (before : Bindings) (name : String)
    (arguments : List Atom) (works : List EquationWork)
    (protectedHead : name ∈ ["range", "if", "empty"])
    (frontier : EquationFrontierRel HERangeSourceProgram.space live
      (.expression (.symbol name :: arguments)) before works) :
    EquationFrontierRel space live (.expression (.symbol name :: arguments)) before works := by
  exact EquationFrontierRel.append_rejected _ _ _ _ _ extensionRows frontier
    (fun row member position => extension_row_rejected live before name arguments position row protectedHead member)

theorem old_symbol_declarations (name : String)
    (protectedHead : name ∈ ["range", "empty", "if", "+", ">=", "superpose"]) :
    getAnnotatedTypes space (.symbol name) = getAnnotatedTypes HERangeSourceProgram.space (.symbol name) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at protectedHead
  rcases protectedHead with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem no_expression_declarations (children : List Atom) :
    getAnnotatedTypes space (.expression children) = [] := rfl

theorem no_subtype_rows : ∀ row ∈ space.atoms, ScopedSubtypeReads.possibleRow row = false := by
  have checked : space.atoms.all (fun row => !ScopedSubtypeReads.possibleRow row) = true := by decide
  intro row present
  simpa using (List.all_eq_true.mp checked) row present

theorem plain_source_rows : TypeDependencyAdmission.resourceFreeList space.atoms = true := by decide

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionSpaceExtension
