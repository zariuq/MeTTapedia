import Mettapedia.Languages.MM0.OnTheStep.TermDeclarations
import Mettapedia.Languages.MM0.Kernel.TheoryAdmission

/-!
# Where MM0's GSLT definition and the Lean MM0 kernel part

The program of `DeclarationProgram` follows MM0's GSLT definition (`sort_environment_v1`, `term_environment_v1`).
The tree's semantic MM0 kernel (`Languages.MM0.Kernel`) admits declarations whose names are resolved to indices
and whose binders are listed one per variable. Two places where the two part, each shown on both sides:

* **A sort declared twice with the same modifiers** (CeTTa's `sort_repeated_identical.mm0`): accepted on the step
  (`SortDeclarations.Examples.repeatedIdentical_on_the_step`), as `mm0-rs` does; the kernel refuses a second
  admission of the same sort (`kernel_refuses_repeated_sort`), as `mm0-c` does. The positive twin: two distinct
  sorts are admitted (`kernel_admits_distinct_sorts`).
* **A binder group with no variable and a `strict` sort**, `term t {: atom}: result;` with `strict sort atom;`: the
  GSLT definition checks a group's type before its names, so the file is refused on the step
  (`emptyStrictGroup_refused`); resolved one binder per variable, the group gives no binder, and the kernel admits
  the declaration (`kernel_admits_without_the_group`). The negative twin: with one variable,
  `term t {x: atom}: result;`, both refuse (`strictGroup_refused`, `kernel_refuses_strict_bound`).

Which side is right is a semantic choice of MM0's definition; nothing here chooses.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.OnTheStep.DialectControls

open Mettapedia.Languages.MM0.Kernel (SortInfo SortSignature TermDecl Theory Admission Binder)
open SortDeclarations.Examples (ident sortStmt)
open TermDeclarations (Statement Typ Group)
open TermDeclarations.Examples (AcceptedOnTheStep accepted_on_the_step_iff plain)

/-! ## A sort declared twice -/

/-- The modifiers of `provable sort wff;`. -/
def provableInfo : SortInfo := { provable := true }

/-- **The kernel refuses a second admission of the same sort**, with the same modifiers. -/
theorem kernel_refuses_repeated_sort :
    (Theory.run? {} [.sort 0 provableInfo, .sort 0 provableInfo]).isNone = true := by decide

/-- The positive twin: two distinct sorts are admitted. -/
theorem kernel_admits_distinct_sorts :
    (Theory.run? {} [.sort 0 provableInfo, .sort 1 { strict := true }]).isSome = true := by decide

/-! ## A binder group with no variable -/

/-- `strict sort atom; sort result; term t {: atom}: result;`. -/
def emptyStrictGroup : List Statement :=
  [.sort (sortStmt false true false false "atom"), .sort (sortStmt false false false false "result"),
    .term ⟨ident "t", [.bound [] (plain "atom")], [], plain "result"⟩]

/-- `strict sort atom; sort result; term t {x: atom}: result;`. -/
def strictGroup : List Statement :=
  [.sort (sortStmt false true false false "atom"), .sort (sortStmt false false false false "result"),
    .term ⟨ident "t", [.bound [ident "x"] (plain "atom")], [], plain "result"⟩]

/-- **The GSLT definition refuses the empty group of a strict sort**: no run reaches `accepted`. -/
theorem emptyStrictGroup_refused : ¬ AcceptedOnTheStep emptyStrictGroup := by
  rw [accepted_on_the_step_iff]
  decide +kernel

/-- With one variable the GSLT definition refuses too. -/
theorem strictGroup_refused : ¬ AcceptedOnTheStep strictGroup := by
  rw [accepted_on_the_step_iff]
  decide +kernel

/-- The sorts of both files for the kernel: `atom` at index `0`, strict; `result` at index `1`. -/
def sorts : SortSignature := fun i => if i = 0 then some { strict := true } else if i = 1 then some {} else none

/-- **The kernel admits the declaration resolved one binder per variable**: the empty group gives no binder. -/
theorem kernel_admits_without_the_group : TermDecl.Admissible sorts ⟨[], 1, ∅⟩ :=
  (TermDecl.check_iff _ _).mp (by decide)

/-- The negative twin: a bound variable of the strict sort is refused by the kernel. -/
theorem kernel_refuses_strict_bound : ¬ TermDecl.Admissible sorts ⟨[.bound 0], 1, ∅⟩ := by
  rw [← TermDecl.check_iff]
  decide

#print axioms kernel_refuses_repeated_sort
#print axioms kernel_admits_distinct_sorts
#print axioms emptyStrictGroup_refused
#print axioms strictGroup_refused
#print axioms kernel_admits_without_the_group
#print axioms kernel_refuses_strict_bound

end Mettapedia.Languages.MM0.OnTheStep.DialectControls
