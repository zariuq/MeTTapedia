import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.ExecutableSchemaMatching
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.ExecutableReduction

/-!
# Source-ordered equation selection with firing receipts

The semantic relation consists independently of all substitution instances of
the authored table. Execution reconstructs a match, checks that every variable
of the right side was assigned, and selects the first matching source entry.
Receipts keep the entry position and the shared assignment. Unassigned right
sides stop execution rather than becoming another equation or a default value.

Priority is an execution choice. No confluence or completeness claim about an
arbitrary table is inferred from successful matching.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality.Normalization.ExecutableSchemaSelection

open AlgebraicSchema
open ExecutableSchemaMatching

variable {Head : Type} [DecidableEq Head]

abbrev Entry (Head : Type) := Σ slots : Nat, Tm Head slots × Tm Head slots

/-- An actual match, retaining its authored occurrence and shared slot store. -/
structure MatchedEntry (table : SchemaTable Head) {ambient : Nat} (source : Tm Head ambient) where
  position : Nat
  entry : Entry Head
  atPosition : table[position]? = some entry
  assignment : Assignment Head entry.1 ambient
  matched : run entry.2.1 source (fun _ => none) = some assignment

def MatchedEntry.target {table : SchemaTable Head} {ambient : Nat} {source : Tm Head ambient}
    (receipt : MatchedEntry table source) : Tm Head ambient :=
  Presentation.subst (materialize receipt.assignment) receipt.entry.2.2

/-- Successful firing, blocked right-side formation, and no matching entry
are separate outcomes. -/
inductive Outcome (table : SchemaTable Head) {ambient : Nat} (source : Tm Head ambient) where
  | fired (receipt : MatchedEntry table source)
      (rightAssigned : RightAssigned receipt.entry.2.2 receipt.assignment)
  | unassigned (receipt : MatchedEntry table source)
      (rightUnassigned : ¬ RightAssigned receipt.entry.2.2 receipt.assignment)
  | missed

def MatchedEntry.prepend {table : SchemaTable Head} {ambient : Nat} {source : Tm Head ambient}
    (first : Entry Head) (receipt : MatchedEntry table source) : MatchedEntry (first :: table) source where
  position := receipt.position + 1
  entry := receipt.entry
  atPosition := by simpa only [List.getElem?_cons_succ] using receipt.atPosition
  assignment := receipt.assignment
  matched := receipt.matched

def Outcome.prepend {table : SchemaTable Head} {ambient : Nat} {source : Tm Head ambient}
    (first : Entry Head) : Outcome table source → Outcome (first :: table) source
  | .fired receipt assigned => .fired (receipt.prepend first) assigned
  | .unassigned receipt unbound => .unassigned (receipt.prepend first) unbound
  | .missed => .missed

def Outcome.target? {table : SchemaTable Head} {ambient : Nat} {source : Tm Head ambient} :
    Outcome table source → Option (Tm Head ambient)
  | .fired receipt _ => some receipt.target
  | .unassigned _ _ | .missed => none

def Outcome.position? {table : SchemaTable Head} {ambient : Nat} {source : Tm Head ambient} :
    Outcome table source → Option Nat
  | .fired receipt _ | .unassigned receipt _ => some receipt.position
  | .missed => none

/-- Only subjects and authored equations are inputs; all match evidence is
constructed during execution. -/
def first : (table : SchemaTable Head) → {ambient : Nat} → (source : Tm Head ambient) →
    Outcome table source
  | [], _, _ => .missed
  | entry :: table, _, source =>
      match computed : run entry.2.1 source (fun _ => none) with
      | none => (first table source).prepend entry
      | some assignment =>
          let receipt : MatchedEntry (entry :: table) source :=
            ⟨0, entry, rfl, assignment, computed⟩
          if assigned : RightAssigned entry.2.2 assignment then .fired receipt assigned
          else .unassigned receipt assigned

/-- The retained match independently reconstructs its left-side instance. -/
theorem MatchedEntry.source_instance {table : SchemaTable Head} {ambient : Nat}
    {source : Tm Head ambient} (receipt : MatchedEntry table source) :
    Presentation.subst (materialize receipt.assignment) receipt.entry.2.1 = source :=
  (run_sound _ receipt.matched).2 _ (materialize_realizes _)

/-- Every firing is an instance of an actual authored equation, with its
occurrence justified by table lookup. -/
theorem MatchedEntry.semantic_step {table : SchemaTable Head} {ambient : Nat}
    {source : Tm Head ambient} (receipt : MatchedEntry table source) :
    (SchemaFamily.computation table.family).step source receipt.target := by
  have member : receipt.entry ∈ table := List.mem_of_getElem? receipt.atPosition
  have step := SchemaTable.step_of_mem table member (materialize receipt.assignment)
  rw [receipt.source_instance] at step
  exact step

/-- Rules with the independently defined schema-instance semantics. -/
def withSchemas (base : Rules Head) (table : SchemaTable Head) : Rules Head :=
  { base with computation := SchemaFamily.computation table.family }

/-- The root evaluator is derived from actual source matching and receipt
construction, rather than supplied as a certificate-producing interface. -/
def root (base : Rules Head) (table : SchemaTable Head) :
    ExecutableReduction.RootEvaluator (withSchemas base table) := fun {_} source =>
  match first table source with
  | .fired receipt _ => some ⟨receipt.target, receipt.semantic_step⟩
  | .unassigned _ _ | .missed => none

/-- Full contextual execution uses that derived root evaluator. -/
def normalize (base : Rules Head) (table : SchemaTable Head) :
    ExecutableReduction.Reducer (withSchemas base table) :=
  ExecutableReduction.normalize (withSchemas base table) (root base table)

theorem normalize_sound (base : Rules Head) (table : SchemaTable Head)
    {ambient budget : Nat} {source target : Tm Head ambient}
    (computed : (normalize base table budget source).map Subtype.val = some target) :
    Reduces (withSchemas base table) source target :=
  ExecutableReduction.normalizeTerm_sound (withSchemas base table) (root base table) computed

end TypedEquality.Normalization.ExecutableSchemaSelection
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
