import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.ExecutableWrittenSchemaMatching
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.ExecutableWrittenSchemaErasure

/-!
# Source-ordered equation selection with firing receipts

The semantic relation consists independently of all substitution instances of
the authored table. Execution reconstructs a match, checks that every variable
of the right side was assigned, and selects the first matching source entry.
Receipts keep the entry position and the shared assignment. Unassigned right
sides stop execution rather than becoming another equation or a default value.

Source equality retains written domains even at repeated slots. Priority is
an execution choice. No confluence or completeness claim about an
arbitrary table is inferred from successful matching.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality.Normalization.ExecutableWrittenSchemaSelection

open ExecutableWrittenSchemaMatching

variable {Head : Type} [DecidableEq Head]

abbrev Entry (Head : Type) := Σ slots : Nat, ATm Head slots × ATm Head slots

abbrev WrittenTable (Head : Type) := List (Entry Head)

/-- Independent authored semantics: all source equation instances, with no
priority or computed match required by the relation. -/
inductive InstanceStep (table : WrittenTable Head) {ambient : Nat} :
    ATm Head ambient → ATm Head ambient → Prop where
  | instantiate (entry : Entry Head) (listed : entry ∈ table)
      (substitution : ATm.ASub Head entry.1 ambient) :
      InstanceStep table (ATm.subst substitution entry.2.1)
        (ATm.subst substitution entry.2.2)

def eraseTable (table : WrittenTable Head) : AlgebraicSchema.SchemaTable Head :=
  table.map (fun entry => ⟨entry.1, entry.2.1.erase, entry.2.2.erase⟩)

omit [DecidableEq Head] in
/-- Every full-source step preserves the independently authored erased
semantics; this does not identify source equality with erased equality. -/
theorem InstanceStep.erase {table : WrittenTable Head} {ambient : Nat}
    {source target : ATm Head ambient} (step : InstanceStep table source target) :
    (AlgebraicSchema.SchemaFamily.computation (eraseTable table).family).step
      source.erase target.erase := by
  cases step with
  | instantiate entry listed substitution =>
      rw [ATm.erase_subst, ATm.erase_subst]
      apply AlgebraicSchema.SchemaTable.step_of_mem
      exact List.mem_map.mpr ⟨entry, listed, rfl⟩

/-- An actual match, retaining its authored occurrence and shared slot store. -/
structure MatchedEntry (table : WrittenTable Head) {ambient : Nat} (source : ATm Head ambient) where
  position : Nat
  entry : Entry Head
  atPosition : table[position]? = some entry
  assignment : Assignment Head entry.1 ambient
  matched : run entry.2.1 source (fun _ => none) = some assignment

def MatchedEntry.target {table : WrittenTable Head} {ambient : Nat} {source : ATm Head ambient}
    (receipt : MatchedEntry table source) : ATm Head ambient :=
  ATm.subst (materialize receipt.assignment) receipt.entry.2.2

/-- Successful firing, blocked right-side formation, and no matching entry
are separate outcomes. -/
inductive Outcome (table : WrittenTable Head) {ambient : Nat} (source : ATm Head ambient) where
  | fired (receipt : MatchedEntry table source)
      (rightAssigned : RightAssigned receipt.entry.2.2 receipt.assignment)
  | unassigned (receipt : MatchedEntry table source)
      (rightUnassigned : ¬ RightAssigned receipt.entry.2.2 receipt.assignment)
  | missed

def MatchedEntry.prepend {table : WrittenTable Head} {ambient : Nat} {source : ATm Head ambient}
    (first : Entry Head) (receipt : MatchedEntry table source) : MatchedEntry (first :: table) source where
  position := receipt.position + 1
  entry := receipt.entry
  atPosition := by simpa only [List.getElem?_cons_succ] using receipt.atPosition
  assignment := receipt.assignment
  matched := receipt.matched

def Outcome.prepend {table : WrittenTable Head} {ambient : Nat} {source : ATm Head ambient}
    (first : Entry Head) : Outcome table source → Outcome (first :: table) source
  | .fired receipt assigned => .fired (receipt.prepend first) assigned
  | .unassigned receipt unbound => .unassigned (receipt.prepend first) unbound
  | .missed => .missed

def Outcome.target? {table : WrittenTable Head} {ambient : Nat} {source : ATm Head ambient} :
    Outcome table source → Option (ATm Head ambient)
  | .fired receipt _ => some receipt.target
  | .unassigned _ _ | .missed => none

def Outcome.position? {table : WrittenTable Head} {ambient : Nat} {source : ATm Head ambient} :
    Outcome table source → Option Nat
  | .fired receipt _ | .unassigned receipt _ => some receipt.position
  | .missed => none

/-- Only subjects and authored equations are inputs; all match evidence is
constructed during execution. -/
def first : (table : WrittenTable Head) → {ambient : Nat} → (source : ATm Head ambient) →
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
theorem MatchedEntry.source_instance {table : WrittenTable Head} {ambient : Nat}
    {source : ATm Head ambient} (receipt : MatchedEntry table source) :
    ATm.subst (materialize receipt.assignment) receipt.entry.2.1 = source :=
  (run_sound _ receipt.matched).2 _ (materialize_realizes _)

/-- Every firing is an instance of an actual authored equation, with its
occurrence justified by table lookup. -/
theorem MatchedEntry.semantic_step {table : WrittenTable Head} {ambient : Nat}
    {source : ATm Head ambient} (receipt : MatchedEntry table source) :
    InstanceStep table source receipt.target := by
  have member : receipt.entry ∈ table := List.mem_of_getElem? receipt.atPosition
  have step := InstanceStep.instantiate receipt.entry member (materialize receipt.assignment)
  rw [receipt.source_instance] at step
  exact step

/-- A firing's written target, erased target and authored source position are
all derived from the same retained assignment. -/
theorem MatchedEntry.erased_step {table : WrittenTable Head} {ambient : Nat}
    {source : ATm Head ambient} (receipt : MatchedEntry table source) :
    (AlgebraicSchema.SchemaFamily.computation (eraseTable table).family).step
      source.erase receipt.target.erase :=
  receipt.semantic_step.erase

end TypedEquality.Normalization.ExecutableWrittenSchemaSelection
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
