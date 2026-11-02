import Mettapedia.Logic.TierZero.Adequacy.MM0ScopedArgumentAdmission
import Mettapedia.Logic.TierZero.Adequacy.MM0RewritingTheoremApplication
import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.ContextualPatternInterfaces

/-!
# MM0 templates with per-formal contextual occurrence spines

Existing source templates retain their constructor trees and binder fields.
Each schematic occurrence receives its declaration-derived restricted spine;
its assignment is the body built by the common recovery operation. Plugging
those bodies reconstructs exactly the independent simultaneous substitution.

The original ambient-spine presentation is retained only as a comparison.
Forward graft itself continues to allow general argument expressions.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.MM0ScopedPatterns

open Mettapedia.Languages.MM0.Kernel
open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
open Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources
open MM0ContextualSupport
open MM0Rewriting
open MM0ScopedArgumentInterfaces

def entryAt (formal : Context) (expressions : List Preterm) (index : Nat) : Option Substitution.Entry := do
  let binder ← formal[index]?
  let expression ← expressions[index]?
  return ((binder, expression), index)

theorem entryAt_member {formal : Context} {expressions : List Preterm} {index : Nat}
    {entry : Substitution.Entry} (found : entryAt formal expressions index = some entry) :
    entry ∈ Substitution.entries formal expressions := by
  cases formalLookup : formal[index]? with
  | none => simp [entryAt, formalLookup] at found
  | some binder =>
      cases expressionLookup : expressions[index]? with
      | none => simp [entryAt, formalLookup, expressionLookup] at found
      | some expression =>
          have same : ((binder, expression), index) = entry := by
            simpa [entryAt, formalLookup, expressionLookup] using found
          subst entry
          simp [Substitution.entries, List.mem_zipIdx_iff_getElem?,
            List.getElem?_zip_eq_some, formalLookup, expressionLookup]

def slot (formal target : Context) (expressions : List Preterm) (index : Nat) :
    ContextualPatterns.Occurrence Head Nat :=
  match entryAt formal expressions index with
  | none => ambientSlot target.length index
  | some entry => occurrence target.length (Substitution.entries formal expressions) entry

def assignment (formal target : Context) (expressions : List Preterm) : Subst Nat (Term Head) :=
  fun index => (entryAt formal expressions index).bind (recoverEntry target (Substitution.entries formal expressions))

def suppliedAssignment (bodies : List (Term Head)) : Subst Nat (Term Head) := fun index => bodies[index]?

private theorem collected_index {A B : Type} {function : A → Option B} {inputs : List A} {outputs : List B}
    (related : List.Forall₂ (fun input output => function input = some output) inputs outputs) :
    ∀ index : Nat, outputs[index]? = (inputs[index]?).bind function := by
  induction related with
  | nil => intro index; cases index <;> rfl
  | cons recovered rest earlier =>
      intro index
      cases index with
      | zero => exact recovered.symm
      | succ index => exact earlier index

theorem entryAt_index (formal : Context) (expressions : List Preterm) (index : Nat) :
    (Substitution.entries formal expressions)[index]? = entryAt formal expressions index := by
  simp only [Substitution.entries, List.getElem?_zipIdx, List.zip, List.getElem?_zipWith, Nat.zero_add]
  cases formalLookup : formal[index]? <;> cases expressionLookup : expressions[index]? <;>
    simp [entryAt, formalLookup, expressionLookup]

/-- Activation uses the body list actually returned by scope construction.
Its finite assignment agrees with the per-occurrence recovery specification. -/
theorem suppliedAssignment_eq {signature : TermSignature} {formal target : Context}
    {expressions : List Preterm} {bodies : List (Term Head)}
    (constructed : MM0ScopedArgumentAdmission.construct signature formal target expressions = some bodies) :
    suppliedAssignment bodies = assignment formal target expressions := by
  have recovered : MM0ScopedArgumentAdmission.recoverBodies formal target expressions = some bodies := by
    unfold MM0ScopedArgumentAdmission.construct at constructed
    split at constructed
    · exact constructed
    · cases constructed
  have columns := collected_index ((MM0ScopedArgumentAdmission.recoverBodies_iff formal target expressions bodies).mp recovered)
  funext index
  change bodies[index]? = _
  rw [columns index, entryAt_index]
  rfl

theorem slot_input (formal target : Context) (expressions : List Preterm) (index : Nat) :
    (slot formal target expressions index).Input := by
  cases found : entryAt formal expressions index with
  | none => simpa only [slot, found] using ambientSlot_input target.length index
  | some entry =>
      simpa only [slot, found] using occurrence_is_an_input target.length (Substitution.entries formal expressions) entry

theorem slot_reconstructs {sorts : SortSignature} {signature : TermSignature}
    {formal target : Context} {expressions : List Preterm}
    (formed : Context.WellFormed sorts target) (admitted : Substitution.Admissible signature formal target expressions)
    (index : Nat) :
    ContextualPatterns.Pattern.atOccurrence (assignment formal target expressions) (slot formal target expressions index) =
      (expressions[index]?).map (encode target) := by
  cases expressionLookup : expressions[index]? with
  | none =>
      cases formalLookup : formal[index]? <;>
        simp [slot, assignment, entryAt, expressionLookup, formalLookup, ContextualPatterns.Pattern.atOccurrence, ambientSlot]
  | some expression =>
      have inside := (List.getElem?_eq_some_iff.mp expressionLookup).1
      have formalInside : index < formal.length := by rw [← admitted.length_eq]; exact inside
      let binder := formal[index]
      have formalLookup : formal[index]? = some binder := List.getElem?_eq_getElem formalInside
      let entry : Substitution.Entry := ((binder, expression), index)
      have found : entryAt formal expressions index = some entry := by
        simp [entryAt, formalLookup, expressionLookup, entry]
      have member := entryAt_member found
      obtain ⟨support, supported⟩ := Substitution.typed_entry_support admitted.typed entry member
      have recoverable : (recoverEntry target (Substitution.entries formal expressions) entry).isSome = true :=
        (recoverEntry_iff supported (encode_supported formed supported)).mpr
          (fun source present sort image bound => admitted.independent source present sort image bound entry member)
      obtain ⟨body, recovered⟩ := Option.isSome_iff_exists.mp recoverable
      have applied := recoverEntry_grafts recovered
      have ownName : (occurrence target.length (Substitution.entries formal expressions) entry).name = index := rfl
      simpa only [slot, found, assignment, ContextualPatterns.Pattern.atOccurrence, ownName,
        Option.bind_some, recovered, expressionLookup, Option.map_some, entry] using applied

/-- The source template's occurrences retain the original ambient identity
spines; this is proved from its real constructor tree. -/
def Ambient (width : Nat) (pattern : Pat) : Prop :=
  ∀ source ∈ pattern.tree.vars, source = ambientSlot width source.name

theorem expressionTree_ambient (width : Nat) (expression : Preterm) :
    ∀ source ∈ (expressionTree width expression).vars, source = ambientSlot width source.name := by
  induction expression with
  | var index =>
      intro source member
      have same : source = ambientSlot width index := by simpa [expressionTree, TreePat.vars] using member
      subst source
      rfl
  | term symbol => simp [expressionTree, TreePat.vars, TreePatFields.vars]
  | app function argument head tail =>
      intro source member
      have present : source ∈ (expressionTree width function).vars ∨ source ∈ (expressionTree width argument).vars := by
        simpa [expressionTree, TreePat.vars, TreePatFields.vars] using member
      exact present.elim (head source) (tail source)

theorem expressionFields_ambient (width : Nat) (expressions : List Preterm) :
    ∀ source ∈ (expressionFields width expressions).vars, source = ambientSlot width source.name := by
  induction expressions with
  | nil => simp [expressionFields, TreePatFields.vars]
  | cons expression expressions earlier =>
      intro source member
      rcases (show source ∈ (expressionTree width expression).vars ∨ source ∈ (expressionFields width expressions).vars from by
        simpa [expressionFields, TreePatFields.vars] using member) with head | tail
      · exact expressionTree_ambient width expression source head
      · exact earlier source tail

theorem judgmentPattern_ambient (width : Nat) (tag : String) (expressions : List Preterm) :
    Ambient width (judgmentPattern width tag expressions) :=
  expressionFields_ambient width expressions

def reinterface (formal target : Context) (expressions : List Preterm) (pattern : Pat) : Pat :=
  ContextualPatternInterfaces.reinterface (fun source => slot formal target expressions source.name) pattern

theorem reinterface_input (formal target : Context) (expressions : List Preterm) (pattern : Pat) :
    (reinterface formal target expressions pattern).Input := by
  intro actual member
  have present := (ContextualPatterns.mem_occurrences _ actual).mp member
  change actual ∈ (ContextualPatternInterfaces.mapTree
    (fun source => slot formal target expressions source.name) pattern.tree).vars at present
  rw [ContextualPatternInterfaces.mapTree_vars] at present
  obtain ⟨source, _, rfl⟩ := Finset.mem_image.mp present
  exact slot_input formal target expressions source.name

theorem reinterface_match_exact (formal target : Context) (expressions : List Preterm) (pattern : Pat)
    (before after : Subst Nat (Term Head)) (value : Term Head) :
    ContextualPatterns.match? (reinterface formal target expressions pattern) before value = some after ↔
      ContextualPatterns.layer.Step before (reinterface formal target expressions pattern) value after :=
  ContextualPatterns.match_exact (reinterface_input formal target expressions pattern) before after value

theorem reinterface_inst {sorts : SortSignature} {signature : TermSignature}
    {formal target : Context} {expressions : List Preterm}
    (formed : Context.WellFormed sorts target) (admitted : Substitution.Admissible signature formal target expressions)
    (pattern : Pat) (original : Ambient target.length pattern) :
    (reinterface formal target expressions pattern).inst (assignment formal target expressions) =
      pattern.inst (expressionAssignment target expressions) := by
  apply ContextualPatternInterfaces.reinterface_inst
  intro source member
  rw [original source member]
  exact (slot_reconstructs formed admitted source.name).trans
    (slot_instantiation target expressions target.length source.name (admitted_arguments_supported formed admitted)).symm

end Mettapedia.Logic.TierZero.Adequacy.MM0ScopedPatterns
