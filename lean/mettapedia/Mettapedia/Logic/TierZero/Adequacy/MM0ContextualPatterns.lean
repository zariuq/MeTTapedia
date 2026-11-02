import Mettapedia.Logic.TierZero.Adequacy.MM0ContextualSubstitution
import Mettapedia.Languages.MM0.Kernel.ContextExtension
import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.ContextualMatcher

/-!
# MM0 schematic expressions use the common contextual pattern layer

Object variables in the target context are encoded by the existing MM0
support-preserving encoding. Declaration formals are schematic variables of
the common pattern language. Their ambient identity spines retain the target
context; MM0's dependency restrictions remain the independently checked
admission conditions. Instantiation is proved to be MM0 simultaneous
substitution, rather than a separate evaluator for proof nodes.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.MM0ContextualSupport

open Mettapedia.Languages.MM0.Kernel
open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT.ScopedApplication
open Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources

theorem encode_supported {sorts : SortSignature} {context : Context} (formed : Context.WellFormed sorts context)
    {expression : Preterm} {support : Finset Nat} (supported : Preterm.Supports context expression support) :
    Term.supportedAt context.length (encode context expression) = true := by
  rw [Scope.supportedAt_iff]
  intro index used
  have member := (support_exact supported index).mp used
  obtain ⟨sort, lookup⟩ := supported.bound_lookup formed member
  exact (List.getElem?_eq_some_iff.mp lookup).1

theorem encode_typed_supported {sorts : SortSignature} {signature : TermSignature} {context remaining : Context}
    (formed : Context.WellFormed sorts context) {expression : Preterm} {sort : Nat}
    (typed : Preterm.HasType signature context expression remaining sort) :
    Term.supportedAt context.length (encode context expression) = true := by
  obtain ⟨support, supported⟩ := typed.support_exists
  exact encode_supported formed supported

def ambientSlot (width variableName : Nat) : ContextualPatterns.Occurrence Head Nat :=
  ⟨variableName, width, (List.range width).map Term.idx⟩

def expressionTree (width : Nat) : Preterm → TreePat Head (ContextualPatterns.Occurrence Head Nat)
  | .var index => .mvar (ambientSlot width index)
  | .term symbol => .node (.constant symbol) .nil
  | .app function argument =>
      .node .application (.cons 0 (expressionTree width function) (.cons 0 (expressionTree width argument) .nil))

def expressionPattern (width : Nat) (expression : Preterm) : ContextualPatterns.Pattern Head Nat :=
  ⟨width, expressionTree width expression⟩

def expressionAssignment (context : Context) (arguments : List Preterm) : Subst Nat (Term Head) :=
  fun index => (arguments[index]?).map (encode context)

theorem ambientSlot_input (width variableName : Nat) : (ambientSlot width variableName).Input :=
  ⟨List.range width, rfl, by simp [ambientSlot], List.nodup_range⟩

theorem expressionPattern_input (width : Nat) (expression : Preterm) : (expressionPattern width expression).Input := by
  induction expression with
  | var index =>
    intro occurrence member
    have same : occurrence = ambientSlot width index := by
      simpa [expressionPattern, expressionTree, ContextualPatterns.occurrences] using member
    subst occurrence
    exact ambientSlot_input width index
  | term symbol =>
    intro occurrence member
    simp [expressionPattern, expressionTree, ContextualPatterns.occurrences,
      ContextualPatterns.fieldOccurrences] at member
  | app function argument ihFunction ihArgument =>
    intro occurrence member
    have cases : occurrence ∈ ContextualPatterns.occurrences (expressionTree width function) ∨
        occurrence ∈ ContextualPatterns.occurrences (expressionTree width argument) := by
      simpa [expressionPattern, expressionTree, ContextualPatterns.occurrences,
        ContextualPatterns.fieldOccurrences] using member
    exact cases.elim (ihFunction occurrence) (ihArgument occurrence)

theorem identity_graft (width : Nat) (body : Term Head) (scopedBody : Term.supportedAt width body = true) :
    graft width ((List.range width).map Term.idx) body = some body := by
  simp only [graft, List.length_map, List.length_range, scopedBody, and_self, ↓reduceIte]
  congr 1
  calc
    Term.substituteMany (argumentAt ((List.range width).map Term.idx)) body =
        Term.substituteMany Term.idx body := by
      apply Term.substituteMany_congr_scoped _ body scopedBody
      intro index inside
      simp [argumentAt, inside]
    _ = body := Term.substituteMany_ids body

theorem slot_instantiation (context : Context) (arguments : List Preterm) (width index : Nat)
    (scopedArguments : ∀ argument ∈ arguments, Term.supportedAt width (encode context argument) = true) :
    ContextualPatterns.Pattern.atOccurrence (expressionAssignment context arguments) (ambientSlot width index) =
      (arguments[index]?).map (encode context) := by
  cases selected : arguments[index]? with
  | none => simp [ContextualPatterns.Pattern.atOccurrence, expressionAssignment, ambientSlot, selected]
  | some argument =>
    have within := scopedArguments argument (List.mem_of_getElem? selected)
    simpa only [ContextualPatterns.Pattern.atOccurrence, expressionAssignment, ambientSlot, selected,
      Option.map_some, Option.bind_some] using identity_graft width (encode context argument) within

theorem expressionTree_instantiation (context : Context) (arguments : List Preterm) (width : Nat)
    (scopedArguments : ∀ argument ∈ arguments, Term.supportedAt width (encode context argument) = true) :
    ∀ expression : Preterm,
      (expressionTree width expression).inst
          (ContextualPatterns.Pattern.atOccurrence (expressionAssignment context arguments)) =
        (Preterm.substitute (Substitution.ofList arguments) expression).map (encode context)
  | .var index => by
      simpa [expressionTree, TreePat.inst, Preterm.substitute, Substitution.ofList] using
        slot_instantiation context arguments width index scopedArguments
  | .term symbol => rfl
  | .app function argument => by
      simp only [expressionTree, TreePat.inst, TreePatFields.inst,
        expressionTree_instantiation context arguments width scopedArguments function,
        expressionTree_instantiation context arguments width scopedArguments argument,
        Preterm.substitute]
      cases Preterm.substitute (Substitution.ofList arguments) function <;>
        cases Preterm.substitute (Substitution.ofList arguments) argument <;> simp [encode]

theorem substituted_encode_supported (context : Context) (arguments : List Preterm) (width : Nat)
    (scopedArguments : ∀ argument ∈ arguments, Term.supportedAt width (encode context argument) = true)
    {expression result : Preterm}
    (substituted : Preterm.Substitutes (Substitution.ofList arguments) expression result) :
    Term.supportedAt width (encode context result) = true := by
  induction substituted with
  | var found => exact scopedArguments _ (List.mem_of_getElem? found)
  | term symbol => rfl
  | app function argument ihFunction ihArgument =>
    simpa [encode, Term.supportedAt, Term.Fields.supportedAt] using And.intro ihFunction ihArgument

/-- Actual common-layer instantiation agrees with independent MM0 substitution. -/
theorem expressionPattern_instantiation (context : Context) (arguments : List Preterm) (width : Nat)
    (scopedArguments : ∀ argument ∈ arguments, Term.supportedAt width (encode context argument) = true)
    (expression : Preterm) :
    (expressionPattern width expression).inst (expressionAssignment context arguments) =
      (Preterm.substitute (Substitution.ofList arguments) expression).map (encode context) := by
  unfold ContextualPatterns.Pattern.inst
  rw [show (expressionPattern width expression).tree = expressionTree width expression from rfl,
    expressionTree_instantiation context arguments width scopedArguments]
  cases substituted : Preterm.substitute (Substitution.ofList arguments) expression with
  | none => rfl
  | some result =>
    have scopedResult := substituted_encode_supported context arguments width scopedArguments
      (Preterm.substitute_sound substituted)
    change (if Term.supportedAt width (encode context result) = true then some (encode context result) else none) =
      some (encode context result)
    rw [if_pos scopedResult]

end Mettapedia.Logic.TierZero.Adequacy.MM0ContextualSupport
