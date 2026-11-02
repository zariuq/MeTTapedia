import Mettapedia.Logic.TierZero.Adequacy.MM0ContextualPatterns
import Mettapedia.Languages.MM0.Kernel.Proof

/-!
# MM0 judgment templates in guarded rewriting's contextual pattern language

Judgment tags are ordinary heads of the common ABT. Their expression fields
use the same contextual patterns as MM0 theorem arguments. Exact decoding
checks the dependency-bearing representation, rather than merely discarding
the dependency fields of a regular variable.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.MM0Rewriting

open Mettapedia.Languages.MM0.Kernel
open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
open Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources
open MM0ContextualSupport

abbrev Tm := Term Head
abbrev Pat := ContextualPatterns.Pattern Head Nat

def fields : List Tm → Fields Head
  | [] => .nil
  | term :: rest => .cons 0 term (fields rest)

def judgment (tag : String) (terms : List Tm) : Tm := .node (.judgment tag) (fields terms)

def expressionFields (width : Nat) : List Preterm → TreePatFields Head (ContextualPatterns.Occurrence Head Nat)
  | [] => .nil
  | expression :: rest => .cons 0 (expressionTree width expression) (expressionFields width rest)

def judgmentPattern (width : Nat) (tag : String) (expressions : List Preterm) : Pat :=
  ⟨width, .node (.judgment tag) (expressionFields width expressions)⟩

theorem fields_injective : Function.Injective fields := by
  intro left
  induction left with
  | nil => intro right equal; cases right <;> simp_all [fields]
  | cons term rest ih =>
      intro right equal
      cases right with
      | nil => simp [fields] at equal
      | cons other tail =>
          have same := Fields.cons.inj equal
          exact congrArg₂ List.cons same.2.1 (ih same.2.2)

theorem judgment_injective (tag : String) : Function.Injective (judgment tag) := by
  intro left right equal
  exact fields_injective (Term.node.inj equal).2

theorem fields_supported (width : Nat) (terms : List Tm) :
    Term.Fields.supportedAt width (fields terms) = true ↔
      ∀ term ∈ terms, Term.supportedAt width term = true := by
  induction terms with
  | nil => simp [fields, Term.Fields.supportedAt]
  | cons term rest ih => simp [fields, Term.Fields.supportedAt, ih]

theorem judgmentPattern_input (width : Nat) (tag : String) (expressions : List Preterm) :
    (judgmentPattern width tag expressions).Input := by
  have each : ∀ es : List Preterm, ∀ occurrence ∈ ContextualPatterns.fieldOccurrences (expressionFields width es),
      occurrence.Input := by
    intro es
    induction es with
    | nil => simp [expressionFields, ContextualPatterns.fieldOccurrences]
    | cons expression rest ih =>
        intro occurrence member
        rcases (show occurrence ∈ ContextualPatterns.occurrences (expressionTree width expression) ∨
            occurrence ∈ ContextualPatterns.fieldOccurrences (expressionFields width rest) from by
          simpa [expressionFields, ContextualPatterns.fieldOccurrences] using member) with head | tail
        · exact expressionPattern_input width expression occurrence head
        · exact ih occurrence tail
  exact each expressions

theorem expressionFields_instantiation (context : Context) (arguments : List Preterm) (width : Nat)
    (scopedArguments : ∀ argument ∈ arguments, Term.supportedAt width (encode context argument) = true) :
    ∀ expressions : List Preterm,
      (expressionFields width expressions).inst
        (ContextualPatterns.Pattern.atOccurrence (expressionAssignment context arguments)) =
      (Substitution.substituteList (Substitution.ofList arguments) expressions).map
        (fun results => fields (results.map (encode context)))
  | [] => rfl
  | expression :: rest => by
      simp only [expressionFields, TreePatFields.inst,
        expressionTree_instantiation context arguments width scopedArguments,
        expressionFields_instantiation context arguments width scopedArguments rest,
        Substitution.substituteList]
      cases expression.substitute (Substitution.ofList arguments) <;>
        cases Substitution.substituteList (Substitution.ofList arguments) rest <;> rfl

theorem judgmentPattern_instantiation (context : Context) (arguments : List Preterm) (width : Nat)
    (scopedArguments : ∀ argument ∈ arguments, Term.supportedAt width (encode context argument) = true)
    (tag : String) (expressions : List Preterm) :
    (judgmentPattern width tag expressions).inst (expressionAssignment context arguments) =
      (Substitution.substituteList (Substitution.ofList arguments) expressions).map
        (fun results => judgment tag (results.map (encode context))) := by
  unfold ContextualPatterns.Pattern.inst
  simp only [judgmentPattern, TreePat.inst,
    expressionFields_instantiation context arguments width scopedArguments]
  cases substituted : Substitution.substituteList (Substitution.ofList arguments) expressions with
  | none => rfl
  | some results =>
      have allScoped : ∀ term ∈ results.map (encode context), Term.supportedAt width term = true := by
        intro term member
        obtain ⟨result, resultMember, rfl⟩ := List.mem_map.mp member
        have relation := (Substitution.substituteList_eq_some_iff _ _ _).mp substituted
        have allResults : ∀ result ∈ results, Term.supportedAt width (encode context result) = true := by
          clear substituted resultMember member
          induction relation with
          | nil => simp
          | cons head tail ih =>
              intro value occurs
              rcases List.mem_cons.mp occurs with rfl | occurs
              · exact substituted_encode_supported context arguments width scopedArguments head
              · exact ih value occurs
        exact allResults result resultMember
      have within := (fields_supported width _).mpr allScoped
      change (if Term.Fields.supportedAt width (fields (results.map (encode context))) = true
        then some (judgment tag (results.map (encode context))) else none) = _
      rw [if_pos within]
      rfl

theorem expression_vars_below (width bound : Nat) {expression : Preterm}
    (bounded : expression.VarsBelow bound) :
    ∀ occurrence ∈ (expressionTree width expression).vars, occurrence.name < bound := by
  induction expression with
  | var index => simpa [expressionTree, TreePat.vars, ambientSlot, Preterm.VarsBelow] using bounded
  | term symbol => simp [expressionTree, TreePat.vars, TreePatFields.vars]
  | app function argument ihFunction ihArgument =>
      intro occurrence member
      have either : occurrence ∈ (expressionTree width function).vars ∨
          occurrence ∈ (expressionTree width argument).vars := by
        simpa [expressionTree, TreePat.vars, TreePatFields.vars] using member
      exact either.elim (ihFunction bounded.1 occurrence) (ihArgument bounded.2 occurrence)

theorem judgmentPattern_vars_below (width bound : Nat) (tag : String) (expressions : List Preterm)
    (bounded : ∀ expression ∈ expressions, expression.VarsBelow bound) :
    ∀ index ∈ (judgmentPattern width tag expressions).vars, index < bound := by
  have each : ∀ es : List Preterm, (∀ e ∈ es, e.VarsBelow bound) →
      ∀ occurrence ∈ (expressionFields width es).vars, occurrence.name < bound := by
    intro es
    induction es with
    | nil => simp [expressionFields, TreePatFields.vars]
    | cons expression rest ih =>
        intro bounds occurrence member
        have either : occurrence ∈ (expressionTree width expression).vars ∨
            occurrence ∈ (expressionFields width rest).vars := by
          simpa [expressionFields, TreePatFields.vars] using member
        exact either.elim (expression_vars_below width bound (bounds expression (by simp)) occurrence)
          (ih (fun e mem => bounds e (by simp [mem])) occurrence)
  intro index member
  obtain ⟨occurrence, occurs, rfl⟩ := Finset.mem_image.mp member
  exact each expressions bounded occurrence occurs

def decodeExact (context : Context) (term : Tm) : Option Preterm := do
  let expression ← decode term
  if encode context expression = term then some expression else none

theorem decodeExact_iff (context : Context) (term : Tm) (expression : Preterm) :
    decodeExact context term = some expression ↔ term = encode context expression := by
  constructor
  · intro success
    unfold decodeExact at success
    cases found : decode term with
    | none => simp [found] at success
    | some result =>
        rw [found] at success
        change (if encode context result = term then some result else none) = some expression at success
        split at success
        · cases success; exact ‹encode context expression = term›.symm
        · cases success
  · intro same
    simp [decodeExact, same, decode_encode]

namespace Controls

theorem exact_decoder_refuses_erased_dependency :
    decodeExact [.bound 0, .regular 0 {0}] (.node (.regular 1) .nil) = none := by
  simp [decodeExact, MM0ContextualSupport.decode, MM0ContextualSupport.encode, encodeVariable, dependencyFields]

theorem exact_decoder_preserves_dependency :
    decodeExact [.bound 0, .regular 0 {0}] (encode [.bound 0, .regular 0 {0}] (.var 1)) = some (.var 1) := by
  exact (decodeExact_iff _ _ _).mpr rfl

theorem judgment_tag_is_not_object_constant : judgment "pf" [] ≠ encode [] (.term 0) := by decide

end Controls

end Mettapedia.Logic.TierZero.Adequacy.MM0Rewriting
