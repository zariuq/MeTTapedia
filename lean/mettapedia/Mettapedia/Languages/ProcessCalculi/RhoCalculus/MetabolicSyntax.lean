import Mettapedia.Languages.ProcessCalculi.RhoCalculus.ResourcePredation

/-!
# Structural stack messages and finite metabolic controllers

Every cell stores its complete encoded signature. Reclaim activates the
received quoted cell through ordinary COMM substitution. The exposed cell
then receives a pop request, reissues its tail and records its consumed head.
No numerical subtraction rule participates in this syntax or its execution.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Metabolic

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.Framework.ConstructorCategory
open Canonical CanonicalTyping CanonicalBag CanonicalReaction
open LanguageDefGSLT LanguageDefRewriteSystem DerivedContextualStep

universe u

/-- A source signature codec supplies stable closed rho syntax. These laws
refer to the actual semantic substitution used by COMM. -/
structure Encoding (Head : Type u) where
  code : Head → Pattern
  typed : ∀ head, ProcWellSorted rhoReflectivePresentation FreeSortContext.empty [] (code head)
  safe : ∀ head depth, binderSafeAt "NQuote" depth (code head) = true
  normalize : ∀ head, semanticNormalizeProc (code head) = code head
  substitution : ∀ head index replacement, semanticSubstProc index replacement (code head) = code head
  canonical : ∀ head, canonicalize (code head) = code head

inductive Stack (Head : Type u) where
  | empty
  | cell (head : Head) (tail : Stack Head)

namespace Stack

def size {Head : Type u} : Stack Head → Nat
  | .empty => 0
  | .cell _ tail => tail.size + 1

def heads {Head : Type u} : Stack Head → List Head
  | .empty => []
  | .cell head tail => head :: tail.heads

theorem size_eq_length {Head : Type u} (stack : Stack Head) :
    stack.size = stack.heads.length := by
  induction stack with
  | empty => rfl
  | cell head tail ih => simp [size, heads, ih]

def append {Head : Type u} : Stack Head → Stack Head → Stack Head
  | .empty, tail => tail
  | .cell head rest, tail => .cell head (rest.append tail)

theorem append_heads {Head : Type u} (first second : Stack Head) :
    (first.append second).heads = first.heads ++ second.heads := by
  induction first with
  | empty => rfl
  | cell head rest ih => simp [append, heads, ih]

theorem append_size {Head : Type u} (first second : Stack Head) :
    (first.append second).size = first.size + second.size := by
  rw [size_eq_length, append_heads, List.length_append, ← size_eq_length, ← size_eq_length]

end Stack

def zero : Pattern := .apply "PZero" []
def metabolic : Pattern := .apply "NQuote" [zero]
def pop : Pattern := .apply "NQuote" [output metabolic zero]
def spent : Pattern := .apply "NQuote" [output pop zero]
def acquisition : Pattern := .apply "NQuote" [output spent zero]
def trigger : Pattern := output pop zero

theorem metabolic_typed (bound : List String) :
    NameWellSorted rhoReflectivePresentation FreeSortContext.empty bound metabolic := .quote .unit

theorem pop_typed (bound : List String) :
    NameWellSorted rhoReflectivePresentation FreeSortContext.empty bound pop :=
  .quote (.output (metabolic_typed _) .unit)

theorem spent_typed (bound : List String) :
    NameWellSorted rhoReflectivePresentation FreeSortContext.empty bound spent :=
  .quote (.output (pop_typed _) .unit)

theorem acquisition_typed (bound : List String) :
    NameWellSorted rhoReflectivePresentation FreeSortContext.empty bound acquisition :=
  .quote (.output (spent_typed _) .unit)

theorem names_safe (depth : Nat) :
    binderSafeAt "NQuote" depth metabolic = true ∧
      binderSafeAt "NQuote" depth pop = true ∧
      binderSafeAt "NQuote" depth spent = true ∧
      binderSafeAt "NQuote" depth acquisition = true := by
  simp [metabolic, pop, spent, acquisition, zero, output, binderSafeAt, binderSafeListAt]

theorem names_distinct : canonicalize metabolic ≠ canonicalize pop ∧
    canonicalize metabolic ≠ canonicalize spent ∧
    canonicalize pop ≠ canonicalize spent ∧
    canonicalize acquisition ≠ canonicalize metabolic := by
  decide +kernel

variable {Head : Type u}

def payload (encoding : Encoding Head) : Stack Head → Pattern
  | .empty => zero
  | .cell head tail => input pop
      (.collection .hashBag [output metabolic (payload encoding tail), output spent (encoding.code head)] none)

def message (encoding : Encoding Head) (stack : Stack Head) : Pattern :=
  output metabolic (payload encoding stack)

def burned (encoding : Encoding Head) (head : Head) : Pattern := output spent (encoding.code head)

def owner : Nat → Pattern
  | 0 => zero
  | count + 1 => input metabolic (.collection .hashBag
      [.apply "PDrop" [.bvar 0], trigger, owner count] none)

def claimant : Pattern := input acquisition (output metabolic (.apply "PDrop" [.bvar 0]))

def offer (encoding : Encoding Head) (stack : Stack Head) : Pattern :=
  output acquisition (payload encoding stack)

theorem payload_typed (encoding : Encoding Head) (stack : Stack Head) (bound : List String) :
    ProcWellSorted rhoReflectivePresentation FreeSortContext.empty bound (payload encoding stack) := by
  induction stack generalizing bound with
  | empty => exact .unit
  | cell head tail ih =>
      exact .input (pop_typed _) (.parallel (.cons
        (.output (metabolic_typed _) (ih _))
        (.cons (.output (spent_typed _) (by simpa using (encoding.typed head).weakenBoundRight _)) .nil)))

theorem payload_safe (encoding : Encoding Head) (stack : Stack Head) (depth : Nat) :
    binderSafeAt "NQuote" depth (payload encoding stack) = true := by
  induction stack generalizing depth with
  | empty => rfl
  | cell head tail ih =>
      simp [payload, input, output, binderSafeAt, binderSafeListAt,
        ih, encoding.safe, (names_safe depth).2.1,
        (names_safe (depth + 1)).1, (names_safe (depth + 1)).2.2.1]

theorem payload_normalize (encoding : Encoding Head) (stack : Stack Head) :
    semanticNormalizeProc (payload encoding stack) = payload encoding stack := by
  induction stack with
  | empty => rfl
  | cell head tail ih =>
      simp [payload, input, output, pop, metabolic, spent, zero,
        semanticNormalizeProc, semanticNormalizeProcList, semanticNormalizeName, ih, encoding.normalize]

theorem payload_substitution (encoding : Encoding Head) (stack : Stack Head)
    (index : Nat) (replacement : Pattern) :
    semanticSubstProc index replacement (payload encoding stack) = payload encoding stack := by
  induction stack generalizing index with
  | empty => rfl
  | cell head tail ih =>
      simp [payload, input, output, pop, metabolic, spent, zero,
        semanticSubstProc, semanticSubstProcList, semanticSubstName, semanticSubstNameMark,
        semanticNormalizeName, semanticNormalizeProc, canonicalize, canonicalizeList, normalizeQuote,
        ih, encoding.substitution]

theorem owner_typed (count : Nat) (bound : List String) :
    ProcWellSorted rhoReflectivePresentation FreeSortContext.empty bound (owner count) := by
  induction count generalizing bound with
  | zero => exact .unit
  | succ count ih =>
      exact .input (metabolic_typed _) (.parallel
        (.cons (.drop (.bvar rfl)) (.cons (.output (pop_typed _) .unit) (.cons (ih _) .nil))))

theorem owner_safe (count depth : Nat) : binderSafeAt "NQuote" depth (owner count) = true := by
  induction count generalizing depth with
  | zero => rfl
  | succ count ih =>
      simp [owner, input, trigger, output, binderSafeAt, binderSafeListAt,
        metabolic, pop, zero, ih]

theorem owner_normalize (count : Nat) : semanticNormalizeProc (owner count) = owner count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp [owner, input, trigger, output, metabolic, pop, zero,
        semanticNormalizeProc, semanticNormalizeProcList, semanticNormalizeName, ih]

theorem owner_substitution (count index : Nat) (replacement : Pattern) :
    semanticSubstProc index replacement (owner count) = owner count := by
  induction count generalizing index with
  | zero => rfl
  | succ count ih =>
      simp [owner, input, trigger, output, metabolic, pop, zero,
        semanticSubstProc, semanticSubstProcList, semanticSubstName, semanticSubstNameMark,
        semanticNormalizeName, semanticNormalizeProc, canonicalize, canonicalizeList, normalizeQuote, ih]

theorem owner_body_typed (count : Nat) :
    ProcWellSorted rhoReflectivePresentation FreeSortContext.empty [rhoReflectivePresentation.nameSort]
      (.collection .hashBag [.apply "PDrop" [.bvar 0], trigger, owner count] none) :=
  .parallel (.cons (.drop (.bvar rfl))
    (.cons (.output (pop_typed _) .unit) (.cons (owner_typed _ _) .nil)))

theorem reclaim_substitution (encoding : Encoding Head) (stack : Stack Head) (count : Nat) :
    semanticCommSubst
      (.collection .hashBag [.apply "PDrop" [.bvar 0], trigger, owner count] none)
      (payload encoding stack) =
      .collection .hashBag [payload encoding stack, trigger, owner count] none := by
  simp [semanticCommSubst, semanticSubstProc, semanticSubstProcList,
    semanticSubstName, semanticSubstNameMark, semanticNormalizeName, semanticNormalizeProc,
    canonicalize, canonicalizeList, normalizeQuote,
    payload_normalize, owner_substitution, trigger, pop, metabolic, output, zero]

theorem pop_substitution (encoding : Encoding Head) (head : Head) (tail : Stack Head) :
    semanticCommSubst
      (.collection .hashBag [message encoding tail, burned encoding head] none) zero =
      .collection .hashBag [message encoding tail, burned encoding head] none := by
  simp [semanticCommSubst, semanticSubstProc, semanticSubstProcList,
    semanticSubstName, semanticSubstNameMark, semanticNormalizeName, semanticNormalizeProc,
    canonicalize, canonicalizeList, normalizeQuote,
    message, burned, metabolic, spent, pop, output, zero, payload_substitution, encoding.substitution]

theorem acquisition_substitution (encoding : Encoding Head) (stack : Stack Head) :
    semanticCommSubst (output metabolic (.apply "PDrop" [.bvar 0])) (payload encoding stack) =
      message encoding stack := by
  simp [semanticCommSubst, semanticSubstProc, semanticSubstName, semanticSubstNameMark,
    canonicalize, canonicalizeList, normalizeQuote,
    semanticNormalizeName, semanticNormalizeProc, payload_normalize, message, output, metabolic, zero]

def closedProcess (pattern : Pattern)
    (typed : ProcWellSorted rhoReflectivePresentation FreeSortContext.empty [] pattern)
    (safe : binderSafeAt "NQuote" 0 pattern = true) : RhoProcess :=
  ⟨pattern, (rhoClosedTermWellSorted_process_iff _).mpr ⟨typed, safe⟩⟩

def messageProcess (encoding : Encoding Head) (stack : Stack Head) : RhoProcess :=
  closedProcess (message encoding stack)
    (.output (metabolic_typed _) (payload_typed _ _ _))
    (by simp [message, output, binderSafeAt, binderSafeListAt, payload_safe, (names_safe 0).1])

def ownerProcess (count : Nat) : RhoProcess := closedProcess (owner count) (owner_typed _ _) (owner_safe _ _)

def burnedProcess (encoding : Encoding Head) (head : Head) : RhoProcess :=
  closedProcess (burned encoding head) (.output (spent_typed _) (encoding.typed head))
    (by simp [burned, output, binderSafeAt, binderSafeListAt, encoding.safe, (names_safe 0).2.2.1])

def parallel (parts : List RhoProcess) : RhoProcess :=
  ofList (parts.map Subtype.val) (by
    intro pattern member
    obtain ⟨process, _, rfl⟩ := List.mem_map.mp member
    exact process.2)

def live (encoding : Encoding Head) (stack : Stack Head) (count : Nat) (record : List Head) : RhoProcess :=
  parallel ([messageProcess encoding stack, ownerProcess count] ++ record.map (burnedProcess encoding))

def reclaimed (encoding : Encoding Head) (stack : Stack Head) (count : Nat) (record : List Head) : RhoProcess :=
  parallel ([closedProcess (payload encoding stack) (payload_typed _ _ _) (payload_safe _ _ _),
    closedProcess trigger (.output (pop_typed _) .unit)
      (by simp [trigger, output, binderSafeAt, binderSafeListAt, zero, (names_safe 0).2.1]),
    ownerProcess count] ++ record.map (burnedProcess encoding))

def acquisitionSource (encoding : Encoding Head) (stack : Stack Head) (count : Nat)
    (record : List Head) : RhoProcess :=
  parallel ([closedProcess claimant
    (.input (acquisition_typed _) (.output (metabolic_typed _) (.drop (.bvar rfl))))
    (by simp [claimant, input, output, binderSafeAt, binderSafeListAt,
      metabolic, acquisition, spent, pop, zero]),
    closedProcess (offer encoding stack) (.output (acquisition_typed _) (payload_typed _ _ _))
      (by simp [offer, output, binderSafeAt, binderSafeListAt, payload_safe, (names_safe 0).2.2.2]),
    ownerProcess count] ++ record.map (burnedProcess encoding))

/-- Readout follows the actual recursive cell syntax and retains each head.
It does not infer a resource count from a controller or predicted execution. -/
inductive PayloadReadout : Pattern → List Pattern → Prop
  | empty : PayloadReadout zero []
  | cell (head tail : Pattern) (heads : List Pattern) (rest : PayloadReadout tail heads) :
      PayloadReadout
        (input pop (.collection .hashBag [output metabolic tail, output spent head] none))
        (head :: heads)

theorem payload_readout (encoding : Encoding Head) (stack : Stack Head) :
    PayloadReadout (payload encoding stack) (stack.heads.map encoding.code) := by
  induction stack with
  | empty => exact .empty
  | cell head tail ih => exact .cell _ _ _ ih

theorem payload_readout_unique {pattern : Pattern} {first second : List Pattern}
    (left : PayloadReadout pattern first) (right : PayloadReadout pattern second) : first = second := by
  induction left generalizing second with
  | empty =>
      generalize shape : zero = pattern at right
      cases right with
      | empty => rfl
      | cell otherHead otherTail otherHeads otherRest => simp [zero, input] at shape
  | cell head tail heads rest ih =>
      generalize shape : input pop (.collection .hashBag
        [output metabolic tail, output spent head] none) = pattern at right
      cases right with
      | empty => simp [zero, input] at shape
      | cell otherHead otherTail otherHeads otherRest =>
          have parts : tail = otherTail ∧ head = otherHead := by
            simpa [input, output] using shape
          rcases parts with ⟨rfl, rfl⟩
          exact congrArg (List.cons head) (ih otherRest)

theorem payload_complete_readout (encoding : Encoding Head) (stack : Stack Head) (heads : List Pattern) :
    PayloadReadout (payload encoding stack) heads ↔ heads = stack.heads.map encoding.code :=
  ⟨fun actual => payload_readout_unique actual (payload_readout encoding stack),
    fun same => same ▸ payload_readout encoding stack⟩

theorem one_cell_burn (head : Head) (tail : Stack Head) :
    (Stack.cell head tail).size = tail.size + 1 := rfl

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Metabolic
