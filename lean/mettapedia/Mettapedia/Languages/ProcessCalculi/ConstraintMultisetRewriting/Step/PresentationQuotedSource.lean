import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PresentationIntrinsicBinding
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramBindersQuoted

/-!
# Authored scalar syntax for the quoted-lambda transform profile

The existing structural grammar carries the actual typed constructor tree,
including binder depths. Its named head interpretation supplies application,
lambda, quotation and activation. Execution uses the contextual equation core;
the independent quoted-lambda step relation is used only for correspondence.
Quotation is inert under this profile's active-context policy. This policy is
not a restriction on the general transform interface.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.QuotedSource

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open QuotedLambda (sig Op)
open LambdaContextualRung (Srt)
open ProgramBinders

local instance : DecidableEq sig.Srt := inferInstanceAs (DecidableEq Srt)

def encodeHead : CommonABT.Head sig → Payloads.Head
  | ⟨_, .app⟩ => .symbol 0
  | ⟨_, .lam⟩ => .symbol 1
  | ⟨_, .quote⟩ => .symbol 2
  | ⟨_, .activate⟩ => .symbol 3

def decodeHead : Payloads.Head → Option (CommonABT.Head sig)
  | .symbol 0 => some ⟨.term, .app⟩
  | .symbol 1 => some ⟨.term, .lam⟩
  | .symbol 2 => some ⟨.term, .quote⟩
  | .symbol 3 => some ⟨.term, .activate⟩
  | _ => none

theorem head_roundtrip (head : CommonABT.Head sig) : decodeHead (encodeHead head) = some head := by
  rcases head with ⟨sort, op⟩
  cases op <;> rfl

def code : Intrinsic.HeadPresentation sig where
  key := ⟨"tcalc.quoted-lambda", 1⟩
  view := encodeHead
  expand := decodeHead
  expand_view := head_roundtrip

def source {Γ : Ctx sig} (term : Term sig Γ .term) : List Nat := Intrinsic.sourceInput code term

noncomputable def read? (Γ : Ctx sig) : List Nat → Option (Term sig Γ .term) :=
  Intrinsic.readSource? code Γ .term

theorem read_source {Γ : Ctx sig} (term : Term sig Γ .term) : read? Γ (source term) = some term :=
  Intrinsic.readSource_print code term

/-- Parsing supplies the terms; both matching and reduction are those of the
existing contextual equation program, including its active-context grammar. -/
def Reduces (Γ : Ctx sig) (input output : List Nat) : Prop :=
  ∃ call answer : Term sig Γ .term, read? Γ input = some call ∧ read? Γ output = some answer ∧
    CRewrites Quoted.grammar (Quoted.schema Γ) call answer

theorem reduction_readback {Γ : Ctx sig} {input output : List Nat}
    (reduced : Reduces Γ input output) {call : Term sig Γ .term} (decoded : read? Γ input = some call) :
    ∃ answer, read? Γ output = some answer ∧ QuotedLambda.Step Γ call answer := by
  obtain ⟨actual, answer, before, after, rewritten⟩ := reduced
  have same : actual = call := Option.some.inj (before.symm.trans decoded)
  subst actual
  exact ⟨answer, after, (Quoted.quoted_rewrites_iff call answer).mp rewritten⟩

theorem encoded_reduction_iff {Γ : Ctx sig} (call answer : Term sig Γ .term) :
    Reduces Γ (source call) (source answer) ↔ QuotedLambda.Step Γ call answer := by
  constructor
  · intro reduced
    obtain ⟨actual, decoded, stepped⟩ := reduction_readback reduced (read_source call)
    have same : actual = answer := Option.some.inj (decoded.symm.trans (read_source answer))
    exact same ▸ stepped
  · intro stepped
    exact ⟨call, answer, read_source call, read_source answer,
      (Quoted.quoted_rewrites_iff call answer).mpr stepped⟩

theorem run_readback {Γ : Ctx sig} {input output : List Nat}
    (run : Relation.ReflTransGen (Reduces Γ) input output)
    {call : Term sig Γ .term} (decoded : read? Γ input = some call) :
    ∃ answer, read? Γ output = some answer ∧ Relation.ReflTransGen (QuotedLambda.Step Γ) call answer := by
  induction run with
  | refl => exact ⟨call, decoded, .refl⟩
  | tail run reduced ih =>
      obtain ⟨middle, readMiddle, earlier⟩ := ih
      obtain ⟨answer, readAnswer, last⟩ := reduction_readback reduced readMiddle
      exact ⟨answer, readAnswer, earlier.tail last⟩

theorem preserves_run {Γ : Ctx sig} {call answer : Term sig Γ .term}
    (run : Relation.ReflTransGen (QuotedLambda.Step Γ) call answer) :
    Relation.ReflTransGen (Reduces Γ) (source call) (source answer) := by
  induction run with
  | refl => exact .refl
  | tail run reduced ih => exact ih.tail ((encoded_reduction_iff _ _).mpr reduced)

theorem encoded_run_iff {Γ : Ctx sig} (call answer : Term sig Γ .term) :
    Relation.ReflTransGen (Reduces Γ) (source call) (source answer) ↔
      Relation.ReflTransGen (QuotedLambda.Step Γ) call answer := by
  constructor
  · intro run
    obtain ⟨actual, decoded, reduced⟩ := run_readback run (read_source call)
    have same : actual = answer := Option.some.inj (decoded.symm.trans (read_source answer))
    exact same ▸ reduced
  · exact preserves_run

/-- Finite source reductions correspond to the retained contextual machine,
whose rules solve their actual matching problems rather than call a source evaluator. -/
theorem contextual_execution_iff {Γ : Ctx sig} (call answer : Term sig Γ .term) :
    Relation.ReflTransGen (Reduces Γ) (source call) (source answer) ↔
      ∃ after, Relation.ReflTransGen (Transition (contextProgram Quoted.grammar (Quoted.schema Γ)))
        (initial call) after ∧ Reads (contextProgram Quoted.grammar (Quoted.schema Γ)) after answer :=
  (encoded_run_iff call answer).trans (Quoted.quoted_execution_iff call answer)

theorem quotation_inert {Γ : Ctx sig} (body : Term sig Γ .term) (output : List Nat) :
    ¬ Reduces Γ (source (QuotedLambda.quote body)) output := by
  intro reduced
  obtain ⟨answer, _, step⟩ := reduction_readback reduced (read_source _)
  exact QuotedLambda.quote_is_inert body answer step

theorem explicit_activation {Γ : Ctx sig} (body : Term sig Γ .term) :
    Reduces Γ (source (QuotedLambda.activate (QuotedLambda.quote body))) (source body) :=
  (encoded_reduction_iff _ _).mpr (.activateQuote body)

theorem beta {Γ : Ctx sig} (body : Term sig (.term :: Γ) .term) (argument : Term sig Γ .term) :
    Reduces Γ (source (QuotedLambda.app (QuotedLambda.lam body) argument)) (source (inst body argument)) :=
  (encoded_reduction_iff _ _).mpr (.beta body argument)

theorem arbitrary_quoted_handle_not_a_constructor (handle : Nat) :
    decodeHead (.quotedRule handle) = none := rfl

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.QuotedSource
