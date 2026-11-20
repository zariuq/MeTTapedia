import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.FiniteConventionHosting
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.FiniteNestedControls

/-!
# Renaming into the variable convention: examples and controls

The step is the single-firing step of the three-rule `program` of `FiniteComm` at the one frame of structural
substitution on patterns, with the five choices stated there.

## A process outside the convention, hosted as written and renamed

`for((0) <- @0)0 | for(y <- @0)y | for(y <- @((0)))y` (`FiniteNestedControls.sharedSource`): the receiver and the
third part both bind `y`.
* Hosted as written (`shared_literal_misreads`): a communication of the program exists at its initial state, and
  after every one the third row, untouched, reads at every solution of the knowledge as
  `for((0) <- @((0)))@((0))`: the communication fixed `y`, and the third part's binder is read as the value.
  That reading is not alpha-equivalent to the third part.
* Renamed apart (`shared_renamed_matched`): the renamed process is alpha-equivalent and hosted, the source's COMM
  is a step up to alpha-equivalence, and the step runs it from the renamed process's initial state to a state
  that represents an alpha-variant of the source's reduct.

## Tameness is needed

`for(y <- @0)(bvar ⟨0,0⟩)`: the receiver with a code in place of its bound occurrence. It is hosted and not tame;
its closed form is the receiver's, and the manuscript's renaming rule does not relate the two
(`code_breaks_alpha_respect`, the argument of `Corrected.alphaEq_not_alpha_with_code` at the receiver). The bag
presentation takes the two alpha-equivalent bags to reducts that are not alpha-equivalent: `@((0))`, and the code.
So without tameness the bag presentation does not respect alpha-equivalence, and the closed form cannot tell a
code from a bound occurrence. The tree's own pair, `for(x <- @0)x` and `for(x <- @0)(bvar ⟨0,0⟩)`, are both hosted
parts with one closed form that renaming does not relate (`code_hosted_not_renamable`).

## Shadowing: the convention within a part

`for((0) <- @0)0 | for(y <- @0)for(y <- @((0)))y` (`shadowing_renamed_apart`): the inner input binds the receiver's
name again, so the redex breaks `Corrected.Apart`, and the dot of the continuation as written substitutes into the
inner binder. After renaming apart the convention holds, and the dot of the renamed continuation is
alpha-equivalent to the corrected reduct `for(y <- @((0)))y`.

## The corrected semantics' EQUIV ranges over codes

`corrected_step_reaches_a_code`: the tree's corrected semantics (`Corrected.Step`, and `Corrected.BagCommStep`
modulo the bag laws) takes equality of closed forms as its EQUIV on all syntax. With the admission `conventional`
it steps from the manuscript's example, through the code variant of the receiver, to `0 | bvar ⟨0,0⟩`, which is not
alpha-equivalent to the manuscript's reduct; no step of the source up to alpha-equivalence reaches it, so the
converse of `FiniteBridge` fails for that admission. With the admission `closing` every step from the example is
alpha-equivalent to the manuscript's reduct.

## The convention along a step of the corrected semantics

`corrected_step_breaks_convention`: the corrected semantics determines a step's target only up to
alpha-equivalence; from a hosted process it reaches a process whose two parts bind the same name. Renaming apart
re-establishes the convention.

## The mechanisms compared

* (a) renaming by names: in `for(y <- x)for(x <- @0)x` the name `x` is free in the channel and bound by the inner
  input. Every renaming of names that keeps the part alpha-equivalent fixes `x`, so the inner binder keeps the
  name of a free variable; the canonical renaming renames that binder alone (`names_cannot_separate`).
* (b) the canonical renaming, by depth and position, gives two sibling inputs at one depth the same names:
  `for(y <- @0)(for(a <- y)a | for(b <- y)b)` has frames apart, its canonical renaming does not
  (`canonical_merges_siblings`). The hosted fragment has one frame per part, so (b) serves it; the nested
  fragment needs names that also carry the input's position.
* (c) the closed form in place of a renaming: hosted as data, the closed forms of the manuscript's example take no
  COMM step, since a code is a constant to the unifier (`closed_forms_take_no_step`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.FiniteConvention.Controls

open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus (pFor par pZero nQuote applyDot demoChan)
open MeTTaOperationsComm (psubst pvars patternAction PSubst psubst_of_pvars_nil commSelection)
open MeTTaCalculus.Corrected (Apart tame Alpha AlphaEq close closeIn canon binders rename rename_pFor rename_fvar
  closeIn_pFor alpha_calcTerm)
open FiniteProgram (parts Hosted HostedProcess BagComm Represents Communicates initial commAt comm_normal
  comm_reads_inputs program parts_pZero predot frames FramesApart pFor_inj)
open MeTTaCalculus.OccurrenceCommits (fire)
open Comm (Tm X E)
open Comm.Controls (zeroTerm y sender receiver source unifier reduct unifier_groundPrincipal)
open FiniteProgram.Controls (unifier_values example_apart parts_source parts_reduct)
open FiniteProgram.NestedControls (echo sharedSource sharedReduct parts_sharedSource parts_sharedReduct shared_step
  shared_comm_pins shared_label shared_present sharedPattern sharedChannel sharedBody example_step_target)
open LogicOverTheStep.StepSpan (Succ)

/-! ## A process outside the convention, hosted as written -/

/-- The third part with its binder read as the value: `for((0) <- @((0)))@((0))`. -/
def echoMisread : Pattern := pFor zeroTerm (nQuote zeroTerm) (nQuote zeroTerm)

theorem sender_hosted : Hosted sender := ⟨by decide +kernel, .inl (by decide +kernel)⟩

theorem receiver_hosted : Hosted receiver :=
  ⟨by decide +kernel, .inr ⟨y, demoChan, y, rfl, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

theorem echo_hosted : Hosted echo :=
  ⟨by decide +kernel, .inr ⟨y, nQuote zeroTerm, y, rfl, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

theorem shared_hosted_parts : ∀ c ∈ parts sharedSource, Hosted c := by
  rw [parts_sharedSource]
  intro c member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact sender_hosted
  · exact receiver_hosted
  · exact echo_hosted

theorem shared_not_hostedProcess : ¬ HostedProcess sharedSource := by
  intro hostedP
  have disjoint := hostedP.disjoint
  rw [parts_sharedSource] at disjoint
  exact absurd disjoint (by decide +kernel)

/-- A communication of the program at the initial state of the process as written. -/
theorem shared_communicates : ∃ s', Communicates (initial (parts sharedSource)) s' := by
  obtain ⟨m₁, m₂, fresh₁, fresh₂, madeDistinct⟩ := FiniteProgram.two_fresh (initial (parts sharedSource)).present
  obtain ⟨ρ, opensFreshly⟩ := FiniteProgram.exists_fresh_opening (initial (parts sharedSource)).label
    ⟨(initial (parts sharedSource)).knowledge, (initial (parts sharedSource)).present⟩ 0 1 m₁ m₂
  have label₀ : (initial (parts sharedSource)).label 0 = predot (pFor zeroTerm demoChan pZero) := by decide +kernel
  have label₁ : (initial (parts sharedSource)).label 1 = predot (pFor y demoChan y) := by decide +kernel
  have admitted := FiniteProgram.comm_admits (initial (parts sharedSource)).label zeroTerm y demoChan pZero y
    ⟨(initial (parts sharedSource)).knowledge, (initial (parts sharedSource)).present⟩ 0 1 m₁ m₂
    (fun σ _ => by rw [label₀]) (fun σ _ => by rw [label₁]) (by decide) madeDistinct (by decide +kernel)
    (by decide +kernel) fresh₁ fresh₂ (σ₀ := fun v => if v = "y" then some zeroTerm else none)
    (fun _ member => absurd member List.not_mem_nil) (by decide +kernel) opensFreshly
  exact ⟨_, commAt ρ 0 1 m₁ m₂, rfl, admitted, rfl⟩

theorem shared_label_two : (initial (parts sharedSource)).label 2 = predot echo := by decide +kernel

/-- After a communication at the initial state of the process as written, the third row is present and keeps its
label. -/
theorem shared_third_row {s' : State Tm ℕ} (fires : Communicates (initial (parts sharedSource)) s') :
    2 ∈ s'.present ∧ s'.label 2 = predot echo := by
  obtain ⟨f, isComm, admitted, rfl⟩ := fires
  obtain ⟨o₁, o₂, m₁, m₂, same, distinct, madeDistinct, present₁, present₂, fresh₁, fresh₂⟩ :=
    comm_normal f isComm admitted
  rw [same] at admitted ⊢
  have small₁ := shared_present present₁
  have small₂ := shared_present present₂
  obtain ⟨-, -, ⟨_, σ₀, solved₀⟩, -⟩ := admitted
  obtain ⟨-, -, channels, -, -⟩ := comm_reads_inputs (initial (parts sharedSource)).label
    (sharedPattern o₁) (sharedPattern o₂) (sharedChannel o₁) (sharedChannel o₂) (sharedBody o₁)
    (sharedBody o₂) ⟨(initial (parts sharedSource)).knowledge, (initial (parts sharedSource)).present⟩
    o₁ o₂ m₁ m₂ (fun τ _ => by rw [shared_label small₁]) (fun τ _ => by rw [shared_label small₂])
    madeDistinct f.opening solved₀
  have groundChannel : ∀ o, psubst σ₀ (sharedChannel o) = sharedChannel o := fun o =>
    psubst_of_pvars_nil σ₀ _ (by unfold sharedChannel; split_ifs <;> decide +kernel)
  rw [groundChannel, groundChannel] at channels
  have notThird : o₁ ≠ 2 ∧ o₂ ≠ 2 := by
    interval_cases o₁ <;> interval_cases o₂
    all_goals first
      | exact absurd rfl distinct
      | exact absurd channels (by decide +kernel)
      | decide
  have third : 2 ∈ (initial (parts sharedSource)).present := by decide +kernel
  have made₁ : m₁ ≠ 2 := fun same => fresh₁ (same ▸ third)
  have made₂ : m₂ ≠ 2 := fun same => fresh₂ (same ▸ third)
  refine ⟨?_, ?_⟩
  · show 2 ∈ fire (initial (parts sharedSource)).present ((commSelection o₁ o₂ m₁ m₂).commit (T := Unit))
    simp only [fire, Selection.commit, commSelection, Finset.mem_union, Finset.mem_sdiff]
    left
    refine ⟨third, ?_⟩
    simp [Ne.symm notThird.1, Ne.symm notThird.2]
  · rw [FiniteProgram.result_label_kept (initial (parts sharedSource))
      (by simp [commAt, commSelection, Ne.symm made₁, Ne.symm made₂])]
    exact shared_label_two

/-- **Control: hosted as written, the third part misreads.** The process `for((0) <- @0)0 | for(y <- @0)y |
for(y <- @((0)))y` is not a hosted process, since two parts bind `y`. A communication of the program exists at its
initial state, and after every one the untouched third row reads, at every solution of the knowledge, as
`for((0) <- @((0)))@((0))`, which is not alpha-equivalent to the third part. -/
theorem shared_literal_misreads :
    ¬ HostedProcess sharedSource ∧ (∃ s', Communicates (initial (parts sharedSource)) s') ∧
      (∀ s', Communicates (initial (parts sharedSource)) s' → 2 ∈ s'.present ∧
        ∀ σ : PSubst, patternAction.Models σ s'.knowledge → psubst σ (s'.label 2) = echoMisread) ∧
      ¬ AlphaEq echoMisread echo := by
  refine ⟨shared_not_hostedProcess, shared_communicates, fun s' fires => ?_, by decide +kernel⟩
  obtain ⟨present, label⟩ := shared_third_row fires
  refine ⟨present, fun σ solved => ?_⟩
  have pinned := shared_comm_pins fires σ solved
  rw [label, show predot echo = pFor y (nQuote zeroTerm) (nQuote y) by decide +kernel, MeTTaOperationsComm.psubst_pFor]
  show pFor ((σ "y").getD (.fvar "y")) (psubst σ (nQuote zeroTerm)) (nQuote ((σ "y").getD (.fvar "y"))) = _
  rw [pinned, psubst_of_pvars_nil σ _ (by decide +kernel)]
  rfl

/-- **The same process renamed apart is matched.** It is alpha-equivalent to the process and hosted; the source's
COMM of the sender and the receiver is a step up to alpha-equivalence; and the single-firing step runs it, from
the renamed process's initial state, to a state that represents an alpha-variant of the source's reduct. -/
theorem shared_renamed_matched :
    Alpha sharedSource (renameApart sharedSource) ∧ HostedProcess (renameApart sharedSource) ∧
      CommUpToAlpha (parts sharedSource : Multiset Pattern) (parts sharedReduct : Multiset Pattern) ∧
      ∃ (s' : State Tm ℕ) (M' : Multiset Pattern),
        Relation.ReflTransGen (Succ (RuleSyntax.step X ℕ E program).toStep)
          (initial (parts (renameApart sharedSource))) s' ∧
          Represents s' M' ∧ M'.map close = (parts sharedReduct : Multiset Pattern).map close := by
  have tameP : tame sharedSource = true := by decide +kernel
  obtain ⟨alpha, hostedP', -⟩ := renaming_into_the_convention sharedSource tameP shared_hosted_parts
  have step : CommUpToAlpha (parts sharedSource : Multiset Pattern) (parts sharedReduct : Multiset Pattern) :=
    ⟨_, _, fun c member => FiniteConvention.tame_of_mem_parts sharedSource c (Multiset.mem_coe.mp member) tameP,
      rfl, shared_step, rfl⟩
  exact ⟨alpha, hostedP', step,
    hosted_runs_up_to_alpha sharedSource tameP shared_hosted_parts (Relation.ReflTransGen.single step)⟩

/-- **The fifth clause of `manuscript_calculus_without_the_convention`, at the process outside the convention.**
From the initial state of the renamed process, the source's COMM, taken from the process as written, is matched by
housekeeping firings and one communication, up to alpha-equivalence of the target. -/
theorem shared_fifth_clause :
    ∃ (s₁ s₂ : State Tm ℕ) (M'' : Multiset Pattern),
      Relation.ReflTransGen FiniteProgram.Administers (initial (parts (renameApart sharedSource))) s₁ ∧
        Communicates s₁ s₂ ∧ Represents s₂ M'' ∧
        M''.map close = (parts sharedReduct : Multiset Pattern).map close := by
  have tameP : tame sharedSource = true := by decide +kernel
  obtain ⟨start, tame₀, -, -⟩ := renamed_bag sharedSource tameP shared_hosted_parts
  have hostedP' := (renaming_into_the_convention sharedSource tameP shared_hosted_parts).2.1
  exact communication_complete_up_to_alpha ⟨_, FiniteProgram.initial_represents (renameApart sharedSource) hostedP'⟩
    tame₀ ⟨_, _, fun c member => FiniteConvention.tame_of_mem_parts sharedSource c (Multiset.mem_coe.mp member) tameP,
      start, shared_step, rfl⟩

/-! ## Tameness is needed -/

/-- The code bound at the outermost frame, in place of a bound occurrence. -/
def codeValue : Pattern := .bvar (Nat.pair 0 0)

/-- The receiver with a code in place of its bound occurrence: `for(y <- @0)(bvar ⟨0,0⟩)`. -/
def codeReceiver : Pattern := pFor y demoChan codeValue

/-- `for((0) <- @0)0 | for(y <- @0)(bvar ⟨0,0⟩)`. -/
def codeSource : Pattern := par sender codeReceiver

theorem parts_codeSource : parts codeSource = [sender, codeReceiver] := by decide +kernel

theorem code_apart : Apart zeroTerm pZero y codeValue :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- **Control: tameness is needed.** The receiver with a code in place of its bound occurrence is hosted and not
tame. Its closed form is the receiver's, and the manuscript's renaming rule does not relate the two. The bags of
`for((0) <- @0)0 | for(y <- @0)y` and of the code variant have the same closed forms; the code variant's COMM gives
the code, and every COMM of the manuscript's example gives `@((0))`, which is not alpha-equivalent to it. -/
theorem code_breaks_alpha_respect :
    Hosted codeReceiver ∧ tame codeReceiver = false ∧ AlphaEq receiver codeReceiver ∧
      ¬ Alpha receiver codeReceiver ∧
      (parts codeSource : Multiset Pattern).map close = (parts source : Multiset Pattern).map close ∧
      BagComm (parts codeSource : Multiset Pattern) {codeValue} ∧
      (∀ M', BagComm (parts source : Multiset Pattern) M' → M' = parts reduct) ∧
      ¬ ∃ M', BagComm (parts source : Multiset Pattern) M' ∧
        M'.map close = ({codeValue} : Multiset Pattern).map close := by
  refine ⟨⟨by decide +kernel, .inr ⟨y, demoChan, codeValue, rfl, by decide +kernel, by decide +kernel,
    by decide +kernel⟩⟩, by decide +kernel, by decide +kernel, fun alpha => ?_, ?_, ?_,
    fun M' step => example_step_target step, ?_⟩
  · have := alpha_calcTerm alpha
    revert this
    decide +kernel
  · rw [parts_codeSource, parts_source, Multiset.map_coe, Multiset.map_coe]
    exact congrArg _ (by decide +kernel : List.map close [sender, codeReceiver] = List.map close [sender, receiver])
  · have step := BagComm.comm zeroTerm y demoChan pZero codeValue unifier 0 unifier_groundPrincipal code_apart
      unifier_values
    have start : (parts codeSource : Multiset Pattern) =
        pFor zeroTerm demoChan pZero ::ₘ pFor y demoChan codeValue ::ₘ 0 := by
      rw [parts_codeSource]
      rfl
    have target : (parts (applyDot unifier pZero) : Multiset Pattern) +
        (parts (applyDot unifier codeValue) : Multiset Pattern) + 0 = {codeValue} := by
      rw [show applyDot unifier pZero = pZero by decide +kernel,
        show applyDot unifier codeValue = codeValue by decide +kernel, parts_pZero,
        show parts codeValue = [codeValue] by decide +kernel]
      rfl
    rw [start, ← target]
    exact step
  · rintro ⟨M', step, closeSame⟩
    rw [example_step_target step, parts_reduct] at closeSame
    revert closeSame
    decide +kernel

/-! ## The convention along a step of the corrected semantics -/

/-- `for(a <- @((0)))a`. -/
def listenerA : Pattern := pFor (.fvar "a") (nQuote zeroTerm) (.fvar "a")

/-- `for(b <- @((0)))b`. -/
def listenerB : Pattern := pFor (.fvar "b") (nQuote zeroTerm) (.fvar "b")

/-- The manuscript's example beside two listeners that bind different names. -/
def withListeners : Pattern := par source (par listenerA listenerB)

/-- The manuscript's reduct beside two listeners that bind the same name. -/
def reductSameNames : Pattern := par reduct (par listenerA listenerA)

theorem listenerA_hosted : Hosted listenerA :=
  ⟨by decide +kernel, .inr ⟨.fvar "a", nQuote zeroTerm, .fvar "a", rfl, by decide +kernel, by decide +kernel,
    by decide +kernel⟩⟩

theorem listenerB_hosted : Hosted listenerB :=
  ⟨by decide +kernel, .inr ⟨.fvar "b", nQuote zeroTerm, .fvar "b", rfl, by decide +kernel, by decide +kernel,
    by decide +kernel⟩⟩

/-- **Control: the corrected semantics does not keep the convention.** From a hosted process, the tree's corrected
semantics, whose EQUIV rule is alpha-equivalence, reaches a process whose two listeners bind the same name; it is
not a hosted process. Renaming apart re-establishes the convention. -/
theorem corrected_step_breaks_convention :
    HostedProcess withListeners ∧
      MeTTaCalculus.Corrected.Step MeTTaCalculus.Corrected.conventional withListeners reductSameNames ∧
      ¬ HostedProcess reductSameNames ∧
      Alpha reductSameNames (renameApart reductSameNames) ∧ HostedProcess (renameApart reductSameNames) := by
  have partsBefore : parts withListeners = [sender, receiver, listenerA, listenerB] := by decide +kernel
  have partsAfter : parts reductSameNames = [nQuote zeroTerm, listenerA, listenerA] := by decide +kernel
  have hostedAfter : ∀ c ∈ parts reductSameNames, Hosted c := by
    rw [partsAfter]
    intro c member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact ⟨by decide +kernel, .inl (by decide +kernel)⟩
    · exact listenerA_hosted
    · exact listenerA_hosted
  obtain ⟨alpha, hostedRenamed, -⟩ :=
    renaming_into_the_convention reductSameNames (by decide +kernel) hostedAfter
  refine ⟨⟨fun c member => ?_, ?_⟩, ?_, fun hostedP => ?_, alpha, hostedRenamed⟩
  · rw [partsBefore] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact sender_hosted
    · exact receiver_hosted
    · exact listenerA_hosted
    · exact listenerB_hosted
  · rw [partsBefore]
    decide +kernel
  · have comm : MeTTaCalculus.Corrected.Step MeTTaCalculus.Corrected.conventional source
        (par (applyDot unifier pZero) (applyDot unifier y)) :=
      .comm zeroTerm y demoChan pZero y unifier (Comm.principal_of_groundPrincipal unifier_groundPrincipal)
        example_apart
    exact .congruence (MeTTaCalculus.Corrected.AlphaEq.refl _) (.parallel (par listenerA listenerB) comm)
      (by decide +kernel)
  · have disjoint := hostedP.disjoint
    rw [partsAfter] at disjoint
    exact absurd disjoint (by decide +kernel)

/-! ## The mechanisms compared -/

/-- A part in which `x` is free, in the channel, and bound, by the inner input: `for(y <- x)for(x <- @0)x`. -/
def freeAndBound : Pattern := pFor y (.fvar "x") (pFor (.fvar "x") demoChan (.fvar "x"))

/-- Every renaming of names that keeps `for(y <- x)for(x <- @0)x` alpha-equivalent fixes `x`. -/
theorem renaming_by_names_fixes_free {g : String → String}
    (alpha : AlphaEq freeAndBound (rename g freeAndBound)) : g "x" = "x" := by
  have closed : closeIn [] freeAndBound = closeIn [] (rename g freeAndBound) := alpha
  unfold freeAndBound at closed
  rw [rename_pFor, closeIn_pFor, closeIn_pFor] at closed
  have channels := (pFor_inj closed).2.1
  rw [rename_fvar] at channels
  simp only [closeIn, MeTTaCalculus.Corrected.lookupBound, Pattern.fvar.injEq] at channels
  exact channels.symm

/-- **Control: renaming by names.** In `for(y <- x)for(x <- @0)x` the name `x` is free in the channel and bound by
the inner input. Every renaming of names that keeps the part alpha-equivalent fixes `x`, so the inner binder keeps
the name of a free variable. The canonical renaming, which acts on binding occurrences, renames the inner binder
alone, by the manuscript's rule. -/
theorem names_cannot_separate :
    (∀ g : String → String, AlphaEq freeAndBound (rename g freeAndBound) → g "x" = "x") ∧
      "x" ∈ pvars (close freeAndBound) ∧ "x" ∈ binders freeAndBound ∧
      Alpha freeAndBound (canon (partName (pvars freeAndBound) 0) 0 freeAndBound) ∧
      "x" ∉ binders (canon (partName (pvars freeAndBound) 0) 0 freeAndBound) ∧
      "x" ∈ pvars (canon (partName (pvars freeAndBound) 0) 0 freeAndBound) :=
  ⟨fun _ alpha => renaming_by_names_fixes_free alpha, by decide +kernel, by decide +kernel,
    alpha_canon_part (pvars freeAndBound) 0 (by decide +kernel) fun _ occurs => occurs, by decide +kernel,
    by decide +kernel⟩

/-- Two sibling inputs at one depth: `for(y <- @0)(for(a <- y)a | for(b <- y)b)`. -/
def siblings : Pattern :=
  pFor y demoChan (par (pFor (.fvar "a") y (.fvar "a")) (pFor (.fvar "b") y (.fvar "b")))

/-- **Control: the canonical renaming by depth and position.** The two sibling inputs of
`for(y <- @0)(for(a <- y)a | for(b <- y)b)` bind different names; after the canonical renaming they bind the same
name, so the convention within a part of the nested fragment (`FramesApart`) fails. The renaming is alpha. -/
theorem canonical_merges_siblings :
    FramesApart (frames siblings) ∧
      ¬ FramesApart (frames (canon (partName (pvars siblings) 0) 0 siblings)) ∧
      Alpha siblings (canon (partName (pvars siblings) 0) 0 siblings) :=
  ⟨by decide +kernel, by decide +kernel,
    alpha_canon_part (pvars siblings) 0 (by decide +kernel) fun _ occurs => occurs⟩

/-- The closed form of the receiver: its bound name is the code of its own frame. -/
def closedReceiver : Pattern := pFor codeValue demoChan codeValue

theorem close_receiver : close receiver = closedReceiver := by decide +kernel

/-- **Control: closed forms in place of a renaming.** Hosted as data, the closed forms of the manuscript's
example take no COMM step of the bag presentation, while the example takes one: to the unifier, a code is a
constant, and it does not unify with `(0)`. -/
theorem closed_forms_take_no_step :
    BagComm (parts source : Multiset Pattern) (parts reduct : Multiset Pattern) ∧
      (parts source).map close = [sender, closedReceiver] ∧
      ∀ M', ¬ BagComm ([sender, closedReceiver] : Multiset Pattern) M' := by
  refine ⟨FiniteProgram.Controls.example_bagComm, by decide +kernel, fun M' step => ?_⟩
  generalize start : ([sender, closedReceiver] : Multiset Pattern) = N at step
  obtain ⟨t, u, x, A, B, bs, rest, gp, -, -⟩ := step
  have first : pFor t x A ∈ ([sender, closedReceiver] : Multiset Pattern) := by
    rw [start]
    exact Multiset.mem_cons_self _ _
  have second : pFor u x B ∈ ([sender, closedReceiver] : Multiset Pattern).erase (pFor t x A) := by
    rw [start, Multiset.erase_cons_head]
    exact Multiset.mem_cons_self _ _
  have senderNe : sender ≠ closedReceiver := by decide +kernel
  have zeroNe : zeroTerm ≠ codeValue := by decide +kernel
  have solves := gp.solves
  have groundZero : psubst bs.lookup zeroTerm = zeroTerm := psubst_of_pvars_nil _ zeroTerm (by decide +kernel)
  have codeFixed : psubst bs.lookup codeValue = codeValue := rfl
  simp only [Multiset.mem_coe, List.mem_cons, List.not_mem_nil, or_false] at first
  rcases first with isSender | isReceiver
  · rw [isSender, Multiset.coe_erase, List.erase_cons_head] at second
    have isReceiver := List.mem_singleton.mp (Multiset.mem_coe.mp second)
    obtain ⟨rfl, -, -⟩ := pFor_inj (show pFor t x A = pFor zeroTerm demoChan pZero from isSender)
    obtain ⟨rfl, -, -⟩ := pFor_inj (show pFor u x B = pFor codeValue demoChan codeValue from isReceiver)
    rw [groundZero, codeFixed] at solves
    exact zeroNe solves
  · rw [isReceiver, Multiset.coe_erase, List.erase_cons_tail (by simpa using senderNe), List.erase_cons_head]
      at second
    have isSender := List.mem_singleton.mp (Multiset.mem_coe.mp second)
    obtain ⟨rfl, -, -⟩ := pFor_inj (show pFor t x A = pFor codeValue demoChan codeValue from isReceiver)
    obtain ⟨rfl, -, -⟩ := pFor_inj (show pFor u x B = pFor zeroTerm demoChan pZero from isSender)
    rw [groundZero, codeFixed] at solves
    exact zeroNe solves.symm

/-! ## The corrected semantics' EQUIV ranges over codes -/

/-- **Control: the corrected semantics reaches a code.** The tree's corrected semantics takes equality of closed
forms as its EQUIV on all syntax. From the manuscript's example it passes to the code variant of the receiver, and
its COMM there gives `0 | bvar ⟨0,0⟩`, which is not alpha-equivalent to the manuscript's reduct `0 | @((0))`; the
same holds modulo the bag laws. No step of the source up to alpha-equivalence from the example reaches it, so the
converse of `FiniteBridge` fails for the admission `conventional`. With the closing admission (calculus
continuations, ground reads) every step from the example is alpha-equivalent to the manuscript's reduct. -/
theorem corrected_step_reaches_a_code :
    MeTTaCalculus.Corrected.Step MeTTaCalculus.Corrected.conventional source (par pZero codeValue) ∧
      MeTTaCalculus.Corrected.BagCommStep MeTTaCalculus.Corrected.conventional source (par pZero codeValue) ∧
      ¬ AlphaEq (par pZero codeValue) reduct ∧
      ¬ MeTTaCalculus.Corrected.BagEq (par pZero codeValue) reduct ∧
      (¬ ∃ M', CommUpToAlpha (parts source : Multiset Pattern) M' ∧
        M'.map close = (parts (par pZero codeValue) : Multiset Pattern).map close) ∧
      ∀ Q, MeTTaCalculus.Corrected.Step MeTTaCalculus.Corrected.closing source Q → AlphaEq Q reduct := by
  have toCode : AlphaEq source codeSource := by decide +kernel
  have reducts : AlphaEq (par (applyDot unifier pZero) (applyDot unifier codeValue)) (par pZero codeValue) := by
    decide +kernel
  have principal := Comm.principal_of_groundPrincipal unifier_groundPrincipal
  refine ⟨.congruence toCode (.comm zeroTerm y demoChan pZero codeValue unifier principal code_apart) reducts,
    .congruence (MeTTaCalculus.Corrected.BagEq.of_alphaEq toCode)
      (.comm zeroTerm y demoChan pZero codeValue unifier principal code_apart)
      (MeTTaCalculus.Corrected.BagEq.of_alphaEq reducts),
    by decide +kernel, by unfold MeTTaCalculus.Corrected.BagEq; decide +kernel, ?_, fun Q step => ?_⟩
  · rintro ⟨M', step, closeSame⟩
    have hostedP := FiniteProgram.Controls.example_hostedProcess
    have tameParts : ∀ c ∈ (parts source : Multiset Pattern), tame c = true := fun c member =>
      FiniteConvention.tame_of_mem_parts source c (Multiset.mem_coe.mp member) (by decide +kernel)
    obtain ⟨M'', commM, closeM''⟩ := bagComm_of_commUpToAlpha tameParts
      (fun c member => hostedP.hosted c (Multiset.mem_coe.mp member)) (convention_of_pairwise _ hostedP.disjoint)
      step
    rw [example_step_target commM] at closeM''
    have wrong := closeM''.trans closeSame
    rw [parts_reduct] at wrong
    revert wrong
    decide +kernel
  · obtain ⟨Q', member, same⟩ := MeTTaCalculus.Corrected.cstep_complete step
    have computed : MeTTaCalculus.Corrected.cstep source = [reduct] := by decide +kernel
    rw [computed, List.mem_singleton] at member
    subst member
    exact MeTTaCalculus.Corrected.AlphaEq.symm same

/-! ## The tree's control of a code, at the hosted fragment -/

/-- **Control: renaming is not available outside tame processes.** The tree's `for(x <- @0)x` and
`for(x <- @0)(bvar ⟨0,0⟩)` are both hosted parts and have one closed form, and the manuscript's renaming rule does
not relate them; the second is not tame (`Corrected.alphaEq_not_alpha_with_code`). -/
theorem code_hosted_not_renamable :
    Hosted MeTTaCalculus.Corrected.boundContinuation ∧ Hosted MeTTaCalculus.Corrected.codeContinuation ∧
      AlphaEq MeTTaCalculus.Corrected.boundContinuation MeTTaCalculus.Corrected.codeContinuation ∧
      ¬ Alpha MeTTaCalculus.Corrected.boundContinuation MeTTaCalculus.Corrected.codeContinuation ∧
      tame MeTTaCalculus.Corrected.codeContinuation = false := by
  obtain ⟨same, notAlpha, -, notTame⟩ := MeTTaCalculus.Corrected.alphaEq_not_alpha_with_code
  exact ⟨⟨by decide +kernel, .inr ⟨.fvar "x", demoChan, .fvar "x", rfl, by decide +kernel, by decide +kernel,
    by decide +kernel⟩⟩, ⟨by decide +kernel, .inr ⟨.fvar "x", demoChan, codeValue, rfl, by decide +kernel,
    by decide +kernel, by decide +kernel⟩⟩, same, notAlpha, notTame⟩

/-! ## Shadowing: the convention within a part -/

/-- A receiver whose continuation binds its name again: `for(y <- @0)for(y <- @((0)))y`. -/
def shadowing : Pattern := pFor y demoChan (pFor y (nQuote zeroTerm) y)

/-- The manuscript's sender beside it. -/
def shadowingSource : Pattern := par sender shadowing

/-- The renamed receiver's name. -/
def renamedName : Pattern := .fvar (partName (pvars shadowingSource) 1 0 0)

/-- The renamed receiver's continuation: the inner input with its own new name. -/
def renamedInner : Pattern :=
  pFor (.fvar (partName (pvars shadowingSource) 1 1 0)) (nQuote zeroTerm)
    (.fvar (partName (pvars shadowingSource) 1 1 0))

/-- A ground term against a variable: binding the variable to the term is a ground principal unifier. -/
theorem ground_var_groundPrincipal (v : String) {g : Pattern} (ground : pvars g = []) :
    MeTTaOperationsComm.GroundPrincipal g (.fvar v) [(v, g)] := by
  have vars : pvars g ++ pvars (.fvar v) = [v] := by simp [ground, pvars]
  refine ⟨fun e member => ?_, fun x member => ?_, ?_, fun σ equation x member value found => ?_⟩
  · rw [vars, List.mem_singleton.mp member]
    exact List.mem_singleton_self v
  · rw [vars, List.mem_singleton] at member
    subst member
    exact ⟨g, FiniteProgram.NestedControls.lookup_single _ g, ground⟩
  · show psubst (Mettapedia.OSLF.MeTTaIL.Match.Bindings.lookup [(v, g)]) g =
      (Mettapedia.OSLF.MeTTaIL.Match.Bindings.lookup [(v, g)] v).getD (.fvar v)
    rw [FiniteProgram.NestedControls.lookup_single, Option.getD_some, psubst_of_pvars_nil _ g ground]
  · rw [vars, List.mem_singleton] at member
    subst member
    rw [FiniteProgram.NestedControls.lookup_single, Option.some.injEq] at found
    subst found
    exact equation.symm.trans (psubst_of_pvars_nil σ _ ground)

/-- **Control: shadowing.** In `for((0) <- @0)0 | for(y <- @0)for(y <- @((0)))y` the inner input binds the
receiver's name again: the redex breaks the variable convention within a part (`Corrected.Apart`), and the dot of
the continuation as written, `for(@((0)) <- @((0)))@((0))`, substitutes into the inner binder; it is not
alpha-equivalent to the corrected reduct `for(y <- @((0)))y`. After renaming apart, the two input parts satisfy the
convention (`apart_of_renameApart`), their patterns have a ground principal unifier, and the dot of the renamed
continuation leaves the inner input alone: it is alpha-equivalent to the corrected reduct. -/
theorem shadowing_renamed_apart :
    ¬ Apart zeroTerm pZero y (pFor y (nQuote zeroTerm) y) ∧
      applyDot unifier (pFor y (nQuote zeroTerm) y) = pFor (nQuote zeroTerm) (nQuote zeroTerm) (nQuote zeroTerm) ∧
      ¬ AlphaEq (pFor (nQuote zeroTerm) (nQuote zeroTerm) (nQuote zeroTerm)) (pFor y (nQuote zeroTerm) y) ∧
      Alpha shadowingSource (renameApart shadowingSource) ∧
      parts (renameApart shadowingSource) = [sender, pFor renamedName demoChan renamedInner] ∧
      Apart zeroTerm pZero renamedName renamedInner ∧
      MeTTaOperationsComm.GroundPrincipal zeroTerm renamedName [(partName (pvars shadowingSource) 1 0 0, zeroTerm)] ∧
      AlphaEq (applyDot [(partName (pvars shadowingSource) 1 0 0, zeroTerm)] renamedInner)
        (pFor y (nQuote zeroTerm) y) := by
  have tameP : tame shadowingSource = true := by decide +kernel
  have shape : parts (renameApart shadowingSource) = [sender, pFor renamedName demoChan renamedInner] := by
    decide +kernel
  have conventions := apart_of_renameApart shadowingSource tameP
  rw [shape, List.pairwise_pair] at conventions
  obtain ⟨apart, -⟩ := conventions zeroTerm demoChan pZero renamedName demoChan renamedInner rfl rfl
  exact ⟨fun apart' => apart'.rightKept "y" (by decide +kernel) (by decide +kernel), by decide +kernel,
    by decide +kernel, alpha_renameApart shadowingSource tameP, shape, apart,
    ground_var_groundPrincipal _ (by decide +kernel), by decide +kernel⟩

#print axioms corrected_step_reaches_a_code
#print axioms code_hosted_not_renamable
#print axioms ground_var_groundPrincipal
#print axioms shadowing_renamed_apart
#print axioms shared_hosted_parts
#print axioms shared_not_hostedProcess
#print axioms shared_communicates
#print axioms shared_third_row
#print axioms shared_literal_misreads
#print axioms shared_renamed_matched
#print axioms shared_fifth_clause
#print axioms code_breaks_alpha_respect
#print axioms corrected_step_breaks_convention
#print axioms renaming_by_names_fixes_free
#print axioms names_cannot_separate
#print axioms canonical_merges_siblings
#print axioms closed_forms_take_no_step

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.FiniteConvention.Controls
