import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalReaction
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.LexCanonical
import Mettapedia.Machines.ConstructorSummary

/-!
# Complete occurrence-sensitive COMM firings

A firing selects an input position and an output position after removing
that input. Equal messages at different positions retain different firing
addresses. The whole residue and semantic substitution result are retained,
and every public closed step has such a firing. The address space is finite
for each supplied source bag, even though the complete reaction family is
not a singleton or a finite list of ground rules.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalReactionOccurrences

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalStepperCompleteness
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefRewriteSystem
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalBag
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalReaction

/-- Exact source occurrences, the complete ground rule and both matches. -/
structure Firing (source : Bag) where
  inputIndex : Fin (ordered source.1).length
  outputIndex : Fin ((ordered source.1).eraseIdx inputIndex.val).length
  rule : GroundComm
  inputAt : (ordered source.1)[inputIndex.val] = input rule.inputChannel rule.body
  outputAt : ((ordered source.1).eraseIdx inputIndex.val)[outputIndex.val] =
    output rule.outputChannel rule.payload

namespace Firing

variable {source : Bag}

def tail (firing : Firing source) : List Pattern :=
  ((ordered source.1).eraseIdx firing.inputIndex.val).eraseIdx firing.outputIndex.val

theorem tail_primes (firing : Firing source) :
    ∀ pattern ∈ firing.tail, IsPrime pattern := by
  intro pattern membership
  exact ordered_prime source (mem_of_mem_eraseIdx_eraseIdx membership)

def residue (firing : Firing source) : Bag :=
  ⟨(firing.tail : Multiset Pattern), fun _ membership =>
    firing.tail_primes _ (by simpa using membership)⟩

def target (firing : Firing source) : Bag := append firing.rule.reactum firing.residue

theorem source_readout (firing : Firing source) :
    source = append firing.rule.redex firing.residue := by
  apply Subtype.ext
  have permutation : List.Perm (ordered source.1)
      (input firing.rule.inputChannel firing.rule.body ::
        output firing.rule.outputChannel firing.rule.payload :: firing.tail) := by
    have perm : List.Perm (ordered source.1)
        ((ordered source.1)[firing.inputIndex.val] ::
          ((ordered source.1).eraseIdx firing.inputIndex.val)[firing.outputIndex.val] ::
            firing.tail) :=
      ((List.getElem_cons_eraseIdx_perm firing.outputIndex.isLt).cons _ |>.trans
        (List.getElem_cons_eraseIdx_perm firing.inputIndex.isLt)).symm
    rwa [firing.inputAt, firing.outputAt] at perm
  rw [← ordered_multiset source.1]
  change (ordered source.1 : Multiset Pattern) =
    ([input firing.rule.inputChannel firing.rule.body,
      output firing.rule.outputChannel firing.rule.payload] : List Pattern) +
      (firing.tail : Multiset Pattern)
  rw [Multiset.coe_add]
  exact Multiset.coe_eq_coe.mpr permutation

theorem reaction (firing : Firing source) : Reaction source firing.target :=
  ⟨firing.rule, firing.residue, firing.source_readout, rfl⟩

theorem public_step (firing : Firing source) :
    rhoLanguageDefGSLT.Step (toProcess source) (toProcess firing.target) :=
  reaction_public firing.reaction

/-- The unnormalized endpoint retains the exact ordered unmatched occurrences. -/
def presentation (firing : Firing source) : RhoProcess :=
  ofList (firing.rule.result.1 :: firing.tail) (fun pattern membership => by
    rcases List.mem_cons.mp membership with rfl | membership
    · exact firing.rule.result.2
    · exact (firing.tail_primes pattern membership).1)

theorem presentation_inventory (firing : Firing source) :
    fromProcess firing.presentation = firing.target := by
  apply Subtype.ext
  unfold presentation
  rw [fromProcess_cons_primes firing.rule.result _ _ firing.tail_primes]
  rfl

theorem whole_target_readout (firing : Firing source) :
    toProcess firing.target = firing.presentation.canonicalize := by
  rw [← firing.presentation_inventory, toProcess_fromProcess]

theorem source_length (firing : Firing source) : 2 ≤ (ordered source.1).length := by
  have remaining := firing.outputIndex.isLt
  have removed := List.length_eraseIdx_add_one firing.inputIndex.isLt
  omega

/-- The unnormalized endpoint of the compiled firing: the compiled contractum
in front of the exact ordered unmatched occurrences. -/
def compiledPresentation (firing : Firing source) : RhoProcess :=
  ofList (firing.rule.compiledResult.1 :: firing.tail) (fun pattern membership => by
    rcases List.mem_cons.mp membership with rfl | membership
    · exact firing.rule.compiledResult.2
    · exact (firing.tail_primes pattern membership).1)

/-- The compiled endpoint is the presented endpoint up to the rho equations. -/
theorem compiledPresentation_equations (firing : Firing source) :
    rhoProcessEquations.r firing.compiledPresentation firing.presentation := by
  change canonicalize (.collection .hashBag (firing.rule.compiledResult.1 :: firing.tail) none) =
    canonicalize (.collection .hashBag (firing.rule.result.1 :: firing.tail) none)
  exact CanonicalStepperCompleteness.canonicalize_bag_cons_congr
    firing.rule.compiledResult_canonical (List.Perm.refl _)

/-- The compiled primitive step agrees at these exact occurrence positions. -/
theorem selected_step (firing : Firing source) :
    RhoStepAt 1 (toProcess source).1 firing.compiledPresentation.1 := by
  rw [toProcess_pattern, collapseBag_eq_bag_of_length_ge_two firing.source_length]
  have step := rhoStepAt_one_comm firing.inputIndex.isLt firing.outputIndex.isLt
    firing.inputAt firing.outputAt
    ((rhoCanonicalEquivalent_iff _ _).mpr firing.rule.channels)
  rw [apply_commBindingsAt_resolved firing.rule.body_typed firing.rule.payload_typed] at step
  exact step

def address (firing : Firing source) :
    Σ position : Fin (ordered source.1).length,
      Fin ((ordered source.1).eraseIdx position.val).length :=
  ⟨firing.inputIndex, firing.outputIndex⟩

end Firing

theorem groundComm_ext {first second : GroundComm}
    (inputEqual : input first.inputChannel first.body = input second.inputChannel second.body)
    (outputEqual : output first.outputChannel first.payload =
      output second.outputChannel second.payload) : first = second := by
  have inputFields : first.inputChannel = second.inputChannel ∧ first.body = second.body := by
    simpa [input] using inputEqual
  have outputFields : first.outputChannel = second.outputChannel ∧ first.payload = second.payload := by
    simpa [output] using outputEqual
  cases first
  cases second
  rcases inputFields with ⟨rfl, rfl⟩
  rcases outputFields with ⟨rfl, rfl⟩
  rfl

theorem Firing.address_injective (source : Bag) :
    Function.Injective (Firing.address (source := source)) := by
  intro first second equal
  cases first with
  | mk i j rule inputAt outputAt =>
    cases second with
    | mk i' j' rule' inputAt' outputAt' =>
      have indices : i = i' := congrArg Sigma.fst equal
      subst i'
      have outputs : j = j' := eq_of_heq (Sigma.mk.inj_iff.mp equal).2
      subst j'
      have rules : rule = rule' := groundComm_ext
        (inputAt.symm.trans inputAt') (outputAt.symm.trans outputAt')
      subst rule'
      rfl

instance (source : Bag) : Finite (Firing source) :=
  Finite.of_injective _ (Firing.address_injective source)

/-- Every independently authored reaction has actual selected occurrences. -/
theorem reaction_has_firing {source target : Bag} (reaction : Reaction source target) :
    ∃ firing : Firing source, firing.target = target := by
  obtain ⟨rule, residue, sourceEquation, targetEquation⟩ := reaction
  have permutation : List.Perm (ordered source.1)
      (input rule.inputChannel rule.body ::
        output rule.outputChannel rule.payload :: ordered residue.1) := by
    apply Multiset.coe_eq_coe.mp
    rw [ordered_multiset]
    change source.1 = ([input rule.inputChannel rule.body,
      output rule.outputChannel rule.payload] ++ ordered residue.1 : List Pattern)
    rw [← Multiset.coe_add, ordered_multiset]
    exact congrArg Subtype.val sourceEquation
  obtain ⟨i, iBound, j, jBound, inputAt, outputAt, tailPermutation⟩ := locate_pair permutation
  let firing : Firing source := ⟨⟨i, iBound⟩, ⟨j, jBound⟩, rule, inputAt, outputAt⟩
  have sameResidue : firing.residue = residue := by
    apply Subtype.ext
    change (((ordered source.1).eraseIdx i).eraseIdx j : Multiset Pattern) = residue.1
    rw [← ordered_multiset residue.1]
    exact Multiset.coe_eq_coe.mpr tailPermutation
  exact ⟨firing, by
    change append rule.reactum firing.residue = target
    rw [sameResidue, ← targetEquation]⟩

theorem reaction_iff_firing (source target : Bag) :
    Reaction source target ↔ ∃ firing : Firing source, firing.target = target := by
  constructor
  · exact reaction_has_firing
  · rintro ⟨firing, rfl⟩
    exact firing.reaction

/-- A fixed canonical source has finitely many complete result bags. This
does not identify firings that select different duplicate occurrences. -/
theorem reaction_targets_finite (source : Bag) :
    Set.Finite {target : Bag | Reaction source target} := by
  have targets : {target : Bag | Reaction source target} =
      Set.range (Firing.target (source := source)) := by
    ext target
    exact reaction_iff_firing source target
  rw [targets]
  exact Set.finite_range _

/-- Every public saturated closed step, with its precise endpoint, has an
occurrence-sensitive firing; conversely every supplied firing really executes. -/
theorem publicStep_iff_firing (source target : RhoProcess) :
    rhoLanguageDefGSLT.Step source target ↔
      ∃ firing : Firing (fromProcess source), firing.target = fromProcess target := by
  rw [publicStep_iff, reaction_iff_firing]


/-! ## Executable occurrence enumeration

The finite traversal is built from actual input and output-after-input-erasure
positions. Its recognizer checks constructor shapes and canonical channel
agreement. Closedness and prime premises come from the supplied bag; no
noncomputable enumeration of the Firing type is used.
-/

namespace Enumeration

abbrev Address (source : Bag) :=
  Σ input : Fin (ordered source.1).length,
    Fin ((ordered source.1).eraseIdx input.val).length

structure InputView (pattern : Pattern) where
  channel : Pattern
  body : Pattern
  shape : pattern = input channel body

structure OutputView (pattern : Pattern) where
  channel : Pattern
  payload : Pattern
  shape : pattern = output channel payload

def inputView : (pattern : Pattern) → Option (InputView pattern)
  | .apply "PInput" [channel, .lambda none body] => some ⟨channel, body, rfl⟩
  | _ => none

def outputView : (pattern : Pattern) → Option (OutputView pattern)
  | .apply "POutput" [channel, payload] => some ⟨channel, payload, rfl⟩
  | _ => none

@[simp] theorem inputView_input (channel body : Pattern) :
    inputView (input channel body) = some ⟨channel, body, rfl⟩ := rfl

@[simp] theorem outputView_output (channel payload : Pattern) :
    outputView (output channel payload) = some ⟨channel, payload, rfl⟩ := rfl

private theorem inputView_exists (pattern channel body : Pattern) (shape : pattern = input channel body) :
    ∃ parsed, inputView pattern = some parsed ∧ parsed.channel = channel ∧ parsed.body = body := by
  subst pattern
  exact ⟨⟨channel, body, rfl⟩, rfl, rfl, rfl⟩

private theorem outputView_exists (pattern channel payload : Pattern) (shape : pattern = output channel payload) :
    ∃ parsed, outputView pattern = some parsed ∧ parsed.channel = channel ∧ parsed.payload = payload := by
  subst pattern
  exact ⟨⟨channel, payload, rfl⟩, rfl, rfl, rfl⟩

def assemble (source : Bag) (address : Address source)
    (receiver : InputView ((ordered source.1)[address.1.val]))
    (sender : OutputView (((ordered source.1).eraseIdx address.1.val)[address.2.val])) : Option (Firing source) :=
  if channels : canonicalize receiver.channel = canonicalize sender.channel then
    let rule : GroundComm :=
      { inputChannel := receiver.channel, outputChannel := sender.channel,
        body := receiver.body, payload := sender.payload,
        inputPrime := by
          rw [← receiver.shape]
          exact ordered_prime source (List.getElem_mem address.1.isLt)
        outputPrime := by
          rw [← sender.shape]
          exact ordered_prime source (List.mem_of_mem_eraseIdx (List.getElem_mem address.2.isLt))
        channels := channels }
    some ⟨address.1, address.2, rule, receiver.shape, sender.shape⟩
  else none

def recognize (source : Bag) (address : Address source) : Option (Firing source) :=
  (inputView ((ordered source.1)[address.1.val])).bind fun receiver =>
    (outputView (((ordered source.1).eraseIdx address.1.val)[address.2.val])).bind fun sender =>
      assemble source address receiver sender

theorem recognized_address (source : Bag) (address : Address source) (firing : Firing source)
    (accepted : recognize source address = some firing) : firing.address = address := by
  obtain ⟨receiver, _, afterInput⟩ := Option.bind_eq_some_iff.mp accepted
  obtain ⟨sender, _, afterOutput⟩ := Option.bind_eq_some_iff.mp afterInput
  unfold assemble at afterOutput
  split at afterOutput
  · cases Option.some.inj afterOutput
    rfl
  · cases afterOutput

/-- Every independently supplied firing is recognized at its own address.
Address injectivity identifies the checked witness; no target is guessed from
an already computed successor. -/
theorem recognize_firing (source : Bag) (firing : Firing source) :
    recognize source firing.address = some firing := by
  have present : (recognize source firing.address).isSome = true := by
    rcases firing with ⟨i, j, rule, inputAt, outputAt⟩
    obtain ⟨receiver, inputParsed, inputChannel, _⟩ := inputView_exists _ _ _ inputAt
    obtain ⟨sender, outputParsed, outputChannel, _⟩ := outputView_exists _ _ _ outputAt
    have channels : canonicalize receiver.channel = canonicalize sender.channel := by
      rw [inputChannel, outputChannel]
      exact rule.channels
    simp only [recognize, Firing.address, inputParsed, outputParsed, Option.bind_some, assemble,
      dif_pos channels, Option.isSome_some]
  cases accepted : recognize source firing.address with
  | none => simp only [accepted, Option.isSome_none, Bool.false_eq_true] at present
  | some selected =>
      have same := Firing.address_injective source (recognized_address source firing.address selected accepted)
      exact congrArg some same

theorem recognized_iff_firing_at_address (source : Bag) (address : Address source) :
    (recognize source address).isSome = true ↔ ∃ firing : Firing source, firing.address = address := by
  constructor
  · intro present
    cases accepted : recognize source address with
    | none => simp only [accepted, Option.isSome_none, Bool.false_eq_true] at present
    | some firing => exact ⟨firing, recognized_address source address firing accepted⟩
  · rintro ⟨firing, rfl⟩
    rw [recognize_firing]
    rfl

theorem recognize_eq_some_iff (source : Bag) (address : Address source) (firing : Firing source) :
    recognize source address = some firing ↔ firing.address = address := by
  constructor
  · exact recognized_address source address firing
  · intro same
    rw [← same, recognize_firing]

instance firingDecidableEq (source : Bag) : DecidableEq (Firing source) := fun first second =>
  if same : first.address = second.address then
    .isTrue (Firing.address_injective source same)
  else .isFalse (fun equal => same (congrArg Firing.address equal))

/-- The outer position is traversed first, then every position in its exact
post-erasure tail. Equal messages are retained at their different positions. -/
def addresses (source : Bag) : List (Address source) :=
  (List.finRange (ordered source.1).length).sigma fun i =>
    List.finRange ((ordered source.1).eraseIdx i.val).length

theorem mem_addresses (source : Bag) (address : Address source) : address ∈ addresses source := by
  rcases address with ⟨i, j⟩
  exact List.mem_flatMap.mpr ⟨i, List.mem_finRange _, List.mem_map.mpr ⟨j, List.mem_finRange _, rfl⟩⟩

theorem addresses_nodup (source : Bag) : (addresses source).Nodup :=
  (List.nodup_finRange _).sigma (fun _ => List.nodup_finRange _)

def firings (source : Bag) : List (Firing source) :=
  (addresses source).filterMap (recognize source)

theorem mem_firings (source : Bag) (firing : Firing source) : firing ∈ firings source :=
  List.mem_filterMap.mpr ⟨firing.address, mem_addresses source firing.address, recognize_firing source firing⟩

theorem firings_nodup (source : Bag) : (firings source).Nodup := by
  apply List.Nodup.filterMap (f := recognize source) ?_ (addresses_nodup source)
  intro first second firing firstAccepted secondAccepted
  exact (recognized_address source first firing (Option.mem_def.mp firstAccepted)).symm.trans
    (recognized_address source second firing (Option.mem_def.mp secondAccepted))

/-- Every enumerated object already carries the original source occurrence,
whole residue, and semantic COMM rule, and therefore executes a public step. -/
theorem enumerated_public_step (source : Bag) (firing : Firing source)
    (_member : firing ∈ firings source) :
    rhoLanguageDefGSLT.Step (toProcess source) (toProcess firing.target) := firing.public_step

/-- Source-kernel coverage follows from the existing independent closed COMM
family and the constructive address traversal, not an assumed coverage law. -/
theorem publicStep_iff_enumerated (source target : RhoProcess) :
    rhoLanguageDefGSLT.Step source target ↔
      ∃ firing ∈ firings (fromProcess source), firing.target = fromProcess target := by
  rw [publicStep_iff_firing]
  exact ⟨fun ⟨firing, target⟩ => ⟨firing, mem_firings _ firing, target⟩,
    fun ⟨firing, _, target⟩ => ⟨firing, target⟩⟩


/-- An empty checked candidate stream means actual closed-COMM quiescence.
Failure or unfinished native enumeration is not represented by this equation. -/
theorem firings_eq_nil_iff_no_public_step (source : Bag) :
    firings source = [] ↔ ¬ ∃ target : RhoProcess, rhoLanguageDefGSLT.Step (toProcess source) target := by
  constructor
  · intro empty ⟨target, step⟩
    obtain ⟨firing, member, _⟩ := (publicStep_iff_enumerated _ _).mp step
    have nonempty := List.length_pos_of_mem member
    have emptyLength : (firings (fromProcess (toProcess source))).length = 0 := by
      rw [fromProcess_toProcess, empty]
      rfl
    omega
  · intro quiescent
    cases listed : firings source with
    | nil => rfl
    | cons firing rest => exact (quiescent ⟨toProcess firing.target, firing.public_step⟩).elim

end Enumeration

/-! ## Full-source endpoint coordinates

These coordinates refer to the declared ordered source inventory. They do
not specify a native normalization order, wire format or persistent-message
extension. Converting an address does not merge equal source occurrences.
-/

namespace FullSource

/-- Both selected endpoints are positions in the complete source. -/
structure Address (source : Bag) where
  inputIndex : Fin (ordered source.1).length
  outputIndex : Fin (ordered source.1).length
  distinct : inputIndex.val ≠ outputIndex.val
  deriving DecidableEq

@[ext] theorem Address.ext {source : Bag} {first second : Address source}
    (inputs : first.inputIndex = second.inputIndex)
    (outputs : first.outputIndex = second.outputIndex) : first = second := by
  cases first
  cases second
  cases inputs
  cases outputs
  rfl

/-- Insert the removed input position back before the selected output. -/
def Address.ofErased {source : Bag} (address : Enumeration.Address source) : Address source where
  inputIndex := address.1
  outputIndex := ⟨if address.2.val < address.1.val then address.2.val else address.2.val + 1, by
    have remaining := address.2.isLt
    have removed := List.length_eraseIdx_add_one address.1.isLt
    split_ifs <;> omega⟩
  distinct := by
    change address.1.val ≠ if address.2.val < address.1.val then address.2.val else address.2.val + 1
    split_ifs <;> omega

/-- Remove the selected input position before indexing the selected output. -/
def Address.toErased {source : Bag} (address : Address source) : Enumeration.Address source :=
  ⟨address.inputIndex, ⟨if address.outputIndex.val < address.inputIndex.val then
      address.outputIndex.val else address.outputIndex.val - 1, by
    have inputBound := address.inputIndex.isLt
    have outputBound := address.outputIndex.isLt
    have different := address.distinct
    have removed := List.length_eraseIdx_add_one address.inputIndex.isLt
    split_ifs <;> omega⟩⟩

@[simp] theorem Address.toErased_ofErased {source : Bag} (address : Enumeration.Address source) :
    (Address.ofErased address).toErased = address := by
  apply Sigma.ext
  · rfl
  apply heq_of_eq
  apply Fin.ext
  simp only [Address.toErased, Address.ofErased]
  split_ifs <;> omega

@[simp] theorem Address.ofErased_toErased {source : Bag} (address : Address source) :
    Address.ofErased address.toErased = address := by
  apply Address.ext (first := Address.ofErased address.toErased) (second := address)
  · rfl
  apply Fin.ext
  have different := address.distinct
  simp only [Address.ofErased, Address.toErased]
  split_ifs <;> omega

/-- Coordinate conversion is a bijection, including duplicate source values. -/
def addressEquiv (source : Bag) : Enumeration.Address source ≃ Address source where
  toFun := Address.ofErased
  invFun := Address.toErased
  left_inv := Address.toErased_ofErased
  right_inv := Address.ofErased_toErased

theorem Address.outputAt_ofErased {source : Bag} (address : Enumeration.Address source) :
    ((ordered source.1).eraseIdx address.1.val)[address.2.val] =
      (ordered source.1)[(Address.ofErased address).outputIndex.val] := by
  have bound : (if address.2.val < address.1.val then address.2.val else address.2.val + 1) <
      (ordered source.1).length := (Address.ofErased address).outputIndex.isLt
  change _ = (ordered source.1)[if address.2.val < address.1.val then
    address.2.val else address.2.val + 1]'bound
  split_ifs with before
  · exact List.getElem_eraseIdx_of_lt address.2.isLt before
  · exact List.getElem_eraseIdx_of_ge address.2.isLt (Nat.le_of_not_gt before)

theorem Address.outputAt_toErased {source : Bag} (address : Address source) :
    ((ordered source.1).eraseIdx address.inputIndex.val)[address.toErased.2.val] =
      (ordered source.1)[address.outputIndex.val] := by
  have indices := congrArg Address.outputIndex (Address.ofErased_toErased address)
  have values := congrArg
    (fun index : Fin (ordered source.1).length => (ordered source.1)[index.val]'index.isLt) indices
  simpa only [Address.toErased] using (Address.outputAt_ofErased address.toErased).trans values

/-- Remove endpoints from the full inventory in descending position order. -/
def Address.tail {source : Bag} (address : Address source) : List Pattern :=
  ((ordered source.1).eraseIdx (max address.inputIndex.val address.outputIndex.val)).eraseIdx
    (min address.inputIndex.val address.outputIndex.val)

private theorem eraseIdx_swap {α : Type*} (items : List α) (first second : Nat)
    (ordered : first ≤ second) :
    (items.eraseIdx first).eraseIdx second = (items.eraseIdx (second + 1)).eraseIdx first := by
  induction items generalizing first second with
  | nil => simp
  | cons head rest induction =>
    cases first with
    | zero => simp
    | succ first =>
      cases second with
      | zero => omega
      | succ second =>
        simpa using congrArg (List.cons head) (induction first second (by omega))

theorem Address.tail_ofErased {source : Bag} (address : Enumeration.Address source) :
    (Address.ofErased address).tail =
      ((ordered source.1).eraseIdx address.1.val).eraseIdx address.2.val := by
  unfold Address.tail Address.ofErased
  dsimp only
  split_ifs with before
  · rw [Nat.max_eq_left (by omega), Nat.min_eq_right (by omega)]
  · rw [Nat.max_eq_right (by omega), Nat.min_eq_left (by omega)]
    exact (eraseIdx_swap _ _ _ (Nat.le_of_not_gt before)).symm


/-- Bounds and distinctness are checked before constructor/channel recognition. -/
def checkAddress (source : Bag) (inputPosition outputPosition : Nat) : Option (Address source) :=
  if inputBound : inputPosition < (ordered source.1).length then
    if outputBound : outputPosition < (ordered source.1).length then
      if distinct : inputPosition ≠ outputPosition then
        some ⟨⟨inputPosition, inputBound⟩, ⟨outputPosition, outputBound⟩, distinct⟩
      else none
    else none
  else none

theorem checkAddress_eq_some_iff (source : Bag) (inputPosition outputPosition : Nat)
    (address : Address source) :
    checkAddress source inputPosition outputPosition = some address ↔
      address.inputIndex.val = inputPosition ∧ address.outputIndex.val = outputPosition := by
  unfold checkAddress
  split_ifs with inputBound outputBound distinct
  · constructor
    · intro same
      have equal := Option.some.inj same
      exact ⟨(congrArg (fun selected => selected.inputIndex.val) equal).symm,
        (congrArg (fun selected => selected.outputIndex.val) equal).symm⟩
    · rintro ⟨inputs, outputs⟩
      congr 1
      apply Address.ext <;> apply Fin.ext
      · exact inputs.symm
      · exact outputs.symm
  · simp only [false_iff]
    intro positions
    have different := address.distinct
    omega
  · simp only [false_iff]
    intro positions
    have bound := address.outputIndex.isLt
    omega
  · simp only [false_iff]
    intro positions
    have bound := address.inputIndex.isLt
    omega

@[simp] theorem checkAddress_address {source : Bag} (address : Address source) :
    checkAddress source address.inputIndex.val address.outputIndex.val = some address :=
  (checkAddress_eq_some_iff _ _ _ _).mpr ⟨rfl, rfl⟩

@[simp] theorem checkAddress_same (source : Bag) (position : Nat) :
    checkAddress source position position = none := by
  simp [checkAddress]

theorem checkAddress_input_out_of_range (source : Bag) (inputPosition outputPosition : Nat)
    (outside : (ordered source.1).length ≤ inputPosition) :
    checkAddress source inputPosition outputPosition = none := by
  simp [checkAddress, Nat.not_lt.mpr outside]

theorem checkAddress_output_out_of_range (source : Bag) (inputPosition outputPosition : Nat)
    (outside : (ordered source.1).length ≤ outputPosition) :
    checkAddress source inputPosition outputPosition = none := by
  simp [checkAddress, Nat.not_lt.mpr outside]

end FullSource

namespace Firing

variable {source : Bag}

/-- The same selected occurrences, both in the complete declared inventory. -/
def fullAddress (firing : Firing source) : FullSource.Address source :=
  FullSource.Address.ofErased firing.address

@[simp] theorem toErased_fullAddress (firing : Firing source) :
    firing.fullAddress.toErased = firing.address :=
  FullSource.Address.toErased_ofErased firing.address

theorem fullAddress_injective (source : Bag) :
    Function.Injective (Firing.fullAddress (source := source)) := by
  intro first second same
  apply address_injective source
  have equal := congrArg FullSource.Address.toErased same
  simpa only [toErased_fullAddress] using equal

theorem inputAt_fullAddress (firing : Firing source) :
    (ordered source.1)[firing.fullAddress.inputIndex.val] =
      input firing.rule.inputChannel firing.rule.body := firing.inputAt

theorem outputAt_fullAddress (firing : Firing source) :
    (ordered source.1)[firing.fullAddress.outputIndex.val] =
      output firing.rule.outputChannel firing.rule.payload :=
  (FullSource.Address.outputAt_ofErased firing.address).symm.trans firing.outputAt

/-- Full-source erasure preserves the entire ordered unmatched inventory. -/
theorem fullAddress_tail (firing : Firing source) : firing.fullAddress.tail = firing.tail :=
  FullSource.Address.tail_ofErased firing.address

theorem residue_fullAddress (firing : Firing source) :
    firing.residue.1 = (firing.fullAddress.tail : Multiset Pattern) := by
  rw [fullAddress_tail]
  rfl

/-- A fully matched ground rule at full-source endpoints yields the existing
firing, not a new reaction semantics. -/
def ofFullSource (address : FullSource.Address source) (rule : GroundComm)
    (inputAt : (ordered source.1)[address.inputIndex.val] = input rule.inputChannel rule.body)
    (outputAt : (ordered source.1)[address.outputIndex.val] = output rule.outputChannel rule.payload) :
    Firing source where
  inputIndex := address.inputIndex
  outputIndex := address.toErased.2
  rule := rule
  inputAt := inputAt
  outputAt := address.outputAt_toErased.trans outputAt

@[simp] theorem fullAddress_ofFullSource (address : FullSource.Address source) (rule : GroundComm)
    (inputAt : (ordered source.1)[address.inputIndex.val] = input rule.inputChannel rule.body)
    (outputAt : (ordered source.1)[address.outputIndex.val] = output rule.outputChannel rule.payload) :
    (ofFullSource address rule inputAt outputAt).fullAddress = address :=
  FullSource.Address.ofErased_toErased address

end Firing

namespace FullSource

/-- Recognize the exact same ground COMM rule via inverse coordinate transport. -/
def recognize (source : Bag) (address : Address source) : Option (Firing source) :=
  Enumeration.recognize source address.toErased

theorem recognize_eq_some_iff (source : Bag) (address : Address source) (firing : Firing source) :
    recognize source address = some firing ↔ firing.fullAddress = address := by
  rw [recognize, Enumeration.recognize_eq_some_iff]
  constructor
  · intro same
    have equal := congrArg Address.ofErased same
    simpa only [Firing.fullAddress, Address.ofErased_toErased] using equal
  · intro same
    have equal := congrArg Address.toErased same
    simpa only [Firing.toErased_fullAddress] using equal

@[simp] theorem recognize_firing (source : Bag) (firing : Firing source) :
    recognize source firing.fullAddress = some firing :=
  (recognize_eq_some_iff source _ firing).mpr rfl

/-- Accepted full-source addresses correspond to actual firings, not
just geometrically well-formed pairs of positions. -/
theorem recognize_get_fullAddress (source : Bag) (address : Address source)
    (accepted : (recognize source address).isSome) :
    ((recognize source address).get accepted).fullAddress = address :=
  (recognize_eq_some_iff source address _).mp (Option.some_get accepted).symm

/-- The partial recognizer gives a constructive bijection with its accepted
addresses. Repeated equal messages remain distinct members of this type. -/
def firingEquiv (source : Bag) : Firing source ≃
    {address : Address source // (recognize source address).isSome} where
  toFun firing := ⟨firing.fullAddress, by rw [recognize_firing]; rfl⟩
  invFun accepted := (recognize source accepted.1).get accepted.2
  left_inv firing := Firing.fullAddress_injective source
    (recognize_get_fullAddress source firing.fullAddress _)
  right_inv accepted := Subtype.ext (recognize_get_fullAddress source accepted.1 accepted.2)

/-- Raw full-source endpoint decoder; malformed coordinates are rejected
before the existing constructor and canonical-channel checks run. -/
def decode (source : Bag) (inputPosition outputPosition : Nat) : Option (Firing source) :=
  (checkAddress source inputPosition outputPosition).bind (recognize source)

theorem decode_eq_some_iff (source : Bag) (inputPosition outputPosition : Nat)
    (firing : Firing source) :
    decode source inputPosition outputPosition = some firing ↔
      firing.fullAddress.inputIndex.val = inputPosition ∧
        firing.fullAddress.outputIndex.val = outputPosition := by
  rw [decode, Option.bind_eq_some_iff]
  constructor
  · rintro ⟨address, checked, recognized⟩
    have same := (recognize_eq_some_iff source address firing).mp recognized
    subst address
    exact (checkAddress_eq_some_iff _ _ _ _).mp checked
  · intro positions
    exact ⟨firing.fullAddress, (checkAddress_eq_some_iff _ _ _ _).mpr positions,
      recognize_firing source firing⟩

/-- Accepted raw endpoints are both in bounds and physically distinct. -/
theorem decoded_bounds_distinct (source : Bag) (inputPosition outputPosition : Nat)
    (firing : Firing source) (decoded : decode source inputPosition outputPosition = some firing) :
    inputPosition < (ordered source.1).length ∧ outputPosition < (ordered source.1).length ∧
      inputPosition ≠ outputPosition := by
  rcases (decode_eq_some_iff source _ _ firing).mp decoded with ⟨rfl, rfl⟩
  exact ⟨firing.fullAddress.inputIndex.isLt, firing.fullAddress.outputIndex.isLt,
    firing.fullAddress.distinct⟩

/-- Rejection describes absence of a firing at these exact positions in the
closed strict-core source. It is not a native allocation/unfinished status. -/
theorem decode_eq_none_iff (source : Bag) (inputPosition outputPosition : Nat) :
    decode source inputPosition outputPosition = none ↔
      ¬ ∃ firing : Firing source, firing.fullAddress.inputIndex.val = inputPosition ∧
        firing.fullAddress.outputIndex.val = outputPosition := by
  constructor
  · intro rejected ⟨firing, positions⟩
    have accepted := (decode_eq_some_iff source _ _ firing).mpr positions
    rw [rejected] at accepted
    contradiction
  · intro absent
    cases decoded : decode source inputPosition outputPosition with
    | none => rfl
    | some firing => exact (absent ⟨firing, (decode_eq_some_iff source _ _ firing).mp decoded⟩).elim

@[simp] theorem decode_firing (source : Bag) (firing : Firing source) :
    decode source firing.fullAddress.inputIndex.val firing.fullAddress.outputIndex.val = some firing :=
  (decode_eq_some_iff source _ _ firing).mpr ⟨rfl, rfl⟩

@[simp] theorem decode_same (source : Bag) (position : Nat) :
    decode source position position = none := by
  simp [decode]

theorem decode_input_out_of_range (source : Bag) (inputPosition outputPosition : Nat)
    (outside : (ordered source.1).length ≤ inputPosition) :
    decode source inputPosition outputPosition = none := by
  rw [decode, checkAddress_input_out_of_range source _ _ outside]
  rfl

theorem decode_output_out_of_range (source : Bag) (inputPosition outputPosition : Nat)
    (outside : (ordered source.1).length ≤ outputPosition) :
    decode source inputPosition outputPosition = none := by
  rw [decode, checkAddress_output_out_of_range source _ _ outside]
  rfl

/-- Reversing the input and output of an actual firing fails constructor
recognition; distinct positions alone are not a COMM permission. -/
theorem decode_swapped_firing (source : Bag) (firing : Firing source) :
    decode source firing.fullAddress.outputIndex.val firing.fullAddress.inputIndex.val = none := by
  cases decoded : decode source firing.fullAddress.outputIndex.val firing.fullAddress.inputIndex.val with
  | none => rfl
  | some other =>
    have positions := (decode_eq_some_iff source _ _ other).mp decoded
    have sameIndex : other.fullAddress.inputIndex = firing.fullAddress.outputIndex :=
      Fin.ext positions.1
    have sameValue := congrArg
      (fun index : Fin (ordered source.1).length => (ordered source.1)[index.val]'index.isLt) sameIndex
    have clash := firing.outputAt_fullAddress.symm.trans
      (sameValue.symm.trans other.inputAt_fullAddress)
    simp [input, output] at clash

/-- Known full-source matches roundtrip through the executable recognizer,
including the actual ground rule and all its substitution data. -/
theorem decode_matches (source : Bag) (address : Address source) (rule : GroundComm)
    (inputAt : (ordered source.1)[address.inputIndex.val] = input rule.inputChannel rule.body)
    (outputAt : (ordered source.1)[address.outputIndex.val] = output rule.outputChannel rule.payload) :
    decode source address.inputIndex.val address.outputIndex.val =
      some (Firing.ofFullSource address rule inputAt outputAt) := by
  apply (decode_eq_some_iff source _ _ _).mpr
  rw [Firing.fullAddress_ofFullSource]
  exact ⟨rfl, rfl⟩

/-- Decoding cannot change the selected semantic ground rule. -/
theorem decode_matches_rule (source : Bag) (address : Address source) (rule : GroundComm)
    (inputAt : (ordered source.1)[address.inputIndex.val] = input rule.inputChannel rule.body)
    (outputAt : (ordered source.1)[address.outputIndex.val] = output rule.outputChannel rule.payload) :
    (decode source address.inputIndex.val address.outputIndex.val).map Firing.rule = some rule := by
  rw [decode_matches source address rule inputAt outputAt]
  rfl

/-- Both coordinates and the complete ordered residue are preserved. -/
theorem decode_matches_residue (source : Bag) (address : Address source) (rule : GroundComm)
    (inputAt : (ordered source.1)[address.inputIndex.val] = input rule.inputChannel rule.body)
    (outputAt : (ordered source.1)[address.outputIndex.val] = output rule.outputChannel rule.payload) :
    (decode source address.inputIndex.val address.outputIndex.val).map (fun firing => firing.residue.1) =
      some (address.tail : Multiset Pattern) := by
  rw [decode_matches source address rule inputAt outputAt]
  change some (Firing.ofFullSource address rule inputAt outputAt).residue.1 = _
  rw [Firing.residue_fullAddress, Firing.fullAddress_ofFullSource]

/-- The unnormalized target retains the whole reactum and unmatched inventory. -/
theorem decode_matches_target (source : Bag) (address : Address source) (rule : GroundComm)
    (inputAt : (ordered source.1)[address.inputIndex.val] = input rule.inputChannel rule.body)
    (outputAt : (ordered source.1)[address.outputIndex.val] = output rule.outputChannel rule.payload) :
    (decode source address.inputIndex.val address.outputIndex.val).map (fun firing => firing.target.1) =
      some (rule.reactum.1 + (address.tail : Multiset Pattern)) := by
  rw [decode_matches source address rule inputAt outputAt]
  change some (rule.reactum.1 + (Firing.ofFullSource address rule inputAt outputAt).residue.1) = _
  rw [Firing.residue_fullAddress, Firing.fullAddress_ofFullSource]

/-- An accepted raw address always produces a genuine source-kernel step. -/
theorem decoded_public_step (source : Bag) (inputPosition outputPosition : Nat) (firing : Firing source)
    (_decoded : decode source inputPosition outputPosition = some firing) :
    rhoLanguageDefGSLT.Step (toProcess source) (toProcess firing.target) := firing.public_step

/-- Every public step has a checked full-source endpoint address, and the
checked decoder invents no endpoint or unmatched occurrence. -/
theorem publicStep_iff_decoded (source target : RhoProcess) :
    rhoLanguageDefGSLT.Step source target ↔
      ∃ inputPosition outputPosition, ∃ firing : Firing (fromProcess source),
        decode (fromProcess source) inputPosition outputPosition = some firing ∧
          firing.target = fromProcess target := by
  rw [publicStep_iff_firing]
  constructor
  · rintro ⟨firing, target⟩
    exact ⟨firing.fullAddress.inputIndex.val, firing.fullAddress.outputIndex.val,
      firing, decode_firing _ firing, target⟩
  · rintro ⟨_, _, firing, _, target⟩
    exact ⟨firing, target⟩

end FullSource

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalReactionOccurrences

/-! ## Prepared reaction rows and occurrence inventory

Completed keys observe the actual occurrence rows below. A reference stable
merge preserves every row and reconstructs the existing `Firing.target`, which
uses the semantic substitution result. The reference merge assumes prepared
rows; retained contextual key merge, native sorting/copying/retirement and the
native persistent-receive extension are separate obligations.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalReactionOccurrences.RetainedInventory

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalBag
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalReaction
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LexCanonical.RetainedKey

/-- A completed reset key is an observation attached to an actual occurrence.
Equal keys, products or syntax values do not identify its ordinal. -/
structure Row where
  value : Pattern
  product : Product
  ordinal : Nat
  deriving DecidableEq, Repr

/-- Completed-key reference order. The base side precedes the body side on ties. -/
def before (left right : Row) : Bool :=
  !(Compare.reference left.product.bytes right.product.bytes == .gt)

/-- Reference merge of already prepared rows. This does not implement native
contextual key preparation, sorting, storage or its retained control states. -/
def merge (base body : List Row) : List Row := List.merge base body before

theorem merge_perm (base body : List Row) : (merge base body).Perm (base ++ body) :=
  List.merge_perm_append before

theorem merge_length (base body : List Row) :
    (merge base body).length = base.length + body.length := by
  exact (merge_perm base body).length_eq.trans List.length_append

theorem merge_value_perm (base body : List Row) :
    ((merge base body).map Row.value).Perm (base.map Row.value ++ body.map Row.value) := by
  simpa only [List.map_append] using (merge_perm base body).map Row.value

theorem merge_ordinal_perm (base body : List Row) :
    ((merge base body).map Row.ordinal).Perm (base.map Row.ordinal ++ body.map Row.ordinal) := by
  simpa only [List.map_append] using (merge_perm base body).map Row.ordinal

theorem equal_key_keeps_base (left right : Row) (base body : List Row)
    (same : left.product.bytes = right.product.bytes) :
    merge (left :: base) (right :: body) = left :: merge base (right :: body) := by
  have reflexive : Compare.reference right.product.bytes right.product.bytes = .eq := by
    simp [Compare.reference]
  simp [merge, before, same, reflexive]

theorem all_ties_keep_original_spines (base body : List Row)
    (same : ∀ left ∈ base, ∀ right ∈ body, left.product.bytes = right.product.bytes) :
    merge base body = base ++ body := by
  apply List.merge_of_le
  intro left right leftMem rightMem
  have reflexive : Compare.reference right.product.bytes right.product.bytes = .eq := by
    simp [Compare.reference]
  simp [before, same left leftMem right rightMem, reflexive]

/-- The reaction inventory consists of every unmatched source occurrence and
all canonical components of the actual semantic substitution result. -/
def spine {source : Bag} (firing : Firing source) : List Pattern :=
  firing.tail ++ contents firing.rule.result

theorem spine_primes {source : Bag} (firing : Firing source) :
    ∀ pattern ∈ spine firing, IsPrime pattern := by
  intro pattern membership
  rcases List.mem_append.mp membership with remaining | produced
  · exact firing.tail_primes _ remaining
  · exact contents_prime _ produced

theorem spine_target {source : Bag} (firing : Firing source) :
    (spine firing : Multiset Pattern) = firing.target.1 := by
  change ((firing.tail ++ contents firing.rule.result : List Pattern) : Multiset Pattern) =
    (contents firing.rule.result : Multiset Pattern) + (firing.tail : Multiset Pattern)
  simpa only [Multiset.coe_add] using
    add_comm (firing.tail : Multiset Pattern) (contents firing.rule.result : Multiset Pattern)

theorem prepared_values_target {source : Bag} (firing : Firing source) (base body : List Row)
    (baseValues : base.map Row.value = firing.tail)
    (bodyValues : body.map Row.value = contents firing.rule.result) :
    ((merge base body).map Row.value : Multiset Pattern) = firing.target.1 := by
  calc
    _ = (base.map Row.value ++ body.map Row.value : Multiset Pattern) :=
      Multiset.coe_eq_coe.mpr (merge_value_perm base body)
    _ = (spine firing : Multiset Pattern) := by rw [baseValues, bodyValues]; rfl
    _ = _ := spine_target firing

theorem prepared_primes {source : Bag} (firing : Firing source) (base body : List Row)
    (baseValues : base.map Row.value = firing.tail)
    (bodyValues : body.map Row.value = contents firing.rule.result) :
    ∀ pattern ∈ (merge base body).map Row.value, IsPrime pattern := by
  intro pattern membership
  apply spine_primes firing pattern
  have original := (merge_value_perm base body).mem_iff.mp membership
  simpa only [baseValues, bodyValues, spine] using original

def candidate {source : Bag} (firing : Firing source) (base body : List Row)
    (baseValues : base.map Row.value = firing.tail)
    (bodyValues : body.map Row.value = contents firing.rule.result) : RhoProcess :=
  ofList ((merge base body).map Row.value)
    (fun pattern membership => (prepared_primes firing base body baseValues bodyValues pattern membership).1)

theorem candidate_inventory {source : Bag} (firing : Firing source) (base body : List Row)
    (baseValues : base.map Row.value = firing.tail)
    (bodyValues : body.map Row.value = contents firing.rule.result) :
    fromProcess (candidate firing base body baseValues bodyValues) = firing.target := by
  apply Subtype.ext
  unfold candidate
  rw [fromProcess_ofList_primes _ (prepared_primes firing base body baseValues bodyValues)]
  exact prepared_values_target firing base body baseValues bodyValues

theorem candidate_readout {source : Bag} (firing : Firing source) (base body : List Row)
    (baseValues : base.map Row.value = firing.tail)
    (bodyValues : body.map Row.value = contents firing.rule.result) :
    (candidate firing base body baseValues bodyValues).canonicalize = toProcess firing.target := by
  rw [← candidate_inventory firing base body baseValues bodyValues, toProcess_fromProcess]

theorem candidate_public_step {source : Bag} (firing : Firing source) (base body : List Row)
    (baseValues : base.map Row.value = firing.tail)
    (bodyValues : body.map Row.value = contents firing.rule.result) :
    rhoLanguageDefGSLT.Step (toProcess source)
      (candidate firing base body baseValues bodyValues).canonicalize := by
  rw [candidate_readout]
  exact firing.public_step

namespace Controls

private def row (ordinal : Nat) : Row :=
  ⟨.apply "POutput" [.apply "NQuote" [.apply "PZero" []], .apply "PZero" []], ⟨[112], 0, 0⟩, ordinal⟩

theorem equal_shared_values_keep_both_occurrences :
    row 3 ≠ row 8 ∧ (row 3).value = (row 8).value ∧
      (merge [row 3] [row 8]).map Row.ordinal = [3, 8] := by
  simp [merge, before, Compare.reference, List.compareLex, row]

theorem key_equality_cannot_justify_deduplication :
    (merge [row 3, row 8] [row 13]).length = 3 ∧
      (merge [row 3, row 8] [row 13]).map Row.value ≠ [(row 3).value] := by
  simp [merge, before, Compare.reference, List.compareLex, row]

theorem reversed_tie_policy_changes_actual_inventory_order :
    merge [row 3] [row 8] ≠ merge [row 8] [row 3] ∧
      (merge [row 3] [row 8]).map Row.value = (merge [row 8] [row 3]).map Row.value := by
  simp [merge, before, Compare.reference, List.compareLex, row]

theorem body_order_on_ties_is_not_reconstructed_from_keys :
    (merge [row 3] [row 8, row 13]).map Row.ordinal = [3, 8, 13] ∧
      (merge [row 3] [row 13, row 8]).map Row.ordinal = [3, 13, 8] := by
  simp [merge, before, Compare.reference, List.compareLex, row]

end Controls

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalReactionOccurrences.RetainedInventory

/-! ## Retained completed-key merge and constructor composition

The producer below retains the existing byte comparator's actual packet and
emits one prepared occurrence row at a time. Its `Cursor.Fold` client appends
that row immediately to the existing constructor assembly. The independent
`List.merge` reference occurs in the representation laws, not the producer.

Completed products have exact ordered children, summary, ordinal/value
inventory and the existing pure-COMM target/public-step readout. Zero, split
and cancellation laws preserve the same representation and declared bill.
The currency counts producer polls; it is not native instructions, byte prices
or a C control-state account. Native copy-origin/ordinal decoding, ownership,
allocation/finalizers, service prices and progress bounds remain separate
obligations. No all-input termination or compiled-C refinement is inferred.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalReactionOccurrences.RetainedInventory.Cursor

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Machines
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LexCanonical.RetainedKey
open _root_.CategoryTheory

private def textWork (bytes : Bytes) : Work := ⟨[.text bytes], ⟨[], 0⟩, false⟩

private theorem text_meaning (decode : Decoder) (bytes : Bytes) :
    meaning decode (textWork bytes) = some (bytes, ⟨[], 0⟩) := by
  simp [textWork, meaning, framesMeaning, frameMeaning]

inductive Control (decode : Decoder) where
  | ready (base body : List Row)
  | comparing (left : Row) (base : List Row) (right : Row) (body : List Row)
      (comparison : Compare.Saved decode)
  | refused

structure State (decode : Decoder) where
  control : Control decode
  polls : Nat

def remaining (decode : Decoder) : Control decode → List Row
  | .ready base body => merge base body
  | .comparing left base right body _ => merge (left :: base) (right :: body)
  | .refused => []

inductive Valid (decode : Decoder) : Control decode → Prop where
  | ready (base body : List Row) : Valid decode (.ready base body)
  | comparing (left : Row) (base : List Row) (right : Row) (body : List Row)
      (comparison : Compare.Saved decode)
      (exact : Compare.savedMeaning decode comparison =
        some (Compare.reference left.product.bytes right.product.bytes)) :
      Valid decode (.comparing left base right body comparison)

/-- Only the existing retained byte comparator decides between two heads.
A progress reply delivers no child and retains the complete comparison packet. -/
def step (decode : Decoder) : Control decode → Option (Option Row) × Control decode
  | .ready [] [] => (none, .ready [] [])
  | .ready (left :: base) [] => (some (some left), .ready base [])
  | .ready [] (right :: body) => (some (some right), .ready [] body)
  | .ready (left :: base) (right :: body) =>
      (some none, .comparing left base right body
        (Compare.start decode (textWork left.product.bytes) (textWork right.product.bytes)))
  | .comparing left base right body comparison =>
      let next := Compare.resume decode 1 comparison
      match Compare.completed decode next with
      | none => (some none, .comparing left base right body next)
      | some (.error _) => (none, .refused)
      | some (.ok .gt) => (some (some right), .ready (left :: base) body)
      | some (.ok _) => (some (some left), .ready base (right :: body))
  | .refused => (none, .refused)

def emitted : Option (Option Row) → List Row
  | some (some row) => [row]
  | _ => []

private theorem comparison_start (decode : Decoder) (left right : Row) :
    Compare.savedMeaning decode
      (Compare.start decode (textWork left.product.bytes) (textWork right.product.bytes)) =
        some (Compare.reference left.product.bytes right.product.bytes) := by
  simp [Compare.start, Compare.savedMeaning, Compare.controlMeaning, text_meaning]

private theorem comparison_completed (decode : Decoder) (saved : Compare.Saved decode)
    (expected : Ordering) (valid : Compare.savedMeaning decode saved = some expected) :
    ∀ answer, Compare.completed decode saved = some answer → answer = .ok expected := by
  rcases saved with ⟨paid, outcome⟩
  cases outcome with
  | paused packet => simp [Compare.completed]
  | done result =>
      rcases result with ⟨index, answer, sources⟩
      cases index
      cases answer with
      | error error => simp [Compare.savedMeaning, Compare.controlMeaning] at valid
      | ok order =>
          have orderEq : order = expected := by
            simpa [Compare.savedMeaning, Compare.controlMeaning] using valid
          simp [Compare.completed, orderEq]

/-- The residual reference is not executed by the producer. The local law
relates actual byte progress/row emission to the independently merged suffix. -/
theorem step_spec (decode : Decoder) (control : Control decode) (valid : Valid decode control) :
    Valid decode (step decode control).2 ∧
      remaining decode control = emitted (step decode control).1 ++ remaining decode (step decode control).2 ∧
      ((step decode control).1 = none → remaining decode control = []) := by
  cases valid with
  | ready base body =>
      cases base with
      | nil =>
          cases body with
          | nil => exact ⟨.ready [] [], rfl, by simp [remaining, merge]⟩
          | cons right body => simp [step, remaining, merge, emitted, Valid.ready]
      | cons left base =>
          cases body with
          | nil => simp [step, remaining, merge, emitted, Valid.ready]
          | cons right body =>
              exact ⟨.comparing left base right body _ (comparison_start decode left right), rfl, by simp [step]⟩
  | comparing left base right body comparison exactComparison =>
      have kept := Compare.resume_preserves_comparison decode 1 comparison _ exactComparison
      cases result : Compare.completed decode (Compare.resume decode 1 comparison) with
      | none =>
          simp only [step, result]
          exact ⟨.comparing left base right body _ kept, rfl, by simp⟩
      | some answer =>
          have actual := comparison_completed decode _ _ kept answer result
          cases answer with
          | error error => cases actual
          | ok order =>
              have exactOrder : order = Compare.reference left.product.bytes right.product.bytes :=
                Except.ok.inj actual
              cases order with
              | lt => simp [step, result, remaining, emitted, merge, before, ← exactOrder, Valid.ready]
              | eq => simp [step, result, remaining, emitted, merge, before, ← exactOrder, Valid.ready]
              | gt => simp [step, result, remaining, emitted, merge, before, ← exactOrder, Valid.ready]

/-- Poll receipts count declared producer operations, including genuine end.
They do not price byte allocation, copying or native control-state steps. -/
def provider (decode : Decoder) : Mettapedia.Machines.Cursor.Provider (Mettapedia.Machines.Cursor.Sequence.protocol (Option Row)) where
  State _ _ := State decode
  step state _ :=
    let result := step decode state.control
    ⟨result.1, ⟨result.2, state.polls + 1⟩⟩

variable {Bit : Type}

def consume (label : ConstructorSummary.Label Bit) (observe : Row → ConstructorSummary.Summary Bit)
    (draft : Option (ConstructorSummary.Assembly.Draft Row Bit)) :
    Option Row → Option (ConstructorSummary.Assembly.Draft Row Bit)
  | none => draft
  | some row => ConstructorSummary.Assembly.append label observe draft row

def client (label : ConstructorSummary.Label Bit) (observe : Row → ConstructorSummary.Summary Bit) :=
  Mettapedia.Machines.Cursor.Fold.client (consume label observe)

abbrev Saved (decode : Decoder) (label : ConstructorSummary.Label Bit)
    (observe : Row → ConstructorSummary.Summary Bit) :=
  Nat × Mettapedia.Machines.Cursor.Outcome (provider decode) (client label observe) ()

def start (decode : Decoder) (label : ConstructorSummary.Label Bit)
    (observe : Row → ConstructorSummary.Summary Bit) (base body : List Row) : Saved decode label observe :=
  (0, .paused ⟨(), .pulling (some (ConstructorSummary.Assembly.initial (base.length + body.length))),
    ⟨.ready base body, 0⟩⟩)

def resume (decode : Decoder) (label : ConstructorSummary.Label Bit)
    (observe : Row → ConstructorSummary.Summary Bit) (allowance : Nat)
    (saved : Saved decode label observe) : Saved decode label observe :=
  Mettapedia.Machines.Cursor.resume (provider decode) (client label observe) (fun _ _ => 1) allowance saved

def completed (decode : Decoder) (label : ConstructorSummary.Label Bit)
    (observe : Row → ConstructorSummary.Summary Bit) (saved : Saved decode label observe) :
    Option (Except Unit (ConstructorSummary.Assembly.Publication Row Bit)) :=
  match saved.2 with
  | .paused _ => none
  | .done ⟨_, draft, state⟩ => match state.control with
    | .refused => some (.error ())
    | _ => some (match ConstructorSummary.Assembly.publish label draft with
        | none => .error ()
        | some publication => .ok publication)

theorem resume_zero (decode : Decoder) (label : ConstructorSummary.Label Bit)
    (observe : Row → ConstructorSummary.Summary Bit) (saved : Saved decode label observe) :
    resume decode label observe 0 saved = saved := Mettapedia.Machines.Cursor.resume_zero _ _ _ _

theorem pause_composition (decode : Decoder) (label : ConstructorSummary.Label Bit)
    (observe : Row → ConstructorSummary.Summary Bit) (first second : Nat)
    (saved : Saved decode label observe) :
    resume decode label observe (first + second) saved =
      resume decode label observe second (resume decode label observe first saved) :=
  Mettapedia.Machines.Cursor.resume_add _ _ _ first second saved

theorem paused_not_published (decode : Decoder) (label : ConstructorSummary.Label Bit)
    (observe : Row → ConstructorSummary.Summary Bit) (paid : Nat)
    (packet : Mettapedia.Machines.Cursor.Packet (provider decode) (client label observe) ()) :
    completed decode label observe (paid, .paused packet) = none := rfl


open ConstructorSummary

private theorem append_prefix (label : Label Bit) (observe : Row → Summary Bit)
    (arity : Nat) (accepted : List Row) (row : Row) (fits : accepted.length + 1 ≤ arity) :
    Assembly.append label observe (some (Assembly.prefixDraft label observe arity accepted)) row =
      some (Assembly.prefixDraft label observe arity (accepted ++ [row])) := by
  have before := Assembly.prefix_invariant label observe arity accepted (by omega)
  have after := Assembly.prefix_invariant label observe arity (accepted ++ [row]) (by simpa using fits)
  rw [List.foldl_append, before] at after
  simpa using after

def accumulator : Mettapedia.Machines.Cursor.Fold.State (Option (Assembly.Draft Row Bit)) →
    Option (Assembly.Draft Row Bit)
  | .pulling draft => draft
  | .finished draft => draft

def exhausted : Mettapedia.Machines.Cursor.Fold.State (Option (Assembly.Draft Row Bit)) → Bool
  | .pulling _ => false
  | .finished _ => true

/-- The reference is split into the actual accepted children and the live
producer suffix. Summary folding happens on arrival, not after collection. -/
def Invariant (decode : Decoder) (label : Label Bit) (observe : Row → Summary Bit)
    (original : List Row) (control : Mettapedia.Machines.Cursor.Fold.State (Option (Assembly.Draft Row Bit)))
    (state : State decode) : Prop :=
  Valid decode state.control ∧ ∃ accepted,
    original = accepted ++ remaining decode state.control ∧
    accumulator control = some (Assembly.prefixDraft label observe original.length accepted) ∧
    (exhausted control = true → remaining decode state.control = [])

private def after (label : Label Bit) (observe : Row → Summary Bit)
    (draft : Option (Assembly.Draft Row Bit)) :
    Option (Option Row) → Mettapedia.Machines.Cursor.Fold.State (Option (Assembly.Draft Row Bit))
  | none => .finished draft
  | some item => .pulling (consume label observe draft item)

private theorem step_invariant (decode : Decoder) (label : Label Bit) (observe : Row → Summary Bit)
    (original : List Row) (draft : Option (Assembly.Draft Row Bit)) (state : State decode)
    (valid : Invariant decode label observe original (.pulling draft) state) :
    Invariant decode label observe original (after label observe draft (step decode state.control).1)
      ⟨(step decode state.control).2, state.polls + 1⟩ := by
  obtain ⟨validControl, accepted, split, actual, _⟩ := valid
  have spec := step_spec decode state.control validControl
  refine ⟨spec.1, ?_⟩
  cases reply : (step decode state.control).1 with
  | none =>
      have ended := spec.2.2 reply
      have nextEmpty : remaining decode (step decode state.control).2 = [] := by
        simpa [emitted, reply, ended] using spec.2.1.symm
      refine ⟨accepted, ?_, ?_, ?_⟩
      · simpa [ended, nextEmpty] using split
      · simpa [after, reply, accumulator] using actual
      · exact fun _ => nextEmpty
  | some item =>
      cases item with
      | none =>
          have suffix : remaining decode state.control = remaining decode (step decode state.control).2 := by
            simpa [emitted, reply] using spec.2.1
          refine ⟨accepted, ?_, ?_, ?_⟩
          · simpa [suffix] using split
          · simpa [after, reply, accumulator, consume] using actual
          · simp [after, exhausted]
      | some row =>
          have suffix : remaining decode state.control = row :: remaining decode (step decode state.control).2 := by
            simpa [emitted, reply] using spec.2.1
          have splitNext : original = (accepted ++ [row]) ++ remaining decode (step decode state.control).2 := by
            simpa [List.append_assoc, suffix] using split
          have fits : accepted.length + 1 ≤ original.length := by
            rw [splitNext, List.length_append, List.length_append]
            simp only [List.length_singleton]
            omega
          refine ⟨accepted ++ [row], splitNext, ?_, ?_⟩
          · have actualDraft : draft = some (Assembly.prefixDraft label observe original.length accepted) := actual
            simp only [after, accumulator, consume, actualDraft]
            exact append_prefix label observe original.length accepted row fits
          · simp [after, exhausted]

def outcomeInvariant (decode : Decoder) (label : Label Bit) (observe : Row → Summary Bit)
    (original : List Row) : Mettapedia.Machines.Cursor.Outcome (provider decode) (client label observe) () → Prop
  | .paused ⟨_, control, state⟩ => Invariant decode label observe original control state
  | .done ⟨_, draft, state⟩ => Invariant decode label observe original (.finished draft) state

theorem advance_invariant (decode : Decoder) (label : Label Bit) (observe : Row → Summary Bit)
    (original : List Row) (allowance : Nat)
    (control : Mettapedia.Machines.Cursor.Fold.State (Option (Assembly.Draft Row Bit))) (state : State decode)
    (valid : Invariant decode label observe original control state) :
    outcomeInvariant decode label observe original
      (Mettapedia.Machines.Cursor.advance (provider decode) (client label observe) (fun _ _ => 1)
        allowance ⟨(), control, state⟩).2 := by
  induction allowance generalizing control state with
  | zero => exact valid
  | succ allowance ih =>
      cases control with
      | finished draft => exact valid
      | pulling draft =>
          have next := ih (after label observe draft (step decode state.control).1)
            ⟨(step decode state.control).2, state.polls + 1⟩
            (step_invariant decode label observe original draft state valid)
          dsimp only [Mettapedia.Machines.Cursor.advance, provider, client,
            Mettapedia.Machines.Cursor.Fold.client]
          simp only [TypeCat.ofHom_apply]
          cases reply : (step decode state.control).1 with
          | none =>
              simpa only [outcomeInvariant, reply, after, provider, client,
                Mettapedia.Machines.Cursor.Fold.client, Mettapedia.Machines.Cursor.Sequence.protocol,
                Mettapedia.TypeTheory.IndexedPolynomial.withHoles] using next
          | some item =>
              simpa only [outcomeInvariant, reply, after, provider, client,
                Mettapedia.Machines.Cursor.Fold.client, Mettapedia.Machines.Cursor.Sequence.protocol,
                Mettapedia.TypeTheory.IndexedPolynomial.withHoles] using next

theorem resume_invariant (decode : Decoder) (label : Label Bit) (observe : Row → Summary Bit)
    (original : List Row) (allowance : Nat) (saved : Saved decode label observe)
    (valid : outcomeInvariant decode label observe original saved.2) :
    outcomeInvariant decode label observe original (resume decode label observe allowance saved).2 := by
  rcases saved with ⟨paid, outcome⟩
  cases outcome with
  | done result => exact valid
  | paused packet =>
      rcases packet with ⟨index, control, state⟩
      cases index
      simpa [resume, Mettapedia.Machines.Cursor.resume] using
        advance_invariant decode label observe original allowance control state valid

theorem start_invariant (decode : Decoder) (label : Label Bit) (observe : Row → Summary Bit)
    (base body : List Row) :
    outcomeInvariant decode label observe (merge base body) (start decode label observe base body).2 := by
  refine ⟨.ready base body, [], rfl, ?_, ?_⟩
  · simp [accumulator, Assembly.prefixDraft, Assembly.initial, merge_length, Aggregate.fold]
  · simp [exhausted]


/-- Every allowance retains one accepted prefix, its aggregate and the exact
unread merge/comparator state. This includes pauses after the final child. -/
theorem prefix_residual (decode : Decoder) (label : Label Bit) (observe : Row → Summary Bit)
    (base body : List Row) (allowance : Nat) :
    outcomeInvariant decode label observe (merge base body)
      (resume decode label observe allowance (start decode label observe base body)).2 :=
  resume_invariant decode label observe _ allowance _ (start_invariant decode label observe base body)

/-- Any completed constructor contains every row in the reference merge's
actual order, with the existing constructor summary of those same children. -/
theorem completed_exact (decode : Decoder) (label : Label Bit) (observe : Row → Summary Bit)
    (base body : List Row) (allowance : Nat) (answer : Except Unit (Assembly.Publication Row Bit))
    (returned : completed decode label observe
      (resume decode label observe allowance (start decode label observe base body)) = some answer) :
    answer = .ok ⟨merge base body, combine label ((merge base body).map observe)⟩ := by
  have valid := prefix_residual decode label observe base body allowance
  generalize savedEq : resume decode label observe allowance (start decode label observe base body) =
    saved at returned valid
  rcases saved with ⟨paid, outcome⟩
  cases outcome with
  | paused packet => simp [completed] at returned
  | done result =>
      rcases result with ⟨index, draft, state⟩
      cases index
      obtain ⟨validControl, accepted, split, actual, ended⟩ := valid
      have empty := ended rfl
      have acceptedEq : accepted = merge base body := by simpa [empty] using split.symm
      subst accepted
      have actualDraft : draft = some (Assembly.prefixDraft label observe (merge base body).length
          (merge base body)) := actual
      have value : completed decode label observe (paid, .done ⟨(), draft, state⟩) =
          some (.ok ⟨merge base body, combine label ((merge base body).map observe)⟩) := by
        cases controlEq : state.control with
        | ready base body => simp [completed, controlEq, actualDraft, Assembly.publish_prefix]
        | comparing left base right body comparison =>
            simp [completed, controlEq, actualDraft, Assembly.publish_prefix]
        | refused => rw [controlEq] at validControl; cases validControl
      exact Option.some.inj (returned.symm.trans value)

theorem completed_children_summary (decode : Decoder) (label : Label Bit) (observe : Row → Summary Bit)
    (base body : List Row) (allowance : Nat) (publication : Assembly.Publication Row Bit)
    (returned : completed decode label observe
      (resume decode label observe allowance (start decode label observe base body)) = some (.ok publication)) :
    publication.children = merge base body ∧
      publication.summary = combine label ((merge base body).map observe) := by
  have actual := Except.ok.inj (completed_exact decode label observe base body allowance (.ok publication) returned)
  cases actual
  exact ⟨rfl, rfl⟩

theorem completed_arity (decode : Decoder) (label : Label Bit) (observe : Row → Summary Bit)
    (base body : List Row) (allowance : Nat) (publication : Assembly.Publication Row Bit)
    (returned : completed decode label observe
      (resume decode label observe allowance (start decode label observe base body)) = some (.ok publication)) :
    publication.children.length = base.length + body.length := by
  rw [(completed_children_summary decode label observe base body allowance publication returned).1, merge_length]

theorem completed_ordinals (decode : Decoder) (label : Label Bit) (observe : Row → Summary Bit)
    (base body : List Row) (allowance : Nat) (publication : Assembly.Publication Row Bit)
    (returned : completed decode label observe
      (resume decode label observe allowance (start decode label observe base body)) = some (.ok publication)) :
    (publication.children.map Row.ordinal).Perm (base.map Row.ordinal ++ body.map Row.ordinal) := by
  rw [(completed_children_summary decode label observe base body allowance publication returned).1]
  exact merge_ordinal_perm base body

theorem completed_values (decode : Decoder) (label : Label Bit) (observe : Row → Summary Bit)
    (base body : List Row) (allowance : Nat) (publication : Assembly.Publication Row Bit)
    (returned : completed decode label observe
      (resume decode label observe allowance (start decode label observe base body)) = some (.ok publication)) :
    (publication.children.map Row.value).Perm (base.map Row.value ++ body.map Row.value) := by
  rw [(completed_children_summary decode label observe base body allowance publication returned).1]
  exact merge_value_perm base body

theorem completed_stable_ties (decode : Decoder) (label : Label Bit) (observe : Row → Summary Bit)
    (base body : List Row) (allowance : Nat) (publication : Assembly.Publication Row Bit)
    (same : ∀ left ∈ base, ∀ right ∈ body, left.product.bytes = right.product.bytes)
    (returned : completed decode label observe
      (resume decode label observe allowance (start decode label observe base body)) = some (.ok publication)) :
    publication.children = base ++ body := by
  rw [(completed_children_summary decode label observe base body allowance publication returned).1]
  exact all_ties_keep_original_spines base body same

def outcomePolls (decode : Decoder) (label : Label Bit) (observe : Row → Summary Bit) :
    Mettapedia.Machines.Cursor.Outcome (provider decode) (client label observe) () → Nat
  | .paused ⟨_, _, state⟩ => state.polls
  | .done ⟨_, _, state⟩ => state.polls

/-- The actual cursor receipt is exactly the provider's poll increment. Client
return is uncharged, while the exhaustion query is charged once. -/
theorem advance_exact_polls (decode : Decoder) (label : Label Bit) (observe : Row → Summary Bit)
    (allowance : Nat) (control : Mettapedia.Machines.Cursor.Fold.State (Option (Assembly.Draft Row Bit)))
    (state : State decode) :
    (Mettapedia.Machines.Cursor.advance (provider decode) (client label observe) (fun _ _ => 1) (base := ())
      allowance ⟨(), control, state⟩).1 + state.polls =
    outcomePolls decode label observe (Mettapedia.Machines.Cursor.advance (provider decode)
      (client label observe) (fun _ _ => 1) allowance ⟨(), control, state⟩).2 := by
  induction allowance generalizing control state with
  | zero => change 0 + state.polls = state.polls; omega
  | succ allowance ih =>
      cases control with
      | finished draft => change 0 + state.polls = state.polls; omega
      | pulling draft =>
          have next := ih (after label observe draft (step decode state.control).1)
            ⟨(step decode state.control).2, state.polls + 1⟩
          dsimp only [Mettapedia.Machines.Cursor.advance, provider, client,
            Mettapedia.Machines.Cursor.Fold.client]
          simp only [TypeCat.ofHom_apply]
          cases reply : (step decode state.control).1 with
          | none =>
              simpa [outcomePolls, reply, after, provider, client,
                Mettapedia.Machines.Cursor.Fold.client, Mettapedia.Machines.Cursor.Sequence.protocol,
                Mettapedia.TypeTheory.IndexedPolynomial.withHoles, Nat.add_assoc, Nat.add_left_comm,
                Nat.add_comm] using next
          | some item =>
              simpa [outcomePolls, reply, after, provider, client,
                Mettapedia.Machines.Cursor.Fold.client, Mettapedia.Machines.Cursor.Sequence.protocol,
                Mettapedia.TypeTheory.IndexedPolynomial.withHoles, Nat.add_assoc, Nat.add_left_comm,
                Nat.add_comm] using next

theorem resume_exact_polls (decode : Decoder) (label : Label Bit) (observe : Row → Summary Bit)
    (allowance : Nat) (saved : Saved decode label observe)
    (accounted : saved.1 = outcomePolls decode label observe saved.2) :
    (resume decode label observe allowance saved).1 =
      outcomePolls decode label observe (resume decode label observe allowance saved).2 := by
  rcases saved with ⟨paid, outcome⟩
  cases outcome with
  | done result => exact accounted
  | paused packet =>
      rcases packet with ⟨index, control, state⟩
      cases index
      have next := advance_exact_polls decode label observe allowance control state
      have initial : paid = state.polls := accounted
      simpa [resume, Mettapedia.Machines.Cursor.resume, initial, Nat.add_comm] using next

theorem run_exact_polls (decode : Decoder) (label : Label Bit) (observe : Row → Summary Bit)
    (base body : List Row) (allowance : Nat) :
    (resume decode label observe allowance (start decode label observe base body)).1 =
      outcomePolls decode label observe
        (resume decode label observe allowance (start decode label observe base body)).2 :=
  resume_exact_polls decode label observe allowance _ rfl


/-- A pending merge retains the same saved byte-comparison continuation. -/
theorem comparison_pending (decode : Decoder) (left right : Row) (base body : List Row)
    (comparison : Compare.Saved decode)
    (pending : Compare.completed decode (Compare.resume decode 1 comparison) = none) :
    step decode (.comparing left base right body comparison) =
      (some none, .comparing left base right body (Compare.resume decode 1 comparison)) := by
  simp [step, pending]

/-- Logical cancellation discards only unpublished preparation. Physical
retirement and its allocator/finalizer costs are not modeled by this operation. -/
def cancel (decode : Decoder) (label : Label Bit) (observe : Row → Summary Bit)
    (saved : Saved decode label observe) : Saved decode label observe :=
  match saved.2 with
  | .paused ⟨index, _, state⟩ =>
      (saved.1, .done ⟨index, none, { state with control := .refused }⟩)
  | .done _ => saved

theorem cancel_preserves_bill (decode : Decoder) (label : Label Bit) (observe : Row → Summary Bit)
    (saved : Saved decode label observe) : (cancel decode label observe saved).1 = saved.1 := by
  rcases saved with ⟨paid, outcome⟩
  cases outcome <;> rfl

theorem cancel_paused_refuses (decode : Decoder) (label : Label Bit) (observe : Row → Summary Bit)
    (paid : Nat) (packet : Mettapedia.Machines.Cursor.Packet (provider decode) (client label observe) ()) :
    completed decode label observe (cancel decode label observe (paid, .paused packet)) = some (.error ()) := by
  rcases packet with ⟨index, control, state⟩
  rfl

theorem cancel_done_inert (decode : Decoder) (label : Label Bit) (observe : Row → Summary Bit)
    (paid : Nat) (result : Mettapedia.Machines.Cursor.Finished (provider decode)
      (Return := fun _ _ => Option (Assembly.Draft Row Bit)) ()) :
    cancel decode label observe (paid, .done result) = (paid, .done result) := rfl

theorem cancelled_cannot_reexecute (decode : Decoder) (label : Label Bit) (observe : Row → Summary Bit)
    (saved : Saved decode label observe) (allowance : Nat) :
    resume decode label observe allowance (cancel decode label observe saved) =
      cancel decode label observe saved := by
  rcases saved with ⟨paid, outcome⟩
  cases outcome <;> rfl

open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalBag
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT

theorem completed_target {source : Bag} (firing : Firing source)
    (decode : Decoder) (label : Label Bit) (observe : Row → Summary Bit)
    (base body : List Row) (allowance : Nat) (publication : Assembly.Publication Row Bit)
    (baseValues : base.map Row.value = firing.tail)
    (bodyValues : body.map Row.value = contents firing.rule.result)
    (returned : completed decode label observe
      (resume decode label observe allowance (start decode label observe base body)) = some (.ok publication)) :
    (publication.children.map Row.value : Multiset Pattern) = firing.target.1 := by
  rw [(completed_children_summary decode label observe base body allowance publication returned).1]
  exact prepared_values_target firing base body baseValues bodyValues

/-- Semantic readout uses the actual published children. Native body-origin
and copied-child ordinal decoding remain representation obligations. -/
def process {source : Bag} (firing : Firing source)
    (decode : Decoder) (label : Label Bit) (observe : Row → Summary Bit)
    (base body : List Row) (allowance : Nat) (publication : Assembly.Publication Row Bit)
    (baseValues : base.map Row.value = firing.tail)
    (bodyValues : body.map Row.value = contents firing.rule.result)
    (returned : completed decode label observe
      (resume decode label observe allowance (start decode label observe base body)) = some (.ok publication)) :
    RhoProcess :=
  ofList (publication.children.map Row.value) (fun pattern membership => by
    rw [(completed_children_summary decode label observe base body allowance publication returned).1] at membership
    exact (prepared_primes firing base body baseValues bodyValues pattern membership).1)

theorem process_eq_candidate {source : Bag} (firing : Firing source)
    (decode : Decoder) (label : Label Bit) (observe : Row → Summary Bit)
    (base body : List Row) (allowance : Nat) (publication : Assembly.Publication Row Bit)
    (baseValues : base.map Row.value = firing.tail)
    (bodyValues : body.map Row.value = contents firing.rule.result)
    (returned : completed decode label observe
      (resume decode label observe allowance (start decode label observe base body)) = some (.ok publication)) :
    process firing decode label observe base body allowance publication baseValues bodyValues returned =
      candidate firing base body baseValues bodyValues := by
  apply Subtype.ext
  simp only [process, candidate,
    (completed_children_summary decode label observe base body allowance publication returned).1]

theorem process_inventory {source : Bag} (firing : Firing source)
    (decode : Decoder) (label : Label Bit) (observe : Row → Summary Bit)
    (base body : List Row) (allowance : Nat) (publication : Assembly.Publication Row Bit)
    (baseValues : base.map Row.value = firing.tail)
    (bodyValues : body.map Row.value = contents firing.rule.result)
    (returned : completed decode label observe
      (resume decode label observe allowance (start decode label observe base body)) = some (.ok publication)) :
    fromProcess (process firing decode label observe base body allowance publication baseValues bodyValues returned) =
      firing.target := by
  rw [process_eq_candidate]
  exact candidate_inventory firing base body baseValues bodyValues

theorem process_readout {source : Bag} (firing : Firing source)
    (decode : Decoder) (label : Label Bit) (observe : Row → Summary Bit)
    (base body : List Row) (allowance : Nat) (publication : Assembly.Publication Row Bit)
    (baseValues : base.map Row.value = firing.tail)
    (bodyValues : body.map Row.value = contents firing.rule.result)
    (returned : completed decode label observe
      (resume decode label observe allowance (start decode label observe base body)) = some (.ok publication)) :
    (process firing decode label observe base body allowance publication baseValues bodyValues returned).canonicalize =
      toProcess firing.target := by
  rw [process_eq_candidate]
  exact candidate_readout firing base body baseValues bodyValues

theorem completed_public_step {source : Bag} (firing : Firing source)
    (decode : Decoder) (label : Label Bit) (observe : Row → Summary Bit)
    (base body : List Row) (allowance : Nat) (publication : Assembly.Publication Row Bit)
    (baseValues : base.map Row.value = firing.tail)
    (bodyValues : body.map Row.value = contents firing.rule.result)
    (returned : completed decode label observe
      (resume decode label observe allowance (start decode label observe base body)) = some (.ok publication)) :
    rhoLanguageDefGSLT.Step (toProcess source)
      (process firing decode label observe base body allowance publication baseValues bodyValues returned).canonicalize := by
  rw [process_eq_candidate]
  exact candidate_public_step firing base body baseValues bodyValues


/-- Reuse the existing empty/singleton/parallel constructor cases on the
published inventory; this is a syntax readout, not a copy/arena operation. -/
def readout (publication : Assembly.Publication Row Bit) : Pattern :=
  collapseBag (publication.children.map Row.value)

theorem readout_empty (publication : Assembly.Publication Row Bit)
    (empty : publication.children = []) : readout publication = .apply "PZero" [] := by
  simp [readout, empty, collapseBag]

theorem readout_single (publication : Assembly.Publication Row Bit) (row : Row)
    (single : publication.children = [row]) : readout publication = row.value := by
  simp [readout, single, collapseBag]

theorem readout_parallel (publication : Assembly.Publication Row Bit)
    (wide : 2 ≤ publication.children.length) :
    readout publication = .collection .hashBag (publication.children.map Row.value) none := by
  exact collapseBag_eq_bag_of_length_ge_two (by simpa using wide)

private theorem collapse_canonical (patterns : List Pattern) :
    canonicalize (collapseBag patterns) = canonicalize (.collection .hashBag patterns none) := by
  cases patterns with
  | nil => simp [collapseBag, canonicalize, canonicalizeList, normalizeBagElements, sortPatterns]
  | cons pattern patterns =>
      cases patterns with
      | nil =>
          rw [collapseBag, Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalStepperCompleteness.canonicalize_bag]
          exact (collapse_normalize_singleton_of_isCanonical (canonicalize_isCanonical pattern)).symm
      | cons pattern rest => rfl

theorem completed_readout_target {source : Bag} (firing : Firing source)
    (decode : Decoder) (label : Label Bit) (observe : Row → Summary Bit)
    (base body : List Row) (allowance : Nat) (publication : Assembly.Publication Row Bit)
    (baseValues : base.map Row.value = firing.tail)
    (bodyValues : body.map Row.value = contents firing.rule.result)
    (returned : completed decode label observe
      (resume decode label observe allowance (start decode label observe base body)) = some (.ok publication)) :
    canonicalize (readout publication) = (toProcess firing.target).1 := by
  rw [readout, collapse_canonical]
  exact congrArg Subtype.val
    (process_readout firing decode label observe base body allowance publication baseValues bodyValues returned)


private theorem before_isLE (left right : Row) :
    before left right = (Compare.reference left.product.bytes right.product.bytes).isLE := by
  rw [Ordering.isLE_eq_not_beq_gt]
  rfl

theorem before_trans (first second third : Row)
    (earlier : before first second = true) (later : before second third = true) :
    before first third = true := by
  simp only [before_isLE, Compare.reference] at *
  exact Std.TransCmp.isLE_trans earlier later

theorem before_total (left right : Row) : (before left right || before right left) = true := by
  have oriented : Compare.reference left.product.bytes right.product.bytes =
      (Compare.reference right.product.bytes left.product.bytes).swap :=
    Std.OrientedCmp.eq_swap (cmp := List.compareLex compare)
  rw [before_isLE, before_isLE, oriented]
  cases Compare.reference right.product.bytes left.product.bytes <;> rfl

theorem completed_sorted (decode : Decoder) (label : Label Bit) (observe : Row → Summary Bit)
    (base body : List Row) (allowance : Nat) (publication : Assembly.Publication Row Bit)
    (baseSorted : base.Pairwise (fun left right => before left right = true))
    (bodySorted : body.Pairwise (fun left right => before left right = true))
    (returned : completed decode label observe
      (resume decode label observe allowance (start decode label observe base body)) = some (.ok publication)) :
    publication.children.Pairwise (fun left right => before left right = true) := by
  rw [(completed_children_summary decode label observe base body allowance publication returned).1]
  exact List.pairwise_merge before_trans before_total base body baseSorted bodySorted

namespace Controls

open Mettapedia.Machines.Cursor.TailSummary

private def decode : Decoder := ⟨literal, fun _ => literal "opaque"⟩
private def label : Label Unit := ConstructorSummary.Controls.plain 1
private def row (ordinal : Nat) (bytes : Bytes) : Row :=
  ⟨.apply "POutput" [.apply "NQuote" [.apply "PZero" []], .apply "PZero" []], ⟨bytes, 0, 0⟩, ordinal⟩
private def observe (_ : Row) : Summary Unit := ConstructorSummary.Controls.leaf 1
private def run (allowance : Nat) (base body : List Row) : Saved decode label observe :=
  resume decode label observe allowance (start decode label observe base body)

private def output (saved : Saved decode label observe) :
    Option (Except Unit (List Nat × Vars × Bool × Bool)) :=
  match completed decode label observe saved with
  | none => none
  | some (.error _) => some (.error ())
  | some (.ok publication) => some (.ok (publication.children.map Row.ordinal,
      publication.summary.aggregate.vars, publication.summary.aggregate.closed,
      publication.summary.aggregate.generation))

private def acceptedOrdinals (saved : Saved decode label observe) : Option (List Nat) :=
  let draft := match saved.2 with
    | .paused ⟨_, control, _⟩ => accumulator control
    | .done ⟨_, value, _⟩ => value
  draft.map fun value => value.reversed.reverse.map Row.ordinal

private def comparisonState (saved : Saved decode label observe) : Option (Compare.Saved decode) :=
  let state := match saved.2 with
    | .paused ⟨_, _, state⟩ => state
    | .done ⟨_, _, state⟩ => state
  match state.control with
  | .comparing _ _ _ _ comparison => some comparison
  | _ => none

private def comparisonPaid (saved : Saved decode label observe) : Option Nat :=
  (comparisonState saved).map Prod.fst

private def leftUnread (saved : Saved decode label observe) : Option Bytes := do
  let comparison ← comparisonState saved
  match comparison.2 with
  | .paused ⟨_, _, sources⟩ => (meaning decode sources.left).map Prod.fst
  | .done ⟨_, _, sources⟩ => (meaning decode sources.left).map Prod.fst

private def heldLeft (saved : Saved decode label observe) : Option UInt8 := do
  let comparison ← comparisonState saved
  match comparison.2 with
  | .paused ⟨_, .right held, _⟩ => held
  | _ => none

/-- Preparing two heads has not secretly compared their complete keys. -/
theorem first_poll_only_prepares_comparison :
    comparisonPaid (run 1 [row 0 [97, 98, 99]] [row 1 [97, 98, 100]]) = some 0 ∧
    leftUnread (run 1 [row 0 [97, 98, 99]] [row 1 [97, 98, 100]]) = some [97, 98, 99] ∧
    acceptedOrdinals (run 1 [row 0 [97, 98, 99]] [row 1 [97, 98, 100]]) = some [] := by
  decide +kernel

/-- The saved byte and unread tail are actual provider residuals. -/
theorem comparison_retains_its_byte_position :
    comparisonPaid (run 2 [row 0 [97, 98, 99]] [row 1 [97, 98, 100]]) = some 1 ∧
    heldLeft (run 2 [row 0 [97, 98, 99]] [row 1 [97, 98, 100]]) = some 97 ∧
    leftUnread (run 2 [row 0 [97, 98, 99]] [row 1 [97, 98, 100]]) = some [98, 99] ∧
    leftUnread (run 4 [row 0 [97, 98, 99]] [row 1 [97, 98, 100]]) = some [99] := by
  decide +kernel

theorem equal_byte_prefix_cannot_emit_a_row :
    acceptedOrdinals (run 3 [row 0 [97]] [row 1 [97, 98]]) = some [] ∧
      output (run 3 [row 0 [97]] [row 1 [97, 98]]) = none := by
  decide +kernel

theorem proper_prefix_and_first_mismatch :
    output (run 64 [row 0 [97]] [row 1 [97, 98]]) = some (.ok ([0, 1], .none, true, false)) ∧
    output (run 64 [row 0 [98]] [row 1 [97, 255, 255]]) = some (.ok ([1, 0], .none, true, false)) := by
  decide +kernel

theorem zero_allowance_is_inert :
    output (run 0 [row 0 [97]] [row 1 [98]]) = none ∧
      (run 0 [row 0 [97]] [row 1 [98]]).1 = 0 ∧
      acceptedOrdinals (run 0 [row 0 [97]] [row 1 [98]]) = some [] := by
  decide +kernel

theorem zero_output_checks_exhaustion :
    output (run 1 [] []) = none ∧ output (run 2 [] []) = some (.ok ([], .none, true, false)) ∧
      (run 2 [] []).1 = 1 := by
  decide +kernel

theorem single_output_is_exact :
    output (run 4 [row 7 [97]] []) = some (.ok ([7], .none, true, false)) ∧
      (run 4 [row 7 [97]] []).1 = 2 := by
  decide +kernel

theorem actual_prefix_updates_same_constructor :
    acceptedOrdinals (run 4 [row 0 [97], row 2 [99]] [row 1 [98]]) = some [0] ∧
      output (run 4 [row 0 [97], row 2 [99]] [row 1 [98]]) = none ∧
      output (run 64 [row 0 [97], row 2 [99]] [row 1 [98]]) =
        some (.ok ([0, 1, 2], .none, true, false)) ∧
      (run 64 [row 0 [97], row 2 [99]] [row 1 [98]]).1 = 10 := by
  decide +kernel

theorem full_constructor_before_end_is_unpublished :
    acceptedOrdinals (run 9 [row 0 [97], row 2 [99]] [row 1 [98]]) = some [0, 1, 2] ∧
      output (run 9 [row 0 [97], row 2 [99]] [row 1 [98]]) = none := by
  decide +kernel

theorem full_constructor_before_client_return_is_unpublished :
    output (run 10 [row 0 [97], row 2 [99]] [row 1 [98]]) = none ∧
      output (run 11 [row 0 [97], row 2 [99]] [row 1 [98]]) =
        some (.ok ([0, 1, 2], .none, true, false)) := by
  decide +kernel

theorem cancellation_preserves_paid_prefix_without_publication :
    (cancel decode label observe (run 4 [row 0 [97], row 2 [99]] [row 1 [98]])).1 = 4 ∧
      output (cancel decode label observe (run 4 [row 0 [97], row 2 [99]] [row 1 [98]])) = some (.error ()) ∧
      output (cancel decode label observe (run 9 [row 0 [97], row 2 [99]] [row 1 [98]])) = some (.error ()) := by
  decide +kernel

theorem completed_publication_survives_cancel :
    output (cancel decode label observe (run 64 [row 7 [97]] [])) =
      some (.ok ([7], .none, true, false)) := by
  decide +kernel

theorem resumed_prefix_has_same_state_and_bill :
    resume decode label observe 60 (run 4 [row 0 [97], row 2 [99]] [row 1 [98]]) =
      run 64 [row 0 [97], row 2 [99]] [row 1 [98]] := by
  exact (pause_composition decode label observe 4 60 _).symm

theorem stable_tie_policy_keeps_actual_rows :
    output (run 64 [row 3 []] [row 8 []]) = some (.ok ([3, 8], .none, true, false)) ∧
      output (run 64 [row 8 []] [row 3 []]) = some (.ok ([8, 3], .none, true, false)) := by
  decide +kernel

theorem duplicate_storage_does_not_remove_occurrences :
    (row 3 []).value = (row 8 []).value ∧
      output (run 64 [row 3 [], row 8 []] [row 13 []]) =
        some (.ok ([3, 8, 13], .none, true, false)) := by
  decide +kernel

theorem deduplication_and_reversed_ties_are_detected :
    output (run 64 [row 3 []] [row 8 []]) ≠ some (.ok ([3], .none, true, false)) ∧
      output (run 64 [row 3 []] [row 8 []]) ≠ some (.ok ([8, 3], .none, true, false)) := by
  decide +kernel

theorem wide_output_retains_every_row :
    output (run 256 ((List.range 32).map (fun i => row i []))
      ((List.range 32).map (fun i => row (i + 32) []))) =
        some (.ok (List.range 64, .none, true, false)) := by
  decide +kernel


/-- Distinct occurrence identities are visible even when every contribution
is the summary of the same shared child value. -/
theorem identical_observations_preserve_distinct_occurrences :
    observe (row 3 []) = observe (row 8 []) ∧
      output (run 64 [row 3 []] [row 8 []]) = some (.ok ([3, 8], .none, true, false)) := by
  constructor
  · rfl
  · decide +kernel

private def variableObserve (child : Row) : Summary Unit :=
  ⟨.arena 1, { Aggregate.unit with vars := .one child.ordinal }⟩

theorem variable_conflict_survives_incremental_merge :
    ((completed decode label variableObserve
      (resume decode label variableObserve 64 (start decode label variableObserve
        [row 3 [], row 3 []] [row 8 []]))).map
      (fun result => result.toOption.map (fun publication => publication.summary.aggregate.vars))) =
      some (some .many) := by
  decide +kernel

private def foreignObserve (_ : Row) : Summary Unit := ⟨.arena 2, Aggregate.unit⟩
private def olderLabel : Label Unit := ConstructorSummary.Controls.plain 1 (some 2)

theorem assembly_still_checks_child_home :
    ((completed decode olderLabel foreignObserve
      (resume decode olderLabel foreignObserve 4 (start decode olderLabel foreignObserve [row 7 []] []))).map
        (fun result => result.toOption.map (fun publication =>
          (publication.summary.aggregate.closed, publication.summary.aggregate.generation)))) =
      some (some (false, true)) := by
  decide +kernel

theorem existing_zero_single_parallel_readout :
    collapseBag ([] : List Pattern) = .apply "PZero" [] ∧
      collapseBag [(row 7 []).value] = (row 7 []).value ∧
      collapseBag [(row 3 []).value, (row 8 []).value] =
        .collection .hashBag [(row 3 []).value, (row 8 []).value] none := by
  exact ⟨rfl, rfl, rfl⟩

end Controls

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalReactionOccurrences.RetainedInventory.Cursor
