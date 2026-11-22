import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Terms
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalReactionControls

/-!
# The source: the reflective higher-order calculus, read against its paper

The tree already has the calculus of Meredith and Radestock, *A reflective higher-order calculus*
(2005), on closed processes; it is reused here, not redefined. Each definition of the paper, with
its section, and the declaration that carries it:

* §2.0.1 syntax: `0`, `x(y).P`, `x⟨|P|⟩`, `*x`, `P | Q`, names `@P`. The carrier `RhoProcess`
  holds the closed, well-sorted patterns of the authored grammar whose quoted bodies are sealed
  (`binderSafeAt "NQuote" 0`): a binder never reaches inside a quote, which is §2.0.4's "@P is
  impervious to substitution". The paper's own α-equivalence matches names up to name
  equivalence (§2.5), so `x(y).(@(*y)⟨|0|⟩)` is α-equivalent to `x(y).(y⟨|0|⟩)`; the carrier keeps
  the second form, with bound names bare.
* §2.3 structural congruence and §2.4 name equivalence: the equations of the source,
  `rhoProcessEquations` (equality of canonical forms), are the structural congruence of the raw
  syntax (`equations_are_structural`), which has the monoid laws, congruence under every former,
  and quote-drop at name positions. Name equivalence is `NameEquiv`: QUOTE-DROP (`quote_drop`) and
  STRUCT-EQUIV (`struct_equiv`). Reading choice: the paper does not say whether `≡` relates two
  processes that differ only by equivalent free names; the tree's equations do (quote-drop holds at
  every name position). COMM and the barbs compare names up to name equivalence in either reading.
* §2.7 semantic substitution: `semanticCommSubst`. A dropped received name becomes the received
  process (`received_drop_runs`); quoted bodies are left alone (`quotes_sealed`).
* §2.8 COMM, PAR, EQUIV: `rhoLanguageDefGSLT.Step`, communication between an input and an output
  whose channels have equal canonical forms, in any parallel context, modulo the equations on both
  sides; `CanonicalReaction.publicStep_iff` reads it as reactions of canonical bags of primes.
* §2.0.4 drop is inert except under an input: no reduction runs a free drop (`free_drop_inert`).

Controls, positive and negative, for each of the three features that separate this calculus from
communication with ordinary substitution:

* quote-drop: `quote_drop`, `struct_equiv`; `free_drop_inert` (the converse shape `*@P` is not `P`);
  `names_not_equivalent`.
* communication only up to name equivalence: `communicates_up_to_name_equivalence` (the channels
  `@(*@0)` and `@0` are different names); `inequivalent_channels_do_not_communicate`.
* **the separating substitution** (`semantic_and_ordinary_differ`): the program
  `for(y <- @0){*y} | @0!(@0!(0))` communicates to `@0!(0)` here; ordinary substitution gives
  `*@(@0!(0))` instead. The two are not equal modulo the equations, and they behave differently:
  beside a receiver on `@0`, the semantic contractum communicates
  (`semantic_contractum_communicates`) and the ordinary one is stuck
  (`ordinary_contractum_stuck`). Communication with ordinary substitution in the tree
  (`RhoSchema.comm`, instantiated by the term algebra's substitution, which also enters quotes)
  produces the ordinary contractum by definition (`RhoSchema.rhs_under_unquote`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Source

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical
  (canonicalize IsCanonical IsCanonicalList)
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefRewriteSystem
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalBag
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalReaction
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalReactionControls

/-! ## §2.3–2.4: the equations and name equivalence -/

/-- **§2.3.** On closed processes the equations of the source are the structural congruence. -/
theorem equations_are_structural (P Q : RhoProcess) :
    rhoProcessEquations.r P Q ↔ StructuralCongruence P.1 Q.1 :=
  rhoProcessEquations_iff_structuralCongruence P Q

/-- **§2.4, QUOTE-DROP.** `@(*@0)` and `@0` are different names, and name-equivalent; their
canonical forms agree. -/
theorem quote_drop :
    alternateChannel ≠ channel ∧ NameEquiv alternateChannel channel ∧
      canonicalize alternateChannel = canonicalize channel :=
  ⟨literal_names_distinct, NameEquiv.quote_drop channel, actual_name_equation⟩

/-- **§2.4, STRUCT-EQUIV.** `@(0 | 0)` and `@0` are name-equivalent. -/
theorem struct_equiv :
    NameEquiv (.apply "NQuote" [.collection .hashBag [zero, zero] none]) channel :=
  NameEquiv.struct_equiv _ _ (StructuralCongruence.par_nil_right zero)

/-- A name that is not equivalent to `@0`: the code of an output. -/
def otherChannel : Pattern := .apply "NQuote" [payload]

/-- Negative control for name equivalence: `@(@0!(0))` is not `@0`, up to the equations. -/
theorem names_not_equivalent : canonicalize otherChannel ≠ canonicalize channel := by
  decide

/-- **§2.0.4.** A free drop is inert: it is not the null process modulo the equations, and it has
no reduction. The converse shape of quote-drop, `*@P = P`, is not an equation of the calculus. -/
theorem free_drop_inert :
    ¬ rhoProcessEquations.r closedFreeDrop closedNil ∧
      ∀ target, ¬ rhoLanguageDefGSLT.Step closedFreeDrop target :=
  ⟨closedFreeDrop_not_equivalent_nil, closedFreeDrop_irreducible_in_gslt⟩

/-! ## §2.7: semantic substitution -/

/-- **§2.7.** The dropped received name becomes the received process. -/
theorem received_drop_runs (received : Pattern) :
    semanticCommSubst (.apply "PDrop" [.bvar 0]) received = semanticNormalizeProc received :=
  semanticCommSubst_collapses_bound_drop received

/-- **§2.0.4.** Substitution does not enter a quote. -/
theorem quotes_sealed (quoted received : Pattern) :
    semanticCommSubst (.apply "NQuote" [quoted]) received = .apply "NQuote" [quoted] :=
  semanticCommSubst_preserves_quoted_code quoted received

/-! ## §2.8: communication up to name equivalence -/

/-- **Positive.** `for(y <- @(*@0)){*y} | @0!(@0!(0))` communicates although its channels are
different names. -/
theorem communicates_up_to_name_equivalence :
    alternateChannel ≠ channel ∧ rhoLanguageDefGSLT.Step alternateSource (rule.target empty) :=
  ⟨literal_names_distinct, public_communication_accepts_name_equation⟩

theorem other_input_prime : IsPrime (input otherChannel body) := by
  refine ⟨(rhoClosedTermWellSorted_process_iff _).mpr
    ⟨.input (.quote (.output (.quote .unit) .unit)) (.drop (.bvar rfl)), ?_⟩, ?_, ?_, ?_⟩
  · rfl
  · simp [input, otherChannel, body, payload, output, channel, zero, IsCanonical,
      IsCanonicalList]
  · simp [input]
  · intro elements
    simp [input]

/-- The input on the inequivalent channel, beside the output on `@0`. -/
theorem mismatchPrimes :
    ∀ pattern ∈ [input otherChannel body, output channel payload], IsPrime pattern := by
  intro pattern membership
  simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
  rcases membership with rfl | rfl
  · exact other_input_prime
  · exact output_prime

/-- `for(y <- @(@0!(0))){*y} | @0!(@0!(0))`. -/
def mismatchSource : RhoProcess :=
  ofList [input otherChannel body, output channel payload]
    (fun _ membership => (mismatchPrimes _ membership).1)

/-- **Negative.** Channels that are not name-equivalent do not communicate. -/
theorem inequivalent_channels_do_not_communicate (target : RhoProcess) :
    ¬ rhoLanguageDefGSLT.Step mismatchSource target := by
  intro step
  obtain ⟨found, rest, source, _⟩ := (publicStep_iff _ _).mp step
  have inventory := congrArg Subtype.val source
  rw [mismatchSource, fromProcess_ofList_primes _ mismatchPrimes, append_inventory] at inventory
  have inputMember : input found.inputChannel found.body ∈
      ((([input otherChannel body, output channel payload] : List Pattern)) : Multiset Pattern) := by
    rw [inventory]
    exact Multiset.mem_add.mpr (.inl (by simp [GroundComm.redex]))
  have outputMember : output found.outputChannel found.payload ∈
      ((([input otherChannel body, output channel payload] : List Pattern)) : Multiset Pattern) := by
    rw [inventory]
    exact Multiset.mem_add.mpr (.inl (by simp [GroundComm.redex]))
  simp [input, output] at inputMember outputMember
  have channels := found.channels
  rw [inputMember.1, outputMember.1] at channels
  exact names_not_equivalent channels

/-! ## The separating substitution -/

/-- The ordinary-substitution contractum of `for(y <- @0){*y}` receiving `@0!(0)`. -/
def ordinaryContractum : Pattern := .apply "PDrop" [.apply "NQuote" [payload]]

theorem ordinary_substitution_gives_drop :
    Mettapedia.OSLF.MeTTaIL.Substitution.openBVar 0 (.apply "NQuote" [payload]) body =
      ordinaryContractum := by
  simp [Mettapedia.OSLF.MeTTaIL.Substitution.openBVar, body, ordinaryContractum]

/-- A receiver on `@0` that discards what it receives. -/
def receiver : Pattern := input channel zero

theorem receiver_prime : IsPrime receiver := by
  refine ⟨(rhoClosedTermWellSorted_process_iff _).mpr ⟨.input (.quote .unit) .unit, ?_⟩, ?_, ?_, ?_⟩
  · rfl
  · simp [receiver, input, channel, zero, IsCanonical, IsCanonicalList]
  · simp [receiver, input]
  · intro elements
    simp [receiver, input]

theorem payload_prime : IsPrime payload := by
  refine ⟨(rhoClosedTermWellSorted_process_iff _).mpr ⟨.output (.quote .unit) .unit, ?_⟩, ?_, ?_, ?_⟩
  · rfl
  · simp [payload, output, channel, zero, IsCanonical, IsCanonicalList]
  · simp [payload, output]
  · intro elements
    simp [payload, output]

theorem ordinary_prime : IsPrime ordinaryContractum := by
  refine ⟨(rhoClosedTermWellSorted_process_iff _).mpr
    ⟨.drop (.quote (.output (.quote .unit) .unit)), ?_⟩, ?_, ?_, ?_⟩
  · rfl
  · simp [ordinaryContractum, payload, output, channel, zero, IsCanonical, IsCanonicalList]
  · simp [ordinaryContractum]
  · intro elements
    simp [ordinaryContractum]

/-- The semantic contractum meets the receiver. -/
def afterwards : GroundComm := ⟨channel, channel, zero, zero, receiver_prime, payload_prime, rfl⟩

/-- **The semantic contractum communicates** with the receiver. -/
theorem semantic_contractum_communicates :
    (fromProcess (afterwards.source empty)).1 = ({receiver, payload} : Multiset Pattern) ∧
      rhoLanguageDefGSLT.Step (afterwards.source empty) (afterwards.target empty) := by
  refine ⟨?_, (publicStep_iff _ _).mpr
    ⟨afterwards, empty, afterwards.source_inventory empty, afterwards.target_inventory empty⟩⟩
  rw [afterwards.source_inventory empty, append_inventory]
  rfl

theorem stuckPrimes : ∀ pattern ∈ [ordinaryContractum, receiver], IsPrime pattern := by
  intro pattern membership
  simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
  rcases membership with rfl | rfl
  · exact ordinary_prime
  · exact receiver_prime

/-- The ordinary contractum beside the same receiver. -/
def stuckSource : RhoProcess :=
  ofList [ordinaryContractum, receiver] (fun _ membership => (stuckPrimes _ membership).1)

/-- **The ordinary contractum is stuck** beside the same receiver: there is no output to meet. -/
theorem ordinary_contractum_stuck (target : RhoProcess) :
    ¬ rhoLanguageDefGSLT.Step stuckSource target := by
  intro step
  obtain ⟨found, rest, source, _⟩ := (publicStep_iff _ _).mp step
  have inventory := congrArg Subtype.val source
  rw [stuckSource, fromProcess_ofList_primes _ stuckPrimes, append_inventory] at inventory
  have outputMember : output found.outputChannel found.payload ∈
      ((([ordinaryContractum, receiver] : List Pattern)) : Multiset Pattern) := by
    rw [inventory]
    exact Multiset.mem_add.mpr (.inl (by simp [GroundComm.redex]))
  simp [output, ordinaryContractum, receiver, input] at outputMember

/-- **The separating substitution.** For `for(y <- @0){*y} | @0!(@0!(0))` (`rule.source empty`):
the source communicates to the semantic contractum `@0!(0)`; ordinary substitution would give
`*@(@0!(0))`; the two are different modulo the equations; and beside a receiver on `@0` the
first communicates while the second is stuck. -/
theorem semantic_and_ordinary_differ :
    rhoLanguageDefGSLT.Step (rule.source empty) (rule.target empty) ∧
    rule.result.1 = payload ∧
    Mettapedia.OSLF.MeTTaIL.Substitution.openBVar 0 (.apply "NQuote" [payload]) body =
      ordinaryContractum ∧
    canonicalize payload ≠ canonicalize ordinaryContractum ∧
    rhoLanguageDefGSLT.Step (afterwards.source empty) (afterwards.target empty) ∧
    (∀ target, ¬ rhoLanguageDefGSLT.Step stuckSource target) := by
  refine ⟨(publicStep_iff _ _).mpr ⟨rule, empty, rule.source_inventory empty,
      rule.target_inventory empty⟩, actual_result, ordinary_substitution_gives_drop, ?_,
    semantic_contractum_communicates.2, ordinary_contractum_stuck⟩
  decide

#print axioms quote_drop
#print axioms names_not_equivalent
#print axioms inequivalent_channels_do_not_communicate
#print axioms semantic_and_ordinary_differ

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Source
