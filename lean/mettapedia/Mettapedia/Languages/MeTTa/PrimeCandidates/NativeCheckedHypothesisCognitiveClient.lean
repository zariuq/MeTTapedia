import Mettapedia.Languages.MeTTa.PrimeCandidates.NativeCheckedHypothesisPolicyNIKSelection
import Mettapedia.GSLT.Dynamics.GuardRevision

/-!
# A cognitive client of the native hypothesis selection

An agent learns a predicate from examples and then keeps using it: it queries
the predicate, moves a cheap guard ahead of an expensive valuation, serves an
ongoing stream of query batches, revises its world, and asks new questions of
the answers.  This module states that workflow over the existing
native-plus-policy selection of `NativeCheckedHypothesisPolicyNIKSelection`
and proves each step.

The generic part works over any finite fact world:

* a fact base over a sorted primitive signature is a MIL vocabulary whose
  evidence for a primitive edge is membership of its fact in the base;
* the interpreted route evaluates a hypothesis by enumerating atoms and binding
  chains; it lists every derivation exactly once (`interpret_nodup`,
  `mem_interpret`), so it agrees with every exact native provider as an
  occurrence bag (`nativeAnswers_eq_of_exact`);
* the facts a hypothesis reads form a NIK dependency view; revalidating a
  retained native result against a revision is a live meaning whose
  dependencies are adequate (`revalidatedLive_adequate`);
* hoisting charges no more for every canonically ordered additive cost
  (`hoist_charge_le`).

The client world is the native Prime fixture `prime_cognitive_client.metta`:
persons alice, bob, eve and carol, numbers zero and one, the facts
mother(alice, bob), mother(alice, eve), father(bob, carol), father(eve, carol)
and successor(zero, one), the learned chain "mother, then father", the
positive example (alice, carol) and the negative example (alice, bob).  The
answer for alice has two occurrences of carol, through bob and through eve,
each with its proof.

The learned predicate is quoted into a formed context of the candidate's
intrinsic `Hyp` family and its native provider is derived structurally from
the primitive fibres.  The raw proof checker of `MILCheckedChain` belongs to
the three-person canary world; this client enters through the typed
quotation.
-/

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.Logic.MetaInterpretiveLearning.CumulativeTheory

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.NativeCheckedHypothesisCognitiveClient

open Mettapedia.GSLT.Core
open Mettapedia.GSLT.Core.NonFactorization
open Mettapedia.GSLT.Core.SearchStreamProductivity
open Mettapedia.GSLT.Dynamics.GuardedWork
open Mettapedia.GSLT.Dynamics.GuardRevision
open Mettapedia.GSLT.Dynamics.ContextualCandidateValuation
open Mettapedia.GSLT.LanguageDef.NIKRouteAdmission
open Mettapedia.GSLT.LanguageDef.NIKPolicyFamilyAdmission
open Mettapedia.GSLT.LanguageDef.NIKPolicyFamilyAdmission.PolicyFamilyAdmittedAt
open Mettapedia.GSLT.ProofRelevantAnswerBag (AnswerOccurrence AnswerBag)
open Mettapedia.GSLT.ProofRelevantAnswerBag.AnswerBag (chainOccurrence)
open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.IntrinsicMILNativeSearch
open Mettapedia.Languages.MeTTa.PrimeCandidates.NativeRelationalSearchNIKSelection
open Mettapedia.Languages.MeTTa.PrimeCandidates.NIKPolicyFamilyCurrentSelection
open Mettapedia.Languages.MeTTa.PrimeCandidates.NativeCheckedHypothesisPolicyNIKSelection
open MILSchemaElaboration.Semantic (Vocabulary Hypothesis)

/-! ## Resources of a hoisted guard -/

/-- Hoisting a guard never charges more, for every canonically ordered
additive cost.  The saving is exactly the valuation charge of the rejected
candidates (`GuardedWork.hoist_charge`); `hoist_nat_charge_le` is the instance
at `Nat`. -/
theorem hoist_charge_le {Candidate Cost : Type*} [AddCommMonoid Cost] [LE Cost]
    [CanonicallyOrderedAdd Cost]
    (guard : Candidate → Bool) (guardCost valueCost : Candidate → Cost)
    (candidates : List Candidate) :
    guardedCharge guard guardCost valueCost candidates ≤
      eagerCharge guardCost valueCost candidates := by
  rw [hoist_charge guard guardCost valueCost candidates]
  exact le_self_add

/-! ## Exact native bags -/

/-- Any duplicate-free list that contains every occurrence of one evidence
fibre is the bag of every exact native provider of that fibre. -/
theorem nativeAnswers_eq_of_exact {Source Target : Type}
    {relation : ProofRel Source Target} (provider : FiniteEvidenceProvider relation)
    (source : Source) (occurrences : List (AnswerOccurrence relation source))
    (nodup : occurrences.Nodup) (complete : ∀ occurrence, occurrence ∈ occurrences) :
    provider.answers source = (occurrences : Multiset (AnswerOccurrence relation source)) :=
  (Multiset.Nodup.ext (provider.answers_nodup source) (Multiset.coe_nodup.2 nodup)).2
    fun occurrence =>
      ⟨fun _ => Multiset.mem_coe.2 (complete occurrence),
        fun _ => (provider.fibre source).mem_answers occurrence⟩

/-- A chained occurrence determines its earlier occurrence. -/
theorem chainOccurrence_earlier_eq {First Middle Last : Type}
    {earlier : ProofRel First Middle} {later : ProofRel Middle Last} {source : First}
    {first first' : AnswerOccurrence earlier source}
    {second : AnswerOccurrence later first.target}
    {second' : AnswerOccurrence later first'.target}
    (same : chainOccurrence first second = chainOccurrence first' second') :
    first = first' :=
  congrArg Sigma.fst
    ((FiniteEvidenceProvider.chainOccurrenceEquiv (later := later) source).injective
      (a₁ := ⟨first, second⟩) (a₂ := ⟨first', second'⟩) same)

/-- For one earlier occurrence, chaining is injective in the later one. -/
theorem chainOccurrence_injective {First Middle Last : Type}
    {earlier : ProofRel First Middle} {later : ProofRel Middle Last} {source : First}
    (first : AnswerOccurrence earlier source) :
    Function.Injective (chainOccurrence (later := later) first) := by
  intro second second' same
  have indices :=
    (FiniteEvidenceProvider.chainOccurrenceEquiv (later := later) source).injective
      (a₁ := ⟨first, second⟩) (a₂ := ⟨first, second'⟩) same
  exact eq_of_heq (Sigma.mk.inj indices).2

/-! ## Fact worlds -/

/-- A ground fact: a primitive symbol applied to two atoms. -/
structure GroundFact (Symbol Atom : Type) where
  symbol : Symbol
  source : Atom
  target : Atom
  deriving DecidableEq, Repr

/-- A sorted primitive signature whose primitives are named by symbols. -/
structure FactSignature (SortCode Symbol : Type) where
  Primitive : SortCode → SortCode → Type
  symbolOf : {source target : SortCode} → Primitive source target → Symbol

namespace FactSignature

variable {SortCode Symbol : Type} (signature : FactSignature SortCode Symbol)
variable (Atom : Type)

/-- A fact base as a MIL vocabulary over one carrier of atoms: the evidence
for a primitive edge is membership of its fact in the base. -/
abbrev vocabulary (base : List (GroundFact Symbol Atom)) : Vocabulary where
  SortCode := SortCode
  Carrier := fun _ => Atom
  Primitive := signature.Primitive
  meaning := fun symbol =>
    ⟨fun source target => PLift (⟨signature.symbolOf symbol, source, target⟩ ∈ base)⟩

variable [DecidableEq Symbol] [DecidableEq Atom]
variable {Atom}

/-- One primitive step of the interpreted route: the answer at `output`, when
its fact is in the base. -/
def primitiveAnswer (base : List (GroundFact Symbol Atom)) {source target : SortCode}
    (symbol : signature.Primitive source target) (input output : Atom) :
    Option (AnswerOccurrence ((signature.vocabulary Atom base).meaning symbol) input) :=
  if member : (⟨signature.symbolOf symbol, input, output⟩ : GroundFact Symbol Atom) ∈ base
  then some ⟨output, ⟨member⟩⟩ else none

theorem primitiveAnswer_target {base : List (GroundFact Symbol Atom)}
    {source target : SortCode} {symbol : signature.Primitive source target}
    {input output : Atom}
    {occurrence : AnswerOccurrence ((signature.vocabulary Atom base).meaning symbol) input}
    (present : occurrence ∈ signature.primitiveAnswer base symbol input output) :
    occurrence.target = output := by
  rw [Option.mem_def] at present
  unfold primitiveAnswer at present
  split at present
  · cases present
    rfl
  · cases present

/-- The interpreted route: primitives keep the atoms, in the order of `atoms`,
whose fact is in the base; a chain binds the later hypothesis at every earlier
occurrence. -/
def interpret (atoms : List Atom) (base : List (GroundFact Symbol Atom)) :
    {source target : SortCode} →
      (hypothesis : Hypothesis (signature.vocabulary Atom base) source target) →
        (input : Atom) → List (AnswerOccurrence hypothesis.denote input)
  | _, _, .primitive symbol, input =>
      atoms.filterMap (signature.primitiveAnswer base symbol input)
  | _, _, .chain earlier later, input =>
      (interpret atoms base earlier input).flatMap fun first =>
        (interpret atoms base later first.target).map (chainOccurrence first)

/-- The interpreted route lists no derivation twice. -/
theorem interpret_nodup {atoms : List Atom} (nodup : atoms.Nodup)
    (base : List (GroundFact Symbol Atom)) :
    {source target : SortCode} →
      (hypothesis : Hypothesis (signature.vocabulary Atom base) source target) →
        (input : Atom) → (signature.interpret atoms base hypothesis input).Nodup
  | _, _, .primitive symbol, input => by
      apply List.Nodup.filterMap _ nodup
      intro output output' occurrence present present'
      exact (signature.primitiveAnswer_target present).symm.trans
        (signature.primitiveAnswer_target present')
  | _, _, .chain earlier later, input => by
      refine List.nodup_flatMap.2
        ⟨fun first _ => List.Nodup.map (chainOccurrence_injective first)
          (interpret_nodup nodup base later first.target), ?_⟩
      refine (interpret_nodup nodup base earlier input).imp fun {first first'} different => ?_
      intro occurrence present present'
      obtain ⟨second, _, rfl⟩ := List.mem_map.1 present
      obtain ⟨second', _, same⟩ := List.mem_map.1 present'
      exact different (chainOccurrence_earlier_eq same).symm

/-- The interpreted route lists every derivation. -/
theorem mem_interpret {atoms : List Atom} (complete : ∀ atom, atom ∈ atoms)
    (base : List (GroundFact Symbol Atom)) :
    {source target : SortCode} →
      (hypothesis : Hypothesis (signature.vocabulary Atom base) source target) →
        (input : Atom) → (occurrence : AnswerOccurrence hypothesis.denote input) →
          occurrence ∈ signature.interpret atoms base hypothesis input
  | _, _, .primitive symbol, input, ⟨output, evidence⟩ => by
      refine List.mem_filterMap.2 ⟨output, complete output, ?_⟩
      unfold primitiveAnswer
      rw [dif_pos (PLift.down evidence)]
      rfl
  | _, _, .chain earlier later, input, ⟨output, evidence⟩ =>
      List.mem_flatMap.2 ⟨⟨evidence.1, evidence.2.1⟩,
        mem_interpret complete base earlier input ⟨evidence.1, evidence.2.1⟩,
        List.mem_map.2 ⟨⟨output, evidence.2.2⟩,
          mem_interpret complete base later evidence.1 ⟨output, evidence.2.2⟩, rfl⟩⟩

/-- The interpreted route agrees with every exact native provider of the
hypothesis's relation, as an occurrence bag. -/
theorem nativeAnswers_eq_interpret {atoms : List Atom} (nodup : atoms.Nodup)
    (complete : ∀ atom, atom ∈ atoms) (base : List (GroundFact Symbol Atom))
    {source target : SortCode}
    (hypothesis : Hypothesis (signature.vocabulary Atom base) source target)
    (provider : FiniteEvidenceProvider hypothesis.denote) (input : Atom) :
    provider.answers input = (signature.interpret atoms base hypothesis input : Multiset _) :=
  nativeAnswers_eq_of_exact provider input _
    (signature.interpret_nodup nodup base hypothesis input)
    (signature.mem_interpret complete base hypothesis input)

/-- Exact finite fibres of the primitive facts: the atoms whose fact is in the
base. -/
def primitiveFibre [Fintype Atom] (base : List (GroundFact Symbol Atom))
    {source target : SortCode} (symbol : signature.Primitive source target)
    (input : Atom) :
    FiniteEvidenceFibre ((signature.vocabulary Atom base).meaning symbol) input where
  Index := {output : Atom //
    (⟨signature.symbolOf symbol, input, output⟩ : GroundFact Symbol Atom) ∈ base}
  indexFintype := inferInstance
  occurrenceEquiv :=
    { toFun := fun output => ⟨output.1, ⟨output.2⟩⟩
      invFun := fun occurrence => ⟨occurrence.target, occurrence.derivation.down⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- The native primitive capabilities of a finite fact world. -/
def primitiveProviders [Fintype Atom] (base : List (GroundFact Symbol Atom)) :
    PrimitiveFiniteSearchProviders (signature.vocabulary Atom base) where
  provide := fun symbol => ⟨signature.primitiveFibre base symbol⟩

end FactSignature

/-! ## Explanations -/

/-- The explanation carried by an answer, as the native runtime prints it:
a fact proof, or a chain step through a middle atom. -/
inductive ProofTerm (Symbol Atom : Type) where
  | fact (fact : GroundFact Symbol Atom)
  | chain (middle : Atom) (earlier later : ProofTerm Symbol Atom)
  deriving DecidableEq, Repr

/-- An answer with its explanation. -/
structure Edge (Symbol Atom : Type) where
  target : Atom
  proof : ProofTerm Symbol Atom
  deriving DecidableEq, Repr

namespace ProofTerm

variable {Symbol Atom : Type}

/-- The facts an explanation rests on. -/
def premises : ProofTerm Symbol Atom → List (GroundFact Symbol Atom)
  | .fact ground => [ground]
  | .chain _ earlier later => earlier.premises ++ later.premises

/-- The middle atom of the outermost chain step. -/
def middle : ProofTerm Symbol Atom → Option Atom
  | .fact _ => none
  | .chain middle _ _ => some middle

end ProofTerm

/-- The middle atom through which an answer was reached. -/
def Edge.middle {Symbol Atom : Type} (edge : Edge Symbol Atom) : Option Atom :=
  edge.proof.middle

namespace FactSignature

variable {SortCode Symbol Atom : Type} (signature : FactSignature SortCode Symbol)

/-- Render proof-relevant evidence as its explanation. -/
def explain {base : List (GroundFact Symbol Atom)} :
    {source target : SortCode} →
      (hypothesis : Hypothesis (signature.vocabulary Atom base) source target) →
        (input output : Atom) → hypothesis.denote.evidence input output →
          ProofTerm Symbol Atom
  | _, _, .primitive symbol, input, output, _ =>
      .fact ⟨signature.symbolOf symbol, input, output⟩
  | _, _, .chain earlier later, input, output, evidence =>
      .chain evidence.1 (explain earlier input evidence.1 evidence.2.1)
        (explain later evidence.1 output evidence.2.2)

/-- The edge printed for an answer occurrence. -/
def edgeOf {base : List (GroundFact Symbol Atom)} {source target : SortCode}
    (hypothesis : Hypothesis (signature.vocabulary Atom base) source target)
    (input : Atom) (occurrence : AnswerOccurrence hypothesis.denote input) :
    Edge Symbol Atom :=
  ⟨occurrence.target, signature.explain hypothesis input occurrence.target
    occurrence.derivation⟩

/-- The symbols a hypothesis mentions. -/
def symbols {base : List (GroundFact Symbol Atom)} :
    {source target : SortCode} →
      Hypothesis (signature.vocabulary Atom base) source target → List Symbol
  | _, _, .primitive symbol => [signature.symbolOf symbol]
  | _, _, .chain earlier later => symbols earlier ++ symbols later

/-- Every premise of an explanation is a fact of the base it was derived in. -/
theorem explain_premises_mem {base : List (GroundFact Symbol Atom)} :
    {source target : SortCode} →
      (hypothesis : Hypothesis (signature.vocabulary Atom base) source target) →
        (input output : Atom) → (evidence : hypothesis.denote.evidence input output) →
          ∀ fact ∈ (signature.explain hypothesis input output evidence).premises, fact ∈ base
  | _, _, .primitive _, _, _, evidence, fact, present => by
      rw [List.mem_singleton.1 present]
      exact PLift.down evidence
  | _, _, .chain earlier later, _, _, evidence, fact, present => by
      rcases List.mem_append.1 present with present | present
      · exact explain_premises_mem earlier _ _ evidence.2.1 fact present
      · exact explain_premises_mem later _ _ evidence.2.2 fact present

/-- Every premise of an explanation has a symbol that the hypothesis
mentions. -/
theorem explain_premises_symbol {base : List (GroundFact Symbol Atom)} :
    {source target : SortCode} →
      (hypothesis : Hypothesis (signature.vocabulary Atom base) source target) →
        (input output : Atom) → (evidence : hypothesis.denote.evidence input output) →
          ∀ fact ∈ (signature.explain hypothesis input output evidence).premises,
            fact.symbol ∈ signature.symbols hypothesis
  | _, _, .primitive _, _, _, _, fact, present => by
      rw [List.mem_singleton.1 present]
      exact List.mem_singleton_self _
  | _, _, .chain earlier later, _, _, evidence, fact, present => by
      rcases List.mem_append.1 present with present | present
      · exact List.mem_append_left _ (explain_premises_symbol earlier _ _ evidence.2.1 fact present)
      · exact List.mem_append_right _ (explain_premises_symbol later _ _ evidence.2.2 fact present)

/-! ### The facts a hypothesis reads -/

variable [DecidableEq Symbol] [DecidableEq Atom]

/-- The facts a hypothesis reads: those whose symbol it mentions. -/
def reads {base : List (GroundFact Symbol Atom)} {source target : SortCode}
    (hypothesis : Hypothesis (signature.vocabulary Atom base) source target)
    (fact : GroundFact Symbol Atom) : Bool :=
  decide (fact.symbol ∈ signature.symbols hypothesis)

/-- An occurrence is still valid at a revision when every premise of its
explanation is still a fact. -/
def stillValid {base : List (GroundFact Symbol Atom)} {source target : SortCode}
    (hypothesis : Hypothesis (signature.vocabulary Atom base) source target)
    (revision : List (GroundFact Symbol Atom)) (input : Atom)
    (occurrence : AnswerOccurrence hypothesis.denote input) : Bool :=
  (signature.explain hypothesis input occurrence.target occurrence.derivation).premises.all
    fun fact => decide (fact ∈ revision)

/-- Every occurrence is valid in the base it was derived in. -/
theorem stillValid_self {base : List (GroundFact Symbol Atom)} {source target : SortCode}
    (hypothesis : Hypothesis (signature.vocabulary Atom base) source target)
    (input : Atom) (occurrence : AnswerOccurrence hypothesis.denote input) :
    signature.stillValid hypothesis base input occurrence = true :=
  List.all_eq_true.2 fun fact present =>
    decide_eq_true (signature.explain_premises_mem hypothesis input occurrence.target
      occurrence.derivation fact present)

end FactSignature

/-- The per-fact dependency view: revisions are fact bases, a dependency is a
selected fact, and its value is whether the base contains it. -/
def factDependencies (Symbol Atom : Type) [DecidableEq Symbol] [DecidableEq Atom]
    (selects : GroundFact Symbol Atom → Bool) : DependencySystem where
  Revision := List (GroundFact Symbol Atom)
  Dependency := {fact : GroundFact Symbol Atom // selects fact = true}
  Value := Bool
  read base fact := decide (fact.1 ∈ base)

/-- Two bases with the same selected facts have the same dependencies. -/
theorem sameDependencies_of_filter_eq {Symbol Atom : Type} [DecidableEq Symbol]
    [DecidableEq Atom] {selects : GroundFact Symbol Atom → Bool}
    {first second : List (GroundFact Symbol Atom)}
    (same : first.filter selects = second.filter selects) :
    (factDependencies Symbol Atom selects).SameDependencies first second := by
  rintro ⟨fact, selected⟩
  change decide (fact ∈ first) = decide (fact ∈ second)
  have member : fact ∈ first ↔ fact ∈ second := by
    constructor
    · intro present
      have filtered : fact ∈ first.filter selects := List.mem_filter.2 ⟨present, selected⟩
      rw [same] at filtered
      exact (List.mem_filter.1 filtered).1
    · intro present
      have filtered : fact ∈ second.filter selects := List.mem_filter.2 ⟨present, selected⟩
      rw [← same] at filtered
      exact (List.mem_filter.1 filtered).1
  exact decide_eq_decide.2 member

namespace FactSignature

variable {SortCode Symbol Atom : Type} (signature : FactSignature SortCode Symbol)
variable [DecidableEq Symbol] [DecidableEq Atom]

/-- Validity at a revision depends only on the facts the hypothesis reads. -/
theorem stillValid_congr {base : List (GroundFact Symbol Atom)} {source target : SortCode}
    (hypothesis : Hypothesis (signature.vocabulary Atom base) source target)
    {first second : List (GroundFact Symbol Atom)}
    (same : (factDependencies Symbol Atom (signature.reads hypothesis)).SameDependencies
      first second) :
    signature.stillValid hypothesis first = signature.stillValid hypothesis second := by
  funext input occurrence
  have agree : ∀ fact ∈ (signature.explain hypothesis input occurrence.target
      occurrence.derivation).premises, fact ∈ first ↔ fact ∈ second := by
    intro fact present
    have read : decide (fact ∈ first) = decide (fact ∈ second) :=
      same ⟨fact, decide_eq_true (signature.explain_premises_symbol hypothesis input
        occurrence.target occurrence.derivation fact present)⟩
    exact decide_eq_decide.1 read
  apply Bool.eq_iff_iff.2
  simp only [stillValid, List.all_eq_true, decide_eq_true_eq]
  exact ⟨fun valid fact present => (agree fact present).1 (valid fact present),
    fun valid fact present => (agree fact present).2 (valid fact present)⟩

end FactSignature

/-! ## Revalidating retained native results -/

section Revalidation

variable {Source Target : Type} {relation : ProofRel Source Target}
variable {dependencies : DependencySystem}

/-- Keep the occurrences of a retained native result that are still valid. -/
def revalidate (validNow : (source : Source) → AnswerOccurrence relation source → Bool)
    (receipt : NativeSearchReceipt relation) : NativeSearchReceipt relation where
  face := receipt.face
  result :=
    ⟨receipt.result.source,
      receipt.result.answers.filter fun occurrence =>
        validNow receipt.result.source occurrence = true⟩

/-- Revalidation keeps a result all of whose occurrences are valid. -/
theorem revalidate_of_valid
    {validNow : (source : Source) → AnswerOccurrence relation source → Bool}
    (allValid : ∀ source occurrence, validNow source occurrence = true)
    (receipt : NativeSearchReceipt relation) :
    revalidate validNow receipt = receipt := by
  obtain ⟨face, source, answers⟩ := receipt
  change (⟨face, ⟨source, answers.filter fun occurrence =>
    validNow source occurrence = true⟩⟩ : NativeSearchReceipt relation) =
      ⟨face, ⟨source, answers⟩⟩
  rw [Multiset.filter_eq_self.2 fun occurrence _ => allValid source occurrence]

variable {family : PolicyFamily (NativeSearchReceipt relation)}

/-- The live meaning of a policy on a retained result at a revision: the
policy applied to the occurrences that are still valid there. -/
def revalidatedLive
    (valid : dependencies.Revision → (source : Source) →
      AnswerOccurrence relation source → Bool) :
    dependencies.Revision → (policy : family.Policy) → NativeSearchReceipt relation →
      family.Result policy :=
  fun revision policy receipt => family.decide policy (revalidate (valid revision) receipt)

/-- If every occurrence is valid at the admitted revision, revalidation there
is the retained meaning. -/
theorem revalidatedLive_retained
    (valid : dependencies.Revision → (source : Source) →
      AnswerOccurrence relation source → Bool)
    (admitted : dependencies.Revision)
    (allValid : ∀ source occurrence, valid admitted source occurrence = true) :
    RetainedMeaning (family := family) (revalidatedLive valid) admitted := by
  intro policy receipt
  change family.decide policy receipt =
    family.decide policy (revalidate (valid admitted) receipt)
  rw [revalidate_of_valid allValid]

/-- If validity depends only on the selected dependencies, so does the
revalidated live meaning. -/
theorem revalidatedLive_adequate
    (valid : dependencies.Revision → (source : Source) →
      AnswerOccurrence relation source → Bool)
    (reads : ∀ first second, dependencies.SameDependencies first second →
      valid first = valid second) :
    DependenciesAdequate (family := family) (revalidatedLive valid) := by
  intro first second same policy receipt
  change family.decide policy (revalidate (valid first) receipt) =
    family.decide policy (revalidate (valid second) receipt)
  rw [reads first second same]

end Revalidation

/-! ## Learned predicates -/

universe uSort uCarrier uPrimitive

/-- Positive and negative examples of a relation. -/
structure Examples (Source Target : Type uCarrier) where
  positive : List (Source × Target)
  negative : List (Source × Target)

/-- A proof-relevant relation is consistent with examples when every positive
example has evidence and no negative example has any. -/
def Examples.ConsistentWith {Source Target : Type uCarrier}
    (examples : Examples Source Target) (relation : ProofRel Source Target) : Prop :=
  (∀ pair ∈ examples.positive, Nonempty (relation.evidence pair.1 pair.2)) ∧
    ∀ pair ∈ examples.negative, IsEmpty (relation.evidence pair.1 pair.2)

/-- A learned predicate, retained with the examples it was learned from. -/
structure LearnedPredicate (vocabulary : Vocabulary.{uSort, uCarrier, uPrimitive})
    (source target : vocabulary.SortCode) where
  hypothesis : Hypothesis vocabulary source target
  examples : Examples (vocabulary.Carrier source) (vocabulary.Carrier target)
  consistent : examples.ConsistentWith hypothesis.denote

/-! ## The client world -/

namespace Client

/-- The atoms of the native fixture, in its declaration order. -/
inductive Entity where
  | alice
  | bob
  | carol
  | eve
  | zero
  | one
  deriving DecidableEq, Repr

/-- The atoms, enumerated by the interpreted route in this order. -/
def atoms : List Entity := [.alice, .bob, .carol, .eve, .zero, .one]

theorem atoms_nodup : atoms.Nodup := by decide

theorem atoms_complete : ∀ entity, entity ∈ atoms := by
  intro entity
  cases entity <;> decide

instance : Fintype Entity where
  elems := ⟨atoms, atoms_nodup⟩
  complete := atoms_complete

inductive SortCode where
  | person
  | number
  deriving DecidableEq, Repr

inductive Symbol where
  | mother
  | father
  | successor
  deriving DecidableEq, Repr

inductive Primitive : SortCode → SortCode → Type where
  | mother : Primitive .person .person
  | father : Primitive .person .person
  | successor : Primitive .number .number

def Primitive.symbol : {source target : SortCode} → Primitive source target → Symbol
  | _, _, .mother => .mother
  | _, _, .father => .father
  | _, _, .successor => .successor

abbrev signature : FactSignature SortCode Symbol where
  Primitive := Primitive
  symbolOf := Primitive.symbol

abbrev Fact := GroundFact Symbol Entity

def motherAliceBob : Fact := ⟨.mother, .alice, .bob⟩
def motherAliceEve : Fact := ⟨.mother, .alice, .eve⟩
def fatherBobCarol : Fact := ⟨.father, .bob, .carol⟩
def fatherEveCarol : Fact := ⟨.father, .eve, .carol⟩
def successorZeroOne : Fact := ⟨.successor, .zero, .one⟩

/-- The world of the native fixture, in its authored order. -/
def snapshot : List Fact :=
  [motherAliceBob, motherAliceEve, fatherBobCarol, fatherEveCarol, successorZeroOne]

abbrev vocabulary (base : List Fact) : Vocabulary := signature.vocabulary Entity base

/-- The learned chain: mother, then father. -/
def learned (base : List Fact) : Hypothesis (vocabulary base) SortCode.person SortCode.person :=
  .chain (.primitive Primitive.mother) (.primitive Primitive.father)

/-- The learned relation on the snapshot. -/
abbrev relation : ProofRel Entity Entity := (learned snapshot).denote

/-- The fixture's examples: (alice, carol) positive, (alice, bob) negative. -/
def examples : Examples Entity Entity := ⟨[(.alice, .carol)], [(.alice, .bob)]⟩

theorem no_father_of_bob : ∀ middle : Entity, (⟨.father, middle, .bob⟩ : Fact) ∉ snapshot := by
  decide

/-- The learned predicate, with its examples. -/
def learnedPredicate : LearnedPredicate (vocabulary snapshot) SortCode.person SortCode.person where
  hypothesis := learned snapshot
  examples := examples
  consistent := by
    constructor
    · intro pair member
      rw [List.mem_singleton.1 member]
      exact ⟨⟨Entity.bob, ⟨by decide⟩, ⟨by decide⟩⟩⟩
    · intro pair member
      rw [List.mem_singleton.1 member]
      refine ⟨fun evidence => ?_⟩
      exact no_father_of_bob evidence.1 (PLift.down evidence.2.2)

/-! ### The learned predicate as a typed candidate program -/

section Quotation

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Declaration
open MILCheckedNativePrograms.FormedQuotationCanary (contextSPS contextSPSWellFormed)

/-- The family parameters and the person sort, then the number sort. -/
def contextNumber : Tower.Ctx 4 := .snoc contextSPS (.var 2)

/-- Then `mother : P person person`. -/
def contextMother : Tower.Ctx 5 := .snoc contextNumber (.app (.app (.var 2) (.var 1)) (.var 1))

/-- Then `father : P person person`. -/
def contextFather : Tower.Ctx 6 := .snoc contextMother (.app (.app (.var 3) (.var 2)) (.var 2))

/-- Then `successor : P number number`: the fixture's full vocabulary. -/
def contextSuccessor : Tower.Ctx 7 :=
  .snoc contextFather (.app (.app (.var 4) (.var 2)) (.var 2))

theorem contextNumber_wellFormed :
    ContextWellFormed IntrinsicMILHypothesis.rules contextNumber := by
  apply ContextWellFormed.snoc
  · exact contextSPSWellFormed
  · exact Presentation.HasType.var 2
  · exact .sort IntrinsicMILHypothesis.sortLevel

theorem contextMother_wellFormed :
    ContextWellFormed IntrinsicMILHypothesis.rules contextMother := by
  apply ContextWellFormed.snoc
  · exact contextNumber_wellFormed
  · apply IntrinsicMILHypothesis.primitiveFamilyApp_hasType
    · exact Presentation.HasType.var 2
    · exact Presentation.HasType.var 1
    · exact Presentation.HasType.var 1
  · exact .sort IntrinsicMILHypothesis.primitiveLevel

theorem contextFather_wellFormed :
    ContextWellFormed IntrinsicMILHypothesis.rules contextFather := by
  apply ContextWellFormed.snoc
  · exact contextMother_wellFormed
  · apply IntrinsicMILHypothesis.primitiveFamilyApp_hasType
    · exact Presentation.HasType.var 3
    · exact Presentation.HasType.var 2
    · exact Presentation.HasType.var 2
  · exact .sort IntrinsicMILHypothesis.primitiveLevel

theorem contextSuccessor_wellFormed :
    ContextWellFormed IntrinsicMILHypothesis.rules contextSuccessor := by
  apply ContextWellFormed.snoc
  · exact contextFather_wellFormed
  · apply IntrinsicMILHypothesis.primitiveFamilyApp_hasType
    · exact Presentation.HasType.var 4
    · exact Presentation.HasType.var 2
    · exact Presentation.HasType.var 2
  · exact .sort IntrinsicMILHypothesis.primitiveLevel

/-- The fixture's vocabulary quoted into a formed context of the candidate's
intrinsic `Hyp` family. -/
def quotation (base : List Fact) :
    MILCheckedNativePrograms.FormedVocabularyQuotation (vocabulary base) contextSuccessor where
  sorts := .var 6
  primitives := .var 5
  sortCode := fun sort =>
    match sort with
    | .person => .var 4
    | .number => .var 3
  primitiveCode := fun symbol =>
    match symbol with
    | .mother => .var 2
    | .father => .var 1
    | .successor => .var 0
  sortsTyping := Presentation.HasType.var 6
  primitivesTyping := Presentation.HasType.var 5
  sortCodeTyping := by
    intro sort
    cases sort with
    | person => exact Presentation.HasType.var 4
    | number => exact Presentation.HasType.var 3
  primitiveCodeTyping := by
    intro source target symbol
    cases symbol with
    | mother => exact Presentation.HasType.var 2
    | father => exact Presentation.HasType.var 1
    | successor => exact Presentation.HasType.var 0
  contextWellFormed := contextSuccessor_wellFormed

end Quotation

/-- The learned chain as an intrinsic program over the quoted vocabulary. -/
def program (base : List Fact) :=
  IntrinsicMILSemanticAdequacy.Program.ofHypothesis (quotation base).toTypedVocabularyQuotation
    (learned base)

/-! ### The native route and its admitted selection -/

/-- The native provider, derived structurally from the primitive fibres. -/
noncomputable def provider : FiniteEvidenceProvider relation :=
  programFiniteSearchProvider (signature.primitiveProviders snapshot) (program snapshot)

/-- The facts the learned chain reads. -/
abbrev chainReads : Fact → Bool := signature.reads (learned snapshot)

/-- Revisions are fact bases; a dependency is a fact the chain reads. -/
abbrev dependencies : DependencySystem := factDependencies Symbol Entity chainReads

/-- The native search and its exact-result and count policies, admitted at the
snapshot. -/
noncomputable def selected := selectedAt provider dependencies snapshot

theorem active : selected.Active snapshot :=
  selected.activate (dependencies.sameDependencies_refl snapshot)

/-- The native result for alice, computed at the snapshot. -/
noncomputable def receipt : NativeSearchReceipt relation := selected.operation.run Entity.alice

noncomputable def prepared : selected.Prepared := selected.prepare Entity.alice receipt

noncomputable def exactPolicy := exactResultPolicy provider

noncomputable def countPolicy := occurrenceCountPolicy provider

/-! ### The interpreted route -/

def interpreted (base : List Fact) (input : Entity) :
    List (AnswerOccurrence (learned base).denote input) :=
  signature.interpret atoms base (learned base) input

/-- The derivation of carol through bob. -/
def throughBob : AnswerOccurrence relation Entity.alice :=
  ⟨Entity.carol, ⟨Entity.bob, ⟨by decide⟩, ⟨by decide⟩⟩⟩

/-- The derivation of carol through eve. -/
def throughEve : AnswerOccurrence relation Entity.alice :=
  ⟨Entity.carol, ⟨Entity.eve, ⟨by decide⟩, ⟨by decide⟩⟩⟩

theorem interpreted_alice : interpreted snapshot Entity.alice = [throughBob, throughEve] :=
  rfl

abbrev ClientEdge := Edge Symbol Entity

/-- The answers of a query at a base, as printed edges. -/
def edges (base : List Fact) (input : Entity) : List ClientEdge :=
  (interpreted base input).map (signature.edgeOf (learned base) input)

/-- `(hyp:edge carol (hyp:chain-proof bob (hyp:primitive-proof mother-symbol
mother-alice-bob) (hyp:primitive-proof father-symbol father-bob-carol)))` -/
def edgeThroughBob : ClientEdge :=
  ⟨.carol, .chain .bob (.fact motherAliceBob) (.fact fatherBobCarol)⟩

/-- The same answer through eve. -/
def edgeThroughEve : ClientEdge :=
  ⟨.carol, .chain .eve (.fact motherAliceEve) (.fact fatherEveCarol)⟩

theorem edges_alice : edges snapshot Entity.alice = [edgeThroughBob, edgeThroughEve] := by
  decide

/-- The native bag for alice is the interpreted bag. -/
theorem native_answers :
    provider.answers Entity.alice = Multiset.ofList (interpreted snapshot Entity.alice) :=
  signature.nativeAnswers_eq_interpret atoms_nodup atoms_complete snapshot (learned snapshot)
    provider Entity.alice

theorem receipt_answers :
    receipt.result.answers = Multiset.ofList (interpreted snapshot Entity.alice) :=
  native_answers

/-! ### Step 1: the learned predicate, its examples and its support -/

/-- The derivations supporting an example: the interpreted answers at its
source that reach its target. -/
def support (base : List Fact) (pair : Entity × Entity) :
    List (AnswerOccurrence (learned base).denote pair.1) :=
  (interpreted base pair.1).filter fun occurrence => decide (occurrence.target = pair.2)

/-- The learned predicate is consistent with its examples and is a typed
program of the candidate's `Hyp` family in the formed context.  Its support
for the positive example (alice, carol) is exactly two derivations, through
bob and through eve, printed with their fact proofs, and it contains every
derivation of that example. -/
theorem learned_predicate_examples_and_support :
    learnedPredicate.examples.ConsistentWith learnedPredicate.hypothesis.denote ∧
      IntrinsicMILHypothesis.HasType contextSuccessor
        (IntrinsicMILHypothesis.quoteHypothesis (quotation snapshot).toTypedVocabularyQuotation
          (learned snapshot))
        ((quotation snapshot).hypothesisType SortCode.person SortCode.person).code ∧
      support snapshot (Entity.alice, Entity.carol) = [throughBob, throughEve] ∧
      (support snapshot (Entity.alice, Entity.carol)).map
          (signature.edgeOf (learned snapshot) Entity.alice) =
        [edgeThroughBob, edgeThroughEve] ∧
      ∀ evidence : relation.evidence Entity.alice Entity.carol,
        (⟨Entity.carol, evidence⟩ : AnswerOccurrence relation Entity.alice) ∈
          support snapshot (Entity.alice, Entity.carol) := by
  refine ⟨learnedPredicate.consistent, (program snapshot).hasType, rfl, by decide, ?_⟩
  intro evidence
  exact List.mem_filter.2
    ⟨signature.mem_interpret atoms_complete snapshot (learned snapshot) Entity.alice
      ⟨Entity.carol, evidence⟩, decide_eq_true rfl⟩

/-! ### Step 2: the interpreted and the represented native route agree -/

/-- On the snapshot, the admitted native search, the represented GSLT-IL
route it runs, and the interpreted route give the same occurrence bag; the
interpreted route orders it through bob, then eve, as the native fixture
prints it. -/
theorem interpreted_route_agrees_with_native_route :
    (active.run Entity.alice).result.answers =
        Multiset.ofList (interpreted snapshot Entity.alice) ∧
      (provider.representedRoute.representation.map Entity.alice).answers =
        Multiset.ofList (interpreted snapshot Entity.alice) ∧
      (active.run Entity.alice).face = .finiteSearch ∧
      edges snapshot Entity.alice = [edgeThroughBob, edgeThroughEve] :=
  ⟨native_answers, native_answers, rfl, edges_alice⟩

/-- The admitted run observed through its retained count policy: two
occurrences. -/
theorem native_count_observation : @Eq Nat (runObserved active Entity.alice countPolicy).2 2 := by
  change receipt.result.answers.card = 2
  rw [receipt_answers]
  decide

/-! ### Step 3: a cheap guard before an expensive valuation -/

/-- The cheap guard of the query: the answer is carol. -/
def reachesCarol (edge : ClientEdge) : Bool := decide (edge.target = Entity.carol)

/-- A guard that admits one of the two occurrences. -/
def viaBob (edge : ClientEdge) : Bool := decide (edge.middle = some Entity.bob)

/-- The expensive valuation: score an answer by its middle and target. -/
def score (edge : ClientEdge) : Option Entity × Entity := (edge.middle, edge.target)

/-- Hoisting the carol guard preserves the ordered occurrences, both typed
derivations and printed edges, including the duplicate answer carol. -/
theorem carol_guard_hoisting_keeps_duplicate :
    valueThenGuard reachesCarol score (edges snapshot Entity.alice) =
        guardThenValue reachesCarol score (edges snapshot Entity.alice) ∧
      (guardThenValue reachesCarol score (edges snapshot Entity.alice)).map
          ValuedOccurrence.occurrence = [edgeThroughBob, edgeThroughEve] ∧
      (guardThenValue reachesCarol score (edges snapshot Entity.alice)).map
          ValuedOccurrence.value =
        [(some Entity.bob, Entity.carol), (some Entity.eve, Entity.carol)] ∧
      valueThenGuard (fun occurrence => decide (occurrence.target = Entity.carol))
          (signature.edgeOf (learned snapshot) Entity.alice) (interpreted snapshot Entity.alice) =
        guardThenValue (fun occurrence => decide (occurrence.target = Entity.carol))
          (signature.edgeOf (learned snapshot) Entity.alice) (interpreted snapshot Entity.alice) ∧
      (guardThenValue (fun occurrence => decide (occurrence.target = Entity.carol))
          (signature.edgeOf (learned snapshot) Entity.alice)
          (interpreted snapshot Entity.alice)).map ValuedOccurrence.occurrence =
        [throughBob, throughEve] :=
  ⟨hoist_guard _ _ _, by decide, by decide, hoist_guard _ _ _, rfl⟩

/-- With a guard that rejects one occurrence, hoisting keeps the answer and
values one occurrence instead of two, the fixture's `(valuations 2 1)`. -/
theorem bob_guard_hoisting_saves_valuation :
    valueThenGuard viaBob score (edges snapshot Entity.alice) =
        guardThenValue viaBob score (edges snapshot Entity.alice) ∧
      (guardThenValue viaBob score (edges snapshot Entity.alice)).map ValuedOccurrence.value =
        [(some Entity.bob, Entity.carol)] ∧
      eagerCharge (fun _ => (0 : Nat)) (fun _ => 1) (edges snapshot Entity.alice) = 2 ∧
      guardedCharge viaBob (fun _ => (0 : Nat)) (fun _ => 1) (edges snapshot Entity.alice) = 1 :=
  ⟨hoist_guard _ _ _, by decide, by decide, by decide⟩

/-- The resource inequality of the client, for every canonically ordered
additive cost of guarding and valuation. -/
theorem client_hoist_charge_le {Cost : Type*} [AddCommMonoid Cost] [LE Cost]
    [CanonicallyOrderedAdd Cost] (guard : ClientEdge → Bool)
    (guardCost valueCost : ClientEdge → Cost) (input : Entity) :
    guardedCharge guard guardCost valueCost (edges snapshot input) ≤
      eagerCharge guardCost valueCost (edges snapshot input) :=
  hoist_charge_le guard guardCost valueCost (edges snapshot input)

/-! ### Step 4: every finite prefix of a stream of batches -/

/-- The batch of one query: its interpreted answers, as edges. -/
def batch (input : Entity) : List ClientEdge := edges snapshot input

/-- For every stream of queries, guard and valuation, every finite requested
prefix of the hoisted stream of batches is the eager one. -/
theorem batch_stream_prefixes_agree (queries : Nat → Entity) (guard : ClientEdge → Bool)
    {Value : Type} (value : ClientEdge → Value) (demand : Nat) :
    streamPrefix (fun epoch => valueThenGuard guard value (batch (queries epoch))) demand =
      streamPrefix (fun epoch => guardThenValue guard value (batch (queries epoch))) demand :=
  streamPrefix_hoist_guard guard value (fun epoch => batch (queries epoch)) demand

/-- The fixture's queries: alice, bob, alice, bob, and so on. -/
def alternating (epoch : Nat) : Entity := if epoch % 2 = 0 then Entity.alice else Entity.bob

/-- The fixture's prefix `(alice bob alice)`: `(((scored bob carol)) ()
((scored bob carol)))`. -/
theorem fixture_stream_prefix :
    streamPrefix (fun epoch =>
        (guardThenValue viaBob score (batch (alternating epoch))).map ValuedOccurrence.value) 3 =
      [[(some Entity.bob, Entity.carol)], [], [(some Entity.bob, Entity.carol)]] := by
  decide

/-! ### Step 5: revisions, invalidation and reuse -/

/-- The snapshot without successor(zero, one): a revision the chain does not
read. -/
def withoutSuccessor : List Fact := snapshot.erase successorZeroOne

/-- The snapshot without father(eve, carol): a revision the chain reads. -/
def withoutFatherEveCarol : List Fact := snapshot.erase fatherEveCarol

/-- The requested policy family: the exact result and the occurrence count. -/
noncomputable abbrev family := (receiptRequest provider).requestedFamily

/-- The live meaning of the retained policies at a fact base: the retained
native result, restricted to the derivations whose facts still hold there. -/
noncomputable abbrev live :
    dependencies.Revision → (policy : family.Policy) → NativeSearchReceipt relation →
      family.Result policy :=
  revalidatedLive (signature.stillValid (learned snapshot))

theorem live_retained : RetainedMeaning live snapshot :=
  revalidatedLive_retained (dependencies := dependencies) (family := family)
    (signature.stillValid (learned snapshot)) snapshot
    (signature.stillValid_self (learned snapshot))

theorem live_adequate : DependenciesAdequate live :=
  revalidatedLive_adequate (signature.stillValid (learned snapshot))
    fun _ _ same => signature.stillValid_congr (learned snapshot) same

theorem successor_revision_keeps_dependencies :
    dependencies.SameDependencies snapshot withoutSuccessor :=
  sameDependencies_of_filter_eq (by decide)

theorem active_without_successor : selected.Active withoutSuccessor :=
  selected.activate successor_revision_keeps_dependencies

/-- Revising successor(zero, one) keeps the chain's dependencies: the admitted
selection stays active, its retained runners give the live meaning at the
revised base, and the interpreted answer there is the cached one. -/
theorem successor_revision_reuses :
    dependencies.SameDependencies snapshot withoutSuccessor ∧
      selected.Active withoutSuccessor ∧
      (∀ policy, active_without_successor.policyActive.runPrepared prepared.policyState policy =
        live withoutSuccessor policy prepared.policyState.state) ∧
      edges withoutSuccessor Entity.alice = edges snapshot Entity.alice :=
  ⟨successor_revision_keeps_dependencies, active_without_successor,
    fun policy => active_without_successor.policyActive.runPrepared_live live live_retained
      live_adequate prepared.policyState policy,
    by decide⟩

theorem father_revision_stale : selected.StaleAt withoutFatherEveCarol := by
  intro same
  have read : decide (fatherEveCarol ∈ snapshot) =
      decide (fatherEveCarol ∈ withoutFatherEveCarol) :=
    same ⟨fatherEveCarol, by decide⟩
  exact absurd read (by decide)

/-- The live occurrence count of the retained result at a base. -/
noncomputable def liveCount (base : List Fact) : Nat := live base countPolicy receipt

/-- It counts the valid part of the interpreted bag. -/
theorem liveCount_eq (base : List Fact) :
    liveCount base =
      ((Multiset.ofList (interpreted snapshot Entity.alice)).filter fun occurrence =>
        signature.stillValid (learned snapshot) base Entity.alice occurrence = true).card := by
  change (receipt.result.answers.filter fun occurrence =>
    signature.stillValid (learned snapshot) base Entity.alice occurrence = true).card = _
  rw [receipt_answers]

theorem liveCount_snapshot : liveCount snapshot = 2 := by
  rw [liveCount_eq]
  decide

theorem liveCount_without_father : liveCount withoutFatherEveCarol = 1 := by
  rw [liveCount_eq]
  decide

/-- Removing father(eve, carol) changes a fact the chain reads: the selection
is stale, the raw query and complete native result survive as fallback, the
recomputed answer has one occurrence, and the live count of the retained
result falls from two to one. -/
theorem father_revision_invalidates :
    selected.StaleAt withoutFatherEveCarol ∧
      (¬ selected.Active withoutFatherEveCarol ∧
        prepared.fallback = (Entity.alice, receipt)) ∧
      edges withoutFatherEveCarol Entity.alice = [edgeThroughBob] ∧
      edges withoutFatherEveCarol Entity.alice ≠ edges snapshot Entity.alice ∧
      liveCount snapshot = 2 ∧ liveCount withoutFatherEveCarol = 1 :=
  ⟨father_revision_stale,
    selected.stale_prevents_activation_and_preserves_fallback father_revision_stale prepared,
    by decide, by decide, liveCount_snapshot, liveCount_without_father⟩

/-- On both revisions, revalidating the retained native result gives the
answers recomputed by the interpreted route there. -/
theorem revalidation_matches_recomputation :
    (revalidate (signature.stillValid (learned snapshot) withoutSuccessor) receipt).result.answers.map
        (signature.edgeOf (learned snapshot) Entity.alice) =
      Multiset.ofList (edges withoutSuccessor Entity.alice) ∧
    (revalidate (signature.stillValid (learned snapshot) withoutFatherEveCarol)
        receipt).result.answers.map (signature.edgeOf (learned snapshot) Entity.alice) =
      Multiset.ofList (edges withoutFatherEveCarol Entity.alice) := by
  constructor
  · change (receipt.result.answers.filter fun occurrence =>
      signature.stillValid (learned snapshot) withoutSuccessor Entity.alice occurrence =
        true).map (signature.edgeOf (learned snapshot) Entity.alice) = _
    rw [receipt_answers]
    decide
  · change (receipt.result.answers.filter fun occurrence =>
      signature.stillValid (learned snapshot) withoutFatherEveCarol Entity.alice occurrence =
        true).map (signature.edgeOf (learned snapshot) Entity.alice) = _
    rw [receipt_answers]
    decide

/-- A stale guard: a dependency selection that omits father(eve, carol), a
fact the chain reads. -/
def omitsFatherEveCarol (fact : Fact) : Bool := chainReads fact && !(fact == fatherEveCarol)

abbrev omittingDependencies : DependencySystem :=
  factDependencies Symbol Entity omitsFatherEveCarol

/-- The omitting selection sees no change when father(eve, carol) is removed,
while the live count changes: one collision refutes its adequacy. -/
theorem omitted_dependency_refuted :
    ¬ DependenciesAdequate (dependencies := omittingDependencies) (family := family)
      (revalidatedLive (signature.stillValid (learned snapshot))) :=
  not_dependenciesAdequate_of_collision _ (first := snapshot) (second := withoutFatherEveCarol)
    (sameDependencies_of_filter_eq (by decide)) countPolicy receipt (by
      change liveCount snapshot ≠ liveCount withoutFatherEveCarol
      rw [liveCount_snapshot, liveCount_without_father]
      decide)

/-! ### Step 6: observers of the answers -/

/-- Exact results and occurrence counts factor through the readout retained by
the admitted selection. -/
theorem exact_and_count_factor_through_retained_readout :
    Factors ((resultOnlyCatalog relation).readout selected.candidate)
        (fun receipt : NativeSearchReceipt relation => receipt.result) ∧
      Factors ((resultOnlyCatalog relation).readout selected.candidate)
        (fun receipt : NativeSearchReceipt relation => receipt.result.answers.card) := by
  have vector := selected.policyAdmission.realization.vectorFactors
  exact ⟨vector.post fun answers => answers exactPolicy,
    vector.post fun answers => answers countPolicy⟩

/-- Which middle an answer went through. -/
def middleOf (occurrence : AnswerOccurrence relation Entity.alice) : Entity :=
  occurrence.derivation.1

/-- The two derivations of carol have the same value and different middles. -/
def explanationFiber :
    NonTrivialFiber (fun occurrence : AnswerOccurrence relation Entity.alice => occurrence.target)
      middleOf where
  left := throughBob
  right := throughEve
  sameShadow := rfl
  differentValue := by decide

/-- An explanation observer is not served by values alone. -/
theorem explanation_not_factors_through_values :
    ¬ Factors (fun occurrence : AnswerOccurrence relation Entity.alice => occurrence.target)
      middleOf :=
  explanationFiber.not_factors

/-- It is served once the support is retained with the value. -/
theorem explanation_factors_with_support :
    Factors (fun occurrence : AnswerOccurrence relation Entity.alice =>
      (occurrence.target, middleOf occurrence)) middleOf :=
  factors_retain _ _

/-- The occurrence-count observer alone. -/
noncomputable def countFamily : PolicyFamily (NativeSearchReceipt relation) :=
  (receiptPolicies relation).reindex fun _ : Unit => ReceiptPolicy.occurrenceCount

/-- The answer values, with their duplicates. -/
def targetsOf (receipt : NativeSearchReceipt relation) : Multiset Entity :=
  receipt.result.answers.map (·.target)

/-- The answer values, with duplicates removed. -/
def dedupTargets (receipt : NativeSearchReceipt relation) : Multiset Entity :=
  (targetsOf receipt).dedup

/-- Values with their duplicates support the occurrence count. -/
theorem targets_support_count : countFamily.SupportsReadout targetsOf :=
  ⟨{ run := fun _ targets => Multiset.card targets
     agrees := fun _ _ => Multiset.card_map _ _ }⟩

/-- Deduplicated values do not: the retained result and its revalidation
without father(eve, carol) both show the value carol once, with two and one
occurrences, the fixture's `(counts 2 1)`. -/
theorem dedup_readout_refuses_count : ¬ countFamily.SupportsReadout dedupTargets := by
  apply countFamily.not_supportsReadout_of_policy_collision dedupTargets (first := receipt)
    (second := revalidate (signature.stillValid (learned snapshot) withoutFatherEveCarol) receipt)
    _ ()
  · change liveCount snapshot ≠ liveCount withoutFatherEveCarol
    rw [liveCount_snapshot, liveCount_without_father]
    decide
  · change (targetsOf receipt).dedup =
      ((receipt.result.answers.filter fun occurrence =>
        signature.stillValid (learned snapshot) withoutFatherEveCarol Entity.alice occurrence =
          true).map (·.target)).dedup
    rw [targetsOf, receipt_answers]
    decide

/-- A run of the valued query: its answers and the valuations it spent. -/
abbrev Run := List (ValuedOccurrence ClientEdge (Option Entity × Entity)) × Nat

def eagerRun : Run :=
  (valueThenGuard viaBob score (edges snapshot Entity.alice),
    eagerCharge (fun _ => 0) (fun _ => 1) (edges snapshot Entity.alice))

def hoistedRun : Run :=
  (guardThenValue viaBob score (edges snapshot Entity.alice),
    guardedCharge viaBob (fun _ => 0) (fun _ => 1) (edges snapshot Entity.alice))

/-- The eager and hoisted runs have the same answers and different costs. -/
def costFiber : NonTrivialFiber (fun run : Run => run.1) (fun run : Run => run.2) where
  left := eagerRun
  right := hoistedRun
  sameShadow := hoist_guard viaBob score (edges snapshot Entity.alice)
  differentValue := by decide

/-- A cost observer is not recoverable from results. -/
theorem cost_not_recoverable_from_results :
    ¬ Factors (fun run : Run => run.1) (fun run : Run => run.2) :=
  costFiber.not_factors

/-- The log of an effectful valuation that records the middle of every answer
it values, run eagerly or after the guard. -/
def valuationLog (guard : ClientEdge → Bool) (hoisted : Bool) (candidates : List ClientEdge) :
    List (Option Entity) :=
  (if hoisted then candidates.filter guard else candidates).map Edge.middle

/-- Moving the guard across an effectful valuation changes the effect: the
eager route logs bob and eve, the hoisted route bob only, while the answers
agree (`bob_guard_hoisting_saves_valuation`). -/
theorem hoisting_changes_effect_log :
    valuationLog viaBob false (edges snapshot Entity.alice) = [some Entity.bob, some Entity.eve] ∧
      valuationLog viaBob true (edges snapshot Entity.alice) = [some Entity.bob] := by
  decide

end Client

#print axioms hoist_charge_le
#print axioms nativeAnswers_eq_of_exact
#print axioms chainOccurrence_earlier_eq
#print axioms chainOccurrence_injective
#print axioms FactSignature.primitiveAnswer_target
#print axioms FactSignature.interpret_nodup
#print axioms FactSignature.mem_interpret
#print axioms FactSignature.nativeAnswers_eq_interpret
#print axioms FactSignature.primitiveProviders
#print axioms FactSignature.explain_premises_mem
#print axioms FactSignature.explain_premises_symbol
#print axioms FactSignature.stillValid_self
#print axioms sameDependencies_of_filter_eq
#print axioms FactSignature.stillValid_congr
#print axioms revalidate_of_valid
#print axioms revalidatedLive_retained
#print axioms revalidatedLive_adequate
#print axioms Client.atoms_nodup
#print axioms Client.atoms_complete
#print axioms Client.no_father_of_bob
#print axioms Client.learnedPredicate
#print axioms Client.contextSuccessor_wellFormed
#print axioms Client.quotation
#print axioms Client.provider
#print axioms Client.selected
#print axioms Client.active
#print axioms Client.interpreted_alice
#print axioms Client.edges_alice
#print axioms Client.native_answers
#print axioms Client.receipt_answers
#print axioms Client.learned_predicate_examples_and_support
#print axioms Client.interpreted_route_agrees_with_native_route
#print axioms Client.native_count_observation
#print axioms Client.carol_guard_hoisting_keeps_duplicate
#print axioms Client.bob_guard_hoisting_saves_valuation
#print axioms Client.client_hoist_charge_le
#print axioms Client.batch_stream_prefixes_agree
#print axioms Client.fixture_stream_prefix
#print axioms Client.live_retained
#print axioms Client.live_adequate
#print axioms Client.successor_revision_keeps_dependencies
#print axioms Client.active_without_successor
#print axioms Client.successor_revision_reuses
#print axioms Client.father_revision_stale
#print axioms Client.liveCount_eq
#print axioms Client.liveCount_snapshot
#print axioms Client.liveCount_without_father
#print axioms Client.father_revision_invalidates
#print axioms Client.revalidation_matches_recomputation
#print axioms Client.omitted_dependency_refuted
#print axioms Client.exact_and_count_factor_through_retained_readout
#print axioms Client.explanation_not_factors_through_values
#print axioms Client.explanation_factors_with_support
#print axioms Client.targets_support_count
#print axioms Client.dedup_readout_refuses_count
#print axioms Client.cost_not_recoverable_from_results
#print axioms Client.hoisting_changes_effect_log

end Mettapedia.Languages.MeTTa.PrimeCandidates.NativeCheckedHypothesisCognitiveClient
