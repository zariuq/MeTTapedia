/-
# Universal space-inclusion checking (executable contract)

This file specifies the backend check for the space-inclusion judgment:
does every atom of a space fit a pattern?  It does not commit the syntax
language to an operator named `match-all`; the judgment may instead elaborate
from a space-type ascription.  A native implementation must satisfy the
contract in each execution mode:

* **finite scan** (materialized spaces): executable, proof-relevant check,
  returning every successful binding when all atoms match and the exact
  violating-atom bag otherwise;
* **cache polarity**: inclusion is anti-monotone in the space — removals
  can never break a verdict, additions are the only invalidators
  (the revision-keying law for admitted `match-all` facts);
* **closure mode** (intensional/least-fixed-point spaces): affirmation by
  generator closure, licensed by `OrderHom.lfp_le`.  The abstract law is
  separated from the fragment-specific executable recognizer which must earn
  it; failure of a recognizer is incomplete, never refutation;
* **honesty split**: for intensional spaces, bounded generation can only
  REFUTE (violation witness) and closure can only AFFIRM — each channel is
  structurally incapable of the other's verdict, and no outcome
  constructor converts silence into truth.

The subtraction implementation used during design is not imported here as an
oracle theorem.  A native realization still owes differential qualification
against a checked MeTTa-level reference.  Evidence-mode reporting
(bounded coverage decorating INCOMPLETE with PLN readouts) is deliberately
deferred to the evidence-fibration instance and stated only in prose.
-/
import Mathlib.Order.FixedPoints
import Mathlib.Data.Multiset.Dedup
import Mathlib.Data.Set.Lattice.Image
import Mettapedia.Logic.LP.Semantics

namespace Mettapedia.Languages.MeTTa.MatchAllContract

universe u v

variable {α : Type u}

/-! ## §1 Finite scan: the executable inclusion check -/

/-- Outcome of the finite scan: either every atom fits and all match bindings
flow onward, or the exact bag of atoms which have no match is returned. -/
inductive InclusionOutcome (α : Type u) (Binding : Type v) where
  | holds (bindings : Multiset Binding)
  | violations (bag : Multiset α)
deriving DecidableEq

/-- The atoms for which the matcher returned no binding.  A ground successful
match is represented by one empty binding, not by the empty bag. -/
def violationBag (matchOne : α → Multiset Binding) (space : Multiset α) :
    Multiset α :=
  space.filter fun atom => (matchOne atom).card = 0

/-- All bindings produced by all atoms, retaining multiplicity. -/
def successfulBindings (matchOne : α → Multiset Binding)
    (space : Multiset α) : Multiset Binding :=
  space.bind matchOne

/-- The executable finite check: filter the non-matching atoms; empty
filter is inclusion, nonempty filter is the witness bag. -/
def checkInclusion (matchOne : α → Multiset Binding)
    (space : Multiset α) : InclusionOutcome α Binding :=
  if (violationBag matchOne space).card = 0 then
    .holds (successfulBindings matchOne space)
  else
    .violations (violationBag matchOne space)

/-- The violation bag is empty exactly when every atom has at least one match
binding. -/
theorem violationBag_eq_zero_iff (matchOne : α → Multiset Binding)
    (space : Multiset α) :
    violationBag matchOne space = 0 ↔
      ∀ atom ∈ space, matchOne atom ≠ 0 := by
  constructor
  · intro noViolations atom member nonmatching
    have inViolations : atom ∈ violationBag matchOne space := by
      simp [violationBag, member, nonmatching]
    simp [noViolations] at inViolations
  · intro allMatch
    apply Multiset.filter_eq_nil.2
    intro atom member empty
    exact allMatch atom member (Multiset.card_eq_zero.1 empty)

/-- Exact characterization of success. -/
theorem checkInclusion_holds_iff
    (matchOne : α → Multiset Binding) (space : Multiset α)
    (bindings : Multiset Binding) :
    checkInclusion matchOne space = .holds bindings ↔
      bindings = successfulBindings matchOne space ∧
        ∀ atom ∈ space, matchOne atom ≠ 0 := by
  unfold checkInclusion
  split
  · next empty =>
    have noViolations : violationBag matchOne space = 0 :=
      Multiset.card_eq_zero.1 empty
    constructor
    · intro result
      cases result
      exact ⟨rfl, (violationBag_eq_zero_iff matchOne space).1 noViolations⟩
    · rintro ⟨rfl, _⟩
      rfl
  · next nonempty =>
    constructor
    · intro result
      cases result
    · rintro ⟨_, allMatch⟩
      have noViolations := (violationBag_eq_zero_iff matchOne space).2 allMatch
      exact absurd (congrArg Multiset.card noViolations) nonempty

/-- The logical content of universal pattern coverage is a `∀`–`∃`
composite: every space atom has at least one unification witness.  This is the
bounded universal predicate which a future hyperdoctrine right adjoint may
internalize; the flat binding bag returned by `checkInclusion` is useful query
output, not itself the dependent-product witness of that adjunction. -/
theorem checkInclusion_holds_iff_forall_exists_binding
    (matchOne : α → Multiset Binding) (space : Multiset α) :
    checkInclusion matchOne space =
        .holds (successfulBindings matchOne space) ↔
      ∀ atom ∈ space, ∃ binding, binding ∈ matchOne atom := by
  constructor
  · intro holds atom member
    have nonempty :=
      (checkInclusion_holds_iff matchOne space
        (successfulBindings matchOne space)).1 holds |>.2 atom member
    exact Multiset.exists_mem_of_ne_zero nonempty
  · intro witnesses
    rw [checkInclusion_holds_iff]
    refine ⟨rfl, ?_⟩
    intro atom member empty
    obtain ⟨binding, bindingMember⟩ := witnesses atom member
    rw [empty] at bindingMember
    exact Multiset.notMem_zero binding bindingMember

/-- Exact characterization of failure: the bag is precisely the
non-matching atoms, and it is nonempty. -/
theorem checkInclusion_violations_iff
    (matchOne : α → Multiset Binding) (space : Multiset α)
    (violations : Multiset α) :
    checkInclusion matchOne space = .violations violations ↔
      violations = violationBag matchOne space ∧ violations ≠ 0 := by
  unfold checkInclusion
  split
  · next empty =>
    constructor
    · intro result
      cases result
    · rintro ⟨rfl, nonzero⟩
      exact absurd (Multiset.card_eq_zero.1 empty) nonzero
  · next nonempty =>
    constructor
    · intro result
      cases result
      exact ⟨rfl, fun zero => nonempty (by simp [zero])⟩
    · rintro ⟨rfl, _⟩; rfl

/-! ## §2 Cache polarity: additions are the only invalidators -/

/-- Inclusion is anti-monotone in the space: a verdict survives shrinking.
This is the revocation law for admitted `match-all` facts — `remove-atom`
never invalidates them. -/
theorem holds_downward (matchOne : α → Multiset Binding)
    {larger smaller : Multiset α} (included : smaller ≤ larger)
    {bindings : Multiset Binding}
    (holds : checkInclusion matchOne larger = .holds bindings) :
    checkInclusion matchOne smaller =
      .holds (successfulBindings matchOne smaller) := by
  rw [checkInclusion_holds_iff]
  exact ⟨rfl, fun atom member =>
    (checkInclusion_holds_iff matchOne larger bindings).1 holds |>.2 atom
      (Multiset.mem_of_le included member)⟩

/-- The dual half of the polarity law: adding one non-matching atom to a
passing space produces exactly that atom as the violation bag.  Additions
are precise, witness-carrying invalidators. -/
theorem add_atom_invalidates (matchOne : α → Multiset Binding)
    {space : Multiset α} {bindings : Multiset Binding}
    (holds : checkInclusion matchOne space = .holds bindings)
    {atom : α} (noMatch : matchOne atom = 0) :
    checkInclusion matchOne (atom ::ₘ space) = .violations {atom} := by
  rw [checkInclusion_violations_iff]
  have allMatch := (checkInclusion_holds_iff matchOne space bindings).1 holds |>.2
  constructor
  · simp only [violationBag, Multiset.filter_cons]
    simp [noMatch]
    have tailEmpty : violationBag matchOne space = 0 :=
      (violationBag_eq_zero_iff matchOne space).2 allMatch
    simpa [violationBag] using congrArg id tailEmpty
  · simp

/-- Adding an atom which has at least one binding preserves universal shape
success and contributes exactly its binding bag. -/
theorem add_matching_atom_preserves
    (matchOne : α → Multiset Binding)
    {space : Multiset α} {bindings : Multiset Binding}
    (holds : checkInclusion matchOne space = .holds bindings)
    {atom : α} (hasMatch : matchOne atom ≠ 0) :
    checkInclusion matchOne (atom ::ₘ space) =
      .holds (successfulBindings matchOne (atom ::ₘ space)) := by
  rw [checkInclusion_holds_iff]
  constructor
  · rfl
  · intro candidate member
    rw [Multiset.mem_cons] at member
    rcases member with rfl | tail
    · exact hasMatch
    · exact (checkInclusion_holds_iff matchOne space bindings).1 holds |>.2
        candidate tail

/-! ## §3 Closure mode: induction as a finite rule-level check -/

/-- **The closure license** (the theorem behind `match-all` on intensional
spaces): if the pattern's denotation is closed under the space's generator
operator, the entire least fixed point is included.  Affirmation over an
infinite generated space reduces to finitely many rule-closure checks —
this is `leastHerbrandModel`-style pre-fixpoint reasoning stated over
Mathlib's `lfp` directly. -/
theorem closure_license (F : Set α →o Set α) {P : Set α}
    (closed : F P ≤ P) : OrderHom.lfp F ≤ P :=
  OrderHom.lfp_le F closed

/-- A fragment recognizer is deliberately one-sided.  Acceptance provides the
pre-fixpoint proof consumed by `closure_license`; rejection says only that this
recognizer could not establish closure. -/
structure ClosureRecognizer (F : Set α →o Set α) (P : Set α) where
  check : Bool
  accepted_sound : check = true → F P ≤ P

inductive ClosureAttempt where
  | proved
  | incomplete
  deriving DecidableEq, Repr

def runClosureRecognizer (recognizer : ClosureRecognizer F P) : ClosureAttempt :=
  if recognizer.check then .proved else .incomplete

theorem runClosureRecognizer_proved_sound
    (recognizer : ClosureRecognizer F P)
    (proved : runClosureRecognizer recognizer = .proved) :
    OrderHom.lfp F ≤ P := by
  unfold runClosureRecognizer at proved
  split at proved
  · next accepted =>
    exact closure_license F (recognizer.accepted_sound accepted)
  · cases proved

/-- For actual logic-program generators, the abstract pre-fixpoint premise
decomposes exactly into base-fact inclusion and preservation by every authored
clause schema under every grounding.  A concrete native mode must still supply
a decidable recognizer for these obligations; finiteness of the rule list alone
does not decide the universally quantified grounding condition. -/
theorem logicProgram_closure_license
    {signature : Mettapedia.Logic.LP.LPSignature}
    (knowledge : Mettapedia.Logic.LP.KnowledgeBase signature)
    (Matches : Mettapedia.Logic.LP.GroundAtom signature → Prop)
    (baseClosed : ∀ atom ∈ knowledge.db, Matches atom)
    (rulesClosed : ∀
      (clause : Mettapedia.Logic.LP.Clause signature)
      (grounding : Mettapedia.Logic.LP.Grounding signature),
      clause ∈ knowledge.prog →
      (∀ premise ∈ clause.body,
        Matches (grounding.groundAtom premise)) →
      Matches (grounding.groundAtom clause.head)) :
    Mettapedia.Logic.LP.leastHerbrandModel knowledge ⊆ {atom | Matches atom} :=
  Mettapedia.Logic.LP.leastHerbrandModel_least knowledge _
    ((Mettapedia.Logic.LP.T_P_LP_le_iff knowledge _).2 ⟨baseClosed, rulesClosed⟩)

/-! ## §4 The honesty split for intensional spaces -/

/-- Verdicts over an intensional space.  Structure enforces the channel
split: `provedByClosure` carries no enumeration, `violation` carries a
generated witness, `incomplete` carries only spent budget — there is no
constructor by which bounded generation affirms, and none by which
closure refutes without a witness. -/
inductive IntensionalVerdict (α : Type u) where
  | provedByClosure
  | violation (witness : α)
  | incomplete (spent : Nat)

/-- A lawful intensional checker: closure affirmations really include the
least fixed point; violation witnesses really live in the space and really
fail the pattern.  `incomplete` claims nothing and needs no law. -/
structure IntensionalChecker (F : Set α →o Set α) (Matches : α → Prop) where
  verdict : Nat → IntensionalVerdict α
  proved_sound : ∀ b, verdict b = .provedByClosure →
    OrderHom.lfp F ≤ {a | Matches a}
  violation_sound : ∀ b w, verdict b = .violation w →
    w ∈ OrderHom.lfp F ∧ ¬ Matches w

/-! ### Nondegenerate infinite positive witness -/

def evenStep : Set Nat →o Set Nat where
  toFun previous :=
    {number | number = 0 ∨
      ∃ earlier, earlier ∈ previous ∧ number = earlier + 2}
  monotone' := by
    intro smaller larger included number generated
    rcases generated with base | ⟨earlier, member, step⟩
    · exact Or.inl base
    · exact Or.inr ⟨earlier, included member, step⟩

def EvenNat (number : Nat) : Prop := ∃ half, number = 2 * half

theorem evenStep_closed : evenStep {number | EvenNat number} ≤
    {number | EvenNat number} := by
  intro number generated
  rcases generated with base | ⟨earlier, ⟨half, even⟩, step⟩
  · exact ⟨0, by omega⟩
  · exact ⟨half + 1, by omega⟩

/-- The generated space is genuinely inhabited. -/
theorem zero_mem_even_generated : 0 ∈ OrderHom.lfp evenStep := by
  rw [← OrderHom.isFixedPt_lfp evenStep]
  exact Or.inl rfl

/-- Every even numeral is generated.  This supplies content beyond the
one-element inhabitation canary. -/
theorem double_mem_even_generated (half : Nat) :
    2 * half ∈ OrderHom.lfp evenStep := by
  induction half with
  | zero => simpa using zero_mem_even_generated
  | succ earlier ih =>
      rw [← OrderHom.isFixedPt_lfp evenStep]
      exact Or.inr ⟨2 * earlier, ih, by omega⟩

/-- The generated space is unbounded and therefore cannot be a finite-prefix
or singleton masquerade. -/
theorem even_generated_unbounded (bound : Nat) :
    ∃ number ∈ OrderHom.lfp evenStep, bound < number := by
  refine ⟨2 * (bound + 1), double_mem_even_generated (bound + 1), ?_⟩
  omega

/-- The asserted pattern is nontrivial: one does not match it. -/
theorem one_not_even : ¬ EvenNat 1 := by
  rintro ⟨half, equality⟩
  omega

def evenClosureRecognizer :
    ClosureRecognizer evenStep {number | EvenNat number} where
  check := true
  accepted_sound := fun _ => evenStep_closed

/-- Positive checker over an unbounded, nonempty generated space whose pattern
excludes a concrete atom.  This prevents the closure channel from being
validated only by an empty fixed point. -/
def evenChecker : IntensionalChecker evenStep EvenNat where
  verdict := fun _ => .provedByClosure
  proved_sound := by
    intro _ _
    exact closure_license evenStep evenStep_closed
  violation_sound := by intro _ _ result; cases result

/-- Negative witness: a checker that reports a violation whose witness
actually matches can satisfy no lawful packaging. -/
theorem false_violation_unlawful (F : Set α →o Set α)
    (Matches : α → Prop) (w : α) (hw : Matches w)
    (j : IntensionalChecker F Matches) (b : Nat) :
    j.verdict b ≠ .violation w := by
  intro h
  exact (j.violation_sound b w h).2 hw

/-! ## §5 The actual quantifier adjoints

`match` and `match-all` are executable query operators.  The categorical
adjoints live one level more abstractly: they are adjoints to substitution
(predicate reindexing) along a context map.  This section proves the thin
predicate-fibre laws directly, so the terminology does not rest on analogy.
-/

namespace PredicateQuantifier

/-- Pointwise entailment is Mathlib's subset order on predicates. -/
abbrev Entails {X : Type u} (P Q : X → Prop) : Prop :=
  {x | P x} ⊆ {x | Q x}

/-- Pull a predicate back along a context map.  This is Mathlib's set
preimage, exposed under the categorical vocabulary used below. -/
abbrev reindex {X : Type u} {Y : Type v} (map : X → Y)
    (Q : Y → Prop) : X → Prop :=
  map ⁻¹' {y | Q y}

/-- Existential image along a context map is Mathlib's set image. -/
abbrev existsAlong {X : Type u} {Y : Type v} (map : X → Y)
    (P : X → Prop) : Y → Prop :=
  map '' {x | P x}

/-- Universal image along a context map.  This, not `match`, is the right
adjoint of predicate reindexing.  Mathlib calls it `Set.kernImage`. -/
abbrev forallAlong {X : Type u} {Y : Type v} (map : X → Y)
    (P : X → Prop) : Y → Prop :=
  Set.kernImage map {x | P x}

/-- Existential image is left adjoint to reindexing. -/
theorem existsAlong_leftAdjoint_reindex
    {X : Type u} {Y : Type v} (map : X → Y)
    (P : X → Prop) (Q : Y → Prop) :
    Entails (existsAlong map P) Q ↔ Entails P (reindex map Q) :=
  Set.image_preimage _ _

/-- Universal image is right adjoint to reindexing. -/
theorem reindex_leftAdjoint_forallAlong
    {X : Type u} {Y : Type v} (map : X → Y)
    (Q : Y → Prop) (P : X → Prop) :
    Entails (reindex map Q) P ↔ Entails Q (forallAlong map P) :=
  Set.preimage_kernImage _ _

/-- The context projection used for quantification. -/
def projection {Context : Type u} {Domain : Type v} :
    Context × Domain → Context :=
  Prod.fst

/-- Along a context projection, the right adjoint is ordinary bounded
universal quantification. -/
theorem forallAlong_projection
    {Context : Type u} {Domain : Type v}
    (P : Context × Domain → Prop) (context : Context) :
    forallAlong projection P context ↔
      ∀ argument : Domain, P (context, argument) := by
  constructor
  · intro universal argument
    exact @universal (context, argument) rfl
  · intro universal pair projected
    rcases pair with ⟨sourceContext, argument⟩
    dsimp [projection] at projected
    subst sourceContext
    exact universal argument

/-- Proof-relevantly, the same right adjoint is a dependent product rather
than a Boolean scan result. -/
abbrev piAlongProjection {Context : Type u} {Domain : Type v}
    (P : Context × Domain → Type v) (context : Context) : Type v :=
  (argument : Domain) → P (context, argument)

end PredicateQuantifier

end Mettapedia.Languages.MeTTa.MatchAllContract
