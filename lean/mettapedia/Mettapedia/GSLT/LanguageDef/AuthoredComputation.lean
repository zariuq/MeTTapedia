import Mettapedia.GSLT.LanguageDef.InferenceComputedLeaves
import Mettapedia.GSLT.LanguageDef.FirstOrderRules
import Mettapedia.GSLT.LanguageDef.DeterministicEquations.Computation
import Mettapedia.GSLT.LanguageDef.DeterministicEquations.DataEquality

/-!
# Authored computations as computed leaves

A guest authors a computation as an equation program, run by the shared engine.
Its meaning is an authored relation between queries and answers. The exact
contract says the program returns an answer exactly when the relation relates
the query to it, and returns the refusal exactly when the relation relates the
query to nothing.

A qualification places the relation in a calculus: every related pair is a
derivable judgment. Together they give a computed leaf of the shared checker
whose evaluator is the authored program itself. A leaf names its query, the
answer it claims and the fuel for the run. It is accepted for a goal exactly
when the program returns that answer within the fuel and the goal is the
judgment of that query and answer. So an accepted leaf answers the query that
was asked, every related pair has an accepted leaf, and a refused query has
none, whatever answer is claimed.

Some judgments of a guest are defined by its computations rather than by
rules: the operations of its kernel, such as admissible substitution or
conversion. An authored family names such judgments. Its facts are the
judgments of related pairs, and a derivation combines rule applications with
facts. The checker accepts exactly these derivations. When every fact is also
derivable by replay, the family adds nothing.

This is a statement about the engine's semantics. It does not cover generated
MeTTa, the CeTTa runtime or any C implementation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Authored

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.InferenceComputedLeaves
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

/-! ## Engine data as patterns

A judgment about a computation speaks about the data the program reads. A
symbol, literal or variable name becomes a nullary constructor under its kind,
and the items of an expression or a list form a `cons` chain, so that rules can
walk a list item by item. The embedding is injective, and every image is a
valid rule argument. -/

mutual

/-- Engine data as a pattern. -/
def termPattern : Term → Pattern
  | .sym name => .apply "sym" [.apply name []]
  | .lit spelling => .apply "lit" [.apply spelling []]
  | .var name => .apply "var" [.apply name []]
  | .expr items => .apply "expr" [itemsPattern items]
  | .list items => .apply "list" [itemsPattern items]

/-- A list of engine data as a `cons` chain. -/
def itemsPattern : List Term → Pattern
  | [] => .apply "nil" []
  | item :: items => .apply "cons" [termPattern item, itemsPattern items]

end

mutual

theorem termPattern_injective : ∀ {first second : Term},
    termPattern first = termPattern second → first = second
  | .sym _, .sym _, same => by simp_all [termPattern]
  | .lit _, .lit _, same => by simp_all [termPattern]
  | .var _, .var _, same => by simp_all [termPattern]
  | .expr _, .expr _, same => by
      simp only [termPattern, Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at same
      rw [itemsPattern_injective same]
  | .list _, .list _, same => by
      simp only [termPattern, Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at same
      rw [itemsPattern_injective same]
  | .sym _, .lit _, same | .sym _, .var _, same | .sym _, .expr _, same | .sym _, .list _, same
  | .lit _, .sym _, same | .lit _, .var _, same | .lit _, .expr _, same | .lit _, .list _, same
  | .var _, .sym _, same | .var _, .lit _, same | .var _, .expr _, same | .var _, .list _, same
  | .expr _, .sym _, same | .expr _, .lit _, same | .expr _, .var _, same | .expr _, .list _, same
  | .list _, .sym _, same | .list _, .lit _, same | .list _, .var _, same | .list _, .expr _, same => by
      simp [termPattern] at same

theorem itemsPattern_injective : ∀ {first second : List Term},
    itemsPattern first = itemsPattern second → first = second
  | [], [], _ => rfl
  | [], _ :: _, same | _ :: _, [], same => by simp [itemsPattern] at same
  | _ :: _, _ :: _, same => by
      simp only [itemsPattern, Pattern.apply.injEq, List.cons.injEq, true_and, and_true] at same
      rw [termPattern_injective same.1, itemsPattern_injective same.2]

end

mutual

theorem termPattern_valid (depth : Nat) : ∀ term : Term,
    (termPattern term).isGroundAt depth = true ∧ (termPattern term).hasCanonicalBinderMetadata = true
  | .sym _ | .lit _ | .var _ => by
      simp [termPattern, Pattern.isGroundAt, Pattern.isGroundListAt,
        Pattern.hasCanonicalBinderMetadata, Pattern.hasCanonicalBinderMetadataList]
  | .expr items | .list items => by
      obtain ⟨ground, canonical⟩ := itemsPattern_valid depth items
      simp [termPattern, Pattern.isGroundAt, Pattern.isGroundListAt,
        Pattern.hasCanonicalBinderMetadata, Pattern.hasCanonicalBinderMetadataList, ground, canonical]

theorem itemsPattern_valid (depth : Nat) : ∀ items : List Term,
    (itemsPattern items).isGroundAt depth = true ∧ (itemsPattern items).hasCanonicalBinderMetadata = true
  | [] => by
      simp [itemsPattern, Pattern.isGroundAt, Pattern.isGroundListAt,
        Pattern.hasCanonicalBinderMetadata, Pattern.hasCanonicalBinderMetadataList]
  | item :: items => by
      obtain ⟨itemGround, itemCanonical⟩ := termPattern_valid depth item
      obtain ⟨ground, canonical⟩ := itemsPattern_valid depth items
      simp [itemsPattern, Pattern.isGroundAt, Pattern.isGroundListAt,
        Pattern.hasCanonicalBinderMetadata, Pattern.hasCanonicalBinderMetadataList,
        itemGround, itemCanonical, ground, canonical]

end

/-- Every embedded datum is a valid rule argument. -/
theorem termPattern_argumentValid (depth : Nat) (term : Term) :
    argumentValidAt depth (termPattern term) = true := by
  obtain ⟨ground, canonical⟩ := termPattern_valid depth term
  simp [argumentValidAt, ground, canonical]

/-- **An authored computation**: an equation program with an exact contract
against an authored relation. -/
structure AuthoredComputation (Query Answer : Type) where
  relation : Query → Answer → Prop
  program : Program
  host : Host
  head : String
  encodeQuery : Query → List Term
  encodeAnswer : Option Answer → Term
  accepts : ∀ query answer,
    Applies program host head (encodeQuery query) (encodeAnswer (some answer)) ↔
      relation query answer
  refuses : ∀ query,
    Applies program host head (encodeQuery query) (encodeAnswer none) ↔
      ¬ ∃ answer, relation query answer

/-- A computed leaf: the query, the answer it claims and the fuel for the run. -/
structure Leaf (Query Answer : Type) where
  query : Query
  answer : Answer
  fuel : Nat

namespace AuthoredComputation

variable {Query Answer : Type} (C : AuthoredComputation Query Answer)

/-- Run the authored program on a leaf: does it return the claimed answer
within the fuel? -/
def runs (leaf : Leaf Query Answer) : Bool :=
  match apply C.program C.host leaf.fuel C.head (C.encodeQuery leaf.query) with
  | .value result => decide (result = C.encodeAnswer (some leaf.answer))
  | _ => false

theorem runs_eq_true_iff (leaf : Leaf Query Answer) :
    C.runs leaf = true ↔
      apply C.program C.host leaf.fuel C.head (C.encodeQuery leaf.query) =
        .value (C.encodeAnswer (some leaf.answer)) := by
  unfold runs
  split
  next result returned =>
    rw [returned, decide_eq_true_eq]
    exact ⟨fun same => same ▸ rfl, fun same => Outcome.value.inj same⟩
  next other notValue =>
    constructor
    · intro impossible
      cases impossible
    · intro returned
      exact absurd returned (notValue _)

/-- **A successful run answers the query**: the claimed answer is related to
the query. -/
theorem relation_of_runs {leaf : Leaf Query Answer} (succeeded : C.runs leaf = true) :
    C.relation leaf.query leaf.answer :=
  (C.accepts leaf.query leaf.answer).mp ⟨leaf.fuel, (C.runs_eq_true_iff leaf).mp succeeded⟩

/-- **Every related pair runs**, with enough fuel and with any more fuel. -/
theorem runs_of_relation {query : Query} {answer : Answer} (related : C.relation query answer) :
    ∃ fuel, ∀ more, fuel ≤ more → C.runs ⟨query, answer, more⟩ = true := by
  obtain ⟨fuel, enough⟩ := ((C.accepts query answer).mpr related).at_least
  exact ⟨fuel, fun more atLeast => (C.runs_eq_true_iff ⟨query, answer, more⟩).mpr
    (enough more atLeast)⟩

/-- **More fuel never undoes a successful run.** -/
theorem runs_mono {query : Query} {answer : Answer} {fuel more : Nat}
    (succeeded : C.runs ⟨query, answer, fuel⟩ = true) (enough : fuel ≤ more) :
    C.runs ⟨query, answer, more⟩ = true := by
  rw [runs_eq_true_iff] at succeeded ⊢
  rw [apply_le enough (by rw [succeeded]; intro impossible; cases impossible)]
  exact succeeded

/-- **A refused query never runs to an answer.** -/
theorem not_runs_of_refused {query : Query} (refused : ¬ ∃ answer, C.relation query answer)
    (answer : Answer) (fuel : Nat) : C.runs ⟨query, answer, fuel⟩ = false := by
  cases succeeded : C.runs ⟨query, answer, fuel⟩
  · rfl
  · exact absurd ⟨answer, C.relation_of_runs succeeded⟩ refused

/-- **The authored relation is functional on encoded answers**: the program is
deterministic. -/
theorem relation_functional (injective : Function.Injective C.encodeAnswer)
    {query : Query} {first second : Answer} (left : C.relation query first)
    (right : C.relation query second) : first = second :=
  Option.some.inj (injective (((C.accepts query first).mpr left).deterministic
    ((C.accepts query second).mpr right)))

/-- **A program that returns a wrong answer has no exact contract** for that
relation. -/
theorem no_contract_of_wrong_result {relation : Query → Answer → Prop} {program : Program}
    {host : Host} {head : String} {encodeQuery : Query → List Term}
    {encodeAnswer : Option Answer → Term} {query : Query} {answer : Answer}
    (returns : Applies program host head (encodeQuery query) (encodeAnswer (some answer)))
    (wrong : ¬ relation query answer) :
    ¬ ∃ computation : AuthoredComputation Query Answer,
      computation.relation = relation ∧ computation.program = program ∧
        computation.host = host ∧ computation.head = head ∧
        computation.encodeQuery = encodeQuery ∧ computation.encodeAnswer = encodeAnswer := by
  rintro ⟨computation, rfl, rfl, rfl, rfl, rfl, rfl⟩
  exact wrong ((computation.accepts query answer).mp returns)

end AuthoredComputation

/-- **A qualification** of an authored relation in a calculus: every related
pair is a derivable judgment. -/
structure Qualification {Query Answer : Type} (C : AuthoredComputation Query Answer)
    (definition : ValidatedCalculusLanguageDef) where
  judgment : Query → Answer → Pattern
  derivable : ∀ query answer, C.relation query answer →
    Nonempty (Derivation definition (judgment query answer))

namespace Qualification

variable {Query Answer : Type} {C : AuthoredComputation Query Answer}
  {definition : ValidatedCalculusLanguageDef} (Q : Qualification C definition)

/-- The computed-leaf evaluator is the authored program. -/
def evaluate (leaf : Leaf Query Answer) : Option Pattern :=
  if C.runs leaf then some (Q.judgment leaf.query leaf.answer) else none

/-- The authored program, qualified, is a qualified computation of the
calculus. -/
def computation : QualifiedComputation definition (Leaf Query Answer) where
  evaluate := Q.evaluate
  sound := by
    intro leaf goal returned
    unfold evaluate at returned
    split at returned
    next succeeded =>
      cases returned
      exact Q.derivable _ _ (C.relation_of_runs succeeded)
    next => cases returned

/-- **A computed leaf is accepted exactly when the program returns the claimed
answer and the goal is the judgment of that query and answer.** -/
theorem computed_accepted_iff (leaf : Leaf Query Answer) (goal : Pattern) :
    check definition Q.computation.evaluate goal (.computed leaf) = true ↔
      C.runs leaf = true ∧ goal = Q.judgment leaf.query leaf.answer := by
  simp only [check]
  rw [decide_eq_true_eq]
  change Q.evaluate leaf = some goal ↔ _
  unfold evaluate
  split
  next succeeded =>
    exact ⟨fun same => ⟨succeeded, (Option.some.inj same).symm⟩,
      fun ⟨_, same⟩ => congrArg some same.symm⟩
  next failed =>
    exact ⟨fun impossible => (by cases impossible), fun ⟨succeeded, _⟩ => absurd succeeded failed⟩

/-- **An accepted leaf answers the query it names.** -/
theorem computed_accepted_relation {leaf : Leaf Query Answer} {goal : Pattern}
    (accepted : check definition Q.computation.evaluate goal (.computed leaf) = true) :
    C.relation leaf.query leaf.answer ∧ goal = Q.judgment leaf.query leaf.answer := by
  obtain ⟨succeeded, same⟩ := (Q.computed_accepted_iff leaf goal).mp accepted
  exact ⟨C.relation_of_runs succeeded, same⟩

/-- **Every related pair has an accepted leaf.** -/
theorem computed_complete {query : Query} {answer : Answer} (related : C.relation query answer) :
    ∃ fuel, check definition Q.computation.evaluate (Q.judgment query answer)
      (.computed ⟨query, answer, fuel⟩) = true := by
  obtain ⟨fuel, enough⟩ := C.runs_of_relation related
  exact ⟨fuel, (Q.computed_accepted_iff _ _).mpr ⟨enough fuel le_rfl, rfl⟩⟩

/-- **A refused query has no accepted leaf**, whatever answer it claims. -/
theorem refused_no_leaf {query : Query} (refused : ¬ ∃ answer, C.relation query answer)
    (answer : Answer) (fuel : Nat) (goal : Pattern) :
    check definition Q.computation.evaluate goal (.computed ⟨query, answer, fuel⟩) = false := by
  cases accepted : check definition Q.computation.evaluate goal (.computed ⟨query, answer, fuel⟩)
  · rfl
  · exact absurd ⟨answer, (Q.computed_accepted_relation accepted).1⟩ refused

/-- Mixed certificates with authored-program leaves accept exactly the
replay-derivable goals. -/
theorem accepted_iff_replay (goal : Pattern) :
    (∃ proof, check definition Q.computation.evaluate goal proof = true) ↔
      ∃ raw, checkRaw definition goal raw = true :=
  InferenceComputedLeaves.accepted_iff_replay Q.computation goal

end Qualification

/-! ## Derivations with facts -/

/-- Derivations from the rules of a calculus and a set of facts. -/
inductive FactDerivation (definition : ValidatedCalculusLanguageDef) (Fact : Pattern → Prop) :
    Pattern → Prop where
  | fact {goal : Pattern} : Fact goal → FactDerivation definition Fact goal
  | byRule (ruleInstance : RuleInstance) {premises : List Pattern} {conclusion : Pattern} :
      RuleApplication definition ruleInstance premises conclusion →
      (∀ premise ∈ premises, FactDerivation definition Fact premise) →
      FactDerivation definition Fact conclusion

namespace FactDerivation

variable {definition : ValidatedCalculusLanguageDef} {Fact : Pattern → Prop}

/-- Every replay derivation is a derivation with facts. -/
theorem of_derivation {goal : Pattern} (derivation : Derivation definition goal) :
    FactDerivation definition Fact goal :=
  Derivation.sound_of_ruleApplications (FactDerivation definition Fact)
    (fun ruleInstance _ _ application children => .byRule ruleInstance application children)
    derivation

/-- **Facts derivable by replay add nothing.** -/
theorem replay (qualified : ∀ goal, Fact goal → Nonempty (Derivation definition goal))
    {goal : Pattern} (derived : FactDerivation definition Fact goal) :
    Nonempty (Derivation definition goal) := by
  induction derived with
  | fact holds => exact qualified _ holds
  | byRule ruleInstance application _ ih =>
      obtain ⟨children⟩ := FirstOrderRules.derivationList_of_forall _ ih
      exact ⟨.byRule ruleInstance application children⟩

mutual

/-- **An accepted certificate is a derivation with facts** when every computed
leaf returns a fact. -/
theorem accepted_sound {Query : Type} {evaluate : Query → Option Pattern}
    (sound : ∀ query goal, evaluate query = some goal → Fact goal)
    {goal : Pattern} {proof : CompactProof Query}
    (accepted : check definition evaluate goal proof = true) :
    FactDerivation definition Fact goal := by
  cases proof with
  | replay raw =>
      obtain ⟨derivation⟩ := checkRaw_soundness (by simpa only [check] using accepted)
      exact of_derivation derivation
  | computed query =>
      exact .fact (sound query goal (by simpa only [check, decide_eq_true_eq] using accepted))
  | node ruleInstance children =>
      simp only [check] at accepted
      cases application : instantiateRule? definition ruleInstance with
      | none => simp [application] at accepted
      | some result =>
          obtain ⟨premises, conclusion⟩ := result
          simp only [application, Bool.and_eq_true, decide_eq_true_eq] at accepted
          obtain ⟨rfl, childrenAccepted⟩ := accepted
          exact .byRule ruleInstance (instantiateRule?_eq_some_iff_application.mp application)
            (children_sound sound childrenAccepted)
termination_by sizeOf proof
decreasing_by all_goals (subst_vars; simp only [CompactProof.node.sizeOf_spec]; omega)

theorem children_sound {Query : Type} {evaluate : Query → Option Pattern}
    (sound : ∀ query goal, evaluate query = some goal → Fact goal)
    {premises : List Pattern} {proofs : List (CompactProof Query)}
    (accepted : checkChildren definition evaluate premises proofs = true) :
    ∀ premise ∈ premises, FactDerivation definition Fact premise := by
  cases premises with
  | nil => exact fun _ member => absurd member List.not_mem_nil
  | cons premise premises =>
      cases proofs with
      | nil => simp [checkChildren] at accepted
      | cons proof proofs =>
          simp only [checkChildren, Bool.and_eq_true] at accepted
          obtain ⟨head, tail⟩ := accepted
          intro other member
          rcases List.mem_cons.mp member with rfl | rest
          · exact accepted_sound sound head
          · exact children_sound sound tail other rest
termination_by sizeOf proofs
decreasing_by all_goals (subst_vars; simp only [List.cons.sizeOf_spec]; omega)

end

theorem children_complete {Query : Type} {evaluate : Query → Option Pattern} :
    ∀ {premises : List Pattern},
      (∀ premise ∈ premises, ∃ proof : CompactProof Query,
        check definition evaluate premise proof = true) →
      ∃ proofs, checkChildren definition evaluate premises proofs = true
  | [], _ => ⟨[], by simp [checkChildren]⟩
  | premise :: _, all => by
      obtain ⟨proof, accepted⟩ := all premise List.mem_cons_self
      obtain ⟨proofs, rest⟩ := children_complete fun other member =>
        all other (List.mem_cons_of_mem _ member)
      exact ⟨proof :: proofs, by simp [checkChildren, accepted, rest]⟩

/-- **Every derivation with facts has an accepted certificate** when every
fact is returned by some computed leaf. -/
theorem accepted_complete {Query : Type} {evaluate : Query → Option Pattern}
    (complete : ∀ goal, Fact goal → ∃ query, evaluate query = some goal)
    {goal : Pattern} (derived : FactDerivation definition Fact goal) :
    ∃ proof : CompactProof Query, check definition evaluate goal proof = true := by
  induction derived with
  | fact holds =>
      obtain ⟨query, returned⟩ := complete _ holds
      exact ⟨.computed query, by simp [check, returned]⟩
  | byRule ruleInstance application _ ih =>
      obtain ⟨children, accepted⟩ := children_complete ih
      refine ⟨.node ruleInstance children, ?_⟩
      simp only [check, instantiateRule?_eq_some_iff_application.mpr application, decide_true,
        Bool.true_and]
      exact accepted

end FactDerivation

/-! ## Authored families -/

/-- **An authored family**: judgments of a calculus defined by authored
computations. -/
structure AuthoredFamily where
  Index : Type
  Query : Index → Type
  Answer : Index → Type
  computation : (index : Index) → AuthoredComputation (Query index) (Answer index)
  judgment : (index : Index) → Query index → Answer index → Pattern

namespace AuthoredFamily

variable (F : AuthoredFamily)

/-- The facts of a family: the judgments of related pairs. -/
def Fact (goal : Pattern) : Prop :=
  ∃ index query answer, (F.computation index).relation query answer ∧
    goal = F.judgment index query answer

/-- A leaf names a member of the family and a leaf of its computation. -/
abbrev Leaf := (index : F.Index) × Authored.Leaf (F.Query index) (F.Answer index)

/-- The evaluator runs the member's program. -/
def evaluate : F.Leaf → Option Pattern
  | ⟨index, leaf⟩ =>
      if (F.computation index).runs leaf then some (F.judgment index leaf.query leaf.answer)
      else none

variable {F}

theorem evaluate_sound {leaf : F.Leaf} {goal : Pattern} (returned : F.evaluate leaf = some goal) :
    F.Fact goal := by
  obtain ⟨index, leaf⟩ := leaf
  by_cases succeeded : (F.computation index).runs leaf = true
  · simp only [evaluate, succeeded, ↓reduceIte, Option.some.injEq] at returned
    exact ⟨index, leaf.query, leaf.answer, (F.computation index).relation_of_runs succeeded,
      returned.symm⟩
  · simp [evaluate, succeeded] at returned

theorem evaluate_complete {goal : Pattern} (holds : F.Fact goal) :
    ∃ leaf, F.evaluate leaf = some goal := by
  obtain ⟨index, query, answer, related, rfl⟩ := holds
  obtain ⟨fuel, enough⟩ := (F.computation index).runs_of_relation related
  exact ⟨⟨index, query, answer, fuel⟩, by simp [evaluate, enough fuel le_rfl]⟩

theorem evaluate_of_runs {index : F.Index} {leaf : Authored.Leaf (F.Query index) (F.Answer index)}
    (succeeded : (F.computation index).runs leaf = true) :
    F.evaluate ⟨index, leaf⟩ = some (F.judgment index leaf.query leaf.answer) := by
  simp [evaluate, succeeded]

theorem evaluate_eq_some {index : F.Index} {leaf : Authored.Leaf (F.Query index) (F.Answer index)}
    {goal : Pattern} (returned : F.evaluate ⟨index, leaf⟩ = some goal) :
    (F.computation index).relation leaf.query leaf.answer ∧
      goal = F.judgment index leaf.query leaf.answer := by
  by_cases succeeded : (F.computation index).runs leaf = true
  · simp only [evaluate, succeeded, ↓reduceIte, Option.some.injEq] at returned
    exact ⟨(F.computation index).relation_of_runs succeeded, returned.symm⟩
  · simp [evaluate, succeeded] at returned

/-- **A leaf claiming an unrelated answer returns nothing**, at any fuel. -/
theorem evaluate_eq_none {index : F.Index} {leaf : Authored.Leaf (F.Query index) (F.Answer index)}
    (unrelated : ¬ (F.computation index).relation leaf.query leaf.answer) :
    F.evaluate ⟨index, leaf⟩ = none := by
  have failed : (F.computation index).runs leaf = false := by
    cases succeeded : (F.computation index).runs leaf
    · rfl
    · exact absurd ((F.computation index).relation_of_runs succeeded) unrelated
  simp [evaluate, failed]

variable (F)

/-- **Accepted certificates are exactly the derivations from rules and the
family's facts.** -/
theorem accepted_iff (definition : ValidatedCalculusLanguageDef) (goal : Pattern) :
    (∃ proof, check definition F.evaluate goal proof = true) ↔
      FactDerivation definition F.Fact goal :=
  ⟨fun ⟨_, accepted⟩ => FactDerivation.accepted_sound (fun _ _ => evaluate_sound) accepted,
    FactDerivation.accepted_complete (fun _ => evaluate_complete)⟩

/-- **A qualified family adds nothing**: when every fact is derivable by
replay, accepted certificates are exactly the replay-derivable goals. -/
theorem accepted_iff_replay (definition : ValidatedCalculusLanguageDef)
    (qualified : ∀ index query answer, (F.computation index).relation query answer →
      Nonempty (Derivation definition (F.judgment index query answer)))
    (goal : Pattern) :
    (∃ proof, check definition F.evaluate goal proof = true) ↔
      ∃ raw, checkRaw definition goal raw = true := by
  rw [accepted_iff]
  constructor
  · intro derived
    obtain ⟨derivation⟩ := derived.replay fun _ ⟨index, query, answer, related, same⟩ =>
      same ▸ qualified index query answer related
    exact ⟨derivation.erase, checkRaw_erase derivation⟩
  · rintro ⟨raw, accepted⟩
    obtain ⟨derivation⟩ := checkRaw_soundness accepted
    exact FactDerivation.of_derivation derivation

end AuthoredFamily

/-! ## Authored calculi and where trust is placed

An authored calculus packages the rules with the computations that decide its
kernel operations. Its specified evaluator runs the authored programs in the
engine's semantics and needs no trust. An implementation — generated code on a
runtime, a native library — is trusted, and the trust it needs for soundness is
one-sided: every judgment it returns is a fact. Failing, running out of
resources or refusing never makes the checker accept a false judgment; it only
costs completeness. The trust is a hypothesis of the theorems about the
implementation, never an axiom. -/

/-- **An authored calculus**: rules and the authored judgments of its kernel
operations, one package. -/
structure AuthoredCalculus where
  definition : ValidatedCalculusLanguageDef
  family : AuthoredFamily

namespace AuthoredCalculus

variable (K : AuthoredCalculus)

/-- Derivable from the rules and the facts. -/
def Derivable (goal : Pattern) : Prop := FactDerivation K.definition K.family.Fact goal

/-- Some certificate is accepted by the specified checker. -/
def Accepts (goal : Pattern) : Prop :=
  ∃ proof, check K.definition K.family.evaluate goal proof = true

theorem accepts_iff (goal : Pattern) : K.Accepts goal ↔ K.Derivable goal :=
  K.family.accepted_iff K.definition goal

/-- **The trust an implementation needs for soundness**: every judgment it
returns is a fact. -/
def ReturnsFacts {Query : Type} (implementation : Query → Option Pattern) : Prop :=
  ∀ query goal, implementation query = some goal → K.family.Fact goal

/-- What an implementation needs, in addition, for completeness: every fact is
returned for some query. Violating it only rejects valid certificates. -/
def CoversFacts {Query : Type} (implementation : Query → Option Pattern) : Prop :=
  ∀ goal, K.family.Fact goal → ∃ query, implementation query = some goal

/-- The specified evaluator needs no trust. -/
theorem specified_returnsFacts : K.ReturnsFacts K.family.evaluate :=
  fun _ _ => AuthoredFamily.evaluate_sound

theorem specified_coversFacts : K.CoversFacts K.family.evaluate :=
  fun _ => AuthoredFamily.evaluate_complete

variable {K}

/-- **Soundness of an implementation, under exactly its trust**: a certificate
it accepts is a derivation from the rules and the facts. -/
theorem implementation_sound {Query : Type} {implementation : Query → Option Pattern}
    (trusted : K.ReturnsFacts implementation) {goal : Pattern} {proof : CompactProof Query}
    (accepted : check K.definition implementation goal proof = true) : K.Derivable goal :=
  FactDerivation.accepted_sound trusted accepted

/-- Completeness of an implementation under its coverage. -/
theorem implementation_complete {Query : Type} {implementation : Query → Option Pattern}
    (covers : K.CoversFacts implementation) {goal : Pattern} (derived : K.Derivable goal) :
    ∃ proof : CompactProof Query, check K.definition implementation goal proof = true :=
  FactDerivation.accepted_complete covers derived

/-- **Conservativity in practice**: when every fact is replay-derivable, a
certificate accepted by a trusted implementation has a replay derivation. The
statement holds under the implementation's trust and no other assumption. -/
theorem implementation_replay {Query : Type} {implementation : Query → Option Pattern}
    (trusted : K.ReturnsFacts implementation)
    (qualified : ∀ goal, K.family.Fact goal → Nonempty (Derivation K.definition goal))
    {goal : Pattern} {proof : CompactProof Query}
    (accepted : check K.definition implementation goal proof = true) :
    ∃ raw, checkRaw K.definition goal raw = true := by
  obtain ⟨derivation⟩ := (implementation_sound trusted accepted).replay qualified
  exact ⟨derivation.erase, checkRaw_erase derivation⟩

/-- A wrong positive answer is the one failure that matters: an implementation
returning a judgment that is not a fact is not trusted. -/
theorem not_returnsFacts_of_wrong {Query : Type} {implementation : Query → Option Pattern}
    {query : Query} {goal : Pattern} (returned : implementation query = some goal)
    (wrong : ¬ K.family.Fact goal) : ¬ K.ReturnsFacts implementation :=
  fun trusted => wrong (trusted query goal returned)

end AuthoredCalculus

end Mettapedia.GSLT.LanguageDef.Authored
