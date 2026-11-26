import Mettapedia.Machines.TIsa.Derivation.SymbolicSearch
import Mettapedia.Machines.TIsa.Derivation.SymbolicBatch
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.MatchIdentity
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleBodySyntax

/-!
# Exhausting matches is a separate observation

A jointly possible batch need not contain every admitted match.
Completeness and uniqueness compare a proposed batch to the finite
population of isolated matches at the entry store. Which matches count
as the same is explicit; reopening a rule or allocating fresh output
identities must not create another match.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.Derivation.SymbolicComplete

open Mettapedia.Logic.LP
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open RuleSyntax.OneFrame (Terms ext)
open RuleSyntax.JointFirings (Bag MatchIdentity firingKey)
open SymbolicFiring (Rules LiveWorld Firing SameInput act)

variable {signature : LPSignature} {rules : Rules signature}

universe uKey

structure Keying (rules : Rules signature) where
  identity : MatchIdentity.{0, _, _, 0, 0, uKey} ℕ (ext (FirstOrder.action signature)) rules.program
  equality : DecidableEq identity.Key
  stable : ∀ {before : SymbolicFiring.World signature ℕ} {first second : Firing before rules.program},
    SameInput first second → identity.key first = identity.key second

private def ruleFields (rule : RuleSyntax.Rule (Terms (Term signature))) :
    RuleInstance (Term signature) × List (Term signature) := (rule.body, rule.collect)

private theorem ruleFields_injective : Function.Injective (ruleFields (signature := signature)) := by
  intro first second equal
  obtain ⟨⟨⟩, body, collect⟩ := first
  obtain ⟨⟨⟩, otherBody, otherCollect⟩ := second
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
  rfl

variable [DecidableEq signature.vars] [DecidableEq signature.constants] [DecidableEq signature.functionSymbols]

def ordered (rules : Rules signature) : Keying rules where
  identity := MatchIdentity.ordered
  equality := by
    letI : DecidableEq (RuleSyntax.Rule (Terms (Term signature))) :=
      fun _ _ => decidable_of_iff _ ruleFields_injective.eq_iff
    exact inferInstanceAs (DecidableEq (RuleSyntax.Rule (Terms (Term signature)) × List ℕ × List ℕ))
  stable := by
    intro before first second same
    change firingKey first = firingKey second
    unfold firingKey
    rw [same.rule, same.taken, same.read]

variable (slots : signature.vars ≃ ℕ) (keying : Keying rules) (before : LiveWorld signature)

def offers : List keying.identity.Key :=
  (SymbolicFiring.attempts slots rules before).filterMap fun attempt =>
    attempt.check.map fun chosen => keying.identity.key chosen.selected.firing

theorem mem_offers (key : keying.identity.Key) :
    key ∈ offers slots keying before ↔
      ∃ source : Firing before.state rules.program, source.Admits (act signature) before.state ∧
        keying.identity.key source = key := by
  constructor
  · intro inOffers
    obtain ⟨attempt, _, listed⟩ := List.mem_filterMap.mp inOffers
    obtain ⟨chosen, _, rfl⟩ := Option.map_eq_some_iff.mp listed
    exact ⟨chosen.selected.firing, chosen.admissible, rfl⟩
  · rintro ⟨source, admitted, rfl⟩
    obtain ⟨attempt, inside, chosen, passed, same⟩ :=
      SymbolicFiring.attempts_cover slots rules before source admitted
    exact List.mem_filterMap.mpr ⟨attempt, inside,
      Option.map_eq_some_iff.mpr ⟨chosen, passed, (keying.stable same).symm⟩⟩

variable (region : keying.identity.Key → Bool)

/-- The checker retains occurrence identities via the match keys and tests
only those offers the region asks for. It does not remove equal outputs. -/
def populationOK (batch : Bag ℕ (ext (FirstOrder.action signature)) rules.program before.state.frame) : Bool :=
  letI := keying.equality
  let keys := batch.keysBy keying.identity
  keys.all region && decide keys.Nodup &&
    (offers slots keying before).all fun key => !(region key) || decide (key ∈ keys)

theorem populationOK_exact
    (batch : Bag ℕ (ext (FirstOrder.action signature)) rules.program before.state.frame) :
    populationOK slots keying before region batch = true ↔
      (∀ key ∈ batch.keysBy keying.identity, region key = true) ∧ batch.DistinctBy keying.identity ∧
      batch.CompleteBy (act signature) before.state keying.identity {k | region k = true} := by
  simp only [populationOK, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, List.all_eq_true,
    Bool.not_eq_true', Bag.DistinctBy, Bag.CompleteBy]
  constructor
  · rintro ⟨⟨inside, distinct⟩, all⟩
    refine ⟨inside, distinct, fun source inRegion admitted => ?_⟩
    have found := (mem_offers slots keying before _).mpr ⟨source, admitted, rfl⟩
    change region (keying.identity.key source) = true at inRegion
    simpa [inRegion] using all _ found
  · rintro ⟨inside, distinct, complete⟩
    refine ⟨⟨inside, distinct⟩, fun key found => ?_⟩
    by_cases inRegion : region key = true
    · obtain ⟨source, admitted, rfl⟩ := (mem_offers slots keying before _).mp found
      exact Or.inr (complete source inRegion admitted)
    · exact Or.inl (Bool.eq_false_iff.mpr inRegion)

inductive Policy where
  | every
  | unique

def Admits (policy : Policy)
    (batch : Bag ℕ (ext (FirstOrder.action signature)) rules.program before.state.frame) : Prop :=
  match policy with
  | .every => batch.AdmitsEveryBy (act signature) before.state keying.identity {k | region k = true}
  | .unique => batch.AdmitsUniqueBy (act signature) before.state keying.identity {k | region k = true}

private def widthOK (policy : Policy) (size : ℕ) : Bool :=
  match policy with
  | .every => true
  | .unique => decide (size = 1)

theorem admits_iff (policy : Policy) (selection : SymbolicBatch.Prepared (program := rules.program) before.state) :
    Admits keying before region policy selection.batch ↔ SymbolicBatch.Admits .memberOwn selection ∧
      populationOK slots keying before region selection.batch = true ∧
      widthOK policy selection.batch.members.length = true := by
  rw [populationOK_exact]
  have region_eq (k : keying.identity.Key) :
      ({k | region k = true} : Set keying.identity.Key) k ↔ region k = true := Iff.rfl
  cases policy <;>
    simp [Admits, Bag.AdmitsEveryBy, Bag.AdmitsUniqueBy, widthOK, SymbolicBatch.Admits, and_assoc, region_eq]

def demandOK (policy : Policy)
    (batch : Bag ℕ (ext (FirstOrder.action signature)) rules.program before.state.frame) : Bool :=
  widthOK policy batch.members.length && populationOK slots keying before region batch

theorem demandOK_exact (policy : Policy) (selection : SymbolicBatch.Prepared (program := rules.program) before.state)
    (own : SymbolicBatch.Admits .memberOwn selection) :
    demandOK slots keying before region policy selection.batch = true ↔
      Admits keying before region policy selection.batch := by
  rw [admits_iff slots keying before region, demandOK, Bool.and_eq_true]
  tauto

def evaluate (policy : Policy) (selection : SymbolicBatch.Prepared (program := rules.program) before.state) :
    Option (Subst signature × SymbolicFiring.World signature ℕ) :=
  if demandOK slots keying before region policy selection.batch then
    SymbolicBatch.evaluate .memberOwn selection
  else none

theorem evaluate_exact (policy : Policy) (selection : SymbolicBatch.Prepared (program := rules.program) before.state)
    (answer : Subst signature) (after : SymbolicFiring.World signature ℕ) :
    evaluate slots keying before region policy selection = some (answer, after) ↔
      unifyTotal (selection.batch.information (act signature) before.state) = some answer ∧
      Admits keying before region policy selection.batch ∧
      after = selection.batch.result (act signature) before.state := by
  by_cases population : populationOK slots keying before region selection.batch = true
  · by_cases width : widthOK policy selection.batch.members.length = true
    · simpa [evaluate, demandOK, admits_iff slots keying before region, population, width] using
        SymbolicBatch.evaluate_exact .memberOwn selection answer after
    · simp [evaluate, demandOK, admits_iff slots keying before region, width]
  · simp [evaluate, demandOK, admits_iff slots keying before region, population]

end Mettapedia.Machines.TIsa.Derivation.SymbolicComplete
