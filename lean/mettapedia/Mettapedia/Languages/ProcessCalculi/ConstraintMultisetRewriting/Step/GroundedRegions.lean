import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.FirstOrderIndependence
import Mettapedia.Logic.LP.TermEquality

/-!
# Binding-sensitive query regions, decided at a principal answer

A query whose region matches a pattern read at the solution depends on the solution (`matching`).
When a principal answer of the store grounds the pattern (`Grounds`), every solution factors
through the answer and leaves the grounded instance fixed, so the region is one region at every
solution:

* **the universal ask is one evaluation at the answer** (`ask_matching_iff`);
* **a writer stays outside the region at every solution exactly when none of its labels is
  equivalent to the grounded instance** (`ignoresWrites_matching_iff`): disjointness from another
  firing's output is a non-unification test at the answer.

Both are the one-frame case of `Interface.Frames.Principal.entails_iff`: the region respects the
action, and it is stable under every extension of the answer.

**In the first-order fibre** the unifier returns a principal answer whenever the store is consistent
(`FirstOrder.accepted_iff_consistent`, `FirstOrder.accepted_principal`), and a ground instance is
fixed by every substitution (`FirstOrder.ground_fixed`); such regions are therefore decided by
unification and one evaluation (`firstOrder_ask_matching_iff`). The unifier also decides consistency
(`firstOrder_decidableConsistent`), so the first-order fibre decides independence of static firings
(`firstOrder_decidableIndependent`). **Controls** (`GroundedControls`):
with the information `X = 1`, the region of `X` is written by a maker of `1` and not by a maker of
`0`, and both verdicts are read at the answer.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns

open MeTTaCalculus.OccurrenceCommits (regionOf)

universe uT uS uO
variable {T : Type uT} {S : Type uS} {O : Type uO}

section Matching

variable (A : SubstitutionAction T S)

/-- A substitution grounds a pattern when every further substitution fixes its instance. -/
def Grounds (μ : S) (pattern : T) : Prop :=
  ∀ ρ : S, A.E (A.apply ρ (A.apply μ pattern)) (A.apply μ pattern)

variable {A}

/-- **A stable ask is decided at a principal answer** (the one-frame case of
`Interface.Frames.Principal.entails_iff`). -/
theorem principal_entails_iff {store : EquationStore T} {μ : S} (principal : A.Principal store μ)
    {observation : S → Prop}
    (respects : ∀ σ τ : S, (∀ t, A.E (A.apply σ t) (A.apply τ t)) → (observation σ ↔ observation τ))
    (stable : ∀ ρ : S, observation μ → observation (A.compose ρ μ)) :
    A.Entails store observation ↔ observation μ := by
  constructor
  · intro asked
    exact asked μ principal.sound
  · intro holds σ solved
    obtain ⟨residual, through⟩ := principal.factors σ solved
    exact (respects σ (A.compose residual μ) through).mpr (stable residual holds)

variable (A) [∀ s t, Decidable (A.E s t)]

/-- **A binding-sensitive region**: the labels equivalent to a pattern read at the solution. -/
def matching (pattern : T) (seen : Finset O) : PredicateQueryAdmission.Query T S O :=
  ⟨fun σ t => decide (A.E (A.apply σ pattern) t), seen⟩

variable {A}

/-- The matching region respects the action. -/
theorem matching_region_congr (pattern : T) {σ τ : S} (same : ∀ t, A.E (A.apply σ t) (A.apply τ t)) :
    (matching A pattern (∅ : Finset O)).region σ = (matching A pattern (∅ : Finset O)).region τ := by
  funext t
  apply decide_eq_decide.mpr
  constructor
  · intro holds
    exact A.equivalence.trans (A.equivalence.symm (same pattern)) holds
  · intro holds
    exact A.equivalence.trans (same pattern) holds

/-- The matching region is the same at every extension of a grounding substitution. -/
theorem matching_region_extend {pattern : T} {μ : S} (grounded : Grounds A μ pattern) (ρ : S) :
    (matching A pattern (∅ : Finset O)).region (A.compose ρ μ) =
      (matching A pattern (∅ : Finset O)).region μ := by
  funext t
  apply decide_eq_decide.mpr
  show A.E (A.apply (A.compose ρ μ) pattern) t ↔ A.E (A.apply μ pattern) t
  rw [A.apply_compose]
  constructor
  · intro holds
    exact A.equivalence.trans (A.equivalence.symm (grounded ρ)) holds
  · intro holds
    exact A.equivalence.trans (grounded ρ) holds

/-- **The universal ask of a grounded binding-sensitive query is one evaluation at the answer.** -/
theorem ask_matching_iff {store : EquationStore T} {μ : S} (principal : A.Principal store μ)
    {pattern : T} (grounded : Grounds A μ pattern) (seen : Finset O) (label : O → T)
    (world : Finset O) :
    (matching A pattern seen).Ask A store label world ↔
      ((matching A pattern seen).atSolution μ).Holds label world := by
  refine principal_entails_iff principal (fun σ τ same => ?_) (fun ρ holds => ?_)
  · have regions := matching_region_congr (O := O) pattern same
    show regionOf label world ((matching A pattern (∅ : Finset O)).region σ) = seen ↔
      regionOf label world ((matching A pattern (∅ : Finset O)).region τ) = seen
    rw [regions]
  · have regions := matching_region_extend (O := O) grounded ρ
    show regionOf label world ((matching A pattern (∅ : Finset O)).region (A.compose ρ μ)) = seen
    rw [regions]
    exact holds

/-- **A writer stays outside a grounded binding-sensitive region at every solution exactly when none
of its labels is equivalent to the grounded instance**: a non-unification test at the answer. -/
theorem ignoresWrites_matching_iff {store : EquationStore T} {μ : S} (principal : A.Principal store μ)
    {pattern : T} (grounded : Grounds A μ pattern) (seen : Finset O) (label : O → T)
    (writer : Selection O) :
    (matching A pattern seen).IgnoresWrites A store label writer ↔
      ∀ o ∈ writer.taken ++ writer.made, ¬ A.E (A.apply μ pattern) (label o) := by
  have atAnswer := principal_entails_iff (observation := fun σ =>
      ∀ o ∈ writer.taken ++ writer.made, (matching A pattern seen).region σ (label o) = false) principal
    (fun σ τ same => by
      have regions := matching_region_congr (O := O) pattern same
      show (∀ o ∈ writer.taken ++ writer.made, (matching A pattern (∅ : Finset O)).region σ (label o) = false) ↔
        ∀ o ∈ writer.taken ++ writer.made, (matching A pattern (∅ : Finset O)).region τ (label o) = false
      rw [regions])
    (fun ρ holds => by
      have regions := matching_region_extend (O := O) grounded ρ
      show ∀ o ∈ writer.taken ++ writer.made,
        (matching A pattern (∅ : Finset O)).region (A.compose ρ μ) (label o) = false
      rw [regions]
      exact holds)
  refine atAnswer.trans ?_
  simp only [matching, decide_eq_false_iff_not]

end Matching

/-! ## The first-order fibre -/

section FirstOrderFibre

open Mettapedia.Logic.LP

variable {signature : LPSignature}

/-- A ground instance is fixed by every substitution, so a substitution that grounds a pattern's
instance grounds the pattern. -/
theorem firstOrder_grounds {μ : Subst signature} {pattern : Term signature}
    (ground : (Subst.applyTerm μ pattern).isGround) :
    Grounds (FirstOrder.action signature) μ pattern :=
  fun ρ => FirstOrder.ground_fixed ρ _ ground

/-- **The first-order fibre decides grounded binding-sensitive queries by unification and one
evaluation**: the unifier's answer is principal, and the ask is read at it. -/
instance firstOrder_decidableE [DecidableEq signature.vars] [DecidableEq signature.constants]
    [DecidableEq signature.functionSymbols] (s t : Term signature) :
    Decidable ((FirstOrder.action signature).E s t) :=
  inferInstanceAs (Decidable (s = t))

theorem firstOrder_ask_matching_iff [DecidableEq signature.vars] [DecidableEq signature.constants]
    [DecidableEq signature.functionSymbols] {O : Type uO} (store : EquationStore (Term signature))
    (answer : Subst signature) (accepted : unifyTotal store = some answer)
    {pattern : Term signature} (ground : (Subst.applyTerm answer pattern).isGround)
    (seen : Finset O) (label : O → Term signature) (world : Finset O) :
    (matching (FirstOrder.action signature) pattern seen).Ask (FirstOrder.action signature) store label world ↔
      ((matching (FirstOrder.action signature) pattern seen).atSolution answer).Holds label world :=
  ask_matching_iff (FirstOrder.accepted_principal store answer accepted) (firstOrder_grounds ground)
    seen label world

/-- **The first-order fibre decides consistency** by its unifier. -/
instance firstOrder_decidableConsistent [DecidableEq signature.vars] [DecidableEq signature.constants]
    [DecidableEq signature.functionSymbols] (store : EquationStore (Term signature)) :
    Decidable ((FirstOrder.action signature).Consistent store) :=
  decidable_of_iff _ (Option.isSome_iff_exists.trans (FirstOrder.accepted_iff_consistent store))

/-- **The first-order fibre decides independence of static firings**: decidable term equality and
the unifier supply the hypotheses of `decidableIndependent`. -/
def firstOrder_decidableIndependent [DecidableEq signature.vars] [DecidableEq signature.constants]
    [DecidableEq signature.functionSymbols] {O : Type uO} [DecidableEq O] (label : O → Term signature)
    {f g : Firing (Term signature) (Subst signature) O} (fStatic : f.Static) (gStatic : g.Static)
    (C : Configuration (Term signature) O) :
    Decidable ((firstOrderTransport (FirstOrder.action signature) label).Independent C f g) :=
  decidableIndependent (FirstOrder.action signature) label fStatic gStatic (Subst.id signature) C

end FirstOrderFibre

/-! ## Controls -/

namespace GroundedControls

open Mettapedia.Logic.LP
open ConstraintMultisetRewriting.Controls (signature A)
open TransportControls (label writer outsider)

/-- The information `X = 1`. -/
def told : EquationStore (Term signature) := [(.var 0, .const 1)]

/-- The region of `X`: the labels equal to the solution's value of `X`. -/
def watched : PredicateQueryAdmission.Query (Term signature) (Subst signature) Nat :=
  matching A (.var 0) ∅

/-- The unifier's answer for `X = 1` is principal and sets `X` to `1`. -/
theorem answer_exists :
    ∃ μ : Subst signature, A.Principal told μ ∧ Subst.applyTerm μ (.var 0) = .const 1 := by
  obtain ⟨μ, accepted⟩ := (FirstOrder.accepted_iff_consistent (signature := signature) told).mpr
    ⟨Subst.single 0 (.const 1), by
      intro equation member
      obtain rfl := List.mem_singleton.mp member
      rfl⟩
  have principal := FirstOrder.accepted_principal (signature := signature) told μ accepted
  refine ⟨μ, principal, ?_⟩
  have solved := principal.sound (.var 0, .const 1) (List.mem_singleton_self _)
  exact solved

/-- **A maker of `1` writes into the region of `X`**, read at the answer. -/
theorem writer_not_ignored : ¬ watched.IgnoresWrites A told label writer.selection := by
  obtain ⟨μ, principal, value⟩ := answer_exists
  have grounded : Grounds A μ (.var 0) := by
    intro ρ
    show Subst.applyTerm ρ (Subst.applyTerm μ (.var 0)) = Subst.applyTerm μ (.var 0)
    rw [value]
    rfl
  rw [show watched = matching A (.var 0) ∅ from rfl, ignoresWrites_matching_iff principal grounded]
  intro ignored
  apply ignored 5 (by simp [writer])
  show Subst.applyTerm μ (.var 0) = label 5
  rw [value]
  rfl

/-- **A maker of `0` stays outside the region of `X`**, read at the answer. -/
theorem outsider_ignored : watched.IgnoresWrites A told label outsider.selection := by
  obtain ⟨μ, principal, value⟩ := answer_exists
  have grounded : Grounds A μ (.var 0) := by
    intro ρ
    show Subst.applyTerm ρ (Subst.applyTerm μ (.var 0)) = Subst.applyTerm μ (.var 0)
    rw [value]
    rfl
  rw [show watched = matching A (.var 0) ∅ from rfl, ignoresWrites_matching_iff principal grounded]
  intro o member
  have only : o = 6 := by simpa [outsider] using member
  subst only
  show ¬ Subst.applyTerm μ (.var 0) = label 6
  rw [value]
  intro same
  cases same

end GroundedControls

#print axioms principal_entails_iff
#print axioms ask_matching_iff
#print axioms ignoresWrites_matching_iff
#print axioms firstOrder_ask_matching_iff
#print axioms GroundedControls.writer_not_ignored
#print axioms GroundedControls.outsider_ignored

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns
