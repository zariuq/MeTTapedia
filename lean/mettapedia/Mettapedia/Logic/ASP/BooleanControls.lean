import Mettapedia.Logic.ASP.LRAT
import Mettapedia.Logic.ASP.FirstUIP
import Mettapedia.Logic.ASP.Counting
import Mettapedia.Logic.ASP.Borrowing
import Mettapedia.Logic.ASP.SolverControls

/-!
# Controls for the Boolean kernel

Every value below is computed by the kernel (`decide`). Programs and runs come
from `CheckerControls` and `SolverControls`.

## The CNF

* Unit propagation of `x₀, x₀ → x₁, x₁ → x₂` derives `x₂` (`chain_propagates`);
  `x₀ ∧ ¬x₀` conflicts (`clash_conflict`); the four clauses over `x₀, x₁` are
  unsatisfiable, yet unit propagation derives nothing from them
  (`xor_propagation_silent`): propagation is sound, not complete.
* Conditioning `x₀ ∨ x₁` on `x₀` (`or_condition`).

## Nogoods as clauses

* The clause of the body nogood `{T (not p, not q), T p}` is `¬(not p, not q) ∨ ¬p`.
* The clause of the nogood `{T q, F p}` of `p :- q` is `¬q ∨ p`: the unit body `q`
  is its literal.
* On the trail of the run of `p :- not p. p :- q.` after the decision `T p`, the
  support nogood of `p` is a conflicting clause, and on the empty trail the
  support nogood `{T q}` of `q` was unit on `T q`.

## The trust bridge and LRAT

* `p :- not p.`: `p` is a falsum atom; the numbered completion is the empty
  clause of its rule and the unit `¬p` of its support (`liar_completionNumbered`);
  the empty clause by one RUP step is accepted by the action checker, so there is
  no supported and no stable model.
* `p :- not p. p :- q.`: both bodies are unit bodies, so the variables are `p`
  and `q`; the numbered completion is the four clauses of
  `liarQ_completionNumbered`, the first of which, `p ∨ p`, repeats its literal. An
  LRAT proof of two RUP steps is accepted: `p` first, as the RUP test does not take
  a clause with a repeated open literal for a unit, then the empty clause.
* `p :- not q.`: the assignment `p, not q` satisfies the numbered completion and
  loop nogoods and decodes to `{p}`; `q` alone does not. No LRAT proof is
  accepted for it (`onlyP_lrat_refused`).
* `p :- p. q :- not p, not q.` (`loopLiar`): `q` is a falsum atom, and its
  rule's nogood is the unit `p`; the rule `p :- p` gives the clause `¬p ∨ p`. The
  completion has a model (`{p}` is supported), but with the loop nogood `{T p}`
  one RUP step refutes it: it has no stable model.
* `p :- p.`: the completion has the model `{p}`; the stable CNF does not. The
  clause `¬p` holds in every stable model and is entailed by the stable CNF, but
  not by the completion: completion alone is not a route for this program.

## First-UIP

* The run of `p :- not p. p :- q.`: the conflict of the support nogood
  `{T p, T p, F q}` of `p` with the decision `T p` analyses to `{T p, F q}`, asserting
  at level 0, and the backjump it drives is a solver step
  (`liarQ_firstUIP_backjump`).
* A hand trail over three levels, where the conflict depends on the first and
  third: first-UIP gives `{T 1, T 4}`, the assertion level is 1, and the backjump
  skips level 2 (`deep_cut`).
* A conflict with no literal at the current level is returned unchanged and has
  no literal there: the hypothesis of `firstUIP_uip` is needed.

## Counting

* `x₀ ∨ x₁` has 3 models over `{0, 1}`; its Shannon split is `1 + 2`.
* `x₀` over `{0}` and `x₁ ∨ ¬x₁` over `{1}` count `1 · 2`; with overlapping
  variables (`x₀` and `¬x₀` over `{0}`) the product law fails.
* With weights 2 for true and 3 for false, `x₀ ∨ x₁` weighs 16.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ASP.BooleanControls

open CheckerControls CheckerControls.Atom SolverControls Program CNF

/-! ## The CNF -/

def chain : CNF.Formula ℕ := [[⟨0, true⟩], [⟨0, false⟩, ⟨1, true⟩], [⟨1, false⟩, ⟨2, true⟩]]

theorem chain_propagates : chain.unitPropagate 1 [] = some [⟨2, true⟩, ⟨1, true⟩, ⟨0, true⟩] := by decide

theorem chain_entails : chain.Entails [⟨2, true⟩] :=
  Formula.entails_of_unitPropagate chain_propagates (by decide)

theorem chain_sat : chain.eval (fun _ => true) = true := by decide

def clash : CNF.Formula ℕ := [[⟨0, true⟩], [⟨0, false⟩]]

theorem clash_conflict : clash.unitPropagate 1 [] = none := by decide

theorem clash_unsat : clash.Unsat := Formula.unsat_of_unitPropagate clash_conflict

def xorF : CNF.Formula ℕ :=
  [[⟨0, true⟩, ⟨1, true⟩], [⟨0, false⟩, ⟨1, true⟩], [⟨0, true⟩, ⟨1, false⟩], [⟨0, false⟩, ⟨1, false⟩]]

theorem xor_unsat : xorF.Unsat := by
  intro σ
  cases h0 : σ 0 <;> cases h1 : σ 1 <;>
    simp [xorF, Formula.eval, Clause.eval, Literal.eval, h0, h1]

/-- Unit propagation is not complete: it derives nothing from an unsatisfiable formula. -/
theorem xor_propagation_silent : xorF.unitPropagate 2 [] = some [] := by decide

def orF : CNF.Formula ℕ := [[⟨0, true⟩, ⟨1, true⟩]]

theorem or_condition : orF.condition 0 false = [[⟨1, true⟩]] ∧ orF.condition 0 true = [] := by decide

/-! ## Nogoods as clauses -/

/-- The body `not p, not q`, of two literals, and its nogood `{T (not p, not q), T p}`. -/
def bothNeg : Body Atom := ⟨[], [p, q]⟩
def bothNegP : Nogood Atom := ⟨[tBody bothNeg, tAtom p], .bodyNeg bothNeg p⟩

theorem bothNegP_clause : bothNegP.clause = [⟨.body bothNeg, false⟩, ⟨.atom p, false⟩] := by decide

theorem liarQ_head_clause : (headNogood (⟨p, [q], []⟩ : Rule Atom)).clause = [⟨.atom q, false⟩, ⟨.atom p, true⟩] := by
  decide

theorem liarQ2_support_conflict :
    (liarQ.supportNogood p).clause.openLits (trailAssignment liarQ2.lits) = [] := by decide

theorem liarQ_support_q_unit :
    (liarQ.supportNogood q).clause.openLits (trailAssignment (State.initial : State Atom).lits) = [⟨.atom q, false⟩] := by
  decide

/-! ## The trust bridge and LRAT -/

/-- The empty nogood of the rule `p :- not p` and the unit support nogood `T p`. -/
theorem liar_completionNumbered : liar.completionNumbered = [[], [⟨0, false⟩]] := by decide

/-- The empty clause from clause 1. -/
def liarProof : List GSLT.Logic.PropositionalLRATActions.Action := [.rup 3 [] [1]]

theorem liar_lrat_accepted :
    GSLT.Logic.PropositionalLRATActions.check liar.completionNumbered.toLRAT liarProof = true := by decide

theorem liar_no_supported_by_lrat (M : Set Atom) : ¬ liar.Supported M :=
  liar.not_supported_of_lratActions liar_lrat_accepted M

theorem liar_no_stable_by_lrat (M : Set Atom) : ¬ liar.Stable M :=
  fun stable => liar_no_supported_by_lrat M (liar.stable_supported stable)

/-- Variables `p, q` numbered `0, 1`: the nogoods `{F p, F p}` and `{T q, F p}` of the rules, the
support nogood `{T p, T p, F q}` of `p` and the unit support nogood of `q`. -/
theorem liarQ_completionNumbered :
    liarQ.completionNumbered = [[⟨0, true⟩, ⟨0, true⟩], [⟨1, false⟩, ⟨0, true⟩],
      [⟨0, false⟩, ⟨0, false⟩, ⟨1, true⟩], [⟨1, false⟩]] := by decide

/-- `p` (clause 5) by RUP from clause 1, `p ∨ p`, which conflicts once `p` is false; the empty clause
from 5, 4 and 3. -/
def liarQProof : List GSLT.Logic.PropositionalLRATActions.Action :=
  [.rup 5 [.pos 0] [1], .rup 6 [] [5, 4, 3]]

/-- The empty clause directly from clause 1 is refused: `p ∨ p` has two open literals. -/
theorem liarQ_repeated_refused :
    GSLT.Logic.PropositionalLRATActions.check liarQ.completionNumbered.toLRAT [.rup 5 [] [1, 4, 3]] = false := by
  decide

theorem liarQ_lrat_accepted :
    GSLT.Logic.PropositionalLRATActions.check liarQ.completionNumbered.toLRAT liarQProof = true := by decide

theorem liarQ_no_stable_by_lrat (M : Set Atom) : ¬ liarQ.Stable M :=
  fun stable => liarQ.not_supported_of_lratActions liarQ_lrat_accepted M (liarQ.stable_supported stable)

/-- The assignment `p, not q` (variables `p`, `q` numbered 0, 1; the unit body `not q` has no
variable). -/
def onlyPModel : ℕ → Bool := fun i => i == 0

theorem onlyP_certificate : onlyP.stableNumbered.eval onlyPModel = true ∧ onlyP.decodeModel onlyPModel = {p} := by
  decide

theorem onlyP_certified : onlyP.Stable ↑({p} : Finset Atom) := by
  have := onlyP.stable_of_stableNumbered onlyP_certificate.1
  rwa [onlyP_certificate.2] at this

theorem onlyP_q_rejected : onlyP.stableNumbered.eval (fun i => i == 1) = false := by decide

/-- No LRAT proof is accepted for a program with a stable model. -/
theorem onlyP_lrat_refused (proof : GSLT.Logic.PropositionalLRAT.Proof) :
    GSLT.Logic.PropositionalLRAT.checker.check onlyP.stableNumbered.toLRAT proof = false := by
  cases accepted : GSLT.Logic.PropositionalLRAT.checker.check onlyP.stableNumbered.toLRAT proof with
  | false => rfl
  | true => exact absurd onlyP_certified (onlyP.not_stable_of_lrat accepted _)

/-- `p :- p. q :- not p, not q.` -/
def loopLiar : Program Atom := [⟨p, [p], []⟩, ⟨q, [], [p, q]⟩]

/-- `{p}` is supported: `p` true, `q` false; the variables are `p` and `q` alone. -/
theorem loopLiar_completion_model : loopLiar.completionNumbered.eval (fun i => i == 0) = true := by
  decide

theorem loopLiar_supported : loopLiar.Supported ↑({p} : Finset Atom) := by
  have := ((loopLiar.completionNumbered_eval_iff _).mp loopLiar_completion_model).1
  rwa [← coe_decodeModel, show loopLiar.decodeModel (fun i => i == 0) = {p} by decide] at this

/-- The rule of `q` is the unit `p` (clause 2); the loop nogood `{T p}` is clause 5; the empty clause
from 2 and 5. -/
def loopLiarProof : List GSLT.Logic.PropositionalLRATActions.Action := [.rup 6 [] [2, 5]]

theorem loopLiar_clauses : loopLiar.stableNumbered[1]? = some [⟨0, true⟩] ∧
    loopLiar.stableNumbered[4]? = some [⟨0, false⟩] ∧ loopLiar.stableNumbered.length = 5 := by decide

theorem loopLiar_lrat_accepted :
    GSLT.Logic.PropositionalLRATActions.check loopLiar.stableNumbered.toLRAT loopLiarProof = true := by decide

theorem loopLiar_no_stable (M : Set Atom) : ¬ loopLiar.Stable M :=
  loopLiar.not_stable_of_lratActions loopLiar_lrat_accepted M

/-- The same proof is refused for the completion alone, which has a model. -/
theorem loopLiar_completion_refused :
    GSLT.Logic.PropositionalLRATActions.check loopLiar.completionNumbered.toLRAT loopLiarProof = false := by
  decide

/-- The same proofs in the integer form of the standard-library checker. -/
def liarIntProof : GSLT.Logic.PropositionalLRAT.Proof := #[.addEmpty 3 #[1]]
def liarQIntProof : GSLT.Logic.PropositionalLRAT.Proof := #[.addRup 5 #[1] #[1], .addEmpty 6 #[5, 4, 3]]
def loopLiarIntProof : GSLT.Logic.PropositionalLRAT.Proof := #[.addEmpty 6 #[2, 5]]

/-- Runtime comparison with the whole-proof standard-library checker, whose hash tables depend on
the host word width; these are runtime tests, separate from the kernel-checked controls above. -/
def verdicts : List (String × Bool) :=
  [("liar completion refuted", GSLT.Logic.PropositionalLRAT.checker.check liar.completionNumbered.toLRAT liarIntProof),
   ("liar completion refuted from text",
      GSLT.Logic.PropositionalLRAT.checkText liar.completionNumbered.toLRAT "3 0 1 0\n".toUTF8),
   ("liarQ completion refuted", GSLT.Logic.PropositionalLRAT.checker.check liarQ.completionNumbered.toLRAT liarQIntProof),
   ("loop liar refuted with loop nogoods",
      GSLT.Logic.PropositionalLRAT.checker.check loopLiar.stableNumbered.toLRAT loopLiarIntProof),
   ("loop liar completion not refuted",
      !GSLT.Logic.PropositionalLRAT.checker.check loopLiar.completionNumbered.toLRAT loopLiarIntProof),
   ("p :- not q not refuted",
      !GSLT.Logic.PropositionalLRAT.checker.check onlyP.stableNumbered.toLRAT loopLiarIntProof)]

theorem selfSupport_completion_model : selfSupport.completionCNF.eval (fun _ => true) = true := by decide

theorem selfSupport_stable_rejects : selfSupport.stableCNF.eval (fun _ => true) = false := by decide

/-- The clause `¬p`. -/
def notP : selfSupport.ProgramClause :=
  ⟨[⟨.atom p, false⟩], fun l hl => by
    rw [List.mem_singleton] at hl
    subst hl
    exact ⟨_, List.mem_cons_self, Or.inl rfl⟩⟩

theorem notP_stableTheory : notP ∈ selfSupport.stableTheory := by
  intro v _ _ stable
  obtain ⟨M, hM, same⟩ := (selfSupport.stable_iff_mem_stableModels _).mp stable
  rw [selfSupport_stableModels, Finset.mem_singleton] at hM
  subst hM
  have : v (.atom p) = false := by
    cases h : v (.atom p) with
    | false => rfl
    | true =>
      have member : p ∈ v.atoms := h
      rw [← same] at member
      simp at member
  simp [notP, Clause.eval, Literal.eval, this]

/-- Borrowing along completion with loop nogoods recovers `¬p`. -/
theorem notP_stableCNF : notP ∈ selfSupport.cnfTheory selfSupport.stableCNF :=
  selfSupport.stableRoute.preserves notP_stableTheory

/-- Completion alone does not entail `¬p`: it is not a route for `p :- p.`. -/
theorem notP_not_completion : notP ∉ selfSupport.cnfTheory selfSupport.completionCNF := by
  intro h
  have := h _ selfSupport_completion_model
  revert this
  decide

/-! ## First-UIP -/

theorem liarQ_firstUIP : firstUIP liarQ2 (liarQ.supportNogood p) = [tAtom p, fAtom q] := by decide

theorem liarQ_assertionLevel : assertionLevel liarQ2.trail [tAtom p, fAtom q] (tAtom p) = 0 := by decide

theorem liarQ_firstUIP_backjump :
    ∃ u ∈ firstUIP liarQ2 (liarQ.supportNogood p), u ∈ (currentLevel liarQ2.trail).map Entry.lit ∧
      assertionLevel liarQ2.trail (firstUIP liarQ2 (liarQ.supportNogood p)) u < levelOf liarQ2.trail ∧
      levelOf (cutTo (assertionLevel liarQ2.trail (firstUIP liarQ2 (liarQ.supportNogood p)) u) liarQ2.trail) =
        assertionLevel liarQ2.trail (firstUIP liarQ2 (liarQ.supportNogood p)) u ∧
      (⟨cutTo (assertionLevel liarQ2.trail (firstUIP liarQ2 (liarQ.supportNogood p)) u) liarQ2.trail,
          liarQ2.learned, liarQ2.restartMark⟩ : State Atom).UnitOn
        ⟨firstUIP liarQ2 (liarQ.supportNogood p), .learned 0⟩ u ∧
      liarQ.Step (.running liarQ2) (.running ⟨⟨u.compl,
        assertionLevel liarQ2.trail (firstUIP liarQ2 (liarQ.supportNogood p)) u,
        some ⟨firstUIP liarQ2 (liarQ.supportNogood p), .learned 0⟩⟩ ::
          cutTo (assertionLevel liarQ2.trail (firstUIP liarQ2 (liarQ.supportNogood p)) u) liarQ2.trail,
        liarQ2.learned, liarQ2.restartMark⟩) :=
  liarQ.firstUIP_backjump (liarQ.reachable_inv liarQ_reach2) (liarQ.reachable_justified liarQ_reach2)
    (Or.inl (by decide)) (by unfold State.Falsifies; decide) (by decide) (by decide) _

/-- `T 3 → T 4`. -/
def reason4 : Nogood ℕ := ⟨[tAtom 3, fAtom 4], .learned 1⟩
/-- `T 1 ∧ T 4 → T 5`. -/
def reason5 : Nogood ℕ := ⟨[tAtom 1, tAtom 4, fAtom 5], .learned 2⟩

/-- Decisions `T 1`, `T 2`, `T 3` at levels 1, 2, 3, then `T 4` and `T 5` propagated. -/
def deep : State ℕ :=
  ⟨[⟨tAtom 5, 3, some reason5⟩, ⟨tAtom 4, 3, some reason4⟩, ⟨tAtom 3, 3, none⟩, ⟨tAtom 2, 2, none⟩,
    ⟨tAtom 1, 1, none⟩], [], 0⟩

def deepConflict : Nogood ℕ := ⟨[tAtom 4, tAtom 5], .learned 3⟩

theorem deep_justified : Justified deep.trail :=
  .implied rfl (by decide) (by decide) (.implied rfl (by decide) (by decide)
    (.decision rfl (.decision rfl (.decision rfl .nil))))

theorem deep_firstUIP : firstUIP deep deepConflict = [tAtom 1, tAtom 4] := by decide

theorem deep_uip :
    (firstUIP deep deepConflict).Nodup ∧ ∃ u ∈ firstUIP deep deepConflict, u ∈ (currentLevel deep.trail).map Entry.lit ∧
      ∀ m ∈ firstUIP deep deepConflict, m ≠ u → m ∈ (belowLevel deep.trail).map Entry.lit :=
  firstUIP_uip deep_justified (by unfold State.Falsifies; decide) (by decide)

theorem deep_assertionLevel : assertionLevel deep.trail [tAtom 1, tAtom 4] (tAtom 4) = 1 := by decide

/-- The backjump skips level 2. -/
theorem deep_cut : cutTo 1 deep.trail = [⟨tAtom 1, 1, none⟩] := by decide

/-- A conflict without a literal at the current level is not analysed into an asserting nogood. -/
theorem stale_conflict :
    firstUIP deep ⟨[tAtom 1, tAtom 2], .learned 4⟩ = [tAtom 1, tAtom 2] ∧
      ∀ m ∈ firstUIP deep ⟨[tAtom 1, tAtom 2], .learned 4⟩, m ∉ (currentLevel deep.trail).map Entry.lit := by
  decide

/-- A reason without the complement of its literal is not justified. -/
theorem unjustified : ¬ Justified [⟨tAtom 4, 1, some ⟨[tAtom 3], .learned 0⟩⟩, ⟨tAtom 3, 1, none⟩] := by
  intro h
  obtain ⟨member, -⟩ := h.reason_spec (ρ := ⟨[tAtom 3], .learned 0⟩) rfl
  revert member
  decide

/-! ## Counting -/

theorem orF_count : orF.count {0, 1} = 3 := by decide

theorem orF_shannon : (orF.condition 0 false).count {1} = 1 ∧ (orF.condition 0 true).count {1} = 2 := by decide

theorem orF_shannon_law : orF.count {0, 1} = (orF.condition 0 false).count {1} + (orF.condition 0 true).count {1} :=
  Formula.count_insert (by decide) orF

/-- `x₀`. -/
def unitX0 : CNF.Formula ℕ := [[⟨0, true⟩]]
/-- `¬x₀`. -/
def notX0 : CNF.Formula ℕ := [[⟨0, false⟩]]
/-- `x₁ ∨ ¬x₁`. -/
def tautX1 : CNF.Formula ℕ := [[⟨1, true⟩, ⟨1, false⟩]]

theorem unitX0_vars : unitX0.VarsIn ↑({0} : Finset ℕ) := by
  intro c hc l hl
  simp only [unitX0, List.mem_singleton] at hc
  subst hc
  simp only [List.mem_singleton] at hl
  subst hl
  simp

theorem tautX1_vars : tautX1.VarsIn ↑({1} : Finset ℕ) := by
  intro c hc l hl
  simp only [tautX1, List.mem_singleton] at hc
  subst hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl <;> simp

theorem components_count : (unitX0 ++ tautX1).count ({0} ∪ {1}) = unitX0.count {0} * tautX1.count {1} :=
  Formula.count_append (by decide) unitX0_vars tautX1_vars

theorem components_values : unitX0.count {0} = 1 ∧ tautX1.count {1} = 2 ∧ (unitX0 ++ tautX1).count {0, 1} = 2 := by
  decide

/-- With shared variables the product law fails. -/
theorem overlap_product_fails : (unitX0 ++ notX0).count ({0} ∪ {0}) ≠ unitX0.count {0} * notX0.count {0} := by
  decide

theorem orF_weighted : orF.weightedCount (fun _ b => if b then (2 : ℕ) else 3) {0, 1} = 16 := by decide

theorem orF_weighted_shannon :
    orF.weightedCount (fun _ b => if b then (2 : ℕ) else 3) {0, 1} =
      3 * (orF.condition 0 false).weightedCount (fun _ b => if b then (2 : ℕ) else 3) {1} +
        2 * (orF.condition 0 true).weightedCount (fun _ b => if b then (2 : ℕ) else 3) {1} :=
  Formula.weightedCount_insert _ (by decide) orF

end Mettapedia.Logic.ASP.BooleanControls
