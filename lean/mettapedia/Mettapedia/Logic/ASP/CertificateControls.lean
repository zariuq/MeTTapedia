import Mettapedia.Logic.ASP.Emission
import Mettapedia.Logic.ASP.Freshness
import Mettapedia.Logic.ASP.BooleanControls

/-!
# Controls for certificate emission, the certificate checker and freshness

Values are computed by the kernel (`decide`). Programs and runs come from
`CheckerControls`, `SolverControls` and `BooleanControls`.

## RUP emission

* Decision `T 1`, then `T 2` and `T 3` propagated, and the conflict `{T 3, T 1}`:
  first-UIP resolves the reasons of `T 3` and `T 2` and learns `{T 1}`. The hints in
  trail order, `{T 1, F 2}, {T 2, F 3}, {T 3, T 1}`, are a RUP derivation; in the
  order the analysis used them they are not (`chain_rup_analysis_order`).
* The emitted clauses have no repeated literals: with a repeated open literal the
  checker's RUP test fails where the clause without the repetition passes
  (`repeated_literal_refused`).
* On the run of `p :- not p. p :- q.`, the first-UIP nogood `{T p, F q}` passes
  the checker's RUP test with its hints, and at level 0 the empty clause does.

## The certificate checker

* `p :- p. q :- not p, not q.` has no stable model, but its completion has a model.
  A certificate with one loop step (the loop nogood `{T p}` of `{p}`) and one RUP
  step, against the unit `p` (clause 2) of the rule of the falsum atom `q`, is accepted
  (`loopLiar_certificate`). Without the loop step it is refused, and so is a loop
  step over a set holding `q` (`loopLiar_falsum_loop_refused`).
* Loop steps the checker refuses, for `p :- not q. q :- not p.`, which has the
  stable model `{p}`:
  - a step stating `{T p}` as the loop nogood of `{p}`, leaving out the external
    body `not q`. The stated clause is false in the stable model `{p}`;
  - a step for the atom `p` with the set `{q}`, which does not contain it. Its
    nogood is violated by the stable model `{p}`.
  The genuine loop step of `{p}` is accepted as a step, and no certificate is
  accepted for this program at all (`choice_certificates_refused`).

## The solver emits its certificate

* `p :- not p.`: the refutation at the start emits the empty clause with the hint
  1, the empty clause of the rule's nogood (`liar_emitted_accepted`).
* `p :- not p. p :- q.` as an emitting run over its four completion clauses (both
  bodies are unit bodies): propagate `F q`; decide `T p`; first-UIP backjump,
  emitting `{T p, F q}` as clause 5 with the hint 3, the support nogood of `p`;
  refutation, emitting the empty clause as clause 6 with hints 4, 5 and 1, the last
  the nogood `{F p, F p}` of `p :- not p`. The emitted certificate is accepted by the
  certificate checker by `emitted_accepted`, and its LRAT actions by the
  action-by-action LRAT checker.

## Freshness

* On that run, the first-UIP nogood is fresh, and the backjump and learning are two
  steps of the discipline (`liarQ_cdnl`).
* With `{T p, F q}` already learned, first-UIP returns it again, and the trail is
  not exhaustive: the nogood was unit below the decision. The hypothesis is needed.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ASP.CertificateControls

open CheckerControls CheckerControls.Atom SolverControls BooleanControls Program Relation
open Mettapedia.GSLT.Logic

/-! ## RUP emission -/

/-- `T 1 → T 2`. -/
def chainR2 : Nogood ℕ := ⟨[tAtom 1, fAtom 2], .learned 1⟩
/-- `T 2 → T 3`. -/
def chainR3 : Nogood ℕ := ⟨[tAtom 2, fAtom 3], .learned 2⟩
/-- The conflict `{T 3, T 1}`. -/
def chainConflict : Nogood ℕ := ⟨[tAtom 3, tAtom 1], .learned 3⟩

/-- Decision `T 1`, then `T 2` and `T 3` propagated. -/
def chain : State ℕ :=
  ⟨[⟨tAtom 3, 1, some chainR3⟩, ⟨tAtom 2, 1, some chainR2⟩, ⟨tAtom 1, 1, none⟩], [], 0⟩

theorem chain_firstUIP : firstUIP chain chainConflict = [tAtom 1] := by decide

theorem chain_hints : firstUIPHints chain chainConflict = [chainR2, chainR3, chainConflict] := by decide

theorem chain_rup : rupNogood [tAtom 1] ((firstUIPHints chain chainConflict).map Nogood.lits) = true :=
  firstUIP_rup chain chainConflict fun m hm => by rwa [chain_firstUIP] at hm

/-- The same hints in the order the analysis used them fail. -/
theorem chain_rup_analysis_order : rupNogood [tAtom 1] [chainR3.lits, chainR2.lits, chainConflict.lits] = false := by
  decide

theorem deep_rup : rupNogood (firstUIP deep deepConflict) ((firstUIPHints deep deepConflict).map Nogood.lits) = true ∧
    firstUIPHints deep deepConflict = [reason5, deepConflict] := by
  decide

/-- With a repeated open literal the RUP test fails; without it, it passes. -/
theorem repeated_literal_refused :
    PropositionalLRATActions.rupCheck [[.pos 1, .pos 1], [.neg 1]] [] = false ∧
      PropositionalLRATActions.rupCheck [[.pos 1], [.neg 1]] [] = true := by
  decide

theorem liarQ_firstUIP_rupCheck :
    PropositionalLRATActions.rupCheck
        ((firstUIPHints liarQ2 (liarQ.supportNogood p)).map fun ρ => liarQ.lratClause ρ.lits)
      (liarQ.lratClause (firstUIP liarQ2 (liarQ.supportNogood p))) = true :=
  liarQ.firstUIP_rupCheck (liarQ.reachable_inv liarQ_reach2) (liarQ.reachable_justified liarQ_reach2)
    (by unfold State.Falsifies; decide)

/-! ## The certificate checker -/

/-- The loop nogood `{T p}` of `{p}` as clause 5, and the empty clause from it and the unit `p`
(clause 2) of the rule of `q`. -/
def loopLiarCertificate : List CertStep := [.loop 5 [.neg 0] [0] 0, .lrat (.rup 6 [] [2, 5])]

theorem loopLiar_certificate : loopLiar.checkCert loopLiarCertificate = true := by decide

theorem loopLiar_no_stable_by_certificate (M : Set Atom) : ¬ loopLiar.Stable M :=
  loopLiar.checkCert_sound loopLiar_certificate M

theorem loopLiar_certificate_needs_loop : loopLiar.checkCert loopLiarCertificate.tail = false := by decide

/-- A loop step over `{p, q}`, holding the falsum atom `q`, is refused. -/
theorem loopLiar_falsum_loop_refused :
    loopLiar.certStep loopLiar.inputs (.loop 5 [.neg 0] [0, 1] 0) = none := by decide

/-- The genuine loop step of `{p}` for `p :- not q. q :- not p.` is accepted as a step. -/
theorem choice_loop_step :
    (choice.certStep choice.inputs (.loop 9 (choice.lratClause (choice.loopNogood [p].toFinset p).lits)
      (choice.atomNumbers [p]) (choice.index (.atom p)))).isSome = true := by
  decide

/-- Stating `{T p}` as the loop nogood of `{p}` is refused. -/
theorem choice_wrong_clause_refused :
    choice.certStep choice.inputs (.loop 9 (choice.lratClause [tAtom p]) (choice.atomNumbers [p])
      (choice.index (.atom p))) = none := by
  decide

/-- The stated clause is false in the stable model `{p}`. -/
theorem choice_wrong_clause_unsound :
    choice.Stable ↑({p} : Finset Atom) ∧
      PropositionalFormula.Clause.sat (choice.encode (canonical ↑({p} : Finset Atom))) (choice.lratClause [tAtom p]) =
        false := by
  refine ⟨(choice_stable_iff _).mpr (Or.inl (Finset.coe_singleton p)), ?_⟩
  rw [← finValuation_eq_canonical]
  decide

/-- A loop step for `p` with a set not containing `p` is refused. -/
theorem choice_outside_refused :
    choice.certStep choice.inputs (.loop 9 (choice.lratClause (choice.loopNogood [q].toFinset p).lits)
      (choice.atomNumbers [q]) (choice.index (.atom p))) = none := by
  decide

/-- Its nogood is violated by the stable model `{p}`. -/
theorem choice_outside_unsound :
    (choice.loopNogood [q].toFinset p).Violated (canonical ↑({p} : Finset Atom)) := by
  rw [← finValuation_eq_canonical]
  decide

/-- No certificate is accepted for a program with a stable model. -/
theorem choice_certificates_refused (steps : List CertStep) : choice.checkCert steps = false := by
  cases accepted : choice.checkCert steps with
  | false => rfl
  | true => exact absurd ((choice_stable_iff _).mpr (Or.inl rfl)) (choice.checkCert_sound accepted {p})

/-! ## The solver emits its certificate -/

theorem liar_emit : liar.EmitReachable (.done .unsat)
    (liar.emitRup liar.initialBook [] (refutationHints State.initial (constraintNogood ⟨p, [], [p]⟩))) :=
  ReflTransGen.single (liar.refutation_emit .refl (Or.inl liar_constraint.1) (by decide)
    (fun l hl => by rw [liar_constraint.2] at hl; cases hl) rfl)

/-- **The liar's emitted certificate is accepted**: the empty clause from clause 1. -/
theorem liar_emitted_accepted :
    liar.checkCert (liar.emitRup liar.initialBook [] (refutationHints State.initial (constraintNogood ⟨p, [], [p]⟩))).steps =
      true :=
  liar.emitted_accepted liar_emit

theorem liar_emitted_hints :
    hintIds liar.initialBook (refutationHints State.initial (constraintNogood ⟨p, [], [p]⟩)) = [1] := by decide

/-- The learned nogood of the run, named by the next free identifier. -/
def liarQLearned5 : Nogood Atom := ⟨firstUIP liarQ2 (liarQ.supportNogood p), .learned liarQ.initialBook.next⟩

def emit3 : State Atom := ⟨⟨fAtom p, 0, some liarQLearned5⟩ :: liarQ1.trail, [], 0⟩

/-- The book after the backjump. -/
def liarQBook3 : Book Atom :=
  liarQ.emitRup liarQ.initialBook liarQLearned5.lits (firstUIPHints liarQ2 (liarQ.supportNogood p))

/-- The book after the refutation. -/
def liarQBook4 : Book Atom := liarQ.emitRup liarQBook3 [] (refutationHints emit3 (headNogood ⟨p, [], [p]⟩))

theorem emit_reach2 : liarQ.EmitReachable (.running liarQ2) liarQ.initialBook := by
  have r1 : liarQ.EmitReachable (.running liarQ1) liarQ.initialBook :=
    ReflTransGen.single (liarQ.propagate_emit (s := State.initial) .refl (δ := liarQ.supportNogood q) (l := tAtom q)
      (Or.inl (by decide)) ⟨by decide, by decide, by simp [State.Assigned, State.initial]⟩ liarQ_isVar_q (by decide))
  exact r1.tail (liarQ.decide_emit r1 (l := tAtom p) liarQ_isVar_p (by simp [State.Assigned, liarQ1, fAtom, tAtom]))

theorem emit_reach3 : liarQ.EmitReachable (.running emit3) liarQBook3 := by
  have step : liarQ.Step (.running liarQ2) (.running emit3) :=
    Step.backjump (δ := liarQ.supportNogood p) (ε := liarQLearned5) (l := tAtom p)
      (newer := []) (older := liarQ1.trail) (d := ⟨tAtom p, 1, none⟩)
      (Or.inl (by decide)) (by unfold State.Falsifies; decide) rfl rfl
      (liarQ.firstUIP_entailed (liarQ.reachable_inv liarQ_reach2) (δ := liarQ.supportNogood p) (Or.inl (by decide)))
      (by decide) (by decide) (by decide) liarQ_isVar_p
  exact emit_reach2.tail (Emit.backjump (P := liarQ) (b := liarQ.initialBook) (ε := liarQLearned5)
    (hints := firstUIPHints liarQ2 (liarQ.supportNogood p)) (l := tAtom p)
    (newer := [⟨tAtom p, 1, none⟩]) (older := liarQ1.trail)
    step rfl (by decide) (by decide))

theorem emit_reach4 : liarQ.EmitReachable (.done .unsat) liarQBook4 :=
  emit_reach3.tail (liarQ.refutation_emit emit_reach3 (Or.inl (by decide)) (by decide)
    (by unfold State.Falsifies; decide) (by decide))

/-- **The emitted certificate is accepted**, by the emission theorem. -/
theorem liarQ_emitted_accepted : liarQ.checkCert liarQBook4.steps = true := liarQ.emitted_accepted emit_reach4

/-- The same verdict computed, and the LRAT part accepted by the action-by-action LRAT checker. -/
theorem liarQ_emitted_checked :
    liarQ.checkCert liarQBook4.steps = true ∧
      PropositionalLRATActions.check liarQ.completionLRAT (CertStep.lratActions liarQBook4.steps) = true := by
  decide

/-- The hint identifiers: `{T p, F q}` from clause 3; the empty clause from 4, 5 and 1. -/
theorem liarQ_emitted_hints :
    hintIds liarQ.initialBook (firstUIPHints liarQ2 (liarQ.supportNogood p)) = [3] ∧
      hintIds liarQBook3 (refutationHints emit3 (headNogood ⟨p, [], [p]⟩)) = [4, 5, 1] ∧
      liarQBook3.next = 6 := by
  decide

/-! ## Freshness -/

theorem liarQ2_exhaustive : Exhaustive liarQ2 := by
  intro newer d older _ _ δ learned
  exact absurd learned List.not_mem_nil

theorem liarQ_fresh :
    (firstUIP liarQ2 (liarQ.supportNogood p)).toFinset ∉ liarQ2.learned.map fun η => η.lits.toFinset :=
  liarQ.firstUIP_fresh (liarQ.reachable_inv liarQ_reach2) (liarQ.reachable_justified liarQ_reach2) liarQ2_exhaustive
    (by unfold State.Falsifies; decide) (by decide) (by decide)

theorem liarQ_cdnl :
    ∃ u s', liarQ.CDNL (.running liarQ2) (.running s') ∧
      s' = ⟨⟨u.compl, assertionLevel liarQ2.trail (firstUIP liarQ2 (liarQ.supportNogood p)) u,
        some ⟨firstUIP liarQ2 (liarQ.supportNogood p), .learned 0⟩⟩ ::
          cutTo (assertionLevel liarQ2.trail (firstUIP liarQ2 (liarQ.supportNogood p)) u) liarQ2.trail,
        liarQ2.learned, liarQ2.restartMark⟩ ∧
      liarQ.CDNL (.running s')
        (.running { s' with learned := ⟨firstUIP liarQ2 (liarQ.supportNogood p), .learned 0⟩ :: s'.learned }) :=
  liarQ.firstUIP_cdnl (liarQ.reachable_inv liarQ_reach2) (liarQ.reachable_justified liarQ_reach2) liarQ2_exhaustive
    (Or.inl (by decide)) (by unfold State.Falsifies; decide) (by decide) (by decide) _

/-- The trail of the run with `{T p, F q}` already learned. -/
def staleLiarQ : State Atom := { liarQ2 with learned := [⟨[tAtom p, fAtom q], .learned 0⟩] }

/-- First-UIP returns a nogood already learned. -/
theorem stale_not_fresh :
    (firstUIP staleLiarQ (liarQ.supportNogood p)).toFinset ∈ staleLiarQ.learned.map fun η => η.lits.toFinset := by
  decide

/-- The learned `{T p, F q}` was unit below the decision: the trail is not exhaustive. -/
theorem stale_not_exhaustive : ¬ Exhaustive staleLiarQ := by
  intro h
  exact (h [] ⟨tAtom p, 1, none⟩ liarQ1.trail rfl rfl _ List.mem_cons_self).2 (tAtom p)
    ⟨by decide, by decide, by simp [State.Assigned, liarQ1, fAtom, tAtom]⟩

end Mettapedia.Logic.ASP.CertificateControls
