import Mettapedia.Logic.ASP.Enumeration
import Mettapedia.Logic.ASP.CheckerAgreement
import Mettapedia.Logic.ASP.BooleanControls
import Mettapedia.Logic.ASP.PropagationControls

/-!
# Controls for the reference driver

Values are computed by the kernel (`decide`, or `decide +kernel` for the larger
batches); the `#eval` lines run the compiled driver on the same and on more
programs.

## Hand-written programs

* `p :- not q.`: the driver returns `{p}`, and enumeration lists exactly `{p}`.
* `p :- not p.` (the liar): `unsat`, with a certificate the certificate checker
  accepts, and whose LRAT part the action-by-action LRAT checker accepts.
* **An even loop**, `p :- not q. q :- not p.`: enumeration lists `{q}` and `{p}`;
  with `enumerate_models` this proves that they are exactly the stable models.
* **An odd loop**, `0 :- not 1. 1 :- not 2. 2 :- not 0.`: `unsat`, with an accepted
  certificate, which by itself proves there is no stable model.
* **A tight program**, `p. q :- p, not r. r :- not q.`: tight, with the two
  stable models `{p, q}` and `{p, r}`, which are also its supported models.
* **Non-tight programs whose supported models are not all stable**:
  - `p :- p.`: `{p}` is supported, and enumeration lists only `{}`;
  - `p :- q. q :- p. r :- not p.`: `{p, q}` is supported, and enumeration lists only
    `{r}`;
  - `p :- q. q :- p. p :- not r. r :- not p.`: both `{p, q}` and `{r}` are stable and
    listed;
  - `p :- p. q :- not p, not q.`: no stable model although its completion has a
    model; `unsat` with an accepted certificate, which needs a loop step.
* **Negative controls**:
  - a certificate with its last step removed is refused (for `p :- not p. p :- q.`;
    the liar's inputs already hold the empty clause, the nogood of its rule);
  - the odd loop's certificate is refused for the even loop;
  - watched propagation with too little fuel runs out, where one more than the
    number of variables reaches the fixpoint;
  - **where the two checkers differ**: appending a deletion of every identifier to
    the liar's certificate keeps the action checker accepting (the empty clause was
    derived) and makes the certificate checker refuse (it is no longer live).

## Generated programs

Sixty-four programs from a fixed linear congruential generator: forty with random
rules over three to six atoms, twenty-four with one to three choice pairs plus
random rules. For each, enumeration lists exactly the brute-force checker's stable
models (`Program.stableModels`), and the final certificate is accepted for the
blocked program. Sixteen are decided by the kernel; all sixty-four are run.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ASP.DriverControls

open CheckerControls CheckerControls.Atom BooleanControls Program

/-! ## Hand-written programs -/

theorem onlyP_solve : onlyP.solve.model? = some [p] := by decide

theorem onlyP_enumerate : onlyP.enumerate.models? = some [[p]] := by decide

theorem liar_refuted :
    liar.solve.model? = none ∧ liar.solve.certificate?.map liar.checkCert = some true ∧
      liar.solve.certificate?.map (fun cert =>
        GSLT.Logic.PropositionalLRATActions.check liar.completionLRAT (CertStep.lratActions cert)) = some true := by
  decide

/-- The liar has no stable model, by the driver's certificate alone. -/
theorem liar_no_stable_by_driver (S : Set Atom) : ¬ liar.Stable S := by
  have computed : liar.solve.model? = none := by decide
  cases h : liar.solve with
  | unsat cert => exact liar.solve_unsat_no_stable h S
  | sat M =>
    rw [h] at computed
    cases computed
  | outOfFuel => exact absurd h liar.solve_ne_outOfFuel

/-! ## An even loop: two models -/

theorem choice_enumerate : choice.enumerate.models? = some [[p], [q]] := by decide

/-- **The stable models of the even loop, read off the driver's enumeration.** -/
theorem choice_stable_by_driver (S : Set Atom) : choice.Stable S ↔ S = {p} ∨ S = {q} := by
  cases h : choice.enumerate with
  | outOfFuel => exact absurd h choice.enumerate_ne_outOfFuel
  | done Ms cert =>
    have computed := choice_enumerate
    rw [h] at computed
    obtain rfl := Option.some.inj computed
    rw [(choice.enumerate_models h).1 S]
    simp [eq_comm]

/-! ## An odd loop: no model, with a certificate -/

/-- `0 :- not 1. 1 :- not 2. 2 :- not 0.` -/
def oddLoop : Program ℕ := [⟨0, [], [1]⟩, ⟨1, [], [2]⟩, ⟨2, [], [0]⟩]

theorem oddLoop_refuted : oddLoop.solve.model? = none ∧ oddLoop.solve.certificate?.map oddLoop.checkCert = some true := by
  decide

/-- **The odd loop has no stable model**, by the driver's certificate. -/
theorem oddLoop_no_stable (S : Set ℕ) : ¬ oddLoop.Stable S := by
  have computed := oddLoop_refuted.1
  cases h : oddLoop.solve with
  | unsat cert => exact oddLoop.solve_unsat_no_stable h S
  | sat M =>
    rw [h] at computed
    cases computed
  | outOfFuel => exact absurd h oddLoop.solve_ne_outOfFuel

theorem oddLoop_enumerate : oddLoop.enumerate.models? = some [] := by decide

/-! ## A tight program -/

/-- `p. q :- p, not r. r :- not q.` -/
def tightTwo : Program Atom := [⟨p, [], []⟩, ⟨q, [p], [r]⟩, ⟨r, [], [q]⟩]

theorem tightTwo_tight : tightTwo.Tight := by
  have onlyPQ : ∀ b a, tightTwo.PosDep b a → b = p ∧ a = q := by
    rintro b a ⟨rule, hr, rfl, hb⟩
    simp only [tightTwo, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp_all
  have accP : Acc tightTwo.PosDep p := ⟨_, fun b h => absurd (onlyPQ b p h).2 (by decide)⟩
  refine ⟨fun a => ⟨_, fun b h => ?_⟩⟩
  obtain ⟨rfl, -⟩ := onlyPQ b a h
  exact accP

theorem tightTwo_enumerate : tightTwo.enumerate.models? = some [[p, q], [p, r]] := by decide

/-- Its stable models are its supported models (Fages), and enumeration lists them. -/
theorem tightTwo_supported :
    tightTwo.supportedModels = tightTwo.stableModels ∧
      (tightTwo.enumerate.models?.map fun Ms => (Ms.map List.toFinset).toFinset) = some tightTwo.stableModels := by
  decide

/-! ## Supported models that are not stable -/

theorem selfSupport_enumerate :
    selfSupport.enumerate.models? = some [[]] ∧ ({p} : Finset Atom) ∈ selfSupport.supportedModels := by
  decide

theorem unsupportedLoop_enumerate :
    unsupportedLoop.enumerate.models? = some [[r]] ∧ ({p, q} : Finset Atom) ∈ unsupportedLoop.supportedModels := by
  decide

theorem supportedLoop_enumerate : supportedLoop.enumerate.models? = some [[r], [q, p]] := by decide

/-- `p :- p. q :- not p, not q.`: the completion has a model, the loop step refutes it. -/
theorem loopLiar_refuted :
    loopLiar.solve.model? = none ∧ loopLiar.solve.certificate?.map loopLiar.checkCert = some true ∧
      loopLiar.supportedModels.Nonempty := by
  decide

/-! ## Negative controls -/

/-- A certificate with its last step removed is refused: `p :- not p. p :- q.` -/
theorem truncated_refused :
    SolverControls.liarQ.solve.certificate?.map (fun cert => SolverControls.liarQ.checkCert cert.dropLast) =
      some false := by
  decide

/-- The liar's inputs hold the empty clause of its rule's nogood: no step is needed. -/
theorem liar_inputs_refute : liar.checkCert [] = true := by decide

/-- `0 :- not 1. 1 :- not 0.` -/
def evenLoop : Program ℕ := [⟨0, [], [1]⟩, ⟨1, [], [0]⟩]

/-- The odd loop's certificate does not refute the even loop. -/
theorem oddLoop_certificate_refused_for_evenLoop :
    oddLoop.solve.certificate?.map evenLoop.checkCert = some false := by
  decide

/-- Watched propagation needs its fuel: one unit runs out on the implications `0 → 1 → 2 → 3`,
and one more than the number of variables reaches the fixpoint. -/
theorem watched_fuel :
    (match propagateWatched 1 PropagationControls.start with | .outOfFuel _ => true | _ => false) = true ∧
      (match propagateWatched 5 PropagationControls.start with | .fixpoint _ => true | _ => false) = true := by
  decide

/-- The liar's certificate, with every identifier deleted at the end. -/
def deleteAll : CertStep := .lrat (.delete (List.range 100))

/-- After deleting the empty clause, the action checker still accepts and the certificate checker
refuses; without the deletion both accept, as `checkCert_lrat_iff_check` requires. -/
theorem deletion_separates :
    liar.solve.certificate?.map (fun cert =>
      (liar.checkCert cert, GSLT.Logic.PropositionalLRATActions.check liar.completionLRAT (CertStep.lratActions cert),
        liar.checkCert (cert ++ [deleteAll]),
        GSLT.Logic.PropositionalLRATActions.check liar.completionLRAT (CertStep.lratActions (cert ++ [deleteAll])))) =
      some (true, true, false, true) := by
  decide

/-! ## Generated programs -/

/-- A linear congruential generator. -/
def lcg (x : ℕ) : ℕ := (x * 1103515245 + 12345) % 2147483648

/-- A random rule over the atoms `0 … n-1`: at most one positive and two negated atoms. -/
def genRule (n x : ℕ) : Rule ℕ × ℕ :=
  let x1 := lcg x
  let x2 := lcg x1
  let x3 := lcg x2
  let x4 := lcg x3
  let x5 := lcg x4
  let x6 := lcg x5
  let pos := if (x2 / 65536) % 2 == 0 then [(x3 / 65536) % n] else []
  let neg := if (x4 / 65536) % 3 != 0 then [(x5 / 65536) % n] else []
  (⟨(x1 / 65536) % n, pos, if (x6 / 65536) % 4 == 0 then ((x6 / 4096) % n) :: neg else neg⟩, x6)

/-- `k` random rules over the atoms `0 … n-1`. -/
def genProgram (n : ℕ) : ℕ → ℕ → Program ℕ
  | 0, _ => []
  | k + 1, x => (genRule n x).1 :: genProgram n k (genRule n x).2

/-- Choice pairs `2i :- not 2i+1. 2i+1 :- not 2i.` for `i < m`, then `k` random rules. -/
def genChoice (m k seed : ℕ) : Program ℕ :=
  ((List.range m).flatMap fun i => [⟨2 * i, [], [2 * i + 1]⟩, ⟨2 * i + 1, [], [2 * i]⟩]) ++
    genProgram (2 * m + 1) k seed

/-- Random programs over three to six atoms. -/
def randomFamily : List (Program ℕ) := (List.range 40).map fun i => genProgram (3 + i % 4) (3 + i % 6) (i * 7919 + 17)

/-- Programs with choice pairs. -/
def choiceFamily : List (Program ℕ) := (List.range 24).map fun i => genChoice (1 + i % 3) (2 + i % 4) (i * 104729 + 3)

/-- **Agreement with the brute-force checker**: enumeration lists exactly the stable models, and
its final certificate is accepted for the blocked program; a single solve returns a model the
reduct checker accepts, or a certificate the certificate checker accepts. -/
def agrees (P : Program ℕ) : Bool :=
  (match P.enumerate with
    | .done Ms cert => decide ((Ms.map List.toFinset).toFinset = P.stableModels) && (P.blocked Ms).checkCert cert
    | .outOfFuel => false) &&
  (match P.solve with
    | .sat M => P.isStable M.toFinset
    | .unsat cert => P.checkCert cert && decide (P.stableModels = ∅)
    | .outOfFuel => false)

theorem randomFamily_agrees : (randomFamily.take 10).all agrees = true := by decide +kernel

theorem choiceFamily_agrees : (choiceFamily.take 6).all agrees = true := by decide +kernel

#eval (randomFamily ++ choiceFamily).all agrees
#eval (randomFamily ++ choiceFamily).map fun P => P.stableModels.card
#eval choice.enumerate.models?
#eval oddLoop.solve.certificate?.map List.length
#eval (choice.solveWF.model?, oddLoop.solveWF.model?, tightTwo.solveWF.model?)

end Mettapedia.Logic.ASP.DriverControls
