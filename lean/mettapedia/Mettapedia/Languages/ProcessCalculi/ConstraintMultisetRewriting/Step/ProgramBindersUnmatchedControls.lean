import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramBindersUnmatched
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramBindersPending

/-!
# Controls for unmatched calls under binders

The constants are `f` and `g`, the ambient context `[f, g]`.
- **Returned:** `(f (λy. y))` with only `(= (f (λx. $N)) $N)` is unmatched, since `$N` cannot capture
  `y`. The unmatched firing is admitted, it reads exactly `(f (λy. y))`, the actual worklist certifies
  the absence, and the reference semantics evaluates the call to itself.
- **Refused:** beside it, the η equation `(= (f (λx. $M x)) (λz. $M z))` matches the same call, so
  the unmatched firing is refused and the η firing is admitted. With the capture equation alone,
  `(f (λy. g))` is matched (by `$N := g`) and refused too; no budget certifies an absence there.
- **Pending:** at `(f (λy. y y))` the only matching problem is the non-pattern `$M x x`. The call is
  matched, so it is not returned; the guard refuter's worklist never refutes it, at any fuel. The
  equation's own firing problem stays pending at every fuel (`Controls.twice_pending_on_step`).
- **Unknown:** `(= g (g $Y))` turns `g` into `(g $Y)` with `$Y` unknown: the state reads `(g g)` and
  `(g f)`. No equation matches any reading, so the call is returned, the absence is certified, it
  holds under every later binding of `$Y`, and no equation fires after the return.
- **Not returned while a binding could make a redex:** after `(= g $Y)`, the call reads `f`, which is
  unmatched, and `(f (λy. g y))`, which the η equation matches. Absence is asked at every future
  solution, so the call is not returned.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramBinders.UnmatchedControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open LambdaContextualRung (sig Srt appT lamT)
open LambdaComparison (app lam app_inj lam_inj)
open ContextualPatternFragment (Pattern generator_pattern)
open Controls

/-! ## Returned: `(f (λy. y))` with only the capture equation -/

theorem capture_call_unmatched : Unmatched captureProgram captureCall := fun _ θ => capture_unmatched θ

theorem capture_returns : UnmatchedAdmitted captureProgram (initial captureCall) :=
  (returns_iff _ captureCall (initial_determines captureCall)).mpr capture_call_unmatched

/-- **The call returns itself.** -/
theorem capture_returns_itself (answer : Term sig Consts .term) :
    Reads (withReturn captureProgram) (unmatchedDestination captureProgram (initial captureCall) capture_returns)
        answer ↔ answer = captureCall :=
  unmatched_reads_iff _ captureCall (initial_determines captureCall) capture_returns answer

/-- The absence is decided by the actual worklist. -/
theorem capture_return_certified : ∃ budget, certifiesUnmatched captureProgram budget (initial captureCall) = true :=
  certifies_of_unmatched _ (initial_pattern captureCall) (fun _ => lhsCapture_pattern)
    (fun future solution call reads => by
      rw [(initial_determines captureCall).2 future solution call reads]
      exact capture_call_unmatched)

theorem capture_evaluates : Evaluates captureProgram captureCall captureCall := ⟨.refl, capture_call_unmatched⟩

/-- After the return, the capture equation still does not fire. -/
theorem capture_final : ¬ Admitted (withReturn captureProgram)
    (unmatchedDestination captureProgram (initial captureCall) capture_returns) (some ()) :=
  returned_is_final _ _ (initial_holds captureCall) capture_returns ()

/-! ## Refused: an equation that matches -/

/-- The η equation beside the capture equation. -/
def matchProgram : Bool → Equation sig Consts .term
  | false => etaEquation
  | true => captureEquation

/-- `(f (λx. $M x))` matches `(f (λy. y))` with `$M x := x`. -/
theorem eta_matches_capture_call : Matches etaEquation captureCall (fun _ => .var .zero) := by
  change instantiate (etaEquation.assign _ (ground sig)) lhsEta = Rigid.includeTerm (ground sig) captureCall
  rw [instantiate_lhsEta]
  rfl

theorem matched_refused : ¬ UnmatchedAdmitted matchProgram (initial captureCall) := fun valid =>
  (returns_iff _ captureCall (initial_determines captureCall)).mp valid false _ eta_matches_capture_call

/-- The matching equation fires instead. -/
theorem matched_fires : Admitted (withReturn matchProgram) (initial captureCall) (some false) :=
  admitted_of_match _ (some false) _ captureCall (initial_reads captureCall) _ eta_matches_capture_call

/-- With the capture equation alone, `(f (λy. g))` is matched and refused. -/
theorem constant_refused : ¬ UnmatchedAdmitted captureProgram (initial constantCall) := by
  intro valid
  obtain ⟨θ, matched, _⟩ := constant_answers
  exact (returns_iff _ constantCall (initial_determines constantCall)).mp valid () θ matched

theorem constant_never_certified (budget : Option Unit → Nat) :
    certifiesUnmatched captureProgram budget (initial constantCall) = false := by
  obtain ⟨θ, matched, _⟩ := constant_answers
  exact matched_never_certified _ _ (initial_holds constantCall) (initial_reads constantCall) () θ matched budget

/-! ## Pending: the non-pattern `$M x x` -/

abbrev twiceStartReturn : State (withReturn twiceProgram) := initial twiceCall

theorem twice_not_unmatched : ¬ Unmatched twiceProgram twiceCall := fun unmatched =>
  unmatched () bothFirst matches_bothFirst

/-- The matched call is not returned. -/
theorem twice_not_returned : ¬ UnmatchedAdmitted twiceProgram twiceStartReturn := fun valid =>
  twice_not_unmatched ((returns_iff _ twiceCall (initial_determines twiceCall)).mp valid)

theorem twice_never_certified (budget : Option Unit → Nat) :
    certifiesUnmatched twiceProgram budget twiceStartReturn = false :=
  matched_never_certified _ _ (initial_holds twiceCall) (initial_reads twiceCall) () bothFirst matches_bothFirst budget

/-- **Never refuted.** At every fuel, the guard refuter's worklist on the call's joint problem
returns a residual, not a refutation. -/
theorem twice_absence_never_refuted (fuel : Nat) :
    letI := twiceStartReturn.1.equality
    ContextualGuardRefutation.certifiesRowAbsence (locals (withReturn twiceProgram))
      (active (withReturn twiceProgram) twiceStartReturn.1.declarations) fuel
      (ContextualActivatedStep.problem (locals (withReturn twiceProgram)) twiceStartReturn.1.declarations
        twiceStartReturn.1.occupied (selection twiceStartReturn.2) (unmatchedRule twiceProgram twiceStartReturn.1.declarations)
        twiceStartReturn.1.inventory.rows twiceStartReturn.1.inventory.configuration)
      (ContextualGuardedStep.guardRows (locals (withReturn twiceProgram)) twiceStartReturn.1.declarations
        twiceStartReturn.1.inventory.rows twiceStartReturn.2)
      (checkAt twiceProgram twiceStartReturn ()) = false := by
  let _ : DecidableEq twiceStartReturn.1.Names := twiceStartReturn.1.equality
  cases computed : ContextualGuardRefutation.certifiesRowAbsence (locals (withReturn twiceProgram))
      (active (withReturn twiceProgram) twiceStartReturn.1.declarations) fuel
      (ContextualActivatedStep.problem (locals (withReturn twiceProgram)) twiceStartReturn.1.declarations
        twiceStartReturn.1.occupied (selection twiceStartReturn.2) (unmatchedRule twiceProgram twiceStartReturn.1.declarations)
        twiceStartReturn.1.inventory.rows twiceStartReturn.1.inventory.configuration)
      (ContextualGuardedStep.guardRows (locals (withReturn twiceProgram)) twiceStartReturn.1.declarations
        twiceStartReturn.1.inventory.rows twiceStartReturn.2)
      (checkAt twiceProgram twiceStartReturn ()) with
  | false => rfl
  | true =>
      refine False.elim (twice_not_returned ?_)
      refine (admitted_of_match twiceStartReturn none (generator (ground sig)) twiceCall (initial_reads twiceCall)
        (fun _ => twiceCall) (return_matches twiceCall)).guard ((guarded_checks_list_iff _ _ _ _ _).mpr ?_)
      intro key member
      obtain ⟨index, rfl⟩ := (mem_returnCarriers key).mp member
      intro Later later candidate solved occurrence present
      have only : occurrence = twiceStartReturn.2 := by
        rw [(initial_holds (program := withReturn twiceProgram) twiceCall).1] at present
        exact Finset.mem_singleton.mp present
      subst only
      exact ContextualGuardRefutation.certifiesRowAbsence_sound _ _ fuel _ _ _ computed candidate solved

/-! ## Unknown: `(g $Y)` stays unmatched under every later binding -/

abbrev unknownArity : Unit → MetaArity sig := holeArity outer

/-- `(g $Y)`. -/
def introRhs : Term (signature sig unknownArity) Consts .term := app _ (.var (.succ .zero)) (generator _ ())

/-- `(= g (g $Y))`: the hole occurs only on the right, so its answer keeps an unknown. -/
def introEquation : Equation sig Consts .term := ⟨Unit, inferInstance, unknownArity, .var (.succ .zero), introRhs⟩

def unknownProgram : Bool → Equation sig Consts .term
  | false => introEquation
  | true => captureEquation

theorem intro_matches (θ : introEquation.Ground) : Matches introEquation gC θ := rfl

theorem instantiate_introRhs {W : Type} {target : W → MetaArity sig} (change : Assignment unknownArity target) :
    instantiate change introRhs = app target (.var (.succ .zero)) (change ()) := by
  change app target (.var (.succ .zero)) (instantiate change (generator _ ())) = _
  rw [instantiate_generator]

theorem intro_answered (t : Term sig Consts .term) :
    instantiate (introEquation.assign (fun _ => t) (ground sig)) introEquation.rhs =
      Rigid.includeTerm (ground sig) (appT gC t) := by
  change instantiate (introEquation.assign (fun _ => t) (ground sig)) introRhs = _
  rw [instantiate_introRhs]
  rfl

theorem intro_answers_shape {call answer : Term sig Consts .term} (answered : Answers introEquation call answer) :
    ∃ t, answer = appT gC t := by
  obtain ⟨θ, _, read⟩ := answered
  change instantiate (introEquation.assign θ (ground sig)) introRhs = _ at read
  rw [instantiate_introRhs] at read
  have same : Rigid.includeTerm (ground sig) (appT gC (θ ())) = Rigid.includeTerm (ground sig) answer := read
  exact ⟨θ (), (Rigid.include_injective _ _ _ same).symm⟩

/-- No equation matches `(g t)`: heads clash, under the binder too. -/
theorem g_unmatched (t : Term sig Consts .term) : Unmatched unknownProgram (appT gC t) := by
  intro index θ matched
  cases index with
  | false => cases matched
  | true =>
      change instantiate (captureEquation.assign θ (ground sig)) lhsCapture =
        Rigid.includeTerm (ground sig) (appT gC t) at matched
      rw [instantiate_lhsCapture] at matched
      have heads := (app_inj matched).1
      cases heads

abbrev unknownStart : State (withReturn unknownProgram) := initial gC

theorem intro_admitted : Admitted (withReturn unknownProgram) unknownStart (some false) :=
  admitted_of_match unknownStart (some false) (generator (ground sig)) gC (initial_reads gC) (fun _ => gC)
    (intro_matches _)

/-- The state after `(= g (g $Y))` fires. -/
abbrev afterIntro : State (withReturn unknownProgram) :=
  destination (withReturn unknownProgram) unknownStart (some false) intro_admitted

theorem afterIntro_reads (t : Term sig Consts .term) : Reads (withReturn unknownProgram) afterIntro (appT gC t) :=
  ⟨_, _, _, destination_reads unknownStart (some false) intro_admitted (generator (ground sig)) gC (initial_reads gC)
    (fun _ => t) (intro_matches _) (appT gC t) (intro_answered t)⟩

/-- The unknown is real: two different readings. -/
theorem afterIntro_has_unknown :
    Reads (withReturn unknownProgram) afterIntro (appT gC gC) ∧ Reads (withReturn unknownProgram) afterIntro (appT gC fC) ∧
      appT gC gC ≠ appT gC fC := by
  refine ⟨afterIntro_reads gC, afterIntro_reads fC, fun same => ?_⟩
  have arguments := (appT_inj same).2
  cases arguments

theorem afterIntro_readings {answer : Term sig Consts .term} (reads : Reads (withReturn unknownProgram) afterIntro answer) :
    ∃ t, answer = appT gC t := by
  obtain ⟨Future, future, solution, readsAt⟩ := reads
  obtain ⟨old, call, readsCall, answered⟩ :=
    destination_reflected unknownStart (some false) intro_admitted _ (initial_holds gC) solution answer readsAt
  exact intro_answers_shape answered

theorem afterIntro_holds : Holds (withReturn unknownProgram) afterIntro
    (output (withReturn unknownProgram) unknownStart.1.declarations (some false) unknownStart.1.occupied unknownStart.2) :=
  destination_holds unknownStart (some false) intro_admitted (initial_holds gC).1

theorem afterIntro_unmatched : UnmatchedReadings unknownProgram afterIntro := by
  intro Future future solution call reads
  obtain ⟨t, rfl⟩ := afterIntro_readings ⟨_, _, solution, reads⟩
  exact g_unmatched t

/-- **The call with an unknown is returned.** -/
theorem unknown_returns : UnmatchedAdmitted unknownProgram afterIntro :=
  (unmatched_admitted_iff afterIntro _ afterIntro_holds).mpr ⟨⟨_, afterIntro_reads gC⟩, afterIntro_unmatched⟩

theorem introLhs_pattern : Pattern sig introEquation.arity introEquation.lhs := .object _

theorem introRhs_pattern : Pattern sig introEquation.arity introEquation.rhs :=
  .rigid (S := sig) LambdaContextualRung.Op.app _ (.cons _ _ (.object _) (.cons _ _ (generator_pattern _) .nil))

theorem unknown_lhs_patterns : ∀ index, Pattern sig (unknownProgram index).arity (unknownProgram index).lhs
  | false => introLhs_pattern
  | true => lhsCapture_pattern

/-- The absence is decided by the actual worklist, with the unknown still open. -/
theorem unknown_return_certified : ∃ budget, certifiesUnmatched unknownProgram budget afterIntro = true :=
  certifies_of_unmatched afterIntro
    (destination_pattern unknownStart (some false) intro_admitted (initial_pattern gC) introLhs_pattern introRhs_pattern)
    unknown_lhs_patterns afterIntro_unmatched

/-- **Stable under every later binding.** Whatever `$Y` is later bound to, in any frame, no
instance of any left-hand side is the bound call. -/
theorem unknown_stays_unmatched {Future : Type} (future : Future → MetaArity sig)
    (solution : Assignment afterIntro.1.declarations future)
    (solved : ContextualFrameUnifier.Models solution afterIntro.1.inventory.configuration.equations)
    {Later : Type} (later : Later → MetaArity sig) (binding : Assignment future later)
    (index : Bool) (θ : Assignment (unknownProgram index).arity later) :
    instantiate θ (unknownProgram index).lhs ≠
      instantiate binding (instantiate solution
        (output (withReturn unknownProgram) unknownStart.1.declarations (some false) unknownStart.1.occupied
          unknownStart.2)) :=
  absence_stable afterIntro _ afterIntro_holds afterIntro_unmatched future solution solved later binding index θ

/-- After the return, no equation fires. -/
theorem unknown_final (index : Bool) :
    ¬ Admitted (withReturn unknownProgram) (unmatchedDestination unknownProgram afterIntro unknown_returns) (some index) :=
  returned_is_final afterIntro _ afterIntro_holds unknown_returns index

/-! ## An unknown that a later binding makes a redex is not returned -/

theorem two_way_admitted : Admitted (withReturn twoWayProgram) (initial gC) (some true) :=
  admitted_of_match (initial gC) (some true) (generator (ground sig)) gC (initial_reads gC) (fun _ => fC) rfl

/-- After `(= g $Y)` fires, the store keeps the unknown `$Y`. -/
abbrev afterUnknown : State (withReturn twoWayProgram) :=
  destination (withReturn twoWayProgram) (initial gC) (some true) two_way_admitted

theorem afterUnknown_reads (answer : Term sig Consts .term) : Reads (withReturn twoWayProgram) afterUnknown answer :=
  ⟨_, _, _, destination_reads (initial gC) (some true) two_way_admitted (generator (ground sig)) gC (initial_reads gC)
    (fun _ => answer) rfl answer (instantiate_generator _ ())⟩

theorem f_unmatched : Unmatched twoWayProgram fC := by
  intro index θ matched
  cases index with
  | true => cases matched
  | false =>
      change instantiate (etaEquation.assign θ (ground sig)) lhsEta = Rigid.includeTerm (ground sig) fC at matched
      rw [instantiate_lhsEta] at matched
      cases matched

/-- **Not returned.** One reading, `f`, is unmatched; another, `(f (λy. g y))`, is matched by the η
equation. Absence is asked at every future solution, so the unknown is not returned as itself: a
later binding could make it a redex. -/
theorem unknown_redex_not_returned :
    Reads (withReturn twoWayProgram) afterUnknown fC ∧ Unmatched twoWayProgram fC ∧
      ¬ UnmatchedAdmitted twoWayProgram afterUnknown := by
  refine ⟨afterUnknown_reads fC, f_unmatched, fun valid => ?_⟩
  have holds := destination_holds (initial gC) (some true) two_way_admitted (initial_holds gC).1
  obtain ⟨_, absent⟩ := (unmatched_admitted_iff afterUnknown _ holds).mp valid
  obtain ⟨Future, future, solution, reads⟩ := afterUnknown_reads callEta
  obtain ⟨θ, matched, _⟩ := (eta_answers (etaExpand gC)).mpr rfl
  exact absent future solution callEta reads false θ matched

#print axioms capture_returns
#print axioms unknown_redex_not_returned
#print axioms capture_returns_itself
#print axioms capture_return_certified
#print axioms capture_evaluates
#print axioms capture_final
#print axioms matched_refused
#print axioms matched_fires
#print axioms constant_refused
#print axioms constant_never_certified
#print axioms twice_not_returned
#print axioms twice_never_certified
#print axioms twice_absence_never_refuted
#print axioms g_unmatched
#print axioms afterIntro_has_unknown
#print axioms unknown_returns
#print axioms unknown_return_certified
#print axioms unknown_stays_unmatched
#print axioms unknown_final

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramBinders.UnmatchedControls
