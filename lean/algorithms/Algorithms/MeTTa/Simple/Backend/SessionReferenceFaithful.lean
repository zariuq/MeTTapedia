import Algorithms.MeTTa.Simple.Backend.SessionReferenceTotal

namespace Algorithms.MeTTa.Simple.Backend.SessionReferenceFaithful

open MeTTailCore.MeTTaIL.Syntax
open Algorithms.MeTTa.Simple

abbrev SessionWF : Session → Prop := Session.WF
abbrev Status := Session.FuelResult

/-- Public fuel policy for the faithful status-based reference backend.
    We reuse the same policy as `SessionReferenceTotal` so the two surfaces can be
    related directly on covered fragments. -/
def referenceFuel (s : Session) : Nat :=
  SessionReferenceTotal.referenceFuel s

/-- The public faithful backend always runs at positive fuel, so it cannot report
    `.outOfFuel` at the top level. -/
theorem referenceFuel_pos (s : Session) : 0 < referenceFuel s := by
  unfold referenceFuel SessionReferenceTotal.referenceFuel
  exact Nat.lt_of_lt_of_le (by decide : 0 < 4096) (Nat.le_max_left 4096 s.maxNodes)

/-- Fuel-indexed faithful evaluator with explicit exhaustion status. -/
abbrev evalWithStateCoreF := Session.evalWithStateCoreF

/-- Fuel-indexed faithful intrinsic evaluator with explicit exhaustion status. -/
abbrev intrinsicStatefulF := Session.intrinsicStatefulF

/-- Public faithful evaluator at the default reference fuel budget. -/
def evalWithStateCore (s : Session) (term : Pattern) :
    Status (Session × List Pattern) :=
  evalWithStateCoreF (referenceFuel s) s term

/-- Public faithful intrinsic evaluator at the default reference fuel budget. -/
def intrinsicStateful (s : Session) (term : Pattern) :
    Status (Option (Session × List Pattern)) :=
  intrinsicStatefulF (referenceFuel s) s term

/-- A successful faithful run preserves `SessionWF`. -/
theorem evalWithStateCoreF_preserves_done
    (fuel : Nat) (s : Session) (term : Pattern)
    (hdone : evalWithStateCoreF fuel s term = .done (s', out))
    (hs : SessionWF s) :
    SessionWF s' :=
  Session.evalWithStateCoreF_preserves fuel s term hdone hs

/-- A successful faithful intrinsic run preserves `SessionWF`. -/
theorem intrinsicStatefulF_preserves_done
    (fuel : Nat) (s : Session) (term : Pattern)
    (hdone : intrinsicStatefulF fuel s term = .done (some (s', out)))
    (hs : SessionWF s) :
    SessionWF s' :=
  Session.intrinsicStatefulF_preserves fuel s term hdone hs

/-- At matching fuel, a successful faithful run agrees with the total reference evaluator. -/
theorem evalWithStateCoreF_done_eq_total
    (fuel : Nat) (s : Session) (term : Pattern)
    (hdone : evalWithStateCoreF fuel s term = .done res) :
    SessionReferenceTotal.totalEvalWithStateCore fuel s term = res :=
  Session.evalWithStateCoreF_done_eq_N fuel s term res hdone

/-- At matching fuel, a successful faithful intrinsic run agrees with the total
reference intrinsic evaluator. -/
theorem intrinsicStatefulF_done_eq_total
    (fuel : Nat) (s : Session) (term : Pattern)
    (hdone : intrinsicStatefulF fuel s term = .done r) :
    SessionReferenceTotal.totalIntrinsicStateful fuel s term = r :=
  Session.intrinsicStatefulF_done_eq_N fuel s term r hdone

/-- A successful public faithful run agrees with the public total reference backend. -/
theorem evalWithStateCore_done_eq_total
    (s : Session) (term : Pattern)
    (hdone : evalWithStateCore s term = .done res) :
    SessionReferenceTotal.evalWithStateCore s term = res := by
  exact evalWithStateCoreF_done_eq_total (referenceFuel s) s term hdone

/-- At public fuel, the faithful evaluator is always `.done`, and the payload is the
    public total-reference evaluator result. -/
theorem evalWithStateCore_eq_done_total
    (s : Session) (term : Pattern) :
    evalWithStateCore s term = .done (SessionReferenceTotal.evalWithStateCore s term) := by
  unfold evalWithStateCore SessionReferenceTotal.evalWithStateCore
  exact Session.evalWithStateCoreF_eq_done_of_pos (referenceFuel s) s term (referenceFuel_pos s)

/-- A successful public faithful intrinsic run agrees with the public total
reference intrinsic backend. -/
theorem intrinsicStateful_done_eq_total
    (s : Session) (term : Pattern)
    (hdone : intrinsicStateful s term = .done r) :
    SessionReferenceTotal.intrinsicStateful s term = r := by
  exact intrinsicStatefulF_done_eq_total (referenceFuel s) s term hdone

/-- At public fuel, the faithful intrinsic evaluator is always `.done`, and the payload
    is the public total-reference intrinsic result. -/
theorem intrinsicStateful_eq_done_total
    (s : Session) (term : Pattern) :
    intrinsicStateful s term = .done (SessionReferenceTotal.intrinsicStateful s term) := by
  unfold intrinsicStateful SessionReferenceTotal.intrinsicStateful
  exact Session.intrinsicStatefulF_eq_done_of_pos (referenceFuel s) s term (referenceFuel_pos s)

/-- A successful public faithful run preserves `SessionWF`. -/
theorem evalWithStateCore_preserves_done
    (s : Session) (term : Pattern)
    (hdone : evalWithStateCore s term = .done (s', out))
    (hs : SessionWF s) :
    SessionWF s' := by
  exact evalWithStateCoreF_preserves_done (referenceFuel s) s term hdone hs

/-- A successful public faithful intrinsic run preserves `SessionWF`. -/
theorem intrinsicStateful_preserves_done
    (s : Session) (term : Pattern)
    (hdone : intrinsicStateful s term = .done (some (s', out)))
    (hs : SessionWF s) :
    SessionWF s' := by
  exact intrinsicStatefulF_preserves_done (referenceFuel s) s term hdone hs

end Algorithms.MeTTa.Simple.Backend.SessionReferenceFaithful
