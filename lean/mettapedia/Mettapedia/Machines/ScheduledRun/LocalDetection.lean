import Mettapedia.Machines.ScheduledRun.Certificates
import Mettapedia.Machines.ScheduledRun.Detection

/-!
# Sound local-interval detection and a conservative detector portfolio

Candidate words are extracted from the actual prefix; a missing state refuses
the candidate. Both observed endpoints must be its live head. All proposed
edges and local clock licences are then checked. The all-interval search is
a correctness prototype, not a claimed efficient native candidate enumerator.
Combining its sound claims with the global monitor retains the latter's
finite-state completeness without choosing a new runtime default.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ScheduledRun

universe u
variable {S : Type u} [DecidableEq S]

def checkInterval (next : S → List S) (mode : Mode) (trace : Nat → Option S)
    (first last : Nat) : Bool :=
  if first < last then
    match (List.range (last - first)).mapM (fun offset => trace (first + offset)) with
    | none => false
    | some path => decide (trace first = path.head?) && decide (trace last = path.head?) &&
        checkLoop next mode first path
  else false

theorem checkInterval_sound (next : S → List S) (mode : Mode) (initial : S) (first last : Nat)
    (checked : checkInterval next mode (run next mode.schedule initial) first last = true) :
    Nonterminating next mode.schedule initial := by
  unfold checkInterval at checked
  split at checked
  · split at checked
    · cases checked
    · rename_i path _extracted
      have pieces := Bool.and_eq_true_iff.mp checked
      have endpoint := Bool.and_eq_true_iff.mp pieces.1
      exact (checkLoop_sound_of_entry next mode initial first path pieces.2 (of_decide_eq_true endpoint.1)).1
  · cases checked

def localClaimAt (next : S → List S) (mode : Mode) (trace : Nat → Option S) (last : Nat) : Bool :=
  (List.range last).any fun first => checkInterval next mode trace first last

theorem localClaimAt_sound (next : S → List S) (mode : Mode) (initial : S) (turn : Nat)
    (claim : localClaimAt next mode (run next mode.schedule initial) turn = true) :
    Nonterminating next mode.schedule initial := by
  obtain ⟨first, _, checked⟩ := List.any_eq_true.mp claim
  exact checkInterval_sound next mode initial first turn checked

def portfolioClaimAt (next : S → List S) (mode : Mode) (trace : Nat → Option S) (turn : Nat) : Bool :=
  claimsAt next mode trace turn || localClaimAt next mode trace turn

theorem portfolioClaimAt_sound (next : S → List S) (mode : Mode) (initial : S) (turn : Nat)
    (claim : portfolioClaimAt next mode (run next mode.schedule initial) turn = true) :
    Nonterminating next mode.schedule initial := by
  rcases Bool.or_eq_true_iff.mp claim with globalClaim | localClaim
  · exact claimsAt_sound next mode initial turn globalClaim
  · exact localClaimAt_sound next mode initial turn localClaim

theorem finite_portfolio_reports_iff (next : S → List S) (mode : Mode) (initial : S)
    (finite : (visited next mode.schedule initial).Finite) :
    (∃ turn, portfolioClaimAt next mode (run next mode.schedule initial) turn = true) ↔
      Nonterminating next mode.schedule initial := by
  constructor
  · rintro ⟨turn, claim⟩
    exact portfolioClaimAt_sound next mode initial turn claim
  · intro infinite
    obtain ⟨turn, globalClaim⟩ := (finite_monitor_reports_iff next mode initial finite).mpr infinite
    exact ⟨turn, Bool.or_eq_true_iff.mpr (Or.inl globalClaim)⟩

end Mettapedia.Machines.ScheduledRun
