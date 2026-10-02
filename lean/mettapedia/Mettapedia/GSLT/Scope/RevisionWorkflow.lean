import Mettapedia.GSLT.Scope.WorldModel
import Mettapedia.GSLT.Scope.Authority
import Mettapedia.GSLT.Scope.Simulation
import Mettapedia.GSLT.LanguageDef.GSLTILOperationalEquipment

/-!
# A revision workflow: which results survive which change

A road map with four towns and four roads: two major roads `a–b–d` and two
minor roads `a–c–d`.  The world state is evidence about each road, as counts
of reports that it is open and that it is closed, read by the world-model
calculus (`reading`, lawful by `coreLaws`).  A road counts as open when open
reports outnumber closed ones, and the answer of interest is whether `d` is
reachable from `a`.

Four kinds of change are kept distinct.
* **World revision**: a road closes, a revision of the world-model calculus
  that adds a closed report (`close`).
* **Abstraction change**: minor roads are hidden (`majorView`), a forgetting.
* **Strategy change**: the search stops as soon as the target is reached
  (`Strategy.earlyExit`), an improvement in the sense of `Improves`.
* **Implementation refinement**: the world is stored as a log of reports and
  read through its tally (`tally`), with closing a road realised by appending
  a report; a refinement square.

A result *stays valid* under a change when it is unchanged, and *stays
usable* when its new value is computable from its old value alone: the update
square closes (`Supports`).

**After a world revision.**
* The evidence stays usable, because the observational quotient supports
  every revision of a lawful reading (`evidence_supports_close`).  So does the
  major view (`majorView_supports_close`).
* **The key negative control: preserving the present answer is not
  preserving the future.**  With every road open, and with only the major
  roads open, `d` is reachable from `a`; after `b–d` closes it is reachable in
  the first world and not in the second.  The answer view identifies the two
  worlds now and separates them after the revision, so it does not support
  the revision (`answer_not_supports_close`).  The same holds for the whole
  map of open roads, which determines every present answer
  (`openMap_determines_answer`): two worlds with one map but different
  evidence margins separate after one closed report
  (`openMap_not_supports_close`).

**After an abstraction change.**  The answer over major roads is still
available (`majorAnswer_descends`); the full answer is not
(`answer_not_descends_majorView`).

**After a strategy change.**  Every answer stays valid, since the early-exit
search improves the exhaustive one (`earlyExit_improves`), while the search
cost does not (`earlyExit_not_preserves_cost`).

**After an implementation refinement.**  Closing a road by appending a report
refines closing it in the evidence (`tally_close`): the refinement square
commutes, so every consumer of the evidence reads the same value
(`consumer_tally_close`).  In the operational equipment, the tally is a
tight arrow between the two implementations as transition systems
(`tallyTight`), and closing a road is a loose route on each side; the
refinement square is a cell of the equipment (`closeRefinementSquare`).
Controls: replacing a road's reports by the latest one is not a refinement
(`closeLatest_not_refines`), and admits no refinement square
(`closeLatest_no_refinementSquare`); a consumer reading the first report
does not descend to the tally (`firstReport_not_descends`).

**Pairs of changes.**
* Revision and abstraction: the major view and closing a road commute
  (`majorView_supports_close`); the open-road map and the answer view do not.
* Revision and strategy: the improvement holds on every revised world
  (`earlyExit_answer_after_close`).
* Revision and implementation: the refinement square (`tally_close`).
* Abstraction and strategy: the improvement holds over the major map
  (`earlyExit_improves_major`), whose answers differ from the full ones
  (`majorAnswer_ne_answer`).
* Abstraction and implementation: hiding minor roads commutes with the tally
  (`majorView_tally`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Scope.RoadMap

open Mettapedia.GSLT.Core.NonFactorization
open Mettapedia.OSLF.Framework.WMCalculusSemantics
open Mettapedia.OSLF.Framework.WMCalculusObservationalQuotient

/-! ## The map -/

/-- Towns. -/
inductive Town
  | a
  | b
  | c
  | d
  deriving DecidableEq

/-- Roads: the major roads `ab`, `bd` and the minor roads `ac`, `cd`. -/
inductive Road
  | ab
  | bd
  | ac
  | cd
  deriving DecidableEq

/-- The towns a road joins. -/
def Road.ends : Road → Town × Town
  | .ab => (.a, .b)
  | .bd => (.b, .d)
  | .ac => (.a, .c)
  | .cd => (.c, .d)

/-- Major roads. -/
def Road.major : Road → Bool
  | .ab => true
  | .bd => true
  | .ac => false
  | .cd => false

/-- All roads. -/
def roads : List Road :=
  [.ab, .bd, .ac, .cd]

/-- All towns. -/
def towns : List Town :=
  [.a, .b, .c, .d]

/-! ## Search -/

/-- Towns joined by an open road. -/
def adjacent (isOpen : Road → Bool) (s t : Town) : Bool :=
  roads.any fun r => isOpen r && (decide (r.ends = (s, t)) || decide (r.ends = (t, s)))

/-- One round of search: add every town adjacent to a reached town. -/
def expand (isOpen : Road → Bool) (reached : Town → Bool) (t : Town) : Bool :=
  reached t || towns.any fun s => reached s && adjacent isOpen s t

/-- The towns reached from `source` after `n` rounds. -/
def reachedAfter (isOpen : Road → Bool) (source : Town) : ℕ → Town → Bool
  | 0 => fun t => decide (t = source)
  | n + 1 => expand isOpen (reachedAfter isOpen source n)

/-- A town once reached stays reached. -/
theorem reachedAfter_succ (isOpen : Road → Bool) (source : Town) {n : ℕ} {t : Town}
    (reached : reachedAfter isOpen source n t = true) :
    reachedAfter isOpen source (n + 1) t = true := by
  change (reachedAfter isOpen source n t || _) = true
  rw [reached, Bool.true_or]

theorem reachedAfter_mono (isOpen : Road → Bool) (source : Town) {t : Town} {n : ℕ}
    (reached : reachedAfter isOpen source n t = true) :
    ∀ k, reachedAfter isOpen source (n + k) t = true
  | 0 => reached
  | k + 1 => reachedAfter_succ isOpen source (reachedAfter_mono isOpen source reached k)

/-- Search strategies. -/
inductive Strategy
  /-- Run every round. -/
  | exhaustive
  /-- Stop as soon as the target is reached. -/
  | earlyExit
  deriving DecidableEq

/-- The rounds a search may use: three suffice for four towns. -/
def budget : ℕ :=
  3

/-- Search with early exit from round `round`, with `fuel` rounds left:
the answer and the number of rounds run. -/
def searchFrom (isOpen : Road → Bool) (source target : Town) : ℕ → ℕ → Bool × ℕ
  | round, 0 => (reachedAfter isOpen source round target, round)
  | round, fuel + 1 =>
      if reachedAfter isOpen source round target then (true, round)
      else searchFrom isOpen source target (round + 1) fuel

/-- Running a strategy: its answer and its cost in rounds. -/
def Strategy.run : Strategy → (Road → Bool) → Town → Town → Bool × ℕ
  | .exhaustive, isOpen, source, target => (reachedAfter isOpen source budget target, budget)
  | .earlyExit, isOpen, source, target => searchFrom isOpen source target 0 budget

theorem searchFrom_answer (isOpen : Road → Bool) (source target : Town) :
    ∀ round fuel, (searchFrom isOpen source target round fuel).1 =
      reachedAfter isOpen source (round + fuel) target
  | round, 0 => rfl
  | round, fuel + 1 => by
      unfold searchFrom
      split
      · next reached =>
          have later := reachedAfter_mono isOpen source reached (fuel + 1)
          rw [later]
      · rw [searchFrom_answer isOpen source target (round + 1) fuel]
        congr 1
        omega

theorem searchFrom_cost_le (isOpen : Road → Bool) (source target : Town) :
    ∀ round fuel, (searchFrom isOpen source target round fuel).2 ≤ round + fuel
  | round, 0 => le_rfl
  | round, fuel + 1 => by
      unfold searchFrom
      split
      · exact Nat.le_add_right round (fuel + 1)
      · have bound := searchFrom_cost_le isOpen source target (round + 1) fuel
        omega

/-! ## The world as evidence -/

/-- Evidence about a road: open reports and closed reports. -/
abbrev Evidence : Type :=
  ℕ × ℕ

/-- A world state: evidence about every road. -/
abbrev World : Type :=
  Road → Evidence

/-- **The world-model reading of road evidence**: revision adds evidence,
extraction reads one road. -/
def reading : WMReading World Road Evidence where
  revise first second r := first r + second r
  extract state r := state r
  combine := (· + ·)
  zero := 0
  world _ _ := (1, 0)
  query _ := .ab

theorem coreLaws : reading.CoreLaws where
  extract_revise _ _ _ := rfl
  combine_comm := add_comm
  combine_assoc := add_assoc
  combine_zero := add_zero

/-- A road is open when open reports outnumber closed ones. -/
def isOpen (w : World) (r : Road) : Bool :=
  decide ((w r).2 < (w r).1)

/-- One closed report about `r`. -/
def closedReport (r : Road) : World := fun r' => if r' = r then (0, 1) else (0, 0)

/-- **World revision**: road `r` closes, by revising with a closed report. -/
def close (r : Road) (w : World) : World :=
  reading.revise w (closedReport r)

/-- The answer: is `d` reachable from `a`? -/
def answer (w : World) : Bool :=
  (Strategy.exhaustive.run (isOpen w) .a .d).1

/-- The map of open roads. -/
def openMap (w : World) : Road → Bool :=
  isOpen w

/-- Every road reported open once. -/
def allOpen : World := fun _ => (1, 0)

/-- Minor roads reported closed, major roads open. -/
def majorOnly : World
  | .ac => (0, 1)
  | .cd => (0, 1)
  | _ => (1, 0)

/-! ## After a world revision -/

/-- **The evidence stays usable**: the observational quotient of the lawful
reading supports every closing of a road. -/
theorem evidence_supports_close (r : Road) : Supports (classOf reading) (close r) :=
  (WorldModel.revisions_supported_of_coreLaws coreLaws).1 (closedReport r)

/-- The map of open roads determines every present answer. -/
theorem openMap_determines_answer : Factors openMap answer :=
  ⟨fun isOpen => (Strategy.exhaustive.run isOpen .a .d).1, fun _ => rfl⟩

theorem answer_allOpen : answer allOpen = true := by decide

theorem answer_majorOnly : answer majorOnly = true := by decide

theorem answer_close_allOpen : answer (close .bd allOpen) = true := by decide

theorem answer_close_majorOnly : answer (close .bd majorOnly) = false := by decide

/-- **Key negative control: the present answer does not support the next
revision.**  Two worlds with the same answer now have different answers after
`b–d` closes. -/
theorem answer_not_supports_close : ¬ Supports answer (close .bd) :=
  not_supports_of_split (x := allOpen) (y := majorOnly)
    (answer_allOpen.trans answer_majorOnly.symm)
    (by rw [answer_close_allOpen, answer_close_majorOnly]; decide)

/-- A world whose road `b–d` has a wide margin. -/
def wideMargin : World
  | .bd => (5, 0)
  | .ac => (0, 1)
  | .cd => (0, 1)
  | _ => (1, 0)

/-- **Even the whole map of open roads does not support the revision**: the
two worlds have one map, and one closed report closes `b–d` in the second
only. -/
theorem openMap_not_supports_close : ¬ Supports openMap (close .bd) := by
  apply not_supports_of_split (x := wideMargin) (y := majorOnly)
  · funext r
    cases r <;> decide
  · intro same
    have atBD := congrFun same .bd
    revert atBD
    decide

/-- The answer after the revision is not valid: it changes. -/
theorem answer_not_valid_close : answer (close .bd majorOnly) ≠ answer majorOnly := by
  decide

/-! ## After an abstraction change -/

/-- **Abstraction change**: evidence about major roads only. -/
def majorView (w : World) (r : {r : Road // r.major = true}) : Evidence :=
  w r.1

/-- The answer over major roads. -/
def majorAnswer (w : World) : Bool :=
  (Strategy.exhaustive.run (fun r => r.major && isOpen w r) .a .d).1

/-- **The major answer is still available after hiding minor roads.** -/
theorem majorAnswer_descends : Factors majorView majorAnswer := by
  refine ⟨fun v => (Strategy.exhaustive.run (fun r => match r with
      | .ab => decide ((v ⟨.ab, rfl⟩).2 < (v ⟨.ab, rfl⟩).1)
      | .bd => decide ((v ⟨.bd, rfl⟩).2 < (v ⟨.bd, rfl⟩).1)
      | .ac => false
      | .cd => false) .a .d).1, fun _ => rfl⟩

/-- Closing `b–d` in the world with every road open. -/
def detour : World :=
  close .bd allOpen

/-- Closing `b–d` in the world with only major roads open. -/
def blocked : World :=
  close .bd majorOnly

theorem majorView_detour_blocked : majorView detour = majorView blocked := by
  funext r
  obtain ⟨r, major⟩ := r
  cases r <;> first | rfl | exact absurd major (by decide)

/-- **The full answer is not available after hiding minor roads.** -/
theorem answer_not_descends_majorView : ¬ Factors majorView answer :=
  NonTrivialFiber.not_factors ⟨detour, blocked, majorView_detour_blocked, by decide⟩

/-! ## After a strategy change -/

/-- The answer of a strategy, on every open-road map and pair of towns. -/
def strategyAnswer (strategy : Strategy) : (Road → Bool) → Town → Town → Bool :=
  fun isOpen source target => (strategy.run isOpen source target).1

/-- The cost of a strategy, on every instance, ordered pointwise. -/
def strategyCost (strategy : Strategy) : (Road → Bool) → Town → Town → ℕ :=
  fun isOpen source target => (strategy.run isOpen source target).2

/-- **Strategy change**: always stop early. -/
def adoptEarlyExit (_ : Strategy) : Strategy :=
  .earlyExit

/-- **The early-exit search improves every strategy here**: the same answers
with no more rounds. -/
theorem earlyExit_improves : Improves strategyAnswer strategyCost adoptEarlyExit := by
  intro strategy
  have sameAnswer : strategyAnswer .earlyExit = strategyAnswer .exhaustive := by
    funext isOpen source target
    exact searchFrom_answer isOpen source target 0 budget
  refine ⟨?_, fun isOpen source target => ?_⟩
  · cases strategy
    · exact sameAnswer
    · rfl
  · cases strategy
    · exact (searchFrom_cost_le isOpen source target 0 budget).trans (by rfl)
    · exact le_rfl

/-- **The cost is not preserved**: from `a` to `b` in the open map, early exit
uses one round and the exhaustive search three. -/
theorem earlyExit_not_preserves_cost : ¬ PreservesExactly strategyCost adoptEarlyExit := by
  intro preserved
  have atAB := congrFun (congrFun (congrFun (preserved .exhaustive) (isOpen allOpen)) .a) .b
  revert atAB
  decide

/-! ## After an implementation refinement -/

/-- A report: a road and whether it was seen open. -/
abbrev Report : Type :=
  Road × Bool

/-- **The log implementation**: the world as the list of reports received. -/
abbrev Log : Type :=
  List Report

/-- The number of reports about `r` with verdict `seenOpen`. -/
def countReports (log : Log) (r : Road) (seenOpen : Bool) : ℕ :=
  (log.filter fun report => decide (report = (r, seenOpen))).length

/-- **The refinement map**: the tally of a log is its evidence. -/
def tally (log : Log) : World :=
  fun r => (countReports log r true, countReports log r false)

/-- Closing a road in the log: append a closed report. -/
def closeLog (r : Road) (log : Log) : Log :=
  log ++ [(r, false)]

theorem countReports_append_closed (log : Log) (r r' : Road) (seenOpen : Bool) :
    countReports (closeLog r log) r' seenOpen =
      countReports log r' seenOpen + if (r, false) = (r', seenOpen) then 1 else 0 := by
  unfold countReports closeLog
  rw [List.filter_append, List.length_append]
  by_cases hit : (r, false) = (r', seenOpen)
  · have single : ([(r, false)] : Log).filter (fun report => decide (report = (r', seenOpen))) =
        [(r, false)] := by
      simp [hit]
    rw [if_pos hit, single]
    rfl
  · have single : ([(r, false)] : Log).filter (fun report => decide (report = (r', seenOpen))) =
        [] := by
      simp [hit]
    rw [if_neg hit, single]
    rfl

/-- **The refinement square**: appending a closed report and then tallying is
tallying and then closing the road. -/
theorem tally_close (r : Road) (log : Log) : tally (closeLog r log) = close r (tally log) := by
  funext r'
  unfold tally close closedReport
  change (countReports (closeLog r log) r' true, countReports (closeLog r log) r' false) =
    (countReports log r' true, countReports log r' false) + if r' = r then (0, 1) else (0, 0)
  rw [countReports_append_closed, countReports_append_closed]
  by_cases same : r' = r
  · subst same
    simp
  · have differ : ¬ (r, false) = (r', false) := fun h => same (Prod.mk.inj h).1.symm
    have differ' : ¬ (r, false) = (r', true) := fun h => same (Prod.mk.inj h).1.symm
    rw [if_neg differ, if_neg differ', if_neg same]
    rfl

/-- **Every consumer of the evidence reads the same value in both
implementations**, before and after closing a road. -/
theorem consumer_tally_close {Z : Sort*} (consumer : World → Z) (r : Road) (log : Log) :
    consumer (tally (closeLog r log)) = consumer (close r (tally log)) :=
  congrArg consumer (tally_close r log)

/-- An implementation that keeps only the latest report about the closed
road. -/
def closeLatest (r : Road) (log : Log) : Log :=
  log.filter (fun report => decide (report.1 ≠ r)) ++ [(r, false)]

/-- **Control: replacing a road's reports by the latest one is not a
refinement** of closing it. -/
theorem closeLatest_not_refines :
    ¬ ∀ log, tally (closeLatest .bd log) = close .bd (tally log) := by
  intro refines
  have atBD := congrFun (refines [(.bd, true), (.bd, true)]) .bd
  revert atBD
  decide

/-- The first report in a log. -/
def firstReport (log : Log) : Option Report :=
  log.head?

/-- **Control: the first report does not descend to the tally**: two orders of
the same reports. -/
theorem firstReport_not_descends : ¬ Factors tally firstReport := by
  apply NonTrivialFiber.not_factors
  refine ⟨[(.ab, true), (.bd, true)], [(.bd, true), (.ab, true)], ?_, by decide⟩
  funext r
  cases r <;> rfl

/-! ### The refinement square in the operational equipment -/

section Equipment

open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.LanguageDef.GSLTIL.OperationalEquipment

/-- The log implementation as a transition system: append a closed report. -/
abbrev logSystem : GSLT :=
  transitionSystem fun (log log' : Log) => ∃ r, log' = closeLog r log

/-- The evidence implementation as a transition system: close a road. -/
abbrev worldSystem : GSLT :=
  transitionSystem fun (w w' : World) => ∃ r, w' = close r w

/-- **The tally is a tight arrow** of the operational equipment: it preserves
every step. -/
def tallyTight : Tight logSystem worldSystem :=
  operationalOfPreserves (view := tally) fun log _ ⟨r, appended⟩ =>
    ⟨r, by rw [appended, tally_close]⟩

/-- Closing a road in the log, with the road retained as the witness. -/
def closeLogRoute : LooseRoute logSystem logSystem :=
  fun log log' => ULift.{0} {r : Road // log' = closeLog r log}

/-- Closing a road in the evidence, with the road retained as the witness. -/
def closeRoute : LooseRoute worldSystem worldSystem :=
  fun w w' => ULift.{0} {r : Road // w' = close r w}

/-- **The refinement square**: every log closing maps to the evidence closing
of the same road. -/
def closeRefinementSquare : RefinementSquare tallyTight tallyTight closeLogRoute closeRoute where
  map := fun {log _} witness =>
    match witness with
    | ⟨⟨r, appended⟩⟩ => ⟨⟨r, by subst appended; exact tally_close r log⟩⟩

/-- Replacing the reports about a road by the latest one, as a loose route on
logs. -/
def closeLatestRoute : LooseRoute logSystem logSystem :=
  fun log log' => ULift.{0} {r : Road // log' = closeLatest r log}

/-- **Control: compaction admits no refinement square** onto closing roads. -/
theorem closeLatest_no_refinementSquare :
    ¬ Nonempty (RefinementSquare tallyTight tallyTight closeLatestRoute closeRoute) := by
  rintro ⟨square⟩
  have image := square.map (source := [(.bd, true), (.bd, true)])
    (target := closeLatest .bd [(.bd, true), (.bd, true)]) ⟨⟨.bd, rfl⟩⟩
  obtain ⟨⟨r, closed⟩⟩ := image
  have atBD := congrFun closed .bd
  revert atBD
  cases r <;> decide

end Equipment

/-! ## Pairs of changes -/

/-- **Revision and abstraction commute**: the major view supports closing any
road. -/
theorem majorView_supports_close (r : Road) : Supports majorView (close r) :=
  ⟨fun v r' => v r' + closedReport r r'.1, fun _ => rfl⟩

/-- **Revision and strategy**: on every revised world, the early-exit answer
is the exhaustive answer. -/
theorem earlyExit_answer_after_close (r : Road) (w : World) (source target : Town) :
    strategyAnswer .earlyExit (isOpen (close r w)) source target =
      strategyAnswer .exhaustive (isOpen (close r w)) source target :=
  congrFun (congrFun (congrFun (earlyExit_improves .exhaustive).1 _) _) _

/-- **Abstraction and strategy**: over the major map, early exit answers as
the exhaustive search does. -/
theorem earlyExit_improves_major (w : World) :
    strategyAnswer .earlyExit (fun r => r.major && isOpen w r) .a .d = majorAnswer w :=
  congrFun (congrFun (congrFun (earlyExit_improves .exhaustive).1 _) _) _

/-- **The major answer is not the full answer**: after `b–d` closes in the open
map, the minor roads still lead to `d`. -/
theorem majorAnswer_ne_answer : majorAnswer detour ≠ answer detour := by
  decide

/-- The tally of the major reports of a log. -/
def majorTally (log : Log) (r : {r : Road // r.major = true}) : Evidence :=
  tally (log.filter fun report => report.1.major) r.1

/-- **Abstraction and implementation commute**: hiding minor roads after
tallying is tallying the major reports. -/
theorem majorView_tally (log : Log) : majorView (tally log) = majorTally log := by
  funext r
  obtain ⟨r, major⟩ := r
  have keep : ∀ seenOpen : Bool,
      (log.filter fun report => report.1.major).filter
          (fun report => decide (report = (r, seenOpen))) =
        log.filter fun report => decide (report = (r, seenOpen)) := by
    intro seenOpen
    rw [List.filter_filter]
    congr 1
    funext report
    by_cases hit : report = (r, seenOpen)
    · subst hit
      simp [major]
    · simp [hit]
  unfold majorView majorTally tally countReports
  rw [keep true, keep false]

end Mettapedia.GSLT.Scope.RoadMap
