import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Semantics

/-!
# Charging a chosen schedule of the source calculus

The shared-world source move determines the replacement bag and the
space request. A strategy chooses which live alternative may move.
Its meters account for solving, selecting a frontier item, and serving
a space request. Structural costs are counted by the labelled source
step. In particular a query returning an empty bag still makes a read.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Preparation

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.ContextualFamily

inductive SpaceRequest (Datum : Type) where
  | query (space pattern : Datum)
  | insert (space atom : Datum)
  | erase (space atom : Datum)
  deriving DecidableEq

structure Charge (Datum : Type) where
  solver : Nat
  frontier : Nat
  alternatives : Nat
  choicePoints : Nat
  request : Option (SpaceRequest Datum)
  space : Nat

/-- One source reduction, its solver work, scheduling and alternatives,
and any work charged by the space service. -/
def Charge.units {Datum : Type} (entry : Charge Datum) : Nat :=
  1 + entry.solver + entry.frontier + entry.alternatives + entry.choicePoints + entry.space

variable {S : Signature} {κ : Keys S} {Γ : Ctx S} {star : S.Srt} {Ty : Type}

def spaceRequest (branch : Branch κ Γ star Ty) : Option (SpaceRequest (Data κ Γ star)) :=
  match branch.focus with
  | .eval (.query space pattern _) => some (.query space pattern)
  | .eval (.add space atom _) => some (.insert space atom)
  | .eval (.remove space atom _) => some (.erase space atom)
  | _ => none

structure Strategy (κ : Keys S) (Γ : Ctx S) (star : S.Srt) (Ty : Type) where
  chooses : Config κ Γ star Ty → Branch κ Γ star Ty → Prop
  solverSteps : World κ Γ star → Branch κ Γ star Ty → Nat
  selectionVisits : Config κ Γ star Ty → Branch κ Γ star Ty → Nat
  spaceSteps : World κ Γ star → SpaceRequest (Data κ Γ star) → Nat

def charge (strategy : Strategy κ Γ star Ty) (config : Config κ Γ star Ty)
    (branch : Branch κ Γ star Ty) (produced : Multiset (Branch κ Γ star Ty)) : Charge (Data κ Γ star) :=
  let request := spaceRequest branch
  { solver := strategy.solverSteps config.world branch
    frontier := 1 + strategy.selectionVisits config branch
    alternatives := produced.card
    choicePoints := if 1 < produced.card then 1 else 0
    request
    space := (request.map (strategy.spaceSteps config.world)).getD 0 }

variable {D : Discipline S Γ star} {P : Program κ Γ star D.Ty} {supply : Nat → Term S Γ star}

inductive ChargedStep (D : Discipline S Γ star) (P : Program κ Γ star D.Ty) (supply : Nat → Term S Γ star)
    (strategy : Strategy κ Γ star D.Ty) :
    Config κ Γ star D.Ty → Charge (Data κ Γ star) → Config κ Γ star D.Ty → Prop where
  | move (world next : World κ Γ star) (branch : Branch κ Γ star D.Ty)
      (rest produced : Multiset (Branch κ Γ star D.Ty))
      (chosen : strategy.chooses ⟨world, branch ::ₘ rest⟩ branch)
      (live : Solvable branch.store) (moved : Move D P supply world branch next produced) :
    ChargedStep D P supply strategy ⟨world, branch ::ₘ rest⟩
      (charge strategy ⟨world, branch ::ₘ rest⟩ branch produced) ⟨next, produced + rest⟩

variable {strategy : Strategy κ Γ star D.Ty}

theorem ChargedStep.source {start finish : Config κ Γ star D.Ty} {entry : Charge (Data κ Γ star)}
    (step : ChargedStep D P supply strategy start entry finish) : Step D P supply start finish := by
  cases step with
  | move world next branch rest produced _ live moved => exact .move world next branch rest produced live moved

inductive ChargedRun (D : Discipline S Γ star) (P : Program κ Γ star D.Ty) (supply : Nat → Term S Γ star)
    (strategy : Strategy κ Γ star D.Ty) :
    Config κ Γ star D.Ty → List (Charge (Data κ Γ star)) → Config κ Γ star D.Ty → Prop where
  | stop (state : Config κ Γ star D.Ty) : ChargedRun D P supply strategy state [] state
  | advance {before next finish : Config κ Γ star D.Ty} {entry : Charge (Data κ Γ star)}
      {rest : List (Charge (Data κ Γ star))}
      (moved : ChargedStep D P supply strategy before entry next)
      (tail : ChargedRun D P supply strategy next rest finish) :
    ChargedRun D P supply strategy before (entry :: rest) finish

theorem ChargedRun.source {start finish : Config κ Γ star D.Ty} {work : List (Charge (Data κ Γ star))}
    (run : ChargedRun D P supply strategy start work finish) : Runs D P supply start finish := by
  induction run with
  | stop => exact .refl
  | advance moved _ later => exact (Relation.ReflTransGen.single moved.source).trans later

theorem ChargedRun.append {start middle finish : Config κ Γ star D.Ty}
    {first later : List (Charge (Data κ Γ star))}
    (before : ChargedRun D P supply strategy start first middle)
    (after : ChargedRun D P supply strategy middle later finish) :
    ChargedRun D P supply strategy start (first ++ later) finish := by
  induction before with
  | stop => exact after
  | advance moved _ ih => exact .advance moved (ih after)

def units {Datum : Type} (entries : List (Charge Datum)) : Nat :=
  (entries.map Charge.units).sum

theorem units_append {Datum : Type} (first later : List (Charge Datum)) :
    units (first ++ later) = units first + units later := by simp [units]

theorem reductions_bounded_by_work {Datum : Type} (entries : List (Charge Datum)) :
    entries.length ≤ units entries := by
  induction entries with
  | nil => exact Nat.zero_le _
  | cons one rest ih =>
    simp only [units, List.map_cons, List.sum_cons, List.length_cons] at *
    have atLeast : 1 ≤ one.units := by unfold Charge.units; omega
    omega

/-- A bound on implementing one charged action lifts to the entire
schedule. The same multiplier works for any selected schedule and
space tariff that meet that local bound. -/
theorem uniform_bound_of_local {Datum : Type} (multiplier : Nat)
    (entries : List (Charge Datum)) (implementation : Charge Datum → Nat)
    (localBound : ∀ entry ∈ entries, implementation entry ≤ multiplier * entry.units) :
    (entries.map implementation).sum ≤ multiplier * units entries := by
  induction entries with
  | nil => simp [units]
  | cons one rest ih =>
    have lead := localBound one (by simp)
    have tail := ih (fun entry member => localBound entry (by simp [member]))
    simpa only [List.map_cons, List.sum_cons, units, Nat.mul_add] using Nat.add_le_add lead tail

/-- A fixed program with an uncharged operation that can emit arbitrarily
many cells cannot have a uniform time bound. The target is charged for
each cell it writes, even when the source has assigned constant charge. -/
theorem bounded_cost_requires_bounded_output {Input : Type}
    (price output time : Input → Nat) (multiplier setup bound : Nat)
    (writes : ∀ input, output input ≤ time input)
    (implements : ∀ input, time input ≤ multiplier * price input + setup)
    (inputs : ∀ input, price input ≤ bound) :
    ∀ input, output input ≤ multiplier * bound + setup := by
  intro input
  exact (writes input).trans ((implements input).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_left multiplier (inputs input)) setup))

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Preparation
