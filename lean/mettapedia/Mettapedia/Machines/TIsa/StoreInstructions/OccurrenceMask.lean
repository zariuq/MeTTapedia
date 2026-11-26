import Mettapedia.Machines.TIsa.StoreInstructions.SolverGuardTrichotomy
import Mettapedia.Machines.TIsa.StoreInstructions.SymbolicExecution

/-!
# Collecting the identities of selected occurrences

The working representation is a mask over a held enumeration,
not a set of normalized terms. A merely possible match prevents
the mask from representing an all-solutions answer. On success,
decoding the mask recovers exactly the original occurrence identities.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.OccurrenceMask

open Mettapedia.Logic.LP
open SolverGuardTrichotomy (Observation specification)

def settled (o : Observation) : Bool := decide (o ≠ .possible)

def mask : List Observation → Option (List Bool)
  | [] => some []
  | .impossible :: rest => (mask rest).map (false :: ·)
  | .assured :: rest => (mask rest).map (true :: ·)
  | .possible :: _ => none

theorem mask_eq (tags : List Observation) :
    mask tags = if tags.all settled then some (tags.map Observation.must) else none := by
  induction tags with
  | nil => rfl
  | cons observed rest ih =>
    cases observed <;> cases closed : rest.all settled <;>
      simp [mask, ih, settled, closed, Observation.must]

theorem length_eq (tags : List Observation) (bits : List Bool) (collected : mask tags = some bits) :
    bits.length = tags.length := by
  rw [mask_eq] at collected
  split at collected
  · obtain rfl := Option.some.inj collected
    simp
  · cases collected

def identities {I : Type*} (ids : List I) (bits : List Bool) : List I :=
  (ids.zip bits).filterMap (fun (id, selected) => if selected then some id else none)

theorem identities_filter {I O : Type*} (id : O → I) (yes : O → Bool) (items : List O) :
    identities (items.map id) (items.map yes) = (items.filter yes).map id := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
    change ((rest.map id).zip (rest.map yes)).filterMap _ = _ at ih
    cases checked : yes item <;> simp [identities, checked, ih]

universe u p
variable {σ : LPSignature.{u,u,p,u}} [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]

def tag (answer : Subst σ) (pattern : Term σ) (o : SymbolicExecution.Atom σ) : Observation :=
  specification (answer.applyTerm pattern) (answer.applyTerm o.2)

theorem must_eq (answer : Subst σ) (pattern : Term σ) (o : SymbolicExecution.Atom σ) :
    (tag answer pattern o).must = SymbolicExecution.assured answer pattern o :=
  SolverGuardTrichotomy.must_exact _ _

theorem may_eq (answer : Subst σ) (pattern : Term σ) (o : SymbolicExecution.Atom σ) :
    (tag answer pattern o).may = SymbolicExecution.possible answer pattern o := by
  simp only [tag, SolverGuardTrichotomy.may_exact, SymbolicExecution.possible, unifyTotalStructural_eq_unifyTotal]

theorem settled_eq (o : Observation) : settled o = (o.must || !o.may) := by cases o <;> rfl

theorem collect_exact (answer : Subst σ) (atoms : List (SymbolicExecution.Atom σ)) (pattern : Term σ) :
    (mask (atoms.map (tag answer pattern))).map (fun bits => (identities (atoms.map Prod.fst) bits).toFinset) =
      SymbolicExecution.collect answer atoms pattern := by
  rw [mask_eq, List.all_map]
  have policy : settled ∘ tag answer pattern =
      fun o => SymbolicExecution.assured answer pattern o || !SymbolicExecution.possible answer pattern o := by
    funext o
    rw [Function.comp_apply, settled_eq, must_eq, may_eq]
  rw [policy]
  unfold SymbolicExecution.collect
  split
  · simp only [Option.map_some, List.map_map, Function.comp_def, must_eq, identities_filter]
  · rfl

namespace Examples

theorem different_identities_can_share_one_match_value :
    (mask [.assured, .impossible, .assured]).map (identities [5, 7, 9]) = some [5, 9] := by decide +kernel

theorem a_possible_match_is_not_an_empty_or_partial_collection :
    (mask [.assured, .possible, .assured]).map (identities [5, 7, 9]) = none := by decide +kernel

end Examples

end Mettapedia.Machines.TIsa.StoreInstructions.OccurrenceMask
