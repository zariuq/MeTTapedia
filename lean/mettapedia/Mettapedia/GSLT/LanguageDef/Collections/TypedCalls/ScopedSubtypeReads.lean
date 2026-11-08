import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeReadSupply
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.SubtypeClosureRounds

/-!
# Per-query subtype-row instantiation

Every direct subtype inquiry owns its result variable and fresh copies of
the candidate rows. The supply is threaded across frontier occurrences and
rounds. Matching, result extraction, pre-round duplicate policy and ancestry
filtering reuse their existing owners. Exhaustion returns no completed list,
while retaining the actual advanced supply.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.ScopedSubtypeReads

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE
open TypeReadSupply (Supply remember fresh)
open RetainedTypePayloads (ExternalView)

def possibleRow : Atom → Bool
  | .var _ => true
  | .expression [.var _, _, _] => true
  | .expression [.symbol ":<", _, _] => true
  | _ => false

def rows (world : ExternalView) (input : Atom) (resultName : String) :
    List Atom → Supply → List Atom × Supply
  | [], supply => ([], supply)
  | row :: rest, supply =>
      if possibleRow row then
        let instantiated := fresh supply row
        let reply := TypeScopeClosure.subtypeRow world input resultName instantiated.1
        let retained := match reply with
          | none => instantiated.2
          | some type_ => remember instantiated.2 [type_]
        let later := rows world input resultName rest retained
        (reply.toList ++ later.1, later.2)
      else rows world input resultName rest supply

def query (world : ExternalView) (sourceRows : List Atom) (base : String)
    (input : Atom) (supply : Supply) : List Atom × Supply :=
  let captured := remember supply [input]
  let chosen := chooseFreshName base captured.used captured.next
  rows world input chosen.1 sourceRows ⟨chosen.1 :: captured.used, chosen.2⟩

def discoveries (world : ExternalView) (sourceRows : List Atom) (base : String)
    (alpha : Atom → Atom → Bool) (before : SubtypeClosureRounds.State) :
    List (SubtypeClosureRounds.Entry × Nat) → Supply → List SubtypeClosureRounds.Entry × Supply
  | [], supply => ([], supply)
  | (entry, index) :: rest, supply =>
      if entry.error then discoveries world sourceRows base alpha before rest supply else
        let response := query world sourceRows base entry.type_ supply
        let accepted := (response.1.filter (SubtypeClosureRounds.accept alpha before index)).map
          (fun type_ => (⟨type_, some index, false⟩ : SubtypeClosureRounds.Entry))
        let later := discoveries world sourceRows base alpha before rest response.2
        (accepted ++ later.1, later.2)

def round (world : ExternalView) (sourceRows : List Atom) (base : String)
    (alpha : Atom → Atom → Bool) (before : SubtypeClosureRounds.State) (supply : Supply) :
    Option SubtypeClosureRounds.State × Supply :=
  let result := discoveries world sourceRows base alpha before
    (before.known.zipIdx.drop before.frontier) supply
  (if result.1.isEmpty then none
    else some ⟨before.known ++ result.1, before.known.length⟩, result.2)

def run (world : ExternalView) (sourceRows : List Atom) (base : String)
    (alpha : Atom → Atom → Bool) :
    Nat → SubtypeClosureRounds.State → Supply → SubtypeClosureRounds.Outcome × Supply
  | 0, state, supply => (.unfinished state, supply)
  | budget + 1, state, supply =>
      let advanced := round world sourceRows base alpha state supply
      match advanced.1 with
      | none => (.complete state, advanced.2)
      | some next => run world sourceRows base alpha budget next advanced.2

def completeTypes (world : ExternalView) (sourceRows : List Atom) (base : String)
    (alpha : Atom → Atom → Bool) (budget : Nat) (seeds : List Atom) (supply : Supply) :
    Option (List Atom) × Supply :=
  let result := run world sourceRows base alpha budget (SubtypeClosureRounds.start seeds)
    (remember supply seeds)
  (match result.1 with
    | .complete final => some (final.known.map SubtypeClosureRounds.Entry.type_)
    | .unfinished _ => none, result.2)

theorem rows_remember (world : ExternalView) (input : Atom) (resultName : String)
    (sourceRows : List Atom) (supply : Supply) :
    supply.used ⊆ (rows world input resultName sourceRows supply).2.used := by
  induction sourceRows generalizing supply with
  | nil => exact fun _ member => member
  | cons row rest ih =>
      dsimp only [rows]
      split
      · intro name member
        have kept := (TypeReadSupply.fresh_remembers supply row).1 member
        apply ih
        cases TypeScopeClosure.subtypeRow world input resultName (fresh supply row).1 with
        | none => exact kept
        | some type_ => exact TypeReadSupply.remember_old _ _ kept
      · exact ih supply

theorem query_remembers (world : ExternalView) (sourceRows : List Atom) (base : String)
    (input : Atom) (supply : Supply) : supply.used ⊆ (query world sourceRows base input supply).2.used := by
  intro name member
  apply rows_remember
  exact List.mem_cons_of_mem _ (TypeReadSupply.remember_old supply [input] member)

theorem discoveries_remember (world : ExternalView) (sourceRows : List Atom) (base : String)
    (alpha : Atom → Atom → Bool) (before : SubtypeClosureRounds.State)
    (frontier : List (SubtypeClosureRounds.Entry × Nat)) (supply : Supply) :
    supply.used ⊆ (discoveries world sourceRows base alpha before frontier supply).2.used := by
  induction frontier generalizing supply with
  | nil => exact fun _ member => member
  | cons pair rest ih =>
      rcases pair with ⟨entry, index⟩
      dsimp only [discoveries]
      split
      · exact ih supply
      · exact fun _ member => ih _ (query_remembers world sourceRows base entry.type_ supply member)

theorem round_remembers (world : ExternalView) (sourceRows : List Atom) (base : String)
    (alpha : Atom → Atom → Bool) (before : SubtypeClosureRounds.State) (supply : Supply) :
    supply.used ⊆ (round world sourceRows base alpha before supply).2.used :=
  discoveries_remember world sourceRows base alpha before _ supply

theorem run_remembers (world : ExternalView) (sourceRows : List Atom) (base : String)
    (alpha : Atom → Atom → Bool) (budget : Nat) (before : SubtypeClosureRounds.State) (supply : Supply) :
    supply.used ⊆ (run world sourceRows base alpha budget before supply).2.used := by
  induction budget generalizing before supply with
  | zero => exact fun _ member => member
  | succ budget ih =>
      dsimp only [run]
      split
      · exact round_remembers world sourceRows base alpha before supply
      · exact fun _ member => ih _ _ (round_remembers world sourceRows base alpha before supply member)

theorem completeTypes_remembers (world : ExternalView) (sourceRows : List Atom) (base : String)
    (alpha : Atom → Atom → Bool) (budget : Nat) (seeds : List Atom) (supply : Supply) :
    supply.used ⊆ (completeTypes world sourceRows base alpha budget seeds supply).2.used :=
  fun _ member => run_remembers world sourceRows base alpha budget _ _
    (TypeReadSupply.remember_old supply seeds member)

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.ScopedSubtypeReads
