import Mettapedia.GSLT.Compilation.OSLFReferenceOnTheStep
import Mettapedia.OSLF.NativeTypes.Decision.Reference.Core

/-!
# Hosting complete OSLF frontiers modulo equations

A decision backend supplies a finite list of receipts and covers the
authored moves up to the source equations. A run starting from an
admitted representative keeps later representatives in that profile.
Finite may-reachability of equation-invariant observations transfers
in both directions.

The source need not have finitely many literal successors: an equation
class can have more representatives than the backend returns. The
reference rule publishes one returned representative per match.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Compilation.OSLFBackendOnTheStep

open Mettapedia.GSLT.IndexedOperational
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis (equalityGSLT EquationPredicate)
open Mettapedia.OSLF.NativeTypes.Decision.Reference.Core (Backend)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open RuleSyntax.Machines (ReadsBag rowState)
open OSLFReferenceOnTheStep (Encoding)

universe u

variable {source : GSLT.{u}} {admitted : source.Term → Prop}

/-- Targets of the completed frontier; repeated receipts remain separate
entries of the list. -/
def frontier (B : Backend source admitted) (term : source.Term) : List source.Term :=
  (B.frontier (B.completionBudget term) term).map (B.target term)

private abbrev representativeTheory (B : Backend source admitted) : GSLT.{u} :=
  equalityGSLT source.Term (fun s t => ∃ receipt ∈ B.frontier (B.completionBudget s) s, B.target s receipt = t)

private theorem frontier_exact (B : Backend source admitted) (s t : source.Term) :
    t ∈ frontier B s ↔ (representativeTheory B).Step s t :=
  List.mem_map

/-- Use the original equations and both backend laws to relate the authored
theory to the returned representatives. -/
private def represented (B : Backend source admitted) :
    OperationalCorrespondence source (representativeTheory B) where
  related origin current := admitted current ∧ source.Equiv origin current
  readStep := by
    intro origin current next ⟨typed, equal⟩ step
    obtain ⟨receipt, found, rfl⟩ := step
    have available := B.sound (B.completionBudget current) current receipt found
    obtain ⟨after, moved, same⟩ :=
      source.rewrites_resp_left (source.equations.iseqv.symm equal) available
    exact Or.inr ⟨after, moved, B.target_admitted _ _ typed _ found, source.equations.iseqv.symm same⟩
  forward := by
    intro origin after current ⟨typed, equal⟩ step
    obtain ⟨actual, moved, same⟩ := source.rewrites_resp_left equal step
    obtain ⟨receipt, found, equivalent⟩ :=
      B.coverage (B.completionBudget current) current (B.complete_at current typed) actual moved
    refine ⟨B.target current receipt, (executionPath_nonempty_iff_multiStep _ _ _).mpr
      (.step ⟨receipt, found, rfl⟩ (.refl _)), ?_⟩
    exact ⟨B.target_admitted _ _ typed _ found, source.equations.iseqv.trans same equivalent⟩

def compiled (B : Backend source admitted) (encoding : Encoding source.Term) : GSLT :=
  OSLFReferenceOnTheStep.compiledStep encoding (frontier B)

def correspondence (B : Backend source admitted) (encoding : Encoding source.Term) :
    OperationalCorrespondence source (compiled B encoding) :=
  (represented B).comp
    (OSLFReferenceOnTheStep.correspondence (representativeTheory B) encoding
      (frontier (source := source) B) (frontier_exact B))

/-- Complete frontiers over representatives suffice for exactly the source
observations invariant under change of representative. The zero-step
case allows the initial input to be supplied in an admitted form. -/
theorem reachable_observation_iff (B : Backend source admitted) (encoding : Encoding source.Term)
    (predicate : EquationPredicate source) {origin representative : source.Term}
    (typed : admitted representative) (equal : source.Equiv origin representative) :
    (∃ after, source.MultiStep origin after ∧ predicate.1 after) ↔
      ∃ final, (compiled B encoding).MultiStep (rowState (encoding.store representative)) final ∧
        ∃ read, ReadsBag final {encoding.store read} ∧ predicate.1 read := by
  let R := represented B
  have starts : R.related origin representative := ⟨typed, equal⟩
  have observed {s r : source.Term} (related : R.related s r) :
      predicate.1 s ↔ predicate.1 r :=
    predicate.2 related.2
  have realizes (endPoint : source.Term) :=
    OSLFReferenceOnTheStep.reaches_iff (representativeTheory B) encoding (frontier (source := source) B)
      (frontier_exact B) representative endPoint
  constructor
  · rintro ⟨after, path, holds⟩
    obtain ⟨next, run, related⟩ := R.liftMultiStep starts path
    obtain ⟨final, firings, read⟩ := (realizes next).mp run
    exact ⟨final, firings, next, read, (observed related).mp holds⟩
  · rintro ⟨final, firings, read, shown, holds⟩
    have run := (realizes read).mpr ⟨final, firings, shown⟩
    obtain ⟨after, path, related⟩ := R.toOperationalReadback.reflectMultiStep starts run
    exact ⟨after, path, (observed related).mpr holds⟩

namespace Controls

open NamesOnTheStep (Expr)

/-- The first bit is observable and can change once. The second bit is an
equational choice of representative. -/
abbrev system : GSLT where
  Term := Bool × Bool
  equations :=
    { r := fun x y => x.1 = y.1
      iseqv := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩ }
  rewrites x y := x.1 = false ∧ y.1 = true
  rewrites_resp_left equal step := ⟨_, ⟨equal.symm.trans step.1, step.2⟩, rfl⟩
  rewrites_resp_right step equal := ⟨step.1, equal.symm.trans step.2⟩

abbrev canonical (term : system.Term) : Prop := term.2 = false

def backend : Backend system canonical where
  Receipt _ := Unit
  target _ _ := (true, false)
  frontier _ state := if state.1 then [] else [()]
  closed _ _ := true
  sound _ state _ found := by
    cases first : state.1
    · exact ⟨first, rfl⟩
    · simp [first] at found
  coverage _ state _ _ step := ⟨(), by simp [step.1], step.2⟩
  target_admitted _ _ _ _ _ := rfl
  completionBudget _ := 0
  complete_at _ _ := rfl
  frontier_stable _ _ _ := rfl
  closed_stable _ _ _ := rfl

def encoding : Encoding system.Term where
  store term := .app (.sym term.1.toNat) (.sym term.2.toNat)
  read
    | .app (.sym n) (.sym m) => some (n != 0, m != 0)
    | _ => none
  read_store := by rintro ⟨(_ | _), (_ | _)⟩ <;> rfl

def finished : EquationPredicate system :=
  ⟨fun s => s.1 = true, fun {s t} equal => by
    change s.1 = true ↔ t.1 = true
    rw [show s.1 = t.1 from equal]⟩

/-- A change is observed from an input whose literal representation is
outside the backend's admitted profile. The recorded output is canonical. -/
theorem observes_progress :
    ∃ final, (compiled backend encoding).MultiStep (rowState (encoding.store (false, false))) final ∧
      ∃ read, ReadsBag final {encoding.store read} ∧ finished.1 read := by
  apply (reachable_observation_iff backend encoding finished (origin := (false, true))
    (representative := (false, false)) rfl rfl).mp
  exact ⟨(true, true), .step ⟨rfl, rfl⟩ (.refl _), rfl⟩

/-- Literal completeness is false. The second representative is allowed
by the source semantics and omitted by the executable frontier. -/
theorem frontier_is_complete_only_up_to_equations :
    system.Step (false, false) (true, true) ∧ (true, true) ∉ frontier backend (false, false) := by
  refine ⟨⟨rfl, rfl⟩, ?_⟩
  change (true, true) ∉ ([(true, false)] : List (Bool × Bool))
  decide +kernel

end Controls

#print axioms reachable_observation_iff
#print axioms Controls.observes_progress
#print axioms Controls.frontier_is_complete_only_up_to_equations

end Mettapedia.GSLT.Compilation.OSLFBackendOnTheStep
