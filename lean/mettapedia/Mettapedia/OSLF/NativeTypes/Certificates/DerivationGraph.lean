import Mettapedia.OSLF.NativeTypes.Certificates.Shared.Emission
import Mettapedia.Logic.DerivationGraph

/-!
# Finite rule presentations on the shared derivation-graph machine

This adapter retains the existing rule inventory and every ordered premise
occurrence. It connects the generated indexed derivations and the existing
judgment-table checker to the generic chronological graph replay. It does not
identify different source calculi or confer native authority on ordinary data.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Certificates

open Mettapedia.TypeTheory

universe u v

namespace Presentation

private theorem finite_nonempty {n : Nat} (F : Fin n → Type u)
    (present : ∀ position, Nonempty (F position)) : Nonempty ((position : Fin n) → F position) := by
  induction n with
  | zero => exact ⟨fun position => Fin.elim0 position⟩
  | succ n ih =>
      obtain ⟨first⟩ := present 0
      obtain ⟨later⟩ := ih (fun position => F position.succ) (fun position => present position.succ)
      exact ⟨Fin.cases first later⟩

/-- A local instance of an original rule, with its complete premise vector. -/
def rules (P : Presentation.{u}) (premises : List P.Judgment)
    (conclusion : P.Judgment) : Prop :=
  ∃ rule : P.Rule, premises = P.premises rule ∧ conclusion = P.conclusion rule

/-- The original rule code is the witness; no derivability oracle is called. -/
abbrev ruleWitness (P : Presentation.{u}) [DecidableEq P.Judgment] :
    Mettapedia.Logic.RuleWitness P.rules where
  W := P.Rule
  isInstance rule premises conclusion :=
    decide (premises = P.premises rule ∧ conclusion = P.conclusion rule)
  sound rule _ _ accepted := ⟨rule, of_decide_eq_true accepted⟩
  complete _ _ instance_ := by
    obtain ⟨rule, premises, conclusion⟩ := instance_
    exact ⟨rule, by simp [premises, conclusion]⟩

/-- Indexed source derivations give exactly the generic rule closure. The
generic closure forgets proof identity; the graph adapter below retains its
submitted rule codes and physical premise occurrences separately. -/
theorem nonempty_derivation_iff_derives (P : Presentation.{u}) (judgment : P.Judgment) :
    Nonempty (P.Derivation judgment) ↔ Mettapedia.Logic.Derives P.rules judgment := by
  constructor
  · rintro ⟨tree⟩
    apply JudgmentDerivation.Derivation.rec
      (motive := fun judgment _ => Mettapedia.Logic.Derives P.rules judgment)
      (t := tree)
    intro judgment rule children ih
    obtain ⟨rule, conclusion⟩ := rule
    cases conclusion
    refine Mettapedia.Logic.Derives.node (P.premises rule) (P.conclusion rule)
      ⟨rule, rfl, rfl⟩ ?_
    intro premise member
    obtain ⟨position, equal⟩ := List.mem_iff_get.mp member
    exact equal ▸ ih ⟨position⟩
  · intro derivation
    apply Mettapedia.Logic.Derives.least
      (fun judgment => Nonempty (P.Derivation judgment)) ?_ derivation
    intro premises conclusion instance_ children
    obtain ⟨rule, rfl, rfl⟩ := instance_
    obtain ⟨premiseTrees⟩ := finite_nonempty
      (fun position => P.Derivation ((P.premises rule).get position))
      (fun position => children ((P.premises rule).get position) (List.get_mem _ position))
    exact ⟨.node ⟨rule, rfl⟩ (fun position => premiseTrees position.down)⟩

end Presentation

namespace PresentationGraph

open Mettapedia.Logic

variable {P : Presentation.{u}} [DecidableEq P.Judgment]
variable {Origin : Type v}

/-- A shared row keeps its literal rule and all reference positions. -/
def ofRow (origin : Origin) (row : Shared.Row P) :
    DerivationGraph.Node P.Judgment P.Rule Origin :=
  ⟨P.conclusion row.rule, row.rule, List.ofFn row.references, origin⟩

omit [DecidableEq P.Judgment] in
@[simp] theorem ofRow_parents (origin : Origin) (row : Shared.Row P) :
    (ofRow origin row).parents = List.ofFn row.references := rfl

omit [DecidableEq P.Judgment] in
@[simp] theorem ofRow_conclusion (origin : Origin) (row : Shared.Row P) :
    (ofRow origin row).conclusion = P.conclusion row.rule := rfl

omit [DecidableEq P.Judgment] in
/-- Complete ordered lookup is equivalent to the independent slot conditions.
Repeated positions remain repeated entries in the looked-up vector. -/
theorem lookup_ofFn (cache : Array P.Judgment) {n : Nat}
    (references : Fin n → Nat) (wanted : Fin n → P.Judgment) :
    DerivationGraph.lookupPremises cache (List.ofFn references) =
        some (List.ofFn wanted) ↔
      ∀ position, cache[references position]? = some (wanted position) := by
  induction n with
  | zero => simp [DerivationGraph.lookupPremises]
  | succ n ih =>
      rw [List.ofFn_succ, List.ofFn_succ]
      constructor
      · intro accepted
        obtain ⟨first, head, later⟩ := Option.bind_eq_some_iff.mp accepted
        obtain ⟨rest, tail, equal⟩ := Option.bind_eq_some_iff.mp later
        have shape : first :: rest = wanted 0 :: List.ofFn (fun position => wanted position.succ) :=
          Option.some.inj equal
        have firstEqual := (List.cons.inj shape).1
        have restEqual := (List.cons.inj shape).2
        intro position
        cases position using Fin.cases with
        | zero => simpa only [firstEqual] using head
        | succ position =>
            exact (ih (fun position => references position.succ)
              (fun position => wanted position.succ)).mp (restEqual ▸ tail) position
      · intro accepted
        have tail := (ih (fun position => references position.succ)
          (fun position => wanted position.succ)).mpr (fun position => accepted position.succ)
        simp [DerivationGraph.lookupPremises, accepted 0, tail]

omit [DecidableEq P.Judgment] in
theorem row_lookup_iff (cache : Array P.Judgment) (row : Shared.Row P) :
    DerivationGraph.lookupPremises cache (List.ofFn row.references) =
        some (P.premises row.rule) ↔ Shared.ValidRow cache.toList row := by
  simpa only [List.ofFn_get, Shared.ValidRow, Array.getElem?_toList] using
    (lookup_ofFn cache row.references (P.premises row.rule).get)

/-- One generic replay performs exactly the existing slot checker. Rejection
is preserved as well as success; no malformed reference is filled in later. -/
theorem replay_row (origin : Origin) (cache : Array P.Judgment) (row : Shared.Row P) :
    (ofRow origin row).replay P.ruleWitness cache =
      if (Shared.inspectRow cache.toList row).1 then
        some (cache.push (P.conclusion row.rule)) else none := by
  unfold DerivationGraph.Node.replay
  cases lookup : DerivationGraph.lookupPremises cache (List.ofFn row.references) with
  | none =>
      have refused : (Shared.inspectRow cache.toList row).1 = false := by
        apply Bool.eq_false_iff.mpr
        intro accepted
        have found := (row_lookup_iff cache row).mpr
          ((Shared.inspectRow_exact _ row).mp accepted)
        rw [lookup] at found
        cases found
      simp [ofRow, lookup, refused]
  | some premises =>
      by_cases equal : premises = P.premises row.rule
      · have accepted : (Shared.inspectRow cache.toList row).1 = true :=
          (Shared.inspectRow_exact _ row).mpr ((row_lookup_iff cache row).mp
            (by simpa only [lookup, Option.some.injEq] using equal))
        simp [ofRow, lookup, Presentation.ruleWitness, equal, accepted]
      · have refused : (Shared.inspectRow cache.toList row).1 = false := by
          apply Bool.eq_false_iff.mpr
          intro accepted
          have found := (row_lookup_iff cache row).mpr
            ((Shared.inspectRow_exact _ row).mp accepted)
          rw [lookup] at found
          exact equal (Option.some.inj found)
        simp [ofRow, lookup, Presentation.ruleWitness, equal, refused]

/-- The two independently defined replay functions agree on every row list,
including unused bad rows, retained prefixes and failed executions. -/
theorem replay_rows (origin : Origin) (cache : Array P.Judgment)
    (rows : List (Shared.Row P)) :
    DerivationGraph.replayFrom P.ruleWitness cache (rows.map (ofRow origin)) =
      ((Shared.inspectRows cache.toList rows).table).map List.toArray := by
  induction rows generalizing cache with
  | nil => simp [DerivationGraph.replayFrom, Shared.inspectRows]
  | cons row rows ih =>
      simp only [List.map_cons, DerivationGraph.replayFrom, replay_row]
      cases tested : (Shared.inspectRow cache.toList row).1 with
      | false => simp [tested, Shared.inspectRows]
      | true =>
          simpa only [tested, ↓reduceIte, Bind.bind, Option.bind,
            Shared.inspectRows, Array.toList_push] using ih (cache.push (P.conclusion row.rule))

/-- A requested root uses the ordinary graph replay and positional lookup. -/
def check (origin : Origin) (certificate : Shared.Certificate P)
    (wanted : P.Judgment) : Bool :=
  match DerivationGraph.replay P.ruleWitness (certificate.rows.map (ofRow origin)) with
  | none => false
  | some cache => decide (cache[certificate.root]? = some wanted)

/-- Shared reconstruction, judgment-only execution and generic graph replay
give the same verdict, not merely the same sound conclusions. -/
theorem check_eq_shared (origin : Origin) (certificate : Shared.Certificate P)
    (wanted : P.Judgment) : check origin certificate wanted = Shared.check certificate wanted := by
  rw [← Shared.checkJudgments_eq_check]
  unfold check DerivationGraph.replay
  rw [replay_rows]
  cases table : (Shared.inspectRows ([] : List P.Judgment) certificate.rows).table with
  | none => simp [table, Shared.checkJudgments, Shared.checkJudgmentsWithWork_eq_inspectRows]
  | some values => simp [table, Shared.checkJudgments, Shared.checkJudgmentsWithWork_eq_inspectRows]

/-- Finite source derivability has an accepted generic graph, and every
accepted generic root reconstructs a source derivation. -/
theorem nonempty_derivation_iff_graph (origin : Origin) (wanted : P.Judgment) :
    Nonempty (P.Derivation wanted) ↔
      ∃ (nodes : List (DerivationGraph.Node P.Judgment P.Rule Origin))
        (cache : Array P.Judgment) (root : Nat),
        DerivationGraph.replay P.ruleWitness nodes = some cache ∧
          cache[root]? = some wanted := by
  rw [Presentation.nonempty_derivation_iff_derives]
  exact DerivationGraph.derives_iff_checked_graph P.ruleWitness origin wanted

namespace Controls

abbrev presentation : Presentation where
  Judgment := Bool
  Rule := Bool
  conclusion := id
  premises rule := if rule then [false, false] else []

def initial : Shared.Row presentation := ⟨false, Fin.elim0⟩

def repeated : Shared.Row presentation := ⟨true, fun _ => 0⟩

def forward : Shared.Row presentation := ⟨true, fun _ => 1⟩

theorem repeated_premises_retained :
    (ofRow () repeated).parents = [0, 0] := by decide +kernel

theorem repeated_premises_accept :
    check () ⟨[initial, repeated], 1⟩ true = true := by decide +kernel

theorem forward_premises_refused :
    check () ⟨[initial, forward], 1⟩ true = false := by decide +kernel

theorem wrong_root_refused :
    check () ⟨[initial, repeated], 0⟩ true = false := by decide +kernel

theorem unused_bad_row_refused :
    check () ⟨[initial, forward], 0⟩ false = false := by decide +kernel

theorem equal_conclusions_keep_two_rows :
    DerivationGraph.replay presentation.ruleWitness
      ([initial, initial].map (ofRow ())) = some #[false, false] := by decide +kernel

end Controls

#print axioms Presentation.nonempty_derivation_iff_derives
#print axioms replay_row
#print axioms replay_rows
#print axioms check_eq_shared
#print axioms nonempty_derivation_iff_graph

end PresentationGraph
end Mettapedia.OSLF.NativeTypes.Certificates
