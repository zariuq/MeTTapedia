import Mettapedia.GSLT.LanguageDef.ProgrammableSpaceMM2Grammar

/-!
# Rule-scoped MM2 matching for programmable spaces

The structural matching cursor retains its unfinished syntax and physical
witness positions. Its captured read copy uses the rule-scoped executor's
compact-key support operations. Completed rows enter the actual rule-scoped
sink implementation, including output-local variables and opaque captures.

The inputs are conjunctions or explicit BTM factors, as admitted by the native
MM2 resource profile. The original directive and its input spelling remain
available to reflective consumers. The batch is atomic with respect to other
workspace mutations: a private snapshot is not a licence to commit against an
independently changed store.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ProgrammableSpaceMM2Matching

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK
open MM2MatchingCursor
open Mettapedia.Machines.Cursor
open HostCalls (collect)

/-- An actual decoded directive with only workspace-matching input factors. -/
structure Request where
  directive : SourceExecFact
  pattern : Pattern
  factorization : factors directive.rule.input = pattern.atoms.map SourceFactor.btm

def live (space : List Atom) (request : Request) : List Atom :=
  morkEraseSupport space request.directive.atom

def snapshot (space : List Atom) (request : Request) : List Atom :=
  morkInsertSupport (live space request) request.directive.atom

def initial (space : List Atom) (request : Request) : StructuralQuanta.State :=
  StructuralQuanta.start (snapshot space request) request.directive.rule.input

abbrev packet (space : List Atom) (request : Request) :=
  NativeControlCursor.packet (StructuralQuanta.pull (entries (snapshot space request)))
    (initial space request) []

abbrev Result (space : List Atom) (request : Request) :=
  Outcome (StructuralQuanta.provider (entries (snapshot space request)))
    (NativeControlCursor.client Row) ()

def guarded (request : Request) (rows : List Row) : List Row :=
  rows.filter fun row => matchSourceGuards row.1 request.directive.rule.guards

def finalize (space : List Atom) (request : Request) (rows : List Row) : List Atom :=
  cApplyRuleScopedTemplate request.directive.rule.input (live space request)
    ((guarded request rows).map Prod.fst) request.directive.rule.tmpl

def publish (space : List Atom) (request : Request) :
    Result space request → Option (List Atom) :=
  fun outcome => (NativeControlCursor.published _ outcome).map (finalize space request)

def run (space : List Atom) (request : Request) (fuel : Nat) :
    Nat × Result space request :=
  advance (StructuralQuanta.provider (entries (snapshot space request)))
    (NativeControlCursor.client Row) (fun _ _ => 1) fuel (packet space request)

@[simp] theorem paused_cannot_publish (space : List Atom) (request : Request)
    (residual : Packet (StructuralQuanta.provider (entries (snapshot space request)))
      (NativeControlCursor.client Row) ()) :
    publish space request (.paused residual) = none := rfl

theorem run_observation (space : List Atom) (request : Request) (fuel : Nat) :
    publish space request (run space request (fuel + 1)).2 =
      (collect (StructuralQuanta.pull (entries (snapshot space request))) fuel
        (initial space request)).map (finalize space request) := by
  unfold publish run packet
  rw [NativeControlCursor.advance_collect]
  simp

theorem completed_rows (space : List Atom) (request : Request) (fuel : Nat)
    (rows : List Row)
    (completed : collect (StructuralQuanta.pull (entries (snapshot space request)))
      fuel (initial space request) = some rows) :
    rows.map (ProgrammableSpaceMM2Grammar.sourceRow request.directive.rule.input) =
      cMatchInputSpecMork [] (snapshot space request) request.directive.rule.input := by
  rw [StructuralQuanta.completed_rows
    (snapshot space request) request.directive.rule.input [] fuel rows completed]
  exact ProgrammableSpaceMM2Grammar.btm_cursor_rows
    (snapshot space request) request.directive.rule.input request.pattern request.factorization []

theorem guarded_substitutions (request : Request) (rows : List Row) :
    (guarded request rows).map Prod.fst =
      ((rows.map (ProgrammableSpaceMM2Grammar.sourceRow request.directive.rule.input)).filter fun row =>
        matchSourceGuards row.1 request.directive.rule.guards).map Prod.fst := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
      simp only [guarded, List.filter_cons, List.map_cons,
        ProgrammableSpaceMM2Grammar.sourceRow_substitution] at ih ⊢
      split <;> simp_all [ProgrammableSpaceMM2Grammar.sourceRow_substitution]

/-- The cursor and independently defined whole source firing produce exactly
the same store, while the receipt retains the erased witness positions. -/
theorem completed_finalize (space : List Atom) (request : Request) (fuel : Nat)
    (rows : List Row)
    (completed : collect (StructuralQuanta.pull (entries (snapshot space request)))
      fuel (initial space request) = some rows) :
    finalize space request rows =
      cFireRuleScopedSourceExecFact space request.directive := by
  unfold finalize
  rw [guarded_substitutions, completed_rows space request fuel rows completed]
  rfl

theorem publish_sound (space : List Atom) (request : Request) (fuel : Nat)
    (target : List Atom)
    (published : publish space request (run space request (fuel + 1)).2 = some target) :
    target = cFireRuleScopedSourceExecFact space request.directive := by
  rw [run_observation] at published
  obtain ⟨rows, completed, rfl⟩ := Option.map_eq_some_iff.mp published
  exact completed_finalize space request fuel rows completed

/-- This bound is a proof of finite completion, not a machine-time estimate. -/
noncomputable def allowance (space : List Atom) (request : Request) : Nat :=
  StructuralQuanta.remainingCost (entries (snapshot space request))
    (initial space request) + 1

theorem collect_complete (space : List Atom) (request : Request) :
    collect (StructuralQuanta.pull (entries (snapshot space request)))
      (allowance space request) (initial space request) =
        some (StructuralQuanta.residualRows (entries (snapshot space request))
          (initial space request)) :=
  StructuralQuanta.collect_complete _ _ _ (Nat.lt_succ_self _)

theorem publish_complete (space : List Atom) (request : Request) :
    publish space request (run space request (allowance space request + 1)).2 =
      some (cFireRuleScopedSourceExecFact space request.directive) := by
  rw [run_observation, collect_complete]
  exact congrArg some (completed_finalize _ _ _ _ (collect_complete space request))

/-- Suspension preserves the actual private cursor, accumulated ordered rows
and their charge. It does not restart from the original workspace. -/
theorem pause_resume (space : List Atom) (request : Request) (first later : Nat) :
    run space request (first + later) =
      Mettapedia.Machines.Cursor.resume
        (StructuralQuanta.provider (entries (snapshot space request)))
        (NativeControlCursor.client Row) (fun _ _ => 1) later
        (run space request first) :=
  StructuralQuanta.pause_resume_exact _ first later (initial space request) []

end Mettapedia.GSLT.LanguageDef.ProgrammableSpaceMM2Matching
