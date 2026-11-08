import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.ScopedSubtypeReads

/-!
# Resource closure and world independence of occurrence-scoped subtype reads

Every row query is freshly instantiated using the threaded name supply.
The proofs compare the complete answer and final supply, including supplies
advanced by failed matches and unfinished closure rounds. Resource closure
is required only for rows visited by the algorithm's actual row classifier.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.ScopedSubtypeReadSafety

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open TypeDependencyAdmission ScopedSubtypeReads
open TypeReadSupply (Supply fresh)
open RetainedTypePayloads (ExternalView)

def RowsSafe (sourceRows : List Atom) : Prop :=
  ∀ row ∈ sourceRows, possibleRow row = true → resourceFree row = true

theorem rowsSafe_of_resourceFree (sourceRows : List Atom) (safe : resourceFreeList sourceRows = true) :
    RowsSafe sourceRows := fun row member _ => (resourceFreeList_iff _).mp safe row member

theorem rowsSafe_tail {row : Atom} {rest : List Atom} (safe : RowsSafe (row :: rest)) : RowsSafe rest :=
  fun value member possible => safe value (List.mem_cons_of_mem _ member) possible

theorem rows_safe (world : ExternalView) (input : Atom) (resultName : String)
    (inputSafe : resourceFree input = true) (sourceRows : List Atom) (safe : RowsSafe sourceRows)
    (supply : Supply) : resourceFreeList (rows world input resultName sourceRows supply).1 = true := by
  induction sourceRows generalizing supply with
  | nil => rfl
  | cons row rest ih =>
      have tailSafe := rowsSafe_tail safe
      dsimp only [rows]
      split
      · rename_i possible
        have rowSafe : resourceFree (fresh supply row).1 = true := by
          rw [TypeReadSupply.fresh_resourceFree]
          exact safe row (by simp) possible
        cases reply : TypeScopeClosure.subtypeRow world input resultName (fresh supply row).1 with
        | none => simpa only [reply, Option.toList_none, List.nil_append] using ih tailSafe (fresh supply row).2
        | some type_ =>
            have typeSafe := TypeScopeClosure.subtypeRow_resourceFree world input resultName inputSafe
              (fresh supply row).1 rowSafe type_ reply
            simp only [Option.toList_some, List.singleton_append, resourceFreeList, typeSafe,
              Bool.true_and]
            exact ih tailSafe _
      · exact ih tailSafe supply

theorem rows_world (first second : ExternalView) (input : Atom) (resultName : String)
    (inputSafe : resourceFree input = true) (sourceRows : List Atom) (safe : RowsSafe sourceRows)
    (supply : Supply) :
    rows first input resultName sourceRows supply = rows second input resultName sourceRows supply := by
  induction sourceRows generalizing supply with
  | nil => rfl
  | cons row rest ih =>
      have tailSafe := rowsSafe_tail safe
      dsimp only [rows]
      split
      · rename_i possible
        have rowSafe : resourceFree (fresh supply row).1 = true := by
          rw [TypeReadSupply.fresh_resourceFree]
          exact safe row (by simp) possible
        rw [TypeScopeClosure.subtypeRow_world first second input resultName inputSafe (fresh supply row).1 rowSafe]
        rw [ih tailSafe]
      · exact ih tailSafe supply

theorem query_safe (world : ExternalView) (sourceRows : List Atom) (safe : RowsSafe sourceRows)
    (base : String) (input : Atom) (inputSafe : resourceFree input = true) (supply : Supply) :
    resourceFreeList (query world sourceRows base input supply).1 = true :=
  rows_safe world input _ inputSafe sourceRows safe _

theorem query_world (first second : ExternalView) (sourceRows : List Atom) (safe : RowsSafe sourceRows)
    (base : String) (input : Atom) (inputSafe : resourceFree input = true) (supply : Supply) :
    query first sourceRows base input supply = query second sourceRows base input supply :=
  rows_world first second input _ inputSafe sourceRows safe _

theorem discoveries_safe (world : ExternalView) (sourceRows : List Atom) (safe : RowsSafe sourceRows)
    (base : String) (alpha : Atom → Atom → Bool) (before : SubtypeClosureRounds.State)
    (frontier : List (SubtypeClosureRounds.Entry × Nat))
    (frontierSafe : ∀ pair ∈ frontier, resourceFree pair.1.type_ = true) (supply : Supply) :
    ∀ entry ∈ (discoveries world sourceRows base alpha before frontier supply).1,
      resourceFree entry.type_ = true := by
  induction frontier generalizing supply with
  | nil => intro entry member; cases member
  | cons pair rest ih =>
      rcases pair with ⟨parent, index⟩
      have parentSafe := frontierSafe (parent, index) (by simp)
      have tailSafe : ∀ pair ∈ rest, resourceFree pair.1.type_ = true :=
        fun pair member => frontierSafe pair (List.mem_cons_of_mem _ member)
      dsimp only [discoveries]
      split
      · exact ih tailSafe supply
      · intro entry member
        rcases List.mem_append.mp member with added | later
        · obtain ⟨type_, accepted, rfl⟩ := List.mem_map.mp added
          exact (resourceFreeList_iff _).mp (query_safe world sourceRows safe base parent.type_ parentSafe supply)
            type_ (List.mem_of_mem_filter accepted)
        · exact ih tailSafe _ entry later

theorem discoveries_world (first second : ExternalView) (sourceRows : List Atom) (safe : RowsSafe sourceRows)
    (base : String) (alpha : Atom → Atom → Bool) (before : SubtypeClosureRounds.State)
    (frontier : List (SubtypeClosureRounds.Entry × Nat))
    (frontierSafe : ∀ pair ∈ frontier, resourceFree pair.1.type_ = true) (supply : Supply) :
    discoveries first sourceRows base alpha before frontier supply =
      discoveries second sourceRows base alpha before frontier supply := by
  induction frontier generalizing supply with
  | nil => rfl
  | cons pair rest ih =>
      rcases pair with ⟨parent, index⟩
      have parentSafe := frontierSafe (parent, index) (by simp)
      have tailSafe : ∀ pair ∈ rest, resourceFree pair.1.type_ = true :=
        fun pair member => frontierSafe pair (List.mem_cons_of_mem _ member)
      dsimp only [discoveries]
      split
      · exact ih tailSafe supply
      · rw [query_world first second sourceRows safe base parent.type_ parentSafe supply]
        rw [ih tailSafe]

theorem frontier_safe (before : SubtypeClosureRounds.State) (safe : SubtypeClosureRounds.Safe before) :
    ∀ pair ∈ before.known.zipIdx.drop before.frontier, resourceFree pair.1.type_ = true := by
  intro pair member
  exact safe pair.1 (List.fst_mem_of_mem_zipIdx (List.mem_of_mem_drop member))

theorem round_safe (world : ExternalView) (sourceRows : List Atom) (safe : RowsSafe sourceRows)
    (base : String) (alpha : Atom → Atom → Bool) (before next : SubtypeClosureRounds.State)
    (beforeSafe : SubtypeClosureRounds.Safe before) (supply : Supply)
    (advanced : (round world sourceRows base alpha before supply).1 = some next) :
    SubtypeClosureRounds.Safe next := by
  dsimp only [ScopedSubtypeReads.round] at advanced
  split at advanced
  · contradiction
  · cases Option.some.inj advanced
    intro entry member
    rcases List.mem_append.mp member with old | added
    · exact beforeSafe entry old
    · exact discoveries_safe world sourceRows safe base alpha before _ (frontier_safe before beforeSafe)
        supply entry added

theorem round_world (first second : ExternalView) (sourceRows : List Atom) (safe : RowsSafe sourceRows)
    (base : String) (alpha : Atom → Atom → Bool) (before : SubtypeClosureRounds.State)
    (beforeSafe : SubtypeClosureRounds.Safe before) (supply : Supply) :
    round first sourceRows base alpha before supply = round second sourceRows base alpha before supply := by
  unfold ScopedSubtypeReads.round
  rw [discoveries_world first second sourceRows safe base alpha before _ (frontier_safe before beforeSafe) supply]

/-- Even an unfinished residual state has only resource-free types. -/
theorem run_safe (world : ExternalView) (sourceRows : List Atom) (safe : RowsSafe sourceRows)
    (base : String) (alpha : Atom → Atom → Bool) (budget : Nat) (before : SubtypeClosureRounds.State)
    (beforeSafe : SubtypeClosureRounds.Safe before) (supply : Supply) :
    SubtypeClosureRounds.Safe (run world sourceRows base alpha budget before supply).1.state := by
  induction budget generalizing before supply with
  | zero => exact beforeSafe
  | succ budget ih =>
      dsimp only [run]
      split
      · exact beforeSafe
      · rename_i next advanced
        exact ih next (round_safe world sourceRows safe base alpha before next beforeSafe supply advanced) _

/-- The complete observation includes the reached name supply and preserves
the complete/unfinished tag, not merely the list of discovered types. -/
theorem run_world (first second : ExternalView) (sourceRows : List Atom) (safe : RowsSafe sourceRows)
    (base : String) (alpha : Atom → Atom → Bool) (budget : Nat) (before : SubtypeClosureRounds.State)
    (beforeSafe : SubtypeClosureRounds.Safe before) (supply : Supply) :
    run first sourceRows base alpha budget before supply =
      run second sourceRows base alpha budget before supply := by
  induction budget generalizing before supply with
  | zero => rfl
  | succ budget ih =>
      have same := round_world first second sourceRows safe base alpha before beforeSafe supply
      dsimp only [run]
      rw [← same]
      cases advanced : (round first sourceRows base alpha before supply).1 with
      | none => rfl
      | some next =>
          exact ih next (round_safe first sourceRows safe base alpha before next beforeSafe supply advanced) _

theorem completeTypes_world (first second : ExternalView) (sourceRows : List Atom) (safe : RowsSafe sourceRows)
    (base : String) (alpha : Atom → Atom → Bool) (budget : Nat) (seeds : List Atom)
    (seedSafe : resourceFreeList seeds = true) (supply : Supply) :
    completeTypes first sourceRows base alpha budget seeds supply =
      completeTypes second sourceRows base alpha budget seeds supply := by
  unfold completeTypes
  rw [run_world first second sourceRows safe base alpha budget _ (SubtypeClosureRounds.start_safe seeds seedSafe)]

theorem completeTypes_safe (world : ExternalView) (sourceRows : List Atom) (safe : RowsSafe sourceRows)
    (base : String) (alpha : Atom → Atom → Bool) (budget : Nat) (seeds : List Atom)
    (seedSafe : resourceFreeList seeds = true) (supply : Supply) (result : List Atom)
    (completed : (completeTypes world sourceRows base alpha budget seeds supply).1 = some result) :
    resourceFreeList result = true := by
  have safeRun := run_safe world sourceRows safe base alpha budget _
    (SubtypeClosureRounds.start_safe seeds seedSafe) (TypeReadSupply.remember supply seeds)
  dsimp only [completeTypes] at completed
  cases outcome : (run world sourceRows base alpha budget (SubtypeClosureRounds.start seeds)
      (TypeReadSupply.remember supply seeds)).1 with
  | unfinished state => simp only [outcome] at completed; contradiction
  | complete state =>
      simp only [outcome] at completed safeRun
      cases Option.some.inj completed
      apply (resourceFreeList_iff _).mpr
      intro type_ member
      obtain ⟨entry, present, rfl⟩ := List.mem_map.mp member
      exact safeRun entry present

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.ScopedSubtypeReadSafety
