import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.InductiveTypes.Signature

/-!
# The numbers on the step

The type of numbers is the region at the handle `num`, declared by two constructors, `zero` and the
successor (`natRules`), the second recursive.

**What the region holds** (`natRules_generated_iff`): the generated rows are exactly the rows
`natRow (numeral k)`. **What is decided from the row**: membership, by a structural check of the row
(`generated_iff_isNumeral`); the constructor that made a row and its premises, since one row is the
conclusion of at most one constructor instance (`natRules_syntaxDirected`); and the stage at which the
row is generated: `natRow (numeral k)` is in stage `m` exactly when `k < m` (`numeral_mem_stage_iff`),
so its first stage is `k + 1` (`first_stage`). A free type's row carries its derivation.

**The parties.** `owner` holds `send` and `peek` at `num` and installs both constructors; `reader`
holds `peek` only and installs both constructors and the junk schema; `junkWriter` holds the owner's
rights and installs the junk schema. Three systems:

* `soleOwner` (owner and reader): one writer. Membership holds on every run
  (`soleOwner_membership`), and every closure statement survives the reader (`soleOwner_closure`):
  the reader's installed junk schema never fires a formed move in the type.
* `twoWriters` (the owner twice): **membership, induction and case analysis by constructor survive**
  (`twoWriters_membership`, `twoWriters_induction`, `twoWriters_cases`), and **a closure statement
  fails**: "the numbers present are only `0`" holds
  in a reachable state and the second writer's successor move breaks it
  (`twoWriters_breaks_closure`), as the exact theorem predicts, since that list is not closed under
  the successor (`onlyZero_not_ruleClosed`).
* `withJunk` (owner and junk writer): **induction fails on a named property**, "is the row of a
  numeral" (`IsNumeralRow`, closed under the constructors, `isNumeralRow_ruleClosed`): a run from the
  empty store reaches `natRow junkE`, which does not have it (`withJunk_breaks_induction`).
* `withShortcut` (owner and a writer that makes the row of two from nothing): the shortcut writer does
  not write through the constructors (`shortcutWriter_not_writes`), yet **membership survives**
  (`withShortcut_membership`): the exact need of membership is that every row written is generated;
  the constructor discipline is the condition checkable at each firing without deciding membership.
  What the shortcut breaks is that a made row's premises are present when it is made: it makes the
  row of two where the row of one is not present (`shortcut_skips_premise`).

**Existence**: every generated row is reached from the empty store by a run of the owner
(`owner_reaches`), so each "every run" statement above speaks of runs that exist.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.InductiveTypes

open WhenTypesApply.ThatsAll
open WhenTypesApply.TwoKinds (stage)
open NamesOnTheStep NamesOnTheStep.IssuingControls
open MeTTaCalculus.InteractionTypes (Rights Facet)

namespace Numbers

/-! ## The generated rows -/

theorem mem_natRules {ps : List Expr} {r : Expr} :
    (ps, r) ∈ natRules ↔
      (ps = [] ∧ r = natRow zeroE) ∨ ∃ x, ps = [natRow x] ∧ r = natRow (succE x) := by
  simp [natRules]

theorem zero_mem : (([] : List Expr), natRow zeroE) ∈ natRules :=
  mem_natRules.mpr (Or.inl ⟨rfl, rfl⟩)

theorem succ_mem (x : Expr) : ([natRow x], natRow (succE x)) ∈ natRules :=
  mem_natRules.mpr (Or.inr ⟨x, rfl, rfl⟩)

/-- **The generated rows are the rows of the numerals.** -/
theorem natRules_generated_iff {r : Expr} :
    Generated natRules ∅ r ↔ ∃ k, r = natRow (numeral k) := by
  constructor
  · intro generated
    induction generated with
    | base inside => exact absurd inside (Set.notMem_empty _)
    | @rule ps r declared _ ih =>
        rcases mem_natRules.mp declared with ⟨rfl, rfl⟩ | ⟨x, rfl, rfl⟩
        · exact ⟨0, rfl⟩
        · obtain ⟨k, same⟩ := ih (natRow x) (List.mem_singleton_self _)
          exact ⟨k + 1, by rw [natRow_injective same]; rfl⟩
  · rintro ⟨k, rfl⟩
    induction k with
    | zero => exact Generated.rule zero_mem fun _ member => absurd member List.not_mem_nil
    | succ k ih =>
        exact Generated.rule (succ_mem (numeral k)) fun p member => by
          rw [List.mem_singleton.mp member]
          exact ih

/-- The row of every numeral is generated. -/
theorem numeral_generated (k : ℕ) : Generated natRules ∅ (natRow (numeral k)) :=
  natRules_generated_iff.mpr ⟨k, rfl⟩

theorem numeral_ne_junk (k : ℕ) : numeral k ≠ junkE := by
  cases k <;> simp [numeral, junkE, zeroE, succE]

/-- `natRow junkE` is not generated. -/
theorem junk_not_generated : ¬ Generated natRules ∅ (natRow junkE) := by
  intro generated
  obtain ⟨k, same⟩ := natRules_generated_iff.mp generated
  exact numeral_ne_junk k (natRow_injective same).symm

/-! ## What is decided from the row -/

/-- **One row, one constructor instance**: the conclusion determines the premises. -/
theorem natRules_syntaxDirected {ps ps' : List Expr} {r : Expr} (first : (ps, r) ∈ natRules)
    (second : (ps', r) ∈ natRules) : ps = ps' := by
  rcases mem_natRules.mp first with ⟨rfl, rfl⟩ | ⟨x, rfl, rfl⟩ <;>
    rcases mem_natRules.mp second with ⟨rfl, same⟩ | ⟨y, rfl, same⟩
  · rfl
  · simp [natRow, zeroE, succE] at same
  · simp [natRow, zeroE, succE] at same
  · rw [succE_injective (natRow_injective same)]

/-- **The structural check of a number.** -/
def isNumeral : Expr → Bool
  | .sym 100 => true
  | .app (.sym 101) x => isNumeral x
  | _ => false

theorem isNumeral_numeral (k : ℕ) : isNumeral (numeral k) = true := by
  induction k with
  | zero => rfl
  | succ k ih => exact ih

theorem isNumeral_iff {e : Expr} : isNumeral e = true ↔ ∃ k, e = numeral k := by
  constructor
  · intro checked
    induction e with
    | sym k =>
        by_cases same : k = 100
        · subst same
          exact ⟨0, rfl⟩
        · simp [isNumeral, same] at checked
    | app f a _ iha =>
        cases f with
        | sym k =>
            by_cases same : k = 101
            · subst same
              obtain ⟨k, rfl⟩ := iha checked
              exact ⟨k + 1, rfl⟩
            · simp [isNumeral, same] at checked
        | app _ _ => simp [isNumeral] at checked
        | name _ => simp [isNumeral] at checked
        | code _ => simp [isNumeral] at checked
    | name n => simp [isNumeral] at checked
    | code e _ => simp [isNumeral] at checked
  · rintro ⟨k, rfl⟩
    exact isNumeral_numeral k

/-- **Membership is decided from the row by recursion on it**: a free type's row carries its
derivation. -/
theorem generated_iff_isNumeral {e : Expr} :
    Generated natRules ∅ (natRow e) ↔ isNumeral e = true := by
  rw [natRules_generated_iff, isNumeral_iff]
  constructor
  · rintro ⟨k, same⟩
    exact ⟨k, natRow_injective same⟩
  · rintro ⟨k, rfl⟩
    exact ⟨k, rfl⟩

/-- **The stage of a row is read from the row**: `natRow (numeral k)` is in stage `m` exactly when
`k < m`. -/
theorem numeral_mem_stage_iff (k m : ℕ) : natRow (numeral k) ∈ stage natRules ∅ m ↔ k < m := by
  induction m generalizing k with
  | zero => simp [stage]
  | succ m ih =>
      show natRow (numeral k) ∈ (∅ : Set Expr) ∪ {r | ∃ premises, (premises, r) ∈ natRules ∧
        ∀ p ∈ premises, p ∈ stage natRules ∅ m} ↔ k < m + 1
      constructor
      · rintro (inside | ⟨ps, declared, present⟩)
        · exact absurd inside (Set.notMem_empty _)
        · rcases mem_natRules.mp declared with ⟨rfl, same⟩ | ⟨x, rfl, same⟩
          · cases k with
            | zero => omega
            | succ k =>
                have := natRow_injective same
                simp [numeral, zeroE, succE] at this
          · cases k with
            | zero =>
                have := natRow_injective same
                simp [numeral, zeroE, succE] at this
            | succ k =>
                have x_eq : numeral k = x := succE_injective (natRow_injective same)
                subst x_eq
                have below := (ih k).mp (present _ (List.mem_singleton_self _))
                omega
      · intro lt
        right
        cases k with
        | zero => exact ⟨[], zero_mem, fun _ member => absurd member List.not_mem_nil⟩
        | succ k =>
            refine ⟨[natRow (numeral k)], succ_mem (numeral k), fun p member => ?_⟩
            rw [List.mem_singleton.mp member]
            exact (ih k).mpr (by omega)

/-- The first stage of `natRow (numeral k)` is `k + 1`. -/
theorem first_stage (k : ℕ) :
    natRow (numeral k) ∈ stage natRules ∅ (k + 1) ∧ natRow (numeral k) ∉ stage natRules ∅ k :=
  ⟨(numeral_mem_stage_iff k (k + 1)).mpr (by omega),
    fun inside => absurd ((numeral_mem_stage_iff k k).mp inside) (by omega)⟩

/-! ## The parties -/

/-- Rights to make and keep number rows. -/
def writerRights : Rights Handle := fun n f =>
  decide (n = .num) && (decide (f = .send) || decide (f = .peek))

/-- Rights to keep number rows only. -/
def readerRights : Rights Handle := fun n f => decide (n = .num) && decide (f = .peek)

/-- **The owner**: `send` and `peek` at `num`, both constructors installed. -/
def owner : SchemaPublicationAuthority.Process Schema Handle := ⟨writerRights, [.zero, .succ]⟩

/-- **A reader**: `peek` at `num`; it installs the constructors and the junk schema. -/
def reader : SchemaPublicationAuthority.Process Schema Handle :=
  ⟨readerRights, [.zero, .succ, .junk]⟩

/-- **A writer that does not follow the constructors**: the owner's rights, the junk schema. -/
def junkWriter : SchemaPublicationAuthority.Process Schema Handle := ⟨writerRights, [.junk]⟩

/-- One writer: the owner (`true`) and a reader. -/
def soleOwner : Bool → SchemaPublicationAuthority.Process Schema Handle :=
  fun b => cond b owner reader

/-- Two writers through the constructors. -/
def twoWriters : Bool → SchemaPublicationAuthority.Process Schema Handle := fun _ => owner

/-- The owner (`true`) and the junk writer. -/
def withJunk : Bool → SchemaPublicationAuthority.Process Schema Handle :=
  fun b => cond b owner junkWriter

/-- The region of the numbers. -/
abbrev inNum : Handle → Prop := fun n => n = .num

theorem owner_writes : Writes activate place inNum natRules owner := by
  refine writes_of_each fun schema installed x ρ computed => Or.inl ?_
  simp only [owner, List.mem_cons, List.not_mem_nil, or_false] at installed
  rcases installed with rfl | rfl
  · rcases x with _ | ⟨a, rest⟩
    · simp only [activate, Option.some.injEq] at computed
      exact ⟨_, zero_mem, computed.symm, fun _ member => absurd member List.not_mem_nil⟩
    · simp [activate] at computed
  · rcases x with _ | ⟨a, _ | ⟨b, rest⟩⟩
    · simp [activate] at computed
    · simp only [activate, Option.some.injEq] at computed
      refine ⟨_, succ_mem a, computed.symm, fun p member => ?_⟩
      rw [List.mem_singleton.mp member]
      rfl
    · simp [activate] at computed

theorem owner_realizes : Realizes activate place natRules owner := by
  intro d declared
  rcases mem_natRules.mp declared with ⟨first, second⟩ | ⟨x, first, second⟩
  · have same : d = ([], natRow zeroE) := Prod.ext first second
    subst same
    exact ⟨rfl, .zero, List.mem_cons_self .., [], rfl⟩
  · have same : d = ([natRow x], natRow (succE x)) := Prod.ext first second
    subst same
    exact ⟨rfl, .succ, List.mem_cons_of_mem _ (List.mem_cons_self ..), [x], rfl⟩

/-- The reader holds no `send` in the type. -/
theorem reader_noSend (e : Expr) (_inside : inNum (place e)) :
    reader.rights (place e) .send = false := by
  simp [reader, readerRights]

theorem soleOwner_writes (b : Bool) : Writes activate place inNum natRules (soleOwner b) := by
  cases b
  · exact writes_of_noSend reader_noSend
  · exact owner_writes

/-! ## Existence -/

/-- **Every generated row is reached** from the empty store by a run of the owner. -/
theorem owner_reaches (k : ℕ) :
    ∃ C, Relation.ReflTransGen (processStep activate place owner) ProgramAdequacy.emptyStore C ∧
      natRow (numeral k) ∈ contents C := by
  obtain ⟨C, run, -, present, -⟩ :=
    reachable_of_generated owner_realizes (numeral_generated k) _ plain_empty
  exact ⟨C, run, present⟩

/-! ## One writer -/

/-- **Membership with one writer**: in every state reached from the empty store, every number row
present is the row of a numeral. -/
theorem soleOwner_membership {C : Conf}
    (run : Relation.ReflTransGen (systemStep activate place soleOwner) ProgramAdequacy.emptyStore C)
    {r : Expr} (present : r ∈ contents C) (inside : inNum (place r)) :
    ∃ k, r = natRow (numeral k) :=
  natRules_generated_iff.mp
    (membership soleOwner_writes run (closedBy_empty _ _) r present inside)

/-- **Every closure statement about the numbers survives the reader**, though it installs a schema
that makes junk: it holds no `send` in the type. -/
theorem soleOwner_closure :
    ClosedReadingSurvives (fun actor => processStep activate place (soleOwner actor)) contents
      (fun e => inNum (place e)) true :=
  closure_of_soleSender fun actor other e inside => by
    cases actor
    · exact reader_noSend e inside
    · exact absurd rfl other

/-! ## Two writers through the constructors -/

theorem twoWriters_writes (b : Bool) : Writes activate place inNum natRules (twoWriters b) :=
  owner_writes

/-- **Membership survives a second writer.** -/
theorem twoWriters_membership {C : Conf}
    (run : Relation.ReflTransGen (systemStep activate place twoWriters) ProgramAdequacy.emptyStore C)
    {r : Expr} (present : r ∈ contents C) (inside : inNum (place r)) :
    ∃ k, r = natRow (numeral k) :=
  natRules_generated_iff.mp
    (membership twoWriters_writes run (closedBy_empty _ _) r present inside)

/-- **Induction survives a second writer**: the induction principle of the numbers, as an invariant
of the runs of two writers. -/
theorem twoWriters_induction (P : Expr → Prop) (base : P (natRow zeroE))
    (step : ∀ x, P (natRow x) → P (natRow (succE x))) {C : Conf}
    (run : Relation.ReflTransGen (systemStep activate place twoWriters) ProgramAdequacy.emptyStore C)
    {r : Expr} (present : r ∈ contents C) (inside : inNum (place r)) : P r := by
  refine induction twoWriters_writes (P := P) ?_ run present inside
  intro ps r declared premises
  rcases mem_natRules.mp declared with ⟨rfl, rfl⟩ | ⟨x, rfl, rfl⟩
  · exact base
  · exact step x (premises _ (List.mem_singleton_self _))

/-- **Case analysis by constructor survives a second writer**: every number row of every state reached
from the empty store is the row of zero, or the row of a successor of a generated row. This is membership read through the
constructors; it is not a closure statement about the rows present. -/
theorem twoWriters_cases {C : Conf}
    (run : Relation.ReflTransGen (systemStep activate place twoWriters) ProgramAdequacy.emptyStore C)
    {r : Expr} (present : r ∈ contents C) (inside : inNum (place r)) :
    r = natRow zeroE ∨ ∃ x, r = natRow (succE x) ∧ Generated natRules ∅ (natRow x) := by
  obtain ⟨k, rfl⟩ := twoWriters_membership run present inside
  cases k with
  | zero => exact Or.inl rfl
  | succ k => exact Or.inr ⟨numeral k, rfl, numeral_generated k⟩

/-- "The numbers present are only `0`." -/
def onlyZero : Set Expr := {natRow zeroE}

theorem succ_zero_not_onlyZero : natRow (succE zeroE) ∉ onlyZero := by
  simp [onlyZero, natRow, succE, zeroE]

/-- That list is not closed under the successor. -/
theorem onlyZero_not_ruleClosed : ¬ RuleClosedIn natRules (fun e => inNum (place e)) onlyZero := by
  intro closed
  exact succ_zero_not_onlyZero (closed [natRow zeroE] (natRow (succE zeroE)) (succ_mem zeroE) rfl
    fun p member => by
      rw [List.mem_singleton.mp member]
      exact ⟨rfl, rfl⟩)

/-- **A closure statement fails with a second writer**: from the empty store the first writer makes
`0`, where "only `0`" holds; the second writer's successor move breaks it. -/
theorem twoWriters_breaks_closure :
    ∃ C C', Relation.ReflTransGen (systemStep activate place twoWriters) ProgramAdequacy.emptyStore C ∧
      ClosedBy contents (fun e => inNum (place e)) onlyZero C ∧
      processStep activate place (twoWriters false) C C' ∧
      ¬ ClosedBy contents (fun e => inNum (place e)) onlyZero C' := by
  obtain ⟨C, moved, plain, exact⟩ :=
    ctor_fires (activate := activate) (place := place) (process := owner) (d := ([], natRow zeroE))
      rfl (List.mem_cons_self ..) (x := []) rfl plain_empty
      fun _ member => absurd member List.not_mem_nil
  have onlyZeroC : contents C = {natRow zeroE} := by
    rw [exact, contents_empty]
    ext e
    simp
  obtain ⟨C', moved', -, exact'⟩ :=
    ctor_fires (activate := activate) (place := place) (process := owner)
      (d := ([natRow zeroE], natRow (succE zeroE))) rfl
      (List.mem_cons_of_mem _ (List.mem_cons_self ..)) (x := [zeroE]) rfl plain fun p member => by
        rw [List.mem_singleton.mp member, onlyZeroC]
        exact Set.mem_singleton _
  refine ⟨C, C', system_run_of_run (actor := true) (Relation.ReflTransGen.single moved), ?_, moved', ?_⟩
  · intro r inside _
    rw [onlyZeroC] at inside
    exact inside
  · intro closed
    exact succ_zero_not_onlyZero (closed _ (by rw [exact']; exact Set.mem_insert _ _) rfl)

/-- **The exact theorem's instance**: "only `0`" does not survive every move of the second writer. -/
theorem onlyZero_not_survives :
    ¬ ∀ C C', Plain C → processStep activate place (twoWriters false) C C' →
      ClosedBy contents (fun e => inNum (place e)) onlyZero C →
        ClosedBy contents (fun e => inNum (place e)) onlyZero C' :=
  fun survives => onlyZero_not_ruleClosed
    ((survives_iff_ruleClosedIn owner_writes owner_realizes onlyZero).mp survives)

/-- With two writers the region is not owned by either. -/
theorem twoWriters_not_owned (k : Bool) :
    ¬ Owned (fun actor => processStep activate place (twoWriters actor)) contents
      (fun e => inNum (place e)) k := by
  intro owned
  have survives := (closedReadingSurvives_iff_owned _ _ _ k).mpr owned
  obtain ⟨C, moved, plain, exact⟩ :=
    ctor_fires (activate := activate) (place := place) (process := owner) (d := ([], natRow zeroE))
      rfl (List.mem_cons_self ..) (x := []) rfl plain_empty
      fun _ member => absurd member List.not_mem_nil
  have missing : ClosedBy contents (fun e => inNum (place e)) ∅ ProgramAdequacy.emptyStore :=
    closedBy_empty _ _
  have := survives (!k) (by cases k <;> decide) ∅ _ _ moved missing (natRow zeroE)
    (by rw [exact]; exact Set.mem_insert _ _) rfl
  exact Set.notMem_empty _ this

/-! ## A writer that does not follow the constructors -/

/-- **"Is the row of a numeral"**, a property of rows. -/
def IsNumeralRow (e : Expr) : Prop := ∃ k, e = natRow (numeral k)

/-- It is closed under the constructors. -/
theorem isNumeralRow_ruleClosed : RuleClosed natRules IsNumeralRow := by
  intro ps r declared premises
  rcases mem_natRules.mp declared with ⟨rfl, rfl⟩ | ⟨x, rfl, rfl⟩
  · exact ⟨0, rfl⟩
  · obtain ⟨k, same⟩ := premises _ (List.mem_singleton_self _)
    exact ⟨k + 1, by rw [natRow_injective same]; rfl⟩

/-- The junk writer does not write through the constructors. -/
theorem junkWriter_not_writes : ¬ Writes activate place inNum natRules junkWriter := by
  intro writes
  obtain ⟨ps, declared, _⟩ := writes .junk (List.mem_singleton_self _) [] _ rfl (natRow junkE)
    (List.mem_singleton_self _) rfl rfl
  exact junk_not_generated (Generated.rule declared fun p member => by
    rcases mem_natRules.mp declared with ⟨_, same⟩ | ⟨x, _, same⟩
    · exact absurd (natRow_injective same) (numeral_ne_junk 0).symm
    · exact absurd (natRow_injective same) (by simp [junkE, succE]))

/-! ## A writer that skips premises: what membership needs exactly -/

/-- **A writer that skips premises**: the owner's rights; it makes the row of two from nothing. -/
def shortcutWriter : SchemaPublicationAuthority.Process Schema Handle := ⟨writerRights, [.shortcut]⟩

/-- The owner (`true`) and the shortcut writer. -/
def withShortcut : Bool → SchemaPublicationAuthority.Process Schema Handle :=
  fun b => cond b owner shortcutWriter

/-- The shortcut writer does not write through the constructors. -/
theorem shortcutWriter_not_writes : ¬ Writes activate place inNum natRules shortcutWriter := by
  intro writes
  obtain ⟨ps, declared, premises⟩ := writes .shortcut (List.mem_singleton_self _) [] _ rfl
    (natRow (succE (succE zeroE))) (List.mem_singleton_self _) rfl rfl
  rcases mem_natRules.mp declared with ⟨_, same⟩ | ⟨x, rfl, _⟩
  · simp [natRow, succE, zeroE] at same
  · have := (premises (natRow x) (List.mem_singleton_self _)).1
    simp [rule] at this

/-- A move of the shortcut writer keeps every number row generated: it makes only the row of two. -/
theorem shortcut_keeps {C C' : Conf} (moved : processStep activate place shortcutWriter C C')
    (holds : ClosedBy contents (fun e => inNum (place e)) {r | Generated natRules ∅ r} C) :
    ClosedBy contents (fun e => inNum (place e)) {r | Generated natRules ∅ r} C' := by
  obtain ⟨schema, installed, x, ρ, computed, sel, valid, -, rfl⟩ := moved
  have isShortcut : schema = .shortcut := List.mem_singleton.mp installed
  subst isShortcut
  rcases x with _ | ⟨a, rest⟩
  · simp only [activate, Option.some.injEq] at computed
    subst computed
    rintro r ⟨o, present, rfl⟩ inside
    rcases MeTTaCalculus.OccurrenceCommits.mem_fire.mp present with ⟨old, -⟩ | made
    · exact holds o.1 ⟨o, old, rfl⟩ inside
    · have madeList : o ∈ sel.made := by simpa [Selection.commit] using made
      have label : o.1 = natRow (succE (succE zeroE)) := List.mem_singleton.mp (made_label valid madeList)
      rw [label]
      exact numeral_generated 2
  · simp [activate] at computed

/-- **Membership survives a writer that skips premises**: the constructor discipline is sufficient for
membership, not necessary; what membership needs is that every row written is generated. -/
theorem withShortcut_membership {C : Conf}
    (run : Relation.ReflTransGen (systemStep activate place withShortcut) ProgramAdequacy.emptyStore C)
    {r : Expr} (present : r ∈ contents C) (inside : inNum (place r)) :
    ∃ k, r = natRow (numeral k) := by
  have invariant : ClosedBy contents (fun e => inNum (place e)) {r | Generated natRules ∅ r} C := by
    clear present inside
    induction run with
    | refl => exact closedBy_empty _ _
    | tail _ moved ih =>
        obtain ⟨actor, moved⟩ := moved
        cases actor
        · exact shortcut_keeps moved ih
        · exact closedBy_survives (throughConstructors_of_writes owner_writes)
            (ruleClosedIn_of_ruleClosed (generated_ruleClosed natRules ∅)) moved ih
  exact natRules_generated_iff.mp (invariant r present inside)

/-- **What the shortcut breaks**: from the empty store it makes the row of two while the row of one,
its premise, is not present; a writer through the constructors leaves every row's premises present when
it made it. -/
theorem shortcut_skips_premise :
    ∃ C, processStep activate place shortcutWriter ProgramAdequacy.emptyStore C ∧
      natRow (numeral 2) ∈ contents C ∧ natRow (numeral 1) ∉ contents C := by
  obtain ⟨C, moved, -, exact⟩ :=
    ctor_fires (activate := activate) (place := place) (process := shortcutWriter)
      (d := ([], natRow (succE (succE zeroE)))) rfl (List.mem_singleton_self _) (x := []) rfl
      plain_empty fun _ member => absurd member List.not_mem_nil
  refine ⟨C, moved, by rw [exact]; exact Set.mem_insert _ _, ?_⟩
  rw [exact, contents_empty]
  simp [numeral, natRow, succE, zeroE]

/-- **Induction fails on a named property** with a writer that does not follow the constructors: a run
from the empty store reaches a number row that is not the row of a numeral, though "is the row of a
numeral" is closed under the constructors. -/
theorem withJunk_breaks_induction :
    ∃ C, Relation.ReflTransGen (systemStep activate place withJunk) ProgramAdequacy.emptyStore C ∧
      natRow junkE ∈ contents C ∧ inNum (place (natRow junkE)) ∧ ¬ IsNumeralRow (natRow junkE) := by
  obtain ⟨C, moved, -, exact⟩ :=
    ctor_fires (activate := activate) (place := place) (process := junkWriter)
      (d := ([], natRow junkE)) rfl (List.mem_singleton_self _) (x := []) rfl plain_empty
      fun _ member => absurd member List.not_mem_nil
  refine ⟨C, system_run_of_run (actor := false) (Relation.ReflTransGen.single moved),
    by rw [exact]; exact Set.mem_insert _ _, rfl, ?_⟩
  rintro ⟨k, same⟩
  exact numeral_ne_junk k (natRow_injective same).symm

end Numbers

#print axioms Numbers.natRules_generated_iff
#print axioms Numbers.natRules_syntaxDirected
#print axioms Numbers.generated_iff_isNumeral
#print axioms Numbers.numeral_mem_stage_iff
#print axioms Numbers.first_stage
#print axioms Numbers.owner_writes
#print axioms Numbers.owner_realizes
#print axioms Numbers.owner_reaches
#print axioms Numbers.soleOwner_membership
#print axioms Numbers.soleOwner_closure
#print axioms Numbers.twoWriters_membership
#print axioms Numbers.twoWriters_induction
#print axioms Numbers.twoWriters_cases
#print axioms Numbers.twoWriters_breaks_closure
#print axioms Numbers.onlyZero_not_survives
#print axioms Numbers.twoWriters_not_owned
#print axioms Numbers.isNumeralRow_ruleClosed
#print axioms Numbers.junkWriter_not_writes
#print axioms Numbers.withJunk_breaks_induction
#print axioms Numbers.shortcutWriter_not_writes
#print axioms Numbers.withShortcut_membership
#print axioms Numbers.shortcut_skips_premise

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.InductiveTypes
