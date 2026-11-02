import Mettapedia.Logic.LP.ConjunctiveUnification
import Mettapedia.Machines.NestedQueryEffects
import Mettapedia.Languages.MeTTa.OSLFCore.Atom

/-!
# PeTTa nested matches answered by one join

PeTTa evaluates `(match S1 P1 (match S2 P2 ... T))`, and a conjunction
`(, P1 P2 ...)`, by reading each pattern's space when its branch is reached:
the first pattern once, each later one afresh for every solution of the ones
before it, after the template instances of the earlier solutions have made
their changes.  A stored row's variables are copied apart for every use, and
a pattern meets a row when the whole system of equations of the branch stays
unifiable.  A removal deletes every row the removed atom unifies with.

Here that evaluation is the source schedule of `NestedQueryEffects` over
unification levels (`unifyLevel`): each stored row is a space name with a term
of an arbitrary first-order signature, the query's patterns sit at activation
scope 0 and the row chosen for the `j`-th pattern at scope `j + 1`.  A level
accepts a row only when the pattern and the row meet (`unifyLevel_sound`), and
its verdict is PeTTa's sequential one: solving the patterns one after another
succeeds exactly when the level accepts (`unifyLevel_iff_solveLegs`).

**Static admission.**  The template of every change is checked once, before
the join, against the patterns after the first (`StaticAdmission`, decidable):

* an added or inserted template meets no later pattern reading its space;
* a removed template deletes no stored row of its space that a later pattern
  meets (over ground rows: the removed template meets no later pattern,
  `staticRemoval_of_ground`);
* an added and a removed template of one space do not meet;
* no space receives both bag additions and set insertions.

Then every change the join makes keeps every later read and every two changes
commute (`admissible_of_static`), so the native run (join against the
snapshot, then every removal, then every addition) answers what PeTTa
answers and leaves the same spaces (`petta_native_eq_source`).  A template
may write what the first pattern reads.  A space named by a variable, a
computed level, or any other template outside the static check is decided by
the dynamic check of `NestedQueryEffects.nativeRun` on the actual instances
and reads (`petta_nativeRun_sound`).

**Answers.**  Every order of the legs computes, for each joined choice, a
most general unifier whose instance of the template is an instance of
PeTTa's, and equal to it when either is ground
(`answer_order_instances`, `answer_order_ground`).

MeTTa atoms are terms of one such signature (`mettaSignature`, `encode`).
Controls: a template meeting a later pattern is rejected
(`template_meets_later_pattern`), a level loop passes (`level_loop_apart`),
and a removal template meeting no later pattern can still delete an open row
a later pattern reads (`open_row_defeats_pattern_test`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.NativeQueryRegions

open Mettapedia.Logic.LP
open Mettapedia.Logic.LP.ConjunctiveUnification
open Mettapedia.Machines.NestedQuerySchedule
open Mettapedia.Machines.NestedQueryEffects

universe w
variable {σ : LPSignature} [DecidableEq σ.vars] [DecidableEq σ.constants]
  [DecidableEq σ.functionSymbols]
variable {Name : Type w} [DecidableEq Name]

/-- A stored row: the space it lives in, and its term. -/
abbrev Row (Name : Type w) (σ : LPSignature) := Name × Term σ

/-! ## Unification levels -/

/-- The equations of the chosen rows: the `j`-th pattern at scope 0 against
the `j`-th chosen row at scope `j + 1`. -/
def systemOf (pattern : ℕ → Term σ) : List (Row Name σ) → ℕ → Equations σ.scoped
  | [], _ => []
  | row :: rows, j =>
      ((pattern j).atScope 0, row.2.atScope (j + 1)) :: systemOf pattern rows (j + 1)

/-- Leg `i`: a row of the space the leg reads, whose term keeps the branch's
system unifiable. -/
def unifyLevel (pattern : ℕ → Term σ) (space : ℕ → List (Row Name σ) → Name) (i : ℕ) :
    Level (Row Name σ) :=
  fun chosen row => decide (row.1 = space i chosen) &&
    decide (Unifiable (((pattern i).atScope 0, row.2.atScope (chosen.length + 1)) ::
      systemOf pattern chosen 0))

/-- **A level accepts a row only when its pattern meets the row's term.** -/
theorem unifyLevel_sound {pattern : ℕ → Term σ} {space : ℕ → List (Row Name σ) → Name}
    {i : ℕ}
    {chosen : List (Row Name σ)} {row : Row Name σ}
    (h : unifyLevel pattern space i chosen row = true) :
    row.1 = space i chosen ∧ CommonInstance (pattern i) row.2 := by
  simp only [unifyLevel, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hspace, δ, hδ⟩ := h
  exact ⟨hspace, commonInstance_of_atScope (hδ _ List.mem_cons_self)⟩

/-- **A level's verdict is PeTTa's sequential one**: solving the chosen rows'
equations one leg at a time, then the new row's, succeeds exactly when the
level accepts the row in the space it reads. -/
theorem unifyLevel_iff_solveLegs (pattern : ℕ → Term σ)
    (space : ℕ → List (Row Name σ) → Name) (i : ℕ) (chosen : List (Row Name σ))
    (row : Row Name σ) :
    unifyLevel pattern space i chosen row = true ↔
      row.1 = space i chosen ∧
        (solveLegs (Subst.id σ.scoped) ((systemOf pattern chosen 0).map (fun e => [e]) ++
          [[((pattern i).atScope 0, row.2.atScope (chosen.length + 1))]])).isSome = true := by
  simp only [unifyLevel, Bool.and_eq_true, decide_eq_true_eq, solveLegs_isSome_iff,
    List.flatten_append, List.flatten_singleton]
  have flat : ((systemOf pattern chosen 0).map (fun e => [e])).flatten =
      systemOf pattern chosen 0 := by
    induction systemOf pattern chosen 0 with
    | nil => rfl
    | cons e es ih => simp [List.flatten_cons, ih]
  rw [flat]
  have perm : (((pattern i).atScope 0, row.2.atScope (chosen.length + 1)) ::
      systemOf pattern chosen 0).Perm
      (systemOf pattern chosen 0 ++ [((pattern i).atScope 0, row.2.atScope (chosen.length + 1))]) :=
    (List.perm_append_singleton _ _).symm
  exact and_congr_right fun _ =>
    ⟨fun ⟨δ, hδ⟩ => ⟨δ, (unifies_perm perm).mp hδ⟩,
      fun ⟨δ, hδ⟩ => ⟨δ, (unifies_perm perm).mpr hδ⟩⟩

/-- The first leg, read once. -/
def firstLevel (pattern : ℕ → Term σ) (space : ℕ → Name) : Level (Row Name σ) :=
  unifyLevel pattern (fun i _ => space i) 0

/-- The legs after the first, read for every solution of the ones before. -/
def laterLevels (pattern : ℕ → Term σ) (space : ℕ → Name) (m : ℕ) :
    List (Level (Row Name σ)) :=
  (List.range m).map fun i => unifyLevel pattern (fun i _ => space i) (i + 1)

/-! ## Templates of changes -/

/-- The template of a change: what a template instance adds to, inserts into,
or removes from a named space. -/
inductive Template (Name : Type w) (σ : LPSignature) where
  | add (target : Name) (data : Term σ)
  | insert (target : Name) (data : Term σ)
  | remove (target : Name) (pattern : Term σ)

namespace Template

def target : Template Name σ → Name
  | .add target _ | .insert target _ | .remove target _ => target

/-- The data an addition or insertion makes rows of. -/
def added : Template Name σ → List (Term σ)
  | .add _ data | .insert _ data => [data]
  | .remove _ _ => []

/-- The pattern a removal deletes by. -/
def removed : Template Name σ → List (Term σ)
  | .remove _ pattern => [pattern]
  | _ => []

def isAdd : Template Name σ → Bool
  | .add _ _ => true
  | _ => false

def isInsert : Template Name σ → Bool
  | .insert _ _ => true
  | _ => false

/-- A change is an instance of the template. -/
def Covers : Template Name σ → Effect (Row Name σ) → Prop
  | .add target data, .add row => row.1 = target ∧ ∃ θ : Subst σ, θ.applyTerm data = row.2
  | .insert target data, .insert row =>
      row.1 = target ∧ ∃ θ : Subst σ, θ.applyTerm data = row.2
  | .remove target pattern, .remove row =>
      row.1 = target ∧ ∃ θ : Subst σ, θ.applyTerm pattern = row.2
  | _, _ => False

end Template

/-- PeTTa's removal: same space, and the removed atom meets the row. -/
def unifyingRemoval (removed row : Row Name σ) : Bool :=
  decide (removed.1 = row.1) && decide (CommonInstance removed.2 row.2)

/-- **The static admission check**: finitely many meeting tests between
templates, the patterns after the first, and the initial rows. -/
def StaticAdmission (templates : List (Template Name σ)) (pattern : ℕ → Term σ)
    (space : ℕ → Name) (m : ℕ) (initial : List (Row Name σ)) : Prop :=
  (∀ t ∈ templates, ∀ data ∈ t.added, ∀ i ∈ List.range m,
      space (i + 1) = t.target → ¬ CommonInstance (pattern (i + 1)) data) ∧
    (∀ t ∈ templates, ∀ removed ∈ t.removed, ∀ i ∈ List.range m,
      space (i + 1) = t.target → ∀ u ∈ initial, u.1 = t.target →
        ¬ (CommonInstance removed u.2 ∧ CommonInstance (pattern (i + 1)) u.2)) ∧
    (∀ t ∈ templates, ∀ t' ∈ templates, ∀ data ∈ t.added, ∀ removed ∈ t'.removed,
      t.target = t'.target → ¬ CommonInstance data removed) ∧
    (∀ t ∈ templates, ∀ t' ∈ templates, t.isAdd = true → t'.isInsert = true →
      t.target ≠ t'.target)

instance (templates : List (Template Name σ)) (pattern : ℕ → Term σ) (space : ℕ → Name)
    (m : ℕ) (initial : List (Row Name σ)) :
    Decidable (StaticAdmission templates pattern space m initial) := by
  unfold StaticAdmission
  infer_instance

omit [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] in
/-- Over ground rows the removal test is between templates and patterns:
a removed template that meets no later pattern of its space passes. -/
theorem staticRemoval_of_ground {removed p u : Term σ} (ground : u.isGround)
    (apart : ¬ CommonInstance removed p) :
    ¬ (CommonInstance removed u ∧ CommonInstance p u) :=
  fun ⟨hr, hp⟩ => apart (hr.of_ground_row ground hp)

section Admission

variable (templates : List (Template Name σ)) (pattern : ℕ → Term σ) (space : ℕ → Name)
  (m : ℕ) (initial : List (Row Name σ))

theorem laterLevel_of_mem {level : Level (Row Name σ)}
    (h : level ∈ laterLevels pattern space m) :
    ∃ i ∈ List.range m, level = unifyLevel pattern (fun i _ => space i) (i + 1) := by
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp h
  exact ⟨i, hi, rfl⟩

/-- A row whose term meets no later pattern of its space is read by no later
read. -/
theorem unread_of_apart {events : List (Level (Row Name σ) × List (Row Name σ))}
    (later : ∀ e ∈ events, e.1 ∈ laterLevels pattern space m) {row : Row Name σ}
    (apart : ∀ i ∈ List.range m, space (i + 1) = row.1 →
      ¬ CommonInstance (pattern (i + 1)) row.2) :
    Unread events row := by
  intro e he
  obtain ⟨i, hi, hlevel⟩ := laterLevel_of_mem pattern space m (later e he)
  cases accepted : e.1 e.2 row
  · rfl
  · rw [hlevel] at accepted
    obtain ⟨hspace, meets⟩ := unifyLevel_sound accepted
    exact absurd meets (apart i hi hspace.symm)

/-- **The static check passes the dynamic one**: every change of the join
keeps every later read, and every two changes commute. -/
theorem admissible_of_static (static : StaticAdmission templates pattern space m initial)
    (effects : List (Row Name σ) → List (Effect (Row Name σ)))
    (covers : ∀ c ∈ join initial (firstLevel pattern space :: laterLevels pattern space m) [],
      ∀ e ∈ effects c, ∃ t ∈ templates, t.Covers e) :
    Admissible unifyingRemoval effects (firstLevel pattern space) (laterLevels pattern space m)
      initial := by
  obtain ⟨additions, removals, disjoint, discipline⟩ := static
  have later :
      ∀ e ∈ innerReads initial (firstLevel pattern space) (laterLevels pattern space m),
      e.1 ∈ laterLevels pattern space m := fun _ he => innerReads_level_mem he
  have addedApart : ∀ t ∈ templates, ∀ data ∈ t.added, ∀ (row : Row Name σ),
      row.1 = t.target → (∃ θ : Subst σ, θ.applyTerm data = row.2) →
      ∀ i ∈ List.range m, space (i + 1) = row.1 →
        ¬ CommonInstance (pattern (i + 1)) row.2 := by
    rintro t ht data hdata row htarget ⟨θ, hθ⟩ i hi hspace meets
    rw [← hθ] at meets
    exact additions t ht data hdata i hi (hspace.trans htarget)
      (CommonInstance.of_instance_right θ meets)
  refine ⟨fun c hc e he => ?_, fun e he e' he' => ?_⟩
  · obtain ⟨t, ht, cover⟩ := covers c hc e he
    cases e with
    | add row =>
        cases t with
        | add target data =>
            exact unread_of_apart pattern space m later
              (addedApart _ ht data List.mem_cons_self row cover.1 cover.2)
        | insert _ _ => exact cover.elim
        | remove _ _ => exact cover.elim
    | insert row =>
        cases t with
        | insert target data =>
            exact unread_of_apart pattern space m later
              (addedApart _ ht data List.mem_cons_self row cover.1 cover.2)
        | add _ _ => exact cover.elim
        | remove _ _ => exact cover.elim
    | remove row =>
        cases t with
        | remove target removed =>
            obtain ⟨htarget, θ, hθ⟩ := cover
            intro u hu deleted
            simp only [unifyingRemoval, Bool.and_eq_true, decide_eq_true_eq] at deleted
            obtain ⟨hsame, meetsRow⟩ := deleted
            rw [← hθ] at meetsRow
            have meetsTemplate := CommonInstance.of_instance_left θ meetsRow
            apply unread_of_apart pattern space m later
            intro i hi hspace meetsPattern
            exact removals _ ht removed List.mem_cons_self i hi
              (hspace.trans (hsame.symm.trans htarget)) u hu (hsame.symm.trans htarget)
              ⟨meetsTemplate, meetsPattern⟩
        | add _ _ => exact cover.elim
        | insert _ _ => exact cover.elim
  · obtain ⟨c, hc, he⟩ := List.mem_flatMap.mp he
    obtain ⟨c', hc', he'⟩ := List.mem_flatMap.mp he'
    obtain ⟨t, ht, cover⟩ := covers c hc e he
    obtain ⟨t', ht', cover'⟩ := covers c' hc' e' he'
    -- A removal and an addition or insertion of one space do not meet.
    have apart : ∀ (tAdd tRem : Template Name σ), tAdd ∈ templates → tRem ∈ templates →
        ∀ data ∈ tAdd.added, ∀ removed ∈ tRem.removed, ∀ (r s : Row Name σ),
        r.1 = tAdd.target → s.1 = tRem.target →
        (∃ θ : Subst σ, θ.applyTerm data = r.2) →
        (∃ θ : Subst σ, θ.applyTerm removed = s.2) →
        unifyingRemoval s r = false := by
      rintro tAdd tRem hAdd hRem data hdata removed hremoved r s hr hs ⟨θ, hθ⟩ ⟨θ', hθ'⟩
      cases result : unifyingRemoval s r
      · rfl
      · simp only [unifyingRemoval, Bool.and_eq_true, decide_eq_true_eq] at result
        obtain ⟨hsame, meets⟩ := result
        rw [← hθ, ← hθ'] at meets
        exact absurd (CommonInstance.of_instances θ' θ meets).symm
          (disjoint tAdd hAdd tRem hRem data hdata removed hremoved
            (hr.symm.trans (hsame.symm.trans hs)))
    cases e with
    | add r =>
        cases t with
        | add target data =>
            cases e' with
            | add _ => trivial
            | insert r' =>
                cases t' with
                | insert target' data' =>
                    show r ≠ r'
                    intro same
                    exact discipline _ ht _ ht' rfl rfl
                      (cover.1.symm.trans (same ▸ cover'.1))
                | add _ _ => exact cover'.elim
                | remove _ _ => exact cover'.elim
            | remove s =>
                cases t' with
                | remove target' removed =>
                    exact apart _ _ ht ht' data List.mem_cons_self removed List.mem_cons_self
                      r s cover.1 cover'.1 cover.2 cover'.2
                | add _ _ => exact cover'.elim
                | insert _ _ => exact cover'.elim
        | insert _ _ => exact cover.elim
        | remove _ _ => exact cover.elim
    | insert r =>
        cases t with
        | insert target data =>
            cases e' with
            | add r' =>
                cases t' with
                | add target' data' =>
                    show r ≠ r'
                    intro same
                    exact discipline _ ht' _ ht rfl rfl
                      (cover'.1.symm.trans (same ▸ cover.1))
                | insert _ _ => exact cover'.elim
                | remove _ _ => exact cover'.elim
            | insert _ => trivial
            | remove s =>
                cases t' with
                | remove target' removed =>
                    exact apart _ _ ht ht' data List.mem_cons_self removed List.mem_cons_self
                      r s cover.1 cover'.1 cover.2 cover'.2
                | add _ _ => exact cover'.elim
                | insert _ _ => exact cover'.elim
        | add _ _ => exact cover.elim
        | remove _ _ => exact cover.elim
    | remove s =>
        cases t with
        | remove target removed =>
            cases e' with
            | add r =>
                cases t' with
                | add target' data =>
                    exact apart _ _ ht' ht data List.mem_cons_self removed List.mem_cons_self
                      r s cover'.1 cover.1 cover'.2 cover.2
                | insert _ _ => exact cover'.elim
                | remove _ _ => exact cover'.elim
            | insert r =>
                cases t' with
                | insert target' data =>
                    exact apart _ _ ht' ht data List.mem_cons_self removed List.mem_cons_self
                      r s cover'.1 cover.1 cover'.2 cover.2
                | add _ _ => exact cover'.elim
                | remove _ _ => exact cover'.elim
            | remove _ => trivial
        | add _ _ => exact cover.elim
        | insert _ _ => exact cover.elim

/-- **PeTTa's nested match, answered by one join.**  Under the static check,
making the join's changes in any order (`native`, for example every removal
first) leaves PeTTa's final spaces as a bag, and any enumeration of the join
(`enumeration`) answers PeTTa's answers as a bag. -/
theorem petta_native_eq_source {Answer : Type*} [DecidableEq (Term σ)]
    (static : StaticAdmission templates pattern space m initial)
    (effects : List (Row Name σ) → List (Effect (Row Name σ)))
    (answers : List (Row Name σ) → List Answer)
    (covers : ∀ c ∈ join initial (firstLevel pattern space :: laterLevels pattern space m) [],
      ∀ e ∈ effects c, ∃ t ∈ templates, t.Covers e)
    (native : List (Effect (Row Name σ)))
    (perm : native.Perm (changes effects (firstLevel pattern space) (laterLevels pattern space m)
      initial))
    (enumeration : List (List (Row Name σ)))
    (permChoices : enumeration.Perm
      (join initial (firstLevel pattern space :: laterLevels pattern space m) [])) :
    ((native.foldl (fun s e => e.apply unifyingRemoval s) initial : List (Row Name σ)) :
        Multiset (Row Name σ)) =
        ((source id (effectBody unifyingRemoval effects answers)
          (firstLevel pattern space :: laterLevels pattern space m) [] initial).1 :
          Multiset (Row Name σ)) ∧
      (enumeration.flatMap answers).Perm
        (source id (effectBody unifyingRemoval effects answers)
          (firstLevel pattern space :: laterLevels pattern space m) [] initial).2 :=
  native_eq_source unifyingRemoval effects answers _ _ initial
    (admissible_of_static templates pattern space m initial static effects covers)
    native perm enumeration permChoices

end Admission

/-- **Spaces named by variables, decided on the actual reads.**  For any
resolution of each leg's space from the rows chosen before it, a native run
whose dynamic check passes answers what PeTTa answers and leaves its final
spaces as a bag. -/
theorem petta_nativeRun_sound {Answer : Type*} [DecidableEq (Term σ)]
    (pattern : ℕ → Term σ) (space : ℕ → List (Row Name σ) → Name) (m : ℕ)
    (initial : List (Row Name σ)) (effects : List (Row Name σ) → List (Effect (Row Name σ)))
    (answers : List (Row Name σ) → List Answer) {store : List (Row Name σ)}
    {answered : List Answer}
    (h : nativeRun unifyingRemoval effects answers (unifyLevel pattern space 0)
      ((List.range m).map fun i => unifyLevel pattern space (i + 1)) initial =
        some (store, answered)) :
    (store : Multiset (Row Name σ)) =
        ((source id (effectBody unifyingRemoval effects answers)
          (unifyLevel pattern space 0 ::
            (List.range m).map fun i => unifyLevel pattern space (i + 1))
          [] initial).1 : Multiset (Row Name σ)) ∧
      answered = (source id (effectBody unifyingRemoval effects answers)
        (unifyLevel pattern space 0 ::
          (List.range m).map fun i => unifyLevel pattern space (i + 1))
        [] initial).2 :=
  nativeRun_sound unifyingRemoval effects answers _ _ initial h

/-! ## Answers in any leg order -/

/-- **Any leg order instantiates a template to an instance of PeTTa's**, and
back: the native answer is PeTTa's up to the names of its variables. -/
theorem answer_order_instances {legs legs' : List (Equations σ.scoped)} (perm : legs.Perm legs')
    {θ θ' : Subst σ.scoped} (source : solveLegs (Subst.id σ.scoped) legs = some θ)
    (native : solveLegs (Subst.id σ.scoped) legs' = some θ') (template : Term σ) :
    (∃ ρ : Subst σ.scoped, θ'.applyTerm (template.atScope 0) =
        ρ.applyTerm (θ.applyTerm (template.atScope 0))) ∧
      ∃ ρ : Subst σ.scoped, θ.applyTerm (template.atScope 0) =
        ρ.applyTerm (θ'.applyTerm (template.atScope 0)) :=
  solveLegs_perm_instances perm source native _

/-- **A ground answer is the same in every leg order.** -/
theorem answer_order_ground {legs legs' : List (Equations σ.scoped)} (perm : legs.Perm legs')
    {θ θ' : Subst σ.scoped} (source : solveLegs (Subst.id σ.scoped) legs = some θ)
    (native : solveLegs (Subst.id σ.scoped) legs' = some θ') {template : Term σ}
    (ground : (θ.applyTerm (template.atScope 0)).isGround) :
    θ'.applyTerm (template.atScope 0) = θ.applyTerm (template.atScope 0) :=
  solveLegs_perm_ground perm source native ground

/-! ## MeTTa atoms as terms -/

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)

/-- The leaves of a MeTTa atom. -/
inductive Leaf where
  | symbol (name : String)
  | grounded (value : GroundedValue)
  deriving DecidableEq

/-- MeTTa atoms as first-order terms: an expression of `n` elements is the
`n`-ary tuple of its elements. -/
abbrev mettaSignature : LPSignature where
  constants := Leaf
  vars := String
  relationSymbols := Empty
  relationArity := fun e => e.elim
  functionSymbols := ℕ
  functionArity := fun n => n

/-- A MeTTa atom as a term. -/
def encode : Atom → Term mettaSignature
  | .symbol name => .const (.symbol name)
  | .var name => .var name
  | .grounded value => .const (.grounded value)
  | .expression elements => .app elements.length fun i => encode (elements.get i)
termination_by atom => sizeOf atom
decreasing_by
  have := List.sizeOf_get elements i
  simp only [Atom.expression.sizeOf_spec]
  omega

theorem encode_expression (elements : List Atom) :
    encode (.expression elements) = .app elements.length fun i => encode (elements.get i) := by
  rw [encode]

/-- `$x` taken to 2. -/
def xToTwo : Subst mettaSignature :=
  fun v => if v = "x" then .const (.grounded (.int 2)) else .var v

/-- **A template that meets a later pattern**: `(add-atom S (q 2 $y))` against
the later pattern `(q $x $y)`; the static check rejects it. -/
theorem template_meets_later_pattern :
    CommonInstance (encode (.expression [.symbol "q", .grounded (.int 2), .var "y"]))
      (encode (.expression [.symbol "q", .var "x", .var "y"])) := by
  refine ⟨Subst.id mettaSignature, xToTwo, ?_⟩
  rw [encode_expression, encode_expression, Subst.applyTerm_app, Subst.applyTerm_app]
  congr 1
  funext i
  fin_cases i <;> simp [encode, xToTwo]
  rfl

/-- **A level loop passes**: `(add-atom S (val 3 $w $v))` meets no later
pattern `(val 2 $w $v)`, whatever the bindings. -/
theorem level_loop_apart :
    ¬ CommonInstance (encode (.expression [.symbol "val", .grounded (.int 3), .var "w", .var "v"]))
      (encode (.expression [.symbol "val", .grounded (.int 2), .var "w", .var "v"])) := by
  rintro ⟨δ₁, δ₂, h⟩
  rw [encode_expression, encode_expression] at h
  simp only [Subst.applyTerm_app, List.length_cons, List.length_nil] at h
  have second := congrFun (eq_of_heq (Term.app.inj h).2) ⟨1, by decide⟩
  simp [encode] at second

/-- `$z` taken to `n`. -/
def zTo (n : ℤ) : Subst mettaSignature :=
  fun v => if v = "z" then .const (.grounded (.int n)) else .var v

/-- `(q n)` for an integer `n`. -/
def qOf (n : ℤ) : Atom := .expression [.symbol "q", .grounded (.int n)]

theorem qOf_meets_open_row (n : ℤ) :
    CommonInstance (encode (qOf n)) (encode (.expression [.symbol "q", .var "z"])) := by
  refine ⟨Subst.id mettaSignature, zTo n, ?_⟩
  rw [qOf, encode_expression, encode_expression, Subst.applyTerm_app, Subst.applyTerm_app]
  congr 1
  funext i
  fin_cases i <;> simp [encode, zTo]

/-- **Testing removal templates against patterns alone is not enough**: the
removed `(q 7)` meets no later pattern `(q 5)`, yet both meet the stored row
`(q $z)`, which PeTTa's removal deletes and the later pattern reads.  The
removal test of `StaticAdmission` asks about the stored rows of the space. -/
theorem open_row_defeats_pattern_test :
    ¬ CommonInstance (encode (qOf 7)) (encode (qOf 5)) ∧
      CommonInstance (encode (qOf 7)) (encode (.expression [.symbol "q", .var "z"])) ∧
      CommonInstance (encode (qOf 5)) (encode (.expression [.symbol "q", .var "z"])) := by
  refine ⟨?_, qOf_meets_open_row 7, qOf_meets_open_row 5⟩
  rintro ⟨δ₁, δ₂, h⟩
  rw [qOf, qOf, encode_expression, encode_expression] at h
  simp only [Subst.applyTerm_app, List.length_cons, List.length_nil] at h
  have second := congrFun (eq_of_heq (Term.app.inj h).2) ⟨1, by decide⟩
  simp [encode] at second

end Mettapedia.Languages.MeTTa.PeTTa.NativeQueryRegions
