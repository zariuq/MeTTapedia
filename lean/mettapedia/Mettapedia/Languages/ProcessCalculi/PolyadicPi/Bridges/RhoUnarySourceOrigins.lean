import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryAdministrativeProgress
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveSyntaxMarking
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveOriginErasure

/-!
# Occurrence markings of the concrete unary runtime source

Each retained activity has its actual list index as origin. Equal messages
and receivers remain separate occurrences; a persistent server's copied
receiver keeps the same original index. Input continuations remain suspended.
The marking fits the actual source syntax and its guarded replicated bodies
satisfy the common structural-erasure condition.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnarySourceOrigins

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open RhoUnaryCompiler RhoUnaryActive RhoUnaryAdministrativeProgress
open ActiveMarking ActiveOriginErasure

def mark {Γ : Ctx sig} : Nat → List (Activity Γ) → ActiveMarking.Tree Nat
  | _, [] => .nil
  | start, activity :: rest =>
      .par (ActiveSyntaxMarking.mark start activity.source) (mark (start + 1) rest)

def one (index : Nat) : Nat → Bool := fun origin => decide (origin = index)

theorem fitted {Γ : Ctx sig} (start : Nat) (activities : List (Activity Γ)) :
    Fits (mark start activities) (source activities) := by
  induction activities generalizing start with
  | nil => exact .nil
  | cons activity rest ih =>
      exact .par (ActiveSyntaxMarking.mark_fits start activity.source) (ih (start + 1))

theorem mark_origin_false (selected : Nat → Bool) (origin : Nat) (unselected : selected origin = false) :
    ∀ {Γ : Ctx sig} (process : Proc Γ),
      originCount selected (ActiveSyntaxMarking.mark origin process) = 0
  | _, .var _ => by simp only [ActiveSyntaxMarking.mark, originCount]
  | _, .op .nil .nil => by simp only [ActiveSyntaxMarking.mark, originCount]
  | _, .op .par (.cons first (.cons second .nil)) => by
      simp only [ActiveSyntaxMarking.mark, originCount]
      rw [mark_origin_false selected origin unselected first,
        mark_origin_false selected origin unselected second]
  | _, .op .inp1 (.cons _ (.cons _ .nil)) => by
      simp only [ActiveSyntaxMarking.mark, originCount, unselected, Bool.false_eq_true, ↓reduceIte]
  | _, .op .inp2 (.cons _ (.cons _ .nil)) => by
      simp only [ActiveSyntaxMarking.mark, originCount, unselected, Bool.false_eq_true, ↓reduceIte]
  | _, .op .out1 (.cons _ (.cons _ .nil)) => by
      simp only [ActiveSyntaxMarking.mark, originCount, unselected, Bool.false_eq_true, ↓reduceIte]
  | _, .op .out2 (.cons _ (.cons _ (.cons _ .nil))) => by
      simp only [ActiveSyntaxMarking.mark, originCount, unselected, Bool.false_eq_true, ↓reduceIte]
  | _, .op .nu (.cons body .nil) => by
      simpa only [ActiveSyntaxMarking.mark, originCount] using mark_origin_false selected origin unselected body
  | _, .op .rep (.cons body .nil) => by
      simpa only [ActiveSyntaxMarking.mark, originCount] using mark_origin_false selected origin unselected body
termination_by _ process => termSize process
decreasing_by all_goals simp only [termSize, argsSize]; omega

theorem lower_bound_zero {Γ : Ctx sig} (activities : List (Activity Γ))
    {index start : Nat} (earlier : index < start) :
    originCount (one index) (mark start activities) = 0 := by
  induction activities generalizing start with
  | nil => rfl
  | cons activity rest ih =>
      simp only [mark, originCount]
      have unequal : one index start = false := by simp [one]; omega
      rw [mark_origin_false (one index) start unequal activity.source, ih (by omega)]

theorem stable_activity_count {Γ : Ctx sig} (selected : Nat → Bool) (origin : Nat)
    (activity : Activity Γ) (stable : Stable activity) :
    originCount selected (ActiveSyntaxMarking.mark origin activity.source) ≤ 1 := by
  cases activity <;> simp_all only [Stable, Activity.source, inp1, out1, rep, nil,
    ActiveSyntaxMarking.mark, originCount]
  all_goals first | omega | split <;> omega

theorem count_unique {Γ : Ctx sig} (activities : List (Activity Γ))
    (stable : ∀ activity ∈ activities, Stable activity) (start index : Nat) :
    originCount (one index) (mark start activities) ≤ 1 := by
  induction activities generalizing start with
  | nil => simp only [mark, originCount]; omega
  | cons activity rest ih =>
      have tailStable : ∀ activity ∈ rest, Stable activity :=
        fun chosen member => stable chosen (List.mem_cons_of_mem _ member)
      simp only [mark, originCount]
      by_cases same : start = index
      · subst index
        rw [lower_bound_zero rest (by omega)]
        exact stable_activity_count (one start) start activity (stable activity List.mem_cons_self)
      · have unequal : one index start = false := by simp [one, same]
        rw [mark_origin_false (one index) start unequal activity.source, Nat.zero_add]
        exact ih tailStable (start + 1)

theorem guarded_singleBodies {Γ : Ctx sig} {process : Proc Γ}
    (guarded : GuardedUnary process) : SingleBodies process := by
  induction guarded with
  | nil => simp only [nil, SingleBodies]
  | par _ _ firstIH secondIH => simpa only [par, SingleBodies] using And.intro firstIH secondIH
  | inp1 => simp only [inp1, SingleBodies]
  | out1 => simp only [out1, SingleBodies]
  | nu _ ih => simpa only [nu, SingleBodies] using ih
  | server => simp only [rep, inp1, SingleBodies, NoActiveRep, width, and_self]

theorem source_singleBodies {Γ : Ctx sig} (activities : List (Activity Γ)) :
    SingleBodies (source activities) := by
  induction activities with
  | nil => simp only [source, List.map_nil, ScopedActiveFrontier.parallel, nil, SingleBodies]
  | cons activity rest ih =>
      simp only [source, List.map_cons, ScopedActiveFrontier.parallel, par, SingleBodies]
      exact ⟨guarded_singleBodies activity.source_guarded, ih⟩

/-- A selected ordinary activity is outside every active replicated body. -/
theorem mark_repFree_noActiveRep (selected : Nat → Bool) (origin : Nat) :
    ∀ {Γ : Ctx sig} (process : Proc Γ), NoActiveRep process →
      RepFree selected (ActiveSyntaxMarking.mark origin process)
  | _, .var _, _ => by simp only [ActiveSyntaxMarking.mark, RepFree]
  | _, .op .nil .nil, _ => by simp only [ActiveSyntaxMarking.mark, RepFree]
  | _, .op .par (.cons first (.cons second .nil)), safe => by
      simp only [NoActiveRep] at safe
      simp only [ActiveSyntaxMarking.mark, RepFree]
      exact ⟨mark_repFree_noActiveRep selected origin first safe.1,
        mark_repFree_noActiveRep selected origin second safe.2⟩
  | _, .op .inp1 (.cons _ (.cons _ .nil)), _ => by simp only [ActiveSyntaxMarking.mark, RepFree]
  | _, .op .inp2 (.cons _ (.cons _ .nil)), _ => by simp only [ActiveSyntaxMarking.mark, RepFree]
  | _, .op .out1 (.cons _ (.cons _ .nil)), _ => by simp only [ActiveSyntaxMarking.mark, RepFree]
  | _, .op .out2 (.cons _ (.cons _ (.cons _ .nil))), _ => by simp only [ActiveSyntaxMarking.mark, RepFree]
  | _, .op .nu (.cons body .nil), safe => by
      simp only [NoActiveRep] at safe
      simpa only [ActiveSyntaxMarking.mark, RepFree] using mark_repFree_noActiveRep selected origin body safe
  | _, .op .rep (.cons _ .nil), impossible => by simp only [NoActiveRep] at impossible
termination_by _ process _ => termSize process
decreasing_by all_goals simp only [termSize, argsSize]; omega

/-- Index ownership identifies the selected ordinary occurrence even when
another activity has an identical channel, body or emitted datum. -/
theorem repFree_at {Γ : Ctx sig} (activities : List (Activity Γ))
    {index : Nat} {activity : Activity Γ} (selected : activities[index]? = some activity)
    (ordinary : NoActiveRep activity.source) (start : Nat) :
    RepFree (one (start + index)) (mark start activities) := by
  induction activities generalizing index start with
  | nil => simp at selected
  | cons first rest ih =>
      cases index with
      | zero =>
          have same : first = activity := Option.some.inj selected
          subst first
          refine ⟨mark_repFree_noActiveRep _ _ activity.source ordinary, ?_⟩
          apply repFree_of_zero
          exact lower_bound_zero rest (by omega)
      | succ index =>
          have later : rest[index]? = some activity := selected
          refine ⟨?_, ?_⟩
          · apply repFree_of_zero
            apply mark_origin_false
            simp only [one, decide_eq_false_iff_not]
            omega
          · simpa only [Nat.add_assoc, Nat.add_comm 1 index] using ih later (start + 1)

def pair (input output : Nat) : Nat → Bool :=
  fun origin => decide (origin = input ∨ origin = output)

theorem pair_count (input output : Nat) (different : input ≠ output)
    (marked : ActiveMarking.Tree Nat) :
    originCount (pair input output) marked =
      originCount (one input) marked + originCount (one output) marked := by
  induction marked with
  | var | nil => rfl
  | par left right leftIH rightIH => simp only [originCount, leftIH, rightIH]; omega
  | inp1 origin | inp2 origin | out1 origin | out2 origin =>
      simp only [originCount, pair, one]
      by_cases first : origin = input
      · subst origin
        simp [different]
      · by_cases second : origin = output <;> simp [first, second, Ne.symm different]
  | nu _ _ ih | rep _ ih => exact ih

theorem repFree_pair (input output : Nat) (different : input ≠ output)
    (marked : ActiveMarking.Tree Nat) (first : RepFree (one input) marked)
    (second : RepFree (one output) marked) : RepFree (pair input output) marked := by
  induction marked with
  | var | nil | inp1 | inp2 | out1 | out2 => trivial
  | par left right leftIH rightIH => exact ⟨leftIH first.1 second.1, rightIH first.2 second.2⟩
  | nu _ _ ih => exact ih first second
  | rep body =>
      change originCount (pair input output) body = 0
      rw [pair_count input output different, first, second]

/-- Erasure acts on each original indexed occurrence without changing its
remaining activity or its original index. -/
def erasedEntry {Γ : Ctx sig} (selected : Nat → Bool) (entry : Activity Γ × Nat) : Proc Γ :=
  erase selected (ActiveSyntaxMarking.mark entry.2 entry.1.source) entry.1.source

theorem erase_entries {Γ : Ctx sig} (selected : Nat → Bool) (start : Nat)
    (activities : List (Activity Γ)) :
    erase selected (mark start activities) (source activities) =
      ScopedActiveFrontier.parallel ((activities.zipIdx start).map (erasedEntry selected)) := by
  induction activities generalizing start with
  | nil => simp only [source, mark, List.map_nil, List.zipIdx_nil,
      ScopedActiveFrontier.parallel, nil, erase]
  | cons first rest ih =>
      simp only [source, mark, List.map_cons, List.zipIdx_cons, ScopedActiveFrontier.parallel,
        par, erase, erasedEntry]
      have tail := ih (start + 1)
      simp only [source] at tail
      rw [tail]

/-- Distinct original indices give a genuine two-occurrence permutation and
an unchanged frame. The erased selected headers remain explicit so the same
receipt applies to ordinary inputs and persistent servers. -/
theorem pair_residual {Γ : Ctx sig} (activities : List (Activity Γ))
    (input output : Nat) (different : input ≠ output) (first second : Activity Γ)
    (firstAt : activities[input]? = some first) (secondAt : activities[output]? = some second) :
    ∃ frame : List (Activity Γ), activities.Perm (first :: second :: frame) ∧
      StructuralEq (erase (pair input output) (mark 0 activities) (source activities))
        (par (erasedEntry (pair input output) (first, input))
          (par (erasedEntry (pair input output) (second, output)) (source frame))) := by
  classical
  let entries := activities.zipIdx
  let rest := (entries.erase (first, input)).erase (second, output)
  have firstMember : (first, input) ∈ entries := List.mk_mem_zipIdx_iff_getElem?.mpr firstAt
  have secondMember : (second, output) ∈ entries := List.mk_mem_zipIdx_iff_getElem?.mpr secondAt
  have distinct : (second, output) ≠ (first, input) := by
    intro same
    exact different (congrArg Prod.snd same).symm
  have secondAfter : (second, output) ∈ entries.erase (first, input) :=
    (List.mem_erase_of_ne distinct).mpr secondMember
  have exposed : entries.Perm ((first, input) :: (second, output) :: rest) :=
    (List.perm_cons_erase firstMember).trans
      (List.Perm.cons _ (List.perm_cons_erase secondAfter))
  have indexed : entries.Nodup := by
    apply List.Nodup.of_map Prod.snd
    simp only [entries, List.zipIdx_map_snd]
    exact List.nodup_range'
  have restFree : ∀ entry ∈ rest, pair input output entry.2 = false := by
    intro entry member
    have middle : entry ∈ entries.erase (first, input) := List.mem_of_mem_erase member
    have original : entry ∈ entries := List.mem_of_mem_erase middle
    have notFirst : entry ≠ (first, input) := (indexed.mem_erase_iff.mp middle).1
    have notSecond : entry ≠ (second, output) := ((indexed.erase _).mem_erase_iff.mp member).1
    have actual : activities[entry.2]? = some entry.1 := List.mk_mem_zipIdx_iff_getElem?.mp original
    have notInput : entry.2 ≠ input := by
      intro same
      rw [same, firstAt] at actual
      apply notFirst
      exact Prod.ext (Option.some.inj actual).symm same
    have notOutput : entry.2 ≠ output := by
      intro same
      rw [same, secondAt] at actual
      apply notSecond
      exact Prod.ext (Option.some.inj actual).symm same
    simp only [pair, decide_eq_false_iff_not]
    exact not_or.mpr ⟨notInput, notOutput⟩
  have unchanged : rest.map (erasedEntry (pair input output)) = rest.map (fun entry => entry.1.source) := by
    apply List.map_congr_left
    intro entry member
    unfold erasedEntry
    exact erase_of_originCount_zero _ (ActiveSyntaxMarking.mark_fits _ _)
      (mark_origin_false _ _ (restFree entry member) _)
  refine ⟨rest.map Prod.fst, ?_, ?_⟩
  · simpa only [entries, List.zipIdx_map_fst, List.map_cons] using exposed.map Prod.fst
  · rw [erase_entries]
    have reordered := ScopedActiveFrontier.parallel_perm (exposed.map (erasedEntry (pair input output)))
    simpa only [entries, List.map_cons, unchanged, ScopedActiveFrontier.parallel,
      source, List.map_map, Function.comp_def] using reordered

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnarySourceOrigins
