import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.ContextualRecovery

/-!
# Contextual matching through the existing tree matcher

The ordinary tree matcher first obtains the subtree at each annotated
occurrence. A reconciliation pass recovers parameter bodies and enforces that
all occurrences of a schematic variable use the same assignment. No second
tree syntax or structural matching algorithm is introduced.

Soundness holds for every successful result. Completeness is stated for the
explicit distinct-variable input-spine profile. Output instantiation continues
to support repeated and compound arguments.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.ContextualPatterns

open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT.ScopedApplication
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources

variable {Head V : Type}

mutual
def occurrences : TreePat Head (Occurrence Head V) → List (Occurrence Head V)
  | .mvar occurrence => [occurrence]
  | .idx _ => []
  | .node _ fields => fieldOccurrences fields

def fieldOccurrences : TreePatFields Head (Occurrence Head V) → List (Occurrence Head V)
  | .nil => []
  | .cons _ pattern rest => occurrences pattern ++ fieldOccurrences rest
end

variable [DecidableEq Head] [DecidableEq V]

mutual
theorem mem_occurrences (p : TreePat Head (Occurrence Head V)) (o : Occurrence Head V) :
    o ∈ occurrences p ↔ o ∈ p.vars := by
  cases p with
  | mvar v => simp [occurrences, TreePat.vars]
  | idx n => simp [occurrences, TreePat.vars]
  | node h fs => exact mem_fieldOccurrences fs o

theorem mem_fieldOccurrences (fs : TreePatFields Head (Occurrence Head V))
    (o : Occurrence Head V) : o ∈ fieldOccurrences fs ↔ o ∈ fs.vars := by
  cases fs with
  | nil => simp [fieldOccurrences, TreePatFields.vars]
  | cons d p rest =>
    simp only [fieldOccurrences, List.mem_append, TreePatFields.vars, Finset.mem_union,
      mem_occurrences p o, mem_fieldOccurrences rest o]
end

/-- The algorithm's completeness profile, expressed on the existing occurrence metadata. -/
def Occurrence.Input (o : Occurrence Head V) : Prop :=
  ∃ indices : List Nat, o.arguments = indices.map Term.idx ∧
    o.arity = indices.length ∧ indices.Nodup

def Pattern.Input (p : Pattern Head V) : Prop :=
  ∀ o ∈ occurrences p.tree, o.Input

/-- The exact executable admission check for an inverse-matching occurrence. -/
def Occurrence.inputCheck (o : Occurrence Head V) : Bool :=
  match Recovery.indices? o.arguments with
  | none => false
  | some indices => decide (o.arity = indices.length ∧ indices.Nodup)

omit [DecidableEq Head] [DecidableEq V] in
theorem Occurrence.inputCheck_iff (o : Occurrence Head V) :
    o.inputCheck = true ↔ o.Input := by
  constructor
  · intro checked
    cases found : Recovery.indices? o.arguments with
    | none => simp [Occurrence.inputCheck, found] at checked
    | some indices =>
      have qualified : o.arity = indices.length ∧ indices.Nodup := by
        simpa [Occurrence.inputCheck, found] using checked
      exact ⟨indices, Recovery.indices?_sound _ _ found, qualified⟩
  · rintro ⟨indices, args, arity, distinct⟩
    simp [Occurrence.inputCheck, args, arity, Recovery.indices?_map, distinct]

def Pattern.inputCheck (p : Pattern Head V) : Bool :=
  (occurrences p.tree).all Occurrence.inputCheck

omit [DecidableEq Head] [DecidableEq V] in
theorem Pattern.inputCheck_iff (p : Pattern Head V) : p.inputCheck = true ↔ p.Input := by
  simp only [Pattern.inputCheck, List.all_eq_true, Occurrence.inputCheck_iff, Pattern.Input]

def solveOccurrence (o : Occurrence Head V) (target : Term Head)
    (σ : Subst V (Term Head)) : Option (Subst V (Term Head)) :=
  match σ o.name with
  | some body => if graft o.arity o.arguments body = some target then some σ else none
  | none => (Recovery.recover o.arity o.arguments target).map fun body =>
      Function.update σ o.name (some body)

theorem solveOccurrence_sound {o : Occurrence Head V} {target : Term Head}
    {σ τ : Subst V (Term Head)} (solved : solveOccurrence o target σ = some τ) :
    Extends σ τ ∧ (∀ v, v ≠ o.name → τ v = σ v) ∧
      Pattern.atOccurrence τ o = some target := by
  unfold solveOccurrence at solved
  cases assigned : σ o.name with
  | some body =>
    rw [assigned] at solved
    change (if graft o.arity o.arguments body = some target then some σ else none) = some τ at solved
    split at solved
    · rename_i applied
      cases solved
      exact ⟨Extends.refl _, fun _ _ => rfl, by simp [Pattern.atOccurrence, assigned, applied]⟩
    · cases solved
  | none =>
    rw [assigned] at solved
    change (Recovery.recover o.arity o.arguments target).map
      (fun body => Function.update σ o.name (some body)) = some τ at solved
    obtain ⟨body, recovered, rfl⟩ := Option.map_eq_some_iff.mp solved
    refine ⟨?_, ?_, ?_⟩
    · intro v t bound
      have different : v ≠ o.name := by
        intro same
        subst v
        rw [assigned] at bound
        cases bound
      simp [Function.update, different, bound]
    · intro v different
      simp [Function.update, different]
    · simp only [Pattern.atOccurrence, Function.update_self, Option.bind_some]
      exact Recovery.recover_sound recovered

omit [DecidableEq Head] [DecidableEq V] in
theorem atOccurrence_extends {σ τ : Subst V (Term Head)} {o : Occurrence Head V}
    {t : Term Head} (grow : Extends σ τ) (applied : Pattern.atOccurrence σ o = some t) :
    Pattern.atOccurrence τ o = some t := by
  have bound := Pattern.atOccurrence_bound (show (Pattern.atOccurrence σ o).isSome by rw [applied]; rfl)
  obtain ⟨body, assigned⟩ := Option.isSome_iff_exists.mp bound
  simpa [Pattern.atOccurrence, assigned, grow o.name body assigned] using applied

theorem solveOccurrence_complete {o : Occurrence Head V} (input : o.Input)
    {target : Term Head} {σ goal : Subst V (Term Head)} (grow : Extends σ goal)
    (applied : Pattern.atOccurrence goal o = some target) :
    ∃ τ, solveOccurrence o target σ = some τ ∧ Extends τ goal := by
  have bound := Pattern.atOccurrence_bound (show (Pattern.atOccurrence goal o).isSome by rw [applied]; rfl)
  obtain ⟨body, assigned⟩ := Option.isSome_iff_exists.mp bound
  have forward : graft o.arity o.arguments body = some target := by
    simpa [Pattern.atOccurrence, assigned] using applied
  cases prior : σ o.name with
  | some old =>
    have same : body = old := Option.some.inj (assigned.symm.trans (grow o.name old prior))
    subst old
    exact ⟨σ, by simp [solveOccurrence, prior, forward], grow⟩
  | none =>
    obtain ⟨indices, args, arity, distinct⟩ := input
    have recovered : Recovery.recover o.arity o.arguments target = some body := by
      rw [args, arity]
      exact Recovery.recover_complete distinct (by simpa [args, arity] using forward)
    refine ⟨Function.update σ o.name (some body), by simp [solveOccurrence, prior, recovered], ?_⟩
    intro v t member
    by_cases same : v = o.name
    · subst v
      have equal : body = t := by simpa using member
      simpa [equal] using assigned
    · apply grow v t
      simpa [Function.update, same] using member

def reconcile : List (Occurrence Head V) → Subst (Occurrence Head V) (Term Head) →
    Subst V (Term Head) → Option (Subst V (Term Head))
  | [], _, σ => some σ
  | o :: rest, targets, σ => do
      let target ← targets o
      let next ← solveOccurrence o target σ
      reconcile rest targets next

theorem reconcile_sound : ∀ (os : List (Occurrence Head V))
    (targets : Subst (Occurrence Head V) (Term Head)) (σ τ : Subst V (Term Head)),
    reconcile os targets σ = some τ →
      Extends σ τ ∧ (∀ v, (∀ o ∈ os, v ≠ o.name) → τ v = σ v) ∧
        ∀ o ∈ os, Pattern.atOccurrence τ o = targets o
  | [], _, σ, τ, ran => by
    have same : σ = τ := Option.some.inj ran
    subst τ
    exact ⟨Extends.refl _, fun _ _ => rfl, by simp⟩
  | o :: rest, targets, σ, τ, ran => by
    cases found : targets o with
    | none => simp [reconcile, found] at ran
    | some t =>
      cases solved : solveOccurrence o t σ with
      | none => simp [reconcile, found, solved] at ran
      | some next =>
        have tail : reconcile rest targets next = some τ := by
          simpa [reconcile, found, solved] using ran
        obtain ⟨grow, only, head⟩ := solveOccurrence_sound solved
        obtain ⟨more, tailOnly, tailValues⟩ := reconcile_sound rest targets next τ tail
        refine ⟨grow.trans more, ?_, ?_⟩
        · intro v absent
          exact (tailOnly v (fun p member => absent p (by simp [member]))).trans
            (only v (absent o (by simp)))
        · intro p member
          rcases List.mem_cons.mp member with rfl | member
          · exact (atOccurrence_extends more head).trans found.symm
          · exact tailValues p member

theorem reconcile_complete : ∀ (os : List (Occurrence Head V))
    (targets : Subst (Occurrence Head V) (Term Head)) (σ goal : Subst V (Term Head)),
    (∀ o ∈ os, o.Input) → Extends σ goal →
    (∀ o ∈ os, ∃ t, targets o = some t ∧ Pattern.atOccurrence goal o = some t) →
    ∃ τ, reconcile os targets σ = some τ ∧ Extends τ goal
  | [], _, σ, goal, _, grow, _ => ⟨σ, rfl, grow⟩
  | o :: rest, targets, σ, goal, inputs, grow, values => by
    obtain ⟨t, found, applied⟩ := values o (by simp)
    obtain ⟨next, solved, extendsGoal⟩ :=
      solveOccurrence_complete (inputs o (by simp)) grow applied
    obtain ⟨τ, tail, result⟩ := reconcile_complete rest targets next goal
      (fun p member => inputs p (by simp [member])) extendsGoal
      (fun p member => values p (by simp [member]))
    exact ⟨τ, by simp [reconcile, found, solved, tail], result⟩

/-- Reuse structural matching, then reconcile contextual occurrences. -/
def match? (p : Pattern Head V) (σ : Subst V (Term Head)) (target : Term Head) :
    Option (Subst V (Term Head)) :=
  if Term.supportedAt p.scope target then do
    let targets ← matchT p.tree (fun _ => none) target
    reconcile (occurrences p.tree) targets σ
  else none

theorem match_sound {p : Pattern Head V} {σ τ : Subst V (Term Head)} {target : Term Head}
    (matched : match? p σ target = some τ) : layer.Step σ p target τ := by
  unfold match? at matched
  split at matched
  · rename_i targetScoped
    cases found : matchT p.tree (fun _ => none) target with
    | none => simp [found] at matched
    | some targets =>
      have ran : reconcile (occurrences p.tree) targets σ = some τ := by simpa [found] using matched
      obtain ⟨_, _, raw⟩ := matchT_sound p.tree (fun _ => none) targets target found
      obtain ⟨grow, only, values⟩ := reconcile_sound _ _ _ _ ran
      refine ⟨grow, ?_, (solves_iff τ p target).mpr ((Pattern.inst_iff τ p target).mpr ⟨?_, targetScoped⟩)⟩
      · intro v outside
        apply only v
        intro o member same
        apply outside
        exact Finset.mem_image.mpr ⟨o, (mem_occurrences p.tree o).mp member, same.symm⟩
      · rw [← raw]
        exact TreePat.inst_local _ _ p.tree fun o member =>
          values o ((mem_occurrences p.tree o).mpr member)
  · cases matched

theorem match_complete {p : Pattern Head V} (input : p.Input)
    {σ goal : Subst V (Term Head)} {target : Term Head}
    (solution : layer.Step σ p target goal) : match? p σ target = some goal := by
  have applied := (solves_iff goal p target).mp solution.solves
  obtain ⟨raw, targetScoped⟩ := (Pattern.inst_iff goal p target).mp applied
  let targets : Subst (Occurrence Head V) (Term Head) :=
    fun o => if o ∈ p.tree.vars then Pattern.atOccurrence goal o else none
  have targetsAgree (o : Occurrence Head V) (member : o ∈ p.tree.vars) :
      targets o = Pattern.atOccurrence goal o := by simp [targets, member]
  have rawTargets : p.tree.inst targets = some target := by
    rw [← raw]
    exact TreePat.inst_local _ _ p.tree targetsAgree
  have found : matchT p.tree (fun _ => none) target = some targets :=
    matchT_complete p.tree _ targets target (by intro o t impossible; cases impossible)
      (by intro o outside; simp [targets, outside]) rawTargets
  obtain ⟨τ, reconciled, growsToGoal⟩ := reconcile_complete (occurrences p.tree) targets σ goal input
    solution.extends_ (by
      intro o member
      have occurs := (mem_occurrences p.tree o).mp member
      have bound := (TreePat.inst_isSome (Pattern.atOccurrence goal) p.tree).mp
        (by rw [raw]; rfl) o occurs
      obtain ⟨t, value⟩ := Option.isSome_iff_exists.mp bound
      exact ⟨t, (targetsAgree o occurs).trans value, value⟩)
  have matched : match? p σ target = some τ := by simp [match?, targetScoped, found, reconciled]
  have result := match_sound matched
  have same : τ = goal := by
    funext v
    by_cases member : v ∈ p.vars
    · have defined := Pattern.inst_bound τ p (by
        rw [(solves_iff τ p target).mp result.solves]; rfl) v member
      obtain ⟨t, value⟩ := Option.isSome_iff_exists.mp defined
      exact value.trans (growsToGoal v t value).symm
    · exact (result.only v member).trans (solution.only v member).symm
  simpa [same] using matched

/-- Exactness is stated on the input profile, while the common layer admits richer outputs. -/
theorem match_exact {p : Pattern Head V} (input : p.Input)
    (σ τ : Subst V (Term Head)) (target : Term Head) :
    match? p σ target = some τ ↔ layer.Step σ p target τ :=
  ⟨match_sound, match_complete input⟩

/-- The executable profile check supplies the hypotheses of matcher exactness. -/
theorem checked_match_exact {p : Pattern Head V} (checked : p.inputCheck = true)
    (σ τ : Subst V (Term Head)) (target : Term Head) :
    match? p σ target = some τ ↔ layer.Step σ p target τ :=
  match_exact ((Pattern.inputCheck_iff p).mp checked) σ τ target

theorem solution_unique {p : Pattern Head V} (input : p.Input)
    {σ first second : Subst V (Term Head)} {target : Term Head}
    (left : layer.Step σ p target first) (right : layer.Step σ p target second) : first = second :=
  Option.some.inj ((match_complete input left).symm.trans (match_complete input right))

def matcher : Matcher V (Term Head) (Pattern Head V) := fun p σ t => (match? p σ t).toList

theorem matcher_sound : Matcher.Sound (layer (Head := Head) (V := V)) matcher := by
  intro p σ t τ member
  apply match_sound
  simpa [matcher] using member

theorem matcher_minimal : Matcher.Minimal (layer (Head := Head) (V := V)) matcher := by
  intro p σ t
  cases match? p σ t <;> simp [matcher]

namespace MatcherControls

def pairPattern : Pattern Nat Nat := ⟨2,
  .node 2 (.cons 0 (.mvar ⟨0, 2, [.idx 0, .idx 1]⟩)
    (.cons 0 (.mvar ⟨0, 2, [.idx 1, .idx 0]⟩) .nil))⟩

def first : Subst Nat (Term Nat) := fun v => if v = 0 then some (.idx 0) else none

theorem two_orders_share_one_body :
    (match? pairPattern (fun _ => none) (Recovery.Controls.pair (.idx 0) (.idx 1))).map
      (fun assignment => assignment 0) = some (some (.idx 0)) := by decide

theorem inconsistent_repeated_hole_refused :
    match? pairPattern (fun _ => none) (Recovery.Controls.pair (.idx 0) (.idx 0)) = none := by decide

def binderPattern : Pattern Nat Nat := ⟨1,
  .node 1 (.cons 1 (.mvar ⟨0, 1, [.idx 1]⟩) .nil)⟩

theorem ambient_body_recovers_beneath_binder :
    (match? binderPattern (fun _ => none) (Recovery.Controls.lam (.idx 1))).map
      (fun assignment => assignment 0) = some (some (.idx 0)) := by decide

theorem undeclared_inner_binder_refused :
    match? binderPattern (fun _ => none) (Recovery.Controls.lam (.idx 0)) = none := by decide

end MatcherControls
end Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.ContextualPatterns
