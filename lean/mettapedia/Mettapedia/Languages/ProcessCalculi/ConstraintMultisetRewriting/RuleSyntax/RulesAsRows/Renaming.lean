import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RulesAsRows.Gating

/-!
# Renaming a rule's own unknowns: the step does not see the names, the code rows do

A firing opens a rule's own unknowns freshly, so the names of those unknowns are invisible to the step:

* **One firing for the other** (`forth`, `back`): for an injective renaming `π`, every admitted firing
  of a rule is matched by an admitted firing of the renamed rule (`rename π r`) with the same selection
  and the same result, and conversely. The opening of the renamed rule reads each renamed unknown as
  the original one.
* **The same steps** (`renamed_succ`): a program and the program with each rule renamed by an injective
  renaming of its own have the same successor relation, so the same runs.
* **Through the interpreter** (`renamed_codes_bisimulation`): the interpreter, from a store holding the
  codes of the renamed rules of a fixed program, is strongly bisimilar to the step of the original
  program. The two-step run of the example program goes through with the codes of renamed rules
  (`renamed_demo_interpreter_run`), although those code rows differ from the original ones
  (`renamed_code_ne`).

**Controls.**
* Injectivity is needed: identifying the two unknowns of a pair pattern gives a rule that is refused at
  a store where the original fires (`pair_fires`, `collapsed_refused`).
* Code rows are syntax: a rule that reads the code of a rule by its exact text fires at a store holding
  that code (`probe_reads_code`) and is refused at a store holding the code of a renamed copy
  (`probe_refuses_renamed`). The step of the coded rules does not see their names; a rule that reads
  code rows as data does.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RulesAsRows.Renaming

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire)
open LogicOverTheStep.StepSpan (Succ)
open Expr
open Examples (DataFragment)
open Gating

/-! ## Renaming -/

/-- The substitution renaming unknowns by `π`. -/
def renamer (π : ℕ → ℕ) : ℕ → Expr := fun v => var (π v)

/-- **A rule with its own unknowns renamed by `π`.** -/
def rename (π : ℕ → ℕ) (r : Rule Tm) : Rule Tm :=
  ⟨r.locals, r.body.map (subst (renamer π)), r.collect.map (subst (renamer π))⟩

theorem subst_renaming (π : ℕ → ℕ) (σ : ℕ → Expr) (t : Expr) :
    subst σ (subst (renamer π) t) = subst (fun v => σ (π v)) t := by
  rw [subst_subst]
  rfl

/-- **Reading each renamed unknown as the original one undoes an injective renaming.** -/
theorem subst_invFun {π : ℕ → ℕ} (inj : Function.Injective π) (σ : ℕ → Expr) (t : Expr) :
    subst (fun w => σ (Function.invFun π w)) (subst (renamer π) t) = subst σ t := by
  rw [subst_renaming]
  congr 1
  funext v
  rw [Function.leftInverse_invFun inj v]

theorem check_map_map (g h : Expr → Expr) (c : Check Expr) :
    (c.map g).map h = c.map fun t => h (g t) := by
  cases c <;> rfl

/-- Mapping a body twice is mapping it by the composite. -/
theorem body_map_map (b : RuleInstance Expr) {g h k : Expr → Expr} (comp : ∀ t, h (g t) = k t) :
    (b.map g).map h = b.map k := by
  have composite : (fun t => h (g t)) = k := funext comp
  obtain ⟨take, read, tell, checks, produce⟩ := b
  simp only [RuleInstance.map, List.map_map, RuleInstance.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact List.map_congr_left fun t _ => comp t
  · exact List.map_congr_left fun t _ => comp t
  · exact List.map_congr_left fun e _ => by simp only [Function.comp_apply, comp]
  · exact List.map_congr_left fun c _ => by rw [Function.comp_apply, check_map_map, composite]
  · exact List.map_congr_left fun t _ => comp t

theorem checkTerms_map (g : Expr → Expr) (c : Check Expr) : checkTerms (c.map g) = (checkTerms c).map g := by
  cases c <;> rfl

/-- The terms of a renamed rule are the renamed terms. -/
theorem terms_rename (π : ℕ → ℕ) (r : Rule Tm) :
    (rename π r).terms = r.terms.map (subst (renamer π)) := by
  simp only [Rule.terms, rename, RuleInstance.map, List.map_append, List.map_map, List.flatMap_map,
    List.map_flatMap, checkTerms_map]
  rfl

/-! ## One firing for the other -/

variable {O : Type*} [DecidableEq O]

section Firings

variable (π : ℕ → ℕ) {P P' : Program Tm}

/-- **The firing of the renamed rule matching a firing**: the opening reads each renamed unknown as the
original one. -/
noncomputable def forthFiring {a : PUnit.{1}} (f : Firing O Ext P a) (member : rename π f.rule ∈ P') :
    Firing O Ext P' a :=
  ⟨rename π f.rule, member, f.ext, fun w => f.opening (Function.invFun π w), f.selection, f.seen⟩

/-- **The firing of a rule matching a firing of its renamed copy**: the opening of each unknown is the
opening of its renamed unknown. -/
def backFiring {a : PUnit.{1}} (f' : Firing O Ext P' a) {r : Rule Tm} (member : r ∈ P) :
    Firing O Ext P a :=
  ⟨r, member, f'.ext, fun v => f'.opening (π v), f'.selection, f'.seen⟩

variable {π}

/-- **Forth**: an admitted firing of a rule gives an admitted firing of its renamed copy, with the same
selection and the same result. -/
theorem forth (inj : Function.Injective π) {s : State Tm O} (f : Firing O Ext P s.frame)
    (admitted : f.Admits X s) (member : rename π f.rule ∈ P') :
    (forthFiring π f member).Admits X s ∧ (forthFiring π f member).selection = f.selection ∧
      (forthFiring π f member).result X s = f.result X s := by
  have opened : (forthFiring π f member).opened X = f.opened X := by
    show (f.rule.body.map (subst (renamer π))).map (X.act fun w => f.opening (Function.invFun π w)) =
      f.rule.body.map (X.act f.opening)
    exact body_map_map f.rule.body fun t => subst_invFun inj f.opening t
  have collect : (forthFiring π f member).collectOpened X = f.collectOpened X := by
    show (f.rule.collect.map (subst (renamer π))).map (X.act fun w => f.opening (Function.invFun π w)) =
      f.rule.collect.map (X.act f.opening)
    rw [List.map_map]
    exact List.map_congr_left fun t _ => subst_invFun inj f.opening t
  have information : (forthFiring π f member).information X s = f.information X s := by
    unfold Firing.information
    rw [opened]
    rfl
  have holds : ∀ (b : PUnit.{1}) (σ : ℕ → Expr),
      (forthFiring π f member).Holds X s (b := b) σ ↔ f.Holds X s (b := b) σ := by
    intro b σ
    unfold Firing.Holds
    rw [opened, collect]
    rfl
  obtain ⟨⟨fresh, takenNodup, madeNodup, takes, reads, makes, collectLength⟩, enabled, solvable,
    entails⟩ := admitted
  refine ⟨⟨⟨?_, takenNodup, madeNodup, ?_, ?_, ?_, ?_⟩, enabled, ?_, ?_⟩, rfl, ?_⟩
  · intro b g h
    obtain ⟨u, mentions, terms⟩ := fresh b g fun v => h (π v)
    refine ⟨u, mentions, ?_⟩
    intro t' inside
    have inside' : t' ∈ (rename π f.rule).terms := inside
    rw [terms_rename, List.mem_map] at inside'
    obtain ⟨t, member', rfl⟩ := inside'
    have one := terms t member'
    show nf (subst u (subst (fun w => f.opening (Function.invFun π w)) (subst (renamer π) t))) =
      nf (subst h (subst (renamer π) t))
    rw [subst_invFun inj, subst_renaming]
    exact one
  · show (f.rule.body.take.map (subst (renamer π))).length = f.selection.taken.length
    rw [List.length_map]
    exact takes
  · show (f.rule.body.read.map (subst (renamer π))).length = f.selection.read.length
    rw [List.length_map]
    exact reads
  · show (f.rule.body.produce.map (subst (renamer π))).length = f.selection.made.length
    rw [List.length_map]
    exact makes
  · show (f.rule.collect.map (subst (renamer π))).length = f.seen.length
    rw [List.length_map]
    exact collectLength
  · rw [information]
    exact solvable
  · rw [information]
    intro b σ solved
    exact (holds b σ).mpr (entails b σ solved)
  · unfold Firing.result
    rw [information, opened]
    rfl

/-- **Back**: an admitted firing of the renamed copy of a rule gives an admitted firing of the rule,
with the same selection and the same result. -/
theorem back (inj : Function.Injective π) {s : State Tm O} (f' : Firing O Ext P' s.frame)
    (admitted : f'.Admits X s) {r : Rule Tm} (member : r ∈ P) (same : f'.rule = rename π r) :
    (backFiring π f' member).Admits X s ∧ (backFiring π f' member).selection = f'.selection ∧
      (backFiring π f' member).result X s = f'.result X s := by
  obtain ⟨rule, member', ext, opening, selection, seen⟩ := f'
  have same' : rule = rename π r := same
  subst same'
  have opened : (backFiring π ⟨rename π r, member', ext, opening, selection, seen⟩ member).opened X =
      (⟨rename π r, member', ext, opening, selection, seen⟩ : Firing O Ext P' s.frame).opened X := by
    show r.body.map (X.act fun v => opening (π v)) =
      (r.body.map (subst (renamer π))).map (X.act opening)
    exact (body_map_map r.body fun t => subst_renaming π opening t).symm
  have collect : (backFiring π ⟨rename π r, member', ext, opening, selection, seen⟩ member).collectOpened X =
      (⟨rename π r, member', ext, opening, selection, seen⟩ : Firing O Ext P' s.frame).collectOpened X := by
    show r.collect.map (X.act fun v => opening (π v)) =
      (r.collect.map (subst (renamer π))).map (X.act opening)
    rw [List.map_map]
    exact List.map_congr_left fun t _ => (subst_renaming π opening t).symm
  have information : (backFiring π ⟨rename π r, member', ext, opening, selection, seen⟩ member).information X s =
      (⟨rename π r, member', ext, opening, selection, seen⟩ : Firing O Ext P' s.frame).information X s := by
    unfold Firing.information
    rw [opened]
    rfl
  have holds : ∀ (b : PUnit.{1}) (σ : ℕ → Expr),
      (backFiring π ⟨rename π r, member', ext, opening, selection, seen⟩ member).Holds X s (b := b) σ ↔
        (⟨rename π r, member', ext, opening, selection, seen⟩ : Firing O Ext P' s.frame).Holds X s (b := b) σ := by
    intro b σ
    unfold Firing.Holds
    rw [opened, collect]
    rfl
  obtain ⟨⟨fresh, takenNodup, madeNodup, takes, reads, makes, collectLength⟩, enabled, solvable,
    entails⟩ := admitted
  refine ⟨⟨⟨?_, takenNodup, madeNodup, ?_, ?_, ?_, ?_⟩, enabled, ?_, ?_⟩, rfl, ?_⟩
  · intro b g h
    obtain ⟨u, mentions, terms⟩ := fresh b g fun w => h (Function.invFun π w)
    refine ⟨u, mentions, ?_⟩
    intro t inside
    have one := terms (subst (renamer π) t) (by
      show subst (renamer π) t ∈ (rename π r).terms
      rw [terms_rename]
      exact List.mem_map.mpr ⟨t, inside, rfl⟩)
    have one' : nf (subst u (subst opening (subst (renamer π) t))) =
        nf (subst (fun w => h (Function.invFun π w)) (subst (renamer π) t)) := one
    rw [subst_renaming, subst_invFun inj] at one'
    exact one'
  · have takes' : (r.body.take.map (subst (renamer π))).length = selection.taken.length := takes
    rw [List.length_map] at takes'
    exact takes'
  · have reads' : (r.body.read.map (subst (renamer π))).length = selection.read.length := reads
    rw [List.length_map] at reads'
    exact reads'
  · have makes' : (r.body.produce.map (subst (renamer π))).length = selection.made.length := makes
    rw [List.length_map] at makes'
    exact makes'
  · have collect' : (r.collect.map (subst (renamer π))).length = seen.length := collectLength
    rw [List.length_map] at collect'
    exact collect'
  · rw [information]
    exact solvable
  · rw [information]
    intro b σ solved
    exact (holds b σ).mpr (entails b σ solved)
  · unfold Firing.result
    rw [information, opened]
    rfl

end Firings

/-! ## The same steps -/

/-- **The program with each rule renamed by a renaming of its own.** -/
def renamed (ρ : Rule Tm → ℕ → ℕ) (P : Program Tm) : Program Tm := (fun r => rename (ρ r) r) '' P

/-- **A program and its renamed copy have the same steps**, when each renaming is injective. -/
theorem renamed_succ {P : Program Tm} {ρ : Rule Tm → ℕ → ℕ} (inj : ∀ r ∈ P, Function.Injective (ρ r))
    (s t : State Tm O) :
    Succ (step X O Ext (renamed ρ P)).toStep s t ↔ Succ (step X O Ext P).toStep s t := by
  constructor
  · rintro ⟨f', admitted, rfl⟩
    obtain ⟨r, hr, same⟩ := f'.member
    obtain ⟨admittedF, -, result⟩ := back (inj r hr) f' admitted hr same.symm
    exact ⟨backFiring (ρ r) f' hr, admittedF, result⟩
  · rintro ⟨f, admitted, rfl⟩
    have member : rename (ρ f.rule) f.rule ∈ renamed ρ P := Set.mem_image_of_mem _ f.member
    obtain ⟨admittedG, -, result⟩ := forth (inj f.rule f.member) f admitted member
    exact ⟨forthFiring (ρ f.rule) f member, admittedG, result⟩

/-- **The same runs.** -/
theorem renamed_runs {P : Program Tm} {ρ : Rule Tm → ℕ → ℕ} (inj : ∀ r ∈ P, Function.Injective (ρ r))
    (s t : State Tm O) :
    Relation.ReflTransGen (Succ (step X O Ext (renamed ρ P)).toStep) s t ↔
      Relation.ReflTransGen (Succ (step X O Ext P).toStep) s t := by
  have same : Succ (step X O Ext (renamed ρ P)).toStep = Succ (step X O Ext P).toStep := by
    funext s t
    exact propext (renamed_succ inj s t)
  rw [same]

/-! ## Through the interpreter -/

theorem dropFree_rename (π : ℕ → ℕ) : ∀ {t : Expr}, t.dropFree → (subst (renamer π) t).dropFree
  | var _, _ => rfl
  | sym _, _ => rfl
  | slot _ _, _ => rfl
  | cell a b, free => by
      simp only [dropFree, Bool.and_eq_true] at free
      simp only [subst, dropFree, Bool.and_eq_true]
      exact ⟨dropFree_rename π free.1, dropFree_rename π free.2⟩
  | drop _ _, free => by simp [dropFree] at free

theorem fragment_rename (π : ℕ → ℕ) {r : Rule Tm} (frag : Fragment r) : Fragment (rename π r) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t inside
    obtain ⟨t, member, rfl⟩ := List.mem_map.mp inside
    exact dropFree_rename π (frag.take t member)
  · intro t inside
    obtain ⟨t, member, rfl⟩ := List.mem_map.mp inside
    exact dropFree_rename π (frag.read t member)
  · intro e inside
    obtain ⟨e, member, rfl⟩ := List.mem_map.mp inside
    exact ⟨dropFree_rename π (frag.tell e member).1, dropFree_rename π (frag.tell e member).2⟩
  · intro c inside t term
    obtain ⟨c, member, rfl⟩ := List.mem_map.mp inside
    rw [checkTerms_map] at term
    obtain ⟨t, member', rfl⟩ := List.mem_map.mp term
    exact dropFree_rename π (frag.check c member t member')
  · intro t inside
    obtain ⟨t, member, rfl⟩ := List.mem_map.mp inside
    exact dropFree_rename π (frag.produce t member)
  · intro t inside
    obtain ⟨t, member, rfl⟩ := List.mem_map.mp inside
    exact dropFree_rename π (frag.collect t member)

theorem data_rename (π : ℕ → ℕ) {r : Rule Tm} (data : r ∈ DataFragment) : rename π r ∈ DataFragment := by
  refine ⟨fragment_rename π data.1, ?_⟩
  intro m inside
  obtain ⟨m, member, rfl⟩ := List.mem_map.mp inside
  obtain ⟨t, rfl⟩ := data.2 m member
  exact ⟨subst (renamer π) t, rfl⟩

theorem kindOf_map (g : Expr → Expr) (c : Check Expr) : kindOf (c.map g) = kindOf c := by
  cases c <;> rfl

theorem pattern_map (g : Expr → Expr) (c : Check Expr) : (c.map g).pattern = g c.pattern := by
  cases c <;> rfl

theorem addressed_rename (π : ℕ → ℕ) {r : Rule Tm} (addressed : DataAddressed r) :
    DataAddressed (rename π r) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p inside
    obtain ⟨p, member, rfl⟩ := List.mem_map.mp inside
    obtain ⟨t, rfl⟩ := addressed.take p member
    exact ⟨subst (renamer π) t, rfl⟩
  · intro p inside
    obtain ⟨p, member, rfl⟩ := List.mem_map.mp inside
    obtain ⟨t, rfl⟩ := addressed.read p member
    exact ⟨subst (renamer π) t, rfl⟩
  · intro c inside kind
    obtain ⟨c, member, rfl⟩ := List.mem_map.mp inside
    rw [kindOf_map] at kind
    obtain ⟨t, same⟩ := addressed.query c member kind
    refine ⟨subst (renamer π) t, ?_⟩
    rw [pattern_map, same]
    rfl
  · intro p inside
    obtain ⟨p, member, rfl⟩ := List.mem_map.mp inside
    obtain ⟨t, rfl⟩ := addressed.collect p member
    exact ⟨subst (renamer π) t, rfl⟩

/-- **A fixed program with each rule renamed.** -/
def renameProgram (P : FixedProgram) (ρ : Rule Tm → ℕ → ℕ) : FixedProgram where
  rules := P.rules.map fun r => rename (ρ r) r
  data r inside := by
    obtain ⟨r, member, rfl⟩ := List.mem_map.mp inside
    exact data_rename (ρ r) (P.data r member)
  addressed r inside := by
    obtain ⟨r, member, rfl⟩ := List.mem_map.mp inside
    exact addressed_rename (ρ r) (P.addressed r member)

theorem renameProgram_program (P : FixedProgram) (ρ : Rule Tm → ℕ → ℕ) :
    (renameProgram P ρ).program = renamed ρ P.program := by
  ext r
  constructor
  · intro inside
    have inside' : r ∈ P.rules.map (fun q => rename (ρ q) q) := inside
    obtain ⟨q, member, rfl⟩ := List.mem_map.mp inside'
    exact Set.mem_image_of_mem _ member
  · rintro ⟨q, member, rfl⟩
    show rename (ρ q) q ∈ P.rules.map (fun q => rename (ρ q) q)
    exact List.mem_map.mpr ⟨q, member, rfl⟩

/-- **The interpreter, from the codes of the renamed rules, runs the original program**: strongly
bisimilar, step for step, to the step of the original fixed program. -/
theorem renamed_codes_bisimulation {P : FixedProgram} {ρ : Rule Tm → ℕ → ℕ}
    (inj : ∀ r ∈ P.rules, Function.Injective (ρ r)) {s : State Tm O}
    {u : State Tm (O ⊕ Fin (renameProgram P ρ).rules.length)} (related : Runs (renameProgram P ρ) s u) :
    (∀ s', Succ (step X O Ext P.program).toStep s s' → ∃ u', InterpSucc u u' ∧ Runs (renameProgram P ρ) s' u') ∧
      (∀ u', InterpSucc u u' →
        ∃ s', Succ (step X O Ext P.program).toStep s s' ∧ Runs (renameProgram P ρ) s' u') := by
  have same : ∀ s s', Succ (step X O Ext (renameProgram P ρ).program).toStep s s' ↔
      Succ (step X O Ext P.program).toStep s s' := by
    intro s s'
    rw [renameProgram_program]
    exact renamed_succ inj s s'
  obtain ⟨forthU, backU⟩ := fixed_program_bisimulation related
  refine ⟨fun s' moved => forthU s' ((same s s').mpr moved), fun u' moved => ?_⟩
  obtain ⟨s', moved', related'⟩ := backU u' moved
  exact ⟨s', (same s s').mp moved', related'⟩

/-! ## Examples -/

section Demo

open Examples (first five six done)

/-- Shift every rule's unknowns up by one hundred. -/
def shiftAll : Rule Tm → ℕ → ℕ := fun _ v => v + 100

theorem shiftAll_injective (r : Rule Tm) : Function.Injective (shiftAll r) :=
  fun _ _ same => Nat.add_right_cancel same

/-- **The renamed codes are different rows.** -/
theorem renamed_code_ne : ruleCode (rename (shiftAll first) first) ≠ ruleCode first := by decide

/-- **The two-step run of the example program, through the interpreter, from the codes of the renamed
rules.** -/
theorem renamed_demo_interpreter_run :
    ∃ u₁ u₂, InterpSucc (withCodes (renameProgram demoProgram shiftAll) dataStart) u₁ ∧ InterpSucc u₁ u₂ ∧
      Runs (renameProgram demoProgram shiftAll) (demoSecond.result X dataMiddle) u₂ := by
  have start := fixed_program_start (P := renameProgram demoProgram shiftAll) dataStart_rows
  obtain ⟨u₁, moved₁, related₁⟩ :=
    (renamed_codes_bisimulation (fun r _ => shiftAll_injective r) start).1 _ demo_run.1
  obtain ⟨u₂, moved₂, related₂⟩ :=
    (renamed_codes_bisimulation (fun r _ => shiftAll_injective r) related₁).1 _ demo_run.2
  exact ⟨u₁, u₂, moved₁, moved₂, related₂⟩

/-! ### Control: injectivity is needed -/

/-- Take a data row holding a pair, make done. -/
def pairRule : Rule Tm := ⟨PUnit.unit, ⟨[obj (cell (var 0) (var 1))], [], [], [], [obj done]⟩, []⟩

/-- Send every unknown to `0`. -/
def collapse : ℕ → ℕ := fun _ => 0

/-- A store holding the pair `(five, six)`. -/
def pairStore : State Tm ℕ := ⟨PUnit.unit, [], {0}, fun _ => obj (cell five six)⟩

/-- The pair rule on the pair. -/
def pairFiring : Firing ℕ Ext ({pairRule} : Program Tm) pairStore.frame :=
  ⟨pairRule, Set.mem_singleton _, PUnit.unit, shift 10, ⟨[0], [], [1]⟩, []⟩

/-- **The pair rule fires on the pair.** -/
theorem pair_fires : pairFiring.Admits X pairStore := by
  have information : pairFiring.information X pairStore =
      [(obj (cell (var 10) (var 11)), obj (cell five six))] := rfl
  refine ⟨⟨fresh_shift pairFiring rfl (by decide), by decide, by decide, rfl, rfl, rfl, rfl⟩,
    by decide, ⟨PUnit.unit, fun v => if v = 10 then five else six, ?_⟩, ?_⟩
  · rw [information]
    intro e inside
    simp only [List.mem_singleton] at inside
    subst inside
    rfl
  · intro b σ _
    refine (holds_iff pairFiring rfl σ).mpr ?_
    intro c inside
    simp [pairFiring, pairRule] at inside

/-- **Its collapsed copy is refused at the same store**: the pattern `(x, x)` does not meet `(five, six)`. -/
theorem collapsed_refused (f : Firing ℕ Ext ({rename collapse pairRule} : Program Tm) pairStore.frame) :
    ¬ f.Admits X pairStore := by
  obtain ⟨rule, member, ext, opening, ⟨taken, read, made⟩, seen⟩ := f
  have isRule : rule = rename collapse pairRule := member
  subst isRule
  rintro ⟨⟨-, -, -, takes, -, -, -⟩, -, ⟨b, σ, solved⟩, -⟩
  have one : 1 = taken.length := takes
  obtain ⟨o, rfl⟩ : ∃ o, taken = [o] := by
    match taken, one with
    | [o], _ => exact ⟨o, rfl⟩
    | [], h => exact absurd h (by simp)
    | _ :: _ :: _, h => exact absurd h (by simp only [List.length_cons]; omega)
  have information : Firing.information X pairStore
      (⟨rename collapse pairRule, member, ext, opening, ⟨[o], read, made⟩, seen⟩ :
        Firing ℕ Ext ({rename collapse pairRule} : Program Tm) pairStore.frame) =
      [(obj (cell (opening 0) (opening 0)), obj (cell five six))] := rfl
  have equation : nf (subst σ (obj (cell (opening 0) (opening 0)))) = nf (subst σ (obj (cell five six))) :=
    solved (obj (cell (opening 0) (opening 0)), obj (cell five six))
      (by rw [information]; exact List.mem_singleton_self _)
  simp only [obj, five, six, subst, nf, Expr.cell.injEq, true_and] at equation
  exact absurd (equation.1.symm.trans equation.2) (by decide)

/-! ### Control: code rows are syntax -/

/-- Read the code of `first` by its exact text, make done. -/
def probe : Rule Tm := ⟨PUnit.unit, ⟨[], [ruleCode first], [], [], [obj done]⟩, []⟩

/-- A store holding one row. -/
def oneRow (c : Expr) : State Tm ℕ := ⟨PUnit.unit, [], {0}, fun _ => c⟩

/-- The probe reading the row. -/
def probeFiring (c : Expr) : Firing ℕ Ext ({probe} : Program Tm) (oneRow c).frame :=
  ⟨probe, Set.mem_singleton _, PUnit.unit, shift 10, ⟨[], [0], [1]⟩, []⟩

/-- **The probe fires at a store holding the code of `first`.** -/
theorem probe_reads_code : (probeFiring (ruleCode first)).Admits X (oneRow (ruleCode first)) := by
  have information : (probeFiring (ruleCode first)).information X (oneRow (ruleCode first)) =
      [(ruleCode first, ruleCode first)] := rfl
  refine ⟨⟨fresh_shift (probeFiring (ruleCode first)) rfl (by decide), by decide, by decide, rfl, rfl, rfl,
    rfl⟩, by decide, ⟨PUnit.unit, var, ?_⟩, ?_⟩
  · rw [information]
    intro e inside
    simp only [List.mem_singleton] at inside
    subst inside
    rfl
  · intro b σ _
    refine (holds_iff (probeFiring (ruleCode first)) rfl σ).mpr ?_
    intro c inside
    simp [probeFiring, probe] at inside

/-- **The probe is refused at a store holding the code of a renamed copy of `first`**, which the step of
the coded rule cannot tell from `first` (`renamed_succ`). -/
theorem probe_refuses_renamed
    (f : Firing ℕ Ext ({probe} : Program Tm) (oneRow (ruleCode (rename (shiftAll first) first))).frame) :
    ¬ f.Admits X (oneRow (ruleCode (rename (shiftAll first) first))) := by
  obtain ⟨rule, member, ext, opening, ⟨taken, read, made⟩, seen⟩ := f
  have isRule : rule = probe := member
  subst isRule
  rintro ⟨⟨-, -, -, -, reads, -, -⟩, -, ⟨b, σ, solved⟩, -⟩
  have one : 1 = read.length := reads
  obtain ⟨o, rfl⟩ : ∃ o, read = [o] := by
    match read, one with
    | [o], _ => exact ⟨o, rfl⟩
    | [], h => exact absurd h (by simp)
    | _ :: _ :: _, h => exact absurd h (by simp only [List.length_cons]; omega)
  have fragFirst : Fragment first := Examples.first_mem.1
  have fragRenamed : Fragment (rename (shiftAll first) first) := fragment_rename _ fragFirst
  have information : Firing.information X (oneRow (ruleCode (rename (shiftAll first) first)))
      (⟨probe, member, ext, opening, ⟨taken, [o], made⟩, seen⟩ :
        Firing ℕ Ext ({probe} : Program Tm) (oneRow (ruleCode (rename (shiftAll first) first))).frame) =
      [(subst opening (ruleCode first), subst var (ruleCode (rename (shiftAll first) first)))] := rfl
  have equation : nf (subst σ (subst opening (ruleCode first))) =
      nf (subst σ (subst var (ruleCode (rename (shiftAll first) first)))) :=
    solved (subst opening (ruleCode first), subst var (ruleCode (rename (shiftAll first) first)))
      (by rw [information]; exact List.mem_singleton_self _)
  rw [subst_ruleCode fragFirst, subst_ruleCode fragFirst, subst_ruleCode fragRenamed,
    subst_ruleCode fragRenamed, nf_ruleCode fragFirst, nf_ruleCode fragRenamed] at equation
  exact renamed_code_ne equation.symm

end Demo

#print axioms forth
#print axioms back
#print axioms renamed_succ
#print axioms renamed_runs
#print axioms renamed_codes_bisimulation
#print axioms renamed_demo_interpreter_run
#print axioms pair_fires
#print axioms collapsed_refused
#print axioms probe_reads_code
#print axioms probe_refuses_renamed

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RulesAsRows.Renaming
