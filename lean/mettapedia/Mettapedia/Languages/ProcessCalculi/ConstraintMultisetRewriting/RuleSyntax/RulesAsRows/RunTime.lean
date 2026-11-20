import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RulesAsRows.Examples

/-!
# Rules added and removed at run time: rows that gate rules of a program fixed in advance

A stored rule fires only while a row holding its code is present (`Examples.code_present`). So a firing
that makes a code row ungates a rule for every later firing, and one that takes the last such row gates
it again. What is added or removed at run time is a row: every rule that can fire is a rule of
`Stored F`, a program fixed before the run, and adding or removing a rule at run time is making or
taking a row that gates a rule of that fixed program (`stored_program_installs`). In a closed fragment
the codes that can be made are literal codes written into the made rows of its rules (`ClosedFragment`);
a rule that makes a code from a row it received is in no closed fragment; for the relay and `second`,
from a start whose messages carry the body of `second`'s code, it is covered through the tags of the
knowledge (`Mobility`). Through the bisimulation, the same runs are runs of the interpreter `U`, whose
program never changes either.

* **The coding is injective** (`ruleCode_injective`): different rules have different codes; quotation
  is injective on all terms (`quote_injective_all`), and a list of checks is determined by its first
  terms, second terms and kinds (`checks_eq_of_parts`).
* **Adding a rule** (`installer`, `interpreter_install_run`): an installer takes `obj go` and makes the
  data row `obj (seen five)` and the code of `second`. Before it fires, no firing of `second` is
  admitted (`second_not_before`), and every admitted firing of `U` is the interpretation of the
  installer (`interpreter_before_install`). After it fires, `second` fires on the row it made; through
  `U`, two admitted firings reach `obj done`, the second one reading a code row that the first
  interpreter firing made: its label is the interpreter's opened made entry, whose value is the code of
  `second` at every solution (the third conjunct of `interpreter_install_run`). The same run is a run of
  the fixed program `Stored InstallFragment` (`stored_program_installs`).
* **Removing a rule** (`remover`, `removeFiring_admitted`, `interpreter_removal`): a rule that takes the
  code row of `second`; after it fires, no firing of `second` is admitted (`second_not_after_removal`).
* **The step is state-based**: admission is a property of the state it is asked at, so a code made
  later enables nothing earlier; `second_not_before` is that fact at the starting store.
* **Control: the ungated program.** The fixed program `{second}`, whose rule reads no code, fires
  `second` at a store holding no code at all (`fixed_fires_without_code`), where the stored-rule program
  does not (`stored_needs_code`); `fixed_rule_mem` restates that the rule of every firing is in the
  program. The one hypothesis the control drops is the gate (the read of the rule's own code): it
  separates the gated `second` from the ungated one, and says nothing against fixed programs, since
  `Stored InstallFragment`, which adds `second` at run time, is itself a fixed program.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RulesAsRows.RunTime

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire)
open LogicOverTheStep.StepSpan (Succ)
open Expr
open Examples (DataFragment dataFragment_closed second second_mem five done code_present)

/-! ## The coding is injective -/

/-- **Quotation is injective on all terms.** -/
theorem quote_injective_all : ∀ {s t : Expr}, quote s = quote t → s = t
  | var _, var _, same => by simpa [quote] using same
  | sym _, sym _, same => by simpa [quote] using same
  | slot _ _, slot _ _, same => by simpa [quote] using same
  | cell a b, cell c d, same => by
      simp only [quote, Expr.cell.injEq] at same
      rw [quote_injective_all same.1, quote_injective_all same.2]
  | drop a b, drop c d, same => by
      simp only [quote, Expr.drop.injEq] at same
      rw [quote_injective_all same.1, quote_injective_all same.2]
  | var _, sym _, same => by simp [quote] at same
  | var _, cell _ _, same => by simp [quote] at same
  | var _, slot _ _, same => by simp [quote] at same
  | var _, drop _ _, same => by simp [quote] at same
  | sym _, var _, same => by simp [quote] at same
  | sym _, cell _ _, same => by simp [quote] at same
  | sym _, slot _ _, same => by simp [quote] at same
  | sym _, drop _ _, same => by simp [quote] at same
  | cell _ _, var _, same => by simp [quote] at same
  | cell _ _, sym _, same => by simp [quote] at same
  | cell _ _, slot _ _, same => by simp [quote] at same
  | cell _ _, drop _ _, same => by simp [quote] at same
  | slot _ _, var _, same => by simp [quote] at same
  | slot _ _, sym _, same => by simp [quote] at same
  | slot _ _, cell _ _, same => by simp [quote] at same
  | slot _ _, drop _ _, same => by simp [quote] at same
  | drop _ _, var _, same => by simp [quote] at same
  | drop _ _, sym _, same => by simp [quote] at same
  | drop _ _, cell _ _, same => by simp [quote] at same
  | drop _ _, slot _ _, same => by simp [quote] at same

/-- **A list of checks is determined by their first terms, second terms and kinds.** -/
theorem checks_eq_of_parts : ∀ {l₁ l₂ : List (Check Expr)},
    l₁.map Check.pattern = l₂.map Check.pattern → l₁.map guardRight = l₂.map guardRight →
      l₁.map kindOf = l₂.map kindOf → l₁ = l₂
  | [], [], _, _, _ => rfl
  | [], _ :: _, same, _, _ => by simp at same
  | _ :: _, [], same, _, _ => by simp at same
  | c₁ :: rest₁, c₂ :: rest₂, patterns, rights, kinds => by
      simp only [List.map_cons, List.cons.injEq] at patterns rights kinds
      have head : c₁ = c₂ := by
        rw [← check_rebuild c₁, ← check_rebuild c₂, patterns.1, rights.1, kinds.1]
      rw [head, checks_eq_of_parts patterns.2 rights.2 kinds.2]

/-- **Different rules have different codes.** -/
theorem ruleCode_injective {r r' : Rule Tm} (same : ruleCode r = ruleCode r') : r = r' := by
  unfold ruleCode code at same
  simp only [Expr.cell.injEq, true_and] at same
  have outer := List.map_inj_left.mp (lst_injective same)
  have part : ∀ k, k < 9 → partsAt r k = partsAt r' k := by
    intro k hk
    have lists := lst_injective (outer k (List.mem_range.mpr hk))
    exact (List.map_injective_iff.mpr (fun _ _ same => quote_injective_all same)) lists
  have take : r.body.take = r'.body.take := part 0 (by decide)
  have read : r.body.read = r'.body.read := part 1 (by decide)
  have produce : r.body.produce = r'.body.produce := part 2 (by decide)
  have fsts : r.body.tell.map Prod.fst = r'.body.tell.map Prod.fst := part 3 (by decide)
  have snds : r.body.tell.map Prod.snd = r'.body.tell.map Prod.snd := part 4 (by decide)
  have patterns : r.body.checks.map Check.pattern = r'.body.checks.map Check.pattern := part 5 (by decide)
  have rights : r.body.checks.map guardRight = r'.body.checks.map guardRight := part 6 (by decide)
  have kindTerms : r.body.checks.map (fun c => (kindOf c).term) =
      r'.body.checks.map (fun c => (kindOf c).term) := part 7 (by decide)
  have collect : r.collect = r'.collect := part 8 (by decide)
  have kinds : r.body.checks.map kindOf = r'.body.checks.map kindOf := by
    have terms : (r.body.checks.map kindOf).map Kind.term = (r'.body.checks.map kindOf).map Kind.term := by
      rw [List.map_map, List.map_map]
      exact kindTerms
    exact (List.map_injective_iff.mpr Kind.term_injective) terms
  have tell : r.body.tell = r'.body.tell := by
    rw [← List.zip_unzip r.body.tell, ← List.zip_unzip r'.body.tell, List.unzip_fst, List.unzip_snd,
      List.unzip_fst, List.unzip_snd, fsts, snds]
  have checks : r.body.checks = r'.body.checks := checks_eq_of_parts patterns rights kinds
  obtain ⟨⟨⟩, ⟨take₁, read₁, tell₁, checks₁, produce₁⟩, collect₁⟩ := r
  obtain ⟨⟨⟩, ⟨take₂, read₂, tell₂, checks₂, produce₂⟩, collect₂⟩ := r'
  simp only at take read produce tell checks collect
  subst take read produce tell checks collect
  rfl

/-! ## The install fragment -/

/-- **The install fragment**: rules of the fragment whose made rows are data rows or codes of data
rules. -/
def InstallFragment : Set (Rule Tm) :=
  {r | Fragment r ∧ ∀ m ∈ r.body.produce, (∃ t, m = obj t) ∨ ∃ q ∈ DataFragment, m = ruleCode q}

theorem dataFragment_sub : DataFragment ⊆ InstallFragment :=
  fun _ hr => ⟨hr.1, fun m inside => Or.inl (hr.2 m inside)⟩

theorem installFragment_closed : ClosedFragment InstallFragment :=
  ⟨fun _ hr => hr.1, fun _ hr m inside =>
    (hr.2 m inside).imp id fun ⟨q, hq, same⟩ => ⟨q, dataFragment_sub hq, same⟩⟩

/-- Go. -/
def go : Expr := sym 14

/-- **An installer**: take `obj go`, make the data row `obj (seen five)` and the code of `second`. -/
def installer : Rule Tm :=
  ⟨PUnit.unit, ⟨[obj go], [], [], [], [obj (Examples.seen five), ruleCode second]⟩, []⟩

theorem installer_mem : installer ∈ InstallFragment := by
  refine ⟨Examples.fragment_of_check (by decide), ?_⟩
  · intro m inside
    simp only [installer, List.mem_cons, List.not_mem_nil, or_false] at inside
    rcases inside with rfl | rfl
    · exact Or.inl ⟨_, rfl⟩
    · exact Or.inr ⟨second, second_mem, rfl⟩

/-! ## Adding a rule -/

/-- The labels of the store before the install. -/
def beforeLabel (o : ℕ) : Expr := if o = 0 then obj go else if o = 1 then ruleCode installer else nil

/-- **The store before the install**: the go row and the installer's code. -/
def before : State Tm ℕ := ⟨PUnit.unit, [], {0, 1}, beforeLabel⟩

theorem before_tagged : Tagged InstallFragment before := by
  intro o present
  simp only [before, Finset.mem_insert, Finset.mem_singleton] at present
  rcases present with rfl | rfl
  · exact Or.inl ⟨_, rfl⟩
  · exact Or.inr ⟨installer, installer_mem, rfl⟩

theorem second_code_ne_installer_code : ruleCode second ≠ ruleCode installer := by decide

/-- **Before the install, `second` does not fire**: no row holds its code. -/
theorem second_not_before (ι : ℕ → Expr) (sel : Selection ℕ) (seen : List (Finset ℕ)) :
    ¬ (storedFiring (dataFragment_sub second_mem) before.frame ι sel seen).Admits X before := by
  intro admitted
  obtain ⟨c₀, present, coded⟩ := code_present installFragment_closed before_tagged _ admitted
  simp only [before, Finset.mem_insert, Finset.mem_singleton] at present
  rcases present with rfl | rfl
  · exact obj_ne_code _ _ coded
  · exact second_code_ne_installer_code coded.symm

/-- **Before the install, every admitted firing of the interpreter interprets the installer**: its
matching stored firing, with the same selection, is a firing of the installer. -/
theorem interpreter_before_install (g : Firing ℕ Ext U before.frame) (admitted : g.Admits X before) :
    ∃ f : Firing ℕ Ext (Stored InstallFragment) before.frame, f.Admits X before ∧
      f.selection = g.selection ∧ f.rule = stored installer := by
  obtain ⟨f, admittedF, same, -⟩ := backward installFragment_closed (represents_refl before_tagged) g admitted
  refine ⟨f, admittedF, same, ?_⟩
  obtain ⟨r, hr, hf⟩ := stored_cases f
  rw [hf] at admittedF ⊢
  obtain ⟨c₀, present, coded⟩ := code_present installFragment_closed before_tagged hr admittedF
  simp only [before, Finset.mem_insert, Finset.mem_singleton] at present
  rcases present with rfl | rfl
  · exact absurd coded (obj_ne_code _ _)
  · have sameRule := ruleCode_injective coded
    show stored r = stored installer
    rw [← sameRule]

/-- The installer, opened above the store's unknowns. -/
def installFiring : Firing ℕ Ext (Stored InstallFragment) before.frame :=
  storedFiring installer_mem before.frame (shift 10) ⟨[0], [1], [2, 3]⟩ []

theorem installFiring_information :
    installFiring.information X before = [(obj go, obj go), (ruleCode installer, ruleCode installer)] :=
  rfl

theorem before_bound : stateBound before ≤ 10 := by decide

/-- **The installer fires.** -/
theorem installFiring_admitted : installFiring.Admits X before := by
  refine ⟨⟨fresh_shift installFiring rfl before_bound, by decide, by decide, rfl, rfl, rfl, rfl⟩,
    by decide, ⟨PUnit.unit, var, ?_⟩, ?_⟩
  · rw [installFiring_information]
    intro e inside
    simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
    rcases inside with rfl | rfl <;> rfl
  · intro b σ _
    refine (holds_iff installFiring rfl σ).mpr ?_
    intro c inside
    simp [installFiring, storedFiring, stored, installer] at inside

/-- The store after the install. -/
def installed : State Tm ℕ := installFiring.result X before

theorem installed_present : installed.present = {1, 2, 3} := by decide

/-- **The made row `3` is the code of `second`.** -/
theorem installed_code : installed.label 3 = ruleCode second := by decide

theorem installed_bound : stateBound installed ≤ 20 := by decide

/-- `second`, now a rule of the store, taking the made data row and reading the made code. -/
def useFiring : Firing ℕ Ext (Stored InstallFragment) installed.frame :=
  storedFiring (dataFragment_sub second_mem) installed.frame (shift 20) ⟨[2], [3], [4]⟩ []

theorem useFiring_information :
    useFiring.information X installed =
      [(obj go, obj go), (ruleCode installer, ruleCode installer),
        (obj (Examples.seen (var 20)), obj (Examples.seen five)), (ruleCode second, ruleCode second)] := by
  decide

/-- **After the install, `second` fires.** -/
theorem useFiring_admitted : useFiring.Admits X installed := by
  refine ⟨⟨fresh_shift useFiring rfl installed_bound, by decide, by decide, rfl, rfl, rfl, rfl⟩,
    by decide, ⟨PUnit.unit, fun _ => five, ?_⟩, ?_⟩
  · rw [useFiring_information]
    intro e inside
    simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
    rcases inside with rfl | rfl | rfl | rfl <;> rfl
  · intro b σ solved
    rw [useFiring_information] at solved
    refine (holds_iff useFiring rfl σ).mpr ?_
    intro c inside
    simp only [useFiring, storedFiring, stored, second, List.mem_singleton] at inside
    subst inside
    have seenRow : nf (subst σ (obj (Examples.seen (var 20)))) = nf (subst σ (obj (Examples.seen five))) :=
      solved _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    simp only [obj, Examples.seen, five, subst, nf, Expr.cell.injEq, true_and] at seenRow
    show nf (σ 20) = five
    exact seenRow

/-- The store after `second`. -/
def after : State Tm ℕ := useFiring.result X installed

theorem after_present : after.present = {1, 3, 4} := by decide

theorem after_done : after.label 4 = obj done := rfl

/-- **A run that adds a rule and uses it.** -/
theorem install_run :
    StoredSucc InstallFragment before installed ∧ StoredSucc InstallFragment installed after :=
  ⟨⟨installFiring, installFiring_admitted, rfl⟩, ⟨useFiring, useFiring_admitted, rfl⟩⟩

/-- **The fixed program `Stored InstallFragment` adds `second` at run time**: before the install no
firing of the stored `second` is admitted; the run makes the row that ungates it, and the stored
`second` fires. Adding a rule at run time is making a row that gates a rule of a program fixed in
advance. -/
theorem stored_program_installs :
    StoredSucc (O := ℕ) InstallFragment before installed ∧
      StoredSucc (O := ℕ) InstallFragment installed after ∧ useFiring.rule = stored second ∧
      ∀ (ι : ℕ → Expr) (sel : Selection ℕ) (seen : List (Finset ℕ)),
        ¬ (storedFiring (dataFragment_sub second_mem) before.frame ι sel seen).Admits X before :=
  ⟨install_run.1, install_run.2, rfl, second_not_before⟩

/-- **Through the interpreter**: two admitted firings of `U`. The first makes a row whose value is the
code of `second` at every solution; the second reads it and reaches `obj done`. -/
theorem interpreter_install_run :
    ∃ u₁ u₂ : State Tm ℕ, InterpSucc before u₁ ∧ InterpSucc u₁ u₂ ∧
      (3 ∈ u₁.present ∧ ∀ σ, action.Models σ u₁.knowledge → nf (subst σ (u₁.label 3)) = ruleCode second) ∧
      Represents InstallFragment after u₂ ∧ 4 ∈ u₂.present ∧
      ∀ σ, action.Models σ u₂.knowledge → nf (subst σ (u₂.label 4)) = obj done := by
  obtain ⟨u₁, moved₁, rep₁⟩ := (bisimulation installFragment_closed (represents_refl before_tagged)).1 _
    install_run.1
  obtain ⟨u₂, moved₂, rep₂⟩ := (bisimulation installFragment_closed rep₁).1 _ install_run.2
  refine ⟨u₁, u₂, moved₁, moved₂, ⟨?_, fun σ solved => ?_⟩, rep₂, ?_, fun σ solved => ?_⟩
  · rw [rep₁.present, installed_present]
    decide
  · have present : 3 ∈ installed.present := by rw [installed_present]; decide
    obtain ⟨σ', -, labels⟩ := rep₁.forth σ solved
    rw [labels 3 present, installed_code, subst_ruleCode second_mem.1, nf_ruleCode second_mem.1]
  · rw [rep₂.present, after_present]
    decide
  · have present : 4 ∈ after.present := by rw [after_present]; decide
    obtain ⟨σ', -, labels⟩ := rep₂.forth σ solved
    rw [labels 4 present, after_done]
    rfl

/-! ## Removing a rule -/

/-- **A remover**: take the code row of `second`. -/
def remover : Rule Tm := ⟨PUnit.unit, ⟨[ruleCode second], [], [], [], []⟩, []⟩

theorem remover_mem : remover ∈ DataFragment :=
  ⟨Examples.fragment_of_check (by decide), fun m inside => by simp [remover] at inside⟩

/-- The labels of a store holding `second`'s code, a seen row, and the remover's code. -/
def holdingLabel (o : ℕ) : Expr :=
  if o = 0 then ruleCode second else if o = 1 then obj (Examples.seen five) else
    if o = 2 then ruleCode remover else nil

/-- A store where `second` could fire. -/
def holding : State Tm ℕ := ⟨PUnit.unit, [], {0, 1, 2}, holdingLabel⟩

theorem holding_tagged : Tagged DataFragment holding := by
  intro o present
  simp only [holding, Finset.mem_insert, Finset.mem_singleton] at present
  rcases present with rfl | rfl | rfl
  · exact Or.inr ⟨second, second_mem, rfl⟩
  · exact Or.inl ⟨_, rfl⟩
  · exact Or.inr ⟨remover, remover_mem, rfl⟩

/-- The remover, taking the code of `second` and reading its own. -/
def removeFiring : Firing ℕ Ext (Stored DataFragment) holding.frame :=
  storedFiring remover_mem holding.frame (shift 10) ⟨[0], [2], []⟩ []

theorem holding_bound : stateBound holding ≤ 10 := by decide

/-- **The remover fires.** -/
theorem removeFiring_admitted : removeFiring.Admits X holding := by
  refine ⟨⟨fresh_shift removeFiring rfl holding_bound, by decide, by decide, rfl, rfl, rfl, rfl⟩,
    by decide, ⟨PUnit.unit, var, ?_⟩, ?_⟩
  · have information : removeFiring.information X holding =
        [(ruleCode second, ruleCode second), (ruleCode remover, ruleCode remover)] := by decide
    rw [information]
    intro e inside
    simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
    rcases inside with rfl | rfl <;> rfl
  · intro b σ _
    refine (holds_iff removeFiring rfl σ).mpr ?_
    intro c inside
    simp [removeFiring, storedFiring, stored, remover] at inside

/-- The store after the removal. -/
def removed : State Tm ℕ := removeFiring.result X holding

theorem removed_present : removed.present = {1, 2} := by decide

theorem removed_tagged : Tagged DataFragment removed := by
  intro o present
  rw [removed_present] at present
  simp only [Finset.mem_insert, Finset.mem_singleton] at present
  rcases present with rfl | rfl
  · exact Or.inl ⟨_, rfl⟩
  · exact Or.inr ⟨remover, remover_mem, by decide⟩

theorem second_code_ne_remover_code : ruleCode second ≠ ruleCode remover := by decide

/-- **After the removal, `second` does not fire.** -/
theorem second_not_after_removal (ι : ℕ → Expr) (sel : Selection ℕ) (seen : List (Finset ℕ)) :
    ¬ (storedFiring second_mem removed.frame ι sel seen).Admits X removed := by
  intro admitted
  obtain ⟨c₀, present, coded⟩ := code_present dataFragment_closed removed_tagged second_mem admitted
  rw [removed_present] at present
  simp only [Finset.mem_insert, Finset.mem_singleton] at present
  rcases present with rfl | rfl
  · have label : removed.label 1 = obj (Examples.seen five) := by decide
    rw [label] at coded
    exact obj_ne_code _ _ coded
  · have label : removed.label 2 = ruleCode remover := by decide
    rw [label] at coded
    exact second_code_ne_remover_code coded.symm

/-- The read patterns of a rule. -/
def readsOf (q : Rule Tm) : List Expr := q.body.read

/-- **The removal run, through the interpreter**: an admitted firing of `U` takes the code row; after
it, no admitted firing of `U` interprets `second` (its matching stored firing would read a row holding
the code of `second`). -/
theorem interpreter_removal :
    ∃ u : State Tm ℕ, InterpSucc holding u ∧ Represents DataFragment removed u ∧
      ∀ (g : Firing ℕ Ext U u.frame), g.Admits X u →
        ∃ f : Firing ℕ Ext (Stored DataFragment) removed.frame, f.Admits X removed ∧
          f.selection = g.selection ∧ f.rule ≠ stored second := by
  obtain ⟨u, moved, rep⟩ := (bisimulation dataFragment_closed (represents_refl holding_tagged)).1 _
    ⟨removeFiring, removeFiring_admitted, rfl⟩
  refine ⟨u, moved, rep, fun g admitted => ?_⟩
  obtain ⟨f, admittedF, same, -⟩ := backward dataFragment_closed rep g admitted
  refine ⟨f, admittedF, same, fun isSecond => ?_⟩
  obtain ⟨r, hr, hf⟩ := stored_cases f
  rw [hf] at admittedF isSecond
  have sameRule : r = second := by
    have reads := congrArg readsOf isSecond
    simp only [readsOf, storedFiring, stored, List.cons.injEq] at reads
    exact ruleCode_injective reads.1
  subst sameRule
  exact second_not_after_removal _ _ _ admittedF

/-! ## Control: the ungated program -/

/-- **The rule of every firing of a program is in the program**: this is the definition of a firing
(`Firing.member`), restated. -/
theorem fixed_rule_mem {P : Program Tm} {s : State Tm ℕ} (f : Firing ℕ Ext P s.frame) : f.rule ∈ P :=
  f.member

/-- A store with a seen row and no code. -/
def bare : State Tm ℕ := ⟨PUnit.unit, [], {0}, fun _ => obj (Examples.seen five)⟩

/-- `second` as a rule of the fixed program `{second}`. -/
def fixedFiring : Firing ℕ Ext ({second} : Program Tm) bare.frame :=
  ⟨second, rfl, PUnit.unit, shift 10, ⟨[0], [], [1]⟩, []⟩

/-- **The ungated program `{second}` fires `second` with no code in the store.** The control drops one
hypothesis, the gate: the stored `second` reads its own code, this rule does not. -/
theorem fixed_fires_without_code : fixedFiring.Admits X bare := by
  refine ⟨⟨fresh_shift fixedFiring rfl (by decide), by decide, by decide, rfl, rfl, rfl, rfl⟩,
    by decide, ⟨PUnit.unit, fun _ => five, ?_⟩, ?_⟩
  · have information : fixedFiring.information X bare =
        [(obj (Examples.seen (var 10)), obj (Examples.seen five))] := rfl
    rw [information]
    intro e inside
    simp only [List.mem_singleton] at inside
    subst inside
    rfl
  · intro b σ solved
    have information : fixedFiring.information X bare =
        [(obj (Examples.seen (var 10)), obj (Examples.seen five))] := rfl
    rw [information] at solved
    refine (holds_iff fixedFiring rfl σ).mpr ?_
    intro c inside
    simp only [fixedFiring, second, List.mem_singleton] at inside
    subst inside
    have seenRow : nf (subst σ (obj (Examples.seen (var 10)))) = nf (subst σ (obj (Examples.seen five))) :=
      solved _ List.mem_cons_self
    simp only [obj, Examples.seen, five, subst, nf, Expr.cell.injEq, true_and] at seenRow
    show nf (σ 10) = five
    exact seenRow

/-- **The stored-rule program does not fire `second` there**: no row holds its code. -/
theorem stored_needs_code (ι : ℕ → Expr) (sel : Selection ℕ) (seen : List (Finset ℕ)) :
    ¬ (storedFiring second_mem bare.frame ι sel seen).Admits X bare := by
  intro admitted
  have tagged : Tagged DataFragment bare := fun _ _ => Or.inl ⟨_, rfl⟩
  obtain ⟨c₀, -, coded⟩ := code_present dataFragment_closed tagged second_mem admitted
  exact obj_ne_code _ _ coded

#print axioms quote_injective_all
#print axioms ruleCode_injective
#print axioms installFragment_closed
#print axioms second_not_before
#print axioms interpreter_before_install
#print axioms install_run
#print axioms stored_program_installs
#print axioms interpreter_install_run
#print axioms second_not_after_removal
#print axioms interpreter_removal
#print axioms fixed_rule_mem
#print axioms fixed_fires_without_code
#print axioms stored_needs_code

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RulesAsRows.RunTime
