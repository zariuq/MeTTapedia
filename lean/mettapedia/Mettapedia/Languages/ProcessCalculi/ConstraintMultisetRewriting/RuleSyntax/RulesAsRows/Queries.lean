import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RulesAsRows.Limits

/-!
# The none query and count queries of stored rules, through the interpreter

**The none query** (`quiet`): "when no token is present, make done", the none query of `obj (tok x)` with the
rule's own unknown `x`. None reads through every solution, and `x` is fresh, so it holds only when
no row could be a token of any value.
* At a store with a key and no token, `quiet` fires (`quiet_admitted`), and so does the interpreter
  (`interpreter_quiet`).
* At a store with a token, every firing of `quiet` is refused (`quiet_refused`), whatever its opening:
  the freshness of the opening provides the solution that sends `x` to the token's value. Since the
  only code there is `quiet`'s, **no firing of the interpreter is admitted at all**
  (`interpreter_idle_at_busy`).

**Count** (`single`): "read a key `y`; when exactly one row is the key `y`, make done". The read binds
`y`, so the count asks how many rows equal the read one.
* With one key five, `single` fires (`single_admitted`), and so does the interpreter
  (`interpreter_single`).
* With two keys five, the same firing is refused (`single_refused`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RulesAsRows.Queries

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire)
open LogicOverTheStep.StepSpan (Succ)
open Expr
open Examples (DataFragment dataFragment_closed five tok key done fragment_of_check code_present)
open RunTime (ruleCode_injective)

/-! ## The none query -/

/-- **When no token is present, make done.** -/
def quiet : Rule Tm := ⟨PUnit.unit, ⟨[], [], [], [.predicate .none (obj (tok (var 0)))], [obj done]⟩, []⟩

theorem quiet_mem : quiet ∈ DataFragment :=
  ⟨fragment_of_check rfl, fun m inside => by
    simp only [quiet, List.mem_singleton] at inside
    exact ⟨_, inside⟩⟩

/-- The labels of a store with a key and the code of `quiet`. -/
def calmLabel (o : ℕ) : Expr := if o = 0 then obj (key five) else if o = 1 then ruleCode quiet else nil

/-- **A store without a token.** -/
def calm : State Tm ℕ := ⟨PUnit.unit, [], {0, 1}, calmLabel⟩

/-- The labels of a store with a token and the code of `quiet`. -/
def busyLabel (o : ℕ) : Expr := if o = 0 then obj (tok five) else if o = 1 then ruleCode quiet else nil

/-- **A store with a token.** -/
def busy : State Tm ℕ := ⟨PUnit.unit, [], {0, 1}, busyLabel⟩

theorem calm_tagged : Tagged DataFragment calm := by
  intro o present
  simp only [calm, Finset.mem_insert, Finset.mem_singleton] at present
  rcases present with rfl | rfl
  · exact Or.inl ⟨_, rfl⟩
  · exact Or.inr ⟨quiet, quiet_mem, rfl⟩

theorem busy_tagged : Tagged DataFragment busy := by
  intro o present
  simp only [busy, Finset.mem_insert, Finset.mem_singleton] at present
  rcases present with rfl | rfl
  · exact Or.inl ⟨_, rfl⟩
  · exact Or.inr ⟨quiet, quiet_mem, rfl⟩

/-- `quiet`, reading its code and making row `2`. -/
def quietFiring : Firing ℕ Ext (Stored DataFragment) calm.frame :=
  storedFiring quiet_mem calm.frame (shift 10) ⟨[], [1], [2]⟩ []

/-- **Without a token, `quiet` fires.** -/
theorem quiet_admitted : quietFiring.Admits X calm := by
  have information : quietFiring.information X calm = [(ruleCode quiet, ruleCode quiet)] := by decide
  refine ⟨⟨fresh_shift quietFiring rfl (by decide), by decide, by decide, rfl, rfl, rfl, rfl⟩,
    by decide, ⟨PUnit.unit, var, ?_⟩, ?_⟩
  · rw [information]
    intro e inside
    simp only [List.mem_singleton] at inside
    subst inside
    rfl
  · intro b σ _
    refine (holds_iff quietFiring rfl σ).mpr ?_
    intro c inside
    simp only [quietFiring, storedFiring, stored, quiet, List.mem_singleton] at inside
    subst inside
    intro o present equated
    simp only [calm, Finset.mem_insert, Finset.mem_singleton] at present
    rw [row_eq] at equated
    have equated' : nf (subst σ (obj (tok (var 10)))) = nf (subst σ (calm.label o)) := equated
    rcases present with rfl | rfl
    · have label : calm.label 0 = obj (key five) := rfl
      rw [label] at equated'
      simp [obj, tok, key, five, subst, nf] at equated'
    · have label : calm.label 1 = ruleCode quiet := rfl
      rw [label, subst_ruleCode quiet_mem.1, nf_ruleCode quiet_mem.1, subst_obj, nf_obj] at equated'
      exact obj_ne_code _ _ equated'

/-- **Through the interpreter, at the store without a token.** -/
theorem interpreter_quiet :
    ∃ u, InterpSucc calm u ∧ Represents DataFragment (quietFiring.result X calm) u ∧ 2 ∈ u.present := by
  obtain ⟨u, moved, rep⟩ := (bisimulation dataFragment_closed (represents_refl calm_tagged)).1 _
    ⟨quietFiring, quiet_admitted, rfl⟩
  refine ⟨u, moved, rep, ?_⟩
  rw [rep.present]
  decide

/-- **With a token present, every firing of `quiet` is refused**, whatever its opening: freshness gives a
solution sending the rule's `x` to the token's value. -/
theorem quiet_refused (f : Firing ℕ Ext (Stored DataFragment) busy.frame)
    (isQuiet : f.rule = stored quiet) : ¬ f.Admits X busy := by
  obtain ⟨rule, member, ext, ι, sel, seen⟩ := f
  subst isQuiet
  rintro ⟨⟨fresh, -, -, takeLength, readLength, -, -⟩, enabled, solvable, asks⟩
  have takenNil : sel.taken = [] := List.length_eq_zero_iff.mp (takeLength : 0 = sel.taken.length).symm
  have readLength' : 0 + 1 = sel.read.length := readLength
  obtain ⟨c₀, rest, reads, restLength⟩ := exists_cons_of_length readLength'
  have restNil : rest = [] := List.length_eq_zero_iff.mp restLength.symm
  subst restNil
  have present := present_of_enabled enabled
  have c₀present : c₀ ∈ busy.present := present c₀ (by simp [reads])
  -- the solution that sends every unknown of the rule to five
  obtain ⟨u, onState, onRule⟩ := fresh PUnit.unit var (fun _ => five)
  have labelEq : ∀ t, busy.Mentions t → nf (subst u t) = nf t := by
    intro t mentions
    have same := onState t mentions
    have same' : nf (subst u (subst var t)) = nf (subst var t) := same
    rw [subst_var] at same'
    exact same'
  -- the read row is the code: otherwise the information has no solution
  have codeRow : busy.label c₀ = ruleCode quiet := by
    obtain ⟨_, τ, solved⟩ := solvable
    have readsF := ((models_information _ takeLength readLength τ).mp solved).2.2.1
    have readsF' : List.Forall₂ (fun p o => nf (subst τ (subst ι p)) = nf (subst τ (busy.label o)))
        [ruleCode quiet] [c₀] := by
      rw [← reads]
      exact readsF
    have codeRead := (List.forall₂_cons.mp readsF').1
    rw [subst_ruleCode quiet_mem.1, subst_ruleCode quiet_mem.1, nf_ruleCode quiet_mem.1] at codeRead
    simp only [busy, Finset.mem_insert, Finset.mem_singleton] at c₀present
    rcases c₀present with rfl | rfl
    · have label : busy.label 0 = obj (tok five) := rfl
      rw [label, subst_obj, nf_obj] at codeRead
      exact absurd codeRead.symm (obj_ne_code _ _)
    · rfl
  have solvedU : X.Models (a := busy.frame) (b := PUnit.unit) u
      ((⟨stored quiet, member, ext, ι, sel, seen⟩ : Firing ℕ Ext (Stored DataFragment) busy.frame).information
        X busy) := by
    refine (models_information _ takeLength readLength u).mpr ⟨by simp [busy], ?_, ?_, ?_⟩
    · show List.Forall₂ _ ([] : List Expr) sel.taken
      rw [takenNil]
      exact List.Forall₂.nil
    · show List.Forall₂ (fun p o => nf (subst u (subst ι p)) = nf (subst u (busy.label o)))
        [ruleCode quiet] sel.read
      rw [reads]
      refine List.Forall₂.cons ?_ List.Forall₂.nil
      show nf (subst u (subst ι (ruleCode quiet))) = nf (subst u (busy.label c₀))
      rw [codeRow, subst_ruleCode quiet_mem.1, subst_ruleCode quiet_mem.1]
    · intro e inside
      simp [stored, quiet] at inside
  have holds := (holds_iff _ rfl u).mp (asks PUnit.unit u solvedU) (.predicate .none (obj (tok (var 0))))
    (by simp [stored, quiet])
  have pattern : nf (subst u (subst ι (obj (tok (var 0))))) = nf (subst (fun _ => five) (obj (tok (var 0)))) :=
    onRule (obj (tok (var 0))) (by simp [Rule.terms, stored, quiet, checkTerms])
  have tokenLabel : nf (subst u (busy.label 0)) = obj (tok five) := by
    rw [labelEq _ (Or.inr (Or.inr ⟨0, by simp [busy], rfl⟩))]
    rfl
  refine holds 0 (by simp [busy]) ?_
  show nf (subst u (subst ι (obj (tok (var 0))))) = nf (subst u (Firing.row X busy _ 0))
  rw [row_eq, pattern, tokenLabel]
  rfl

/-- **With a token present, the interpreter does nothing**: the only code there is `quiet`'s, and every
firing of `quiet` is refused. -/
theorem interpreter_idle_at_busy (g : Firing ℕ Ext U busy.frame) : ¬ g.Admits X busy := by
  intro admitted
  obtain ⟨f, admittedF, -, -⟩ := backward dataFragment_closed (represents_refl busy_tagged) g admitted
  obtain ⟨r, hr, hf⟩ := stored_cases f
  have admittedF' := admittedF
  rw [hf] at admittedF'
  obtain ⟨c₀, present, coded⟩ := code_present dataFragment_closed busy_tagged hr admittedF'
  simp only [busy, Finset.mem_insert, Finset.mem_singleton] at present
  rcases present with rfl | rfl
  · have label : busy.label 0 = obj (tok five) := rfl
    rw [label] at coded
    exact obj_ne_code _ _ coded
  · have label : busy.label 1 = ruleCode quiet := rfl
    rw [label] at coded
    have sameRule : quiet = r := ruleCode_injective coded
    subst sameRule
    exact quiet_refused f (by rw [hf]; rfl) admittedF

/-! ## Count -/

/-- **Read a key `y`; when exactly one row is the key `y`, make done.** -/
def single : Rule Tm :=
  ⟨PUnit.unit, ⟨[], [obj (key (var 0))], [], [.count (obj (key (var 0))) 1], [obj done]⟩, []⟩

theorem single_mem : single ∈ DataFragment :=
  ⟨fragment_of_check rfl, fun m inside => by
    simp only [single, List.mem_singleton] at inside
    exact ⟨_, inside⟩⟩

/-- The labels of a store with one key five and the code of `single`. -/
def oneKeyLabel (o : ℕ) : Expr := if o = 0 then obj (key five) else if o = 1 then ruleCode single else nil

/-- **One key five.** -/
def oneKey : State Tm ℕ := ⟨PUnit.unit, [], {0, 1}, oneKeyLabel⟩

/-- The labels of a store with two keys five and the code of `single`. -/
def twoKeysLabel (o : ℕ) : Expr :=
  if o = 0 then obj (key five) else if o = 1 then ruleCode single else if o = 2 then obj (key five) else nil

/-- **Two keys five.** -/
def twoKeys : State Tm ℕ := ⟨PUnit.unit, [], {0, 1, 2}, twoKeysLabel⟩

theorem oneKey_tagged : Tagged DataFragment oneKey := by
  intro o present
  simp only [oneKey, Finset.mem_insert, Finset.mem_singleton] at present
  rcases present with rfl | rfl
  · exact Or.inl ⟨_, rfl⟩
  · exact Or.inr ⟨single, single_mem, rfl⟩

/-- `single` reading its code and the key at row `0`, making row `3`. -/
def singleFiring (s : State Tm ℕ) : Firing ℕ Ext (Stored DataFragment) s.frame :=
  storedFiring single_mem s.frame (shift 10) ⟨[], [1, 0], [3]⟩ []

/-- Every solution of `single`'s information sends its `y` to five. -/
theorem single_solution {s : State Tm ℕ} (key0 : s.label 0 = obj (key five)) {σ : ℕ → Expr}
    (solved : X.Models (a := s.frame) (b := PUnit.unit) σ ((singleFiring s).information X s)) :
    nf (σ 10) = five := by
  have readsF := ((models_information (singleFiring s) rfl rfl σ).mp solved).2.2.1
  have keyRead := (List.forall₂_cons.mp (List.forall₂_cons.mp readsF).2).1
  have keyRead' : nf (subst σ (obj (key (var 10)))) = nf (subst σ (s.label 0)) := keyRead
  rw [key0] at keyRead'
  simp [obj, key, five, subst, nf] at keyRead'
  exact keyRead'

/-- **With one key five, `single` fires.** -/
theorem single_admitted : (singleFiring oneKey).Admits X oneKey := by
  have information : (singleFiring oneKey).information X oneKey =
      [(ruleCode single, ruleCode single), (obj (key (var 10)), obj (key five))] := by decide
  refine ⟨⟨fresh_shift (singleFiring oneKey) rfl (by decide), by decide, by decide, rfl, rfl, rfl, rfl⟩,
    by decide, ⟨PUnit.unit, fun _ => five, ?_⟩, ?_⟩
  · rw [information]
    intro e inside
    simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
    rcases inside with rfl | rfl <;> rfl
  · intro b σ solved
    have value := single_solution rfl solved
    refine (holds_iff (singleFiring oneKey) rfl σ).mpr ?_
    intro c inside
    simp only [singleFiring, storedFiring, stored, single, List.mem_singleton] at inside
    subst inside
    show (matchesAt X (b := PUnit.unit) σ (Firing.row X oneKey (singleFiring oneKey)) oneKey.present
      (subst (shift 10) (obj (key (var 0))))).card = 1
    have matched : matchesAt X (b := PUnit.unit) σ (Firing.row X oneKey (singleFiring oneKey)) oneKey.present
        (subst (shift 10) (obj (key (var 0)))) = {0} := by
      ext o
      rw [mem_matchesAt, row_eq]
      simp only [oneKey, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨present, equated⟩
        have equated' : nf (subst σ (obj (key (var 10)))) = nf (subst σ (oneKey.label o)) := equated
        rcases present with rfl | rfl
        · rfl
        · exfalso
          have label : oneKey.label 1 = ruleCode single := rfl
          rw [label, subst_ruleCode single_mem.1, nf_ruleCode single_mem.1, subst_obj, nf_obj] at equated'
          exact obj_ne_code _ _ equated'
      · rintro rfl
        refine ⟨Or.inl rfl, ?_⟩
        show nf (subst σ (obj (key (var 10)))) = nf (subst σ (oneKey.label 0))
        have label : oneKey.label 0 = obj (key five) := rfl
        rw [label]
        simp only [obj, key, subst, nf]
        rw [value]
        rfl
    rw [matched]
    rfl

/-- **Through the interpreter, with one key five.** -/
theorem interpreter_single :
    ∃ u, InterpSucc oneKey u ∧ Represents DataFragment ((singleFiring oneKey).result X oneKey) u ∧
      3 ∈ u.present := by
  obtain ⟨u, moved, rep⟩ := (bisimulation dataFragment_closed (represents_refl oneKey_tagged)).1 _
    ⟨singleFiring oneKey, single_admitted, rfl⟩
  refine ⟨u, moved, rep, ?_⟩
  rw [rep.present]
  decide

/-- **With two keys five, the same firing is refused**: the count is two at every solution. -/
theorem single_refused : ¬ (singleFiring twoKeys).Admits X twoKeys := by
  rintro ⟨-, -, -, asks⟩
  have information : (singleFiring twoKeys).information X twoKeys =
      [(ruleCode single, ruleCode single), (obj (key (var 10)), obj (key five))] := by decide
  have solved : X.Models (a := twoKeys.frame) (b := PUnit.unit) (fun _ => five)
      ((singleFiring twoKeys).information X twoKeys) := by
    rw [information]
    intro e inside
    simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
    rcases inside with rfl | rfl <;> rfl
  have holds := (holds_iff (singleFiring twoKeys) rfl _).mp (asks PUnit.unit _ solved)
    (.count (obj (key (var 0))) 1) (by simp [singleFiring, storedFiring, stored, single])
  have matched : matchesAt X (b := PUnit.unit) (fun _ => five) (Firing.row X twoKeys (singleFiring twoKeys))
      twoKeys.present (subst (shift 10) (obj (key (var 0)))) = {0, 2} := by
    ext o
    rw [mem_matchesAt, row_eq]
    simp only [twoKeys, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨present, equated⟩
      rcases present with rfl | rfl | rfl
      · exact Or.inl rfl
      · exfalso
        have equated' : nf (subst (fun _ => five) (obj (key (var 10)))) =
            nf (subst (fun _ => five) (twoKeys.label 1)) := equated
        have label : twoKeys.label 1 = ruleCode single := rfl
        rw [label, subst_ruleCode single_mem.1, nf_ruleCode single_mem.1, subst_obj, nf_obj] at equated'
        exact obj_ne_code _ _ equated'
      · exact Or.inr rfl
    · rintro (rfl | rfl)
      · exact ⟨Or.inl rfl, rfl⟩
      · exact ⟨Or.inr (Or.inr rfl), rfl⟩
  have count : (matchesAt X (b := PUnit.unit) (fun _ => five) (Firing.row X twoKeys (singleFiring twoKeys))
      twoKeys.present (subst (shift 10) (obj (key (var 0))))).card = 1 := holds
  rw [matched] at count
  exact absurd count (by decide)

#print axioms quiet_admitted
#print axioms interpreter_quiet
#print axioms quiet_refused
#print axioms interpreter_idle_at_busy
#print axioms single_admitted
#print axioms interpreter_single
#print axioms single_refused

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RulesAsRows.Queries
