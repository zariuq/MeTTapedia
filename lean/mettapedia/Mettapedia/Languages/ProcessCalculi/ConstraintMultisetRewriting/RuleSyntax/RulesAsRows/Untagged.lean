import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RulesAsRows.Gating

/-!
# Why stores must be tagged: an unknown row read as a code; and the tags along runs

The bisimulation of the interpreter with the stored-rule program holds on stores tagged through their
knowledge: every row a data row at every solution, or made by every solution the code of one rule of
the fragment (`SemTagged`). This module shows the hypothesis is needed, and how it travels along runs.

**The tags exclude an unknown row** (`loose_not_semTagged`): the store below, whose knowledge allows
every value of its row `var 7`, is not tagged through its knowledge.

**The store** (`loose`): row `0` is the store's unknown `var 7`, row `1` is the data row `obj a`.

**The interpreter reads the unknown row as a code** (`loose_admitted`): its one-take rule reads row `0`
by its code pattern and takes row `1`. The code read binds `var 7` to a code whose take entry is the
interpreter's own unknown, and that entry is constrained only by the take. Two solutions of the result
send `var 7` to the codes of two different rules: "take `obj a`" (`solution_takeA`) and "take any row"
(`solution_takeAny`).

**No stored firing matches it** (`loose_unmatched`): every admitted firing of the stored-rule program
with the same selection reads row `0` against the ground code of its own rule, so every solution of
its result sends `var 7` to that one code. The interpreter's result has solutions with two different
values there, so no solution correspondence on the rows relates the two results.

**The tags along runs.**
* Every row the interpreter makes is a `drop` (`interp_made_drop`), so after an interpreter firing that
  makes a row no set of rules tags its store by syntax (`interp_result_untagged`, with an instance,
  `interp_result_untagged_exists`).
* That is harmless: the tags are asked of the specification's side, and an interpreter store that
  represents a store, for a set of rules of the fragment, is itself tagged through its own knowledge
  (`Represents.semTagged_interp`), so it represents itself and the bisimulation restarts from it with
  no representative to exhibit (`interp_result_restarts`).
* The same holds of a store whose code row is an unknown that its knowledge binds to the body of a
  code (`looseCode`): tagged by no set of rules by syntax (`looseCode_untagged`), tagged through its
  knowledge (`looseCode_semTagged`), and represented by the store that writes the code literally
  (`literal_represents_loose`), so the interpreter from it is bisimilar to the stored-rule program
  (`loose_interpreter_covered`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RulesAsRows.Untagged

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)
open Expr
open Examples (DataFragment)

/-- A constant. -/
def a : Expr := sym 30

/-- **A store whose row `0` is an unknown.** -/
def loose : State Tm ℕ := ⟨PUnit.unit, [], {0, 1}, fun o => if o = 0 then var 7 else obj a⟩

/-- The interpreter's shape with one take. -/
def oneTake : Shape := ⟨1, 0, 0, 0, [], 0⟩

/-- The interpreter reading row `0` as a code and taking row `1`. -/
def looseFiring : Firing ℕ Ext U loose.frame :=
  interpFiring oneTake loose.frame (shift 10) ⟨[1], [0], []⟩ []

/-- The code read by the interpreter, opened: its take entry is the unknown `var 11`. -/
def openedCode : Expr := code (lst [lst [var 11], nil, nil, nil, nil, nil, nil, nil, nil])

theorem looseFiring_information :
    looseFiring.information X loose = [(drop (var 11) (var 10), obj a), (openedCode, var 7)] := by
  decide

/-- **Take `obj a`.** -/
def takeA : Rule Tm := ⟨PUnit.unit, ⟨[obj a], [], [], [], []⟩, []⟩

/-- **Take any row.** -/
def takeAny : Rule Tm := ⟨PUnit.unit, ⟨[var 0], [], [], [], []⟩, []⟩

/-- A solution sending the take entry to the quotation of `obj a`. -/
def σA : ℕ → Expr := fun v => if v = 7 then ruleCode takeA else if v = 11 then obj a else nil

/-- A solution sending the take entry to the quotation of an unknown, and the environment to `[obj a]`. -/
def σAny : ℕ → Expr := fun v =>
  if v = 7 then ruleCode takeAny else if v = 11 then slot 0 0 else if v = 10 then lst [obj a] else nil

theorem solution_takeA : action.Models σA (looseFiring.information X loose) := by
  rw [looseFiring_information]
  intro e inside
  simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
  rcases inside with rfl | rfl <;> rfl

theorem solution_takeAny : action.Models σAny (looseFiring.information X loose) := by
  rw [looseFiring_information]
  intro e inside
  simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
  rcases inside with rfl | rfl <;> rfl

theorem takeA_code_ne : ruleCode takeA ≠ ruleCode takeAny := by decide

/-- **The interpreter reads the unknown row as a code and fires.** -/
theorem loose_admitted : looseFiring.Admits X loose := by
  refine ⟨⟨fresh_shift looseFiring rfl (by decide), by decide, by decide, rfl, rfl, rfl, rfl⟩,
    by decide, ⟨PUnit.unit, σA, solution_takeA⟩, ?_⟩
  intro b σ _
  refine (holds_iff looseFiring rfl σ).mpr ?_
  intro c inside
  simp [looseFiring, interpFiring, interp, oneTake] at inside

/-- **Its result leaves the read code undetermined**: two solutions send `var 7` to the codes of two
different rules. -/
theorem loose_undetermined :
    action.Models σA (looseFiring.result X loose).knowledge ∧
      action.Models σAny (looseFiring.result X loose).knowledge ∧
      nf (subst σA (var 7)) = ruleCode takeA ∧ nf (subst σAny (var 7)) = ruleCode takeAny :=
  ⟨solution_takeA, solution_takeAny, by decide, by decide⟩

/-- **No admitted firing of the stored-rule program with the same selection matches the interpreter's
result**: each determines the value of row `0` to be the code of its own rule. -/
theorem loose_unmatched (f : Firing ℕ Ext (Stored DataFragment) loose.frame) (admitted : f.Admits X loose)
    (same : f.selection = looseFiring.selection) :
    ¬ ∀ σ, action.Models σ (looseFiring.result X loose).knowledge →
      ∃ σ', action.Models σ' (f.result X loose).knowledge ∧
        ∀ o ∈ (f.result X loose).present,
          nf (subst σ ((looseFiring.result X loose).label o)) = nf (subst σ' ((f.result X loose).label o)) := by
  intro forth
  obtain ⟨r, hr, hf⟩ := stored_cases f
  rw [hf] at admitted forth
  have frag := hr.1
  -- every solution of the stored firing's information sends `var 7` to the code of its rule
  have determined : ∀ σ', action.Models σ' ((storedFiring hr loose.frame f.opening f.selection f.seen).information
      X loose) → nf (σ' 7) = ruleCode r := by
    intro σ' solved
    have readsF := ((models_information _ admitted.1.2.2.2.1 admitted.1.2.2.2.2.1 σ').mp solved).2.2.1
    have reads : f.selection.read = [0] := by rw [same]; rfl
    have readsF' : List.Forall₂ (fun p o => nf (subst σ' (subst f.opening p)) = nf (subst σ' (loose.label o)))
        (ruleCode r :: r.body.read) [0] := by
      rw [← reads]
      exact readsF
    have codeRead := (List.forall₂_cons.mp readsF').1
    rw [subst_ruleCode frag, subst_ruleCode frag, nf_ruleCode frag] at codeRead
    exact codeRead.symm
  have present : (0 : ℕ) ∈ ((storedFiring hr loose.frame f.opening f.selection f.seen).result X loose).present := by
    show 0 ∈ fire loose.present (f.selection.commit (T := Unit))
    rw [same]
    decide
  have notMade : (0 : ℕ) ∉ (storedFiring hr loose.frame f.opening f.selection f.seen).selection.made := by
    show 0 ∉ f.selection.made
    rw [same]
    simp [looseFiring, interpFiring]
  have labelF : ((storedFiring hr loose.frame f.opening f.selection f.seen).result X loose).label 0 = var 7 := by
    rw [Firing.result_label_other _ notMade]
    rfl
  have labelG : (looseFiring.result X loose).label 0 = var 7 := by decide
  obtain ⟨σ₁, solved₁, values₁⟩ := forth σA solution_takeA
  obtain ⟨σ₂, solved₂, values₂⟩ := forth σAny solution_takeAny
  have one := values₁ 0 present
  have two := values₂ 0 present
  rw [labelG, labelF] at one two
  have codeOne : ruleCode takeA = ruleCode r := by
    have := determined σ₁ solved₁
    rw [← this]
    exact one
  have codeTwo : ruleCode takeAny = ruleCode r := by
    have := determined σ₂ solved₂
    rw [← this]
    exact two
  exact takeA_code_ne (codeOne.trans codeTwo.symm)

theorem takeA_mem : takeA ∈ DataFragment :=
  ⟨Examples.fragment_of_check rfl, fun m inside => by simp [takeA] at inside⟩

/-- The stored rule "take `obj a`", reading row `0` as its code, with the interpreter's selection. -/
def takeAFiring : Firing ℕ Ext (Stored DataFragment) loose.frame :=
  storedFiring takeA_mem loose.frame (shift 10) ⟨[1], [0], []⟩ []

/-- **Stored firings with that selection exist** (so `loose_unmatched` is not vacuous): "take `obj a`"
reads the unknown row as its code, binding it. -/
theorem takeA_admitted : takeAFiring.Admits X loose ∧ takeAFiring.selection = looseFiring.selection := by
  have information : takeAFiring.information X loose = [(obj a, obj a), (ruleCode takeA, var 7)] := by
    decide
  refine ⟨⟨⟨fresh_shift takeAFiring rfl (by decide), by decide, by decide, rfl, rfl, rfl, rfl⟩,
    by decide, ⟨PUnit.unit, σA, ?_⟩, ?_⟩, rfl⟩
  · rw [information]
    intro e inside
    simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
    rcases inside with rfl | rfl <;> rfl
  · intro b σ _
    refine (holds_iff takeAFiring rfl σ).mpr ?_
    intro c inside
    simp [takeAFiring, storedFiring, stored, takeA] at inside

/-- **The loose store is not tagged through its knowledge**: its knowledge allows every value of
`var 7`, so its row is neither a data row nor one code at every solution. -/
theorem loose_not_semTagged : ¬ SemTagged DataFragment loose := by
  intro tagged
  have present : (0 : ℕ) ∈ loose.present := by decide
  have known : action.Models (fun _ => sym 3) loose.knowledge := fun e inside =>
    absurd inside List.not_mem_nil
  have label : loose.label 0 = var 7 := rfl
  rcases tagged 0 present with data | ⟨r, hr, coded⟩
  · obtain ⟨t, same⟩ := data _ known
    rw [label] at same
    exact Expr.noConfusion same
  · have value := coded.value hr.1 known
    rw [label] at value
    exact Expr.noConfusion value

#print axioms takeA_admitted
#print axioms loose_admitted
#print axioms loose_undetermined
#print axioms loose_unmatched
#print axioms loose_not_semTagged

/-! ## The tags along runs -/

section AlongRuns

variable {O : Type*} [DecidableEq O]

omit [DecidableEq O] in
theorem exists_zip_right {α β : Type*} : ∀ {l₁ : List α} {l₂ : List β}, l₁.length = l₂.length →
    ∀ {a : α}, a ∈ l₁ → ∃ b, (a, b) ∈ l₁.zip l₂
  | [], _, _, _, inside => absurd inside List.not_mem_nil
  | _ :: _, [], lengths, _, _ => by simp at lengths
  | _ :: _, y :: _, lengths, _, inside => by
      rcases List.mem_cons.mp inside with rfl | later
      · exact ⟨y, by simp⟩
      · obtain ⟨b, pair⟩ := exists_zip_right (Nat.succ.inj lengths) later
        exact ⟨b, by simp [pair]⟩

omit [DecidableEq O] in
/-- **Every row the interpreter makes is a drop.** -/
theorem interp_made_drop {u : State Tm O} (g : Firing O Ext U u.frame) {t : Expr}
    (inside : t ∈ (g.opened X).produce) : ∃ c e, t = drop c e := by
  obtain ⟨rule, ⟨sh, rfl⟩, ext, opening, selection, seen⟩ := g
  have mapped : t ∈ (openedColumn sh 2).map (subst opening) := inside
  obtain ⟨p, member, rfl⟩ := List.mem_map.mp mapped
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp member
  exact ⟨_, _, rfl⟩

/-- **After an interpreter firing that makes a row, no set of rules tags the store by its syntax.** -/
theorem interp_result_untagged {u : State Tm O} (g : Firing O Ext U u.frame) (admitted : g.Admits X u)
    {o : O} (made : o ∈ g.selection.made) (F : Set (Rule Tm)) : ¬ Tagged F (g.result X u) := by
  intro tagged
  obtain ⟨-, -, -, -, -, madeLength, -⟩ := admitted.1
  have lengths : g.selection.made.length = (g.opened X).produce.length := by
    simp only [Firing.opened, RuleInstance.map, List.length_map]
    exact madeLength.symm
  obtain ⟨t, pair⟩ := exists_zip_right lengths made
  have label := Firing.result_label_made g admitted.1 pair
  have present : o ∈ (g.result X u).present :=
    mem_fire.mpr (Or.inr (by simpa [Selection.commit] using made))
  obtain ⟨c, e, isDrop⟩ := interp_made_drop g (List.of_mem_zip pair).2
  rcases tagged o present with ⟨t', same⟩ | ⟨r, -, same⟩
  · rw [label, isDrop] at same
    simp [obj] at same
  · rw [label, isDrop] at same
    simp [ruleCode, code] at same

end AlongRuns

/-- **Such firings exist, and the bisimulation restarts from their results**: interpreting the
installer from its tagged store makes a row; the result is tagged by no set of rules by syntax, yet
through its knowledge, so it represents itself. -/
theorem interp_result_restarts :
    ∃ g : Firing ℕ Ext U RunTime.before.frame, g.Admits X RunTime.before ∧
      (∀ F : Set (Rule Tm), ¬ Tagged F (g.result X RunTime.before)) ∧
      SemTagged RunTime.InstallFragment (g.result X RunTime.before) ∧
      Represents RunTime.InstallFragment (g.result X RunTime.before) (g.result X RunTime.before) := by
  obtain ⟨g, admitted, same, rep⟩ := forward RunTime.installFragment_closed
    (represents_refl RunTime.before_tagged) RunTime.installFiring RunTime.installFiring_admitted
  have tags := rep.semTagged_interp RunTime.installFragment_closed.fragment
  refine ⟨g, admitted, fun F => interp_result_untagged g admitted (o := 2) ?_ F, tags,
    represents_refl_sem tags⟩
  rw [same]
  decide

/-- **The same, without the representation**: a firing of the interpreter whose result no set of
rules tags by syntax. -/
theorem interp_result_untagged_exists :
    ∃ g : Firing ℕ Ext U RunTime.before.frame, g.Admits X RunTime.before ∧
      ∀ F : Set (Rule Tm), ¬ Tagged F (g.result X RunTime.before) := by
  obtain ⟨g, admitted, untagged, -⟩ := interp_result_restarts
  exact ⟨g, admitted, untagged⟩

/-! ## A code row whose unknown the knowledge binds -/

/-- The body of the code of `second`. -/
def secondBody : Expr := lst ((List.range 9).map fun k => lst ((partsAt Examples.second k).map quote))

theorem code_secondBody : code secondBody = ruleCode Examples.second := rfl

theorem secondBody_closed : secondBody.closed = true := by decide

/-- An interpreter store whose row is `code (var 9)`, with the knowledge `9 = body of second`. -/
def looseCode : State Tm ℕ := ⟨PUnit.unit, [(var 9, secondBody)], {0}, fun _ => code (var 9)⟩

/-- The same knowledge, the row written as the code of `second`. -/
def literalCode : State Tm ℕ := ⟨PUnit.unit, [(var 9, secondBody)], {0}, fun _ => ruleCode Examples.second⟩

theorem lst_ne_var (l : List Expr) (v : ℕ) : lst l ≠ var v := by
  cases l <;> simp [lst, nil]

/-- **No set of rules tags the store by syntax.** -/
theorem looseCode_untagged (G : Set (Rule Tm)) : ¬ Tagged G looseCode := by
  intro tagged
  rcases tagged 0 (Finset.mem_singleton_self 0) with ⟨t, same⟩ | ⟨r, -, same⟩
  · exact obj_ne_code t (var 9) same.symm
  · exact lst_ne_var _ 9 (Expr.cell.inj same).2.symm

theorem value_of_known (σ : ℕ → Expr) (known : action.Models σ [(var 9, secondBody)]) :
    nf (σ 9) = secondBody := by
  have bound : nf (subst σ (var 9)) = nf (subst σ secondBody) := known _ List.mem_cons_self
  rw [subst_of_closed σ secondBody_closed, nf_of_closed secondBody_closed] at bound
  exact bound

/-- The row's value at every solution of the knowledge is the code of `second`. -/
theorem looseCode_value (σ : ℕ → Expr) (known : action.Models σ [(var 9, secondBody)]) :
    nf (subst σ (code (var 9))) = nf (subst σ (ruleCode Examples.second)) := by
  show code (nf (σ 9)) = _
  rw [value_of_known σ known, subst_ruleCode Examples.second_mem.1, nf_ruleCode Examples.second_mem.1]
  rfl

/-- **The knowledge makes the row the code of `second`**: the store is tagged through its knowledge. -/
theorem looseCode_semTagged : SemTagged DataFragment looseCode :=
  fun _ _ => Or.inr ⟨Examples.second, Examples.second_mem, looseCode_value⟩

/-- **The untagged interpreter store is represented by the tagged one.** -/
theorem literal_represents_loose : Represents DataFragment literalCode looseCode := by
  refine ⟨rfl, Tagged.sem (F := DataFragment) (s := literalCode)
    (fun _ _ => Or.inr ⟨Examples.second, Examples.second_mem, rfl⟩), ?_, ?_⟩
  · intro σ known
    exact ⟨σ, known, fun _ _ => looseCode_value σ known⟩
  · intro σ known
    exact ⟨σ, known, fun _ _ => looseCode_value σ known⟩

/-- **Hence the interpreter from the untagged store is bisimilar to the stored-rule program from the
tagged one**, and from itself through its knowledge. -/
theorem loose_interpreter_covered :
    ((∀ s', StoredSucc DataFragment literalCode s' → ∃ u', InterpSucc looseCode u' ∧
        Represents DataFragment s' u') ∧
      (∀ u', InterpSucc looseCode u' → ∃ s', StoredSucc DataFragment literalCode s' ∧
        Represents DataFragment s' u')) ∧
    ((∀ s', StoredSucc DataFragment looseCode s' → ∃ u', InterpSucc looseCode u' ∧
        Represents DataFragment s' u') ∧
      (∀ u', InterpSucc looseCode u' → ∃ s', StoredSucc DataFragment looseCode s' ∧
        Represents DataFragment s' u')) :=
  ⟨bisimulation Examples.dataFragment_closed literal_represents_loose,
    bisimulation Examples.dataFragment_closed (represents_refl_sem looseCode_semTagged)⟩

#print axioms interp_made_drop
#print axioms interp_result_untagged
#print axioms interp_result_restarts
#print axioms interp_result_untagged_exists
#print axioms looseCode_untagged
#print axioms looseCode_semTagged
#print axioms literal_represents_loose
#print axioms loose_interpreter_covered

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RulesAsRows.Untagged
