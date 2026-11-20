import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RulesAsRows.Interpreter

/-!
# The interpreter simulates the stored-rule program, both ways, firing for firing

Fix a set `F` of rules of the fragment, closed under what its rules make (`ClosedFragment`). The
stored-rule program `Stored F` and the interpreter `U` run on the same stores.

**The representation** (`Represents F s u`): the two states have the same present occurrences; every
row of `s` is, through `s`'s knowledge, a data row or the code of a rule of `F` (`SemTagged`: a data
row at every solution of the knowledge, or a row that every solution makes the code of one rule
`r`, `CodedAt`); and their knowledge has the same solutions on the labels: every solution of `u`'s
knowledge has a solution of `s`'s knowledge with the same label values (in normal form), and
conversely (`forth`, `back`). A store whose rows are literally data rows or codes (`Tagged`) is tagged
through its knowledge (`Tagged.sem`), and every such state represents itself (`represents_refl`,
`represents_refl_sem`). The tags are asked of the specification's side only: the interpreter's store
is related to it through the knowledge.

**The theorems.**
* `forward`: every admitted firing of `Stored F` at `s` is matched by an admitted firing of `U` at `u`
  with the same selection (same taken, read and made occurrences), and the results are represented.
* `backward`: every admitted firing of `U` at `u` is matched by an admitted firing of `Stored F` at `s`
  with the same selection, and the results are represented. So `U` has no extra behaviour.
* `bisimulation`: hence `Represents F` is a strong bisimulation between the two steps' successor
  relations, and runs are matched step for step in both directions (`runs_forward`,
  `runs_backward`). No administrative firings: one object firing is one interpreter firing.

**How the interpreter's firing is matched** (`Agree`, `information_transfer`, `holds_transfer`,
`labels_transfer`): a solution of the interpreter's information and a solution of the object
information correspond when they agree on the knowledge, the labels, the code read, and each opened
entry. Every solution on one side has a corresponding one on the other (`agree_of_interp`,
`agree_of_stored`), built from the freshness of each side's opening: from the interpreter's side, the
object values are the entries of the environment (`objectOf`); from the object side, the environment
holds the object values (`uInst`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RulesAsRows

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)
open LogicOverTheStep.StepSpan (Succ)
open Expr

variable {O : Type*}

/-! ## Firings of the two programs -/

/-- The firing of a stored rule with an opening, a selection and seen sets. -/
def storedFiring {F : Set (Rule Tm)} {r : Rule Tm} (hr : r ∈ F) (a : PUnit.{1}) (opening : ℕ → Expr)
    (selection : Selection O) (seen : List (Finset O)) : Firing O Ext (Stored F) a :=
  ⟨stored r, ⟨r, hr, rfl⟩, PUnit.unit, opening, selection, seen⟩

/-- The firing of an interpreter rule with an opening, a selection and seen sets. -/
def interpFiring (sh : Shape) (a : PUnit.{1}) (opening : ℕ → Expr) (selection : Selection O)
    (seen : List (Finset O)) : Firing O Ext U a :=
  ⟨interp sh, ⟨sh, rfl⟩, PUnit.unit, opening, selection, seen⟩

theorem stored_cases {F : Set (Rule Tm)} {a : PUnit.{1}} (f : Firing O Ext (Stored F) a) :
    ∃ (r : Rule Tm) (hr : r ∈ F), f = storedFiring hr a f.opening f.selection f.seen := by
  obtain ⟨rule, ⟨r, hr, rfl⟩, ext, opening, selection, seen⟩ := f
  exact ⟨r, hr, rfl⟩

theorem interp_cases {a : PUnit.{1}} (g : Firing O Ext U a) :
    ∃ sh, g = interpFiring sh a g.opening g.selection g.seen := by
  obtain ⟨rule, ⟨sh, rfl⟩, ext, opening, selection, seen⟩ := g
  exact ⟨sh, rfl⟩

/-! ## The information and the guards at one frame -/

theorem row_eq {P : Program Tm} {s : State Tm O} (f : Firing O Ext P s.frame) : f.row X s = s.label :=
  funext fun o => subst_var (s.label o)

/-- **The solutions of a firing's information**: solutions of the knowledge that equate each opened
take and read pattern with its row and solve each opened tell. -/
theorem models_information {P : Program Tm} {s : State Tm O} (f : Firing O Ext P s.frame)
    (takeLength : f.rule.body.take.length = f.selection.taken.length)
    (readLength : f.rule.body.read.length = f.selection.read.length) (τ : ℕ → Expr) :
    X.Models (a := s.frame) (b := PUnit.unit) τ (f.information X s) ↔
      action.Models τ s.knowledge ∧
      List.Forall₂ (fun p o => nf (subst τ (subst f.opening p)) = nf (subst τ (s.label o)))
        f.rule.body.take f.selection.taken ∧
      List.Forall₂ (fun p o => nf (subst τ (subst f.opening p)) = nf (subst τ (s.label o)))
        f.rule.body.read f.selection.read ∧
      ∀ e ∈ f.rule.body.tell, nf (subst τ (subst f.opening e.1)) = nf (subst τ (subst f.opening e.2)) := by
  have knowledgeEq : X.applyStore (Ext.weaken f.ext) s.knowledge = s.knowledge :=
    Frames.applyStore_id (X := X) s.knowledge
  have takes : X.Models (a := s.frame) (b := PUnit.unit) τ (f.matching X s (f.opened X).take f.selection.taken) ↔
      List.Forall₂ (fun p o => nf (subst τ (subst f.opening p)) = nf (subst τ (s.label o)))
        f.rule.body.take f.selection.taken := by
    unfold Firing.matching
    rw [row_eq f]
    exact (Selection.models_equations_iff action τ s.label
      (by simpa [Firing.opened, RuleInstance.map] using takeLength)).trans List.forall₂_map_left_iff
  have reads : X.Models (a := s.frame) (b := PUnit.unit) τ (f.matching X s (f.opened X).read f.selection.read) ↔
      List.Forall₂ (fun p o => nf (subst τ (subst f.opening p)) = nf (subst τ (s.label o)))
        f.rule.body.read f.selection.read := by
    unfold Firing.matching
    rw [row_eq f]
    exact (Selection.models_equations_iff action τ s.label
      (by simpa [Firing.opened, RuleInstance.map] using readLength)).trans List.forall₂_map_left_iff
  have tells : X.Models (a := s.frame) (b := PUnit.unit) τ (f.opened X).tell ↔
      ∀ e ∈ f.rule.body.tell, nf (subst τ (subst f.opening e.1)) = nf (subst τ (subst f.opening e.2)) := by
    show (∀ e ∈ f.rule.body.tell.map fun pair => (subst f.opening pair.1, subst f.opening pair.2),
      nf (subst τ e.1) = nf (subst τ e.2)) ↔ _
    exact List.forall_mem_map
  unfold Firing.information
  rw [Frames.models_append, Frames.models_append, Frames.models_append, knowledgeEq, takes, reads,
    tells]
  exact ⟨fun ⟨⟨⟨k, t⟩, r⟩, e⟩ => ⟨k, t, r, e⟩, fun ⟨k, t, r, e⟩ => ⟨⟨⟨k, t⟩, r⟩, e⟩⟩

/-- **The guards of a collect-free firing**: each check, opened, at the solution. -/
theorem holds_iff {P : Program Tm} {s : State Tm O} (f : Firing O Ext P s.frame)
    (collect : f.rule.collect = []) (σ : ℕ → Expr) :
    f.Holds X s (b := PUnit.unit) σ ↔
      ∀ c ∈ f.rule.body.checks,
        checkHolds X (b := PUnit.unit) σ (f.row X s) s.present (c.map (subst f.opening)) := by
  unfold Firing.Holds Firing.collectOpened
  rw [collect]
  constructor
  · rintro ⟨checks, -⟩ c inside
    exact checks _ (List.mem_map.mpr ⟨c, inside, rfl⟩)
  · intro checks
    refine ⟨fun c inside => ?_, fun q inside => by simp at inside⟩
    obtain ⟨c', member, rfl⟩ := List.mem_map.mp inside
    exact checks c' member

/-- **The guard predicate of a firing**: each check, opened, at the solution, and each collect pattern,
opened, seeing exactly its claimed rows. -/
theorem holds_iff_full {P : Program Tm} {s : State Tm O} (f : Firing O Ext P s.frame) (σ : ℕ → Expr) :
    f.Holds X s (b := PUnit.unit) σ ↔
      (∀ c ∈ f.rule.body.checks,
        checkHolds X (b := PUnit.unit) σ (f.row X s) s.present (c.map (subst f.opening))) ∧
      ∀ q ∈ (f.rule.collect.map (subst f.opening)).zip f.seen,
        matchesAt X (b := PUnit.unit) σ (f.row X s) s.present q.1 = q.2 := by
  unfold Firing.Holds Firing.collectOpened
  refine and_congr ⟨fun all c inside => all _ (List.mem_map.mpr ⟨c, inside, rfl⟩), fun all c inside => ?_⟩
    Iff.rfl
  obtain ⟨c', member, rfl⟩ := List.mem_map.mp inside
  exact all c' member

/-! ## Index facts -/

theorem forall_mem_iff_index {α : Type*} {l : List α} {P : α → Prop} :
    (∀ a ∈ l, P a) ↔ ∀ (i : ℕ) (inside : i < l.length), P l[i] :=
  ⟨fun all i inside => all _ (List.getElem_mem inside), fun all a member => by
    obtain ⟨i, inside, rfl⟩ := List.mem_iff_getElem.mp member
    exact all i inside⟩

theorem forall₂_transfer {l : List O} {pg pf : List Expr} {Rg Rf : Expr → O → Prop}
    (lengths : pg.length = pf.length)
    (each : ∀ (i : ℕ) (hg : i < pg.length) (hf : i < pf.length) (o : O), o ∈ l → (Rg pg[i] o ↔ Rf pf[i] o)) :
    List.Forall₂ Rg pg l ↔ List.Forall₂ Rf pf l := by
  constructor
  · intro related
    have lengthL := related.length_eq
    refine forall₂_of_index (lengths ▸ lengthL) fun i hf hl => ?_
    have hg : i < pg.length := lengths ▸ hf
    exact (each i hg hf l[i] (List.getElem_mem hl)).mp (index_of_forall₂ related i hg hl)
  · intro related
    have lengthL := related.length_eq
    refine forall₂_of_index (lengths.trans lengthL) fun i hg hl => ?_
    have hf : i < pf.length := lengths ▸ hg
    exact (each i hg hf l[i] (List.getElem_mem hl)).mpr (index_of_forall₂ related i hf hl)

theorem length_openedColumn (sh : Shape) (k : ℕ) : (openedColumn sh k).length = sh.len k := by
  simp [openedColumn]

theorem getElem_openedColumn (sh : Shape) (k : ℕ) {i : ℕ} (inside : i < (openedColumn sh k).length) :
    (openedColumn sh k)[i] = opened (slotVar k i) := by
  simp [openedColumn]

/-! ## Terms of the two rules -/

/-- **A part entry of a stored rule is one of its terms, or a closed constant.** -/
theorem mem_stored_terms_or_closed {r : Rule Tm} {k : ℕ} (hk : k < 9) (hk7 : k ≠ 7) {p : Expr}
    (inside : p ∈ partsAt r k) : p ∈ (stored r).terms ∨ p.closed := by
  have terms : ∀ {t : Expr}, (t ∈ r.body.take ∨ t ∈ ruleCode r :: r.body.read ∨
      t ∈ r.body.tell.map Prod.fst ∨ t ∈ r.body.tell.map Prod.snd ∨
      t ∈ r.body.checks.flatMap checkTerms ∨ t ∈ r.body.produce ∨ t ∈ r.collect) →
        t ∈ (stored r).terms := by
    intro t member
    unfold Rule.terms
    simp only [stored, List.mem_append]
    tauto
  match k, hk, hk7 with
  | 0, _, _ => exact Or.inl (terms (Or.inl inside))
  | 1, _, _ => exact Or.inl (terms (Or.inr (Or.inl (List.mem_cons_of_mem _ inside))))
  | 2, _, _ => exact Or.inl (terms (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl inside)))))))
  | 3, _, _ => exact Or.inl (terms (Or.inr (Or.inr (Or.inl inside))))
  | 4, _, _ => exact Or.inl (terms (Or.inr (Or.inr (Or.inr (Or.inl inside)))))
  | 5, _, _ =>
      obtain ⟨c, member, rfl⟩ := List.mem_map.mp inside
      refine Or.inl (terms (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        (List.mem_flatMap.mpr ⟨c, member, ?_⟩)))))))
      cases c <;> simp [checkTerms, Check.pattern]
  | 6, _, _ =>
      obtain ⟨c, member, rfl⟩ := List.mem_map.mp inside
      cases c with
      | equal left right =>
          exact Or.inl (terms (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
            (List.mem_flatMap.mpr ⟨_, member, by simp [checkTerms, guardRight]⟩)))))))
      | predicate quantifier _ => exact Or.inr rfl
      | count _ _ => exact Or.inr rfl
  | 7, _, h7 => exact absurd rfl h7
  | 8, _, _ => exact Or.inl (terms (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr inside)))))))
  | _ + 9, outside, _ => omega

/-- **An opened entry of an interpreter rule is one of its terms**, the second terms of the checks
when the check is an equation. -/
theorem mem_interp_terms (sh : Shape) {k : ℕ} (hk : k < 9) (hk7 : k ≠ 7) {i : ℕ} (inside : i < sh.len k)
    (equal : k = 6 → sh.kinds[i]? = some Kind.equal) :
    opened (slotVar k i) ∈ (interp sh).terms := by
  have column : opened (slotVar k i) ∈ openedColumn sh k :=
    List.mem_map.mpr ⟨i, List.mem_range.mpr inside, rfl⟩
  have terms : ∀ {t : Expr}, (t ∈ openedColumn sh 0 ∨ t ∈ codePattern sh :: openedColumn sh 1 ∨
      t ∈ ((openedColumn sh 3).zip (openedColumn sh 4)).map Prod.fst ∨
      t ∈ ((openedColumn sh 3).zip (openedColumn sh 4)).map Prod.snd ∨
      t ∈ (sh.kinds.mapIdx fun i k => k.check (opened (slotVar 5 i)) (opened (slotVar 6 i))).flatMap
        checkTerms ∨ t ∈ openedColumn sh 2 ∨ t ∈ openedColumn sh 8) → t ∈ (interp sh).terms := by
    intro t member
    unfold Rule.terms
    simp only [interp, List.mem_append]
    tauto
  have checkAt : ∀ (j : ℕ) (hj : j < sh.kinds.length),
      (sh.kinds[j]).check (opened (slotVar 5 j)) (opened (slotVar 6 j)) ∈
        sh.kinds.mapIdx (fun i k => k.check (opened (slotVar 5 i)) (opened (slotVar 6 i))) := by
    intro j hj
    have below : j < (sh.kinds.mapIdx fun i k =>
        k.check (opened (slotVar 5 i)) (opened (slotVar 6 i))).length := by simpa using hj
    have member := List.getElem_mem below
    rw [List.getElem_mapIdx] at member
    exact member
  match k, hk, hk7 with
  | 0, _, _ => exact terms (Or.inl column)
  | 1, _, _ => exact terms (Or.inr (Or.inl (List.mem_cons_of_mem _ column)))
  | 2, _, _ => exact terms (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl column))))))
  | 3, _, _ =>
      refine terms (Or.inr (Or.inr (Or.inl ?_)))
      rw [List.map_fst_zip (by simp [length_openedColumn, Shape.len])]
      exact column
  | 4, _, _ =>
      refine terms (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
      rw [List.map_snd_zip (by simp [length_openedColumn, Shape.len])]
      exact column
  | 5, _, _ =>
      have hj : i < sh.kinds.length := inside
      refine terms (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        (List.mem_flatMap.mpr ⟨_, checkAt i hj, ?_⟩))))))
      cases sh.kinds[i] <;> simp [Kind.check, checkTerms]
  | 6, _, _ =>
      have hj : i < sh.kinds.length := inside
      have kindEq : sh.kinds[i] = Kind.equal := by
        have known := equal rfl
        rw [List.getElem?_eq_getElem hj] at known
        exact Option.some.inj known
      refine terms (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        (List.mem_flatMap.mpr ⟨_, checkAt i hj, ?_⟩))))))
      rw [kindEq]
      simp [Kind.check, checkTerms]
  | 7, _, h7 => exact absurd rfl h7
  | 8, _, _ => exact terms (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr column))))))
  | _ + 9, outside, _ => omega

theorem codePattern_mem_interp_terms (sh : Shape) : codePattern sh ∈ (interp sh).terms := by
  unfold Rule.terms
  simp [interp]

/-! ## Tagged stores and the representation -/

/-- **A store of the stored-rule program, by its syntax**: every present row is a data row or the code
of a rule of `F`. -/
def Tagged (F : Set (Rule Tm)) (s : State Tm O) : Prop :=
  ∀ o ∈ s.present, (∃ t, s.label o = obj t) ∨ ∃ r ∈ F, s.label o = ruleCode r

/-- **A row that the knowledge makes the code of `r`**: at every solution of the knowledge, the row's
value is the value of the code of `r`. -/
def CodedAt (s : State Tm O) (o : O) (r : Rule Tm) : Prop :=
  ∀ σ, action.Models σ s.knowledge → nf (subst σ (s.label o)) = nf (subst σ (ruleCode r))

/-- **A store of the stored-rule program, read through its knowledge**: every present row is a data row
at every solution of the knowledge, or the knowledge makes it the code of one rule of `F`. -/
def SemTagged (F : Set (Rule Tm)) (s : State Tm O) : Prop :=
  ∀ o ∈ s.present, (∀ σ, action.Models σ s.knowledge → ∃ t, nf (subst σ (s.label o)) = obj t) ∨
    ∃ r ∈ F, CodedAt s o r

/-- **A store tagged by its syntax is tagged through its knowledge.** -/
theorem Tagged.sem {F : Set (Rule Tm)} {s : State Tm O} (tagged : Tagged F s) : SemTagged F s :=
  fun o present => (tagged o present).imp
    (fun ⟨t, same⟩ σ _ => ⟨nf (subst σ t), by rw [same]; rfl⟩)
    (fun ⟨r, hr, same⟩ => ⟨r, hr, fun σ _ => by rw [same]⟩)

/-- The value of a coded row, for a rule of the fragment. -/
theorem CodedAt.value {s : State Tm O} {o : O} {r : Rule Tm} (coded : CodedAt s o r) (frag : Fragment r)
    {σ : ℕ → Expr} (known : action.Models σ s.knowledge) : nf (subst σ (s.label o)) = ruleCode r := by
  rw [coded σ known, subst_ruleCode frag, nf_ruleCode frag]

/-- **The representation**: the same present occurrences, a store tagged through its knowledge, and
knowledge with the same solutions on the labels, in both directions. -/
structure Represents (F : Set (Rule Tm)) (s u : State Tm O) : Prop where
  present : u.present = s.present
  tagged : SemTagged F s
  forth : ∀ σ, action.Models σ u.knowledge → ∃ σ', action.Models σ' s.knowledge ∧
    ∀ o ∈ s.present, nf (subst σ (u.label o)) = nf (subst σ' (s.label o))
  back : ∀ σ', action.Models σ' s.knowledge → ∃ σ, action.Models σ u.knowledge ∧
    ∀ o ∈ s.present, nf (subst σ (u.label o)) = nf (subst σ' (s.label o))

/-- **Every store tagged through its knowledge represents itself.** -/
theorem represents_refl_sem {F : Set (Rule Tm)} {s : State Tm O} (tagged : SemTagged F s) :
    Represents F s s :=
  ⟨rfl, tagged, fun σ known => ⟨σ, known, fun _ _ => rfl⟩, fun σ known => ⟨σ, known, fun _ _ => rfl⟩⟩

/-- **Every tagged store represents itself.** -/
theorem represents_refl {F : Set (Rule Tm)} {s : State Tm O} (tagged : Tagged F s) :
    Represents F s s :=
  represents_refl_sem tagged.sem

/-- **A store that represents a store is tagged through its own knowledge**, for a set of rules of the
fragment: every solution of its knowledge corresponds to a solution of the represented store's, with
the same row values. So an interpreter store reached from a represented one represents itself
(`represents_refl_sem`). -/
theorem Represents.semTagged_interp {F : Set (Rule Tm)} (frag : ∀ r ∈ F, Fragment r) {s u : State Tm O}
    (rep : Represents F s u) : SemTagged F u := by
  intro o present
  have presentS : o ∈ s.present := rep.present ▸ present
  rcases rep.tagged o presentS with data | ⟨r, hr, coded⟩
  · refine Or.inl fun σ known => ?_
    obtain ⟨σ', knownS, labels⟩ := rep.forth σ known
    obtain ⟨t, same⟩ := data σ' knownS
    exact ⟨t, (labels o presentS).trans same⟩
  · refine Or.inr ⟨r, hr, fun σ known => ?_⟩
    obtain ⟨σ', knownS, labels⟩ := rep.forth σ known
    rw [labels o presentS, coded.value (frag r hr) knownS, subst_ruleCode (frag r hr),
      nf_ruleCode (frag r hr)]

/-! ## Corresponding solutions -/

/-- **Corresponding solutions** of the interpreter's information (`τ`, opening `ιU`) and of the object
information (`τ'`, opening `ιP`) for the rule `r`. -/
structure Agree (r : Rule Tm) (s u : State Tm O) (ιP ιU τ' τ : ℕ → Expr) : Prop where
  knowledgeU : action.Models τ u.knowledge
  knowledgeS : action.Models τ' s.knowledge
  labels : ∀ o ∈ s.present, nf (subst τ (u.label o)) = nf (subst τ' (s.label o))
  code : nf (subst τ (subst ιU (codePattern (shapeOf r)))) = ruleCode r
  entries : ∀ k, k < 9 → k ≠ 7 → ∀ (i : ℕ) (inside : i < (partsAt r k).length),
    nf (subst τ (subst ιU (opened (slotVar k i)))) = nf (subst τ' (subst ιP ((partsAt r k)[i])))

section Transfer

variable {F : Set (Rule Tm)} {r : Rule Tm} (hr : r ∈ F) (frag : Fragment r) {s u : State Tm O}
  {ιP ιU τ' τ : ℕ → Expr} {sel : Selection O} {seenP seenU : List (Finset O)}

include hr frag in
/-- **Corresponding solutions solve both informations or neither.** -/
theorem information_transfer (agree : Agree r s u ιP ιU τ' τ) {c₀ : O} {rest : List O}
    (reads : sel.read = c₀ :: rest) (coded : CodedAt s c₀ r)
    (present : ∀ o ∈ sel.taken ++ sel.read, o ∈ s.present)
    (takeLength : r.body.take.length = sel.taken.length) (readLength : r.body.read.length = rest.length) :
    X.Models (a := u.frame) (b := PUnit.unit) τ ((interpFiring (shapeOf r) u.frame ιU sel seenU).information X u) ↔
      X.Models (a := s.frame) (b := PUnit.unit) τ' ((storedFiring hr s.frame ιP sel seenP).information X s) := by
  have gTake : (openedColumn (shapeOf r) 0).length = sel.taken.length := by
    rw [length_openedColumn]
    exact takeLength
  have gRead : (codePattern (shapeOf r) :: openedColumn (shapeOf r) 1).length = sel.read.length := by
    rw [reads, List.length_cons, List.length_cons, length_openedColumn]
    exact congrArg (· + 1) readLength
  have fRead : (ruleCode r :: r.body.read).length = sel.read.length := by
    rw [reads, List.length_cons, List.length_cons]
    exact congrArg (· + 1) readLength
  rw [models_information (interpFiring (shapeOf r) u.frame ιU sel seenU) gTake gRead τ,
    models_information (storedFiring hr s.frame ιP sel seenP) takeLength fRead τ']
  show (action.Models τ u.knowledge ∧
      List.Forall₂ (fun p o => nf (subst τ (subst ιU p)) = nf (subst τ (u.label o)))
        (openedColumn (shapeOf r) 0) sel.taken ∧
      List.Forall₂ (fun p o => nf (subst τ (subst ιU p)) = nf (subst τ (u.label o)))
        (codePattern (shapeOf r) :: openedColumn (shapeOf r) 1) sel.read ∧
      ∀ e ∈ (openedColumn (shapeOf r) 3).zip (openedColumn (shapeOf r) 4),
        nf (subst τ (subst ιU e.1)) = nf (subst τ (subst ιU e.2))) ↔
    (action.Models τ' s.knowledge ∧
      List.Forall₂ (fun p o => nf (subst τ' (subst ιP p)) = nf (subst τ' (s.label o)))
        r.body.take sel.taken ∧
      List.Forall₂ (fun p o => nf (subst τ' (subst ιP p)) = nf (subst τ' (s.label o)))
        (ruleCode r :: r.body.read) sel.read ∧
      ∀ e ∈ r.body.tell, nf (subst τ' (subst ιP e.1)) = nf (subst τ' (subst ιP e.2)))
  have c₀present : c₀ ∈ s.present := present c₀ (List.mem_append_right _ (reads ▸ List.mem_cons_self))
  refine and_congr (iff_of_true agree.knowledgeU agree.knowledgeS) (and_congr ?_ (and_congr ?_ ?_))
  · -- takes
    refine forall₂_transfer (by rw [length_openedColumn]; rfl) fun i hg hf o member => ?_
    have entry := agree.entries 0 (by decide) (by decide) i hf
    have label := agree.labels o (present o (List.mem_append_left _ member))
    show nf (subst τ (subst ιU (openedColumn (shapeOf r) 0)[i])) = nf (subst τ (u.label o)) ↔
      nf (subst τ' (subst ιP (r.body.take[i]))) = nf (subst τ' (s.label o))
    rw [getElem_openedColumn, entry, label]
    rfl
  · -- reads: the code read holds on both sides, the other reads correspond
    rw [reads, List.forall₂_cons, List.forall₂_cons]
    have codeG : nf (subst τ (subst ιU (codePattern (shapeOf r)))) = nf (subst τ (u.label c₀)) := by
      rw [agree.code, agree.labels c₀ c₀present, coded.value frag agree.knowledgeS]
    have codeF : nf (subst τ' (subst ιP (ruleCode r))) = nf (subst τ' (s.label c₀)) := by
      rw [subst_ruleCode frag ιP, subst_ruleCode frag τ', nf_ruleCode frag,
        coded.value frag agree.knowledgeS]
    refine and_congr (iff_of_true codeG codeF) ?_
    refine forall₂_transfer (by rw [length_openedColumn]; rfl) fun i hg hf o member => ?_
    have entry := agree.entries 1 (by decide) (by decide) i hf
    have label := agree.labels o (present o (List.mem_append_right _ (reads ▸ List.mem_cons_of_mem _ member)))
    show nf (subst τ (subst ιU (openedColumn (shapeOf r) 1)[i])) = nf (subst τ (u.label o)) ↔
      nf (subst τ' (subst ιP (r.body.read[i]))) = nf (subst τ' (s.label o))
    rw [getElem_openedColumn, entry, label]
    rfl
  · -- tells
    rw [forall_mem_iff_index, forall_mem_iff_index]
    have zipLength : ((openedColumn (shapeOf r) 3).zip (openedColumn (shapeOf r) 4)).length =
        r.body.tell.length := by
      simp [length_openedColumn, Shape.len, shapeOf]
    constructor
    · intro all i inside
      have inside' : i < ((openedColumn (shapeOf r) 3).zip (openedColumn (shapeOf r) 4)).length :=
        zipLength ▸ inside
      have holds := all i inside'
      have inside3 : i < (partsAt r 3).length := by simpa [partsAt, parts] using inside
      have inside4 : i < (partsAt r 4).length := by simpa [partsAt, parts] using inside
      rw [List.getElem_zip, getElem_openedColumn, getElem_openedColumn,
        agree.entries 3 (by decide) (by decide) i inside3,
        agree.entries 4 (by decide) (by decide) i inside4] at holds
      simpa [partsAt, parts] using holds
    · intro all i inside'
      have inside : i < r.body.tell.length := zipLength ▸ inside'
      have holds := all i inside
      have inside3 : i < (partsAt r 3).length := by simpa [partsAt, parts] using inside
      have inside4 : i < (partsAt r 4).length := by simpa [partsAt, parts] using inside
      rw [List.getElem_zip, getElem_openedColumn, getElem_openedColumn,
        agree.entries 3 (by decide) (by decide) i inside3,
        agree.entries 4 (by decide) (by decide) i inside4]
      simpa [partsAt, parts] using holds

include hr in
/-- **Corresponding solutions see the same rows matched by corresponding patterns.** -/
theorem matchesAt_transfer (agree : Agree r s u ιP ιU τ' τ) (presentSame : u.present = s.present)
    {x p : Expr} (value : nf (subst τ x) = nf (subst τ' p)) :
    matchesAt X (b := PUnit.unit) τ (Firing.row X u (interpFiring (shapeOf r) u.frame ιU sel seenU))
        u.present x =
      matchesAt X (b := PUnit.unit) τ' (Firing.row X s (storedFiring hr s.frame ιP sel seenP))
        s.present p := by
  ext o
  rw [mem_matchesAt, mem_matchesAt, presentSame, row_eq, row_eq]
  constructor
  · rintro ⟨present, equated⟩
    refine ⟨present, ?_⟩
    have equated' : nf (subst τ x) = nf (subst τ (u.label o)) := equated
    show nf (subst τ' p) = nf (subst τ' (s.label o))
    rw [← value, ← agree.labels o present]
    exact equated'
  · rintro ⟨present, equated⟩
    refine ⟨present, ?_⟩
    have equated' : nf (subst τ' p) = nf (subst τ' (s.label o)) := equated
    show nf (subst τ x) = nf (subst τ (u.label o))
    rw [value, agree.labels o present]
    exact equated'

include hr in
/-- **Corresponding solutions pass the guards of both firings or of neither**: equations, none checks and
counts check by check, and each collect pattern sees the same rows. -/
theorem holds_transfer (agree : Agree r s u ιP ιU τ' τ) (presentSame : u.present = s.present)
    {seen : List (Finset O)} :
    (interpFiring (shapeOf r) u.frame ιU sel seen).Holds X u (b := PUnit.unit) τ ↔
      (storedFiring hr s.frame ιP sel seen).Holds X s (b := PUnit.unit) τ' := by
  rw [holds_iff_full, holds_iff_full]
  have value5 : ∀ (i : ℕ) (inside : i < r.body.checks.length),
      nf (subst τ (subst ιU (opened (slotVar 5 i)))) =
        nf (subst τ' (subst ιP (Check.pattern r.body.checks[i]))) := by
    intro i inside
    have inside5 : i < (partsAt r 5).length := by simpa [partsAt, parts] using inside
    rw [agree.entries 5 (by decide) (by decide) i inside5]
    simp [partsAt, parts]
  have value6 : ∀ (i : ℕ) (inside : i < r.body.checks.length),
      nf (subst τ (subst ιU (opened (slotVar 6 i)))) =
        nf (subst τ' (subst ιP (guardRight r.body.checks[i]))) := by
    intro i inside
    have inside6 : i < (partsAt r 6).length := by simpa [partsAt, parts] using inside
    rw [agree.entries 6 (by decide) (by decide) i inside6]
    simp [partsAt, parts]
  apply and_congr
  · show (∀ c ∈ (shapeOf r).kinds.mapIdx (fun i k => k.check (opened (slotVar 5 i)) (opened (slotVar 6 i))),
        checkHolds X (b := PUnit.unit) τ (Firing.row X u (interpFiring (shapeOf r) u.frame ιU sel seen))
          u.present (c.map (subst ιU))) ↔
      ∀ c ∈ r.body.checks, checkHolds X (b := PUnit.unit) τ'
        (Firing.row X s (storedFiring hr s.frame ιP sel seen)) s.present (c.map (subst ιP))
    rw [forall_mem_iff_index, forall_mem_iff_index]
    have lengths : ((shapeOf r).kinds.mapIdx fun i k =>
        k.check (opened (slotVar 5 i)) (opened (slotVar 6 i))).length = r.body.checks.length := by
      simp [shapeOf]
    have each : ∀ (i : ℕ) (inside : i < r.body.checks.length),
        checkHolds X (b := PUnit.unit) τ (Firing.row X u (interpFiring (shapeOf r) u.frame ιU sel seen))
            u.present (((kindOf r.body.checks[i]).check (opened (slotVar 5 i))
              (opened (slotVar 6 i))).map (subst ιU)) ↔
          checkHolds X (b := PUnit.unit) τ' (Firing.row X s (storedFiring hr s.frame ιP sel seen))
            s.present ((r.body.checks[i]).map (subst ιP)) := by
      intro i inside
      have v5 := value5 i inside
      have v6 := value6 i inside
      generalize r.body.checks[i] = c at v5 v6 ⊢
      cases c with
      | equal left right =>
          show nf (subst τ (subst ιU (opened (slotVar 5 i)))) =
              nf (subst τ (subst ιU (opened (slotVar 6 i)))) ↔
            nf (subst τ' (subst ιP left)) = nf (subst τ' (subst ιP right))
          rw [v5, v6]
          rfl
      | predicate quantifier pattern =>
          show quantifier.Holds u.present (fun o => nf (subst τ (subst ιU (opened (slotVar 5 i)))) =
              nf (subst τ (Firing.row X u (interpFiring (shapeOf r) u.frame ιU sel seen) o))) ↔
            quantifier.Holds s.present (fun o => nf (subst τ' (subst ιP pattern)) =
              nf (subst τ' (Firing.row X s (storedFiring hr s.frame ιP sel seen) o)))
          rw [presentSame, row_eq, row_eq, v5]
          exact quantifier.holds_congr fun o present => by
            have label := agree.labels o present
            show (nf (subst τ' (subst ιP pattern)) = nf (subst τ (u.label o))) ↔ _
            rw [label]
      | count pattern number =>
          show (matchesAt X (b := PUnit.unit) τ (Firing.row X u (interpFiring (shapeOf r) u.frame ιU sel seen))
              u.present (subst ιU (opened (slotVar 5 i)))).card = number ↔
            (matchesAt X (b := PUnit.unit) τ' (Firing.row X s (storedFiring hr s.frame ιP sel seen))
              s.present (subst ιP pattern)).card = number
          rw [matchesAt_transfer hr agree presentSame (seenP := seen) (seenU := seen) v5]
          rfl
    have kind : ∀ (i : ℕ) (inside : i < (shapeOf r).kinds.length),
        (shapeOf r).kinds[i] = kindOf (r.body.checks[i]'(by simpa [shapeOf] using inside)) := by
      intro i inside
      simp [shapeOf]
    constructor
    · intro all i inside
      have inside' : i < ((shapeOf r).kinds.mapIdx fun i k =>
          k.check (opened (slotVar 5 i)) (opened (slotVar 6 i))).length := lengths ▸ inside
      have holds := all i inside'
      rw [List.getElem_mapIdx, kind] at holds
      exact (each i inside).mp holds
    · intro all i inside'
      have inside : i < r.body.checks.length := lengths ▸ inside'
      rw [List.getElem_mapIdx, kind]
      exact (each i inside).mpr (all i inside)
  · show (∀ q ∈ ((openedColumn (shapeOf r) 8).map (subst ιU)).zip seen,
        matchesAt X (b := PUnit.unit) τ (Firing.row X u (interpFiring (shapeOf r) u.frame ιU sel seen))
          u.present q.1 = q.2) ↔
      ∀ q ∈ (r.collect.map (subst ιP)).zip seen,
        matchesAt X (b := PUnit.unit) τ' (Firing.row X s (storedFiring hr s.frame ιP sel seen))
          s.present q.1 = q.2
    rw [forall_mem_iff_index, forall_mem_iff_index]
    have each : ∀ (j : ℕ) (inside : j < r.collect.length),
        matchesAt X (b := PUnit.unit) τ (Firing.row X u (interpFiring (shapeOf r) u.frame ιU sel seen))
            u.present (subst ιU (opened (slotVar 8 j))) =
          matchesAt X (b := PUnit.unit) τ' (Firing.row X s (storedFiring hr s.frame ιP sel seen))
            s.present (subst ιP (r.collect[j])) := by
      intro j inside
      have inside8 : j < (partsAt r 8).length := by simpa [partsAt, parts] using inside
      refine matchesAt_transfer hr agree presentSame ?_
      rw [agree.entries 8 (by decide) (by decide) j inside8]
      rfl
    have lengths : (((openedColumn (shapeOf r) 8).map (subst ιU)).zip seen).length =
        ((r.collect.map (subst ιP)).zip seen).length := by
      simp [length_openedColumn, Shape.len, shapeOf]
    constructor
    · intro all j inside
      have inside' := lengths ▸ inside
      have holds := all j inside'
      have below : j < r.collect.length := by simp at inside; omega
      rw [List.getElem_zip, List.getElem_map, getElem_openedColumn, each j below] at holds
      rw [List.getElem_zip, List.getElem_map]
      exact holds
    · intro all j inside'
      have inside : j < ((r.collect.map (subst ιP)).zip seen).length := lengths ▸ inside'
      have holds := all j inside
      have below : j < r.collect.length := by simp at inside; omega
      rw [List.getElem_zip, List.getElem_map] at holds
      rw [List.getElem_zip, List.getElem_map, getElem_openedColumn, each j below]
      exact holds

include hr in
/-- **Corresponding solutions give the results' rows the same values.** -/
theorem labels_transfer [DecidableEq O] (agree : Agree r s u ιP ιU τ' τ) (madeNodup : sel.made.Nodup)
    (madeLength : sel.made.length = r.body.produce.length) :
    ∀ o ∈ fire s.present (sel.commit (T := Unit)),
      nf (subst τ (((interpFiring (shapeOf r) u.frame ιU sel seenU).result X u).label o)) =
        nf (subst τ' (((storedFiring hr s.frame ιP sel seenP).result X s).label o)) := by
  intro o member
  by_cases made : o ∈ sel.made
  · obtain ⟨j, inside, rfl⟩ := List.mem_iff_getElem.mp made
    have gLength : sel.made.length = (openedColumn (shapeOf r) 2).length := by
      rw [length_openedColumn]
      exact madeLength
    have gLabel : ((interpFiring (shapeOf r) u.frame ιU sel seenU).result X u).label sel.made[j] =
        subst ιU (opened (slotVar 2 j)) := by
      have zipped := Firing.relabel_zip (Firing.row X u (interpFiring (shapeOf r) u.frame ιU sel seenU))
        sel.made ((openedColumn (shapeOf r) 2).map (subst ιU)) madeNodup (by simpa using gLength)
        (sel.made[j], subst ιU (opened (slotVar 2 j))) (by
          have below : j < (sel.made.zip ((openedColumn (shapeOf r) 2).map (subst ιU))).length := by
            simpa [gLength] using inside
          have entry := List.getElem_mem below
          rw [List.getElem_zip, List.getElem_map, getElem_openedColumn] at entry
          exact entry)
      exact zipped
    have fLabel : ((storedFiring hr s.frame ιP sel seenP).result X s).label sel.made[j] =
        subst ιP (r.body.produce[j]'(madeLength ▸ inside)) := by
      have zipped := Firing.relabel_zip (Firing.row X s (storedFiring hr s.frame ιP sel seenP))
        sel.made (r.body.produce.map (subst ιP)) madeNodup (by simpa using madeLength)
        (sel.made[j], subst ιP (r.body.produce[j]'(madeLength ▸ inside))) (by
          have below : j < (sel.made.zip (r.body.produce.map (subst ιP))).length := by
            simpa [madeLength] using inside
          have entry := List.getElem_mem below
          rw [List.getElem_zip, List.getElem_map] at entry
          exact entry)
      exact zipped
    rw [gLabel, fLabel]
    exact agree.entries 2 (by decide) (by decide) j (by simpa [partsAt, parts] using madeLength ▸ inside)
  · have gLabel : ((interpFiring (shapeOf r) u.frame ιU sel seenU).result X u).label o = u.label o :=
      (Firing.result_label_other _ made).trans (congrFun (row_eq _) o)
    have fLabel : ((storedFiring hr s.frame ιP sel seenP).result X s).label o = s.label o :=
      (Firing.result_label_other _ made).trans (congrFun (row_eq _) o)
    rw [gLabel, fLabel]
    have old : o ∈ s.present := by
      rcases mem_fire.mp member with ⟨present, -⟩ | fresh
      · exact present
      · exact absurd (by simpa [Selection.commit] using fresh) made
    exact agree.labels o old

end Transfer

/-! ## Every solution has a corresponding one -/

section Construction

variable {F : Set (Rule Tm)} {r : Rule Tm} (hr : r ∈ F) (frag : Fragment r) {s u : State Tm O}

include hr frag in
/-- **From a solution of the interpreter's information to a corresponding object solution**: the
object values are the entries of the environment. -/
theorem agree_of_interp (rep : Represents F s u) {ιP ιU : ℕ → Expr} {sel : Selection O}
    {seenP : List (Finset O)} (fresh : (storedFiring hr s.frame ιP sel seenP).Fresh X s)
    {c₀ : O} (coded : CodedAt s c₀ r) (c₀present : c₀ ∈ s.present) {τ : ℕ → Expr}
    (known : action.Models τ u.knowledge)
    (codeRead : nf (subst τ (subst ιU (codePattern (shapeOf r)))) = nf (subst τ (u.label c₀))) :
    ∃ τ', Agree r s u ιP ιU τ' τ := by
  obtain ⟨σ', knownS, labels⟩ := rep.forth τ known
  have code : nf (subst τ (subst ιU (codePattern (shapeOf r)))) = ruleCode r := by
    rw [codeRead, labels c₀ c₀present, coded.value frag knownS]
  have codeH : nf (subst (fun v => subst τ (ιU v)) (codePattern (shapeOf r))) = ruleCode r := by
    rw [← subst_subst]
    exact code
  obtain ⟨τ', onState, onRule⟩ := fresh PUnit.unit σ' (objectOf fun v => subst τ (ιU v))
  have agreeState : ∀ t, s.Mentions t → nf (subst τ' t) = nf (subst σ' t) := by
    intro t mentions
    have same := onState t mentions
    rwa [show X.act (Ext.weaken (storedFiring hr s.frame ιP sel seenP).ext) t = t from subst_var t] at same
  refine ⟨τ', ⟨known, fun e member => ?_, fun o present => ?_, code, fun k hk hk7 i inside => ?_⟩⟩
  · have left := agreeState e.1 (Or.inl (List.mem_map.mpr ⟨e, member, rfl⟩))
    have right := agreeState e.2 (Or.inr (Or.inl (List.mem_map.mpr ⟨e, member, rfl⟩)))
    show nf (subst τ' e.1) = nf (subst τ' e.2)
    rw [left, right]
    exact knownS e member
  · rw [labels o present, agreeState _ (Or.inr (Or.inr ⟨o, present, rfl⟩))]
  · obtain ⟨lengths, entries⟩ := decode codeH hk hk7
    have free := partsAt_dropFree frag (List.getElem_mem inside)
    have coded' := entries i (lengths ▸ inside)
    rw [subst_subst, nf_subst_opened_objectOf _ _ free coded']
    rcases mem_stored_terms_or_closed hk hk7 (List.getElem_mem inside) with member | closedP
    · exact (onRule _ member).symm
    · rw [subst_of_closed _ closedP, subst_of_closed _ closedP, subst_of_closed _ closedP]

include frag in
/-- **From an object solution to a corresponding solution of the interpreter's information**: the
environment holds the object values. -/
theorem agree_of_stored (rep : Represents F s u) {ιP ιU : ℕ → Expr} {sel : Selection O}
    {seenU : List (Finset O)} (fresh : (interpFiring (shapeOf r) u.frame ιU sel seenU).Fresh X u)
    {τ' : ℕ → Expr} (known : action.Models τ' s.knowledge) :
    ∃ τ, Agree r s u ιP ιU τ' τ := by
  obtain ⟨σ, knownU, labels⟩ := rep.back τ' known
  obtain ⟨τ, onState, onRule⟩ := fresh PUnit.unit σ (uInst r fun v => subst τ' (ιP v))
  have agreeState : ∀ t, u.Mentions t → nf (subst τ t) = nf (subst σ t) := by
    intro t mentions
    have same := onState t mentions
    rwa [show X.act (Ext.weaken (interpFiring (shapeOf r) u.frame ιU sel seenU).ext) t = t from
      subst_var t] at same
  have codeEq : nf (subst τ (subst ιU (codePattern (shapeOf r)))) =
      nf (subst (uInst r fun v => subst τ' (ιP v)) (codePattern (shapeOf r))) :=
    onRule _ (codePattern_mem_interp_terms _)
  refine ⟨τ, ⟨fun e member => ?_, known, fun o present => ?_, ?_, fun k hk hk7 i inside => ?_⟩⟩
  · have left := agreeState e.1 (Or.inl (List.mem_map.mpr ⟨e, member, rfl⟩))
    have right := agreeState e.2 (Or.inr (Or.inl (List.mem_map.mpr ⟨e, member, rfl⟩)))
    show nf (subst τ e.1) = nf (subst τ e.2)
    rw [left, right]
    exact knownU e member
  · have uPresent : o ∈ u.present := rep.present ▸ present
    rw [agreeState _ (Or.inr (Or.inr ⟨o, uPresent, rfl⟩)), labels o present]
  · rw [codeEq]
    exact nf_subst_uInst_codePattern frag _
  · by_cases closedP : ((partsAt r k)[i]).closed
    · -- a closed entry is fixed by the code read
      have codeH : nf (subst (fun v => subst τ (ιU v)) (codePattern (shapeOf r))) = ruleCode r := by
        rw [← subst_subst, codeEq]
        exact nf_subst_uInst_codePattern frag _
      obtain ⟨lengths, entries⟩ := decode codeH hk hk7
      have free := partsAt_dropFree frag (List.getElem_mem inside)
      have coded' := entries i (lengths ▸ inside)
      rw [subst_subst, nf_subst_opened_objectOf _ _ free coded', subst_of_closed _ closedP,
        subst_of_closed _ closedP, subst_of_closed _ closedP]
    · -- an entry that is not closed is opened in one of the interpreter rule's terms
      have equalKind : k = 6 → (shapeOf r).kinds[i]? = some Kind.equal := by
        intro six
        subst six
        have inside' : i < r.body.checks.length := by simpa [partsAt, parts] using inside
        have entry : (partsAt r 6)[i] = guardRight r.body.checks[i] := by simp [partsAt, parts]
        rw [entry] at closedP
        simp only [shapeOf, List.getElem?_map, List.getElem?_eq_getElem inside', Option.map_some]
        revert closedP
        cases r.body.checks[i] <;> simp [guardRight, kindOf, nil, closed]
      have member := mem_interp_terms (shapeOf r) hk hk7 (i := i) (by rw [len_shapeOf r hk]; exact inside)
        equalKind
      have entryEq : nf (subst τ (subst ιU (opened (slotVar k i)))) =
          nf (subst (uInst r fun v => subst τ' (ιP v)) (opened (slotVar k i))) := onRule _ member
      rw [entryEq, nf_subst_uInst_opened frag _ hk inside, subst_subst]

end Construction

/-! ## Admission and results correspond -/

section Correspondence

variable [DecidableEq O] {F : Set (Rule Tm)} {r : Rule Tm} (hr : r ∈ F) (frag : Fragment r)
  {s u : State Tm O} {ιP ιU : ℕ → Expr} {sel : Selection O} {seenP seenU : List (Finset O)}

/-- The hypotheses under which a firing of a stored rule and a firing of the interpreter with the same
selection are compared. -/
structure Comparable (r : Rule Tm) (s u : State Tm O) (sel : Selection O) (c₀ : O) (rest : List O) :
    Prop where
  reads : sel.read = c₀ :: rest
  coded : CodedAt s c₀ r
  present : ∀ o ∈ sel.taken ++ sel.read, o ∈ s.present
  takeLength : r.body.take.length = sel.taken.length
  readLength : r.body.read.length = rest.length
  madeLength : sel.made.length = r.body.produce.length
  takenNodup : sel.taken.Nodup
  madeNodup : sel.made.Nodup

include hr frag in
/-- **Admission corresponds.** With both openings fresh, the firing of the interpreter is admitted
exactly when the firing of the stored rule is. -/
theorem admits_transfer (rep : Represents F s u) {c₀ : O} {rest : List O}
    (comparable : Comparable r s u sel c₀ rest) {seen : List (Finset O)}
    (freshP : (storedFiring hr s.frame ιP sel seen).Fresh X s)
    (freshU : (interpFiring (shapeOf r) u.frame ιU sel seen).Fresh X u) :
    (interpFiring (shapeOf r) u.frame ιU sel seen).Admits X u ↔
      (storedFiring hr s.frame ιP sel seen).Admits X s := by
  have c₀present : c₀ ∈ s.present :=
    comparable.present c₀ (List.mem_append_right _ (comparable.reads ▸ List.mem_cons_self))
  have collectSame : (openedColumn (shapeOf r) 8).length = seen.length ↔ r.collect.length = seen.length := by
    rw [length_openedColumn]
    rfl
  have shapesG : r.collect.length = seen.length →
      (interpFiring (shapeOf r) u.frame ιU sel seen).Shapes X u := by
    intro collect
    refine ⟨freshU, comparable.takenNodup, comparable.madeNodup, ?_, ?_, ?_, collectSame.mpr collect⟩
    · show (openedColumn (shapeOf r) 0).length = sel.taken.length
      rw [length_openedColumn]
      exact comparable.takeLength
    · show (codePattern (shapeOf r) :: openedColumn (shapeOf r) 1).length = sel.read.length
      rw [comparable.reads, List.length_cons, List.length_cons, length_openedColumn]
      exact congrArg (· + 1) comparable.readLength
    · show (openedColumn (shapeOf r) 2).length = sel.made.length
      rw [length_openedColumn]
      exact comparable.madeLength.symm
  have shapesF : r.collect.length = seen.length → (storedFiring hr s.frame ιP sel seen).Shapes X s := by
    intro collect
    refine ⟨freshP, comparable.takenNodup, comparable.madeNodup, comparable.takeLength, ?_,
      comparable.madeLength.symm, collect⟩
    show (ruleCode r :: r.body.read).length = sel.read.length
    rw [comparable.reads, List.length_cons, List.length_cons]
    exact congrArg (· + 1) comparable.readLength
  have enabledSame : Enabled (fun _ : O => ()) u.present (sel.commit (T := Unit)) ↔
      Enabled (fun _ : O => ()) s.present (sel.commit (T := Unit)) := by
    rw [rep.present]
  -- the code read of any solution of the interpreter's information
  have codeOf : ∀ τ, X.Models (a := u.frame) (b := PUnit.unit) τ
      ((interpFiring (shapeOf r) u.frame ιU sel seen).information X u) →
        action.Models τ u.knowledge ∧
          nf (subst τ (subst ιU (codePattern (shapeOf r)))) = nf (subst τ (u.label c₀)) := by
    intro τ solved
    have gTake : (openedColumn (shapeOf r) 0).length = sel.taken.length := by
      rw [length_openedColumn]
      exact comparable.takeLength
    have gRead : (codePattern (shapeOf r) :: openedColumn (shapeOf r) 1).length = sel.read.length := by
      rw [comparable.reads, List.length_cons, List.length_cons, length_openedColumn]
      exact congrArg (· + 1) comparable.readLength
    obtain ⟨known, -, reads, -⟩ := (models_information _ gTake gRead τ).mp solved
    have reads' : List.Forall₂ (fun p o => nf (subst τ (subst ιU p)) = nf (subst τ (u.label o)))
        (codePattern (shapeOf r) :: openedColumn (shapeOf r) 1) (c₀ :: rest) := by
      rw [← comparable.reads]
      exact reads
    exact ⟨known, (List.forall₂_cons.mp reads').1⟩
  have fKnown : ∀ τ', X.Models (a := s.frame) (b := PUnit.unit) τ'
      ((storedFiring hr s.frame ιP sel seen).information X s) → action.Models τ' s.knowledge := by
    intro τ' solved
    have fRead : (ruleCode r :: r.body.read).length = sel.read.length := by
      rw [comparable.reads, List.length_cons, List.length_cons]
      exact congrArg (· + 1) comparable.readLength
    exact ((models_information _ comparable.takeLength fRead τ').mp solved).1
  constructor
  · rintro ⟨shapes, enabled, ⟨_, τ, solved⟩, asks⟩
    refine ⟨shapesF (collectSame.mp shapes.2.2.2.2.2.2), enabledSame.mp enabled, ?_, ?_⟩
    · obtain ⟨known, codeRead⟩ := codeOf τ solved
      obtain ⟨τ', agree⟩ := agree_of_interp hr frag rep freshP comparable.coded c₀present known codeRead
      exact ⟨PUnit.unit, τ', (information_transfer hr frag agree comparable.reads comparable.coded
        comparable.present comparable.takeLength comparable.readLength).mp solved⟩
    · intro b τ' solved
      obtain ⟨τ, agree⟩ := agree_of_stored frag rep freshU (fKnown τ' solved)
      have solvedG := (information_transfer hr frag agree comparable.reads comparable.coded
        comparable.present comparable.takeLength comparable.readLength (seenP := seen)
        (seenU := seen)).mpr solved
      exact (holds_transfer hr agree rep.present).mp (asks PUnit.unit τ solvedG)
  · rintro ⟨shapes, enabled, ⟨_, τ', solved⟩, asks⟩
    refine ⟨shapesG shapes.2.2.2.2.2.2, enabledSame.mpr enabled, ?_, ?_⟩
    · obtain ⟨τ, agree⟩ := agree_of_stored frag rep freshU (fKnown τ' solved)
      exact ⟨PUnit.unit, τ, (information_transfer hr frag agree comparable.reads comparable.coded
        comparable.present comparable.takeLength comparable.readLength (seenP := seen)
        (seenU := seen)).mpr solved⟩
    · intro b τ solved
      obtain ⟨known, codeRead⟩ := codeOf τ solved
      obtain ⟨τ', agree⟩ := agree_of_interp hr frag rep freshP comparable.coded c₀present known codeRead
      have solvedF := (information_transfer hr frag agree comparable.reads comparable.coded
        comparable.present comparable.takeLength comparable.readLength (seenP := seen)
        (seenU := seen)).mp solved
      exact (holds_transfer hr agree rep.present).mpr (asks PUnit.unit τ' solvedF)

include hr frag in
/-- **Results are represented**, when the stored-rule program's result is tagged through its knowledge
(for a closed fragment it always is: `keepsTags_of_closed`). -/
theorem results_represent (rep : Represents F s u) {c₀ : O} {rest : List O}
    (comparable : Comparable r s u sel c₀ rest)
    (freshP : (storedFiring hr s.frame ιP sel seenP).Fresh X s)
    (freshU : (interpFiring (shapeOf r) u.frame ιU sel seenU).Fresh X u)
    (tags : SemTagged F ((storedFiring hr s.frame ιP sel seenP).result X s)) :
    Represents F ((storedFiring hr s.frame ιP sel seenP).result X s)
      ((interpFiring (shapeOf r) u.frame ιU sel seenU).result X u) := by
  have c₀present : c₀ ∈ s.present :=
    comparable.present c₀ (List.mem_append_right _ (comparable.reads ▸ List.mem_cons_self))
  have gTake : (openedColumn (shapeOf r) 0).length = sel.taken.length := by
    rw [length_openedColumn]
    exact comparable.takeLength
  have gRead : (codePattern (shapeOf r) :: openedColumn (shapeOf r) 1).length = sel.read.length := by
    rw [comparable.reads, List.length_cons, List.length_cons, length_openedColumn]
    exact congrArg (· + 1) comparable.readLength
  have fRead : (ruleCode r :: r.body.read).length = sel.read.length := by
    rw [comparable.reads, List.length_cons, List.length_cons]
    exact congrArg (· + 1) comparable.readLength
  refine ⟨?_, tags, ?_, ?_⟩
  · show fire u.present (sel.commit (T := Unit)) = fire s.present (sel.commit (T := Unit))
    rw [rep.present]
  · intro τ solved
    have solvedG : X.Models (a := u.frame) (b := PUnit.unit) τ
        ((interpFiring (shapeOf r) u.frame ιU sel seenU).information X u) := solved
    obtain ⟨known, -, reads, -⟩ := (models_information _ gTake gRead τ).mp solvedG
    have reads' : List.Forall₂ (fun p o => nf (subst τ (subst ιU p)) = nf (subst τ (u.label o)))
        (codePattern (shapeOf r) :: openedColumn (shapeOf r) 1) (c₀ :: rest) := by
      rw [← comparable.reads]
      exact reads
    obtain ⟨τ', agree⟩ := agree_of_interp hr frag rep freshP comparable.coded c₀present known
      (List.forall₂_cons.mp reads').1
    refine ⟨τ', (information_transfer hr frag agree comparable.reads comparable.coded comparable.present
      comparable.takeLength comparable.readLength).mp solvedG, ?_⟩
    exact labels_transfer hr agree comparable.madeNodup comparable.madeLength
  · intro τ' solved
    have solvedF : X.Models (a := s.frame) (b := PUnit.unit) τ'
        ((storedFiring hr s.frame ιP sel seenP).information X s) := solved
    have known := ((models_information _ comparable.takeLength fRead τ').mp solvedF).1
    obtain ⟨τ, agree⟩ := agree_of_stored frag rep freshU known
    refine ⟨τ, (information_transfer hr frag agree comparable.reads comparable.coded comparable.present
      comparable.takeLength comparable.readLength).mpr solvedF, ?_⟩
    exact labels_transfer hr agree comparable.madeNodup comparable.madeLength

end Correspondence

#print axioms Represents.semTagged_interp
#print axioms models_information
#print axioms information_transfer
#print axioms holds_transfer
#print axioms labels_transfer
#print axioms agree_of_interp
#print axioms agree_of_stored
#print axioms admits_transfer
#print axioms results_represent

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RulesAsRows
