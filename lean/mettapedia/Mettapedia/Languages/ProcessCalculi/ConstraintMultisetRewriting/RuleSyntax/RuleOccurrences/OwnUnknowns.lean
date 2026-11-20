import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.Program

/-!
# A rule and a copy with its own unknowns renamed have the same firings

Over any frame action and extensions. For a rule `r` and a morphism `j` out of its frame of unknowns,
`renamed X r j` is `r` with every term carried along `j`. When `j` has a left inverse on the terms of
`r` (a morphism `back` with `back (j t) = t` for every term `t` of `r`):

* **`renamed_firing`**: the firing of the renamed rule with opening `u` is admitted exactly when the
  firing of `r` with opening `u ∘ j` is, with the same extension, selection and collected rows; and the
  two results are the same state.
* **`opening_congr`**: two firings of one rule whose openings act alike on the rule's terms are
  admitted together and have the same result.
* **`renamed_firing_back`**: so the firing of `r` with opening `v` is matched by the firing of the
  renamed rule with opening `v ∘ back`.
* **`renamed_succ`**: a program with `r` and the program with the renamed rule in its place have the
  same transitions; and so do the candidate's states that hold one or the other (`held_renamed`).

The names of a rule's own unknowns are therefore not observable by the step: two rules that differ by
such a renaming are the same rule for every state, selection and result.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire)
open LogicOverTheStep.StepSpan (Succ)

universe uO uT uH uE uOcc uR uZ

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}

/-- **A rule with its own unknowns renamed** along a morphism out of its frame. -/
def renamed (X : Frames Tm Hom) (r : Rule Tm) {b : Obj} (j : Hom r.locals b) : Rule Tm :=
  ⟨b, r.body.map (X.act j), r.collect.map (X.act j)⟩

section Maps

variable (X : Frames Tm Hom)

/-- Opening after renaming is opening along the composite. -/
theorem map_act_comp {a b c : Obj} (j : Hom a b) (u : Hom b c) (body : RuleInstance (Tm a)) :
    (body.map (X.act j)).map (X.act u) = body.map (X.act (X.comp u j)) := by
  have act : X.act (X.comp u j) = fun t => X.act u (X.act j t) := funext fun t => X.act_comp u j t
  have checkMaps : (Check.map (X.act u) ∘ Check.map (X.act j)) =
      Check.map fun t => X.act u (X.act j t) := by
    funext check
    cases check <;> rfl
  obtain ⟨take, read, tell, checks, produce⟩ := body
  rw [act]
  show RuleInstance.mk ((take.map (X.act j)).map (X.act u)) ((read.map (X.act j)).map (X.act u))
      ((tell.map fun pair => (X.act j pair.1, X.act j pair.2)).map
        fun pair => (X.act u pair.1, X.act u pair.2))
      ((checks.map (Check.map (X.act j))).map (Check.map (X.act u)))
      ((produce.map (X.act j)).map (X.act u)) =
    RuleInstance.mk (take.map fun t => X.act u (X.act j t)) (read.map fun t => X.act u (X.act j t))
      (tell.map fun pair => (X.act u (X.act j pair.1), X.act u (X.act j pair.2)))
      (checks.map (Check.map fun t => X.act u (X.act j t)))
      (produce.map fun t => X.act u (X.act j t))
  rw [List.map_map, List.map_map, List.map_map, List.map_map, List.map_map, checkMaps]
  rfl

/-- The terms of the renamed rule are the renamed terms. -/
theorem terms_renamed (r : Rule Tm) {b : Obj} (j : Hom r.locals b) :
    (renamed X r j).terms = r.terms.map (X.act j) := by
  have checks : ∀ cs : List (Check (Tm r.locals)),
      (cs.map (Check.map (X.act j))).flatMap checkTerms = (cs.flatMap checkTerms).map (X.act j) := by
    intro cs
    induction cs with
    | nil => rfl
    | cons check rest ih =>
        rw [List.map_cons, List.flatMap_cons, List.flatMap_cons, List.map_append, ih]
        cases check <;> rfl
  show r.body.take.map (X.act j) ++ r.body.read.map (X.act j) ++
      (r.body.tell.map fun pair => (X.act j pair.1, X.act j pair.2)).map Prod.fst ++
      (r.body.tell.map fun pair => (X.act j pair.1, X.act j pair.2)).map Prod.snd ++
      (r.body.checks.map (Check.map (X.act j))).flatMap checkTerms ++ r.body.produce.map (X.act j) ++
      r.collect.map (X.act j) =
    (r.body.take ++ r.body.read ++ r.body.tell.map Prod.fst ++ r.body.tell.map Prod.snd ++
      r.body.checks.flatMap checkTerms ++ r.body.produce ++ r.collect).map (X.act j)
  rw [checks]
  simp only [List.map_append, List.map_map]
  rfl

/-- Two morphisms that act alike on the terms of a rule open its body alike. -/
theorem map_congr_terms (r : Rule Tm) {c : Obj} (v v' : Hom r.locals c)
    (alike : ∀ t ∈ r.terms, X.act v t = X.act v' t) :
    r.body.map (X.act v) = r.body.map (X.act v') ∧
      r.collect.map (X.act v) = r.collect.map (X.act v') := by
  have inTake : ∀ t ∈ r.body.take, t ∈ r.terms := fun t inside => by
    unfold Rule.terms
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl inside)))))
  have inRead : ∀ t ∈ r.body.read, t ∈ r.terms := fun t inside => by
    unfold Rule.terms
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr inside)))))
  have inFst : ∀ e ∈ r.body.tell, e.1 ∈ r.terms := fun e inside => by
    unfold Rule.terms
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (List.mem_map.mpr ⟨e, inside, rfl⟩)))))
  have inSnd : ∀ e ∈ r.body.tell, e.2 ∈ r.terms := fun e inside => by
    unfold Rule.terms
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inr (List.mem_map.mpr ⟨e, inside, rfl⟩))))
  have inChecks : ∀ check ∈ r.body.checks, ∀ t ∈ checkTerms check, t ∈ r.terms :=
    fun check inside t member => by
      unfold Rule.terms
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inr (List.mem_flatMap.mpr ⟨check, inside, member⟩)))
  have inProduce : ∀ t ∈ r.body.produce, t ∈ r.terms := fun t inside => by
    unfold Rule.terms
    simp only [List.mem_append]
    exact Or.inl (Or.inr inside)
  have inCollect : ∀ t ∈ r.collect, t ∈ r.terms := fun t inside => by
    unfold Rule.terms
    simp only [List.mem_append]
    exact Or.inr inside
  have checkAlike : ∀ check ∈ r.body.checks,
      Check.map (X.act v) check = Check.map (X.act v') check := by
    intro check inside
    have terms := inChecks check inside
    cases check with
    | equal left right =>
        show Check.equal (X.act v left) (X.act v right) = Check.equal (X.act v' left) (X.act v' right)
        rw [alike left (terms left (by simp [checkTerms])),
          alike right (terms right (by simp [checkTerms]))]
    | predicate quantifier pattern =>
        show Check.predicate quantifier (X.act v pattern) = Check.predicate quantifier (X.act v' pattern)
        rw [alike pattern (terms pattern (by simp [checkTerms]))]
    | count pattern number =>
        show Check.count (X.act v pattern) number = Check.count (X.act v' pattern) number
        rw [alike pattern (terms pattern (by simp [checkTerms]))]
  refine ⟨?_, List.map_congr_left fun t inside => alike t (inCollect t inside)⟩
  show RuleInstance.mk (r.body.take.map (X.act v)) (r.body.read.map (X.act v))
      (r.body.tell.map fun pair => (X.act v pair.1, X.act v pair.2))
      (r.body.checks.map (Check.map (X.act v))) (r.body.produce.map (X.act v)) =
    RuleInstance.mk (r.body.take.map (X.act v')) (r.body.read.map (X.act v'))
      (r.body.tell.map fun pair => (X.act v' pair.1, X.act v' pair.2))
      (r.body.checks.map (Check.map (X.act v'))) (r.body.produce.map (X.act v'))
  rw [List.map_congr_left fun t inside => alike t (inTake t inside),
    List.map_congr_left fun t inside => alike t (inRead t inside),
    List.map_congr_left (f := fun pair : Tm r.locals × Tm r.locals => (X.act v pair.1, X.act v pair.2))
      (g := fun pair => (X.act v' pair.1, X.act v' pair.2))
      (fun e inside => by rw [alike e.1 (inFst e inside), alike e.2 (inSnd e inside)]),
    List.map_congr_left checkAlike,
    List.map_congr_left fun t inside => alike t (inProduce t inside)]

end Maps

/-! ## Firings -/

section Firings

variable (X : Frames Tm Hom) {O : Type uOcc} [DecidableEq O] {E : Extensions.{uO, uH, uE} Hom}
  {P P' : Program Tm}

/-- **Two firings of one rule whose openings act alike on its terms** are admitted together and have
the same result. -/
theorem opening_congr (r : Rule Tm) (inP : r ∈ P) (inP' : r ∈ P') (s : State Tm O)
    (e : E.Ext s.frame) (v v' : Hom r.locals (E.target e))
    (alike : ∀ t ∈ r.terms, X.act v t = X.act v' t) (selection : Selection O)
    (seen : List (Finset O)) :
    ((⟨r, inP, e, v, selection, seen⟩ : Firing O E P s.frame).Admits X s ↔
        (⟨r, inP', e, v', selection, seen⟩ : Firing O E P' s.frame).Admits X s) ∧
      (⟨r, inP, e, v, selection, seen⟩ : Firing O E P s.frame).result X s =
        (⟨r, inP', e, v', selection, seen⟩ : Firing O E P' s.frame).result X s := by
  let g : Firing O E P s.frame := ⟨r, inP, e, v, selection, seen⟩
  let g' : Firing O E P' s.frame := ⟨r, inP', e, v', selection, seen⟩
  obtain ⟨bodies, collects⟩ := map_congr_terms X r v v' alike
  have opened : g.opened X = g'.opened X := bodies
  have collect : g.collectOpened X = g'.collectOpened X := collects
  have information : g.information X s = g'.information X s := by
    unfold Firing.information
    rw [opened]
    rfl
  have holds : ∀ {B : Obj} (σ : Hom (E.target e) B), g.Holds X s σ ↔ g'.Holds X s σ := by
    intro B σ
    unfold Firing.Holds
    rw [opened, collect]
    exact Iff.rfl
  have fresh : g.Fresh X s ↔ g'.Fresh X s := by
    constructor
    · intro isFresh B γ h
      obtain ⟨w, state, rule⟩ := isFresh B γ h
      refine ⟨w, state, fun t inside => ?_⟩
      have related := rule t inside
      show X.E (X.act w (X.act v' t)) (X.act h t)
      rw [← alike t inside]
      exact related
    · intro isFresh B γ h
      obtain ⟨w, state, rule⟩ := isFresh B γ h
      refine ⟨w, state, fun t inside => ?_⟩
      have related := rule t inside
      show X.E (X.act w (X.act v t)) (X.act h t)
      rw [alike t inside]
      exact related
  have result : g.result X s = g'.result X s := by
    unfold Firing.result
    rw [information, opened]
    rfl
  refine ⟨?_, result⟩
  show g.Admits X s ↔ g'.Admits X s
  unfold Firing.Admits Firing.Shapes
  rw [information, fresh]
  constructor
  · rintro ⟨shapes, enabled, solvable, asks⟩
    exact ⟨shapes, enabled, solvable, fun B σ solved => (holds σ).mp (asks B σ solved)⟩
  · rintro ⟨shapes, enabled, solvable, asks⟩
    exact ⟨shapes, enabled, solvable, fun B σ solved => (holds σ).mpr (asks B σ solved)⟩

/-- **The firing of a renamed rule is the firing of the rule along the composite opening**: admitted
together, with the same result. -/
theorem renamed_firing (r : Rule Tm) {b : Obj} (j : Hom r.locals b) (back : Hom b r.locals)
    (undo : ∀ t ∈ r.terms, X.act back (X.act j t) = t) (inP : r ∈ P)
    (inP' : renamed X r j ∈ P') (s : State Tm O) (e : E.Ext s.frame) (u : Hom b (E.target e))
    (selection : Selection O) (seen : List (Finset O)) :
    ((⟨renamed X r j, inP', e, u, selection, seen⟩ : Firing O E P' s.frame).Admits X s ↔
        (⟨r, inP, e, X.comp u j, selection, seen⟩ : Firing O E P s.frame).Admits X s) ∧
      (⟨renamed X r j, inP', e, u, selection, seen⟩ : Firing O E P' s.frame).result X s =
        (⟨r, inP, e, X.comp u j, selection, seen⟩ : Firing O E P s.frame).result X s := by
  let g' : Firing O E P' s.frame := ⟨renamed X r j, inP', e, u, selection, seen⟩
  let g : Firing O E P s.frame := ⟨r, inP, e, X.comp u j, selection, seen⟩
  have opened : g'.opened X = g.opened X := map_act_comp X j u r.body
  have collect : g'.collectOpened X = g.collectOpened X := by
    show (r.collect.map (X.act j)).map (X.act u) = r.collect.map (X.act (X.comp u j))
    rw [List.map_map]
    exact List.map_congr_left fun t _ => (X.act_comp u j t).symm
  have information : g'.information X s = g.information X s := by
    unfold Firing.information
    rw [opened]
    rfl
  have holds : ∀ {B : Obj} (σ : Hom (E.target e) B), g'.Holds X s σ ↔ g.Holds X s σ := by
    intro B σ
    unfold Firing.Holds
    rw [opened, collect]
    exact Iff.rfl
  have terms : g'.rule.terms = r.terms.map (X.act j) := terms_renamed X r j
  have fresh : g'.Fresh X s ↔ g.Fresh X s := by
    constructor
    · intro isFresh B γ h
      obtain ⟨w, state, rule⟩ := isFresh B γ (X.comp h back)
      refine ⟨w, state, fun t inside => ?_⟩
      have image : X.act j t ∈ g'.rule.terms := by
        rw [terms]
        exact List.mem_map.mpr ⟨t, inside, rfl⟩
      have related : X.E (X.act w (X.act u (X.act j t))) (X.act (X.comp h back) (X.act j t)) :=
        rule (X.act j t) image
      rw [X.act_comp h back, undo t inside] at related
      show X.E (X.act w (X.act (X.comp u j) t)) (X.act h t)
      rw [X.act_comp u j t]
      exact related
    · intro isFresh B γ h'
      obtain ⟨w, state, rule⟩ := isFresh B γ (X.comp h' j)
      refine ⟨w, state, fun t' inside => ?_⟩
      rw [terms] at inside
      obtain ⟨t, member, rfl⟩ := List.mem_map.mp inside
      have related : X.E (X.act w (X.act (X.comp u j) t)) (X.act (X.comp h' j) t) := rule t member
      rw [X.act_comp u j t, X.act_comp h' j t] at related
      exact related
  have takes : g'.rule.body.take.length = g.rule.body.take.length := List.length_map _
  have reads : g'.rule.body.read.length = g.rule.body.read.length := List.length_map _
  have produces : g'.rule.body.produce.length = g.rule.body.produce.length := List.length_map _
  have collectLength : g'.rule.collect.length = g.rule.collect.length := List.length_map _
  have result : g'.result X s = g.result X s := by
    unfold Firing.result
    rw [information, opened]
    rfl
  refine ⟨?_, result⟩
  show g'.Admits X s ↔ g.Admits X s
  unfold Firing.Admits Firing.Shapes
  rw [information, fresh, takes, reads, produces, collectLength]
  constructor
  · rintro ⟨shapes, enabled, solvable, asks⟩
    exact ⟨shapes, enabled, solvable, fun B σ solved => (holds σ).mp (asks B σ solved)⟩
  · rintro ⟨shapes, enabled, solvable, asks⟩
    exact ⟨shapes, enabled, solvable, fun B σ solved => (holds σ).mpr (asks B σ solved)⟩

/-- **The firing of a rule is matched by a firing of its renamed copy**, opened along the inverse:
admitted together, with the same result. -/
theorem renamed_firing_back (r : Rule Tm) {b : Obj} (j : Hom r.locals b) (back : Hom b r.locals)
    (undo : ∀ t ∈ r.terms, X.act back (X.act j t) = t) (inP : r ∈ P)
    (inP' : renamed X r j ∈ P') (s : State Tm O) (e : E.Ext s.frame)
    (v : Hom r.locals (E.target e)) (selection : Selection O) (seen : List (Finset O)) :
    ((⟨r, inP, e, v, selection, seen⟩ : Firing O E P s.frame).Admits X s ↔
        (⟨renamed X r j, inP', e, X.comp v back, selection, seen⟩ : Firing O E P' s.frame).Admits X s) ∧
      (⟨r, inP, e, v, selection, seen⟩ : Firing O E P s.frame).result X s =
        (⟨renamed X r j, inP', e, X.comp v back, selection, seen⟩ : Firing O E P' s.frame).result X s := by
  have alike : ∀ t ∈ r.terms, X.act v t = X.act (X.comp (X.comp v back) j) t := by
    intro t inside
    rw [X.act_comp, X.act_comp, undo t inside]
  obtain ⟨admits, result⟩ := opening_congr X r inP inP s e v (X.comp (X.comp v back) j) alike
    selection seen
  obtain ⟨admits', result'⟩ := renamed_firing X r j back undo inP inP' s e (X.comp v back)
    selection seen
  exact ⟨admits.trans admits'.symm, result.trans result'.symm⟩

/-- **A program with a rule and the program with its renamed copy have the same transitions.** -/
theorem renamed_succ (Q : Program Tm) (r : Rule Tm) {b : Obj} (j : Hom r.locals b)
    (back : Hom b r.locals) (undo : ∀ t ∈ r.terms, X.act back (X.act j t) = t) (s t : State Tm O) :
    Succ (step X O E (Q ∪ {r})).toStep s t ↔ Succ (step X O E (Q ∪ {renamed X r j})).toStep s t := by
  constructor
  · rintro ⟨⟨rule, member, e, v, selection, seen⟩, admitted, reached⟩
    rcases member with inQ | isRule
    · exact ⟨⟨rule, Or.inl inQ, e, v, selection, seen⟩, admitted, reached⟩
    · have same : rule = r := isRule
      subst same
      obtain ⟨admits, result⟩ := renamed_firing_back X rule j back undo (P := Q ∪ {rule})
        (P' := Q ∪ {renamed X rule j}) (Or.inr rfl) (Or.inr rfl) s e v selection seen
      exact ⟨_, admits.mp admitted, result.symm.trans reached⟩
  · rintro ⟨⟨rule, member, e, u, selection, seen⟩, admitted, reached⟩
    rcases member with inQ | isRule
    · exact ⟨⟨rule, Or.inl inQ, e, u, selection, seen⟩, admitted, reached⟩
    · have same : rule = renamed X r j := isRule
      subst same
      obtain ⟨admits, result⟩ := renamed_firing X r j back undo (P := Q ∪ {r})
        (P' := Q ∪ {renamed X r j}) (Or.inr rfl) (Or.inr rfl) s e u selection seen
      exact ⟨_, admits.mp admitted, result.symm.trans reached⟩

end Firings

/-! ## On the candidate -/

section Held

variable (X : Frames Tm Hom) {O : Type uOcc} [DecidableEq O] {R : Type uR} [DecidableEq R]
  {Z : Type uZ} (E : Extensions.{uO, uH, uE} Hom)

/-- **Holding a rule or its renamed copy gives the same transitions**: with the same ambient
program, the state that holds `r` at one identity and the state that holds its renamed copy there
reach the same rows. -/
theorem held_renamed (Q : Program Tm) (r : Rule Tm) {b : Obj} (j : Hom r.locals b)
    (back : Hom b r.locals) (undo : ∀ t ∈ r.terms, X.act back (X.act j t) = t) (ρ : R)
    (zone : R → Z) (s t : State Tm O) :
    Succ (rstep X O R E (ofRules Z) Q).toStep (holding s {ρ} (fun _ => r) zone)
        (holding t {ρ} (fun _ => r) zone) ↔
      Succ (rstep X O R E (ofRules Z) Q).toStep (holding s {ρ} (fun _ => renamed X r j) zone)
        (holding t {ρ} (fun _ => renamed X r j) zone) := by
  have offers : ∀ rule : Rule Tm, Offers ({rule} : Program Tm) ({ρ} : Finset R) (fun _ => rule) := by
    intro rule candidate
    constructor
    · intro inside
      exact ⟨ρ, Finset.mem_singleton_self ρ, (Set.mem_singleton_iff.mp inside).symm⟩
    · rintro ⟨_, _, same⟩
      exact Set.mem_singleton_iff.mpr same.symm
  rw [program_eq R X E (offers r) zone s t, program_eq R X E (offers (renamed X r j)) zone s t]
  exact renamed_succ X Q r j back undo s t

end Held

#print axioms map_act_comp
#print axioms terms_renamed
#print axioms map_congr_terms
#print axioms opening_congr
#print axioms renamed_firing
#print axioms renamed_firing_back
#print axioms renamed_succ
#print axioms held_renamed

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences
