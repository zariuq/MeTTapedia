import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation.Schematic.Matching
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation.Direct

/-!
# Admitted firings of `RuleSyntax.step` with unknowns, at ground stores, are firings by matching

The step is `RuleSyntax.step` itself at one frame over rows with unknowns (`schematicStep`), with the
existing first-order action. A state is **ground** when its present labels are terms of rows
(`GroundLabels`), and its knowledge is **trivial** when each equation has identical sides
(`TrivialKnowledge`).

A firing opens the rule's unknowns into the frame (`Firing.opening`): the result's labels are the opened
made rows, terms with unknowns, and its knowledge is the firing's information, which binds them. So the
result is ground only **modulo its knowledge**: `ReadsAs s rows` says that every solution of the knowledge
reads the present labels as exactly these rows.

* `solutions_agree`: **every solution of the information reads each unknown a take or read pattern binds
  as the match does**: on ground rows, solving the take and read equations is matching.
* `match_of_admitted`: an admitted firing of a rule of the fragment, at a ground state, is a firing by
  matching, and the result reads as the made rows' instances beside the rest.
* `admitted_of_match`: conversely every firing by matching is an admitted firing, with an opening that
  renames the rule's unknowns apart from every unknown of the knowledge (`shift`, fresh: `shift_fresh`),
  when identities are infinitely many.
* `readsAs_unique`: a state with solvable knowledge reads as at most one bag of rows.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation.Schematic

open Mettapedia.Logic.LP
open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire)
open OneFrame (frames ext)
open NamesOnTheStep (Expr)

universe uO

/-- The first-order action on rows with unknowns. -/
abbrev A : SubstitutionAction Tm (Subst rowSig) := FirstOrder.action rowSig

/-- Its one-frame frame action. -/
abbrev X := frames A

/-- The identity extension. -/
abbrev E := ext A

/-- States at the one frame over rows with unknowns. -/
abbrev SState (O : Type uO) := State (OneFrame.Terms Tm) O

/-- **The step of a program with unknowns**: `RuleSyntax.step` at one frame over the first-order action. -/
abbrev schematicStep (O : Type uO) [DecidableEq O] (rules : List SRule) :=
  step X O E {r | r ∈ rules}

variable {O : Type uO} [DecidableEq O] {rules : List SRule}

/-- **A ground state**: every present label is the term of a row. -/
def GroundLabels (s : SState O) (rows : O → Expr) : Prop := ∀ o ∈ s.present, s.label o = toTerm (rows o)

/-- **Trivial knowledge**: every equation has identical sides. -/
def TrivialKnowledge (store : EquationStore Tm) : Prop := ∀ e ∈ store, e.1 = e.2

/-- **A state reads as a bag of rows**: every solution of its knowledge reads its present labels as exactly
those rows. -/
def ReadsAs (s : SState O) (bag : Multiset Expr) : Prop :=
  ∀ σ : Subst rowSig, A.Models σ s.knowledge → s.present.val.map (fun o => σ.applyTerm (s.label o)) = bag.map toTerm

omit [DecidableEq O] in
/-- **A state with solvable knowledge reads as at most one bag of rows.** -/
theorem readsAs_unique {s : SState O} {first second : Multiset Expr} (solvable : A.Consistent s.knowledge)
    (readsFirst : ReadsAs s first) (readsSecond : ReadsAs s second) : first = second := by
  obtain ⟨σ, solved⟩ := solvable
  exact Multiset.map_injective toTerm_injective ((readsFirst σ solved).symm.trans (readsSecond σ solved))

omit [DecidableEq O] in
theorem readsAs_of_ground {s : SState O} {rows : O → Expr} (ground : GroundLabels s rows) :
    ReadsAs s (s.present.val.map rows) := by
  intro σ _
  rw [Multiset.map_map]
  refine Multiset.map_congr rfl fun o member => ?_
  rw [ground o (Finset.mem_val.mp member), applyTerm_toTerm]
  rfl

/-! ## Lists in pairs -/

theorem pairs_of_map_eq {α β γ : Type*} {f : α → γ} {g : β → γ} :
    ∀ {l₁ : List α} {l₂ : List β}, l₁.map f = l₂.map g → ∀ x ∈ l₁.zip l₂, f x.1 = g x.2
  | [], _, _, _, member => by simp at member
  | _ :: _, [], same, _, _ => by simp at same
  | a :: as, b :: bs, same, x, member => by
      simp only [List.map_cons, List.cons.injEq] at same
      rcases List.mem_cons.mp member with rfl | member
      · exact same.1
      · exact pairs_of_map_eq same.2 x member

theorem exists_zip_of_mem {α β : Type*} : ∀ {l₁ : List α} {l₂ : List β}, l₁.length = l₂.length →
    ∀ {a : α}, a ∈ l₁ → ∃ b, (a, b) ∈ l₁.zip l₂
  | [], _, _, _, member => absurd member List.not_mem_nil
  | _ :: _, [], lengths, _, _ => by simp at lengths
  | x :: xs, y :: ys, lengths, a, member => by
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨y, List.mem_cons_self⟩
      · obtain ⟨b, inside⟩ := exists_zip_of_mem (Nat.succ.inj lengths) member
        exact ⟨b, List.mem_cons_of_mem _ inside⟩

theorem mem_zip_map_left {α β γ : Type*} {f : α → γ} {l₁ : List α} {l₂ : List β} {a : α} {b : β}
    (member : (a, b) ∈ l₁.zip l₂) : (f a, b) ∈ (l₁.map f).zip l₂ := by
  rw [List.zip_map_left]
  exact List.mem_map.mpr ⟨(a, b), member, rfl⟩

/-! ## A firing at one frame -/

section Firing

variable {s : SState O} (g : Firing O E {r | r ∈ rules} s.frame)

omit [DecidableEq O] in
theorem row_eq (o : O) : g.row X s o = s.label o := Subst.applyTerm_id (s.label o)

omit [DecidableEq O] in
/-- An equation of the information matching a pattern with a selected row. -/
theorem mem_matching {patterns : List Tm} {selected : List O} {e : Equation Tm}
    (member : e ∈ g.matching X s (patterns.map g.opening.applyTerm) selected) :
    ∃ p o, (p, o) ∈ patterns.zip selected ∧ e = (g.opening.applyTerm p, s.label o) := by
  unfold Firing.matching at member
  rw [← List.map_uncurry_zip_eq_zipWith, List.zip_map_left, List.map_map] at member
  obtain ⟨⟨p, o⟩, inside, rfl⟩ := List.mem_map.mp member
  exact ⟨p, o, inside, by simp [row_eq]⟩

omit [DecidableEq O] in
/-- **Every solution of the information reads each unknown a take or read pattern binds as the match does**:
on ground rows, solving the take and read equations is matching. -/
theorem solutions_agree {rows : O → Expr} (ground : GroundLabels s rows) (θ : ℕ → Expr)
    (takeLength : g.rule.body.take.length = g.selection.taken.length)
    (readLength : g.rule.body.read.length = g.selection.read.length)
    (takenPresent : ∀ o ∈ g.selection.taken, o ∈ s.present) (readPresent : ∀ o ∈ g.selection.read, o ∈ s.present)
    (takesMatch : ∀ x ∈ g.rule.body.take.zip g.selection.taken, inst θ x.1 = rows x.2)
    (readsMatch : ∀ x ∈ g.rule.body.read.zip g.selection.read, inst θ x.1 = rows x.2)
    {σ : Subst rowSig} (solved : A.Models σ (g.information X s)) :
    ∀ x, Bound g.rule x → σ.applyTerm (g.opening x) = toTerm (θ x) := by
  rintro x ⟨t, member, vars⟩
  have composed : ∀ {p : Tm} {o : O}, o ∈ s.present → inst θ p = rows o →
      σ.applyTerm (g.opening.applyTerm p) = σ.applyTerm (g.row X s o) → ∀ y ∈ p.freeVars,
        σ.applyTerm (g.opening y) = toTerm (θ y) := by
    intro p o present instantiated equation y vars
    rw [row_eq, ground o present, applyTerm_toTerm, ← instantiated, ← applyTerm_lift,
      ← Subst.applyTerm_comp] at equation
    exact agree_of_applyTerm_eq p equation y vars
  rcases List.mem_append.mp member with taken | read
  · obtain ⟨o, inside⟩ := exists_zip_of_mem takeLength taken
    exact composed (takenPresent o (List.of_mem_zip inside).2) (takesMatch _ inside)
      (g.take_solved (b := PUnit.unit) solved (mem_zip_map_left inside)) x vars
  · obtain ⟨o, inside⟩ := exists_zip_of_mem readLength read
    exact composed (readPresent o (List.of_mem_zip inside).2) (readsMatch _ inside)
      (g.read_solved (b := PUnit.unit) solved (mem_zip_map_left inside)) x vars

omit [DecidableEq O] in
/-- Where every bound unknown reads as the match does, a term of the rule written within the bound unknowns
reads as its instance. -/
theorem written_reads {θ : ℕ → Expr} {σ : Subst rowSig}
    (agree : ∀ x, Bound g.rule x → σ.applyTerm (g.opening x) = toTerm (θ x)) {t : Tm}
    (bound : ∀ x ∈ t.freeVars, Bound g.rule x) :
    σ.applyTerm (g.opening.applyTerm t) = toTerm (inst θ t) := by
  rw [← Subst.applyTerm_comp, ← applyTerm_lift]
  exact Subst.applyTerm_congr fun x vars => agree x (bound x vars)

end Firing

/-! ## The result reads as the made rows beside the rest -/

/-- **The result of an admitted firing reads as the instances of the made rows beside the rows not taken.** -/
theorem result_readsAs {s : SState O} {rows : O → Expr} (ground : GroundLabels s rows)
    (g : Firing O E {r | r ∈ rules} s.frame) (admitted : (schematicStep O rules).Admits (s := s) g)
    (restricted : RangeRestricted g.rule) (θ : ℕ → Expr)
    (agree : ∀ σ : Subst rowSig, A.Models σ (g.information X s) →
      ∀ x, Bound g.rule x → σ.applyTerm (g.opening x) = toTerm (θ x)) :
    ReadsAs ((schematicStep O rules).result g admitted)
      ((s.present \ g.selection.taken.toFinset).val.map rows + (g.rule.body.produce.map (inst θ) : Multiset Expr)) := by
  obtain ⟨_, ⟨_, madeNodup, _, _, produceLength, _⟩, enabled, _⟩ := (admits_iff g).mp admitted
  intro σ solved
  have apart : Disjoint (s.present \ g.selection.taken.toFinset) g.selection.made.toFinset :=
    Finset.disjoint_of_subset_left Finset.sdiff_subset enabled.fresh.symm
  show (fire s.present (g.selection.commit (T := Unit))).val.map
    (fun o => σ.applyTerm ((g.result X s).label o)) = _
  unfold fire
  show ((s.present \ g.selection.taken.toFinset) ∪ g.selection.made.toFinset).val.map _ = _
  rw [val_union_of_disjoint apart, Multiset.map_add, toFinset_val_of_nodup madeNodup, Multiset.map_coe,
    Multiset.map_add, Multiset.map_map, Multiset.map_coe, List.map_map]
  congr 1
  · refine Multiset.map_congr rfl fun o member => ?_
    have present := (Finset.mem_sdiff.mp (Finset.mem_val.mp member)).1
    have notMade : o ∉ g.selection.made := fun made =>
      Finset.disjoint_left.mp apart (Finset.mem_val.mp member) (List.mem_toFinset.mpr made)
    show σ.applyTerm ((g.result X s).label o) = toTerm (rows o)
    rw [g.result_label_other notMade, row_eq, ground o present, applyTerm_toTerm]
  · have lengths : g.selection.made.length = (g.opened X).produce.length := by
      simp only [Firing.opened, RuleInstance.map, List.length_map]
      exact produceLength.symm
    have mapped := map_eq_of_zip _ g.selection.made (g.opened X).produce lengths
      (Firing.relabel_zip (g.row X s) g.selection.made (g.opened X).produce madeNodup lengths)
    have labels : g.selection.made.map (g.result X s).label = (g.opened X).produce := mapped
    have composed : g.selection.made.map (fun o => σ.applyTerm ((g.result X s).label o)) =
        ((g.opened X).produce).map σ.applyTerm := by
      rw [← labels, List.map_map]
      rfl
    rw [show (fun o => σ.applyTerm ((g.result X s).label o)) = fun o => σ.applyTerm ((g.result X s).label o)
      from rfl]
    show ((g.selection.made.map fun o => σ.applyTerm ((g.result X s).label o) : List Tm) : Multiset Tm) = _
    rw [composed]
    show (((g.rule.body.produce.map g.opening.applyTerm).map σ.applyTerm : List Tm) : Multiset Tm) = _
    rw [List.map_map]
    congr 1
    refine List.map_congr_left fun t member => ?_
    exact written_reads g (agree σ solved) fun x vars => restricted t (mem_written_of_produce member) x vars

/-! ## Admitted firings are firings by matching -/

/-- **An admitted firing of a rule of the fragment, at a ground state, is a firing by matching**, and its
result reads as the made rows' instances beside the rows not taken. -/
theorem match_of_admitted {s : SState O} {rows : O → Expr} (ground : GroundLabels s rows)
    (fragment : ∀ r ∈ rules, RangeRestrictedPositive r)
    (g : Firing O E {r | r ∈ rules} s.frame) (admitted : (schematicStep O rules).Admits (s := s) g) :
    ∃ θ : ℕ → Expr, MatchFires g.rule θ (s.present.toList.map rows)
        ((s.present \ g.selection.taken.toFinset).toList.map rows) ∧
      ReadsAs ((schematicStep O rules).result g admitted)
        ((s.present \ g.selection.taken.toFinset).val.map rows + (g.rule.body.produce.map (inst θ) : Multiset Expr)) := by
  obtain ⟨-, ⟨takenNodup, _, takeLength, readLength, _, _⟩, enabled, solvable, checks, _⟩ :=
    (admits_iff g).mp admitted
  have fragmentRule := fragment g.rule g.member
  obtain ⟨σ, solved⟩ := (Frames.ofSubstitution_solvable_iff A _).mp solvable
  let θ := groundPart (σ.comp g.opening)
  have takenPresent : ∀ o ∈ g.selection.taken, o ∈ s.present := fun o member =>
    enabled.taken_subset (List.mem_toFinset.mpr member)
  have readPresent : ∀ o ∈ g.selection.read, o ∈ s.present := fun o member =>
    enabled.kept_subset (List.mem_toFinset.mpr member)
  have matchedBy : ∀ {p : Tm} {o : O}, o ∈ s.present →
      σ.applyTerm (g.opening.applyTerm p) = σ.applyTerm (g.row X s o) → inst θ p = rows o := by
    intro p o present equation
    rw [row_eq, ground o present, applyTerm_toTerm, ← Subst.applyTerm_comp] at equation
    exact (inst_groundPart _ p (rows o) equation).1
  have takesMatch : ∀ x ∈ g.rule.body.take.zip g.selection.taken, inst θ x.1 = rows x.2 := fun x inside =>
    matchedBy (takenPresent x.2 (List.of_mem_zip inside).2)
      (g.take_solved (b := PUnit.unit) solved (mem_zip_map_left inside))
  have readsMatch : ∀ x ∈ g.rule.body.read.zip g.selection.read, inst θ x.1 = rows x.2 := fun x inside =>
    matchedBy (readPresent x.2 (List.of_mem_zip inside).2)
      (g.read_solved (b := PUnit.unit) solved (mem_zip_map_left inside))
  have agree : ∀ σ' : Subst rowSig, A.Models σ' (g.information X s) →
      ∀ x, Bound g.rule x → σ'.applyTerm (g.opening x) = toTerm (θ x) := fun σ' solved' =>
    solutions_agree g ground θ takeLength readLength takenPresent readPresent takesMatch readsMatch solved'
  have reads : ∀ σ' : Subst rowSig, A.Models σ' (g.information X s) → ∀ t : Tm, (∀ x ∈ t.freeVars, Bound g.rule x) →
      σ'.applyTerm (g.opening.applyTerm t) = toTerm (inst θ t) := fun σ' solved' t bound =>
    written_reads g (agree σ' solved') bound
  refine ⟨θ, ⟨?_, ?_, ?_⟩, result_readsAs ground g admitted fragmentRule.2.2 θ agree⟩
  · -- the takes beside the rest are the store
    have takeRows : g.rule.body.take.map (inst θ) = g.selection.taken.map rows :=
      map_eq_of_zip' takeLength takesMatch
    refine Multiset.coe_eq_coe.mp ?_
    rw [takeRows, ← Multiset.coe_add, ← Multiset.map_coe rows (s.present \ g.selection.taken.toFinset).toList,
      ← Multiset.map_coe rows s.present.toList, Finset.coe_toList, Finset.coe_toList]
    exact (bagOf_split rows (C := ⟨[], s.present⟩) takenNodup enabled.taken_subset).symm
  · -- every read is a row of the rest
    intro q member
    obtain ⟨o, inside⟩ := exists_zip_of_mem readLength member
    rw [readsMatch _ inside]
    refine List.mem_map_of_mem (Finset.mem_toList.mpr (Finset.mem_sdiff.mpr ⟨readPresent o (List.of_mem_zip inside).2,
      fun taken => ?_⟩))
    exact Finset.disjoint_left.mp enabled.apart taken (List.mem_toFinset.mpr (List.of_mem_zip inside).2)
  · -- every tell and guard holds
    intro e member
    have written := mem_written_of_equation member
    have boundLeft : ∀ x ∈ e.1.freeVars, Bound g.rule x := fun x vars => fragmentRule.2.2 _ written.1 x vars
    have boundRight : ∀ x ∈ e.2.freeVars, Bound g.rule x := fun x vars => fragmentRule.2.2 _ written.2 x vars
    have equal : σ.applyTerm (g.opening.applyTerm e.1) = σ.applyTerm (g.opening.applyTerm e.2) := by
      rcases List.mem_append.mp member with told | guarded
      · exact g.tell_solved (b := PUnit.unit) solved (List.mem_map_of_mem (f := fun pair => (g.opening.applyTerm pair.1,
          g.opening.applyTerm pair.2)) told)
      · obtain ⟨c, inChecks, inGuard⟩ := List.mem_flatMap.mp guarded
        cases c with
        | equal l r =>
            rw [guardOf, List.mem_singleton] at inGuard
            subst inGuard
            exact checks (Check.map g.opening.applyTerm (.equal l r)) (List.mem_map_of_mem inChecks)
              PUnit.unit σ solved
        | predicate quantifier _ => simp [guardOf] at inGuard
        | count _ _ => simp [guardOf] at inGuard
    rw [reads σ solved e.1 boundLeft, reads σ solved e.2 boundRight] at equal
    exact toTerm_injective equal
where
  map_eq_of_zip' {θ : ℕ → Expr} {rows : O → Expr} {ps : List Tm} {os : List O} (lengths : ps.length = os.length)
      (each : ∀ x ∈ ps.zip os, inst θ x.1 = rows x.2) : ps.map (inst θ) = os.map rows := by
    induction ps generalizing os with
    | nil => cases os with
      | nil => rfl
      | cons _ _ => simp at lengths
    | cons p ps ih => cases os with
      | nil => simp at lengths
      | cons o os =>
          rw [List.map_cons, List.map_cons, each (p, o) List.mem_cons_self,
            ih (Nat.succ.inj lengths) fun x member => each x (List.mem_cons_of_mem _ member)]

/-! ## Firings by matching are admitted firings -/

theorem le_foldr_max : ∀ {l : List ℕ} {a : ℕ}, a ∈ l → a ≤ l.foldr max 0
  | [], _, member => absurd member List.not_mem_nil
  | b :: l, a, member => by
      rcases List.mem_cons.mp member with rfl | member
      · exact le_max_left _ _
      · exact (le_foldr_max member).trans (le_max_right _ _)

/-- **A bound beyond every unknown the knowledge mentions.** -/
def knowledgeBound (store : EquationStore Tm) : ℕ :=
  (store.map fun e => (e.1.freeVars ∪ e.2.freeVars).sup id).foldr max 0 + 1

theorem lt_knowledgeBound {store : EquationStore Tm} {e : Equation Tm} (member : e ∈ store) {x : ℕ}
    (vars : x ∈ e.1.freeVars ∨ x ∈ e.2.freeVars) : x < knowledgeBound store := by
  have inSup : x ≤ (e.1.freeVars ∪ e.2.freeVars).sup id :=
    Finset.le_sup (f := id) (Finset.mem_union.mpr vars)
  have inFold := le_foldr_max (List.mem_map_of_mem (f := fun e : Equation Tm => (e.1.freeVars ∪ e.2.freeVars).sup id)
    member)
  unfold knowledgeBound
  omega

/-- **The opening that renames each unknown `x` of a rule to `x + N`.** -/
def shift (N : ℕ) : Subst rowSig := fun x => .var (x + N)

/-- The solution that reads each renamed unknown as its row and fixes the others. -/
def shiftedSolution (N : ℕ) (θ : ℕ → Expr) : Subst rowSig := fun v => if N ≤ v then toTerm (θ (v - N)) else .var v

theorem shifted_reads (N : ℕ) (θ : ℕ → Expr) (t : Tm) :
    (shiftedSolution N θ).applyTerm ((shift N).applyTerm t) = toTerm (inst θ t) := by
  rw [← Subst.applyTerm_comp, ← applyTerm_lift]
  congr 1
  funext x
  simp [Subst.comp, shift, shiftedSolution, lift]

omit [DecidableEq O] in
/-- **Renaming the rule's unknowns beyond the knowledge's unknowns is a fresh opening.** -/
theorem shift_fresh {s : SState O} {rows : O → Expr} (ground : GroundLabels s rows)
    (g : Firing O E {r | r ∈ rules} s.frame) (opening : g.opening = shift (knowledgeBound s.knowledge)) :
    g.Fresh X s := by
  intro b (g' : Subst rowSig) (h : Subst rowSig)
  let u : Subst rowSig := fun v => if knowledgeBound s.knowledge ≤ v then h (v - knowledgeBound s.knowledge) else g' v
  refine ⟨u, ?_, ?_⟩
  · intro t mentioned
    show Subst.applyTerm u (Subst.applyTerm (Subst.id rowSig) t) = g'.applyTerm t
    rw [Subst.applyTerm_id]
    rcases mentioned with inFirst | inSecond | ⟨o, present, rfl⟩
    · obtain ⟨e, member, rfl⟩ := List.mem_map.mp inFirst
      exact Subst.applyTerm_congr fun v vars => if_neg (Nat.not_le.mpr (lt_knowledgeBound member (Or.inl vars)))
    · obtain ⟨e, member, rfl⟩ := List.mem_map.mp inSecond
      exact Subst.applyTerm_congr fun v vars => if_neg (Nat.not_le.mpr (lt_knowledgeBound member (Or.inr vars)))
    · rw [ground o present, applyTerm_toTerm, applyTerm_toTerm]
  · intro t _
    show Subst.applyTerm u (Subst.applyTerm g.opening t) = h.applyTerm t
    rw [opening, ← Subst.applyTerm_comp]
    congr 1
    funext x
    show (if knowledgeBound s.knowledge ≤ x + knowledgeBound s.knowledge then
      h (x + knowledgeBound s.knowledge - knowledgeBound s.knowledge) else g' (x + knowledgeBound s.knowledge)) = h x
    rw [if_pos (Nat.le_add_left _ _), Nat.add_sub_cancel]

/-- **Every firing by matching at a ground state with trivial knowledge is an admitted firing of
`RuleSyntax.step`**, and its result reads as the made rows' instances beside the rest, when identities are
infinitely many. -/
theorem admitted_of_match [Infinite O] {s : SState O} {rows : O → Expr} (ground : GroundLabels s rows)
    (knowledge : TrivialKnowledge s.knowledge) {r : SRule} (member : r ∈ rules)
    (fragmentRule : RangeRestrictedPositive r) {θ : ℕ → Expr} {restM : Multiset Expr}
    (split : (r.body.take.map (inst θ) : Multiset Expr) + restM = s.present.val.map rows)
    (reads : ∀ q ∈ r.body.read, inst θ q ∈ restM) (equations : ∀ e ∈ equationsOf r, inst θ e.1 = inst θ e.2) :
    ∃ (g : Firing O E {r | r ∈ rules} s.frame) (admitted : (schematicStep O rules).Admits (s := s) g),
      g.rule = r ∧
        ReadsAs ((schematicStep O rules).result g admitted) ((r.body.produce.map (inst θ) : Multiset Expr) + restM) := by
  obtain ⟨taken, takenNodup, takenIn, takenRows⟩ := exists_taken rows (r.body.take.map (inst θ)) s.present
    (show ((r.body.take.map (inst θ) : List Expr) : Multiset Expr) ≤ s.present.val.map rows from
      (le_add_right le_rfl).trans_eq split)
  have takenSub : taken.toFinset ⊆ s.present := fun o member => takenIn o (List.mem_toFinset.mp member)
  have restEq : restM = (s.present \ taken.toFinset).val.map rows := by
    have whole := bagOf_split rows (C := ⟨[], s.present⟩) takenNodup takenSub
    rw [takenRows] at whole
    exact add_left_cancel (split.trans whole)
  obtain ⟨read, readIn, readRows⟩ := exists_read rows (r.body.read.map (inst θ)) (s.present \ taken.toFinset)
    (fun x inside => by
      obtain ⟨q, inRead, rfl⟩ := List.mem_map.mp inside
      rw [← restEq]
      exact reads q inRead)
  obtain ⟨made, madeNodup, madeLength, madeFresh⟩ := exists_fresh s.present r.body.produce.length
  have collectEmpty : r.collect = [] := fragmentRule.1
  let g : Firing O E {r | r ∈ rules} s.frame :=
    ⟨r, member, PUnit.unit, shift (knowledgeBound s.knowledge), ⟨taken, read, made⟩, []⟩
  have takeLength : r.body.take.length = taken.length := by
    rw [← List.length_map (f := inst θ), ← takenRows, List.length_map]
  have readLength : r.body.read.length = read.length := by
    rw [← List.length_map (f := inst θ), ← readRows, List.length_map]
  have takenPresent : ∀ o ∈ taken, o ∈ s.present := takenIn
  have readPresent : ∀ o ∈ read, o ∈ s.present := fun o inside => (Finset.mem_sdiff.mp (readIn o inside)).1
  have takesMatch : ∀ x ∈ r.body.take.zip taken, inst θ x.1 = rows x.2 := pairs_of_map_eq takenRows.symm
  have readsMatch : ∀ x ∈ r.body.read.zip read, inst θ x.1 = rows x.2 := pairs_of_map_eq readRows.symm
  have agree : ∀ σ' : Subst rowSig, A.Models σ' (g.information X s) →
      ∀ x, Bound g.rule x → σ'.applyTerm (g.opening x) = toTerm (θ x) := fun σ' solved' =>
    solutions_agree g ground θ takeLength readLength takenPresent readPresent takesMatch readsMatch solved'
  have known : X.applyStore ((ext A).weaken g.ext) s.knowledge = s.knowledge :=
    Frames.applyStore_id (X := X) s.knowledge
  have solved : A.Models (shiftedSolution (knowledgeBound s.knowledge) θ) (g.information X s) := by
    intro e inside
    unfold Firing.information at inside
    rw [known] at inside
    simp only [List.mem_append] at inside
    rcases inside with ((old | taking) | reading) | told
    · show Subst.applyTerm _ e.1 = Subst.applyTerm _ e.2
      rw [knowledge e old]
    · obtain ⟨p, o, pair, rfl⟩ := mem_matching g taking
      show Subst.applyTerm _ (Subst.applyTerm (shift _) p) = Subst.applyTerm _ (s.label o)
      rw [shifted_reads, ground o (takenPresent o (List.of_mem_zip pair).2), applyTerm_toTerm, takesMatch _ pair]
    · obtain ⟨p, o, pair, rfl⟩ := mem_matching g reading
      show Subst.applyTerm _ (Subst.applyTerm (shift _) p) = Subst.applyTerm _ (s.label o)
      rw [shifted_reads, ground o (readPresent o (List.of_mem_zip pair).2), applyTerm_toTerm, readsMatch _ pair]
    · obtain ⟨pair, inTell, rfl⟩ := List.mem_map.mp told
      show Subst.applyTerm _ (Subst.applyTerm (shift _) pair.1) = Subst.applyTerm _ (Subst.applyTerm (shift _) pair.2)
      rw [shifted_reads, shifted_reads, equations pair (List.mem_append_left _ inTell)]
  have admitted : (schematicStep O rules).Admits (s := s) g := by
    refine (admits_iff g).mpr ⟨shift_fresh ground g rfl, ⟨takenNodup, madeNodup, takeLength, readLength,
      madeLength.symm, by rw [collectEmpty]; rfl⟩, ?_,
      (Frames.ofSubstitution_solvable_iff A _).mpr ⟨_, solved⟩, ?_, ?_⟩
    · exact ⟨takenSub, fun o inside => readPresent o (List.mem_toFinset.mp inside),
        Finset.disjoint_left.mpr fun o taking reading =>
          (Finset.mem_sdiff.mp (readIn o (List.mem_toFinset.mp reading))).2 taking,
        Finset.disjoint_left.mpr fun o inside present => madeFresh o (List.mem_toFinset.mp inside) present,
        fun query inside => by simp [Selection.commit] at inside⟩
    · intro c inChecks b σ' solved'
      obtain ⟨c₀, inRule, rfl⟩ := List.mem_map.mp inChecks
      have isGuardC := List.all_eq_true.mp fragmentRule.2.1 c₀ inRule
      cases c₀ with
      | equal l r' =>
          have inEquations : (l, r') ∈ equationsOf r :=
            List.mem_append_right _ (List.mem_flatMap.mpr ⟨.equal l r', inRule, List.mem_singleton_self _⟩)
          have written := mem_written_of_equation inEquations
          show Subst.applyTerm σ' (Subst.applyTerm (shift _) l) = Subst.applyTerm σ' (Subst.applyTerm (shift _) r')
          rw [written_reads g (agree σ' solved') fun x vars => fragmentRule.2.2 _ written.1 x vars,
            written_reads g (agree σ' solved') fun x vars => fragmentRule.2.2 _ written.2 x vars,
            equations _ inEquations]
      | predicate quantifier _ => simp [isGuard] at isGuardC
      | count _ _ => simp [isGuard] at isGuardC
    · intro q inside
      have none : (g.collectOpened X).zip g.seen = [] := by
        simp [Firing.collectOpened, g, collectEmpty]
      rw [none] at inside
      exact absurd inside List.not_mem_nil
  refine ⟨g, admitted, rfl, ?_⟩
  have result := result_readsAs ground g admitted fragmentRule.2.2 θ agree
  rw [← restEq, add_comm] at result
  exact result

#print axioms readsAs_unique
#print axioms solutions_agree
#print axioms result_readsAs
#print axioms match_of_admitted
#print axioms shift_fresh
#print axioms admitted_of_match

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation.Schematic
