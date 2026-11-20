import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ModuleReading.Syntax

/-!
# A rule module read as a set-store program, by demand

The reading of `lib/tcalc_modules.metta` (CeTTa), as rules of `RuleSyntax` over a set store. It uses
three kinds of row besides a relation's rows:

* `demandRow C`, `(demand C)`: the call `C` is asked;
* `valueRow C w`, `(value C w)`: the call `C` has the value `w`;
* `stageRow l C [t1, .., ti]`, `(l/i C t1 .. ti)`: rule `l` has matched `C` and its premises
  `1 .. i`, with targets `t1 .. ti` (a query's target is the query itself, `Premise.target`).

Stage `0` of rule `l` is `demandRow lhs` (`stagePattern`). For each module rule `l` with premises
`1 .. n`, `readRule` gives, in the library's order:

* `l/i.ask` (`askRule`): read stage `i-1`, make `(demand K(a))`, for a call premise `K(a) ~> t`;
* `l/i` (`stepRule`): read stage `i-1` and `(value K(a) t)` or the row `R(a)`, make stage `i`;
* `l` (`finalRule`): read stage `n`, make `(value lhs rhs)`.

Every rule only reads and makes. **T0** (`readRule_propagates_iff`): the reading of a module rule is
in the licensed fragment `SetStoreSyntax.Propagates` exactly when the rule is range-restricted.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ModuleReading

open Mettapedia.Logic.LP (LPSignature Term Atom Subst)
open OneFrame (Terms)
open SetStoreSyntax (varsIn mem_variables Propagates agree_of_apply_eq)

universe u

variable {σ : LPSignature.{u, u, u, u}} {L : Type u}

/-! ## Rows -/

section Rows

/-- `(demand C)`: the call `C` is asked. -/
def demandRow (C : Term (readingSignature σ L)) : Term (readingSignature σ L) :=
  .app Head.demand ![C]

/-- `(value C w)`: the call `C` has the value `w`. -/
def valueRow (C w : Term (readingSignature σ L)) : Term (readingSignature σ L) :=
  .app Head.value ![C, w]

/-- `(l/i C t1 .. ti)`: rule `l` has matched the call `C` and its first `i` premises, with targets
`ts = [t1, .., ti]`. -/
def stageRow (l : L) (C : Term (readingSignature σ L)) (ts : List (Term (readingSignature σ L))) :
    Term (readingSignature σ L) :=
  .app (Head.stage l ts.length) fun j => (C :: ts).get j

/-- A relation's row `R(a)`; a query is read as the same row. -/
def atomRow (atom : Atom (readingSignature σ L)) : Term (readingSignature σ L) :=
  .app (Head.rel atom.symbol) atom.args

/-- What a stage stores for a premise: a call's target, or the query itself. -/
def Premise.target : Premise (readingSignature σ L) → Term (readingSignature σ L)
  | .call _ target => target
  | .query atom => atomRow atom

/-- The row a premise's stage rule reads beside the previous stage. -/
def Premise.row : Premise (readingSignature σ L) → Term (readingSignature σ L)
  | .call source target => valueRow source target
  | .query atom => atomRow atom

/-- The targets premises store. -/
def targets (ps : List (Premise (readingSignature σ L))) : List (Term (readingSignature σ L)) :=
  ps.map Premise.target

/-- Stage `i` of rule `l` as a pattern: `(demand lhs)` before any premise, `(l/i lhs t1 .. ti)`
after `i` premises. -/
def stagePattern (l : L) (lhs : Term (readingSignature σ L)) :
    List (Term (readingSignature σ L)) → Term (readingSignature σ L)
  | [] => demandRow lhs
  | t :: ts => stageRow l lhs (t :: ts)

theorem targets_append (pre post : List (Premise (readingSignature σ L))) :
    targets (pre ++ post) = targets pre ++ targets post :=
  List.map_append

theorem targets_length (ps : List (Premise (readingSignature σ L))) : (targets ps).length = ps.length :=
  List.length_map _

end Rows

/-! ## Rows under substitution -/

section Apply

variable (θ : Subst (readingSignature σ L))

theorem apply_demandRow (C : Term (readingSignature σ L)) :
    θ.applyTerm (demandRow C) = demandRow (θ.applyTerm C) := by
  show Term.app (σ := readingSignature σ L) Head.demand (fun i : Fin 1 => θ.applyTerm (![C] i)) =
    Term.app Head.demand ![θ.applyTerm C]
  congr 1
  funext j
  obtain ⟨k, bound⟩ := j
  obtain rfl : k = 0 := by change k < 1 at bound; omega
  rfl

theorem apply_valueRow (C w : Term (readingSignature σ L)) :
    θ.applyTerm (valueRow C w) = valueRow (θ.applyTerm C) (θ.applyTerm w) := by
  show Term.app (σ := readingSignature σ L) Head.value (fun i : Fin 2 => θ.applyTerm (![C, w] i)) =
    Term.app Head.value ![θ.applyTerm C, θ.applyTerm w]
  congr 1
  funext j
  obtain ⟨k, bound⟩ := j
  change k < 2 at bound
  rcases k with _ | _ | k
  · rfl
  · rfl
  · omega

theorem apply_stageRow (l : L) (C : Term (readingSignature σ L)) (ts : List (Term (readingSignature σ L))) :
    θ.applyTerm (stageRow l C ts) = stageRow l (θ.applyTerm C) (ts.map θ.applyTerm) := by
  unfold stageRow
  rw [Mettapedia.Logic.LP.Subst.applyTerm_app]
  congr 1
  · simp
  · apply (Fin.heq_fun_iff (by simp)).mpr
    intro j
    cases j using Fin.cases with
    | zero => rfl
    | succ j => exact (List.getElem_map _).symm

theorem apply_atomRow (atom : Atom (readingSignature σ L)) :
    θ.applyTerm (atomRow atom) = atomRow (θ.applyAtom atom) := rfl

theorem apply_stagePattern (l : L) (lhs : Term (readingSignature σ L)) :
    ∀ ts : List (Term (readingSignature σ L)),
      θ.applyTerm (stagePattern l lhs ts) = stagePattern l (θ.applyTerm lhs) (ts.map θ.applyTerm)
  | [] => apply_demandRow θ lhs
  | t :: ts => apply_stageRow θ l lhs (t :: ts)

theorem apply_stagePattern_cons (l : L) (lhs : Term (readingSignature σ L))
    {pre : List (Premise (readingSignature σ L))} (nonempty : pre ≠ []) :
    θ.applyTerm (stagePattern l lhs (targets pre)) =
      stageRow l (θ.applyTerm lhs) ((targets pre).map θ.applyTerm) := by
  obtain ⟨p, rest, rfl⟩ := List.exists_cons_of_ne_nil nonempty
  exact apply_stageRow θ l lhs _

theorem stagePattern_nil (l : L) (lhs : Term (readingSignature σ L)) :
    θ.applyTerm (stagePattern l lhs (targets [])) = demandRow (θ.applyTerm lhs) :=
  apply_demandRow θ lhs

theorem demandRow_ground {C : Term (readingSignature σ L)} (ground : C.isGround) :
    (demandRow C).isGround := by
  intro i
  obtain ⟨k, bound⟩ := i
  obtain rfl : k = 0 := by change k < 1 at bound; omega
  exact ground

end Apply

/-! ## Distinct heads, injective rows -/

section Injective

theorem demandRow_inj {C C' : Term (readingSignature σ L)} (same : demandRow C = demandRow C') :
    C = C' := by
  have args := eq_of_heq (Term.app.inj same).2
  exact congrFun args 0

theorem valueRow_inj {C C' w w' : Term (readingSignature σ L)} (same : valueRow C w = valueRow C' w') :
    C = C' ∧ w = w' := by
  have args := eq_of_heq (Term.app.inj same).2
  exact ⟨congrFun args 0, congrFun args 1⟩

theorem stageRow_inj {l l' : L} {C C' : Term (readingSignature σ L)}
    {ts ts' : List (Term (readingSignature σ L))} (same : stageRow l C ts = stageRow l' C' ts') :
    l = l' ∧ C = C' ∧ ts = ts' := by
  unfold stageRow at same
  obtain ⟨heads, args⟩ := Term.app.inj same
  obtain ⟨rfl, lengths⟩ := Head.stage.inj heads
  have whole : C :: ts = C' :: ts' := by
    apply List.ext_get (by simp [lengths])
    intro n h₁ h₂
    exact (Fin.heq_fun_iff (by simp [lengths])).mp args ⟨n, h₁⟩
  exact ⟨rfl, List.cons.inj whole⟩

theorem atomRow_inj {a a' : Atom (readingSignature σ L)} (same : atomRow a = atomRow a') : a = a' := by
  obtain ⟨heads, args⟩ := Term.app.inj same
  exact Atom.ext (Head.rel.inj heads) args

theorem demandRow_ne_valueRow (C C' w : Term (readingSignature σ L)) : demandRow C ≠ valueRow C' w :=
  fun same => by have heads := (Term.app.inj same).1; cases heads

theorem demandRow_ne_stageRow (C : Term (readingSignature σ L)) (l : L) (C' : Term (readingSignature σ L))
    (ts : List (Term (readingSignature σ L))) : demandRow C ≠ stageRow l C' ts :=
  fun same => by have heads := (Term.app.inj same).1; cases heads

theorem demandRow_ne_atomRow (C : Term (readingSignature σ L)) (a : Atom (readingSignature σ L)) :
    demandRow C ≠ atomRow a :=
  fun same => by have heads := (Term.app.inj same).1; cases heads

theorem valueRow_ne_stageRow (C w : Term (readingSignature σ L)) (l : L) (C' : Term (readingSignature σ L))
    (ts : List (Term (readingSignature σ L))) : valueRow C w ≠ stageRow l C' ts :=
  fun same => by have heads := (Term.app.inj same).1; cases heads

theorem valueRow_ne_atomRow (C w : Term (readingSignature σ L)) (a : Atom (readingSignature σ L)) :
    valueRow C w ≠ atomRow a :=
  fun same => by have heads := (Term.app.inj same).1; cases heads

theorem stageRow_ne_atomRow (l : L) (C : Term (readingSignature σ L)) (ts : List (Term (readingSignature σ L)))
    (a : Atom (readingSignature σ L)) : stageRow l C ts ≠ atomRow a :=
  fun same => by have heads := (Term.app.inj same).1; cases heads

end Injective

/-! ## Variables of rows -/

section Variables

variable [DecidableEq σ.vars]

theorem varsIn_append (xs ys : List (Term (readingSignature σ L))) :
    varsIn (xs ++ ys) = varsIn xs ∪ varsIn ys := by
  induction xs with
  | nil => simp [varsIn]
  | cons x rest ih => simp [varsIn, ih, Finset.union_assoc]

theorem varsIn_singleton (x : Term (readingSignature σ L)) : varsIn [x] = x.freeVars := by
  simp [varsIn]

theorem freeVars_demandRow (C : Term (readingSignature σ L)) : (demandRow C).freeVars = C.freeVars := by
  change (Finset.univ : Finset (Fin 1)).biUnion (fun i => (![C] i).freeVars) = C.freeVars
  simp

theorem freeVars_valueRow (C w : Term (readingSignature σ L)) :
    (valueRow C w).freeVars = C.freeVars ∪ w.freeVars := by
  change (Finset.univ : Finset (Fin 2)).biUnion (fun i => (![C, w] i).freeVars) = C.freeVars ∪ w.freeVars
  ext v
  simp [Fin.exists_fin_two]

theorem freeVars_stageRow (l : L) (C : Term (readingSignature σ L)) (ts : List (Term (readingSignature σ L))) :
    (stageRow l C ts).freeVars = C.freeVars ∪ varsIn ts := by
  change (Finset.univ : Finset (Fin (ts.length + 1))).biUnion (fun j => ((C :: ts).get j).freeVars) =
    C.freeVars ∪ varsIn ts
  ext v
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_union, mem_variables]
  constructor
  · rintro ⟨j, inside⟩
    cases j using Fin.cases with
    | zero => exact Or.inl (by simpa using inside)
    | succ j => exact Or.inr ⟨ts.get j, List.get_mem ts j, by simpa [List.get_eq_getElem] using inside⟩
  · rintro (inside | ⟨t, member, inside⟩)
    · exact ⟨0, by simpa using inside⟩
    · obtain ⟨j, rfl⟩ := List.get_of_mem member
      exact ⟨j.succ, by simpa [List.get_eq_getElem] using inside⟩

theorem freeVars_atomRow (atom : Atom (readingSignature σ L)) : (atomRow atom).freeVars = atom.freeVars :=
  rfl

theorem freeVars_stagePattern (l : L) (lhs : Term (readingSignature σ L)) :
    ∀ ts : List (Term (readingSignature σ L)), (stagePattern l lhs ts).freeVars = lhs.freeVars ∪ varsIn ts
  | [] => by simp [stagePattern, freeVars_demandRow, varsIn]
  | t :: ts => freeVars_stageRow l lhs (t :: ts)

theorem freeVars_target (p : Premise (readingSignature σ L)) : p.target.freeVars = p.binds := by
  cases p <;> rfl

theorem freeVars_target_subset_row (p : Premise (readingSignature σ L)) : p.target.freeVars ⊆ p.row.freeVars := by
  cases p with
  | call source target => simp [Premise.target, Premise.row, freeVars_valueRow]
  | query atom => exact Finset.Subset.refl _

theorem agree_of_map_eq (θ θ' : Subst (readingSignature σ L)) (ts : List (Term (readingSignature σ L)))
    (same : ts.map θ.applyTerm = ts.map θ'.applyTerm) : ∀ v ∈ varsIn ts, θ v = θ' v := by
  intro v inside
  obtain ⟨t, member, mentions⟩ := (mem_variables ts v).mp inside
  exact agree_of_apply_eq θ θ' t (List.map_inj_left.mp same t member) v mentions

theorem varsIn_targets (ps : List (Premise (readingSignature σ L))) : varsIn (targets ps) = bindsAll ps := by
  induction ps with
  | nil => rfl
  | cons p rest ih => simp [targets, varsIn, bindsAll, freeVars_target, ← ih]

end Variables

/-! ## The reading -/

section Reading

/-- A rule that reads `reads` and makes `makes`: no take, tell, check or collect query. -/
def makeRule (reads makes : List (Term (readingSignature σ L))) : Rule (Terms (Term (readingSignature σ L))) :=
  ⟨PUnit.unit, ⟨[], reads, [], [], makes⟩, []⟩

/-- `l/i.ask`: read stage `i-1`, make `(demand K(a))`, for the call premise `K(a) ~> t`. -/
def askRule (l : L) (lhs : Term (readingSignature σ L)) (ts : List (Term (readingSignature σ L)))
    (source : Term (readingSignature σ L)) : Rule (Terms (Term (readingSignature σ L))) :=
  makeRule [stagePattern l lhs ts] [demandRow source]

/-- `l/i`: read stage `i-1` and the premise's row (`(value K(a) t)` or `R(a)`), make stage `i`. -/
def stepRule (l : L) (lhs : Term (readingSignature σ L)) (ts : List (Term (readingSignature σ L)))
    (p : Premise (readingSignature σ L)) : Rule (Terms (Term (readingSignature σ L))) :=
  makeRule [stagePattern l lhs ts, p.row] [stagePattern l lhs (ts ++ [p.target])]

/-- `l`: read stage `n`, make `(value lhs rhs)`. -/
def finalRule (l : L) (lhs : Term (readingSignature σ L)) (ts : List (Term (readingSignature σ L)))
    (rhs : Term (readingSignature σ L)) : Rule (Terms (Term (readingSignature σ L))) :=
  makeRule [stagePattern l lhs ts] [valueRow lhs rhs]

/-- The name the library gives a rule of the reading: `l/i.ask`, `l/i`, `l`. -/
inductive ReadName (L : Type u) where
  | ask (rule : L) (index : ℕ)
  | step (rule : L) (index : ℕ)
  | final (rule : L)

/-- The rules of premise `i = ts.length + 1`, given the targets `ts` of the premises before it. -/
def premiseRules (l : L) (lhs : Term (readingSignature σ L)) (ts : List (Term (readingSignature σ L))) :
    Premise (readingSignature σ L) → List (ReadName L × Rule (Terms (Term (readingSignature σ L))))
  | .call source target =>
      [(.ask l (ts.length + 1), askRule l lhs ts source),
        (.step l (ts.length + 1), stepRule l lhs ts (.call source target))]
  | .query atom => [(.step l (ts.length + 1), stepRule l lhs ts (.query atom))]

/-- The rules of the remaining premises and the final rule (`tcalc-module:steps`). -/
def steps (l : L) (lhs rhs : Term (readingSignature σ L)) :
    List (Term (readingSignature σ L)) → List (Premise (readingSignature σ L)) →
      List (ReadName L × Rule (Terms (Term (readingSignature σ L))))
  | ts, [] => [(.final l, finalRule l lhs ts rhs)]
  | ts, p :: rest => premiseRules l lhs ts p ++ steps l lhs rhs (ts ++ [p.target]) rest

/-- The reading of one module rule, with the library's names, in the library's order. -/
def readRule (l : L) (r : ModuleRule (readingSignature σ L)) :
    List (ReadName L × Rule (Terms (Term (readingSignature σ L)))) :=
  steps l r.lhs r.rhs [] r.premises

/-- **The reading of a module**: the rules of every module rule's reading. -/
def reading (M : L → ModuleRule (readingSignature σ L)) : Program (Terms (Term (readingSignature σ L))) :=
  {rule | ∃ l, rule ∈ (readRule l (M l)).map Prod.snd}

/-- The reading as a list, module rule by module rule in the order `labels` gives. -/
def readingList (M : L → ModuleRule (readingSignature σ L)) (labels : List L) :
    List (ReadName L × Rule (Terms (Term (readingSignature σ L)))) :=
  labels.flatMap fun l => readRule l (M l)

theorem mem_reading_of_mem_list {M : L → ModuleRule (readingSignature σ L)} {labels : List L}
    {rule : Rule (Terms (Term (readingSignature σ L)))}
    (inside : rule ∈ (readingList M labels).map Prod.snd) : rule ∈ reading M := by
  obtain ⟨⟨name, rule'⟩, member, rfl⟩ := List.mem_map.mp inside
  obtain ⟨l, _, inRule⟩ := List.mem_flatMap.mp member
  exact ⟨l, List.mem_map.mpr ⟨_, inRule, rfl⟩⟩

theorem mem_list_of_mem_reading {M : L → ModuleRule (readingSignature σ L)} {labels : List L}
    (every : ∀ l, l ∈ labels) {rule : Rule (Terms (Term (readingSignature σ L)))}
    (inside : rule ∈ reading M) : rule ∈ (readingList M labels).map Prod.snd := by
  obtain ⟨l, member⟩ := inside
  obtain ⟨pair, inRule, rfl⟩ := List.mem_map.mp member
  exact List.mem_map.mpr ⟨pair, List.mem_flatMap.mpr ⟨l, every l, inRule⟩, rfl⟩

variable {l : L} {lhs rhs : Term (readingSignature σ L)}

theorem mem_premiseRules {ts : List (Term (readingSignature σ L))} {p : Premise (readingSignature σ L)}
    {rule : Rule (Terms (Term (readingSignature σ L)))} :
    rule ∈ (premiseRules l lhs ts p).map Prod.snd ↔
      (∃ source target, p = .call source target ∧ rule = askRule l lhs ts source) ∨
        rule = stepRule l lhs ts p := by
  cases p with
  | call source target => simp [premiseRules]
  | query atom => simp [premiseRules]

/-- Every rule of the reading of the premises `ps` after the targets `ts` is an ask at a call premise,
the stage rule of a premise, or the final rule. -/
theorem of_mem_steps : ∀ (ts : List (Term (readingSignature σ L))) (ps : List (Premise (readingSignature σ L)))
    {rule : Rule (Terms (Term (readingSignature σ L)))},
    rule ∈ (steps l lhs rhs ts ps).map Prod.snd →
      (∃ pre source target post, ps = pre ++ .call source target :: post ∧
          rule = askRule l lhs (ts ++ targets pre) source) ∨
        (∃ pre p post, ps = pre ++ p :: post ∧ rule = stepRule l lhs (ts ++ targets pre) p) ∨
        rule = finalRule l lhs (ts ++ targets ps) rhs
  | ts, [], rule, inside => by
    right; right
    simpa [steps, targets] using inside
  | ts, p :: rest, rule, inside => by
    rw [steps, List.map_append, List.mem_append] at inside
    rcases inside with here | later
    · rcases mem_premiseRules.mp here with ⟨source, target, rfl, rfl⟩ | rfl
      · exact Or.inl ⟨[], source, target, rest, rfl, by simp [targets]⟩
      · exact Or.inr (Or.inl ⟨[], p, rest, rfl, by simp [targets]⟩)
    · rcases of_mem_steps (ts ++ [p.target]) rest later with
          ⟨pre, source, target, post, rfl, rfl⟩ | ⟨pre, q, post, rfl, rfl⟩ | rfl
      · exact Or.inl ⟨p :: pre, source, target, post, rfl, by simp [targets]⟩
      · exact Or.inr (Or.inl ⟨p :: pre, q, post, rfl, by simp [targets]⟩)
      · exact Or.inr (Or.inr (by simp [targets]))

theorem askRule_mem_steps (source target : Term (readingSignature σ L)) (post : List (Premise (readingSignature σ L))) :
    ∀ (ts : List (Term (readingSignature σ L))) (pre : List (Premise (readingSignature σ L))),
      askRule l lhs (ts ++ targets pre) source ∈
        (steps l lhs rhs ts (pre ++ .call source target :: post)).map Prod.snd
  | ts, [] => by simp [steps, premiseRules, targets]
  | ts, p :: pre => by
    have later := askRule_mem_steps source target post (ts ++ [p.target]) pre
    rw [List.cons_append, steps, List.map_append, List.mem_append]
    exact Or.inr (by simpa [targets] using later)

theorem stepRule_mem_steps (p : Premise (readingSignature σ L)) (post : List (Premise (readingSignature σ L))) :
    ∀ (ts : List (Term (readingSignature σ L))) (pre : List (Premise (readingSignature σ L))),
      stepRule l lhs (ts ++ targets pre) p ∈ (steps l lhs rhs ts (pre ++ p :: post)).map Prod.snd
  | ts, [] => by
    rw [List.nil_append, steps, List.map_append, List.mem_append]
    left
    cases p <;> simp [premiseRules, targets]
  | ts, q :: pre => by
    have later := stepRule_mem_steps p post (ts ++ [q.target]) pre
    rw [List.cons_append, steps, List.map_append, List.mem_append]
    exact Or.inr (by simpa [targets] using later)

theorem finalRule_mem_steps :
    ∀ (ts : List (Term (readingSignature σ L))) (ps : List (Premise (readingSignature σ L))),
      finalRule l lhs (ts ++ targets ps) rhs ∈ (steps l lhs rhs ts ps).map Prod.snd
  | ts, [] => by simp [steps, targets]
  | ts, p :: rest => by
    have later := finalRule_mem_steps (ts ++ [p.target]) rest
    rw [steps, List.map_append, List.mem_append]
    exact Or.inr (by simpa [targets] using later)

variable {M : L → ModuleRule (readingSignature σ L)}

/-- **The rules of the reading, flat**: for some module rule `l`, an ask at a call premise, the stage
rule of a premise, or the final rule, each after the targets of the premises before it. -/
theorem mem_reading_iff {rule : Rule (Terms (Term (readingSignature σ L)))} :
    rule ∈ reading M ↔ ∃ l,
      (∃ pre source target post, (M l).premises = pre ++ .call source target :: post ∧
          rule = askRule l (M l).lhs (targets pre) source) ∨
        (∃ pre p post, (M l).premises = pre ++ p :: post ∧ rule = stepRule l (M l).lhs (targets pre) p) ∨
        rule = finalRule l (M l).lhs (targets (M l).premises) (M l).rhs := by
  constructor
  · rintro ⟨l, inside⟩
    exact ⟨l, by simpa using of_mem_steps (l := l) [] (M l).premises inside⟩
  · rintro ⟨l, ⟨pre, source, target, post, split, rfl⟩ | ⟨pre, p, post, split, rfl⟩ | rfl⟩
    · refine ⟨l, ?_⟩
      have inside := askRule_mem_steps (l := l) (lhs := (M l).lhs) (rhs := (M l).rhs) source target post [] pre
      rw [List.nil_append, ← split] at inside
      exact inside
    · refine ⟨l, ?_⟩
      have inside := stepRule_mem_steps (l := l) (lhs := (M l).lhs) (rhs := (M l).rhs) p post [] pre
      rw [List.nil_append, ← split] at inside
      exact inside
    · exact ⟨l, by simpa [readRule] using finalRule_mem_steps (l := l) (lhs := (M l).lhs) (rhs := (M l).rhs) [] (M l).premises⟩

theorem askRule_mem_reading (l : L) {pre post : List (Premise (readingSignature σ L))}
    {source target : Term (readingSignature σ L)} (split : (M l).premises = pre ++ .call source target :: post) :
    askRule l (M l).lhs (targets pre) source ∈ reading M :=
  mem_reading_iff.mpr ⟨l, Or.inl ⟨pre, source, target, post, split, rfl⟩⟩

theorem stepRule_mem_reading (l : L) {pre post : List (Premise (readingSignature σ L))}
    {p : Premise (readingSignature σ L)} (split : (M l).premises = pre ++ p :: post) :
    stepRule l (M l).lhs (targets pre) p ∈ reading M :=
  mem_reading_iff.mpr ⟨l, Or.inr (Or.inl ⟨pre, p, post, split, rfl⟩)⟩

theorem finalRule_mem_reading (l : L) :
    finalRule l (M l).lhs (targets (M l).premises) (M l).rhs ∈ reading M :=
  mem_reading_iff.mpr ⟨l, Or.inr (Or.inr rfl)⟩

/-- Every rule of the reading is a `makeRule`. -/
theorem exists_makeRule_of_mem_reading {rule : Rule (Terms (Term (readingSignature σ L)))}
    (inside : rule ∈ reading M) : ∃ reads makes, rule = makeRule reads makes := by
  obtain ⟨_, ⟨_, _, _, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ | rfl⟩ := mem_reading_iff.mp inside <;>
    exact ⟨_, _, rfl⟩

theorem checks_of_mem_reading {rule : Rule (Terms (Term (readingSignature σ L)))}
    (inside : rule ∈ reading M) : rule.body.checks = [] := by
  obtain ⟨reads, makes, rfl⟩ := exists_makeRule_of_mem_reading inside
  rfl

end Reading

/-! ## T0: the reading is in the licensed fragment exactly for range-restricted rules -/

section Licence

variable [DecidableEq σ.vars]

theorem makeRule_propagates_iff (reads makes : List (Term (readingSignature σ L))) :
    Propagates (makeRule reads makes) ↔ varsIn makes ⊆ varsIn reads := by
  constructor
  · exact fun pure => pure.madeScoped
  · intro scopedMakes
    refine ⟨rfl, rfl, ⟨fun check inside => absurd inside List.not_mem_nil, rfl⟩, scopedMakes, ?_⟩
    simp [makeRule, varsIn]

theorem askRule_propagates_iff (l : L) (lhs : Term (readingSignature σ L)) (ts : List (Term (readingSignature σ L)))
    (source : Term (readingSignature σ L)) :
    Propagates (askRule l lhs ts source) ↔ source.freeVars ⊆ lhs.freeVars ∪ varsIn ts := by
  simp [askRule, makeRule_propagates_iff, varsIn_singleton, freeVars_demandRow, freeVars_stagePattern]

theorem stepRule_propagates (l : L) (lhs : Term (readingSignature σ L)) (ts : List (Term (readingSignature σ L)))
    (p : Premise (readingSignature σ L)) : Propagates (stepRule l lhs ts p) := by
  rw [stepRule, makeRule_propagates_iff]
  have target := freeVars_target_subset_row p
  intro v inside
  simp only [varsIn, Finset.union_empty, freeVars_stagePattern, varsIn_append, Finset.mem_union] at inside ⊢
  rcases inside with inLhs | inTs | inTarget
  · exact Or.inl (Or.inl inLhs)
  · exact Or.inl (Or.inr inTs)
  · exact Or.inr (target inTarget)

theorem finalRule_propagates_iff (l : L) (lhs : Term (readingSignature σ L)) (ts : List (Term (readingSignature σ L)))
    (rhs : Term (readingSignature σ L)) :
    Propagates (finalRule l lhs ts rhs) ↔ rhs.freeVars ⊆ lhs.freeVars ∪ varsIn ts := by
  simp only [finalRule, makeRule_propagates_iff, varsIn_singleton, freeVars_valueRow, freeVars_stagePattern]
  constructor
  · exact fun both => Finset.union_subset_right both
  · exact fun right => Finset.union_subset Finset.subset_union_left right

/-- **T0.** The reading of a module rule only reads and makes, with every made variable read
(`SetStoreSyntax.Propagates`), exactly when the rule is range-restricted. -/
theorem readRule_propagates_iff (l : L) (r : ModuleRule (readingSignature σ L)) :
    (∀ rule ∈ (readRule l r).map Prod.snd, Propagates rule) ↔ RangeRestricted r := by
  constructor
  · intro pure
    refine ⟨fun pre source target post split => ?_, ?_⟩
    · have member : askRule l r.lhs (targets pre) source ∈ (readRule l r).map Prod.snd := by
        have inside := askRule_mem_steps (l := l) (lhs := r.lhs) (rhs := r.rhs) source target post [] pre
        rw [List.nil_append, ← split] at inside
        exact inside
      have bounded := (askRule_propagates_iff l r.lhs (targets pre) source).mp (pure _ member)
      rwa [varsIn_targets] at bounded
    · have member : finalRule l r.lhs (targets r.premises) r.rhs ∈ (readRule l r).map Prod.snd := by
        simpa [readRule] using finalRule_mem_steps (l := l) (lhs := r.lhs) (rhs := r.rhs) [] r.premises
      have bounded := (finalRule_propagates_iff l r.lhs (targets r.premises) r.rhs).mp (pure _ member)
      rwa [varsIn_targets] at bounded
  · intro rr rule inside
    rcases of_mem_steps (l := l) [] r.premises inside with
        ⟨pre, source, target, post, split, rfl⟩ | ⟨pre, p, post, split, rfl⟩ | rfl
    · rw [List.nil_append, askRule_propagates_iff, varsIn_targets]
      exact rr.calls pre source target post split
    · exact stepRule_propagates l r.lhs _ p
    · rw [List.nil_append, finalRule_propagates_iff, varsIn_targets]
      exact rr.rhs

/-- **T0.** Every rule of the reading of a range-restricted module is `Propagates`. -/
theorem reading_propagates {M : L → ModuleRule (readingSignature σ L)} (rr : ∀ l, RangeRestricted (M l)) :
    ∀ rule ∈ reading M, Propagates rule := by
  rintro rule ⟨l, inside⟩
  exact (readRule_propagates_iff l (M l)).mpr (rr l) rule inside

end Licence

#print axioms apply_stageRow
#print axioms apply_stagePattern
#print axioms stageRow_inj
#print axioms atomRow_inj
#print axioms freeVars_stagePattern
#print axioms varsIn_targets
#print axioms of_mem_steps
#print axioms mem_reading_iff
#print axioms makeRule_propagates_iff
#print axioms readRule_propagates_iff
#print axioms reading_propagates

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ModuleReading
