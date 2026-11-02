import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.Rename
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.SourceMatching

/-!
# Gather patterns over binding trees, and the matcher on trees

This module is the specification that every store of binding trees implements; it does not
depend on how trees are stored. Its content is the representation-independent half of the
shifts layer's `SharedTerms/Matching.lean`, restated here so that the thinnings layer does not
depend on the shifts files.

A gather pattern is a binding tree with **pattern variables** (`TreePat`): `mvar v` matches any
subtree, `idx n` matches exactly the variable `n`, and a node pattern matches a node with the same
head and fields. Matching is syntactic on nameless trees, so it is matching up to
alpha-equivalence.

* `treeLayer`: the patterns and trees form a term layer of the source semantics
  (`Sources.TermLayer`) whose declared theory is equality.
* `matchT`: the matcher on trees; it is **sound, complete and minimal** for `treeLayer`
  (`treeMatcher_sound`, `treeMatcher_complete`, `treeMatcher_minimal`), the hypotheses under which
  the compiled rows of a transform are its declarative rows (`Sources.agreement`).

Example: `(app $f $f)` matches `(app t t)` and not `(app t u)` for `t ≠ u`; `(lam (app 0 $x))`
matches `λy. (y c)` with `$x := c`, whatever the bound variable was called.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings

open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources

variable {Head : Type} {V : Type}

/-! ## Patterns -/

mutual

/-- A gather pattern: a binding tree with pattern variables. -/
inductive TreePat (Head : Type) (V : Type) where
  | mvar (v : V)
  | idx (n : ℕ)
  | node (head : Head) (fields : TreePatFields Head V)

/-- The fields of a node pattern, with their binder counts. -/
inductive TreePatFields (Head : Type) (V : Type) where
  | nil
  | cons (depth : ℕ) (p : TreePat Head V) (rest : TreePatFields Head V)

end

mutual

/-- The pattern variables of a pattern. -/
def TreePat.vars [DecidableEq V] : TreePat Head V → Finset V
  | .mvar v => {v}
  | .idx _ => ∅
  | .node _ fields => TreePatFields.vars fields

def TreePatFields.vars [DecidableEq V] : TreePatFields Head V → Finset V
  | .nil => ∅
  | .cons _ p rest => TreePat.vars p ∪ TreePatFields.vars rest

end

mutual

/-- Instantiate a pattern: replace each pattern variable by its value. -/
def TreePat.inst (σ : Subst V (Term Head)) : TreePat Head V → Option (Term Head)
  | .mvar v => σ v
  | .idx n => some (.idx n)
  | .node head fields => (TreePatFields.inst σ fields).map (.node head)

def TreePatFields.inst (σ : Subst V (Term Head)) : TreePatFields Head V → Option (Fields Head)
  | .nil => some .nil
  | .cons d p rest =>
      match TreePat.inst σ p, TreePatFields.inst σ rest with
      | some t, some ts => some (.cons d t ts)
      | _, _ => none

end

section Laws

variable [DecidableEq V]

mutual

theorem TreePat.inst_isSome (σ : Subst V (Term Head)) (p : TreePat Head V) :
    (p.inst σ).isSome ↔ ∀ v ∈ p.vars, (σ v).isSome := by
  cases p with
  | mvar v => simp [TreePat.inst, TreePat.vars]
  | idx n => simp [TreePat.inst, TreePat.vars]
  | node head fields =>
      simp only [TreePat.inst, TreePat.vars, Option.isSome_map]
      exact TreePatFields.inst_isSome σ fields

theorem TreePatFields.inst_isSome (σ : Subst V (Term Head)) (fields : TreePatFields Head V) :
    (fields.inst σ).isSome ↔ ∀ v ∈ fields.vars, (σ v).isSome := by
  cases fields with
  | nil => simp [TreePatFields.inst, TreePatFields.vars]
  | cons d p rest =>
      simp only [TreePatFields.inst, TreePatFields.vars, Finset.mem_union]
      have hp := TreePat.inst_isSome σ p
      have hr := TreePatFields.inst_isSome σ rest
      constructor
      · intro h v m
        cases ep : p.inst σ with
        | none => rw [ep] at h; simp at h
        | some t =>
            cases er : rest.inst σ with
            | none => rw [ep, er] at h; simp at h
            | some ts =>
                rcases m with m | m
                · exact hp.mp (by rw [ep]; rfl) v m
                · exact hr.mp (by rw [er]; rfl) v m
      · intro h
        obtain ⟨t, et⟩ := Option.isSome_iff_exists.mp (hp.mpr fun v m => h v (Or.inl m))
        obtain ⟨ts, ets⟩ := Option.isSome_iff_exists.mp (hr.mpr fun v m => h v (Or.inr m))
        rw [et, ets]; rfl

end

mutual

theorem TreePat.inst_local (σ τ : Subst V (Term Head)) (p : TreePat Head V)
    (same : ∀ v ∈ p.vars, σ v = τ v) : p.inst σ = p.inst τ := by
  cases p with
  | mvar v => simpa [TreePat.inst, TreePat.vars] using same v
  | idx n => rfl
  | node head fields =>
      simp only [TreePat.inst]
      rw [TreePatFields.inst_local σ τ fields same]

theorem TreePatFields.inst_local (σ τ : Subst V (Term Head)) (fields : TreePatFields Head V)
    (same : ∀ v ∈ fields.vars, σ v = τ v) : fields.inst σ = fields.inst τ := by
  cases fields with
  | nil => rfl
  | cons d p rest =>
      simp only [TreePatFields.inst]
      rw [TreePat.inst_local σ τ p (fun v m => same v (by simp [TreePatFields.vars, m])),
        TreePatFields.inst_local σ τ rest (fun v m => same v (by simp [TreePatFields.vars, m]))]

end

/-- **Binding trees with pattern variables form a term layer** whose declared theory is equality:
two stored trees are equal values exactly when they are the same tree. -/
def treeLayer : TermLayer V (Term Head) (TreePat Head V) where
  E := (· = ·)
  equivalence := ⟨fun _ => rfl, fun h => h.symm, fun h k => h.trans k⟩
  vars := TreePat.vars
  inst σ p := p.inst σ
  inst_bound σ p := (TreePat.inst_isSome σ p).mp
  inst_local σ τ p same := TreePat.inst_local σ τ p same
  inst_congr σ τ p rel := by
    have same : ∀ v ∈ p.vars, σ v = τ v := fun v m => by
      rcases optionRel_iff.mp (rel v m) with ⟨h1, h2⟩ | ⟨x, y, h1, h2, e⟩
      · rw [h1, h2]
      · rw [h1, h2, show x = y from e]
    rw [TreePat.inst_local σ τ p same]
    cases p.inst τ with
    | none => exact Option.Rel.none
    | some t => exact Option.Rel.some rfl

/-- Unannotated structural patterns still instantiate for every fully bound assignment. -/
theorem treeLayer_total : (treeLayer (Head := Head) (V := V)).Total :=
  fun σ p bound => (TreePat.inst_isSome σ p).mpr bound

end Laws

/-! ## The matcher on trees -/

section TreeMatcher

variable [DecidableEq V] [DecidableEq Head]

mutual

/-- Match a pattern against a tree, extending `σ`. -/
def matchT : TreePat Head V → Subst V (Term Head) → Term Head → Option (Subst V (Term Head))
  | .mvar v, σ, t =>
      match σ v with
      | some u => if u = t then some σ else none
      | none => some (Function.update σ v (some t))
  | .idx n, σ, t => if t = .idx n then some σ else none
  | .node head ps, σ, .node head' fs => if head = head' then matchFieldsT ps σ fs else none
  | .node _ _, _, .idx _ => none

def matchFieldsT : TreePatFields Head V → Subst V (Term Head) → Fields Head →
    Option (Subst V (Term Head))
  | .nil, σ, .nil => some σ
  | .cons d p ps, σ, .cons d' t ts =>
      if d = d' then (matchT p σ t).bind fun σ' => matchFieldsT ps σ' ts else none
  | .nil, _, .cons _ _ _ => none
  | .cons _ _ _, _, .nil => none

end

omit [DecidableEq Head] in
theorem inst_extends {σ τ : Subst V (Term Head)} {p : TreePat Head V} {t : Term Head}
    (inst : p.inst σ = some t) (grow : Extends σ τ) : p.inst τ = some t := by
  rw [← inst]
  refine (TreePat.inst_local σ τ p fun v mem => ?_).symm
  have bound : (σ v).isSome := (TreePat.inst_isSome σ p).mp (by rw [inst]; rfl) v mem
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp bound
  rw [ha, grow v a ha]

mutual

/-- **The tree matcher is sound**: its answer extends `σ`, binds only the pattern's variables, and
instantiates the pattern to the tree. -/
theorem matchT_sound : ∀ (p : TreePat Head V) (σ τ : Subst V (Term Head)) (t : Term Head),
    matchT p σ t = some τ → Extends σ τ ∧ (∀ v, v ∉ p.vars → τ v = σ v) ∧ p.inst τ = some t
  | .mvar v, σ, τ, t, h => by
      cases hv : σ v with
      | some u =>
          simp only [matchT, hv] at h
          by_cases e : u = t
          · rw [if_pos e] at h
            cases h; subst e
            exact ⟨Extends.refl _, fun _ _ => rfl, by simpa [TreePat.inst] using hv⟩
          · rw [if_neg e] at h; cases h
      | none =>
          simp only [matchT, hv] at h
          cases h
          refine ⟨fun w a hw => ?_, fun w notIn => ?_, by simp [TreePat.inst]⟩
          · have : w ≠ v := fun e => by rw [e, hv] at hw; cases hw
            simp [Function.update, this, hw]
          · have : w ≠ v := by simpa [TreePat.vars] using notIn
            simp [Function.update, this]
  | .idx n, σ, τ, t, h => by
      simp only [matchT] at h
      by_cases e : t = .idx n
      · rw [if_pos e] at h; cases h; subst e
        exact ⟨Extends.refl _, fun _ _ => rfl, rfl⟩
      · rw [if_neg e] at h; cases h
  | .node head ps, σ, τ, .node head' fs, h => by
      simp only [matchT] at h
      by_cases e : head = head'
      · rw [if_pos e] at h; subst e
        obtain ⟨grow, only, inst⟩ := matchFieldsT_sound ps σ τ fs h
        exact ⟨grow, fun v notIn => only v (by simpa [TreePat.vars] using notIn),
          by simp [TreePat.inst, inst]⟩
      · rw [if_neg e] at h; cases h
  | .node _ _, _, _, .idx _, h => by simp [matchT] at h

theorem matchFieldsT_sound : ∀ (ps : TreePatFields Head V) (σ τ : Subst V (Term Head))
    (fs : Fields Head), matchFieldsT ps σ fs = some τ →
      Extends σ τ ∧ (∀ v, v ∉ ps.vars → τ v = σ v) ∧ ps.inst τ = some fs
  | .nil, σ, τ, .nil, h => by
      simp only [matchFieldsT] at h; cases h
      exact ⟨Extends.refl _, fun _ _ => rfl, rfl⟩
  | .cons d p ps, σ, τ, .cons d' t ts, h => by
      simp only [matchFieldsT] at h
      by_cases e : d = d'
      · rw [if_pos e] at h; subst e
        cases h1 : matchT p σ t with
        | none => rw [h1] at h; cases h
        | some σ' =>
            rw [h1, Option.bind_some] at h
            obtain ⟨g1, o1, i1⟩ := matchT_sound p σ σ' t h1
            obtain ⟨g2, o2, i2⟩ := matchFieldsT_sound ps σ' τ ts h
            refine ⟨g1.trans g2, fun v notIn => ?_, ?_⟩
            · simp only [TreePatFields.vars, Finset.mem_union, not_or] at notIn
              rw [o2 v notIn.2, o1 v notIn.1]
            · simp [TreePatFields.inst, inst_extends i1 g2, i2]
      · rw [if_neg e] at h; cases h
  | .nil, _, _, .cons _ _ _, h => by simp [matchFieldsT] at h
  | .cons _ _ _, _, _, .nil, h => by simp [matchFieldsT] at h

end

mutual

/-- **The tree matcher is complete**: every substitution that extends `σ`, binds only the
pattern's variables and instantiates the pattern to the tree is its answer. -/
theorem matchT_complete : ∀ (p : TreePat Head V) (σ τ : Subst V (Term Head)) (t : Term Head),
    Extends σ τ → (∀ v, v ∉ p.vars → τ v = σ v) → p.inst τ = some t → matchT p σ t = some τ
  | .mvar v, σ, τ, t, grow, only, inst => by
      simp only [TreePat.inst] at inst
      cases hv : σ v with
      | some u =>
          have tv := grow v u hv
          rw [inst] at tv
          cases tv
          simp only [matchT, hv, ite_true]
          congr 1
          funext w
          by_cases e : w = v
          · subst e; rw [hv, inst]
          · exact (only w (by simp [TreePat.vars, e])).symm
      | none =>
          simp only [matchT, hv]
          congr 1
          funext w
          by_cases e : w = v
          · subst e; simp [inst]
          · simp [Function.update, e, only w (by simp [TreePat.vars, e])]
  | .idx n, σ, τ, t, _, only, inst => by
      simp only [TreePat.inst, Option.some.injEq] at inst
      subst inst
      simp only [matchT, ite_true]
      congr 1
      funext w
      exact (only w (by simp [TreePat.vars])).symm
  | .node head ps, σ, τ, t, grow, only, inst => by
      simp only [TreePat.inst, Option.map_eq_some_iff] at inst
      obtain ⟨fs, hfs, rfl⟩ := inst
      simp only [matchT, ite_true]
      exact matchFieldsT_complete ps σ τ fs grow (fun v notIn => only v (by simpa [TreePat.vars] using notIn)) hfs

theorem matchFieldsT_complete : ∀ (ps : TreePatFields Head V) (σ τ : Subst V (Term Head))
    (fs : Fields Head), Extends σ τ → (∀ v, v ∉ ps.vars → τ v = σ v) → ps.inst τ = some fs →
      matchFieldsT ps σ fs = some τ
  | .nil, σ, τ, fs, _, only, inst => by
      simp only [TreePatFields.inst, Option.some.injEq] at inst
      subst inst
      simp only [matchFieldsT]
      congr 1
      funext w
      exact (only w (by simp [TreePatFields.vars])).symm
  | .cons d p ps, σ, τ, fs, grow, only, inst => by
      simp only [TreePatFields.inst] at inst
      cases ip : p.inst τ with
      | none => rw [ip] at inst; cases inst
      | some t =>
          cases irest : ps.inst τ with
          | none => rw [ip, irest] at inst; cases inst
          | some ts =>
              rw [ip, irest] at inst
              cases inst
              let σ' : Subst V (Term Head) := fun w => if w ∈ p.vars then τ w else σ w
              have first : matchT p σ t = some σ' := by
                refine matchT_complete p σ σ' t (fun w a h => ?_) (fun w notIn => ?_) ?_
                · simp only [σ']; split_ifs
                  · exact grow w a h
                  · exact h
                · simp [σ', notIn]
                · rw [← ip]
                  exact TreePat.inst_local σ' τ p fun w m => by simp [σ', m]
              simp only [matchFieldsT, ite_true, first, Option.bind_some]
              refine matchFieldsT_complete ps σ' τ ts (fun w a h => ?_) (fun w notIn => ?_) irest
              · simp only [σ'] at h; split_ifs at h
                · exact h
                · exact grow w a h
              · simp only [σ']
                split_ifs with m
                · rfl
                · exact only w (by simp [TreePatFields.vars, m, notIn])

end

/-- The tree matcher as a matcher of the source semantics. -/
def treeMatcher : Matcher V (Term Head) (TreePat Head V) := fun p σ t => (matchT p σ t).toList

theorem treeMatcher_sound : Matcher.Sound (treeLayer (Head := Head) (V := V)) treeMatcher := by
  intro p σ t τ mem
  have h : matchT p σ t = some τ := by
    simp only [treeMatcher] at mem
    cases e : matchT p σ t with
    | none => rw [e] at mem; simp at mem
    | some τ' => rw [e] at mem; simp at mem; rw [mem]
  obtain ⟨grow, only, inst⟩ := matchT_sound p σ τ t h
  exact ⟨grow, only, ⟨t, inst, rfl⟩⟩

theorem treeMatcher_complete : Matcher.Complete (treeLayer (Head := Head) (V := V)) treeMatcher := by
  intro p σ σ' t τ' same step
  have hσ : σ = σ' := substEquiv_eq_iff.mp same
  subst hσ
  obtain ⟨u, inst, e⟩ := step.solves
  have e' : u = t := e
  subst e'
  refine ⟨τ', ?_, SubstEquiv.refl (treeLayer (Head := Head) (V := V)).equivalence τ'⟩
  simp [treeMatcher, matchT_complete p σ τ' u step.extends_ step.only inst]

theorem treeMatcher_minimal : Matcher.Minimal (treeLayer (Head := Head) (V := V)) treeMatcher := by
  intro p σ t
  cases matchT p σ t <;> simp [treeMatcher]

end TreeMatcher

/-! ## Controls -/

namespace PatternControls

open RenameControls

/-- `(app $0 $0)`. -/
def pDiag : TreePat H ℕ := .node .app (.cons 0 (.mvar 0) (.cons 0 (.mvar 0) .nil))

/-- `(lam (app 0 $0))`: under the binder, the bound variable applied to anything. -/
def pApplyBound : TreePat H ℕ := .node .lam (.cons 1 (.node .app (.cons 0 (.idx 0) (.cons 0 (.mvar 0) .nil))) .nil)

/-- Positive: `(app $0 $0)` matches `(app 3 3)`. -/
theorem diag_matches : (matchT pDiag (fun _ => none) (app (.idx 3) (.idx 3))).isSome = true := by
  decide

/-- Negative: `(app $0 $0)` does not match `(app 3 4)`. -/
theorem diag_refuses : (matchT pDiag (fun _ => none) (app (.idx 3) (.idx 4))).isSome = false := by
  decide

/-- Positive: `(lam (app 0 $0))` matches `λ. (0 5)`, binding `$0` to the variable `5` seen
under the binder. -/
theorem bound_matches :
    ((matchT pApplyBound (fun _ => none) (lam (app (.idx 0) (.idx 5)))).map fun σ => σ 0) =
      some (some (.idx 5)) := by
  decide

/-- Negative: it does not match `λ. (1 0)`, whose head applies a free variable. -/
theorem bound_refuses : (matchT pApplyBound (fun _ => none) (lam (app (.idx 1) (.idx 0)))).isSome = false := by
  decide

end PatternControls

end Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings
