import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.SharedTerms.Operations
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.SourceMatching

/-!
# Matching binding trees, on trees and on shared terms

A gather pattern is a binding tree with **pattern variables** (`TreePat`): `mvar v` matches any
subtree, `idx n` matches exactly the index `n`, and a node pattern matches a node with the same head
and fields. Matching is syntactic on nameless trees, so it is matching up to alpha-equivalence.

* `treeLayer`: the patterns and trees form a term layer of the source semantics
  (`Sources.TermLayer`) whose declared theory is equality.
* `matchT`: the matcher on trees; it is **sound, complete and minimal** for `treeLayer`
  (`matchT_sound`, `matchT_complete`, `treeMatcher_minimal`), the hypotheses under which the
  compiled rows of a transform are its declarative rows (`Sources.agreement`).
* `matchR`: the same matcher run on references into a canonical store. It takes nodes apart with
  `view`, and compares the values of a repeated variable by **pointer equality**. **It computes
  exactly what `matchT` computes on the unfolded trees** (`matchR_spec`).
* `instR`: building a template's instance in the store computes exactly `TreePat.inst`
  (`instR_spec`).

Example (`MatchControls`): the pattern `(app $f $f)` matches `(app t t)` for a stored `t` by
comparing two references, and fails on `(app t u)` for `t ≠ u`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.SharedTerms

open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources

variable {Head : Type} {V : Type}

/-! ## Deciding equality of trees -/

mutual

/-- Structural comparison of trees. -/
def termBeq [DecidableEq Head] : Term Head → Term Head → Bool
  | .idx a, .idx b => decide (a = b)
  | .node h fs, .node h' fs' => decide (h = h') && fieldsBeq fs fs'
  | .idx _, .node _ _ => false
  | .node _ _, .idx _ => false

def fieldsBeq [DecidableEq Head] : Fields Head → Fields Head → Bool
  | .nil, .nil => true
  | .cons d t r, .cons d' t' r' => decide (d = d') && termBeq t t' && fieldsBeq r r'
  | .nil, .cons _ _ _ => false
  | .cons _ _ _, .nil => false

end

mutual

theorem termBeq_iff [DecidableEq Head] (s t : Term Head) : termBeq s t = true ↔ s = t := by
  cases s with
  | idx a =>
      cases t with
      | idx b => simp [termBeq]
      | node _ _ => simp [termBeq]
  | node h fs =>
      cases t with
      | idx b => simp [termBeq]
      | node h' fs' =>
          simp only [termBeq, Bool.and_eq_true, decide_eq_true_eq, Term.node.injEq]
          rw [fieldsBeq_iff fs fs']

theorem fieldsBeq_iff [DecidableEq Head] (f g : Fields Head) : fieldsBeq f g = true ↔ f = g := by
  cases f with
  | nil =>
      cases g with
      | nil => simp [fieldsBeq]
      | cons _ _ _ => simp [fieldsBeq]
  | cons d t r =>
      cases g with
      | nil => simp [fieldsBeq]
      | cons d' t' r' =>
          simp only [fieldsBeq, Bool.and_eq_true, decide_eq_true_eq, Fields.cons.injEq]
          rw [termBeq_iff t t', fieldsBeq_iff r r']
          tauto

end

instance [DecidableEq Head] : DecidableEq (Term Head) :=
  fun s t => decidable_of_iff _ (termBeq_iff s t)

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

/-! ## The matcher on shared terms -/

section SharedMatcher

variable [DecidableEq V] [DecidableEq Head]

/-- Read a substitution of references as one of trees. -/
def unfoldSubst (St : Store Head) (σ : Subst V Ref) : Subst V (Term Head) :=
  fun v => (σ v).map (unfold St)

/-- A substitution of references is canonical in a store. -/
def CanonSubst (St : Store Head) (σ : Subst V Ref) : Prop := ∀ v r, σ v = some r → CanonRef St r

omit [DecidableEq V] [DecidableEq Head] in
theorem CanonSubst.prefix {St St' : Store Head} (topo : Topo St) (grow : St <+: St')
    {σ : Subst V Ref} (canon : CanonSubst St σ) : CanonSubst St' σ :=
  fun v r h => (canon v r h).prefix topo grow

omit [DecidableEq V] [DecidableEq Head] in
theorem unfoldSubst_prefix {St St' : Store Head} (topo : Topo St) (grow : St <+: St')
    {σ : Subst V Ref} (canon : CanonSubst St σ) : unfoldSubst St' σ = unfoldSubst St σ := by
  funext v
  simp only [unfoldSubst]
  cases h : σ v with
  | none => rfl
  | some r => simp [unfold_prefix topo grow (canon v r h).valid]

omit [DecidableEq Head] in
theorem unfoldSubst_update (St : Store Head) (σ : Subst V Ref) (v : V) (r : Ref) :
    unfoldSubst St (Function.update σ v (some r)) =
      Function.update (unfoldSubst St σ) v (some (unfold St r)) := by
  funext w
  by_cases e : w = v
  · subst e; simp [unfoldSubst]
  · simp [unfoldSubst, Function.update, e]

mutual

/-- **Match a pattern against a reference**: take nodes apart with `view`, compare the values of
a repeated variable by pointer equality. The store may grow (views push shifts into fields). -/
def matchR : TreePat Head V → Store Head → Subst V Ref → Ref → Store Head × Option (Subst V Ref)
  | .mvar v, St, σ, r =>
      match σ v with
      | some u => (St, if u = r then some σ else none)
      | none => (St, some (Function.update σ v (some r)))
  | .idx n, St, σ, r =>
      match (view St r).2 with
      | .idx m => ((view St r).1, if m = n then some σ else none)
      | .node _ _ => ((view St r).1, none)
  | .node head ps, St, σ, r =>
      match (view St r).2 with
      | .node head' fs =>
          if head = head' then matchFieldsR ps (view St r).1 σ fs else ((view St r).1, none)
      | .idx _ => ((view St r).1, none)

def matchFieldsR : TreePatFields Head V → Store Head → Subst V Ref → List (ℕ × Ref) →
    Store Head × Option (Subst V Ref)
  | .nil, St, σ, [] => (St, some σ)
  | .cons d p ps, St, σ, (d', r) :: rest =>
      if d = d' then
        match matchR p St σ r with
        | (St1, some σ') => matchFieldsR ps St1 σ' rest
        | (St1, none) => (St1, none)
      else (St, none)
  | .nil, St, _, _ :: _ => (St, none)
  | .cons _ _ _, St, _, [] => (St, none)

end

/-- What `matchR` promises: the store grows and stays canonical, the answer's references are
canonical, and the answer, unfolded, is the tree matcher's answer. -/
def MatchROk (St St' : Store Head) (res : Option (Subst V Ref))
    (expected : Option (Subst V (Term Head))) : Prop :=
  St <+: St' ∧ Canonical St' ∧ (∀ τ, res = some τ → CanonSubst St' τ) ∧
    res.map (unfoldSubst St') = expected

mutual

/-- **Matching on shared terms is matching on the trees they stand for.** -/
theorem matchR_spec : ∀ (p : TreePat Head V) (St : Store Head) (σ : Subst V Ref) (r : Ref),
    Canonical St → CanonSubst St σ → CanonRef St r →
    MatchROk St (matchR p St σ r).1 (matchR p St σ r).2 (matchT p (unfoldSubst St σ) (unfold St r))
  | .mvar v, St, σ, r, canon, hσ, hr => by
      simp only [matchR]
      cases hv : σ v with
      | some u =>
          have hu := hσ v u hv
          have tv : unfoldSubst St σ v = some (unfold St u) := by simp [unfoldSubst, hv]
          simp only [matchT, tv]
          refine ⟨List.prefix_refl St, canon, fun τ h => ?_, ?_⟩
          · split_ifs at h with e
            · cases h; exact hσ
          · by_cases e : u = r
            · rw [if_pos e, if_pos (by rw [e])]; rfl
            · rw [if_neg e, if_neg (fun e' => e ((unfold_eq_iff canon hu hr).mp e'))]; rfl
      | none =>
          have tv : unfoldSubst St σ v = none := by simp [unfoldSubst, hv]
          simp only [matchT, tv]
          refine ⟨List.prefix_refl St, canon, fun τ h => ?_, ?_⟩
          · cases h
            intro w x hw
            by_cases e : w = v
            · subst e; simp at hw; subst hw; exact hr
            · rw [Function.update_of_ne e] at hw; exact hσ w x hw
          · simp [unfoldSubst_update]
  | .idx n, St, σ, r, canon, hσ, hr => by
      have spec := view_spec canon r
      simp only [matchR]
      generalize view St r = res at spec ⊢
      obtain ⟨St', w⟩ := res
      obtain ⟨grow, canon', shows⟩ := spec
      dsimp only at grow canon' shows ⊢
      cases w with
      | idx m =>
          change unfold St r = .idx m at shows
          dsimp only
          simp only [matchT, shows, Term.idx.injEq]
          refine ⟨grow, canon', fun τ h => ?_, ?_⟩
          · split_ifs at h; cases h; exact hσ.prefix canon.topo grow
          · split_ifs with e
            · simp [unfoldSubst_prefix canon.topo grow hσ]
            · rfl
      | node head fs =>
          obtain ⟨_, eq⟩ := shows
          dsimp only
          simp only [matchT, eq]
          exact ⟨grow, canon', fun τ h => (by cases h), by simp⟩
  | .node head ps, St, σ, r, canon, hσ, hr => by
      have spec := view_spec canon r
      simp only [matchR]
      generalize view St r = res at spec ⊢
      obtain ⟨St', w⟩ := res
      obtain ⟨grow, canon', shows⟩ := spec
      dsimp only at grow canon' shows ⊢
      cases w with
      | idx m =>
          change unfold St r = .idx m at shows
          dsimp only
          rw [shows]
          exact ⟨grow, canon', fun τ h => (by cases h), rfl⟩
      | node head' fs =>
          obtain ⟨kids, eq⟩ := shows
          dsimp only
          rw [eq]
          have red : matchT (.node head ps) (unfoldSubst St σ) (.node head' (fieldsOf (unfold St') fs)) =
              if head = head' then matchFieldsT ps (unfoldSubst St σ) (fieldsOf (unfold St') fs)
              else none := rfl
          rw [red]
          by_cases e : head = head'
          · rw [if_pos e, if_pos e]
            obtain ⟨grow2, canon2, hres, eqres⟩ := matchFieldsR_spec ps St' σ fs canon'
              (hσ.prefix canon.topo grow) kids
            refine ⟨grow.trans grow2, canon2, hres, ?_⟩
            rw [eqres, unfoldSubst_prefix canon.topo grow hσ]
          · rw [if_neg e, if_neg e]
            exact ⟨grow, canon', fun τ h => (by cases h), rfl⟩

theorem matchFieldsR_spec : ∀ (ps : TreePatFields Head V) (St : Store Head) (σ : Subst V Ref)
    (fs : List (ℕ × Ref)), Canonical St → CanonSubst St σ → (∀ x ∈ fs, CanonRef St x.2) →
    MatchROk St (matchFieldsR ps St σ fs).1 (matchFieldsR ps St σ fs).2
      (matchFieldsT ps (unfoldSubst St σ) (fieldsOf (unfold St) fs))
  | .nil, St, σ, [], canon, hσ, _ => by
      simp only [matchFieldsR, fieldsOf, matchFieldsT]
      exact ⟨List.prefix_refl St, canon, fun τ h => by cases h; exact hσ, rfl⟩
  | .cons d p ps, St, σ, (d', r) :: rest, canon, hσ, kids => by
      simp only [matchFieldsR, fieldsOf, matchFieldsT]
      by_cases e : d = d'
      · rw [if_pos e, if_pos e]
        have hr : CanonRef St r := kids (d', r) (by simp)
        obtain ⟨grow1, canon1, hres1, eq1⟩ := matchR_spec p St σ r canon hσ hr
        revert grow1 canon1 hres1 eq1
        cases matchR p St σ r with
        | mk St1 res =>
            intro grow1 canon1 hres1 eq1
            cases res with
            | none =>
                simp only at eq1 ⊢
                rw [← eq1]
                exact ⟨grow1, canon1, fun τ h => (by cases h), rfl⟩
            | some σ' =>
                simp only [Option.map_some] at eq1
                rw [← eq1, Option.bind_some]
                have kids1 : ∀ x ∈ rest, CanonRef St1 x.2 :=
                  fun x m => (kids x (by simp [m])).prefix canon.topo grow1
                obtain ⟨grow2, canon2, hres2, eq2⟩ := matchFieldsR_spec ps St1 σ' rest canon1
                  (hres1 σ' rfl) kids1
                refine ⟨grow1.trans grow2, canon2, hres2, ?_⟩
                rw [eq2, fieldsOf_congr fun x m => unfold_prefix canon.topo grow1 (kids x (by simp [m])).valid]
      · rw [if_neg e, if_neg e]
        exact ⟨List.prefix_refl St, canon, fun τ h => (by cases h), rfl⟩
  | .nil, St, σ, _ :: _, canon, _, _ => by
      simp only [matchFieldsR, fieldsOf, matchFieldsT]
      exact ⟨List.prefix_refl St, canon, fun τ h => (by cases h), rfl⟩
  | .cons _ _ _, St, σ, [], canon, _, _ => by
      simp only [matchFieldsR, fieldsOf, matchFieldsT]
      exact ⟨List.prefix_refl St, canon, fun τ h => (by cases h), rfl⟩

end

/-! ## Building a template's instance in the store -/

mutual

/-- Build the instance of a pattern in the store. -/
def instR : TreePat Head V → Store Head → Subst V Ref → Store Head × Option Ref
  | .mvar v, St, σ => (St, σ v)
  | .idx n, St, _ =>
      let got := intern St .var
      (got.1, some ⟨n, got.2⟩)
  | .node head ps, St, σ =>
      match instFieldsR ps St σ with
      | (St1, some fs) =>
          let made := mkNode St1 head fs
          (made.1, some made.2)
      | (St1, none) => (St1, none)

def instFieldsR : TreePatFields Head V → Store Head → Subst V Ref →
    Store Head × Option (List (ℕ × Ref))
  | .nil, St, _ => (St, some [])
  | .cons d p ps, St, σ =>
      match instR p St σ with
      | (St1, some r) =>
          match instFieldsR ps St1 σ with
          | (St2, some fs) => (St2, some ((d, r) :: fs))
          | (St2, none) => (St2, none)
      | (St1, none) => (St1, none)

end

omit [DecidableEq V] in
mutual

/-- **Building in the store is instantiating the tree.** -/
theorem instR_spec : ∀ (p : TreePat Head V) (St : Store Head) (σ : Subst V Ref),
    Canonical St → CanonSubst St σ →
    St <+: (instR p St σ).1 ∧ Canonical (instR p St σ).1 ∧
      (∀ r, (instR p St σ).2 = some r → CanonRef (instR p St σ).1 r) ∧
      (instR p St σ).2.map (unfold (instR p St σ).1) = p.inst (unfoldSubst St σ)
  | .mvar v, St, σ, canon, hσ => by
      refine ⟨List.prefix_refl St, canon, fun r h => hσ v r h, ?_⟩
      simp [instR, TreePat.inst, unfoldSubst]
  | .idx n, St, σ, canon, hσ => by
      obtain ⟨grow, canon2, cr, eq⟩ := encode_spec St canon (.idx n : Term Head)
      simp only [encode] at grow canon2 cr eq
      refine ⟨grow, canon2, fun r h => ?_, ?_⟩
      · simp only [instR, Option.some.injEq] at h
        subst h; exact cr
      · simp [instR, TreePat.inst, eq]
  | .node head ps, St, σ, canon, hσ => by
      obtain ⟨grow1, canon1, kids1, eq1⟩ := instFieldsR_spec ps St σ canon hσ
      have unfoldR : instR (.node head ps) St σ =
          (match instFieldsR ps St σ with
            | (St1, some fs) => ((mkNode St1 head fs).1, some (mkNode St1 head fs).2)
            | (St1, none) => (St1, none)) := by
        simp only [instR]
      rw [unfoldR]
      generalize instFieldsR ps St σ = res at grow1 canon1 kids1 eq1 ⊢
      obtain ⟨St1, res⟩ := res
      dsimp only at grow1 canon1 kids1 eq1 ⊢
      cases res with
      | none =>
          dsimp only
          simp only [Option.map_none] at eq1
          refine ⟨grow1, canon1, fun r h => (by cases h), ?_⟩
          simp [TreePat.inst, ← eq1]
      | some fs =>
          dsimp only
          simp only [Option.map_some] at eq1
          obtain ⟨grow2, canon2, cr2, eq2⟩ := mkNode_spec canon1 head (kids1 fs rfl)
          refine ⟨grow1.trans grow2, canon2, fun r h => ?_, ?_⟩
          · simp only [Option.some.injEq] at h; subst h; exact cr2
          · simp [TreePat.inst, ← eq1, eq2]

theorem instFieldsR_spec : ∀ (ps : TreePatFields Head V) (St : Store Head) (σ : Subst V Ref),
    Canonical St → CanonSubst St σ →
    St <+: (instFieldsR ps St σ).1 ∧ Canonical (instFieldsR ps St σ).1 ∧
      (∀ fs, (instFieldsR ps St σ).2 = some fs → ∀ x ∈ fs, CanonRef (instFieldsR ps St σ).1 x.2) ∧
      (instFieldsR ps St σ).2.map (fieldsOf (unfold (instFieldsR ps St σ).1)) =
        ps.inst (unfoldSubst St σ)
  | .nil, St, σ, canon, _ => by
      refine ⟨List.prefix_refl St, canon, fun fs h => ?_, ?_⟩
      · simp only [instFieldsR, Option.some.injEq] at h; subst h; simp
      · simp [instFieldsR, TreePatFields.inst, fieldsOf]
  | .cons d p ps, St, σ, canon, hσ => by
      obtain ⟨grow1, canon1, cr1, eq1⟩ := instR_spec p St σ canon hσ
      have unfoldF : instFieldsR (.cons d p ps) St σ =
          (match instR p St σ with
            | (St1, some r) =>
                match instFieldsR ps St1 σ with
                | (St2, some fs) => (St2, some ((d, r) :: fs))
                | (St2, none) => (St2, none)
            | (St1, none) => (St1, none)) := by
        simp only [instFieldsR]
      rw [unfoldF]
      generalize instR p St σ = res1 at grow1 canon1 cr1 eq1 ⊢
      obtain ⟨St1, res1⟩ := res1
      dsimp only at grow1 canon1 cr1 eq1 ⊢
      cases res1 with
      | none =>
          dsimp only
          simp only [Option.map_none] at eq1
          refine ⟨grow1, canon1, fun fs h => (by cases h), ?_⟩
          simp [TreePatFields.inst, ← eq1]
      | some r =>
          dsimp only
          simp only [Option.map_some] at eq1
          have hσ1 := hσ.prefix canon.topo grow1
          obtain ⟨grow2, canon2, kids2, eq2⟩ := instFieldsR_spec ps St1 σ canon1 hσ1
          rw [unfoldSubst_prefix canon.topo grow1 hσ] at eq2
          generalize instFieldsR ps St1 σ = res2 at grow2 canon2 kids2 eq2 ⊢
          obtain ⟨St2, res2⟩ := res2
          dsimp only at grow2 canon2 kids2 eq2 ⊢
          cases res2 with
          | none =>
              dsimp only
              simp only [Option.map_none] at eq2
              refine ⟨grow1.trans grow2, canon2, fun fs h => (by cases h), ?_⟩
              simp [TreePatFields.inst, ← eq1, ← eq2]
          | some fs =>
              dsimp only
              simp only [Option.map_some] at eq2
              refine ⟨grow1.trans grow2, canon2, fun fs' h => ?_, ?_⟩
              · simp only [Option.some.injEq] at h
                subst h
                intro x m
                rcases List.mem_cons.mp m with rfl | m
                · exact (cr1 r rfl).prefix canon1.topo grow2
                · exact kids2 fs rfl x m
              · simp only [Option.map_some, TreePatFields.inst, ← eq1, ← eq2, fieldsOf,
                  unfold_prefix canon1.topo grow2 (cr1 r rfl).valid]

end


end SharedMatcher

/-! ## Controls -/

namespace MatchControls

open SharingControls

/-- `(app $0 $0)`. -/
def pDiag : TreePat H ℕ := .node .app (.cons 0 (.mvar 0) (.cons 0 (.mvar 0) .nil))

/-- The empty substitution of references. -/
def none₀ : Subst ℕ Ref := fun _ => none

/-- `(app t1 t1)`, stored. -/
def St₁ : Store H := (encode [] (app t1 t1)).1

def r₁ : Ref := (encode [] (app t1 t1)).2

/-- `(app t1 t2)`, stored. -/
def St₂ : Store H := (encode [] (app t1 t2)).1

def r₂ : Ref := (encode [] (app t1 t2)).2

/-- Positive: `(app $0 $0)` matches `(app t1 t1)`; the second `$0` is a pointer comparison. -/
theorem diag_matches : ((matchR pDiag St₁ none₀ r₁).2.map fun σ => σ 0).isSome = true := by
  decide +kernel

/-- Negative: `(app $0 $0)` does not match `(app t1 t2)`: `t1` and `t2` are different
references. -/
theorem diag_refuses : (matchR pDiag St₂ none₀ r₂).2 = none := by
  decide +kernel

end MatchControls

end Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.SharedTerms
