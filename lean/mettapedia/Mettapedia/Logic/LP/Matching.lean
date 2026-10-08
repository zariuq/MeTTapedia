import Mettapedia.Logic.LP.Substitution
import Mathlib.Algebra.BigOperators.Fin

/-!
# Logic Programming Kernel: Matching (One-Sided Unification)

This module handles the ground-target fragment of one-sided matching.
Given a pattern `p` and a ground target `t`, matching finds
`θ` such that `θ(p) = t`.  This is used in:

- Bottom-up evaluation (T_P): matching rule heads against ground atoms.
- Clause selection in SLD resolution (before full unification is needed).

## Design

We collect variable bindings as a `List (σ.vars × GroundTerm σ)`, then build
a `Subst σ`.  Iteration over Fin-indexed subterms converts to `List` for clean
structural recursion on pairs of lists.  Termination uses the sum of `Term.size`
across the pattern list.

## References

- Lloyd, *Foundations of Logic Programming*, Ch. 1 (matching in T_P)
-/

namespace Mettapedia.Logic.LP

/-! ## Section 1: Fin-to-List utilities -/

/-- Convert a Fin-indexed family to a list. -/
def finToList {α : Type*} {n : ℕ} (f : Fin n → α) : List α :=
  (List.finRange n).map f

@[simp]
theorem finToList_length {α : Type*} {n : ℕ} (f : Fin n → α) :
    (finToList f).length = n := by
  simp [finToList]

/-! ## Section 2: Total pattern size (termination measure) -/

/-- Total term size of a list of patterns. -/
def patternListSize {σ : LPSignature} (ps : List (Term σ)) : ℕ :=
  (ps.map Term.size).sum

private theorem patternListSize_cons {σ : LPSignature} (p : Term σ) (ps : List (Term σ)) :
    patternListSize (p :: ps) = p.size + patternListSize ps := by
  simp [patternListSize]

private theorem patternListSize_append {σ : LPSignature}
    (ps qs : List (Term σ)) :
    patternListSize (ps ++ qs) = patternListSize ps + patternListSize qs := by
  simp [patternListSize, List.map_append, List.sum_append]

private theorem patternListSize_finToList {σ : LPSignature} {n : ℕ}
    (ts : Fin n → Term σ) :
    patternListSize (finToList ts) = ∑ i : Fin n, (ts i).size := by
  simp only [patternListSize, finToList, List.map_map, Fin.sum_univ_def]
  rfl

private theorem patternListSize_finToList_app {σ : LPSignature}
    (f : σ.functionSymbols) (ts : Fin (σ.functionArity f) → Term σ)
    (ps : List (Term σ)) :
    patternListSize (finToList ts ++ ps) < patternListSize (Term.app f ts :: ps) := by
  rw [patternListSize_append, patternListSize_cons, Term.size, patternListSize_finToList]
  omega

/-! ## Section 3: Binding collection -/

/-- Collect bindings from paired lists of pattern and ground terms. -/
def collectBindingsList {σ : LPSignature} [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols]
    (ps : List (Term σ)) (gs : List (GroundTerm σ)) :
    Option (List (σ.vars × GroundTerm σ)) :=
  match ps, gs with
  | [], [] => some []
  | .var v :: ps', g :: gs' => do
    let rest ← collectBindingsList ps' gs'
    return (v, g) :: rest
  | .const c :: ps', .const c' :: gs' =>
    if c = c' then collectBindingsList ps' gs' else none
  | .const _ :: _, .app _ _ :: _ => none
  | .app _ _ :: _, .const _ :: _ => none
  | .app f ts :: ps', .app g us :: gs' =>
    if h : f = g then
      collectBindingsList (finToList ts ++ ps') (finToList (h ▸ us) ++ gs')
    else none
  | [], _ :: _ => none
  | _ :: _, [] => none
termination_by patternListSize ps
decreasing_by
  all_goals simp only [patternListSize_cons]
  · have := Term.size_pos (.var v); omega
  · have := Term.size_pos (.const c); omega
  · rw [← patternListSize_cons]; exact patternListSize_finToList_app _ _ _

/-- Collect bindings by matching a pattern term against a ground term. -/
def collectBindings {σ : LPSignature} [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] (p : Term σ) (gt : GroundTerm σ) :
    Option (List (σ.vars × GroundTerm σ)) :=
  collectBindingsList [p] [gt]

/-- Collect bindings for an atom against a ground atom. -/
def collectAtomBindings {σ : LPSignature} [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]
    (a : Atom σ) (ga : GroundAtom σ) :
    Option (List (σ.vars × GroundTerm σ)) :=
  if h : a.symbol = ga.symbol then
    collectBindingsList (finToList a.args) (finToList (h ▸ ga.args))
  else none

/-! ## Section 4: Substitution construction -/

/-- Build a substitution from a binding list. First binding for each variable wins. -/
def bindingsToSubst {σ : LPSignature} [DecidableEq σ.vars]
    (bs : List (σ.vars × GroundTerm σ)) : Subst σ :=
  fun v => match bs.find? (fun p => p.1 == v) with
    | some (_, gt) => gt.toTerm
    | none => .var v

/-- A binding list is consistent if each variable maps to a unique ground term. -/
def BindingsConsistent {σ : LPSignature} (bs : List (σ.vars × GroundTerm σ)) : Prop :=
  ∀ v g₁ g₂, (v, g₁) ∈ bs → (v, g₂) ∈ bs → g₁ = g₂

/-- Structural equality of finite ground terms, including their ordered arguments. -/
def GroundTerm.decEq {σ : LPSignature} [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] : DecidableEq (GroundTerm σ)
  | .const c, .const d => decidable_of_iff (c = d)
      ⟨congrArg GroundTerm.const, fun h => by cases h; rfl⟩
  | .const _, .app _ _ => isFalse (by intro h; cases h)
  | .app _ _, .const _ => isFalse (by intro h; cases h)
  | .app f ts, .app g us =>
    if h : f = g then by
      subst g
      letI : (i : Fin (σ.functionArity f)) → Decidable (ts i = us i) :=
        fun i => GroundTerm.decEq (ts i) (us i)
      exact decidable_of_iff (∀ i, ts i = us i) (by
        constructor
        · intro h; exact congrArg (GroundTerm.app f) (funext h)
        · intro h; cases h; intro i; rfl)
    else isFalse (by intro heq; cases heq; exact h rfl)

/-- Check that all occurrences of each pattern variable captured the same term. -/
def bindingsConsistent? {σ : LPSignature} [DecidableEq σ.vars]
    [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    (bs : List (σ.vars × GroundTerm σ)) : Bool :=
  letI := GroundTerm.decEq (σ := σ)
  bs.all fun left => bs.all fun right =>
    decide (left.1 = right.1 → left.2 = right.2)

theorem bindingsConsistent?_eq_true {σ : LPSignature} [DecidableEq σ.vars]
    [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    (bs : List (σ.vars × GroundTerm σ)) :
    bindingsConsistent? bs = true ↔ BindingsConsistent bs := by
  simp only [bindingsConsistent?, List.all_eq_true, decide_eq_true_eq]
  constructor
  · intro h v g₁ g₂ h₁ h₂
    exact h (v, g₁) h₁ (v, g₂) h₂ rfl
  · intro h left hleft right hright heq
    rcases left with ⟨v, g₁⟩
    rcases right with ⟨w, g₂⟩
    dsimp at heq ⊢
    subst w
    exact h v g₁ g₂ hleft hright

/-! ## Section 5: Full matching interface -/

/-- Result of a matching attempt. -/
inductive MatchResult (σ : LPSignature) where
  | success : Subst σ → MatchResult σ
  | failure : MatchResult σ

/-- Match a pattern term against a ground term. -/
def matchTerm {σ : LPSignature} [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] :
    Term σ → GroundTerm σ → MatchResult σ
  | p, gt =>
    match collectBindings p gt with
    | none => .failure
    | some bs =>
      if bindingsConsistent? bs then .success (bindingsToSubst bs) else .failure

/-- Match a pattern atom against a ground atom. -/
def matchAtom {σ : LPSignature} [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols] :
    Atom σ → GroundAtom σ → MatchResult σ
  | a, ga =>
    match collectAtomBindings a ga with
    | none => .failure
    | some bs =>
      if bindingsConsistent? bs then .success (bindingsToSubst bs) else .failure

/-! ## Section 6: Binding lookup -/

/-- `bindingsToSubst` maps a bound variable to its ground term (head entry). -/
private theorem bindingsToSubst_head {σ : LPSignature} [DecidableEq σ.vars]
    (v : σ.vars) (g : GroundTerm σ) (rest : List (σ.vars × GroundTerm σ)) :
    (bindingsToSubst ((v, g) :: rest)) v = g.toTerm := by
  simp [bindingsToSubst]

/-- `bindingsToSubst` skips non-matching head entries. -/
private theorem bindingsToSubst_skip {σ : LPSignature} [DecidableEq σ.vars]
    (w : σ.vars) (g' : GroundTerm σ) (rest : List (σ.vars × GroundTerm σ))
    (v : σ.vars) (h : w ≠ v) :
    (bindingsToSubst ((w, g') :: rest)) v = (bindingsToSubst rest) v := by
  simp [bindingsToSubst, show (w == v) = false from by simp [h]]

/-- If `(v, g) ∈ bs` and `bs` is consistent, `bindingsToSubst bs` maps `v` to `g.toTerm`. -/
theorem bindingsToSubst_mem {σ : LPSignature} [DecidableEq σ.vars]
    (bs : List (σ.vars × GroundTerm σ)) (v : σ.vars) (g : GroundTerm σ)
    (hmem : (v, g) ∈ bs) (hcons : BindingsConsistent bs) :
    (bindingsToSubst bs) v = g.toTerm := by
  induction bs with
  | nil => simp at hmem
  | cons b rest ih =>
    obtain ⟨w, g'⟩ := b
    by_cases hwv : w = v
    · subst hwv
      rw [bindingsToSubst_head]
      exact congrArg GroundTerm.toTerm (hcons _ g' g (List.mem_cons_self ..) hmem)
    · rw [bindingsToSubst_skip w g' rest v hwv]
      have hmem' : (v, g) ∈ rest := by
        rcases List.mem_cons.mp hmem with h | h
        · exact absurd (congrArg Prod.fst h).symm hwv
        · exact h
      exact ih hmem' (fun v₁ g₁ g₂ h1 h2 => hcons v₁ g₁ g₂
          (List.mem_cons_of_mem _ h1) (List.mem_cons_of_mem _ h2))

/-! ## Section 7: Soundness -/

/-- Split equal appended lists of known lengths. -/
private theorem append_eq_append {α : Type*} {l₁ l₂ : List α} {r₁ r₂ : List α}
    (h : l₁ ++ r₁ = l₂ ++ r₂) (hl : l₁.length = l₂.length) :
    l₁ = l₂ ∧ r₁ = r₂ := by
  induction l₁ generalizing l₂ with
  | nil =>
    cases l₂ with
    | nil => exact ⟨rfl, h⟩
    | cons _ _ => simp at hl
  | cons a l₁ ih =>
    cases l₂ with
    | nil => simp at hl
    | cons b l₂ =>
      simp only [List.cons_append, List.cons.injEq, List.length_cons] at h hl
      obtain ⟨rfl, h⟩ := h
      obtain ⟨hl₁, hr⟩ := ih h (by omega)
      exact ⟨congrArg _ hl₁, hr⟩

/-- Extract pointwise equality from `finToList` map equality. -/
private theorem finToList_map_pointwise {α₁ α₂ β : Type*} {n : ℕ}
    (f : Fin n → α₁) (g : Fin n → α₂) (F : α₁ → β) (G : α₂ → β)
    (h : (finToList f).map F = (finToList g).map G) :
    ∀ i : Fin n, F (f i) = G (g i) := by
  intro i
  simp only [finToList, List.map_map] at h
  -- h : (List.finRange n).map (F ∘ f) = (List.finRange n).map (G ∘ g)
  have hi₁ : i.val < ((List.finRange n).map (F ∘ f)).length := by simp
  have hi₂ : i.val < ((List.finRange n).map (G ∘ g)).length := by simp
  have hlhs : ((List.finRange n).map (F ∘ f))[i.val]'hi₁ = F (f i) := by
    simp [List.getElem_map, List.getElem_finRange]
  have hrhs : ((List.finRange n).map (G ∘ g))[i.val]'hi₂ = G (g i) := by
    simp [List.getElem_map, List.getElem_finRange]
  rw [← hlhs, ← hrhs]; exact getElem_congr_coll h

/-- Core soundness: any substitution agreeing with bindings sends patterns
    to their ground counterparts. -/
theorem collectBindingsList_sound {σ : LPSignature}
    [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    (ps : List (Term σ)) (gs : List (GroundTerm σ)) (bs : List (σ.vars × GroundTerm σ))
    (h : collectBindingsList ps gs = some bs)
    (θ : Subst σ) (hθ : ∀ v g, (v, g) ∈ bs → θ v = g.toTerm) :
    ps.map θ.applyTerm = gs.map GroundTerm.toTerm := by
  -- Strong induction on patternListSize ps
  suffices key : ∀ n, ∀ (ps : List (Term σ)) (gs : List (GroundTerm σ))
      (bs : List (σ.vars × GroundTerm σ)),
      patternListSize ps ≤ n →
      collectBindingsList ps gs = some bs →
      ∀ (θ : Subst σ), (∀ v g, (v, g) ∈ bs → θ v = g.toTerm) →
      ps.map θ.applyTerm = gs.map GroundTerm.toTerm from
    key (patternListSize ps) ps gs bs le_rfl h θ hθ
  intro n
  induction n with
  | zero =>
    intro ps gs bs hle h θ hθ
    match ps with
    | [] =>
      match gs with
      | [] => simp
      | _ :: _ => simp [collectBindingsList] at h
    | p :: _ =>
      exfalso; simp [patternListSize] at hle; have := Term.size_pos p; omega
  | succ n ih =>
    intro ps gs bs hle h θ hθ
    match ps, gs with
    | [], [] => simp
    | [], _ :: _ => simp [collectBindingsList] at h
    | _ :: _, [] =>
      -- All patterns against empty ground list return none
      rcases ps with ⟨⟩ | ⟨_, _⟩ <;> simp [collectBindingsList] at h
    | .var v :: ps', g :: gs' =>
      simp only [collectBindingsList] at h
      -- h : (collectBindingsList ps' gs').bind (fun rest => some ((v, g) :: rest)) = some bs
      -- which means collectBindingsList ps' gs' = some rest and bs = (v, g) :: rest
      match h_rest : collectBindingsList ps' gs' with
      | none => simp [h_rest] at h
      | some rest =>
        simp [h_rest] at h; subst h
        simp only [List.map]
        have hvar : θ.applyTerm (.var v) = g.toTerm := by
          simp [Subst.applyTerm]; exact hθ v g (List.mem_cons_self ..)
        have htail := ih ps' gs' rest
          (by simp [patternListSize] at hle ⊢; have := Term.size_pos (.var v : Term σ); omega)
          h_rest θ (fun v' g' hm => hθ v' g' (List.mem_cons_of_mem _ hm))
        rw [hvar, htail]
    | .const c :: ps', .const c' :: gs' =>
      simp only [collectBindingsList] at h
      split at h
      · rename_i hcc; subst hcc
        simp only [List.map, Subst.applyTerm, GroundTerm.toTerm]
        exact congrArg _ (ih ps' gs' bs
          (by simp [patternListSize] at hle ⊢; have := Term.size_pos (.const c : Term σ); omega)
          h θ hθ)
      · simp at h
    | .const _ :: _, .app _ _ :: _ => simp [collectBindingsList] at h
    | .app _ _ :: _, .const _ :: _ => simp [collectBindingsList] at h
    | .app f ts :: ps', .app g us :: gs' =>
      simp only [collectBindingsList] at h
      split at h
      · rename_i hfg; subst hfg
        -- h : collectBindingsList (finToList ts ++ ps') (finToList us ++ gs') = some bs
        have ih_result := ih (finToList ts ++ ps') (finToList us ++ gs') bs
          (by have := patternListSize_finToList_app f ts ps'; omega)
          h θ hθ
        -- ih_result : (finToList ts ++ ps').map θ.applyTerm =
        --             (finToList us ++ gs').map GroundTerm.toTerm
        simp only [List.map_append] at ih_result
        have hlen : (finToList ts).length = (finToList us).length := by simp
        obtain ⟨hleft, hright⟩ := append_eq_append ih_result (by simp [List.length_map, hlen])
        simp only [List.map]
        have happ : θ.applyTerm (.app f ts) = (GroundTerm.app f us).toTerm := by
          simp only [Subst.applyTerm, GroundTerm.toTerm]
          congr 1; funext i
          exact finToList_map_pointwise ts us θ.applyTerm GroundTerm.toTerm hleft i
        rw [happ, hright]
      · simp at h

/-- Soundness for single-term matching. -/
theorem collectBindings_sound {σ : LPSignature} [DecidableEq σ.vars]
    [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    (p : Term σ) (gt : GroundTerm σ) (bs : List (σ.vars × GroundTerm σ))
    (h : collectBindings p gt = some bs) (hcons : BindingsConsistent bs) :
    (bindingsToSubst bs).applyTerm p = gt.toTerm := by
  have hsound := collectBindingsList_sound [p] [gt] bs h
    (bindingsToSubst bs) (fun v g hm => bindingsToSubst_mem bs v g hm hcons)
  simpa using hsound

/-- Soundness for atom matching. -/
theorem collectAtomBindings_sound {σ : LPSignature} [DecidableEq σ.vars]
    [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]
    (a : Atom σ) (ga : GroundAtom σ) (bs : List (σ.vars × GroundTerm σ))
    (h : collectAtomBindings a ga = some bs) (hcons : BindingsConsistent bs) :
    (bindingsToSubst bs).applyAtom a = ga.toAtom := by
  obtain ⟨sa, argsa⟩ := a; obtain ⟨sga, argsga⟩ := ga
  unfold collectAtomBindings at h
  split at h
  · rename_i hsym; dsimp only at hsym h; subst hsym
    simp only [Subst.applyAtom, GroundAtom.toAtom, Atom.mk.injEq, heq_eq_eq, true_and]
    funext i
    have hsound := collectBindingsList_sound (finToList argsa) (finToList argsga) bs h
      (bindingsToSubst bs) (fun v g hm => bindingsToSubst_mem bs v g hm hcons)
    exact finToList_map_pointwise argsa argsga
      (bindingsToSubst bs).applyTerm GroundTerm.toTerm hsound i
  · simp at h

/-- Every successful public term match instantiates the pattern to its target.
    Repeated-hole consistency is checked by the operation, not assumed here. -/
theorem matchTerm_sound {σ : LPSignature} [DecidableEq σ.vars]
    [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    (p : Term σ) (gt : GroundTerm σ) (θ : Subst σ)
    (h : matchTerm p gt = .success θ) : θ.applyTerm p = gt.toTerm := by
  cases hb : collectBindings p gt with
  | none => simp [matchTerm, hb] at h
  | some bs =>
    by_cases hc : bindingsConsistent? bs = true
    · simp [matchTerm, hb, hc] at h
      subst θ
      exact collectBindings_sound p gt bs hb ((bindingsConsistent?_eq_true bs).mp hc)
    · simp [matchTerm, hb, hc] at h

/-- Every successful public atom match instantiates the whole atom, including
    repeated variables occurring in different arguments. -/
theorem matchAtom_sound {σ : LPSignature} [DecidableEq σ.vars]
    [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    [DecidableEq σ.relationSymbols]
    (a : Atom σ) (ga : GroundAtom σ) (θ : Subst σ)
    (h : matchAtom a ga = .success θ) : θ.applyAtom a = ga.toAtom := by
  cases hb : collectAtomBindings a ga with
  | none => simp [matchAtom, hb] at h
  | some bs =>
    by_cases hc : bindingsConsistent? bs = true
    · simp [matchAtom, hb, hc] at h
      subst θ
      exact collectAtomBindings_sound a ga bs hb ((bindingsConsistent?_eq_true bs).mp hc)
    · simp [matchAtom, hb, hc] at h

theorem GroundTerm.toTerm_injective {σ : LPSignature} :
    Function.Injective (GroundTerm.toTerm (σ := σ)) := by
  intro left right same
  induction left generalizing right with
  | const c => cases right <;> simp_all [GroundTerm.toTerm]
  | app f args ih =>
    cases right with
    | const c => simp [GroundTerm.toTerm] at same
    | app g rest =>
      simp only [GroundTerm.toTerm, Term.app.injEq] at same
      obtain ⟨equal, same⟩ := same
      subst g
      simp only [heq_eq_eq] at same
      congr 1
      funext i
      exact ih i (congrFun same i)

/-- Every ground instance can be collected, and every collected binding agrees
    with its witnessing substitution. Repeated names are retained here. -/
theorem collectBindingsList_complete {σ : LPSignature}
    [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    (ps : List (Term σ)) (gs : List (GroundTerm σ)) (θ : Subst σ)
    (same : ps.map θ.applyTerm = gs.map GroundTerm.toTerm) :
    ∃ bs, collectBindingsList ps gs = some bs ∧
      ∀ v g, (v, g) ∈ bs → θ v = g.toTerm := by
  match ps, gs with
  | [], [] => exact ⟨[], by simp [collectBindingsList], by simp⟩
  | [], _ :: _ => simp at same
  | _ :: _, [] => simp at same
  | .var v :: rest, g :: tail =>
    simp only [List.map_cons, List.cons.injEq, Subst.applyTerm_var] at same
    obtain ⟨bs, collected, agree⟩ := collectBindingsList_complete rest tail θ same.2
    refine ⟨(v, g) :: bs, by simp [collectBindingsList, collected], ?_⟩
    intro w h member
    rcases List.mem_cons.mp member with equal | member
    · cases equal; exact same.1
    · exact agree w h member
  | .const c :: rest, .const d :: tail =>
    simp only [List.map_cons, List.cons.injEq, Subst.applyTerm_const,
      GroundTerm.toTerm, Term.const.injEq] at same
    obtain ⟨rfl, same⟩ := same
    obtain ⟨bs, collected, agree⟩ := collectBindingsList_complete rest tail θ same
    exact ⟨bs, by simpa [collectBindingsList] using collected, agree⟩
  | .const _ :: _, .app _ _ :: _ =>
    simp [Subst.applyTerm, GroundTerm.toTerm] at same
  | .app _ _ :: _, .const _ :: _ =>
    simp [Subst.applyTerm, GroundTerm.toTerm] at same
  | .app f args :: rest, .app g targets :: tail =>
    simp only [List.map_cons, List.cons.injEq, Subst.applyTerm_app,
      GroundTerm.toTerm, Term.app.injEq] at same
    obtain ⟨⟨equal, children⟩, tailEq⟩ := same
    subst g
    simp only [heq_eq_eq] at children
    have childEq : (finToList args).map θ.applyTerm =
        (finToList targets).map GroundTerm.toTerm := by
      simp only [finToList, List.map_map]
      apply List.map_congr_left
      intro i _
      exact congrFun children i
    have next : (finToList args ++ rest).map θ.applyTerm =
        (finToList targets ++ tail).map GroundTerm.toTerm := by
      simp only [List.map_append, childEq, tailEq]
    obtain ⟨bs, collected, agree⟩ := collectBindingsList_complete
      (finToList args ++ rest) (finToList targets ++ tail) θ next
    exact ⟨bs, by simpa [collectBindingsList] using collected, agree⟩
termination_by patternListSize ps
decreasing_by
  · simp [patternListSize_cons, Term.size]
  · simp [patternListSize_cons, Term.size]
  · exact patternListSize_finToList_app _ _ _

private theorem bindings_consistent_of_agree {σ : LPSignature}
    (bs : List (σ.vars × GroundTerm σ)) (θ : Subst σ)
    (agree : ∀ v g, (v, g) ∈ bs → θ v = g.toTerm) : BindingsConsistent bs := by
  intro v left right hl hr
  exact GroundTerm.toTerm_injective ((agree v left hl).symm.trans (agree v right hr))

/-- Checking repeated holes rejects exactly non-instances, without losing any
    ground instance that the former unchecked collector accepted soundly. -/
theorem matchTerm_complete {σ : LPSignature} [DecidableEq σ.vars]
    [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    (pattern : Term σ) (target : GroundTerm σ) (θ : Subst σ)
    (same : θ.applyTerm pattern = target.toTerm) :
    ∃ answer, matchTerm pattern target = .success answer := by
  obtain ⟨bs, collected, agree⟩ := collectBindingsList_complete [pattern] [target] θ
    (by simpa using same)
  have checked := (bindingsConsistent?_eq_true bs).mpr (bindings_consistent_of_agree bs θ agree)
  exact ⟨bindingsToSubst bs, by simp [matchTerm, collectBindings, collected, checked]⟩

theorem matchAtom_complete {σ : LPSignature} [DecidableEq σ.vars]
    [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    [DecidableEq σ.relationSymbols]
    (pattern : Atom σ) (target : GroundAtom σ) (θ : Subst σ)
    (same : θ.applyAtom pattern = target.toAtom) :
    ∃ answer, matchAtom pattern target = .success answer := by
  rcases pattern with ⟨f, args⟩
  rcases target with ⟨g, targets⟩
  simp only [Subst.applyAtom, GroundAtom.toAtom, Atom.mk.injEq] at same
  obtain ⟨equal, children⟩ := same
  subst g
  simp only [heq_eq_eq] at children
  have childEq : (finToList args).map θ.applyTerm =
      (finToList targets).map GroundTerm.toTerm := by
    simp only [finToList, List.map_map]
    apply List.map_congr_left
    intro i _
    exact congrFun children i
  obtain ⟨bs, collected, agree⟩ := collectBindingsList_complete _ _ θ childEq
  have checked := (bindingsConsistent?_eq_true bs).mpr (bindings_consistent_of_agree bs θ agree)
  exact ⟨bindingsToSubst bs, by simp [matchAtom, collectAtomBindings, collected, checked]⟩

end Mettapedia.Logic.LP
