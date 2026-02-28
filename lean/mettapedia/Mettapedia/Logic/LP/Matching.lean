import Mettapedia.Logic.LP.Substitution
import Mathlib.Algebra.BigOperators.Fin

/-!
# Logic Programming Kernel: Matching (One-Sided Unification)

Matching is the restriction of unification where only one side may contain
variables.  Given a pattern `p` and a ground target `t`, matching finds
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
    | some bs => .success (bindingsToSubst bs)

/-- Match a pattern atom against a ground atom. -/
def matchAtom {σ : LPSignature} [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols] :
    Atom σ → GroundAtom σ → MatchResult σ
  | a, ga =>
    match collectAtomBindings a ga with
    | none => .failure
    | some bs => .success (bindingsToSubst bs)

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

universe u_t u_r

/-- Core soundness: any substitution agreeing with bindings sends patterns
    to their ground counterparts. -/
theorem collectBindingsList_sound {σ : LPSignature.{u_t, u_t, u_r, u_t}}
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
theorem collectBindings_sound {σ : LPSignature.{u_t, u_t, u_r, u_t}} [DecidableEq σ.vars]
    [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    (p : Term σ) (gt : GroundTerm σ) (bs : List (σ.vars × GroundTerm σ))
    (h : collectBindings p gt = some bs) (hcons : BindingsConsistent bs) :
    (bindingsToSubst bs).applyTerm p = gt.toTerm := by
  have hsound := collectBindingsList_sound [p] [gt] bs h
    (bindingsToSubst bs) (fun v g hm => bindingsToSubst_mem bs v g hm hcons)
  simpa using hsound

/-- Soundness for atom matching. -/
theorem collectAtomBindings_sound {σ : LPSignature.{u_t, u_t, u_r, u_t}} [DecidableEq σ.vars]
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

end Mettapedia.Logic.LP
