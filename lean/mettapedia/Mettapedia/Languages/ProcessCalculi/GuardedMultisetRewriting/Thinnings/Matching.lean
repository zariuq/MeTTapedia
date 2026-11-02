import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.Operations
import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.Patterns
import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.TemplateInstantiation

/-!
# Matching and instantiating on shared terms

* `matchR`: the tree matcher (`matchT`) run on references into a canonical store. It takes nodes
  apart with `view` and compares the values of a repeated pattern variable by **pointer
  equality**. Viewing allocates nothing, so **matching only reads the store**: `matchR` returns a
  substitution of references and no new store. **It computes exactly what `matchT` computes on the
  trees** (`matchR_spec`).
* `instR`: building a template's instance in the store computes exactly `TreePat.inst`
  (`instR_spec`). Each node of the template is one `mkNode`.

Example (`MatchControls`): `(app $f $f)` matches `(app t t)` for a stored `t` by comparing two
references, and fails on `(app t u)` for `t ≠ u`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings

open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources
open Thin

variable {Head : Type} {V : Type}

section SharedMatcher

variable [DecidableEq V] [DecidableEq Head]

/-- Read a substitution of references as one of trees. -/
def unfoldSubst (St : Store Head) (σ : Subst V Ref) : Subst V (Term Head) :=
  fun v => (σ v).map (unfold St)

/-- A substitution of references is canonical in a store. -/
def CanonSubst (St : Store Head) (σ : Subst V Ref) : Prop := ∀ v r, σ v = some r → CanonRef St r

omit [DecidableEq V] [DecidableEq Head] in
theorem CanonSubst.prefix {St St' : Store Head} (grow : St <+: St') {σ : Subst V Ref}
    (canon : CanonSubst St σ) : CanonSubst St' σ :=
  fun v r h => (canon v r h).prefix grow

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

/-! ## Matching -/

mutual

/-- **Match a pattern against a reference**: take nodes apart with `view`, compare the values of
a repeated variable by pointer equality. The store is only read. -/
def matchR : TreePat Head V → Store Head → Subst V Ref → Ref → Option (Subst V Ref)
  | .mvar v, _, σ, r =>
      match σ v with
      | some u => if u = r then some σ else none
      | none => some (Function.update σ v (some r))
  | .idx n, St, σ, r =>
      match view St r with
      | .idx m => if m = n then some σ else none
      | .node _ _ => none
  | .node head ps, St, σ, r =>
      match view St r with
      | .node head' fs => if head = head' then matchFieldsR ps St σ fs else none
      | .idx _ => none

def matchFieldsR : TreePatFields Head V → Store Head → Subst V Ref → List (ℕ × Ref) →
    Option (Subst V Ref)
  | .nil, _, σ, [] => some σ
  | .cons d p ps, St, σ, (d', r) :: rest =>
      if d = d' then (matchR p St σ r).bind fun σ' => matchFieldsR ps St σ' rest else none
  | .nil, _, _, _ :: _ => none
  | .cons _ _ _, _, _, [] => none

end

/-- What `matchR` promises: the answer's references are canonical, and the answer, unfolded, is the
tree matcher's answer. -/
def MatchROk (St : Store Head) (res : Option (Subst V Ref)) (expected : Option (Subst V (Term Head))) :
    Prop :=
  (∀ τ, res = some τ → CanonSubst St τ) ∧ res.map (unfoldSubst St) = expected

mutual

/-- **Matching on shared terms is matching on the trees they stand for.** -/
theorem matchR_spec : ∀ (p : TreePat Head V) (St : Store Head) (σ : Subst V Ref) (r : Ref),
    Canonical St → CanonSubst St σ → CanonRef St r →
    MatchROk St (matchR p St σ r) (matchT p (unfoldSubst St σ) (unfold St r))
  | .mvar v, St, σ, r, canon, hσ, hr => by
      simp only [matchR]
      cases hv : σ v with
      | some u =>
          have hu := hσ v u hv
          have tv : unfoldSubst St σ v = some (unfold St u) := by simp [unfoldSubst, hv]
          simp only [matchT, tv]
          refine ⟨fun τ h => ?_, ?_⟩
          · split_ifs at h with e
            · cases h; exact hσ
          · by_cases e : u = r
            · rw [if_pos e, if_pos (by rw [e])]; rfl
            · rw [if_neg e, if_neg (fun e' => e ((unfold_eq_iff canon hu hr).mp e'))]; rfl
      | none =>
          have tv : unfoldSubst St σ v = none := by simp [unfoldSubst, hv]
          simp only [matchT, tv]
          refine ⟨fun τ h => ?_, ?_⟩
          · cases h
            intro w x hw
            by_cases e : w = v
            · subst e; simp at hw; subst hw; exact hr
            · rw [Function.update_of_ne e] at hw; exact hσ w x hw
          · simp [unfoldSubst_update]
  | .idx n, St, σ, r, canon, hσ, hr => by
      have shows := view_spec canon r
      simp only [matchR]
      generalize view St r = w at shows ⊢
      cases w with
      | idx m =>
          change unfold St r = .idx m at shows
          simp only [matchT, shows, Term.idx.injEq]
          refine ⟨fun τ h => ?_, ?_⟩
          · split_ifs at h; cases h; exact hσ
          · split_ifs with e
            · rfl
            · rfl
      | node head fs =>
          obtain ⟨_, eq⟩ := shows
          simp only [matchT, eq]
          exact ⟨fun τ h => (by cases h), by simp⟩
  | .node head ps, St, σ, r, canon, hσ, hr => by
      have shows := view_spec canon r
      simp only [matchR]
      generalize view St r = w at shows ⊢
      cases w with
      | idx m =>
          change unfold St r = .idx m at shows
          rw [shows]
          exact ⟨fun τ h => (by cases h), rfl⟩
      | node head' fs =>
          obtain ⟨kids, eq⟩ := shows
          rw [eq]
          have red : matchT (.node head ps) (unfoldSubst St σ) (.node head' (fieldsOfRefs St fs)) =
              if head = head' then matchFieldsT ps (unfoldSubst St σ) (fieldsOfRefs St fs)
              else none := rfl
          rw [red]
          dsimp only
          by_cases e : head = head'
          · rw [if_pos e, if_pos e]
            exact matchFieldsR_spec ps St σ fs canon hσ kids
          · rw [if_neg e, if_neg e]
            exact ⟨fun τ h => (by cases h), rfl⟩

theorem matchFieldsR_spec : ∀ (ps : TreePatFields Head V) (St : Store Head) (σ : Subst V Ref)
    (fs : List (ℕ × Ref)), Canonical St → CanonSubst St σ → (∀ x ∈ fs, CanonRef St x.2) →
    MatchROk St (matchFieldsR ps St σ fs) (matchFieldsT ps (unfoldSubst St σ) (fieldsOfRefs St fs))
  | .nil, St, σ, [], canon, hσ, _ => by
      simp only [matchFieldsR, fieldsOfRefs, matchFieldsT]
      exact ⟨fun τ h => by cases h; exact hσ, rfl⟩
  | .cons d p ps, St, σ, (d', r) :: rest, canon, hσ, kids => by
      simp only [matchFieldsR, fieldsOfRefs, matchFieldsT]
      by_cases e : d = d'
      · rw [if_pos e, if_pos e]
        have hr : CanonRef St r := kids (d', r) (by simp)
        obtain ⟨hres1, eq1⟩ := matchR_spec p St σ r canon hσ hr
        cases h1 : matchR p St σ r with
        | none =>
            rw [h1] at eq1
            simp only [Option.map_none] at eq1
            rw [← eq1]
            exact ⟨fun τ h => (by cases h), rfl⟩
        | some σ' =>
            rw [h1] at eq1 hres1
            simp only [Option.map_some] at eq1
            rw [← eq1, Option.bind_some, Option.bind_some]
            exact matchFieldsR_spec ps St σ' rest canon (hres1 σ' rfl)
              fun x m => kids x (by simp [m])
      · rw [if_neg e, if_neg e]
        exact ⟨fun τ h => (by cases h), rfl⟩
  | .nil, St, σ, _ :: _, canon, _, _ => by
      simp only [matchFieldsR, fieldsOfRefs, matchFieldsT]
      exact ⟨fun τ h => (by cases h), rfl⟩
  | .cons _ _ _, St, σ, [], canon, _, _ => by
      simp only [matchFieldsR, fieldsOfRefs, matchFieldsT]
      exact ⟨fun τ h => (by cases h), rfl⟩

end

/-! ## Building a template's instance in the store -/

/-- Plain lookup is one instance of the common variable resolver. -/
def referenceResolver (σ : Subst V Ref) : VariableResolver Head V :=
  fun variableName store => (store, σ variableName)

omit [DecidableEq V] [DecidableEq Head] in
theorem referenceResolver_correct (store : Store Head) (canonical : Canonical store)
    (σ : Subst V Ref) (valid : CanonSubst store σ) :
    ResolverCorrect store (referenceResolver σ) (unfoldSubst store σ) := by
  intro larger grows largerCanonical variableName
  refine ⟨List.prefix_refl _, largerCanonical, ?_, ?_⟩
  · intro result assigned
    exact (valid.prefix grows) variableName result assigned
  · exact congrFun (unfoldSubst_prefix canonical.topo grows valid) variableName

/-- Structural and contextual templates share the same constructor traversal. -/
def instR (p : TreePat Head V) (store : Store Head) (σ : Subst V Ref) : Store Head × Option Ref :=
  instantiateByR (referenceResolver σ) p store

def instFieldsR (ps : TreePatFields Head V) (store : Store Head) (σ : Subst V Ref) :
    Store Head × Option (List (Nat × Ref)) :=
  instantiateFieldsByR (referenceResolver σ) ps store

omit [DecidableEq V] in
/-- Building in the store is instantiating the tree. -/
theorem instR_spec (p : TreePat Head V) (store : Store Head) (σ : Subst V Ref)
    (canonical : Canonical store) (valid : CanonSubst store σ) :
    store <+: (instR p store σ).1 ∧ Canonical (instR p store σ).1 ∧
      (∀ r, (instR p store σ).2 = some r → CanonRef (instR p store σ).1 r) ∧
      (instR p store σ).2.map (unfold (instR p store σ).1) = p.inst (unfoldSubst store σ) :=
  instantiateByR_spec store (referenceResolver σ) (unfoldSubst store σ)
    (referenceResolver_correct store canonical σ valid) p store (List.prefix_refl _) canonical

omit [DecidableEq V] in
theorem instFieldsR_spec (ps : TreePatFields Head V) (store : Store Head) (σ : Subst V Ref)
    (canonical : Canonical store) (valid : CanonSubst store σ) :
    store <+: (instFieldsR ps store σ).1 ∧ Canonical (instFieldsR ps store σ).1 ∧
      (∀ fs, (instFieldsR ps store σ).2 = some fs → ∀ x ∈ fs, CanonRef (instFieldsR ps store σ).1 x.2) ∧
      (instFieldsR ps store σ).2.map (fieldsOfRefs (instFieldsR ps store σ).1) =
        ps.inst (unfoldSubst store σ) :=
  instantiateFieldsByR_spec store (referenceResolver σ) (unfoldSubst store σ)
    (referenceResolver_correct store canonical σ valid) ps store (List.prefix_refl _) canonical

end SharedMatcher

/-! ## Controls -/

namespace MatchControls

open SharingControls

/-- `(app $0 $0)`. -/
def pDiag : TreePat H ℕ := .node .app (.cons 0 (.mvar 0) (.cons 0 (.mvar 0) .nil))

/-- The empty substitution of references. -/
def none₀ : Subst ℕ Ref := fun _ => none

/-- `(app t1 t1)`, stored. -/
def St₁ : Store H := (encodeR [] (app t1 t1)).1

def r₁ : Ref := (encodeR [] (app t1 t1)).2

/-- `(app t1 t2)`, stored. -/
def St₂ : Store H := (encodeR [] (app t1 t2)).1

def r₂ : Ref := (encodeR [] (app t1 t2)).2

/-- Positive: `(app $0 $0)` matches `(app t1 t1)`; the second `$0` is a pointer comparison. -/
theorem diag_matches : ((matchR pDiag St₁ none₀ r₁).map fun σ => σ 0).isSome = true := by
  decide +kernel

/-- Negative: `(app $0 $0)` does not match `(app t1 t2)`: `t1` and `t2` are one node with two
different references. -/
theorem diag_refuses : (matchR pDiag St₂ none₀ r₂).isSome = false := by
  decide +kernel

end MatchControls

end Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings
