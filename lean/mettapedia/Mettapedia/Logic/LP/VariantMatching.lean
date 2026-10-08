import Mettapedia.Logic.LP.Matching
import Mettapedia.Logic.LP.StructuralTestRenaming

/-!
# Executable global variant witnesses

Structural collection pairs corresponding variable occurrences. The public
checker requires the collected relation to be functional in both directions.
The resulting finite map is applied simultaneously, so swaps are valid and do
not become cyclic logical substitutions. One map covers the whole batch.
-/

namespace Mettapedia.Logic.LP.VariantMatching

open UnificationRenaming

variable {σ : LPSignature}

private theorem size_tail (p : Term σ) (ps : List (Term σ)) :
    patternListSize ps < patternListSize (p :: ps) := by
  simp only [patternListSize, List.map_cons, List.sum_cons]
  have := Term.size_pos p
  omega

private theorem size_children (f : σ.functionSymbols)
    (args : Fin (σ.functionArity f) → Term σ) (ps : List (Term σ)) :
    patternListSize (finToList args ++ ps) < patternListSize (.app f args :: ps) := by
  simp [patternListSize, finToList, Term.size, List.map_map, Fin.sum_univ_def, Function.comp_def]

/-- Collect the variable pairs forced by equal constructor structure. -/
def collect [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    (ps qs : List (Term σ)) : Option (List (σ.vars × σ.vars)) :=
  match ps, qs with
  | [], [] => some []
  | .var x :: rest, .var y :: tail => do
    let pairs ← collect rest tail
    return (x, y) :: pairs
  | .const c :: rest, .const d :: tail =>
    if c = d then collect rest tail else none
  | .app f args :: rest, .app g targets :: tail =>
    if h : f = g then
      collect (finToList args ++ rest) (finToList (h ▸ targets) ++ tail)
    else none
  | _, _ => none
termination_by patternListSize ps
decreasing_by all_goals first | exact size_tail _ _ | exact size_children _ _ _

def Agrees (pairs : List (σ.vars × σ.vars)) (r : σ.vars → σ.vars) : Prop :=
  ∀ x y, (x, y) ∈ pairs → r x = y

def Occurs [DecidableEq σ.vars] (ps : List (Term σ)) (x : σ.vars) : Prop :=
  ∃ term ∈ ps, x ∈ term.freeVars

@[simp] theorem occurs_cons [DecidableEq σ.vars] (p : Term σ)
    (ps : List (Term σ)) (x : σ.vars) :
    Occurs (p :: ps) x ↔ x ∈ p.freeVars ∨ Occurs ps x := by
  simp [Occurs]

@[simp] theorem occurs_children [DecidableEq σ.vars]
    (f : σ.functionSymbols) (args : Fin (σ.functionArity f) → Term σ)
    (ps : List (Term σ)) (x : σ.vars) :
    Occurs (finToList args ++ ps) x ↔ Occurs (.app f args :: ps) x := by
  rw [occurs_cons]
  constructor
  · rintro ⟨term, member, present⟩
    rcases List.mem_append.mp member with member | member
    · obtain ⟨i, _, rfl⟩ := List.mem_map.mp member
      exact Or.inl (Term.mem_freeVars_app.mpr ⟨i, present⟩)
    · exact Or.inr ⟨term, member, present⟩
  · rintro (present | ⟨term, member, present⟩)
    · obtain ⟨i, present⟩ := Term.mem_freeVars_app.mp present
      exact ⟨args i, List.mem_append_left _
        (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩), present⟩
    · exact ⟨term, List.mem_append_right _ member, present⟩

/-- Every map agreeing with the collected pairs transforms the whole input. -/
theorem collect_sound [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    (ps qs : List (Term σ)) (pairs : List (σ.vars × σ.vars))
    (accepted : collect ps qs = some pairs) (r : σ.vars → σ.vars)
    (agree : Agrees pairs r) : ps.map (rename r) = qs := by
  match ps, qs with
  | [], [] => rfl
  | .var x :: rest, .var y :: tail =>
    cases hc : collect rest tail with
    | none => simp [collect, hc] at accepted
    | some entries =>
      have hp : pairs = (x, y) :: entries := by simpa [collect, hc] using accepted.symm
      subst pairs
      have head := agree x y (by simp)
      have step := collect_sound rest tail entries hc r
        (fun a b h => agree a b (List.mem_cons_of_mem _ h))
      simp [head, step]
  | .const c :: rest, .const d :: tail =>
    by_cases equal : c = d
    · subst d
      have step := collect_sound rest tail pairs
        (by simpa [collect] using accepted) r agree
      simp [step]
    · simp [collect, equal] at accepted
  | .app f args :: rest, .app g targets :: tail =>
    by_cases equal : f = g
    · subst g
      have step := collect_sound (finToList args ++ rest) (finToList targets ++ tail)
        pairs (by simpa [collect] using accepted) r agree
      simp only [List.map_append] at step
      obtain ⟨children, restEq⟩ := List.append_inj step (by simp)
      have pointwise : ∀ i, rename r (args i) = targets i := by
        simpa only [finToList, List.map_map, List.map_inj_left,
          List.mem_finRange, forall_const, Function.comp_apply] using children
      simp only [List.map_cons, rename_app, restEq]
      exact congrArg (· :: tail) (congrArg (Term.app f) (funext pointwise))
    · simp [collect, equal] at accepted
  | [], _ :: _ => simp [collect] at accepted
  | _ :: _, [] => simp [collect] at accepted
  | .var _ :: _, .const _ :: _ => simp [collect] at accepted
  | .var _ :: _, .app _ _ :: _ => simp [collect] at accepted
  | .const _ :: _, .var _ :: _ => simp [collect] at accepted
  | .const _ :: _, .app _ _ :: _ => simp [collect] at accepted
  | .app _ _ :: _, .var _ :: _ => simp [collect] at accepted
  | .app _ _ :: _, .const _ :: _ => simp [collect] at accepted
termination_by patternListSize ps
decreasing_by all_goals first | exact size_tail _ _ | exact size_children _ _ _

/-- Every renaming with the required constructor shape is collected; all its
    occurrences, including repeats across separate terms, remain in the list. -/
theorem collect_complete [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    (ps qs : List (Term σ)) (r : σ.vars → σ.vars)
    (same : ps.map (rename r) = qs) :
    ∃ pairs, collect ps qs = some pairs ∧ Agrees pairs r := by
  match ps, qs with
  | [], [] => exact ⟨[], by simp [collect], by simp [Agrees]⟩
  | .var x :: rest, .var y :: tail =>
    simp only [List.map_cons, rename_var, List.cons.injEq, Term.var.injEq] at same
    obtain ⟨pairs, accepted, agree⟩ := collect_complete rest tail r same.2
    refine ⟨(x, y) :: pairs, by simp [collect, accepted], ?_⟩
    intro a b member
    rcases List.mem_cons.mp member with equal | member
    · cases equal; exact same.1
    · exact agree a b member
  | .const c :: rest, .const d :: tail =>
    simp only [List.map_cons, rename_const, List.cons.injEq, Term.const.injEq] at same
    obtain ⟨rfl, same⟩ := same
    obtain ⟨pairs, accepted, agree⟩ := collect_complete rest tail r same
    exact ⟨pairs, by simpa [collect] using accepted, agree⟩
  | .app f args :: rest, .app g targets :: tail =>
    simp only [List.map_cons, rename_app, List.cons.injEq, Term.app.injEq] at same
    obtain ⟨⟨equal, children⟩, restEq⟩ := same
    subst g
    simp only [heq_eq_eq] at children
    have next : (finToList args ++ rest).map (rename r) = finToList targets ++ tail := by
      simp only [List.map_append, finToList, List.map_map, restEq]
      congr 1
      exact congrArg (List.map · (List.finRange _)) children
    obtain ⟨pairs, accepted, agree⟩ := collect_complete _ _ r next
    exact ⟨pairs, by simpa [collect] using accepted, agree⟩
  | [], _ :: _ => simp at same
  | _ :: _, [] => simp at same
  | .var _ :: _, .const _ :: _ => simp at same
  | .var _ :: _, .app _ _ :: _ => simp at same
  | .const _ :: _, .var _ :: _ => simp at same
  | .const _ :: _, .app _ _ :: _ => simp at same
  | .app _ _ :: _, .var _ :: _ => simp at same
  | .app _ _ :: _, .const _ :: _ => simp at same
termination_by patternListSize ps
decreasing_by all_goals first | exact size_tail _ _ | exact size_children _ _ _

/-- The finite map's domain covers exactly the variables in the input batch. -/
theorem collect_domain [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] (ps qs : List (Term σ))
    (pairs : List (σ.vars × σ.vars)) (accepted : collect ps qs = some pairs)
    (x : σ.vars) : (∃ y, (x, y) ∈ pairs) ↔ Occurs ps x := by
  match ps, qs with
  | [], [] =>
    have hp : pairs = [] := by simpa [collect] using accepted.symm
    simp [hp, Occurs]
  | .var a :: rest, .var b :: tail =>
    cases hc : collect rest tail with
    | none => simp [collect, hc] at accepted
    | some entries =>
      have hp : pairs = (a, b) :: entries := by simpa [collect, hc] using accepted.symm
      subst pairs
      have step := collect_domain rest tail entries hc x
      simp [List.mem_cons, Prod.mk.injEq, exists_or, step, Term.freeVars]
  | .const c :: rest, .const d :: tail =>
    by_cases equal : c = d
    · subst d
      have step := collect_domain rest tail pairs (by simpa [collect] using accepted) x
      simpa [Term.freeVars] using step
    · simp [collect, equal] at accepted
  | .app f args :: rest, .app g targets :: tail =>
    by_cases equal : f = g
    · subst g
      have step := collect_domain (finToList args ++ rest) (finToList targets ++ tail)
        pairs (by simpa [collect] using accepted) x
      simpa using step
    · simp [collect, equal] at accepted
  | [], _ :: _ => simp [collect] at accepted
  | _ :: _, [] => simp [collect] at accepted
  | .var _ :: _, .const _ :: _ => simp [collect] at accepted
  | .var _ :: _, .app _ _ :: _ => simp [collect] at accepted
  | .const _ :: _, .var _ :: _ => simp [collect] at accepted
  | .const _ :: _, .app _ _ :: _ => simp [collect] at accepted
  | .app _ _ :: _, .var _ :: _ => simp [collect] at accepted
  | .app _ _ :: _, .const _ :: _ => simp [collect] at accepted
termination_by patternListSize ps
decreasing_by all_goals first | exact size_tail _ _ | exact size_children _ _ _

def PartialBijection (pairs : List (σ.vars × σ.vars)) : Prop :=
  ∀ x y, (x, y) ∈ pairs → ∀ u v, (u, v) ∈ pairs → (x = u ↔ y = v)

def partialBijection? [DecidableEq σ.vars] (pairs : List (σ.vars × σ.vars)) : Bool :=
  pairs.all fun left => pairs.all fun right => decide (left.1 = right.1 ↔ left.2 = right.2)

theorem partialBijection?_eq_true [DecidableEq σ.vars] (pairs : List (σ.vars × σ.vars)) :
    partialBijection? pairs = true ↔ PartialBijection pairs := by
  simp only [partialBijection?, List.all_eq_true, decide_eq_true_eq, PartialBijection]
  constructor
  · intro h x y member u v present
    exact h (x, y) member (u, v) present
  · intro h left member right present
    exact h left.1 left.2 member right.1 right.2 present

/-- Simultaneous finite renaming; names outside the domain stay unchanged. -/
def lookup [DecidableEq σ.vars] (pairs : List (σ.vars × σ.vars)) (x : σ.vars) : σ.vars :=
  match pairs.find? (fun pair => pair.1 == x) with
  | some pair => pair.2
  | none => x

theorem lookup_agrees [DecidableEq σ.vars] (pairs : List (σ.vars × σ.vars))
    (bijective : PartialBijection pairs) : Agrees pairs (lookup pairs) := by
  intro x y member
  induction pairs with
  | nil => simp at member
  | cons pair rest ih =>
    by_cases same : pair.1 = x
    · have value := (bijective pair.1 pair.2 (List.mem_cons_self ..) x y member).mp same
      simp [lookup, same, value]
    · have present : (x, y) ∈ rest := by
        rcases List.mem_cons.mp member with equal | present
        · exact False.elim (same (congrArg Prod.fst equal).symm)
        · exact present
      have step := ih (fun a b ha c d hd =>
        bijective a b (List.mem_cons_of_mem _ ha) c d (List.mem_cons_of_mem _ hd)) present
      simpa [lookup, same] using step

theorem lookup_injective [DecidableEq σ.vars] (pairs : List (σ.vars × σ.vars))
    (bijective : PartialBijection pairs) :
    Set.InjOn (lookup pairs) {x | ∃ y, (x, y) ∈ pairs} := by
  intro x hx u hu equal
  obtain ⟨y, hy⟩ := hx
  obtain ⟨v, hv⟩ := hu
  rw [lookup_agrees pairs bijective x y hy, lookup_agrees pairs bijective u v hv] at equal
  exact (bijective x y hy u v hv).mpr equal

/-- The executable interface publishes a witness only after both directions
    of the finite-map consistency check pass. -/
def solve [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] (ps qs : List (Term σ)) :
    Option (List (σ.vars × σ.vars)) := do
  let pairs ← collect ps qs
  if partialBijection? pairs then some pairs else none

def VariantBatch [DecidableEq σ.vars] (ps qs : List (Term σ)) : Prop :=
  ∃ r : σ.vars → σ.vars, Set.InjOn r {x | Occurs ps x} ∧ ps.map (rename r) = qs

/-- Every successful result is a usable, globally injective renaming. -/
theorem solve_sound [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] (ps qs : List (Term σ)) (pairs : List (σ.vars × σ.vars))
    (accepted : solve ps qs = some pairs) :
    PartialBijection pairs ∧ Set.InjOn (lookup pairs) {x | Occurs ps x} ∧
      ps.map (rename (lookup pairs)) = qs := by
  cases hc : collect ps qs with
  | none => simp [solve, hc] at accepted
  | some entries =>
    by_cases checked : partialBijection? entries = true
    · have equal : entries = pairs := by simpa [solve, hc, checked] using accepted
      subst entries
      have bijective := (partialBijection?_eq_true pairs).mp checked
      refine ⟨bijective, ?_, collect_sound ps qs pairs hc _ (lookup_agrees pairs bijective)⟩
      intro x hx y hy same
      exact lookup_injective pairs bijective
        ((collect_domain ps qs pairs hc x).mpr hx)
        ((collect_domain ps qs pairs hc y).mpr hy) same
    · simp [solve, hc, checked] at accepted

/-- Constructor collection and the two consistency checks lose no variants. -/
theorem solve_complete [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] (ps qs : List (Term σ))
    (variant : VariantBatch ps qs) : ∃ pairs, solve ps qs = some pairs := by
  obtain ⟨r, injective, same⟩ := variant
  obtain ⟨pairs, collected, agree⟩ := collect_complete ps qs r same
  have bijective : PartialBijection pairs := by
    intro x y hxy u v huv
    constructor
    · intro equal
      subst u
      exact (agree x y hxy).symm.trans (agree x v huv)
    · intro equal
      apply injective
        ((collect_domain ps qs pairs collected x).mp ⟨y, hxy⟩)
        ((collect_domain ps qs pairs collected u).mp ⟨v, huv⟩)
      exact (agree x y hxy).trans (equal.trans (agree u v huv).symm)
  have checked := (partialBijection?_eq_true pairs).mpr bijective
  exact ⟨pairs, by simp [solve, collected, checked]⟩

theorem solve_none_iff [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] (ps qs : List (Term σ)) :
    solve ps qs = none ↔ ¬VariantBatch ps qs := by
  constructor
  · intro rejected variant
    obtain ⟨pairs, accepted⟩ := solve_complete ps qs variant
    simp [rejected] at accepted
  · intro impossible
    cases h : solve ps qs with
    | none => rfl
    | some pairs =>
      have sound := solve_sound ps qs pairs h
      exact False.elim (impossible ⟨lookup pairs, sound.2⟩)

/-- The batch relation extends the library's existing single-term variant
    relation, with exactly the same notion of an injective variable renaming. -/
theorem singleton_iff [DecidableEq σ.vars] (p q : Term σ) :
    VariantBatch [p] [q] ↔ StructuralTestRenaming.Variant p q := by
  simp [VariantBatch, StructuralTestRenaming.Variant, Occurs]

theorem swap_bijection (pairs : List (σ.vars × σ.vars)) (h : PartialBijection pairs) :
    PartialBijection (pairs.map Prod.swap) := by
  intro x y hxy u v huv
  obtain ⟨⟨a, b⟩, hab, equal⟩ := List.mem_map.mp hxy
  cases equal
  obtain ⟨⟨c, d⟩, hcd, equal⟩ := List.mem_map.mp huv
  cases equal
  exact (h a b hab c d hcd).symm

/-- The inverse witness undoes a saved renaming on every captured identity. -/
theorem lookup_round_trip [DecidableEq σ.vars] (pairs : List (σ.vars × σ.vars))
    (h : PartialBijection pairs) (x y : σ.vars) (member : (x, y) ∈ pairs) :
    lookup (pairs.map Prod.swap) (lookup pairs x) = x := by
  rw [lookup_agrees pairs h x y member]
  exact lookup_agrees _ (swap_bijection pairs h) y x
    (List.mem_map.mpr ⟨(x, y), member, rfl⟩)

/-- Renaming and its inverse recover complete terms, including their shared
    variables. Applying the map is simultaneous, not recursive dereferencing. -/
theorem solve_round_trip [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] (ps qs : List (Term σ)) (pairs : List (σ.vars × σ.vars))
    (accepted : solve ps qs = some pairs) :
    qs.map (rename (lookup (pairs.map Prod.swap))) = ps := by
  have sound := solve_sound ps qs pairs accepted
  have collected : collect ps qs = some pairs := by
    cases hc : collect ps qs with
    | none => simp [solve, hc] at accepted
    | some entries =>
      by_cases checked : partialBijection? entries = true
      · simpa [solve, hc, checked] using accepted
      · simp [solve, hc, checked] at accepted
  rw [← sound.2.2, List.map_map]
  conv_rhs => rw [← List.map_id ps]
  apply List.map_congr_left
  intro term member
  rw [Function.comp_apply, rename_comp]
  apply Subst.applyTerm_eq_self
  intro x present
  obtain ⟨y, hxy⟩ := (collect_domain ps qs pairs collected x).mpr ⟨term, member, present⟩
  exact congrArg Term.var (lookup_round_trip pairs sound.1 x y hxy)

end Mettapedia.Logic.LP.VariantMatching
