/-
Loop persistence for the raw merge-insertion steps.

The merge fold's conditional invariant peels backward from the public
loop-filter fact: to use the induction hypothesis at `source`, a loop-free
extended record must certify a loop-free `source`.  This file proves the two
raw (non-reconciliation) cases:

* `hasLoop_false_of_addValRaw_fresh` — a loop-free `addValRaw source key
  value` with `classValues source key = []` certifies loop-free `source`.

The engine is two general facts about the bounded resolver:

* **Success replay** (`resolveAtomAux_some_of_cons_val_fresh`): with the
  equality graph unchanged and the fresh key's class valueless in `source`,
  the source resolution tree is the extended tree pruned to immediate
  successes at the fresh class, so extended success replays in `source` at
  the same fuel and visited set.

* **Fuel canonicity** (`resolveAtomAux_some_at_resolutionFuel`): success at
  any fuel implies success at the canonical `resolutionFuel` budget.  Along
  any successful path every value jump passes the visited guard and then
  pushes its whole class, so the jumped classes are pairwise disjoint and
  each stored value pays for its own descent: failure at the canonical
  budget is always a genuine cycle, never budget shortfall.
-/
import Mettapedia.Languages.MeTTa.HE.HumanMatchCompleteness

namespace Mettapedia.Languages.MeTTa.HE.LeaTTaBridge

/-! ## Generic list accounting -/

private theorem sum_drop_le {α : Type} :
    ∀ (l : List α) (g g' : α → Nat) (a : α), a ∈ l →
      (∀ w ∈ l, g' w ≤ g w) → g' a = 0 →
      (l.map g').sum + g a ≤ (l.map g).sum
  | [], _, _, _, ha, _, _ => absurd ha (List.not_mem_nil)
  | head :: tail, g, g', a, ha, hmono, hzero => by
    simp only [List.map_cons, List.sum_cons]
    cases List.mem_cons.mp ha with
    | inl heq =>
      subst heq
      have htail : (tail.map g').sum ≤ (tail.map g).sum := by
        apply List.sum_le_sum
        intro w hw
        exact hmono w (List.mem_cons_of_mem _ hw)
      omega
    | inr htail =>
      have hhead : g' head ≤ g head :=
        hmono head List.mem_cons_self
      have := sum_drop_le tail g g' a htail
        (fun w hw => hmono w (List.mem_cons_of_mem _ hw)) hzero
      omega

/-! ## Class-machinery facts -/

private theorem lookupVal_mem' :
    ∀ {lb : Metta.Bindings} {x : String} {a : Metta.Atom},
      Metta.Bindings.lookupVal lb x = some a →
      Metta.BindingRel.val x a ∈ lb
  | [], _, _, h => by simp [Metta.Bindings.lookupVal] at h
  | .val y v :: rest, x, a, h => by
    simp only [Metta.Bindings.lookupVal] at h
    by_cases hxy : (x == y) = true
    · rw [if_pos hxy] at h
      cases h
      have : x = y := by simpa using hxy
      subst this
      exact List.mem_cons_self
    · rw [if_neg hxy] at h
      exact List.mem_cons_of_mem _ (lookupVal_mem' h)
  | .eq _ _ :: rest, x, a, h => by
    simp only [Metta.Bindings.lookupVal] at h
    exact List.mem_cons_of_mem _ (lookupVal_mem' h)

private theorem mem_eqVarsFold_mono {v : String} :
    ∀ (l : Metta.Bindings) (acc : List String), v ∈ acc →
      v ∈ l.foldl (fun acc r => match r with
        | Metta.BindingRel.eq x y =>
            let acc := if acc.contains y then acc else acc ++ [y]
            if acc.contains x then acc else acc ++ [x]
        | _ => acc) acc
  | [], _, hv => hv
  | rel :: rest, acc, hv => by
    simp only [List.foldl_cons]
    apply mem_eqVarsFold_mono rest
    cases rel with
    | val _ _ => exact hv
    | eq x y =>
      have hstep : ∀ acc2 : List String, v ∈ acc2 →
          v ∈ (if acc2.contains x then acc2 else acc2 ++ [x]) := by
        intro acc2 hv2
        split
        · exact hv2
        · exact List.mem_append_left _ hv2
      have h1 : v ∈ (if acc.contains y then acc else acc ++ [y]) := by
        split
        · exact hv
        · exact List.mem_append_left _ hv
      exact hstep _ h1

private theorem endpoint_mem_eqVarsInOrder
    {lb : Metta.Bindings} {a b : String}
    (hmem : Metta.BindingRel.eq a b ∈ lb) :
    a ∈ Metta.Bindings.eqVarsInOrder lb ∧
      b ∈ Metta.Bindings.eqVarsInOrder lb := by
  unfold Metta.Bindings.eqVarsInOrder
  have hmem' : Metta.BindingRel.eq a b ∈ lb.reverse :=
    List.mem_reverse.mpr hmem
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hmem'
  rw [hsplit, List.foldl_append, List.foldl_cons]
  set seed := pre.foldl (fun acc r => match r with
    | Metta.BindingRel.eq x y =>
        let acc := if acc.contains y then acc else acc ++ [y]
        if acc.contains x then acc else acc ++ [x]
    | _ => acc) [] with hseed
  have hstep : ∀ acc2 : List String, b ∈ acc2 →
      a ∈ (if acc2.contains a then acc2 else acc2 ++ [a]) ∧
        b ∈ (if acc2.contains a then acc2 else acc2 ++ [a]) := by
    intro acc2 hb
    constructor
    · split
      · rename_i ha
        simpa using ha
      · exact List.mem_append_right _ (by simp)
    · split
      · exact hb
      · exact List.mem_append_left _ hb
  have hb2 : b ∈ (if seed.contains b then seed else seed ++ [b]) := by
    split
    · rename_i hbc
      simpa using hbc
    · exact List.mem_append_right _ (by simp)
  obtain ⟨hafin, hbfin⟩ :=
    hstep (if seed.contains b then seed else seed ++ [b]) hb2
  exact ⟨mem_eqVarsFold_mono post _ hafin,
    mem_eqVarsFold_mono post _ hbfin⟩

private theorem self_mem_eqClass
    (lb : Metta.Bindings) (x : String) :
    x ∈ Metta.Bindings.eqClass lb x :=
  mem_leaEqClass_iff_reachable.mpr .rfl

private theorem eqClass_mem_congr
    {lb : Metta.Bindings} {x y : String}
    (hxy : y ∈ Metta.Bindings.eqClass lb x) (w : String) :
    w ∈ Metta.Bindings.eqClass lb y ↔
      w ∈ Metta.Bindings.eqClass lb x := by
  rw [mem_leaEqClass_iff_reachable, mem_leaEqClass_iff_reachable]
  have hreach := mem_leaEqClass_iff_reachable.mp hxy
  exact ⟨fun h => hreach.trans h, fun h => hreach.symm.trans h⟩

private theorem mem_eqVarsInOrder_of_reachable_ne
    {lb : Metta.Bindings} {x c : String} (hne : x ≠ c)
    (hreach : (EqualityClosure.edgeGraph
      (leaEqualityEdges lb)).Reachable x c) :
    x ∈ Metta.Bindings.eqVarsInOrder lb := by
  apply hreach.elim
  intro walk
  cases walk with
  | nil => exact absurd rfl hne
  | cons hadj tail =>
    rcases (EqualityClosure.edgeGraph_adj_iff.mp hadj).2 with
      hedge | hedge
    · exact (endpoint_mem_eqVarsInOrder
        (mem_leaEqualityEdges_iff.mp hedge)).1
    · exact (endpoint_mem_eqVarsInOrder
        (mem_leaEqualityEdges_iff.mp hedge)).2

private theorem self_mem_eqClassOrdered
    (lb : Metta.Bindings) (x : String) :
    x ∈ Metta.Bindings.eqClassOrdered lb x := by
  unfold Metta.Bindings.eqClassOrdered
  cases hfilter : (Metta.Bindings.eqVarsInOrder lb).filter
      (fun y => (Metta.Bindings.eqClass lb x).contains y) with
  | nil => simp
  | cons c cs =>
    have hc : c ∈ (Metta.Bindings.eqVarsInOrder lb).filter
        (fun y => (Metta.Bindings.eqClass lb x).contains y) := by
      rw [hfilter]; exact List.mem_cons_self
    have hcclass : c ∈ Metta.Bindings.eqClass lb x := by
      simpa using (List.mem_filter.mp hc).2
    have hx : x ∈ Metta.Bindings.eqVarsInOrder lb := by
      by_cases hxc : x = c
      · subst hxc
        exact (List.mem_filter.mp hc).1
      · exact mem_eqVarsInOrder_of_reachable_ne hxc
          (mem_leaEqClass_iff_reachable.mp hcclass)
    have hxf : x ∈ (Metta.Bindings.eqVarsInOrder lb).filter
        (fun y => (Metta.Bindings.eqClass lb x).contains y) :=
      List.mem_filter.mpr ⟨hx, by simpa using self_mem_eqClass lb x⟩
    rw [hfilter] at hxf
    try rw [hfilter]
    exact hxf

private theorem eqClassOrdered_congr_of_mem
    {lb : Metta.Bindings} {x y : String}
    (hxy : y ∈ Metta.Bindings.eqClass lb x) :
    Metta.Bindings.eqClassOrdered lb y =
      Metta.Bindings.eqClassOrdered lb x := by
  unfold Metta.Bindings.eqClassOrdered
  have hfilter : (Metta.Bindings.eqVarsInOrder lb).filter
      (fun w => (Metta.Bindings.eqClass lb y).contains w) =
      (Metta.Bindings.eqVarsInOrder lb).filter
        (fun w => (Metta.Bindings.eqClass lb x).contains w) := by
    apply List.filter_congr
    intro w _
    have := eqClass_mem_congr hxy w
    by_cases hw : w ∈ Metta.Bindings.eqClass lb x
    · simp [hw, this.mpr hw]
    · have hwy : w ∉ Metta.Bindings.eqClass lb y :=
        fun hcontra => hw (this.mp hcontra)
      simp [hw, hwy]
  rw [hfilter]
  cases hcase : (Metta.Bindings.eqVarsInOrder lb).filter
      (fun w => (Metta.Bindings.eqClass lb x).contains w) with
  | nil =>
    by_cases hxyeq : y = x
    · rw [hxyeq]
    · exfalso
      have hy : y ∈ Metta.Bindings.eqVarsInOrder lb :=
        mem_eqVarsInOrder_of_reachable_ne hxyeq
          (mem_leaEqClass_iff_reachable.mp hxy).symm
      have : y ∈ (Metta.Bindings.eqVarsInOrder lb).filter
          (fun w => (Metta.Bindings.eqClass lb x).contains w) :=
        List.mem_filter.mpr ⟨hy, by simpa using hxy⟩
      rw [hcase] at this
      exact absurd this (List.not_mem_nil)
  | cons c cs => rfl

private theorem mem_eqClassOrdered_cases'
    {lb : Metta.Bindings} {x y : String}
    (h : y ∈ Metta.Bindings.eqClassOrdered lb x) :
    y = x ∨ y ∈ Metta.Bindings.eqClass lb x := by
  unfold Metta.Bindings.eqClassOrdered at h
  cases hfilter : (Metta.Bindings.eqVarsInOrder lb).filter
      (fun z => (Metta.Bindings.eqClass lb x).contains z) with
  | nil =>
    rw [hfilter] at h
    simp only [List.mem_singleton] at h
    exact Or.inl h
  | cons head tail =>
    rw [hfilter] at h
    have hmem : y ∈ (Metta.Bindings.eqVarsInOrder lb).filter
        (fun z => (Metta.Bindings.eqClass lb x).contains z) := by
      rw [hfilter]; exact h
    exact Or.inr (by simpa using (List.mem_filter.mp hmem).2)

/-! ## Invariance of the class machinery under a value cons -/

section ConsVal

variable (source : Metta.Bindings) (key : String) (value : Metta.Atom)

private theorem leaEqualityEdges_cons_val :
    leaEqualityEdges (Metta.BindingRel.val key value :: source) =
      leaEqualityEdges source := rfl

private theorem eqClass_cons_val_mem (z w : String) :
    w ∈ Metta.Bindings.eqClass
        (Metta.BindingRel.val key value :: source) z ↔
      w ∈ Metta.Bindings.eqClass source z := by
  rw [mem_leaEqClass_iff_reachable, mem_leaEqClass_iff_reachable,
    leaEqualityEdges_cons_val]

private theorem eqVarsInOrder_cons_val :
    Metta.Bindings.eqVarsInOrder
        (Metta.BindingRel.val key value :: source) =
      Metta.Bindings.eqVarsInOrder source := by
  unfold Metta.Bindings.eqVarsInOrder
  rw [List.reverse_cons, List.foldl_append]
  rfl

private theorem eqClassOrdered_cons_val (z : String) :
    Metta.Bindings.eqClassOrdered
        (Metta.BindingRel.val key value :: source) z =
      Metta.Bindings.eqClassOrdered source z := by
  unfold Metta.Bindings.eqClassOrdered
  rw [eqVarsInOrder_cons_val]
  have hfilter : (Metta.Bindings.eqVarsInOrder source).filter
      (fun y => (Metta.Bindings.eqClass
        (Metta.BindingRel.val key value :: source) z).contains y) =
      (Metta.Bindings.eqVarsInOrder source).filter
        (fun y => (Metta.Bindings.eqClass source z).contains y) := by
    apply List.filter_congr
    intro w _
    have := eqClass_cons_val_mem source key value z w
    by_cases hw : w ∈ Metta.Bindings.eqClass source z
    · simp [hw, this.mpr hw]
    · have hw' : w ∉ Metta.Bindings.eqClass
          (Metta.BindingRel.val key value :: source) z :=
        fun hcontra => hw (this.mp hcontra)
      simp [hw, hw']
  rw [hfilter]

private theorem eqRepresentative_cons_val (z : String) :
    Metta.Bindings.eqRepresentative
        (Metta.BindingRel.val key value :: source) z =
      Metta.Bindings.eqRepresentative source z := by
  unfold Metta.Bindings.eqRepresentative
  rw [eqClassOrdered_cons_val]

private theorem lookupVal_cons_val (z : String) :
    Metta.Bindings.lookupVal
        (Metta.BindingRel.val key value :: source) z =
      if (z == key) = true then some value
      else Metta.Bindings.lookupVal source z := by
  simp only [Metta.Bindings.lookupVal]

private theorem classValues_cons_val_untouched {z : String}
    (hkey : key ∉ Metta.Bindings.eqClassOrdered source z) :
    Metta.Bindings.classValues
        (Metta.BindingRel.val key value :: source) z =
      Metta.Bindings.classValues source z := by
  unfold Metta.Bindings.classValues
  rw [eqClassOrdered_cons_val]
  apply List.filterMap_congr
  intro w hw
  rw [lookupVal_cons_val]
  have hne : (w == key) ≠ true := by
    intro hcontra
    have : w = key := by simpa using hcontra
    subst this
    exact hkey hw
  rw [if_neg hne]

private theorem classValues_source_nil_of_key_class {z : String}
    (hfresh : Metta.Bindings.classValues source key = [])
    (hkey : key ∈ Metta.Bindings.eqClassOrdered source z) :
    Metta.Bindings.classValues source z = [] := by
  rcases mem_eqClassOrdered_cases' hkey with heq | hclass
  · subst heq; exact hfresh
  · have hordered : Metta.Bindings.eqClassOrdered source key =
        Metta.Bindings.eqClassOrdered source z :=
      eqClassOrdered_congr_of_mem hclass
    unfold Metta.Bindings.classValues at hfresh ⊢
    rw [← hordered]
    exact hfresh

end ConsVal

/-! ## Success replay: extended cons-val record to source -/

private theorem mapM_some_of_pointwise
    {f g : Metta.Atom → Option Metta.Atom} :
    ∀ (xs : List Metta.Atom) (ys : List Metta.Atom),
      xs.mapM f = some ys →
      (∀ z ∈ xs, ∀ w, f z = some w → (g z).isSome = true) →
      ∃ ws, xs.mapM g = some ws
  | [], _, _, _ => ⟨[], rfl⟩
  | x :: xs, ys, h, hpt => by
    cases hx : f x with
    | none => simp [List.mapM_cons, hx] at h
    | some xr =>
      cases hxs : xs.mapM f with
      | none => simp [List.mapM_cons, hx, hxs] at h
      | some xsr =>
        obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp
          (hpt x List.mem_cons_self xr hx)
        obtain ⟨ws, hws⟩ := mapM_some_of_pointwise xs xsr hxs
          (fun z hz => hpt z (List.mem_cons_of_mem _ hz))
        exact ⟨w :: ws, by simp [List.mapM_cons, hw, hws]⟩

/-- Extended success replays in the source at the same fuel and visited
set: the source resolution tree is the extended tree pruned to immediate
successes at the fresh key's (valueless) class. -/
private theorem resolveAtomAux_some_of_cons_val_fresh
    {source : Metta.Bindings} {key : String} {value : Metta.Atom}
    (hfresh : Metta.Bindings.classValues source key = []) :
    ∀ (fuel : Nat) (visited : List String) (a r : Metta.Atom),
      Metta.Bindings.resolveAtomAux
          (Metta.BindingRel.val key value :: source) fuel visited a =
        some r →
      (Metta.Bindings.resolveAtomAux source fuel visited a).isSome =
        true := by
  intro fuel
  induction fuel with
  | zero =>
    intro visited a r h
    simp [Metta.Bindings.resolveAtomAux] at h
  | succ fuel ih =>
    intro visited a r h
    cases a with
    | sym s => simp [Metta.Bindings.resolveAtomAux]
    | gnd g => simp [Metta.Bindings.resolveAtomAux]
    | expr xs =>
      simp only [Metta.Bindings.resolveAtomAux] at h ⊢
      cases hmap : xs.mapM (Metta.Bindings.resolveAtomAux
          (Metta.BindingRel.val key value :: source) fuel visited) with
      | none => rw [hmap] at h; cases h
      | some ys =>
        obtain ⟨ws, hws⟩ := mapM_some_of_pointwise xs ys hmap
          (fun z _ w hw => ih visited z w hw)
        rw [hws]
        simp
    | var z =>
      simp only [Metta.Bindings.resolveAtomAux] at h ⊢
      rw [eqClassOrdered_cons_val] at h
      by_cases hguard : ((Metta.Bindings.eqClassOrdered source z).any
          visited.contains) = true
      · rw [if_pos hguard] at h
        cases h
      · rw [if_neg hguard] at h
        rw [if_neg hguard]
        by_cases hkey : key ∈ Metta.Bindings.eqClassOrdered source z
        · rw [classValues_source_nil_of_key_class source key hfresh hkey]
          simp
        · rw [classValues_cons_val_untouched source key value hkey] at h
          cases hvalues : Metta.Bindings.classValues source z with
          | nil =>
            rw [hvalues] at h
            simp
          | cons v rest =>
            rw [hvalues] at h
            cases v with
            | var y =>
              by_cases hcontains :
                  y ∈ Metta.Bindings.eqClassOrdered source z
              · by_cases hlen :
                    (Metta.Bindings.eqClassOrdered source z).length = 1
                · simp [hcontains, hlen] at h
                · simp [hcontains, hlen]
              · have hrec : Metta.Bindings.resolveAtomAux
                    (Metta.BindingRel.val key value :: source) fuel
                    (Metta.Bindings.eqClassOrdered source z ++ visited)
                    (Metta.Atom.var y) = some r := by
                  simpa [hcontains] using h
                simpa [hcontains] using ih _ _ _ hrec
            | sym s =>
              have hrec : Metta.Bindings.resolveAtomAux
                  (Metta.BindingRel.val key value :: source) fuel
                  (Metta.Bindings.eqClassOrdered source z ++ visited)
                  (Metta.Atom.sym s) = some r := by
                simpa using h
              simpa using ih _ _ _ hrec
            | gnd g =>
              have hrec : Metta.Bindings.resolveAtomAux
                  (Metta.BindingRel.val key value :: source) fuel
                  (Metta.Bindings.eqClassOrdered source z ++ visited)
                  (Metta.Atom.gnd g) = some r := by
                simpa using h
              simpa using ih _ _ _ hrec
            | expr atoms =>
              have hrec : Metta.Bindings.resolveAtomAux
                  (Metta.BindingRel.val key value :: source) fuel
                  (Metta.Bindings.eqClassOrdered source z ++ visited)
                  (Metta.Atom.expr atoms) = some r := by
                simpa using h
              simpa using ih _ _ _ hrec

/-! ## Fuel canonicity -/

/-- The unspent value budget: every stored value of a class not yet touched
by the visited set still pays for its own descent plus one jump step. -/
private def remBudget (b : Metta.Bindings) (visited : List String) : Nat :=
  (b.map (fun rel => match rel with
    | Metta.BindingRel.val x v =>
        if (Metta.Bindings.eqClassOrdered b x).any visited.contains then 0
        else v.size + 1
    | Metta.BindingRel.eq _ _ => 0)).sum

private theorem remBudget_term_mono (b : Metta.Bindings)
    {small large : List String} (hsub : ∀ s ∈ small, s ∈ large)
    (rel : Metta.BindingRel) :
    (match rel with
      | Metta.BindingRel.val x v =>
          if (Metta.Bindings.eqClassOrdered b x).any large.contains then 0
          else v.size + 1
      | Metta.BindingRel.eq _ _ => 0) ≤
    (match rel with
      | Metta.BindingRel.val x v =>
          if (Metta.Bindings.eqClassOrdered b x).any small.contains then 0
          else v.size + 1
      | Metta.BindingRel.eq _ _ => 0) := by
  cases rel with
  | eq _ _ => simp
  | val x v =>
    simp only []
    by_cases hsmall : ((Metta.Bindings.eqClassOrdered b x).any
        small.contains) = true
    · have hlarge : ((Metta.Bindings.eqClassOrdered b x).any
          large.contains) = true := by
        rw [List.any_eq_true] at hsmall ⊢
        obtain ⟨w, hw, hcontains⟩ := hsmall
        exact ⟨w, hw, by
          have : w ∈ small := by simpa using hcontains
          simpa using hsub w this⟩
      rw [if_pos hsmall, if_pos hlarge]
    · rw [if_neg hsmall]
      split <;> omega

/-- Jumping into a class value strictly repays the budget: the value's own
relation drops out of the unspent sum. -/
private theorem remBudget_jump
    {b : Metta.Bindings} {x : String} {v : Metta.Atom} {visited : List String}
    (hguard : ((Metta.Bindings.eqClassOrdered b x).any
      visited.contains) = false)
    (hhead : v ∈ Metta.Bindings.classValues b x) :
    remBudget b (Metta.Bindings.eqClassOrdered b x ++ visited) +
      (v.size + 1) ≤ remBudget b visited := by
  unfold Metta.Bindings.classValues at hhead
  obtain ⟨y, hy, hlookup⟩ := List.mem_filterMap.mp hhead
  have hyv : Metta.BindingRel.val y v ∈ b := lookupVal_mem' hlookup
  have hyclass : Metta.Bindings.eqClassOrdered b y =
      Metta.Bindings.eqClassOrdered b x := by
    rcases mem_eqClassOrdered_cases' hy with heq | hclass
    · rw [heq]
    · exact eqClassOrdered_congr_of_mem hclass
  have hdrop := sum_drop_le b
    (fun rel => match rel with
      | Metta.BindingRel.val w u =>
          if (Metta.Bindings.eqClassOrdered b w).any visited.contains then 0
          else u.size + 1
      | Metta.BindingRel.eq _ _ => 0)
    (fun rel => match rel with
      | Metta.BindingRel.val w u =>
          if (Metta.Bindings.eqClassOrdered b w).any
              (Metta.Bindings.eqClassOrdered b x ++ visited).contains then 0
          else u.size + 1
      | Metta.BindingRel.eq _ _ => 0)
    (Metta.BindingRel.val y v) hyv
    (fun w _ => remBudget_term_mono b
      (fun s hs => List.mem_append_right _ hs) w)
    (by
      simp only []
      have hyin : ((Metta.Bindings.eqClassOrdered b y).any
          (Metta.Bindings.eqClassOrdered b x ++ visited).contains) =
            true := by
        rw [List.any_eq_true]
        refine ⟨y, self_mem_eqClassOrdered b y, ?_⟩
        have : y ∈ Metta.Bindings.eqClassOrdered b x ++ visited :=
          List.mem_append_left _ hy
        simpa using this
      rw [if_pos hyin])
  have hterm : (match Metta.BindingRel.val y v with
      | Metta.BindingRel.val w u =>
          if (Metta.Bindings.eqClassOrdered b w).any visited.contains then 0
          else u.size + 1
      | Metta.BindingRel.eq _ _ => 0) = v.size + 1 := by
    simp only []
    rw [hyclass, hguard]
    simp
  rw [hterm] at hdrop
  exact hdrop

private theorem mapM_transfer
    {f g : Metta.Atom → Option Metta.Atom} :
    ∀ (xs ys : List Metta.Atom),
      xs.mapM f = some ys →
      (∀ z ∈ xs, ∀ w, f z = some w → g z = some w) →
      xs.mapM g = some ys
  | [], _, h, _ => h
  | x :: xs, ys, h, hpt => by
    cases hx : f x with
    | none => simp [List.mapM_cons, hx] at h
    | some xr =>
      cases hxs : xs.mapM f with
      | none => simp [List.mapM_cons, hx, hxs] at h
      | some xsr =>
        have hys : xr :: xsr = ys := by
          simpa [List.mapM_cons, hx, hxs] using h
        have hgx := hpt x List.mem_cons_self xr hx
        have hgxs := mapM_transfer xs xsr hxs
          (fun z hz => hpt z (List.mem_cons_of_mem _ hz))
        rw [← hys]
        simp [List.mapM_cons, hgx, hgxs]

private theorem persist_size_pos (a : Metta.Atom) : 0 < a.size := by
  cases a <;> simp only [Metta.Atom.size] <;> omega

private theorem persist_size_lt_of_mem {a : Metta.Atom} :
    ∀ {l : List Metta.Atom}, a ∈ l →
      a.size < (Metta.Atom.expr l).size
  | x :: xs, h => by
    cases List.mem_cons.mp h with
    | inl h1 =>
      subst h1
      simp only [Metta.Atom.size, List.map_cons, List.sum_cons]
      omega
    | inr h2 =>
      have := persist_size_lt_of_mem h2
      simp only [Metta.Atom.size, List.map_cons, List.sum_cons] at this ⊢
      omega

/-- **Fuel canonicity core.**  A successful bounded resolution also succeeds
— with the same result — at the canonical budget `a.size + remBudget + 1`:
every jump on a successful path strictly repays the budget. -/
private theorem resolveAtomAux_some_at_budget'
    {b : Metta.Bindings} :
    ∀ (fuel : Nat) (visited : List String) (a r : Metta.Atom),
      Metta.Bindings.resolveAtomAux b fuel visited a = some r →
      Metta.Bindings.resolveAtomAux b
          (a.size + remBudget b visited + 1) visited a = some r := by
  intro fuel
  induction fuel with
  | zero =>
    intro visited a r h
    simp [Metta.Bindings.resolveAtomAux] at h
  | succ fuel ih =>
    intro visited a r h
    cases a with
    | sym s =>
      simp only [Metta.Bindings.resolveAtomAux] at h ⊢
      exact h
    | gnd g =>
      simp only [Metta.Bindings.resolveAtomAux] at h ⊢
      exact h
    | expr xs =>
      simp only [Metta.Bindings.resolveAtomAux] at h ⊢
      cases hmap : xs.mapM
          (Metta.Bindings.resolveAtomAux b fuel visited) with
      | none => rw [hmap] at h; cases h
      | some ys =>
        rw [hmap] at h
        have htransfer := mapM_transfer
          (f := Metta.Bindings.resolveAtomAux b fuel visited)
          (g := Metta.Bindings.resolveAtomAux b
            ((Metta.Atom.expr xs).size + remBudget b visited) visited)
          xs ys hmap (by
            intro z hz w hw
            have hcanon := ih visited z w hw
            have hle : z.size + remBudget b visited + 1 ≤
                (Metta.Atom.expr xs).size + remBudget b visited := by
              have := persist_size_lt_of_mem hz
              omega
            obtain ⟨extra, hextra⟩ := Nat.le.dest hle
            rw [← hextra]
            exact leaResolveAtomAux_some_add_fuel extra hcanon)
        rw [htransfer]
        exact h
    | var z =>
      simp only [Metta.Bindings.resolveAtomAux] at h ⊢
      by_cases hguard : ((Metta.Bindings.eqClassOrdered b z).any
          visited.contains) = true
      · rw [if_pos hguard] at h
        cases h
      · rw [if_neg hguard] at h
        rw [if_neg hguard]
        cases hvalues : Metta.Bindings.classValues b z with
        | nil =>
          rw [hvalues] at h
          simpa using h
        | cons v rest =>
          rw [hvalues] at h
          have hguard' : ((Metta.Bindings.eqClassOrdered b z).any
              visited.contains) = false := by
            simpa using hguard
          have hhead : v ∈ Metta.Bindings.classValues b z := by
            rw [hvalues]; exact List.mem_cons_self
          have hjump := remBudget_jump hguard' hhead
          have hinner : ∀ r',
              Metta.Bindings.resolveAtomAux b fuel
                  (Metta.Bindings.eqClassOrdered b z ++ visited) v =
                some r' →
              Metta.Bindings.resolveAtomAux b
                  ((Metta.Atom.var z).size + remBudget b visited)
                  (Metta.Bindings.eqClassOrdered b z ++ visited) v =
                some r' := by
            intro r' hr'
            have hcanon := ih _ _ _ hr'
            have hle : v.size + remBudget b
                  (Metta.Bindings.eqClassOrdered b z ++ visited) + 1 ≤
                (Metta.Atom.var z).size + remBudget b visited := by
              simp only [Metta.Atom.size]
              omega
            obtain ⟨extra, hextra⟩ := Nat.le.dest hle
            rw [← hextra]
            exact leaResolveAtomAux_some_add_fuel extra hcanon
          cases v with
          | var y =>
            by_cases hcontains :
                y ∈ Metta.Bindings.eqClassOrdered b z
            · by_cases hlen :
                  (Metta.Bindings.eqClassOrdered b z).length = 1
              · simp [hcontains, hlen] at h
              · simpa [hcontains, hlen] using h
            · have hrec : Metta.Bindings.resolveAtomAux b fuel
                  (Metta.Bindings.eqClassOrdered b z ++ visited)
                  (Metta.Atom.var y) = some r := by
                simpa [hcontains] using h
              simpa [hcontains] using hinner r hrec
          | sym s =>
            have hrec : Metta.Bindings.resolveAtomAux b fuel
                (Metta.Bindings.eqClassOrdered b z ++ visited)
                (Metta.Atom.sym s) = some r := by
              simpa using h
            simpa using hinner r hrec
          | gnd g =>
            have hrec : Metta.Bindings.resolveAtomAux b fuel
                (Metta.Bindings.eqClassOrdered b z ++ visited)
                (Metta.Atom.gnd g) = some r := by
              simpa using h
            simpa using hinner r hrec
          | expr atoms =>
            have hrec : Metta.Bindings.resolveAtomAux b fuel
                (Metta.Bindings.eqClassOrdered b z ++ visited)
                (Metta.Atom.expr atoms) = some r := by
              simpa using h
            simpa using hinner r hrec

/-- **Fuel canonicity.**  Success at any fuel implies success at the
canonical `resolutionFuel` budget.  Failure at the canonical budget is
therefore always a genuine cyclic dependency, never budget shortfall. -/
theorem resolveAtomAux_some_at_resolutionFuel
    {b : Metta.Bindings} {fuel : Nat} {a r : Metta.Atom}
    (h : Metta.Bindings.resolveAtomAux b fuel [] a = some r) :
    Metta.Bindings.resolveAtomAux b
        (Metta.Bindings.resolutionFuel b a) [] a = some r := by
  have hcanon := resolveAtomAux_some_at_budget' fuel [] a r h
  have hle : a.size + remBudget b [] + 1 ≤
      Metta.Bindings.resolutionFuel b a := by
    unfold Metta.Bindings.resolutionFuel
    have hsum : remBudget b [] ≤
        (b.map Metta.Bindings.relationResolutionFuel).sum := by
      unfold remBudget
      apply List.sum_le_sum
      intro rel _
      cases rel with
      | val x v =>
        simp only [Metta.Bindings.relationResolutionFuel]
        split <;> omega
      | eq _ _ =>
        simp [Metta.Bindings.relationResolutionFuel]
    omega
  obtain ⟨extra, hextra⟩ := Nat.le.dest hle
  rw [← hextra]
  exact leaResolveAtomAux_some_add_fuel extra hcanon

/-! ## Composition: loop persistence for the raw value insertion -/

private theorem lookupVal_isSome_of_mem :
    ∀ {lb : Metta.Bindings} {y : String} {v : Metta.Atom},
      Metta.BindingRel.val y v ∈ lb →
      (Metta.Bindings.lookupVal lb y).isSome = true
  | [], _, _, h => absurd h (List.not_mem_nil)
  | .val z w :: rest, y, v, h => by
    simp only [Metta.Bindings.lookupVal]
    by_cases hyz : (y == z) = true
    · rw [if_pos hyz]; rfl
    · rw [if_neg hyz]
      cases List.mem_cons.mp h with
      | inl heq =>
        cases heq
        exact absurd (by simp) hyz
      | inr htail => exact lookupVal_isSome_of_mem htail
  | .eq _ _ :: rest, y, v, h => by
    simp only [Metta.Bindings.lookupVal]
    cases List.mem_cons.mp h with
    | inl heq => cases heq
    | inr htail => exact lookupVal_isSome_of_mem htail

private theorem mem_vars_cons
    {rel : Metta.BindingRel} {lb : Metta.Bindings} {x : String}
    (h : x ∈ Metta.Bindings.vars lb) :
    x ∈ Metta.Bindings.vars (rel :: lb) := by
  unfold Metta.Bindings.vars at h ⊢
  rw [List.mem_eraseDups] at h ⊢
  rw [List.flatMap_cons]
  exact List.mem_append_right _ h

/-- **Loop persistence, fresh value insertion.**  A loop-free raw value
insertion for a key whose class is valueless certifies a loop-free source:
the direct scan restricts to the sublist, and every recursive resolution
replays in the source and re-canonicalizes to the source's own budget. -/
theorem hasLoop_false_of_addValRaw_fresh
    {source : Metta.Bindings} {key : String} {value : Metta.Atom}
    (hfresh : Metta.Bindings.classValues source key = [])
    (hloop : (Metta.Bindings.addValRaw source key value).hasLoop = false) :
    source.hasLoop = false := by
  have hlookup : Metta.Bindings.lookupVal source key = none := by
    cases hl : Metta.Bindings.lookupVal source key with
    | none => rfl
    | some v =>
      exfalso
      have hmem : v ∈ Metta.Bindings.classValues source key := by
        unfold Metta.Bindings.classValues
        exact List.mem_filterMap.mpr
          ⟨key, self_mem_eqClassOrdered source key, hl⟩
      rw [hfresh] at hmem
      exact absurd hmem (List.not_mem_nil)
  have hremove : Metta.Bindings.removeVal source key = source := by
    unfold Metta.Bindings.removeVal
    apply List.filter_eq_self.mpr
    intro rel hrel
    cases rel with
    | eq _ _ => simp
    | val y v =>
      simp only []
      by_cases hy : y = key
      · subst hy
        have := lookupVal_isSome_of_mem hrel
        rw [hlookup] at this
        cases this
      · simpa using hy
  unfold Metta.Bindings.addValRaw at hloop
  rw [hremove] at hloop
  unfold Metta.Bindings.hasLoop at hloop ⊢
  rw [Bool.or_eq_false_iff] at hloop ⊢
  obtain ⟨hdirect, hrecursive⟩ := hloop
  constructor
  · simp only [List.any_cons, Bool.or_eq_false_iff] at hdirect
    exact hdirect.2
  · rw [List.any_eq_false] at hrecursive ⊢
    intro x hx
    have hx' := mem_vars_cons
      (rel := Metta.BindingRel.val key value) hx
    have hext := hrecursive x hx'
    cases hres : Metta.Bindings.resolveAtomAux
        (Metta.BindingRel.val key value :: source)
        (Metta.Bindings.resolutionFuel
          (Metta.BindingRel.val key value :: source) (Metta.Atom.var x))
        [] (Metta.Atom.var x) with
    | none => rw [hres] at hext; exact absurd rfl hext
    | some r =>
      have hsome := resolveAtomAux_some_of_cons_val_fresh hfresh
        _ _ _ _ hres
      obtain ⟨r', hr'⟩ := Option.isSome_iff_exists.mp hsome
      have hcanon := resolveAtomAux_some_at_resolutionFuel hr'
      simp [hcanon]

/-! ## Invariance and transfer under an equality cons -/

section ConsEq

variable (source : Metta.Bindings) (l r : String)

private theorem lookupVal_cons_eq (z : String) :
    Metta.Bindings.lookupVal (Metta.BindingRel.eq l r :: source) z =
      Metta.Bindings.lookupVal source z := rfl

private theorem leaEqualityEdges_cons_eq :
    leaEqualityEdges (Metta.BindingRel.eq l r :: source) =
      (l, r) :: leaEqualityEdges source := rfl

private theorem edgeGraph_le_cons_eq :
    EqualityClosure.edgeGraph (leaEqualityEdges source) ≤
      EqualityClosure.edgeGraph
        (leaEqualityEdges (Metta.BindingRel.eq l r :: source)) := by
  intro u v huv
  rw [EqualityClosure.edgeGraph_adj_iff] at huv ⊢
  refine ⟨huv.1, ?_⟩
  rw [leaEqualityEdges_cons_eq]
  rcases huv.2 with h | h
  · exact Or.inl (List.mem_cons_of_mem _ h)
  · exact Or.inr (List.mem_cons_of_mem _ h)

private theorem eqClass_mem_mono_cons_eq {z w : String}
    (h : w ∈ Metta.Bindings.eqClass source z) :
    w ∈ Metta.Bindings.eqClass (Metta.BindingRel.eq l r :: source) z := by
  rw [mem_leaEqClass_iff_reachable] at h ⊢
  exact h.mono (edgeGraph_le_cons_eq source l r)

private theorem reachable_cons_eq_untouched {z w : String}
    (hz : ¬ (EqualityClosure.edgeGraph
      (leaEqualityEdges (Metta.BindingRel.eq l r :: source))).Reachable
        z l)
    (h : (EqualityClosure.edgeGraph
      (leaEqualityEdges (Metta.BindingRel.eq l r :: source))).Reachable
        z w) :
    (EqualityClosure.edgeGraph (leaEqualityEdges source)).Reachable z w := by
  suffices key : ∀ (a b : String),
      (EqualityClosure.edgeGraph
        (leaEqualityEdges (Metta.BindingRel.eq l r :: source))).Walk a b →
      ¬ (EqualityClosure.edgeGraph
        (leaEqualityEdges (Metta.BindingRel.eq l r :: source))).Reachable
          a l →
      (EqualityClosure.edgeGraph (leaEqualityEdges source)).Reachable a b by
    exact h.elim fun walk => key z w walk hz
  intro a b walk
  induction walk with
  | nil => intro _; exact .rfl
  | @cons start next finish hadj tail ih =>
    intro hstart
    have hnext : ¬ (EqualityClosure.edgeGraph
        (leaEqualityEdges (Metta.BindingRel.eq l r :: source))).Reachable
          next l :=
      fun hcontra => hstart (hadj.reachable.trans hcontra)
    have hadjSource : (EqualityClosure.edgeGraph
        (leaEqualityEdges source)).Adj start next := by
      have hadjOrig := hadj
      rw [EqualityClosure.edgeGraph_adj_iff] at hadj ⊢
      refine ⟨hadj.1, ?_⟩
      rw [leaEqualityEdges_cons_eq] at hadj
      rcases hadj.2 with h' | h'
      · rcases List.mem_cons.mp h' with heq | hmem
        · exfalso
          have : start = l := congrArg Prod.fst heq
          subst this
          exact hstart .rfl
        · exact Or.inl hmem
      · rcases List.mem_cons.mp h' with heq | hmem
        · exfalso
          have hnextl : next = l := congrArg Prod.fst heq
          subst hnextl
          exact hstart hadjOrig.reachable
        · exact Or.inr hmem
    exact hadjSource.reachable.trans (ih hnext)

private theorem eqVarsInOrder_cons_eq_eq :
    Metta.Bindings.eqVarsInOrder (Metta.BindingRel.eq l r :: source) =
      (let acc := if (Metta.Bindings.eqVarsInOrder source).contains r
          then Metta.Bindings.eqVarsInOrder source
          else Metta.Bindings.eqVarsInOrder source ++ [r];
        if acc.contains l then acc else acc ++ [l]) := by
  show Metta.Bindings.eqVarsInOrder (Metta.BindingRel.eq l r :: source) = _
  unfold Metta.Bindings.eqVarsInOrder
  rw [List.reverse_cons, List.foldl_append]
  rfl

private theorem mem_eqVarsInOrder_cons_eq {v : String}
    (hv : v ∈ Metta.Bindings.eqVarsInOrder source) :
    v ∈ Metta.Bindings.eqVarsInOrder
      (Metta.BindingRel.eq l r :: source) := by
  rw [eqVarsInOrder_cons_eq_eq]
  simp only []
  split <;> split <;>
    first
      | exact hv
      | exact List.mem_append_left _ hv
      | exact List.mem_append_left _ (List.mem_append_left _ hv)

private theorem filter_eqVarsInOrder_cons_eq {p : String → Bool}
    (hl : p l = false) (hr : p r = false) :
    (Metta.Bindings.eqVarsInOrder
        (Metta.BindingRel.eq l r :: source)).filter p =
      (Metta.Bindings.eqVarsInOrder source).filter p := by
  rw [eqVarsInOrder_cons_eq_eq]
  simp only []
  split <;> split <;> simp [List.filter_append, hl, hr]

private theorem mem_eqClassOrdered_cons_eq {z y : String}
    (hy : y ∈ Metta.Bindings.eqClassOrdered source z) :
    y ∈ Metta.Bindings.eqClassOrdered
      (Metta.BindingRel.eq l r :: source) z := by
  rcases mem_eqClassOrdered_cases' hy with heq | hclass
  · subst heq
    exact self_mem_eqClassOrdered _ _
  · by_cases hyz : y = z
    · subst hyz
      exact self_mem_eqClassOrdered _ _
    · have hyorder : y ∈ Metta.Bindings.eqVarsInOrder source :=
        mem_eqVarsInOrder_of_reachable_ne hyz
          (mem_leaEqClass_iff_reachable.mp hclass).symm
      have hyorderE : y ∈ Metta.Bindings.eqVarsInOrder
          (Metta.BindingRel.eq l r :: source) :=
        mem_eqVarsInOrder_cons_eq source l r hyorder
      have hyclassE : y ∈ Metta.Bindings.eqClass
          (Metta.BindingRel.eq l r :: source) z :=
        eqClass_mem_mono_cons_eq source l r hclass
      have hyf : y ∈ (Metta.Bindings.eqVarsInOrder
          (Metta.BindingRel.eq l r :: source)).filter
          (fun w => (Metta.Bindings.eqClass
            (Metta.BindingRel.eq l r :: source) z).contains w) :=
        List.mem_filter.mpr ⟨hyorderE, by simpa using hyclassE⟩
      unfold Metta.Bindings.eqClassOrdered
      cases hfilter : (Metta.Bindings.eqVarsInOrder
          (Metta.BindingRel.eq l r :: source)).filter
          (fun w => (Metta.Bindings.eqClass
            (Metta.BindingRel.eq l r :: source) z).contains w) with
      | nil =>
        rw [hfilter] at hyf
        exact absurd hyf (List.not_mem_nil)
      | cons c cs =>
        rw [hfilter] at hyf
        try rw [hfilter]
        exact hyf

private theorem mem_classValues_cons_eq {z : String} {v : Metta.Atom}
    (hv : v ∈ Metta.Bindings.classValues source z) :
    v ∈ Metta.Bindings.classValues
      (Metta.BindingRel.eq l r :: source) z := by
  unfold Metta.Bindings.classValues at hv ⊢
  obtain ⟨y, hy, hlookup⟩ := List.mem_filterMap.mp hv
  exact List.mem_filterMap.mpr
    ⟨y, mem_eqClassOrdered_cons_eq source l r hy,
      by rw [lookupVal_cons_eq]; exact hlookup⟩

private theorem eqClassOrdered_cons_eq_untouched {z : String}
    (hlr : l ≠ r)
    (htouched : l ∉ Metta.Bindings.eqClass
      (Metta.BindingRel.eq l r :: source) z) :
    Metta.Bindings.eqClassOrdered (Metta.BindingRel.eq l r :: source) z =
      Metta.Bindings.eqClassOrdered source z := by
  have hzl : ¬ (EqualityClosure.edgeGraph
      (leaEqualityEdges (Metta.BindingRel.eq l r :: source))).Reachable
        z l := fun hcontra =>
    htouched (mem_leaEqClass_iff_reachable.mpr hcontra)
  have hadjrl : (EqualityClosure.edgeGraph
      (leaEqualityEdges (Metta.BindingRel.eq l r :: source))).Adj r l := by
    rw [EqualityClosure.edgeGraph_adj_iff]
    exact ⟨fun hcontra => hlr hcontra.symm, by
      rw [leaEqualityEdges_cons_eq]
      exact Or.inr List.mem_cons_self⟩
  have hrtouched : r ∉ Metta.Bindings.eqClass
      (Metta.BindingRel.eq l r :: source) z := by
    intro hcontra
    exact hzl ((mem_leaEqClass_iff_reachable.mp hcontra).trans
      hadjrl.reachable)
  have hlcontains : ((Metta.Bindings.eqClass
      (Metta.BindingRel.eq l r :: source) z).contains l) = false := by
    simpa using htouched
  have hrcontains : ((Metta.Bindings.eqClass
      (Metta.BindingRel.eq l r :: source) z).contains r) = false := by
    simpa using hrtouched
  unfold Metta.Bindings.eqClassOrdered
  rw [filter_eqVarsInOrder_cons_eq source l r hlcontains hrcontains]
  have hpred : (Metta.Bindings.eqVarsInOrder source).filter
      (fun w => (Metta.Bindings.eqClass
        (Metta.BindingRel.eq l r :: source) z).contains w) =
      (Metta.Bindings.eqVarsInOrder source).filter
        (fun w => (Metta.Bindings.eqClass source z).contains w) := by
    apply List.filter_congr
    intro w _
    by_cases hw : w ∈ Metta.Bindings.eqClass source z
    · have hwE : w ∈ Metta.Bindings.eqClass
          (Metta.BindingRel.eq l r :: source) z :=
        eqClass_mem_mono_cons_eq source l r hw
      simp [hw, hwE]
    · have hwE : w ∉ Metta.Bindings.eqClass
          (Metta.BindingRel.eq l r :: source) z := by
        intro hcontra
        apply hw
        rw [mem_leaEqClass_iff_reachable]
        exact reachable_cons_eq_untouched source l r hzl
          (mem_leaEqClass_iff_reachable.mp hcontra)
      simp [hw, hwE]
  rw [hpred]

private theorem classValues_cons_eq_untouched {z : String}
    (hlr : l ≠ r)
    (htouched : l ∉ Metta.Bindings.eqClass
      (Metta.BindingRel.eq l r :: source) z) :
    Metta.Bindings.classValues (Metta.BindingRel.eq l r :: source) z =
      Metta.Bindings.classValues source z := by
  unfold Metta.Bindings.classValues
  rw [eqClassOrdered_cons_eq_untouched source l r hlr htouched]
  apply List.filterMap_congr
  intro w _
  rw [lookupVal_cons_eq]

private theorem classValues_congr_of_ordered_eq
    {lb : Metta.Bindings} {a b : String}
    (h : Metta.Bindings.eqClassOrdered lb a =
      Metta.Bindings.eqClassOrdered lb b) :
    Metta.Bindings.classValues lb a = Metta.Bindings.classValues lb b := by
  unfold Metta.Bindings.classValues
  rw [h]

private theorem classValues_head_nonvar
    {lb : Metta.Bindings}
    (hnonvar : LeaAssignmentsNonVariable lb) {z : String}
    {v : Metta.Atom} (hv : v ∈ Metta.Bindings.classValues lb z) :
    ∀ y, v ≠ Metta.Atom.var y := by
  intro y hcontra
  subst hcontra
  unfold Metta.Bindings.classValues at hv
  obtain ⟨w, _, hlookup⟩ := List.mem_filterMap.mp hv
  exact hnonvar w y (lookupVal_mem' hlookup)

end ConsEq

/-! ## Success replay: extended equality record to source -/

private theorem resolveAtomAux_some_of_cons_eq
    {source : Metta.Bindings} {l r : String}
    (hlr : l ≠ r)
    (hnonvar : LeaAssignmentsNonVariable source)
    (hsame : ∀ v ∈ Metta.Bindings.classValues
        (Metta.BindingRel.eq l r :: source) l,
      ∀ w ∈ Metta.Bindings.classValues
        (Metta.BindingRel.eq l r :: source) l, v = w) :
    ∀ (fuel : Nat) (visitedE visitedS : List String) (a res : Metta.Atom),
      (∀ s ∈ visitedS, s ∈ visitedE) →
      Metta.Bindings.resolveAtomAux
          (Metta.BindingRel.eq l r :: source) fuel visitedE a = some res →
      (Metta.Bindings.resolveAtomAux source fuel visitedS a).isSome =
        true := by
  intro fuel
  induction fuel with
  | zero =>
    intro _ _ _ _ _ h
    simp [Metta.Bindings.resolveAtomAux] at h
  | succ fuel ih =>
    intro visitedE visitedS a res hvis h
    cases a with
    | sym s => simp [Metta.Bindings.resolveAtomAux]
    | gnd g => simp [Metta.Bindings.resolveAtomAux]
    | expr xs =>
      simp only [Metta.Bindings.resolveAtomAux] at h ⊢
      cases hmap : xs.mapM (Metta.Bindings.resolveAtomAux
          (Metta.BindingRel.eq l r :: source) fuel visitedE) with
      | none => rw [hmap] at h; cases h
      | some ys =>
        obtain ⟨ws, hws⟩ := mapM_some_of_pointwise xs ys hmap
          (fun z _ w hw => ih visitedE visitedS z w hvis hw)
        rw [hws]
        simp
    | var z =>
      simp only [Metta.Bindings.resolveAtomAux] at h ⊢
      by_cases hgS : ((Metta.Bindings.eqClassOrdered source z).any
          visitedS.contains) = true
      · exfalso
        rw [List.any_eq_true] at hgS
        obtain ⟨w, hw, hwv⟩ := hgS
        have hgE : ((Metta.Bindings.eqClassOrdered
            (Metta.BindingRel.eq l r :: source) z).any
            visitedE.contains) = true := by
          rw [List.any_eq_true]
          refine ⟨w, mem_eqClassOrdered_cons_eq source l r hw, ?_⟩
          have hwS : w ∈ visitedS := by simpa using hwv
          simpa using hvis w hwS
        rw [if_pos hgE] at h
        cases h
      · rw [if_neg hgS]
        by_cases hgE : ((Metta.Bindings.eqClassOrdered
            (Metta.BindingRel.eq l r :: source) z).any
            visitedE.contains) = true
        · rw [if_pos hgE] at h
          cases h
        · rw [if_neg hgE] at h
          have hvisJump : ∀ s ∈ Metta.Bindings.eqClassOrdered source z ++
              visitedS, s ∈ Metta.Bindings.eqClassOrdered
                (Metta.BindingRel.eq l r :: source) z ++ visitedE := by
            intro s hs
            rcases List.mem_append.mp hs with hs | hs
            · exact List.mem_append_left _
                (mem_eqClassOrdered_cons_eq source l r hs)
            · exact List.mem_append_right _ (hvis s hs)
          cases hvaluesS : Metta.Bindings.classValues source z with
          | nil => simp
          | cons v rest =>
            have hvmem : v ∈ Metta.Bindings.classValues source z := by
              rw [hvaluesS]; exact List.mem_cons_self
            have hvnonvar := classValues_head_nonvar hnonvar hvmem
            have hjump : Metta.Bindings.resolveAtomAux
                (Metta.BindingRel.eq l r :: source) fuel
                (Metta.Bindings.eqClassOrdered
                  (Metta.BindingRel.eq l r :: source) z ++ visitedE) v =
                some res := by
              by_cases htouched : l ∈ Metta.Bindings.eqClass
                  (Metta.BindingRel.eq l r :: source) z
              · have hordered : Metta.Bindings.eqClassOrdered
                    (Metta.BindingRel.eq l r :: source) l =
                    Metta.Bindings.eqClassOrdered
                      (Metta.BindingRel.eq l r :: source) z :=
                  eqClassOrdered_congr_of_mem htouched
                have hclassvals : Metta.Bindings.classValues
                    (Metta.BindingRel.eq l r :: source) l =
                    Metta.Bindings.classValues
                      (Metta.BindingRel.eq l r :: source) z :=
                  classValues_congr_of_ordered_eq hordered
                have hvE : v ∈ Metta.Bindings.classValues
                    (Metta.BindingRel.eq l r :: source) z :=
                  mem_classValues_cons_eq source l r hvmem
                cases hvaluesE : Metta.Bindings.classValues
                    (Metta.BindingRel.eq l r :: source) z with
                | nil =>
                  rw [hvaluesE] at hvE
                  exact absurd hvE (List.not_mem_nil)
                | cons vE restE =>
                  have hvEhead : vE ∈ Metta.Bindings.classValues
                      (Metta.BindingRel.eq l r :: source) z := by
                    rw [hvaluesE]; exact List.mem_cons_self
                  have hveq : v = vE := by
                    apply hsame
                    · rw [hclassvals]; exact hvE
                    · rw [hclassvals]; exact hvEhead
                  rw [hvaluesE] at h
                  subst hveq
                  cases v with
                  | var y => exact absurd rfl (hvnonvar y)
                  | sym s => simpa using h
                  | gnd g => simpa using h
                  | expr atoms => simpa using h
              · have hclassvals := classValues_cons_eq_untouched
                  source l r hlr htouched
                rw [hclassvals, hvaluesS] at h
                cases v with
                | var y => exact absurd rfl (hvnonvar y)
                | sym s => simpa using h
                | gnd g => simpa using h
                | expr atoms => simpa using h
            cases v with
            | var y => exact absurd rfl (hvnonvar y)
            | sym s => simpa using ih _ _ _ _ hvisJump hjump
            | gnd g => simpa using ih _ _ _ _ hvisJump hjump
            | expr atoms => simpa using ih _ _ _ _ hvisJump hjump

/-! ## Pairwise-equal class values from an empty unifier -/

private theorem applyClassSolution_id :
    ∀ a : Metta.Atom,
      applyClassSolution (fun x => Metta.Atom.var x) a = a := by
  suffices key : ∀ (n : Nat) (a : Metta.Atom), a.size ≤ n →
      applyClassSolution (fun x => Metta.Atom.var x) a = a by
    exact fun a => key a.size a le_rfl
  intro n
  induction n with
  | zero =>
    intro a hsize
    exact absurd hsize (by have := persist_size_pos a; omega)
  | succ n ihn =>
    intro a hsize
    cases a with
    | sym s => simp [applyClassSolution]
    | gnd g => simp [applyClassSolution]
    | var v => simp [applyClassSolution]
    | expr atoms =>
      simp only [applyClassSolution, Metta.Atom.expr.injEq]
      have : atoms.map (applyClassSolution (fun x => Metta.Atom.var x)) =
          atoms.map id := by
        apply List.map_congr_left
        intro child hchild
        have := persist_size_lt_of_mem hchild
        exact ihn child (by omega)
      rw [this, List.map_id]

private theorem classValues_pairwise_of_unifyValues_nil
    {lb : Metta.Bindings} {z : String}
    (hnoFloat : ∀ v ∈ Metta.Bindings.classValues lb z,
      MettaAtomNoFloat v)
    (hunify : Metta.Bindings.unifyValues
      (Metta.Bindings.classValues lb z) = some []) :
    ∀ v ∈ Metta.Bindings.classValues lb z,
      ∀ w ∈ Metta.Bindings.classValues lb z, v = w := by
  have hiff := unifyValues_solution_iff
    (fun x => Metta.Atom.var x) hnoFloat hunify
  have hsat : MettaEquationsSatisfied (fun x => Metta.Atom.var x)
      (mettaClassValueEquations (Metta.Bindings.classValues lb z)) :=
    hiff.mp (fun c hc => absurd hc (List.not_mem_nil))
  cases hvals : Metta.Bindings.classValues lb z with
  | nil =>
    intro v hv
    exact absurd hv (List.not_mem_nil)
  | cons first rest =>
    rw [hvals] at hsat
    have hhead : ∀ v ∈ first :: rest, v = first := by
      intro v hv
      rcases List.mem_cons.mp hv with heq | hmem
      · exact heq
      · have hpair : MettaEquationSatisfied (fun x => Metta.Atom.var x)
            (first, v) := by
          apply hsat
          simp only [mettaClassValueEquations]
          exact List.mem_map.mpr ⟨v, hmem, rfl⟩
        have := hpair
        simp only [MettaEquationSatisfied, applyClassSolution_id] at this
        exact this.symm
    intro v hv w hw
    rw [hhead v hv, hhead w hw]

/-! ## Composition: loop persistence for the raw equality insertion -/

/-- **Loop persistence, raw equality insertion with an empty class
unifier.**  A loop-free `addEqRaw source left right` whose joined class
carries an empty value unifier certifies a loop-free `source`. -/
theorem hasLoop_false_of_addEqRaw_emptyUnifier
    {source : Metta.Bindings} {left right : String}
    (hnonvar : LeaAssignmentsNonVariable source)
    (hnoFloat : LeaBindingsNoFloat source)
    (hunify : Metta.Bindings.unifyValues
      (Metta.Bindings.classValues
        (Metta.Bindings.addEqRaw source left right) left) = some [])
    (hloop : (Metta.Bindings.addEqRaw source left right).hasLoop = false) :
    source.hasLoop = false := by
  by_cases hlr : (left == right) = true
  · unfold Metta.Bindings.addEqRaw at hloop
    rw [if_pos hlr] at hloop
    exact hloop
  · have hlr' : left ≠ right := by simpa using hlr
    have hext : Metta.Bindings.addEqRaw source left right =
        Metta.BindingRel.eq left right :: source := by
      unfold Metta.Bindings.addEqRaw
      rw [if_neg hlr]
    rw [hext] at hloop hunify
    have hnoFloatVals : ∀ v ∈ Metta.Bindings.classValues
        (Metta.BindingRel.eq left right :: source) left,
        MettaAtomNoFloat v := by
      intro v hv
      unfold Metta.Bindings.classValues at hv
      obtain ⟨y, _, hlookup⟩ := List.mem_filterMap.mp hv
      have hval := lookupVal_mem' hlookup
      rcases List.mem_cons.mp hval with heq | hmem
      · cases heq
      · exact hnoFloat y v hmem
    have hsame := classValues_pairwise_of_unifyValues_nil
      hnoFloatVals hunify
    unfold Metta.Bindings.hasLoop at hloop ⊢
    rw [Bool.or_eq_false_iff] at hloop ⊢
    obtain ⟨hdirect, hrecursive⟩ := hloop
    constructor
    · simp only [List.any_cons, Bool.or_eq_false_iff] at hdirect
      exact hdirect.2
    · rw [List.any_eq_false] at hrecursive ⊢
      intro x hx
      have hx' := mem_vars_cons
        (rel := Metta.BindingRel.eq left right) hx
      have hext' := hrecursive x hx'
      cases hres : Metta.Bindings.resolveAtomAux
          (Metta.BindingRel.eq left right :: source)
          (Metta.Bindings.resolutionFuel
            (Metta.BindingRel.eq left right :: source) (Metta.Atom.var x))
          [] (Metta.Atom.var x) with
      | none => rw [hres] at hext'; exact absurd rfl hext'
      | some res =>
        have hsome := resolveAtomAux_some_of_cons_eq hlr' hnonvar hsame
          _ _ [] _ _ (fun s hs => hs) hres
        obtain ⟨res', hres'⟩ := Option.isSome_iff_exists.mp hsome
        have hcanon := resolveAtomAux_some_at_resolutionFuel hres'
        simp [hcanon]

end Mettapedia.Languages.MeTTa.HE.LeaTTaBridge
