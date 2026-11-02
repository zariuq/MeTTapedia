import Mettapedia.InformationTheory.SymmetryKeys.Orbits

/-!
# Keys computed bottom-up by sorting the arguments of declared heads

Tree canonization (Aho, Hopcroft and Ullman): arrange a term bottom-up, sorting the arguments of
every declared head by the keys of the arguments, already arranged (`arrangeBy key`).

* **Names as data** (`pcanon_eq_iff_arr`).  When the key of an argument tells any two terms apart,
  the arranged term is a canonical form for "equal up to the argument order of declared heads":
  `arrangeBy key s = arrangeBy key t` iff `Arr s t`.  Variables are compared by name.  This is the
  bag equality a kernel needs for `@(A|B) = @(B|A)` at every depth.
* **Renaming too: the easy class** (`sortKey_eq_iff_orbit`).  Sort by the variant keys of the
  arguments and number the variables of the arranged term by first occurrence (`sortKey`).
  - For every term, equal keys put two terms in one orbit (`orbit_of_sortKey_eq`): a wrong merge is
    impossible.
  - For a term of the easy class (`Priv`), the converse holds too.  In that class the arguments of
    a declared head share no variable, and a variable under a declared head occurs in no sibling of
    the argument it sits in.
  - Example: `(f $x (bag (g $y) (h $z)))` is in the class; `(k (bag (g $x) (g $y)) $y)` is not, and
    there the converse fails: `(k (bag (g $y) (g $x)) $y)` is in the same orbit with another key
    (`TreeCanonControls`).
-/

namespace Mettapedia.InformationTheory.SymmetryKeys

open Mettapedia.InformationTheory.RelationStoreVariantKeys

namespace ETm

variable {A V : Type*} (comm : A → Prop) [DecidablePred comm]

/-! ### Lists -/

theorem forall₂_eq_of_map_eq {α β : Type*} (g : α → β) :
    ∀ {l m : List α}, l.map g = m.map g → List.Forall₂ (fun a b => g a = g b) l m
  | [], [], _ => .nil
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | _ :: _, _ :: _, h => by
      simp only [List.map_cons, List.cons.injEq] at h
      exact .cons h.1 (forall₂_eq_of_map_eq g h.2)

theorem exists_of_mem_forall₂_right {α β : Type*} {Q : α → β → Prop} :
    ∀ {l : List α} {m : List β}, List.Forall₂ Q l m →
      ∀ {b}, b ∈ m → ∃ a ∈ l, Q a b
  | _, _, .nil, _, hb => by simp at hb
  | a :: _, _ :: _, .cons hab hrest, _, hb => by
      rcases List.mem_cons.mp hb with rfl | hb
      · exact ⟨a, List.mem_cons_self, hab⟩
      · obtain ⟨a', ha', hq⟩ := exists_of_mem_forall₂_right hrest hb
        exact ⟨a', List.mem_cons_of_mem _ ha', hq⟩

theorem forall₂_swap' {α β : Type*} {R : α → β → Prop} :
    ∀ {l : List α} {m : List β}, List.Forall₂ R l m → List.Forall₂ (fun b a => R a b) m l
  | _, _, .nil => .nil
  | _, _, .cons h hrest => .cons h (forall₂_swap' hrest)

theorem forall₂_and' {α β : Type*} {R Q : α → β → Prop} :
    ∀ {l : List α} {m : List β}, List.Forall₂ R l m → List.Forall₂ Q l m →
      List.Forall₂ (fun a b => R a b ∧ Q a b) l m
  | _, _, .nil, _ => .nil
  | _, _, .cons h hrest, .cons h' hrest' => .cons ⟨h, h'⟩ (forall₂_and' hrest hrest')

theorem pairwise_of_forall₂ {α β : Type*} {R : α → α → Prop} {R' : β → β → Prop}
    {Q : α → β → Prop} (hQ : ∀ a b a' b', Q a a' → Q b b' → R a b → R' a' b') :
    ∀ {l : List α} {m : List β}, List.Forall₂ Q l m → l.Pairwise R → m.Pairwise R'
  | _, _, .nil, _ => .nil
  | _ :: _, _ :: _, .cons hab hrest, hp => by
      rw [List.pairwise_cons] at hp ⊢
      refine ⟨fun b' hb' => ?_, pairwise_of_forall₂ hQ hrest hp.2⟩
      obtain ⟨b, hb, hq⟩ := exists_of_mem_forall₂_right hrest hb'
      exact hQ _ _ _ _ hab hq (hp.1 b hb)

theorem orderedInsert_map {α β : Type*} (r : α → α → Prop)
    (r' : β → β → Prop) [DecidableRel r]
    [DecidableRel r'] (g : α → β) (hr : ∀ a b, r' (g a) (g b) ↔ r a b) (a : α) :
    ∀ l : List α, (l.map g).orderedInsert r' (g a) = (l.orderedInsert r a).map g
  | [] => rfl
  | b :: l => by
      simp only [List.map_cons, List.orderedInsert_cons, hr]
      split_ifs
      · rfl
      · simp [orderedInsert_map r r' g hr a l]

theorem insertionSort_map {α β : Type*} (r : α → α → Prop)
    (r' : β → β → Prop) [DecidableRel r]
    [DecidableRel r'] (g : α → β) (hr : ∀ a b, r' (g a) (g b) ↔ r a b) :
    ∀ l : List α, (l.map g).insertionSort r' = (l.insertionSort r).map g
  | [] => rfl
  | a :: l => by
      simp only [List.map_cons, List.insertionSort_cons]
      rw [insertionSort_map r r' g hr l, orderedInsert_map r r' g hr a]

/-! ### Variables under arrangement -/

theorem flatten_perm_of_forall₂ {α β : Type*} {f : α → List β} :
    ∀ {l m : List α}, List.Forall₂ (fun a b => (f a).Perm (f b)) l m →
      ((l.map f).flatten).Perm ((m.map f).flatten)
  | _, _, .nil => .refl _
  | _, _, .cons h hrest => by
      simp only [List.map_cons, List.flatten_cons]
      exact h.append (flatten_perm_of_forall₂ hrest)

mutual

/-- The variables that occur under a declared head, one entry per occurrence. -/
def hidden : ETm A V → List V
  | .atom _ => []
  | .var _ => []
  | .node h args => if comm h then varsArgs args else hiddenArgs args

/-- `hidden` on each argument. -/
def hiddenArgs : List (ETm A V) → List V
  | [] => []
  | c :: cs => hidden c ++ hiddenArgs cs

end

theorem hiddenArgs_eq (l : List (ETm A V)) : hiddenArgs comm l = (l.map (hidden comm)).flatten := by
  induction l with
  | nil => rfl
  | cons c cs ih => simp [hiddenArgs, ih]

theorem hidden_node (h : A) (args : List (ETm A V)) :
    hidden comm (.node h args) =
      if comm h then (args.map vars).flatten else (args.map (hidden comm)).flatten := by
  simp only [hidden, varsArgs_eq, hiddenArgs_eq]

omit [DecidablePred comm] in
mutual

theorem vars_perm_of_arr : ∀ (s u : ETm A V), Arr comm s u → s.vars.Perm u.vars
  | .atom _, _, h => by
      rw [arr_atom] at h
      subst h
      exact .refl _
  | .var _, _, h => by
      rw [arr_var] at h
      subst h
      exact .refl _
  | .node h args, _, hs => by
      obtain ⟨m, a', rfl, f, p, e⟩ := (arr_node comm).mp hs
      simp only [vars_node]
      have h1 := flatten_perm_of_forall₂ (vars_perm_of_arr_args args m f)
      by_cases hc : comm h
      · exact h1.trans (((p hc).map vars).flatten)
      · rw [← e hc]
        exact h1

theorem vars_perm_of_arr_args : ∀ (l m : List (ETm A V)), List.Forall₂ (Arr comm) l m →
    List.Forall₂ (fun a b => a.vars.Perm b.vars) l m
  | [], _, h => by
      cases h
      exact .nil
  | c :: cs, _, h => by
      cases h with
      | cons hcd hrest =>
          exact .cons (vars_perm_of_arr c _ hcd) (vars_perm_of_arr_args cs _ hrest)

end

mutual

theorem hidden_perm_of_arr : ∀ (s u : ETm A V), Arr comm s u →
    (hidden comm s).Perm (hidden comm u)
  | .atom _, _, h => by
      rw [arr_atom] at h
      subst h
      exact .refl _
  | .var _, _, h => by
      rw [arr_var] at h
      subst h
      exact .refl _
  | .node h args, _, hs => by
      obtain ⟨m, a', rfl, f, p, e⟩ := (arr_node comm).mp hs
      rw [hidden_node, hidden_node]
      by_cases hc : comm h
      · rw [if_pos hc, if_pos hc]
        have h1 := flatten_perm_of_forall₂ (vars_perm_of_arr_args comm args m f)
        exact h1.trans (((p hc).map vars).flatten)
      · rw [if_neg hc, if_neg hc, ← e hc]
        exact flatten_perm_of_forall₂ (hidden_perm_of_arr_args args m f)

theorem hidden_perm_of_arr_args : ∀ (l m : List (ETm A V)), List.Forall₂ (Arr comm) l m →
    List.Forall₂ (fun a b => (hidden comm a).Perm (hidden comm b)) l m
  | [], _, h => by
      cases h
      exact .nil
  | c :: cs, _, h => by
      cases h with
      | cons hcd hrest =>
          exact .cons (hidden_perm_of_arr c _ hcd) (hidden_perm_of_arr_args cs _ hrest)

end

/-! ### Arranging by a key -/

section Arrange

variable {K : Type*} [LinearOrder K] (key : ETm A V → K)

/-- Compare two terms by their keys. -/
def keyLE (c d : ETm A V) : Prop := key c ≤ key d

instance : DecidableRel (keyLE key) := fun c d => inferInstanceAs (Decidable (key c ≤ key d))

theorem keyLE_total : Std.Total (keyLE key) := ⟨fun a b => le_total (key a) (key b)⟩

theorem keyLE_trans : IsTrans (ETm A V) (keyLE key) :=
  ⟨fun _ _ _ hab hbc => le_trans (α := K) hab hbc⟩

theorem pairwise_sort (l : List (ETm A V)) : (l.insertionSort (keyLE key)).Pairwise (keyLE key) :=
  haveI := keyLE_total key
  haveI := keyLE_trans key
  List.pairwise_insertionSort (keyLE key) l

mutual

/-- Arrange bottom-up: the arguments of each declared head, arranged first, are sorted by their
keys. -/
def arrangeBy : ETm A V → ETm A V
  | .atom a => .atom a
  | .var v => .var v
  | .node h args =>
      .node h (if comm h then (arrangeByArgs args).insertionSort (keyLE key)
        else arrangeByArgs args)

/-- `arrangeBy` on each argument. -/
def arrangeByArgs : List (ETm A V) → List (ETm A V)
  | [] => []
  | c :: cs => arrangeBy c :: arrangeByArgs cs

end

theorem arrangeByArgs_eq (l : List (ETm A V)) :
    arrangeByArgs comm key l = l.map (arrangeBy comm key) := by
  induction l with
  | nil => rfl
  | cons c cs ih => simp [arrangeByArgs, ih]

theorem arrangeBy_node (h : A) (args : List (ETm A V)) :
    arrangeBy comm key (.node h args) = .node h (if comm h then
      (args.map (arrangeBy comm key)).insertionSort (keyLE key)
      else args.map (arrangeBy comm key)) := by
  simp only [arrangeBy, arrangeByArgs_eq]

/-- **The arranged term is an arrangement.** -/
theorem arr_arrangeBy (t : ETm A V) : Arr comm t (arrangeBy comm key t) := by
  induction t using ETm.rec (motive_2 := fun l => List.Forall₂ (Arr comm) l
      (l.map (arrangeBy comm key))) with
  | atom a => simp [arrangeBy]
  | var v => simp [arrangeBy]
  | node h args ih =>
      rw [arrangeBy_node, arr_node]
      by_cases hc : comm h
      · rw [if_pos hc]
        exact ⟨_, _, rfl, ih, fun _ => (List.perm_insertionSort _ _).symm,
          fun h' => absurd hc h'⟩
      · rw [if_neg hc]
        exact ⟨_, _, rfl, ih, fun h' => absurd h' hc, fun _ => rfl⟩
  | nil => exact .nil
  | cons c cs hc hcs => exact .cons hc hcs

end Arrange

/-! ### Names as data: the positional canonical form -/

section Positional

variable {K : Type*} [LinearOrder K] (key : ETm A V → K)

theorem keyLE_antisymm (hkey : Function.Injective key) : Std.Antisymm (keyLE key) :=
  ⟨fun _ _ hab hba => hkey (le_antisymm (α := K) hab hba)⟩

mutual

theorem arrangeBy_eq_of_arr (hkey : Function.Injective key) :
    ∀ (s t : ETm A V), Arr comm s t → arrangeBy comm key s = arrangeBy comm key t
  | .atom _, _, h => by
      rw [arr_atom] at h
      rw [h]
  | .var _, _, h => by
      rw [arr_var] at h
      rw [h]
  | .node h args, _, hs => by
      obtain ⟨m, a', rfl, f, p, e⟩ := (arr_node comm).mp hs
      have hm : args.map (arrangeBy comm key) = m.map (arrangeBy comm key) :=
        arrangeBy_eq_of_arr_args hkey args m f
      rw [arrangeBy_node, arrangeBy_node, hm]
      by_cases hc : comm h
      · rw [if_pos hc, if_pos hc]
        have := keyLE_antisymm key hkey
        congr 1
        exact List.Perm.eq_of_pairwise' (pairwise_sort key _) (pairwise_sort key _)
          (((List.perm_insertionSort _ _).trans ((p hc).map _)).trans
            (List.perm_insertionSort _ _).symm)
      · rw [if_neg hc, if_neg hc, e hc]

theorem arrangeBy_eq_of_arr_args (hkey : Function.Injective key) :
    ∀ (l m : List (ETm A V)), List.Forall₂ (Arr comm) l m →
      l.map (arrangeBy comm key) = m.map (arrangeBy comm key)
  | [], _, h => by
      cases h
      rfl
  | c :: cs, _, h => by
      cases h with
      | cons hcd hrest =>
          simp only [List.map_cons]
          rw [arrangeBy_eq_of_arr hkey c _ hcd, arrangeBy_eq_of_arr_args hkey cs _ hrest]

end

/-- **Tree canonization with names as data**: for a key that tells terms apart, two terms have one
arranged form exactly when each is an arrangement of the other. -/
theorem pcanon_eq_iff_arr (hkey : Function.Injective key) {s t : ETm A V} :
    arrangeBy comm key s = arrangeBy comm key t ↔ Arr comm s t := by
  constructor
  · intro h
    have hs := arr_arrangeBy comm key s
    have ht := arr_arrangeBy comm key t
    rw [h] at hs
    exact arr_trans comm _ _ _ hs (arr_symm comm _ _ ht)
  · exact arrangeBy_eq_of_arr comm key hkey s t

end Positional

/-! ### Renaming too: the easy class -/

mutual

/-- **The easy class.**  At a declared head, no variable occurs in two arguments; at any other head,
a variable that occurs under a declared head inside one argument occurs in no other argument.  So
every variable under a declared head occurs only inside the one argument it sits in. -/
def Priv : ETm A V → Prop
  | .atom _ => True
  | .var _ => True
  | .node h args => PrivArgs args ∧
      (comm h → args.Pairwise fun c d => ∀ v ∈ c.vars, v ∉ d.vars) ∧
      (¬ comm h → args.Pairwise fun c d =>
        (∀ v ∈ hidden comm c, v ∉ d.vars) ∧ (∀ v ∈ hidden comm d, v ∉ c.vars))

/-- `Priv` on each argument. -/
def PrivArgs : List (ETm A V) → Prop
  | [] => True
  | c :: cs => Priv c ∧ PrivArgs cs

end

theorem privArgs_iff : ∀ l : List (ETm A V), PrivArgs comm l ↔ ∀ c ∈ l, Priv comm c
  | [] => by simp [PrivArgs]
  | c :: cs => by simp [PrivArgs, privArgs_iff cs]

theorem priv_node {h : A} {args : List (ETm A V)} :
    Priv comm (.node h args) ↔ (∀ c ∈ args, Priv comm c) ∧
      (comm h → args.Pairwise fun c d => ∀ v ∈ c.vars, v ∉ d.vars) ∧
      (¬ comm h → args.Pairwise fun c d =>
        (∀ v ∈ hidden comm c, v ∉ d.vars) ∧ (∀ v ∈ hidden comm d, v ∉ c.vars)) := by
  simp only [Priv, privArgs_iff]

section Glue

variable [DecidableEq V]

/-- **Renamings with separate supports glue into one.**  Each argument `c` is carried to its
partner by a renaming that moves only variables of `S c`; a set `S c` meets no other argument.  Then
one renaming carries every argument to its partner and moves only variables of the sets. -/
theorem glue (S : ETm A V → List V) :
    ∀ (l m : List (ETm A V)),
    List.Forall₂ (fun c d => ∃ f : V → V, c.rename f = d ∧
      ∀ v ∈ c.vars, v ∉ S c → f v = v) l m →
    l.Pairwise (fun c c' => (∀ v ∈ c'.vars, v ∉ S c) ∧ (∀ v ∈ c.vars, v ∉ S c')) →
    ∃ F : V → V, l.map (rename F) = m ∧ ∀ v, (∀ c ∈ l, v ∉ S c) → F v = v
  | [], _, h, _ => by
      cases h
      exact ⟨id, rfl, fun _ _ => rfl⟩
  | c :: cs, _, h, hp => by
      cases h with
      | cons hcd hrest =>
          obtain ⟨f, hf, hfix⟩ := hcd
          rw [List.pairwise_cons] at hp
          obtain ⟨F', hF', hfix'⟩ := glue S cs _ hrest hp.2
          refine ⟨fun v => if v ∈ S c then f v else F' v, ?_, ?_⟩
          · simp only [List.map_cons]
            congr 1
            · rw [← hf]
              apply rename_congr
              intro v hv
              by_cases hvS : v ∈ S c
              · simp [hvS]
              · simp only [hvS, if_false]
                rw [hfix v hv hvS]
                exact hfix' v (fun c' hc' => (hp.1 c' hc').2 v hv)
            · rw [← hF']
              apply List.map_congr_left
              intro c' hc'
              apply rename_congr
              intro v hv
              have hvS : v ∉ S c := (hp.1 c' hc').1 v hv
              simp [hvS]
          · intro v hv
            have h1 : v ∉ S c := hv c List.mem_cons_self
            simp only [h1, if_false]
            exact hfix' v (fun c' hc' => hv c' (List.mem_cons_of_mem _ hc'))

end Glue

section SortKey

variable [DecidableEq V] {K : Type*} [LinearOrder K] (κ : Tm (Tok A) ℕ → K)

/-- The variant key of a term, as a sort key. -/
def vkey (t : ETm A V) : K := κ (ecanon t)

/-- **The sort key**: arrange bottom-up, sorting the arguments of declared heads by their variant
keys, then number the variables of the arranged term by first occurrence. -/
def sortKey (t : ETm A V) : Tm (Tok A) ℕ := ecanon (arrangeBy comm (vkey κ) t)

omit [LinearOrder K] in
theorem vkey_rename (σ : Equiv.Perm V) (t : ETm A V) : vkey κ (t.rename σ) = vkey κ t := by
  unfold vkey
  rw [← perm_smul_def]
  exact congrArg κ (ekey_perm_smul idxOf_separates idxOf_renameInvariant σ t)

omit [LinearOrder K] in
theorem vkey_eq_of_variant {s t : ETm A V} (h : Variant s t) : vkey κ s = vkey κ t := by
  unfold vkey
  rw [ecanon_eq_iff_variant.mpr h]

/-- Arranging commutes with permutations of the variables. -/
theorem arrangeBy_rename (σ : Equiv.Perm V) (t : ETm A V) :
    arrangeBy comm (vkey κ) (t.rename σ) = (arrangeBy comm (vkey κ) t).rename σ := by
  induction t using ETm.rec (motive_2 := fun l =>
      (l.map (rename σ)).map (arrangeBy comm (vkey κ)) =
        (l.map (arrangeBy comm (vkey κ))).map (rename σ)) with
  | atom a => rfl
  | var v => rfl
  | node h args ih =>
      rw [rename_node, arrangeBy_node, arrangeBy_node, ih]
      by_cases hc : comm h
      · rw [if_pos hc, if_pos hc, rename_node]
        congr 1
        exact insertionSort_map (keyLE (vkey κ)) (keyLE (vkey κ)) (rename σ)
          (fun a b => by simp only [keyLE, vkey_rename]) _
      · rw [if_neg hc, if_neg hc, rename_node]
  | nil => rfl
  | cons c cs hc hcs =>
      simp only [List.map_cons, List.cons.injEq]
      exact ⟨hc, hcs⟩

theorem map_eq_of_forall₂ {α β γ : Type*} {g : α → γ} {g' : β → γ} :
    ∀ {l : List α} {m : List β}, List.Forall₂ (fun a b => g a = g' b) l m →
      l.map g = m.map g'
  | _, _, .nil => rfl
  | _, _, .cons h hrest => by simp [h, map_eq_of_forall₂ hrest]

/-- Lists with pairwise disjoint variables. -/
def Disjoint' (l : List (ETm A V)) : Prop :=
  l.Pairwise fun c c' => (∀ v ∈ c'.vars, v ∉ c.vars) ∧ (∀ v ∈ c.vars, v ∉ c'.vars)

omit [DecidableEq V] in
theorem disjoint'_of_pairwise {l : List (ETm A V)}
    (h : l.Pairwise fun c d => ∀ v ∈ c.vars, v ∉ d.vars) : Disjoint' l :=
  h.imp fun hcd => ⟨fun v hv hv' => hcd v hv' hv, hcd⟩

omit [DecidableEq V] in
theorem disjoint'_perm {l l' : List (ETm A V)} (h : Disjoint' l) (hp : l.Perm l') : Disjoint' l' :=
  h.perm hp fun hxy => ⟨hxy.2, hxy.1⟩

omit [DecidableEq V] in
theorem disjoint'_of_forall₂ {l m : List (ETm A V)}
    (hf : List.Forall₂ (fun a b => a.vars.Perm b.vars) l m) (h : Disjoint' l) : Disjoint' m :=
  pairwise_of_forall₂ (fun _ _ _ _ ha hb hab =>
    ⟨fun v hv hv' => hab.1 v (hb.mem_iff.mpr hv) (ha.mem_iff.mpr hv'),
     fun v hv hv' => hab.2 v (ha.mem_iff.mpr hv) (hb.mem_iff.mpr hv')⟩) hf h

theorem vars_perm_arrange (t : ETm A V) : (arrangeBy comm (vkey κ) t).vars.Perm t.vars :=
  (vars_perm_of_arr comm _ _ (arr_arrangeBy comm (vkey κ) t)).symm

theorem hidden_perm_arrange (t : ETm A V) :
    (hidden comm (arrangeBy comm (vkey κ) t)).Perm (hidden comm t) :=
  (hidden_perm_of_arr comm _ _ (arr_arrangeBy comm (vkey κ) t)).symm

theorem forall₂_arrange_vars {l : List (ETm A V)} :
    List.Forall₂ (fun a b => a.vars.Perm b.vars) l (l.map (arrangeBy comm (vkey κ))) := by
  rw [List.forall₂_map_right_iff]
  exact List.forall₂_same.mpr fun c _ => (vars_perm_arrange comm κ c).symm

mutual

/-- **In the easy class, arranging an arrangement gives a variant**, by renamings that move only
variables under declared heads. -/
theorem arrange_variant (hκ : Function.Injective κ) :
    ∀ (s u : ETm A V), Priv comm s → Arr comm s u →
      ∃ f g : V → V, (arrangeBy comm (vkey κ) s).rename f = arrangeBy comm (vkey κ) u ∧
        (arrangeBy comm (vkey κ) u).rename g = arrangeBy comm (vkey κ) s ∧
        ∀ v, v ∉ hidden comm s → f v = v ∧ g v = v
  | .atom _, _, _, h => by
      rw [arr_atom] at h
      subst h
      exact ⟨id, id, rename_id _, rename_id _, fun _ _ => ⟨rfl, rfl⟩⟩
  | .var _, _, _, h => by
      rw [arr_var] at h
      subst h
      exact ⟨id, id, rename_id _, rename_id _, fun _ _ => ⟨rfl, rfl⟩⟩
  | .node h args, _, hpriv, hs => by
      obtain ⟨m, a', rfl, f₂, p, e⟩ := (arr_node comm).mp hs
      obtain ⟨hpa, hcomm, hord⟩ := (priv_node comm).mp hpriv
      have IH := arrange_variant_args hκ args m hpa f₂
      have hvm : List.Forall₂ (fun a b => a.vars.Perm b.vars) args m :=
        vars_perm_of_arr_args comm args m f₂
      by_cases hc : comm h
      · -- a declared head: sorted lists of pointwise variants
        set L₁ := (args.map (arrangeBy comm (vkey κ))).insertionSort (keyLE (vkey κ)) with hL₁
        set L₂ := (a'.map (arrangeBy comm (vkey κ))).insertionSort (keyLE (vkey κ)) with hL₂
        have hpm : (args.map (arrangeBy comm (vkey κ))).map (vkey κ) =
            (m.map (arrangeBy comm (vkey κ))).map (vkey κ) := by
          rw [List.map_map, List.map_map]
          refine map_eq_of_forall₂ (IH.imp fun {c d} hcd => ?_)
          obtain ⟨f, g, hf, hg, -⟩ := hcd
          exact vkey_eq_of_variant κ ⟨⟨f, hf⟩, g, hg⟩
        have hkeys : L₁.map (vkey κ) = L₂.map (vkey κ) := by
          have : Std.Antisymm (fun a b : K => a ≤ b) := ⟨fun _ _ h1 h2 => le_antisymm h1 h2⟩
          refine List.Perm.eq_of_pairwise' (r := fun a b : K => a ≤ b) ?_ ?_ ?_
          · exact List.pairwise_map.mpr (pairwise_sort (vkey κ) _)
          · exact List.pairwise_map.mpr (pairwise_sort (vkey κ) _)
          · have q1 : (L₁.map (vkey κ)).Perm
                ((args.map (arrangeBy comm (vkey κ))).map (vkey κ)) :=
              (List.perm_insertionSort _ _).map _
            have q2 : (L₂.map (vkey κ)).Perm
                ((a'.map (arrangeBy comm (vkey κ))).map (vkey κ)) :=
              (List.perm_insertionSort _ _).map _
            rw [hpm] at q1
            exact q1.trans ((((p hc).map (arrangeBy comm (vkey κ))).map (vkey κ)).trans q2.symm)
        have hvar : List.Forall₂ Variant L₁ L₂ := by
          refine (forall₂_eq_of_map_eq (vkey κ) hkeys).imp fun {c d} hcd => ?_
          exact ecanon_eq_iff_variant.mp (hκ hcd)
        have hd₁ : Disjoint' L₁ :=
          disjoint'_perm (disjoint'_of_forall₂ (forall₂_arrange_vars comm κ)
            (disjoint'_of_pairwise (hcomm hc))) (List.perm_insertionSort _ _).symm
        have hd₂ : Disjoint' L₂ := by
          have hdm : Disjoint' m := disjoint'_of_forall₂ hvm (disjoint'_of_pairwise (hcomm hc))
          exact disjoint'_perm (disjoint'_of_forall₂ (forall₂_arrange_vars comm κ)
            (disjoint'_perm hdm (p hc))) (List.perm_insertionSort _ _).symm
        obtain ⟨F, hF, hFfix⟩ := glue (fun c => c.vars) L₁ L₂
          (hvar.imp fun {c d} hcd => by
            obtain ⟨⟨f, hf⟩, -⟩ := hcd
            exact ⟨f, hf, fun v hv hv' => absurd hv hv'⟩) hd₁
        obtain ⟨G, hG, hGfix⟩ := glue (fun c => c.vars) L₂ L₁
          (forall₂_swap' (hvar.imp fun {c d} hcd => by
            obtain ⟨-, g, hg⟩ := hcd
            exact ⟨g, hg, fun v hv hv' => absurd hv hv'⟩)) hd₂
        refine ⟨F, G, ?_, ?_, ?_⟩
        · rw [arrangeBy_node, arrangeBy_node, if_pos hc, if_pos hc, rename_node]
          exact congrArg _ hF
        · rw [arrangeBy_node, arrangeBy_node, if_pos hc, if_pos hc, rename_node]
          exact congrArg _ hG
        · intro v hv
          rw [hidden_node, if_pos hc] at hv
          have hv' : ∀ c ∈ args, v ∉ c.vars := fun c hc' hvc =>
            hv (List.mem_flatten.mpr ⟨c.vars, List.mem_map.mpr ⟨c, hc', rfl⟩, hvc⟩)
          refine ⟨hFfix v fun c hcL => ?_, hGfix v fun d hdL => ?_⟩
          · obtain ⟨c₀, hc₀, rfl⟩ :=
              List.mem_map.mp ((List.perm_insertionSort _ _).subset hcL)
            exact fun hvc => hv' c₀ hc₀ ((vars_perm_arrange comm κ c₀).subset hvc)
          · obtain ⟨d₀, hd₀, rfl⟩ :=
              List.mem_map.mp ((List.perm_insertionSort _ _).subset hdL)
            obtain ⟨c₀, hc₀, hq⟩ :=
              exists_of_mem_forall₂_right hvm ((p hc).symm.subset hd₀)
            exact fun hvd => hv' c₀ hc₀
              (hq.symm.subset ((vars_perm_arrange comm κ d₀).subset hvd))
      · -- any other head: glue the arguments' renamings, which move only hidden variables
        have em := e hc
        subst em
        have hfw : List.Forall₂ (fun c d => ∃ f : V → V, c.rename f = d ∧
            ∀ v ∈ c.vars, v ∉ hidden comm c → f v = v)
            (args.map (arrangeBy comm (vkey κ))) (m.map (arrangeBy comm (vkey κ))) := by
          rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
          refine IH.imp fun {c d} hcd => ?_
          obtain ⟨f, g, hf, -, hfix⟩ := hcd
          exact ⟨f, hf, fun v _ hv => (hfix v fun hv' =>
            hv ((hidden_perm_arrange comm κ c).symm.subset hv')).1⟩
        have hbw : List.Forall₂ (fun c d => ∃ f : V → V, c.rename f = d ∧
            ∀ v ∈ c.vars, v ∉ hidden comm c → f v = v)
            (m.map (arrangeBy comm (vkey κ))) (args.map (arrangeBy comm (vkey κ))) := by
          rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
          refine forall₂_swap' ((forall₂_and' IH (hidden_perm_of_arr_args comm args m f₂)).imp
            fun {c d} hcd => ?_)
          obtain ⟨⟨f, g, -, hg, hfix⟩, hh⟩ := hcd
          refine ⟨g, hg, fun v _ hv => (hfix v fun hv' => hv ?_).2⟩
          exact (hidden_perm_arrange comm κ d).symm.subset (hh.subset hv')
        have hpw : (args.map (arrangeBy comm (vkey κ))).Pairwise (fun c c' =>
            (∀ v ∈ c'.vars, v ∉ hidden comm c) ∧
            (∀ v ∈ c.vars, v ∉ hidden comm c')) := by
          rw [List.pairwise_map]
          refine (hord hc).imp fun {c d} hcd => ⟨fun v hv hv' => ?_, fun v hv hv' => ?_⟩
          · exact hcd.1 v ((hidden_perm_arrange comm κ c).subset hv')
              ((vars_perm_arrange comm κ d).subset hv)
          · exact hcd.2 v ((hidden_perm_arrange comm κ d).subset hv')
              ((vars_perm_arrange comm κ c).subset hv)
        have hpw' : (m.map (arrangeBy comm (vkey κ))).Pairwise (fun c c' =>
            (∀ v ∈ c'.vars, v ∉ hidden comm c) ∧
            (∀ v ∈ c.vars, v ∉ hidden comm c')) := by
          have hq : List.Forall₂ (fun a b => a.vars.Perm b.vars ∧
              (hidden comm a).Perm (hidden comm b)) args m :=
            forall₂_and' hvm (hidden_perm_of_arr_args comm args m f₂)
          rw [List.pairwise_map]
          refine pairwise_of_forall₂ (R := fun c d =>
            (∀ v ∈ hidden comm c, v ∉ d.vars) ∧ (∀ v ∈ hidden comm d, v ∉ c.vars))
            (fun a b a' b' ha hb hab => ⟨fun v hv hv' => ?_, fun v hv hv' => ?_⟩) hq (hord hc)
          · exact hab.1 v (ha.2.symm.subset ((hidden_perm_arrange comm κ a').subset hv'))
              (hb.1.symm.subset ((vars_perm_arrange comm κ b').subset hv))
          · exact hab.2 v (hb.2.symm.subset ((hidden_perm_arrange comm κ b').subset hv'))
              (ha.1.symm.subset ((vars_perm_arrange comm κ a').subset hv))
        obtain ⟨F, hF, hFfix⟩ := glue (hidden comm) _ _ hfw hpw
        obtain ⟨G, hG, hGfix⟩ := glue (hidden comm) _ _ hbw hpw'
        refine ⟨F, G, ?_, ?_, ?_⟩
        · rw [arrangeBy_node, arrangeBy_node, if_neg hc, if_neg hc, rename_node]
          exact congrArg _ hF
        · rw [arrangeBy_node, arrangeBy_node, if_neg hc, if_neg hc, rename_node]
          exact congrArg _ hG
        · intro v hv
          rw [hidden_node, if_neg hc] at hv
          have hv' : ∀ c ∈ args, v ∉ hidden comm c := fun c hc' hvc =>
            hv (List.mem_flatten.mpr ⟨hidden comm c, List.mem_map.mpr ⟨c, hc', rfl⟩, hvc⟩)
          refine ⟨hFfix v fun c hcL => ?_, hGfix v fun d hdL => ?_⟩
          · obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.mp hcL
            exact fun hvc => hv' c₀ hc₀ ((hidden_perm_arrange comm κ c₀).subset hvc)
          · obtain ⟨d₀, hd₀, rfl⟩ := List.mem_map.mp hdL
            obtain ⟨c₀, hc₀, hq⟩ := exists_of_mem_forall₂_right
              (hidden_perm_of_arr_args comm args m f₂) hd₀
            exact fun hvd => hv' c₀ hc₀
              (hq.symm.subset ((hidden_perm_arrange comm κ d₀).subset hvd))

theorem arrange_variant_args (hκ : Function.Injective κ) :
    ∀ (l m : List (ETm A V)), (∀ c ∈ l, Priv comm c) → List.Forall₂ (Arr comm) l m →
      List.Forall₂ (fun c d => ∃ f g : V → V,
        (arrangeBy comm (vkey κ) c).rename f = arrangeBy comm (vkey κ) d ∧
        (arrangeBy comm (vkey κ) d).rename g = arrangeBy comm (vkey κ) c ∧
        ∀ v, v ∉ hidden comm c → f v = v ∧ g v = v) l m
  | [], _, _, h => by
      cases h
      exact .nil
  | c :: cs, _, hp, h => by
      cases h with
      | cons hcd hrest =>
          exact .cons (arrange_variant hκ c _ (hp c List.mem_cons_self) hcd)
            (arrange_variant_args hκ cs _ (fun c' hc' => hp c' (List.mem_cons_of_mem _ hc')) hrest)

end

/-- **Soundness for every term**: equal sort keys put two terms in one orbit. -/
theorem orbit_of_sortKey_eq {s t : ETm A V} (h : sortKey comm κ s = sortKey comm κ t) :
    t ∈ MulAction.orbit (Sym comm V) s := by
  have hv : Variant (arrangeBy comm (vkey κ) s) (arrangeBy comm (vkey κ) t) :=
    ecanon_eq_iff_variant.mp h
  have h1 : arrangeBy comm (vkey κ) t ∈ MulAction.orbit (Sym comm V) s :=
    (mem_orbit_sym_iff comm).mpr ⟨_, arr_arrangeBy comm (vkey κ) s, hv⟩
  have h2 : t ∈ MulAction.orbit (Sym comm V) (arrangeBy comm (vkey κ) t) :=
    (mem_orbit_sym_iff comm).mpr ⟨t, arr_symm comm _ _ (arr_arrangeBy comm (vkey κ) t),
      variant_refl t⟩
  rw [MulAction.orbit_eq_iff.mpr h1] at h2
  exact h2

/-- **Completeness in the easy class**: terms in one orbit have one sort key. -/
theorem sortKey_eq_of_orbit (hκ : Function.Injective κ) {s t : ETm A V} (hs : Priv comm s)
    (h : t ∈ MulAction.orbit (Sym comm V) s) : sortKey comm κ s = sortKey comm κ t := by
  obtain ⟨u, hu, hv⟩ := (mem_orbit_sym_iff comm).mp h
  obtain ⟨σ, rfl⟩ := variant_iff_exists_perm.mp hv
  obtain ⟨f, g, hf, hg, -⟩ := arrange_variant comm κ hκ s u hs hu
  unfold sortKey
  rw [arrangeBy_rename]
  refine ecanon_eq_iff_variant.mpr (variant_trans ⟨⟨f, hf⟩, g, hg⟩ ?_)
  exact variant_iff_exists_perm.mpr ⟨σ, rfl⟩

/-- **The easy class has a bottom-up canonical key**: sorting the arguments of declared heads by
their variant keys and numbering the variables by first occurrence gives equal keys exactly on the
orbits of renamings and argument permutations. -/
theorem sortKey_eq_iff_orbit (hκ : Function.Injective κ) {s t : ETm A V} (hs : Priv comm s) :
    sortKey comm κ s = sortKey comm κ t ↔ t ∈ MulAction.orbit (Sym comm V) s :=
  ⟨orbit_of_sortKey_eq comm κ, sortKey_eq_of_orbit comm κ hκ hs⟩

end SortKey

end ETm

/-! ### A linear order on keys, and controls -/

namespace TreeCanonControls

open ETm

/-- A prefix code for keys over numbered atoms: lists of numbers, compared lexicographically. -/
def ser : Tm (Tok ℕ) ℕ → List ℕ
  | .pair s t => 0 :: (ser s ++ ser t)
  | .atom (.sym a) => [1, a]
  | .atom (.head h) => [2, h]
  | .atom .nil => [3]
  | .var n => [4, n]

theorem ser_append_inj : ∀ (s t : Tm (Tok ℕ) ℕ) (r r' : List ℕ),
    ser s ++ r = ser t ++ r' → s = t ∧ r = r' := by
  intro s
  induction s with
  | atom a =>
      intro t r r' h
      rcases t with b | m | ⟨t₁, t₂⟩
      · rcases a with a | a | _ <;> rcases b with b | b | _ <;> simp_all [ser]
      · rcases a with a | a | _ <;> simp_all [ser]
      · rcases a with a | a | _ <;> simp_all [ser]
  | var n =>
      intro t r r' h
      rcases t with b | m | ⟨t₁, t₂⟩
      · rcases b with b | b | _ <;> simp_all [ser]
      · simp_all [ser]
      · simp_all [ser]
  | pair s₁ s₂ ih₁ ih₂ =>
      intro t r r' h
      rcases t with b | m | ⟨t₁, t₂⟩
      · rcases b with b | b | _ <;> simp_all [ser]
      · simp_all [ser]
      · simp only [ser, List.cons_append, List.cons.injEq, List.append_assoc, true_and] at h
        obtain ⟨rfl, h2⟩ := ih₁ t₁ _ _ h
        obtain ⟨rfl, rfl⟩ := ih₂ t₂ _ _ h2
        exact ⟨rfl, rfl⟩

theorem ser_injective : Function.Injective ser := fun s t h =>
  (ser_append_inj s t [] [] (by simpa using h)).1

/-- Names as data: the key of a term is the code of its encoding. -/
def posKey (t : ETm ℕ ℕ) : List ℕ := ser (enc t)

theorem posKey_injective : Function.Injective posKey := fun _ _ h =>
  enc_injective (ser_injective h)

/-- Head `0` is the declared bag; `1` is `f`, `2` is `g`, `3` is `h`, `4` is `k`. -/
def declared (h : ℕ) : Prop := h = 0

instance : DecidablePred declared := fun h => inferInstanceAs (Decidable (h = 0))

/-- Names as data: `(bag (g $0) (h $1))` and `(bag (h $1) (g $0))` have one arranged form. -/
theorem pos_same : arrangeBy declared posKey (.node 0 [.node 2 [.var 0], .node 3 [.var 1]]) =
    arrangeBy declared posKey (.node 0 [.node 3 [.var 1], .node 2 [.var 0]]) := by decide

/-- Names as data: `(bag (g $0) (h $1))` and `(bag (h $0) (g $1))` are not arrangements of each
other. -/
theorem pos_apart : ¬ Arr declared (.node 0 [.node 2 [.var 0], .node 3 [.var 1]] : ETm ℕ ℕ)
    (.node 0 [.node 3 [.var 0], .node 2 [.var 1]]) := by
  rw [← pcanon_eq_iff_arr declared posKey posKey_injective]
  decide

/-- The easy class: `(f $0 (bag (g $1) (h $2)))`. -/
def easy : ETm ℕ ℕ := .node 1 [.var 0, .node 0 [.node 2 [.var 1], .node 3 [.var 2]]]

/-- `(f $5 (bag (h $6) (g $7)))`, in the orbit of `easy`. -/
def easy' : ETm ℕ ℕ := .node 1 [.var 5, .node 0 [.node 3 [.var 6], .node 2 [.var 7]]]

theorem easy_priv : Priv declared easy := by
  simp [easy, Priv, PrivArgs, ETm.hidden, ETm.hiddenArgs, varsArgs, vars, declared]

theorem easy_sortKey : sortKey declared ser easy = sortKey declared ser easy' := by decide

theorem easy_orbit : easy' ∈ MulAction.orbit (Sym declared ℕ) easy :=
  orbit_of_sortKey_eq declared ser easy_sortKey

/-- Outside the class: `(k (bag (g $0) (g $1)) $1)`; `$1` is under the bag and outside it. -/
def coupled : ETm ℕ ℕ := .node 4 [.node 0 [.node 2 [.var 0], .node 2 [.var 1]], .var 1]

/-- `(k (bag (g $1) (g $0)) $1)`: the same term with the bag's arguments exchanged. -/
def coupled' : ETm ℕ ℕ := .node 4 [.node 0 [.node 2 [.var 1], .node 2 [.var 0]], .var 1]

theorem coupled_orbit : coupled' ∈ MulAction.orbit (Sym declared ℕ) coupled :=
  (key_eq_iff_orbit declared idxOf_separates idxOf_renameInvariant).mp (by decide)

/-- **The negative control**: one orbit, two sort keys. -/
theorem coupled_sortKey : sortKey declared ser coupled ≠ sortKey declared ser coupled' := by
  decide

/-- So the coupled term is not in the easy class, and the class condition cannot be dropped. -/
theorem coupled_not_priv : ¬ Priv declared coupled := fun h =>
  coupled_sortKey ((sortKey_eq_iff_orbit declared ser ser_injective h).mpr coupled_orbit)

end TreeCanonControls

end Mettapedia.InformationTheory.SymmetryKeys
