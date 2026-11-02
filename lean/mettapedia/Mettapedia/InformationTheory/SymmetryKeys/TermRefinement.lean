import Mettapedia.InformationTheory.SymmetryKeys.TreeCanon

/-!
# Refinement keys for any term are sound

A refinement key for terms with variables, built only from operations that every element of the
symmetry group respects.

* Round `0` gives every variable one colour.
* Round `k + 1` colours the variable `v` by the arranged form (`arrangeBy`, names as data) of the
  term in which `v` is replaced by a mark and every other variable by its colour after round `k`
  (`colour`).  Colours are ground terms.
* The key after `k` rounds is the arranged form of the term with every variable replaced by its
  colour (`refineKey`).

Example: in `(f $x $x)` and `(f $x $y)` every variable has the same colour after round `0`, so the
round-`0` keys agree although the terms are in two orbits; after round `1` the variable `$x` of
`(f $x $x)` is coloured by `(f ● ●)` and the variables of `(f $x $y)` by `(f ● ○)`,
so the round-`1`
keys differ.

* `colour_smul`, `refineKey_smul`: renaming and permuting the arguments of declared heads keep every
  colour (carried along the renaming) and every key.
* **Soundness** (`not_orbit_of_refineKey_ne`): different keys after some round, different orbits.

Completeness fails: equal keys do not put two terms in one orbit (for graphs, `Refinement`), so a
collision of refinement keys must be confirmed by an exact test.
-/

namespace Mettapedia.InformationTheory.SymmetryKeys

open Mettapedia.InformationTheory.RelationStoreVariantKeys

namespace ETm

variable {A B V W X : Type*}

/-! ### Substituting terms for variables, and renaming atoms -/

mutual

/-- Replace every variable by a term. -/
def subst (c : V → ETm A W) : ETm A V → ETm A W
  | .atom a => .atom a
  | .var v => c v
  | .node h args => .node h (substArgs c args)

/-- `subst` on each argument. -/
def substArgs (c : V → ETm A W) : List (ETm A V) → List (ETm A W)
  | [] => []
  | x :: xs => subst c x :: substArgs c xs

end

theorem substArgs_eq_map (c : V → ETm A W) (l : List (ETm A V)) :
    substArgs c l = l.map (subst c) := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [substArgs, ih]

theorem subst_node (c : V → ETm A W) (h : A) (args : List (ETm A V)) :
    subst c (.node h args) = .node h (args.map (subst c)) := by
  simp [subst, substArgs_eq_map]

theorem subst_rename (c : V → ETm A W) (f : X → V) (t : ETm A X) :
    subst c (t.rename f) = subst (c ∘ f) t := by
  induction t using ETm.rec (motive_2 := fun l =>
      (l.map (rename f)).map (subst c) = l.map (subst (c ∘ f))) with
  | atom a => rfl
  | var v => rfl
  | node h args ih => rw [rename_node, subst_node, subst_node, ih]
  | nil => rfl
  | cons x xs hx hxs => simp only [List.map_cons, List.cons.injEq]; exact ⟨hx, hxs⟩

mutual

/-- Every atom and head renamed by `g`. -/
def mapAtoms (g : A → B) : ETm A V → ETm B V
  | .atom a => .atom (g a)
  | .var v => .var v
  | .node h args => .node (g h) (mapAtomsArgs g args)

/-- `mapAtoms` on each argument. -/
def mapAtomsArgs (g : A → B) : List (ETm A V) → List (ETm B V)
  | [] => []
  | x :: xs => mapAtoms g x :: mapAtomsArgs g xs

end

theorem mapAtomsArgs_eq_map (g : A → B) (l : List (ETm A V)) :
    mapAtomsArgs g l = l.map (mapAtoms g) := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [mapAtomsArgs, ih]

theorem mapAtoms_node (g : A → B) (h : A) (args : List (ETm A V)) :
    mapAtoms g (.node h args : ETm A V) = .node (g h) (args.map (mapAtoms g)) := by
  simp [mapAtoms, mapAtomsArgs_eq_map]

theorem mapAtoms_rename (g : A → B) (f : V → W) (t : ETm A V) :
    mapAtoms g (t.rename f) = (mapAtoms g t).rename f := by
  induction t using ETm.rec (motive_2 := fun l =>
      (l.map (rename f)).map (mapAtoms g) = (l.map (mapAtoms g)).map (rename f)) with
  | atom a => rfl
  | var v => rfl
  | node h args ih => rw [rename_node, mapAtoms_node, mapAtoms_node, rename_node, ih]
  | nil => rfl
  | cons x xs hx hxs => simp only [List.map_cons, List.cons.injEq]; exact ⟨hx, hxs⟩

section ArrMaps

variable (comm : A → Prop) (comm' : B → Prop)

mutual

theorem arr_subst (c : V → ETm A W) :
    ∀ (s t : ETm A V), Arr comm s t → Arr comm (subst c s) (subst c t)
  | .atom _, _, h => by
      rw [arr_atom] at h
      subst h
      exact arr_refl comm _
  | .var _, _, h => by
      rw [arr_var] at h
      subst h
      exact arr_refl comm _
  | .node h args, _, hs => by
      obtain ⟨m, a', rfl, f, p, e⟩ := (arr_node comm).mp hs
      rw [subst_node, subst_node, arr_node]
      refine ⟨m.map (subst c), a'.map (subst c), rfl, ?_, fun hc => (p hc).map _,
        fun hc => by rw [e hc]⟩
      rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
      exact arr_subst_args c args m f

theorem arr_subst_args (c : V → ETm A W) : ∀ (l m : List (ETm A V)),
    List.Forall₂ (Arr comm) l m →
      List.Forall₂ (fun a b => Arr comm (subst c a) (subst c b)) l m
  | [], _, h => by
      cases h
      exact .nil
  | x :: xs, _, h => by
      cases h with
      | cons hxy hrest => exact .cons (arr_subst c x _ hxy) (arr_subst_args c xs _ hrest)

end

mutual

theorem arr_mapAtoms (g : A → B) (hg : ∀ h, comm' (g h) ↔ comm h) :
    ∀ (s t : ETm A V), Arr comm s t → Arr comm' (mapAtoms g s) (mapAtoms g t)
  | .atom _, _, h => by
      rw [arr_atom] at h
      subst h
      exact arr_refl comm' _
  | .var _, _, h => by
      rw [arr_var] at h
      subst h
      exact arr_refl comm' _
  | .node h args, _, hs => by
      obtain ⟨m, a', rfl, f, p, e⟩ := (arr_node comm).mp hs
      rw [mapAtoms_node, mapAtoms_node, arr_node]
      refine ⟨m.map (mapAtoms g), a'.map (mapAtoms g), rfl, ?_,
        fun hc => (p ((hg h).mp hc)).map _, fun hc => by rw [e (fun h' => hc ((hg h).mpr h'))]⟩
      rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
      exact arr_mapAtoms_args g hg args m f

theorem arr_mapAtoms_args (g : A → B) (hg : ∀ h, comm' (g h) ↔ comm h) :
    ∀ (l m : List (ETm A V)), List.Forall₂ (Arr comm) l m →
      List.Forall₂ (fun a b => Arr comm' (mapAtoms g a) (mapAtoms g b)) l m
  | [], _, h => by
      cases h
      exact .nil
  | x :: xs, _, h => by
      cases h with
      | cons hxy hrest =>
          exact .cons (arr_mapAtoms g hg x _ hxy) (arr_mapAtoms_args g hg xs _ hrest)

end

end ArrMaps

/-! ### Rounds of refinement -/

variable (comm : A → Prop) [DecidablePred comm]

/-- Declared heads among the colour atoms: `none` is a mark, never declared. -/
def ocomm : Option A → Prop
  | none => False
  | some h => comm h

instance : DecidablePred (ocomm comm) := fun o => by
  cases o with
  | none => exact inferInstanceAs (Decidable False)
  | some h => exact inferInstanceAs (Decidable (comm h))

omit [DecidablePred comm] in
theorem ocomm_some (h : A) : ocomm comm (some h) ↔ comm h := Iff.rfl

variable {L : Type*} [LinearOrder L] (pk : ETm (Option A) Empty → L) [DecidableEq V]

/-- The mark that replaces the variable being coloured. -/
def mark : ETm (Option A) Empty := .node none []

/-- The colour of the variable `v` of `t` after `k` rounds: a ground term. -/
def colour (t : ETm A V) : ℕ → V → ETm (Option A) Empty
  | 0, _ => .atom none
  | k + 1, v => arrangeBy (ocomm comm) pk
      (subst (fun w => if w = v then mark else colour t k w) (mapAtoms some t))

/-- **The refinement key after `k` rounds**: the arranged form of the term with every variable
replaced by its colour. -/
def refineKey (k : ℕ) (t : ETm A V) : ETm (Option A) Empty :=
  arrangeBy (ocomm comm) pk (subst (colour comm pk t k) (mapAtoms some t))

omit [DecidableEq V] in
/-- Arrangements and renamings of the term carry over to the coloured terms. -/
theorem arranged_subst_eq (hpk : Function.Injective pk) (g : Sym comm V) (t : ETm A V)
    (c : V → ETm (Option A) Empty) :
    arrangeBy (ocomm comm) pk (subst (c ∘ g.1.symm) (mapAtoms some (g • t))) =
      arrangeBy (ocomm comm) pk (subst c (mapAtoms some t)) := by
  rw [sym_smul_def, perm_smul_def, mapAtoms_rename, subst_rename]
  have hc : (c ∘ g.1.symm) ∘ g.1 = c := by
    funext v
    simp
  rw [hc]
  apply (pcanon_eq_iff_arr (ocomm comm) pk hpk).mpr
  apply arr_symm
  exact arr_subst (ocomm comm) c _ _
    (arr_mapAtoms comm (ocomm comm) some (ocomm_some comm) _ _ (arr_smul comm g.2 t))

/-- **Every colour is kept**, carried along the renaming. -/
theorem colour_smul (hpk : Function.Injective pk) (g : Sym comm V) (t : ETm A V) :
    ∀ (k : ℕ) (v : V), colour comm pk (g • t) k (g.1 v) = colour comm pk t k v
  | 0, _ => rfl
  | k + 1, v => by
      have hc : (fun w => if w = g.1 v then mark else colour comm pk (g • t) k w) =
          (fun w => if w = v then mark else colour comm pk t k w) ∘ g.1.symm := by
        funext w
        have hw : g.1 (g.1.symm w) = w := g.1.apply_symm_apply w
        simp only [Function.comp_apply]
        by_cases h : w = g.1 v
        · rw [if_pos h, if_pos (by rw [h, Equiv.symm_apply_apply])]
        · rw [if_neg h, if_neg (fun h' => h (by rw [← h', hw])), ← colour_smul hpk g t k, hw]
      show arrangeBy (ocomm comm) pk (subst _ (mapAtoms some (g • t))) = _
      rw [hc, arranged_subst_eq comm pk hpk g t]
      rfl

/-- **Every key is kept** by renamings and argument permutations of declared heads. -/
theorem refineKey_smul (hpk : Function.Injective pk) (g : Sym comm V) (t : ETm A V) (k : ℕ) :
    refineKey comm pk k (g • t) = refineKey comm pk k t := by
  have hc : colour comm pk (g • t) k = colour comm pk t k ∘ g.1.symm := by
    funext w
    simp only [Function.comp_apply]
    rw [← colour_smul comm pk hpk g t k (g.1.symm w), Equiv.apply_symm_apply]
  unfold refineKey
  rw [hc, arranged_subst_eq comm pk hpk g t]

/-- Terms in one orbit have equal refinement keys after every round. -/
theorem refineKey_eq_of_orbit (hpk : Function.Injective pk) {s t : ETm A V}
    (h : t ∈ MulAction.orbit (Sym comm V) s) (k : ℕ) :
    refineKey comm pk k s = refineKey comm pk k t := by
  obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.mp h
  exact (refineKey_smul comm pk hpk g s k).symm

/-- **Refinement keys are sound for every term**: different keys after some round, different
orbits. -/
theorem not_orbit_of_refineKey_ne (hpk : Function.Injective pk) {s t : ETm A V} (k : ℕ)
    (h : refineKey comm pk k s ≠ refineKey comm pk k t) : t ∉ MulAction.orbit (Sym comm V) s :=
  fun ho => h (refineKey_eq_of_orbit comm pk hpk ho k)

/-! ### Injective maps of terms -/

omit [DecidablePred comm] [DecidableEq V] in
theorem rename_injective {f : V → W} (hf : Function.Injective f) :
    Function.Injective (rename f : ETm A V → ETm A W) := by
  intro s t h
  apply enc_injective
  have h' : (enc s).rename f = (enc t).rename f := by rw [← enc_rename, ← enc_rename, h]
  obtain ⟨hskel, hvars⟩ := Tm.rename_eq_rename_iff.mp h'
  have hv : (enc s).vars = (enc t).vars := (List.map_injective_iff.mpr hf) hvars
  have := (Tm.rename_eq_rename_iff (f := id) (g := id)).mpr ⟨hskel, by rw [hv]⟩
  simpa using this

omit [DecidablePred comm] [DecidableEq V] in
mutual

theorem mapAtoms_inj {g : A → B} (hg : Function.Injective g) :
    ∀ s t : ETm A V, mapAtoms g s = mapAtoms g t → s = t
  | .atom a, .atom b, e => by
      simp only [mapAtoms, atom.injEq] at e
      rw [hg e]
  | .atom _, .var _, e => by simp [mapAtoms] at e
  | .atom _, .node _ _, e => by simp [mapAtoms] at e
  | .var _, .atom _, e => by simp [mapAtoms] at e
  | .var v, .var w, e => by
      simp only [mapAtoms, var.injEq] at e
      rw [e]
  | .var _, .node _ _, e => by simp [mapAtoms] at e
  | .node _ _, .atom _, e => by simp [mapAtoms] at e
  | .node _ _, .var _, e => by simp [mapAtoms] at e
  | .node h args, .node h' args', e => by
      simp only [mapAtoms, node.injEq] at e
      rw [hg e.1, mapAtomsArgs_inj hg args args' e.2]

theorem mapAtomsArgs_inj {g : A → B} (hg : Function.Injective g) :
    ∀ l l' : List (ETm A V), mapAtomsArgs g l = mapAtomsArgs g l' → l = l'
  | [], [], _ => rfl
  | [], _ :: _, e => by simp [mapAtomsArgs] at e
  | _ :: _, [], e => by simp [mapAtomsArgs] at e
  | x :: xs, y :: ys, e => by
      simp only [mapAtomsArgs, List.cons.injEq] at e
      rw [mapAtoms_inj hg x y e.1, mapAtomsArgs_inj hg xs ys e.2]

end

end ETm

/-! ### Controls -/

namespace TermRefinementControls

open ETm TreeCanonControls

/-- Colour atoms as numbers: `none ↦ 0`, `some n ↦ n + 1`. -/
def code : Option ℕ → ℕ
  | none => 0
  | some n => n + 1

theorem code_injective : Function.Injective code := by
  intro a b h
  cases a <;> cases b <;> simp_all [code]

/-- A key for colour terms: the code of their encoding. -/
def colourKey (t : ETm (Option ℕ) Empty) : List ℕ :=
  ser (enc ((mapAtoms code t).rename Empty.elim))

theorem colourKey_injective : Function.Injective colourKey := fun _ _ h =>
  mapAtoms_inj code_injective _ _
    (rename_injective (fun x => x.elim) (enc_injective (ser_injective h)))

/-- `(f $0 $0)` and `(f $0 $1)`, with `f` the head `1`. -/
def fxx : ETm ℕ ℕ := .node 1 [.var 0, .var 0]
def fxy : ETm ℕ ℕ := .node 1 [.var 0, .var 1]

/-- Two orbits. -/
theorem fxx_fxy_two_orbits : fxy ∉ MulAction.orbit (Sym declared ℕ) fxx := by
  rw [← key_eq_iff_orbit declared idxOf_separates idxOf_renameInvariant]
  decide

/-- **Negative control**: after round `0` the keys collide. -/
theorem round0_collides :
    refineKey declared colourKey 0 fxx = refineKey declared colourKey 0 fxy := by
  decide

/-- **Positive control**: after round `1` the keys differ, which proves the two orbits apart. -/
theorem round1_apart :
    refineKey declared colourKey 1 fxx ≠ refineKey declared colourKey 1 fxy := by
  decide

theorem round1_proves_two_orbits : fxy ∉ MulAction.orbit (Sym declared ℕ) fxx :=
  not_orbit_of_refineKey_ne declared colourKey colourKey_injective 1 round1_apart

/-- Keys agree on one orbit: `(bag (g $0) (h $1))` and `(bag (h $5) (g $4))`. -/
theorem bag_keys_agree :
    refineKey declared colourKey 2 (.node 0 [.node 2 [.var 0], .node 3 [.var 1]] : ETm ℕ ℕ) =
      refineKey declared colourKey 2 (.node 0 [.node 3 [.var 5], .node 2 [.var 4]]) := by
  decide

end TermRefinementControls

end Mettapedia.InformationTheory.SymmetryKeys
