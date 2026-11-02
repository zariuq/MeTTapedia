import Mettapedia.InformationTheory.SymmetryKeys.Terms

/-!
# Orbit keys: renamings and the argument orders of declared heads

Some heads are declared unordered (`comm h`): the arguments of `(bag a b c)` form a bag, and
`(bag b a c)` is the same bag.  Two groups act on terms.

* **Positions** (`Pos comm`): words in the exchanges `swapAt p i`, each of which exchanges
  arguments `i` and `i + 1` of the node at path `p` (argument positions from the root) when that
  node's head is declared.  Each exchange is an involution, so the free group on them acts on terms
  (`FreeGroup.lift`).  Example: `swapAt [] 0 (bag a b c) = (bag b a c)`, and
  `swapAt [1] 0 (f x (bag a b)) = (f x (bag b a))`.
* **Renamings**: the permutations of the variables (`Terms`).

The two actions commute (`smul_rename`), so their product `Sym comm V` acts on terms.  Its orbits
are the classes "equal up to the names of the variables and the order of the arguments of declared
heads, at every depth".

* `Arr comm t u`: `u` is `t` with the arguments of declared heads permuted, at every depth.  It is
  the orbit relation of the positional group (`mem_orbit_pos_iff`).
* `mem_orbit_sym_iff`: `t` is in the orbit of `s` iff some arrangement of `s` is a variant of `t`.
* `arrs comm t` lists all arrangements (`mem_arrs`); so the positional orbit is finite.
* **`key_eq_iff_orbit`**: for a numbering that separates variables and reads only their pattern,
  the set of keys of the arrangements of a term (`orbitKeys`) is equal for two terms exactly when
  they are in one orbit.  Its least element under any linear order is a single key with the same
  property (`orbitKey_eq_iff_orbit`).  One key per orbit (`card_orbitKeys_eq_card_orbits`).

This is the specification: computing it lists every arrangement.  Faster keys are compared with it
in `TreeCanon`.
-/

namespace Mettapedia.InformationTheory.SymmetryKeys

open Mettapedia.InformationTheory.RelationStoreVariantKeys

namespace ETm

variable {A V W : Type*}

/-! ### Lists: adjacent exchanges, modifications, orderings -/

/-- Exchange the elements at `i` and `i + 1`; a list too short for them is unchanged. -/
def swapAdj {α : Type*} : ℕ → List α → List α
  | 0, a :: b :: l => b :: a :: l
  | n + 1, a :: l => a :: swapAdj n l
  | 0, [] => []
  | 0, [a] => [a]
  | _ + 1, [] => []

theorem swapAdj_swapAdj {α : Type*} : ∀ (n : ℕ) (l : List α), swapAdj n (swapAdj n l) = l
  | 0, [] => rfl
  | 0, [_] => rfl
  | 0, _ :: _ :: _ => rfl
  | _ + 1, [] => rfl
  | n + 1, a :: l => by simp only [swapAdj, swapAdj_swapAdj n l]

theorem swapAdj_perm {α : Type*} : ∀ (n : ℕ) (l : List α), (swapAdj n l).Perm l
  | 0, [] => .refl _
  | 0, [_] => .refl _
  | 0, a :: b :: l => .swap a b l
  | _ + 1, [] => .refl _
  | n + 1, a :: l => (swapAdj_perm n l).cons a

theorem map_swapAdj {α β : Type*} (f : α → β) :
    ∀ (n : ℕ) (l : List α), (swapAdj n l).map f = swapAdj n (l.map f)
  | 0, [] => rfl
  | 0, [_] => rfl
  | 0, _ :: _ :: _ => rfl
  | _ + 1, [] => rfl
  | n + 1, a :: l => by simp only [swapAdj, List.map_cons, map_swapAdj f n l]

theorem swapAdj_append {α : Type*} (pre : List α) (x y : α) (l : List α) :
    swapAdj pre.length (pre ++ y :: x :: l) = pre ++ x :: y :: l := by
  induction pre with
  | nil => rfl
  | cons a pre ih => simp only [List.length_cons, List.cons_append, swapAdj, ih]

theorem map_modify {α β : Type*} (f : α → β) {g : α → α} {g' : β → β}
    (hfg : ∀ a, f (g a) = g' (f a)) : ∀ (l : List α) (k : ℕ),
    (l.modify k g).map f = (l.map f).modify k g'
  | [], _ => by simp
  | a :: l, 0 => by simp [hfg]
  | a :: l, k + 1 => by simp [map_modify f hfg l k]

theorem modify_append_length {α : Type*} (pre : List α) (c : α)
    (post : List α) (g : α → α) :
    (pre ++ c :: post).modify pre.length g = pre ++ g c :: post := by
  induction pre with
  | nil => simp
  | cons a pre ih => simp [ih]

theorem forall₂_modify {α : Type*} {R : α → α → Prop}
    (hrefl : ∀ a, R a a) {g : α → α}
    (hg : ∀ a, R a (g a)) : ∀ (l : List α) (k : ℕ), List.Forall₂ R l (l.modify k g)
  | [], _ => by simp
  | a :: l, 0 => by
      simp only [List.modify_zero_cons]
      exact .cons (hg a) (List.forall₂_same.mpr fun x _ => hrefl x)
  | a :: l, k + 1 => by
      simp only [List.modify_succ_cons]
      exact .cons (hrefl a) (forall₂_modify hrefl hg l k)

/-- All ways to insert `a` into a list. -/
def insertions {α : Type*} (a : α) : List α → List (List α)
  | [] => [[a]]
  | b :: l => (a :: b :: l) :: (insertions a l).map (b :: ·)

/-- All orderings of a list. -/
def perms {α : Type*} : List α → List (List α)
  | [] => [[]]
  | a :: l => (perms l).flatMap (insertions a)

theorem perm_of_mem_insertions {α : Type*} {a : α} :
    ∀ {l m : List α}, m ∈ insertions a l → m.Perm (a :: l)
  | [], m, h => by
      simp only [insertions, List.mem_singleton] at h
      subst h
      exact .refl _
  | b :: l, m, h => by
      simp only [insertions, List.mem_cons, List.mem_map] at h
      rcases h with rfl | ⟨m', hm', rfl⟩
      · exact .refl _
      · exact ((perm_of_mem_insertions hm').cons b).trans (.swap a b l)

theorem self_mem_insertions {α : Type*} (a : α) : ∀ l : List α, a :: l ∈ insertions a l
  | [] => by simp [insertions]
  | b :: l => by simp [insertions]

theorem mem_insertions_erase {α : Type*} [DecidableEq α] {a : α} :
    ∀ {m : List α}, a ∈ m → m ∈ insertions a (m.erase a)
  | b :: m, h => by
      by_cases hb : b = a
      · subst hb
        rw [List.erase_cons_head]
        exact self_mem_insertions b m
      · have ha : a ∈ m := by
          rcases List.mem_cons.mp h with h' | h'
          · exact absurd h'.symm hb
          · exact h'
        rw [List.erase_cons_tail (by simpa using hb)]
        simp only [insertions, List.mem_cons, List.mem_map]
        exact Or.inr ⟨m, mem_insertions_erase ha, rfl⟩

theorem mem_perms {α : Type*} : ∀ {l m : List α}, m ∈ perms l ↔ m.Perm l
  | [], m => by simp [perms]
  | a :: l, m => by
      classical
      simp only [perms, List.mem_flatMap]
      constructor
      · rintro ⟨m', hm', hm⟩
        exact (perm_of_mem_insertions hm).trans ((mem_perms.mp hm').cons a)
      · intro hp
        have ha : a ∈ m := hp.symm.subset List.mem_cons_self
        refine ⟨m.erase a, mem_perms.mpr ?_, mem_insertions_erase ha⟩
        exact ((List.perm_cons_erase ha).symm.trans hp).cons_inv

variable (comm : A → Prop)

/-! ### Arrangements -/

mutual

/-- `Arr t u`: `u` is `t` with the arguments of declared heads permuted, at every depth. -/
def Arr : ETm A V → ETm A V → Prop
  | .atom a, u => u = .atom a
  | .var v, u => u = .var v
  | .node h args, u => ∃ m args', u = .node h args' ∧ ArrArgs args m ∧
      (comm h → m.Perm args') ∧ (¬ comm h → m = args')

/-- Arrangements, argument by argument. -/
def ArrArgs : List (ETm A V) → List (ETm A V) → Prop
  | [], m => m = []
  | c :: cs, m => ∃ d ds, m = d :: ds ∧ Arr c d ∧ ArrArgs cs ds

end

theorem arrArgs_iff : ∀ l m : List (ETm A V), ArrArgs comm l m ↔ List.Forall₂ (Arr comm) l m
  | [], m => by cases m <;> simp [ArrArgs]
  | c :: cs, m => by
      cases m with
      | nil => simp [ArrArgs]
      | cons d ds => simp [ArrArgs, arrArgs_iff cs ds]

@[simp] theorem arr_atom {a : A} {u : ETm A V} : Arr comm (.atom a) u ↔ u = .atom a := by
  simp [Arr]

@[simp] theorem arr_var {v : V} {u : ETm A V} : Arr comm (.var v) u ↔ u = .var v := by
  simp [Arr]

theorem arr_node {h : A} {args : List (ETm A V)} {u : ETm A V} :
    Arr comm (.node h args) u ↔ ∃ m args', u = .node h args' ∧
      List.Forall₂ (Arr comm) args m ∧
      (comm h → m.Perm args') ∧ (¬ comm h → m = args') := by
  simp only [Arr, arrArgs_iff]

mutual

theorem arr_refl : ∀ t : ETm A V, Arr comm t t
  | .atom _ => by simp
  | .var _ => by simp
  | .node _ args => (arr_node comm).mpr
      ⟨args, args, rfl, arr_refl_args args, fun _ => .refl _, fun _ => rfl⟩

theorem arr_refl_args : ∀ l : List (ETm A V), List.Forall₂ (Arr comm) l l
  | [] => .nil
  | c :: cs => .cons (arr_refl c) (arr_refl_args cs)

end

mutual

theorem arr_trans : ∀ (s t u : ETm A V), Arr comm s t → Arr comm t u → Arr comm s u
  | .atom _, _, _, h1, h2 => by
      rw [arr_atom] at h1
      subst h1
      exact h2
  | .var _, _, _, h1, h2 => by
      rw [arr_var] at h1
      subst h1
      exact h2
  | .node h args, _, _, h1, h2 => by
      obtain ⟨m₁, a₁, rfl, f₁, p₁, e₁⟩ := (arr_node comm).mp h1
      obtain ⟨m₂, a₂, rfl, f₂, p₂, e₂⟩ := (arr_node comm).mp h2
      rw [arr_node]
      by_cases hc : comm h
      · obtain ⟨m', fm, pm⟩ := List.perm_comp_forall₂ (p₁ hc) f₂
        exact ⟨m', a₂, rfl, arr_trans_args args m₁ m' f₁ fm, fun _ => pm.trans (p₂ hc),
          fun h' => absurd hc h'⟩
      · have e₁' := e₁ hc
        have e₂' := e₂ hc
        subst e₁' e₂'
        exact ⟨m₂, m₂, rfl, arr_trans_args args m₁ m₂ f₁ f₂,
          fun h' => absurd h' hc, fun _ => rfl⟩

theorem arr_trans_args : ∀ (l m n : List (ETm A V)), List.Forall₂ (Arr comm) l m →
    List.Forall₂ (Arr comm) m n → List.Forall₂ (Arr comm) l n
  | [], _, _, h1, h2 => by
      cases h1
      exact h2
  | c :: cs, _, _, h1, h2 => by
      cases h1 with
      | cons hcd hrest =>
          cases h2 with
          | cons hde hrest' =>
              exact .cons (arr_trans _ _ _ hcd hde) (arr_trans_args cs _ _ hrest hrest')

end

mutual

theorem arr_symm : ∀ (s t : ETm A V), Arr comm s t → Arr comm t s
  | .atom _, _, h1 => by
      rw [arr_atom] at h1
      subst h1
      simp
  | .var _, _, h1 => by
      rw [arr_var] at h1
      subst h1
      simp
  | .node h args, _, h1 => by
      obtain ⟨m₁, a₁, rfl, f₁, p₁, e₁⟩ := (arr_node comm).mp h1
      have back : List.Forall₂ (Arr comm) m₁ args := arr_symm_args args m₁ f₁
      rw [arr_node]
      by_cases hc : comm h
      · obtain ⟨m', fm, pm⟩ := List.perm_comp_forall₂ (p₁ hc).symm back
        exact ⟨m', args, rfl, fm, fun _ => pm, fun h' => absurd hc h'⟩
      · have e₁' := e₁ hc
        subst e₁'
        exact ⟨args, args, rfl, back, fun h' => absurd h' hc, fun _ => rfl⟩

theorem arr_symm_args : ∀ (l m : List (ETm A V)), List.Forall₂ (Arr comm) l m →
    List.Forall₂ (Arr comm) m l
  | [], _, h1 => by
      cases h1
      exact .nil
  | c :: cs, _, h1 => by
      cases h1 with
      | cons hcd hrest => exact .cons (arr_symm _ _ hcd) (arr_symm_args cs _ hrest)

end

variable [DecidablePred comm]

/-! ### All arrangements, listed -/

mutual

/-- All arrangements of a term. -/
def arrs : ETm A V → List (ETm A V)
  | .atom a => [.atom a]
  | .var v => [.var v]
  | .node h args => (arrsArgs args).flatMap fun m =>
      if comm h then (perms m).map (.node h) else [.node h m]

/-- All argument lists obtained by arranging each argument. -/
def arrsArgs : List (ETm A V) → List (List (ETm A V))
  | [] => [[]]
  | c :: cs => (arrs c).flatMap fun d => (arrsArgs cs).map (d :: ·)

end

mutual

theorem mem_arrs : ∀ (t u : ETm A V), u ∈ arrs comm t ↔ Arr comm t u
  | .atom _, _ => by simp [arrs]
  | .var _, _ => by simp [arrs]
  | .node h args, u => by
      rw [arr_node]
      simp only [arrs, List.mem_flatMap]
      constructor
      · rintro ⟨m, hm, hu⟩
        have f := (mem_arrsArgs args m).mp hm
        by_cases hc : comm h
        · rw [if_pos hc, List.mem_map] at hu
          obtain ⟨l', hl', rfl⟩ := hu
          exact ⟨m, l', rfl, f, fun _ => (mem_perms.mp hl').symm, fun h' => absurd hc h'⟩
        · rw [if_neg hc, List.mem_singleton] at hu
          exact ⟨m, m, hu, f, fun h' => absurd h' hc, fun _ => rfl⟩
      · rintro ⟨m, a', rfl, f, p, e⟩
        refine ⟨m, (mem_arrsArgs args m).mpr f, ?_⟩
        by_cases hc : comm h
        · rw [if_pos hc, List.mem_map]
          exact ⟨a', mem_perms.mpr (p hc).symm, rfl⟩
        · rw [if_neg hc, e hc]
          exact List.mem_singleton_self _

theorem mem_arrsArgs : ∀ (l m : List (ETm A V)), m ∈ arrsArgs comm l ↔
    List.Forall₂ (Arr comm) l m
  | [], m => by cases m <;> simp [arrsArgs]
  | c :: cs, m => by
      simp only [arrsArgs, List.mem_flatMap, List.mem_map]
      constructor
      · rintro ⟨d, hd, ds, hds, rfl⟩
        exact .cons ((mem_arrs c d).mp hd) ((mem_arrsArgs cs ds).mp hds)
      · intro hf
        cases hf with
        | cons hcd hrest =>
            exact ⟨_, (mem_arrs c _).mpr hcd, _, (mem_arrsArgs cs _).mpr hrest, rfl⟩

end

/-! ### Exchanges at a path -/

/-- Exchange arguments `i` and `i + 1` of the node at path `p` when its head is declared; anything
else is unchanged.  A path lists argument positions from the root. -/
def swapAt : List ℕ → ℕ → ETm A V → ETm A V
  | [], i, .node h args => if comm h then .node h (swapAdj i args) else .node h args
  | k :: p, i, .node h args => .node h (args.modify k (swapAt p i))
  | _, _, .atom a => .atom a
  | _, _, .var v => .var v

theorem swapAt_swapAt (p : List ℕ) (i : ℕ) :
    ∀ t : ETm A V, swapAt comm p i (swapAt comm p i t) = t := by
  induction p with
  | nil =>
      intro t
      cases t with
      | atom a => rfl
      | var v => rfl
      | node h args =>
          by_cases hc : comm h
          · simp [swapAt, hc, swapAdj_swapAdj]
          · simp [swapAt, hc]
  | cons k p ih =>
      intro t
      cases t with
      | atom a => rfl
      | var v => rfl
      | node h args =>
          have hid : (swapAt comm p i ∘ swapAt comm p i : ETm A V → ETm A V) = id := funext ih
          simp only [swapAt, List.modify_modify_eq, hid, List.modify_id]

theorem rename_swapAt (f : V → W) (p : List ℕ) (i : ℕ) :
    ∀ t : ETm A V, (swapAt comm p i t).rename f = swapAt comm p i (t.rename f) := by
  induction p with
  | nil =>
      intro t
      cases t with
      | atom a => rfl
      | var v => rfl
      | node h args =>
          by_cases hc : comm h
          · simp [swapAt, hc, map_swapAdj]
          · simp [swapAt, hc]
  | cons k p ih =>
      intro t
      cases t with
      | atom a => rfl
      | var v => rfl
      | node h args =>
          simp only [swapAt, rename_node]
          rw [map_modify (rename f) ih]

theorem arr_swapAt (p : List ℕ) (i : ℕ) : ∀ t : ETm A V, Arr comm t (swapAt comm p i t) := by
  induction p with
  | nil =>
      intro t
      cases t with
      | atom a => simp [swapAt]
      | var v => simp [swapAt]
      | node h args =>
          rw [arr_node]
          by_cases hc : comm h
          · refine ⟨args, swapAdj i args, by simp [swapAt, hc], arr_refl_args comm args,
              fun _ => (swapAdj_perm i args).symm, fun h' => absurd hc h'⟩
          · exact ⟨args, args, by simp [swapAt, hc], arr_refl_args comm args,
              fun h' => absurd h' hc, fun _ => rfl⟩
  | cons k p ih =>
      intro t
      cases t with
      | atom a => simp [swapAt]
      | var v => simp [swapAt]
      | node h args =>
          rw [arr_node]
          have hf := forall₂_modify (arr_refl comm) (g := swapAt comm p i) ih args k
          by_cases hc : comm h
          · exact ⟨_, _, rfl, hf, fun _ => .refl _, fun h' => absurd hc h'⟩
          · exact ⟨_, _, rfl, hf, fun h' => absurd h' hc, fun _ => rfl⟩

/-! ### The positional group -/

/-- The positional group: words in the exchanges at all positions. -/
def Pos (_c : A → Prop) : Type := FreeGroup (List ℕ × ℕ)

instance (c : A → Prop) : Group (Pos c) := inferInstanceAs (Group (FreeGroup (List ℕ × ℕ)))

/-- The exchange at path `p` and index `i`, as an element of the positional group. -/
def gen (c : A → Prop) (p : List ℕ) (i : ℕ) : Pos c := FreeGroup.of (p, i)

/-- Induction over words in the exchanges. -/
@[elab_as_elim]
theorem Pos.induction_on {c : A → Prop} {C : Pos c → Prop} (w : Pos c) (one : C 1)
    (of : ∀ p i, C (gen c p i)) (inv_of : ∀ p i, C (gen c p i) → C (gen c p i)⁻¹)
    (mul : ∀ x y : Pos c, C x → C y → C (x * y)) : C w :=
  FreeGroup.induction_on (C := C) w one (fun g => of g.1 g.2) (fun g => inv_of g.1 g.2) mul

/-- An exchange, as a permutation of terms. -/
def swapPerm (g : List ℕ × ℕ) : Equiv.Perm (ETm A V) :=
  Function.Involutive.toPerm (swapAt comm g.1 g.2) (swapAt_swapAt comm g.1 g.2)

/-- Words act through their exchanges. -/
def posHom : Pos comm →* Equiv.Perm (ETm A V) := FreeGroup.lift (swapPerm comm)

instance {c : A → Prop} [DecidablePred c] : MulAction (Pos c) (ETm A V) :=
  MulAction.compHom (ETm A V) (posHom (V := V) c)

theorem pos_smul_def (w : Pos comm) (t : ETm A V) : w • t = posHom comm w t := rfl

theorem gen_smul (p : List ℕ) (i : ℕ) (t : ETm A V) :
    gen comm p i • t = swapAt comm p i t := by
  rw [pos_smul_def]
  show (FreeGroup.lift (swapPerm comm)) (FreeGroup.of (p, i)) t = _
  rw [FreeGroup.lift_apply_of]
  rfl

theorem gen_inv_smul (p : List ℕ) (i : ℕ) (t : ETm A V) :
    (gen comm p i)⁻¹ • t = swapAt comm p i t := by
  rw [pos_smul_def, map_inv]
  show ((FreeGroup.lift (swapPerm comm)) (FreeGroup.of (p, i)))⁻¹ t = _
  rw [FreeGroup.lift_apply_of, Equiv.Perm.inv_def]
  rw [Equiv.symm_apply_eq]
  exact (swapAt_swapAt comm p i t).symm

/-- **Positions and renamings commute**: a word acts the same before or after a renaming. -/
theorem smul_rename (w : Pos comm) (f : V → W) (t : ETm A V) :
    w • t.rename f = (w • t).rename f := by
  induction w using Pos.induction_on generalizing t with
  | one => simp
  | of p i => rw [gen_smul, gen_smul, rename_swapAt]
  | inv_of p i _ => rw [gen_inv_smul, gen_inv_smul, rename_swapAt]
  | mul x y hx hy => rw [mul_smul, mul_smul, hy, hx]

/-- The product of renamings and positions. -/
abbrev Sym (c : A → Prop) (V : Type*) := Equiv.Perm V × Pos c

/-- **Renamings combined with the argument permutations of declared heads form a group acting on
terms**: `(σ, w)` permutes positions by `w`, then renames by `σ`. -/
instance {c : A → Prop} [DecidablePred c] : MulAction (Sym c V) (ETm A V) where
  smul g t := g.1 • (g.2 • t)
  one_smul t := by
    show (1 : Equiv.Perm V) • ((1 : Pos c) • t) = t
    rw [one_smul, one_smul]
  mul_smul g g' t := by
    show (g.1 * g'.1) • ((g.2 * g'.2) • t) = g.1 • (g.2 • (g'.1 • (g'.2 • t)))
    rw [mul_smul, mul_smul]
    congr 1
    rw [perm_smul_def, perm_smul_def, smul_rename]

theorem sym_smul_def (g : Sym comm V) (t : ETm A V) : g • t = g.1 • (g.2 • t) := rfl

/-! ### The positional orbit is the set of arrangements -/

/-- Every element of the positional orbit is an arrangement. -/
theorem arr_smul (w : Pos comm) : ∀ t : ETm A V, Arr comm t (w • t) := by
  induction w using Pos.induction_on with
  | one => intro t; rw [one_smul]; exact arr_refl comm t
  | of p i => intro t; rw [gen_smul]; exact arr_swapAt comm p i t
  | inv_of p i _ => intro t; rw [gen_inv_smul]; exact arr_swapAt comm p i t
  | mul x y hx hy =>
      intro t
      rw [mul_smul]
      exact arr_trans comm _ _ _ (hy t) (hx _)

/-- A word lifted to act on argument `k`. -/
def liftW (k : ℕ) : Pos comm →* Pos comm := FreeGroup.map (fun g => (k :: g.1, g.2))

omit [DecidablePred comm] in
theorem liftW_gen (k : ℕ) (p : List ℕ) (i : ℕ) :
    liftW comm k (gen comm p i) = gen comm (k :: p) i :=
  FreeGroup.map.of

theorem liftW_smul (k : ℕ) (w : Pos comm) (h : A) (args : List (ETm A V)) :
    liftW comm k w • ETm.node h args = .node h (args.modify k (w • ·)) := by
  induction w using Pos.induction_on generalizing args with
  | one =>
      rw [map_one, one_smul]
      have : ((1 : Pos comm) • · : ETm A V → ETm A V) = id := funext fun t => one_smul _ t
      simp only [this, List.modify_id]
  | of p i =>
      rw [liftW_gen, gen_smul]
      have : (gen comm p i • · : ETm A V → ETm A V) = swapAt comm p i :=
        funext fun t => gen_smul comm p i t
      rw [this]
      rfl
  | inv_of p i _ =>
      rw [map_inv, liftW_gen, gen_inv_smul]
      have : ((gen comm p i)⁻¹ • · : ETm A V → ETm A V) = swapAt comm p i :=
        funext fun t => gen_inv_smul comm p i t
      rw [this]
      rfl
  | mul x y hx hy =>
      rw [map_mul, mul_smul, hy, hx, List.modify_modify_eq]
      congr 2
      funext t
      exact (mul_smul x y t).symm

theorem exists_word_forall₂ (h : A) : ∀ (pre l m : List (ETm A V)),
    List.Forall₂ (fun c d => ∃ w : Pos comm, w • c = d) l m →
    ∃ w : Pos comm, w • ETm.node h (pre ++ l) = .node h (pre ++ m)
  | pre, [], _, hlm => by
      cases hlm
      exact ⟨1, one_smul _ _⟩
  | _, _ :: _, [], hlm => by cases hlm
  | pre, c :: l, d :: m, hlm => by
      cases hlm with
      | cons hcd hrest =>
          obtain ⟨w₁, hw₁⟩ := hcd
          obtain ⟨w₂, hw₂⟩ := exists_word_forall₂ h (pre ++ [d]) l m hrest
          refine ⟨w₂ * liftW comm pre.length w₁, ?_⟩
          rw [mul_smul, liftW_smul, modify_append_length, hw₁]
          simpa using hw₂

theorem exists_word_perm {h : A} (hc : comm h) {l l' : List (ETm A V)} (hp : l.Perm l') :
    ∀ pre : List (ETm A V),
      ∃ w : Pos comm, w • ETm.node h (pre ++ l) = .node h (pre ++ l') := by
  induction hp with
  | nil => exact fun _ => ⟨1, one_smul _ _⟩
  | cons x _ ih =>
      intro pre
      obtain ⟨w, hw⟩ := ih (pre ++ [x])
      exact ⟨w, by simpa using hw⟩
  | swap x y l =>
      intro pre
      refine ⟨gen comm [] pre.length, ?_⟩
      rw [gen_smul]
      simp [swapAt, hc, swapAdj_append]
  | trans _ _ ih₁ ih₂ =>
      intro pre
      obtain ⟨w₁, hw₁⟩ := ih₁ pre
      obtain ⟨w₂, hw₂⟩ := ih₂ pre
      exact ⟨w₂ * w₁, by rw [mul_smul, hw₁, hw₂]⟩

mutual

theorem exists_word_of_arr : ∀ (t u : ETm A V), Arr comm t u → ∃ w : Pos comm, w • t = u
  | .atom _, _, h1 => by
      rw [arr_atom] at h1
      exact ⟨1, by rw [one_smul, h1]⟩
  | .var _, _, h1 => by
      rw [arr_var] at h1
      exact ⟨1, by rw [one_smul, h1]⟩
  | .node h args, _, h1 => by
      obtain ⟨m, a', rfl, f, p, e⟩ := (arr_node comm).mp h1
      obtain ⟨w₁, hw₁⟩ := exists_word_forall₂ comm h [] args m (exists_word_args args m f)
      simp only [List.nil_append] at hw₁
      by_cases hc : comm h
      · obtain ⟨w₂, hw₂⟩ := exists_word_perm comm hc (p hc) []
        simp only [List.nil_append] at hw₂
        exact ⟨w₂ * w₁, by rw [mul_smul, hw₁, hw₂]⟩
      · have e' := e hc
        subst e'
        exact ⟨w₁, hw₁⟩

theorem exists_word_args : ∀ (l m : List (ETm A V)), List.Forall₂ (Arr comm) l m →
    List.Forall₂ (fun c d => ∃ w : Pos comm, w • c = d) l m
  | [], _, h1 => by
      cases h1
      exact .nil
  | c :: cs, _, h1 => by
      cases h1 with
      | cons hcd hrest => exact .cons (exists_word_of_arr _ _ hcd) (exists_word_args cs _ hrest)

end

/-- **The positional orbit is the set of arrangements.** -/
theorem mem_orbit_pos_iff {t u : ETm A V} :
    u ∈ MulAction.orbit (Pos comm) t ↔ Arr comm t u := by
  rw [MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨w, rfl⟩
    exact arr_smul comm w t
  · exact exists_word_of_arr comm t u

theorem arr_rename (f : V → W) {s t : ETm A V} (h : Arr comm s t) :
    Arr comm (s.rename f) (t.rename f) := by
  obtain ⟨w, rfl⟩ := exists_word_of_arr comm s t h
  rw [← smul_rename]
  exact arr_smul comm w _

/-- **The orbit of `s` under renamings and positions**: the variants of its arrangements. -/
theorem mem_orbit_sym_iff [DecidableEq V] {s t : ETm A V} :
    t ∈ MulAction.orbit (Sym comm V) s ↔ ∃ u, Arr comm s u ∧ Variant u t := by
  rw [MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g.2 • s, arr_smul comm g.2 s, variant_iff_exists_perm.mpr ⟨g.1, rfl⟩⟩
  · rintro ⟨u, hu, hv⟩
    obtain ⟨w, rfl⟩ := exists_word_of_arr comm s u hu
    obtain ⟨σ, rfl⟩ := variant_iff_exists_perm.mp hv
    exact ⟨(σ, w), rfl⟩

/-! ### Orbit keys -/

variable [DecidableEq A] [DecidableEq V]

/-- The keys of all arrangements of a term. -/
def orbitKeys (N : Numbering V) (t : ETm A V) : Finset (Tm (Tok A) ℕ) :=
  ((arrs comm t).map (ekey N)).toFinset

theorem mem_orbitKeys {N : Numbering V} {t : ETm A V} {k : Tm (Tok A) ℕ} :
    k ∈ orbitKeys comm N t ↔ ∃ u, Arr comm t u ∧ ekey N u = k := by
  simp [orbitKeys, mem_arrs]

theorem ekey_mem_orbitKeys (N : Numbering V) (t : ETm A V) : ekey N t ∈ orbitKeys comm N t :=
  (mem_orbitKeys comm).mpr ⟨t, arr_refl comm t, rfl⟩

theorem orbitKeys_subset {N : Numbering V} (hsep : Separates N) (hinv : RenameInvariant N)
    {s t : ETm A V} (h : t ∈ MulAction.orbit (Sym comm V) s) :
    orbitKeys comm N s ⊆ orbitKeys comm N t := by
  obtain ⟨u, hu, hv⟩ := (mem_orbit_sym_iff comm).mp h
  obtain ⟨σ, rfl⟩ := variant_iff_exists_perm.mp hv
  intro k hk
  obtain ⟨x, hx, rfl⟩ := (mem_orbitKeys comm).mp hk
  have hux : Arr comm u x := arr_trans comm _ _ _ (arr_symm comm _ _ hu) hx
  exact (mem_orbitKeys comm).mpr ⟨x.rename σ, arr_rename comm σ hux,
    ekey_perm_smul hsep hinv σ x⟩

/-- **Equal orbit keys exactly on orbits** of renamings and argument permutations of declared
heads, for a numbering that separates variables and reads only their pattern. -/
theorem key_eq_iff_orbit {N : Numbering V} (hsep : Separates N) (hinv : RenameInvariant N)
    {s t : ETm A V} :
    orbitKeys comm N s = orbitKeys comm N t ↔ t ∈ MulAction.orbit (Sym comm V) s := by
  constructor
  · intro h
    have hk := ekey_mem_orbitKeys comm N s
    rw [h] at hk
    obtain ⟨u, hu, hk⟩ := (mem_orbitKeys comm).mp hk
    have hst : s ∈ MulAction.orbit (Sym comm V) t :=
      (mem_orbit_sym_iff comm).mpr ⟨u, hu, (ekey_eq_iff_variant hsep hinv).mp hk⟩
    exact MulAction.mem_orbit_symm.mp hst
  · intro h
    exact (orbitKeys_subset comm hsep hinv h).antisymm
      (orbitKeys_subset comm hsep hinv (MulAction.mem_orbit_symm.mp h))

theorem orbitKeys_nonempty (N : Numbering V) (t : ETm A V) : (orbitKeys comm N t).Nonempty :=
  ⟨_, ekey_mem_orbitKeys comm N t⟩

/-- The least key of the arrangements of a term, under a linear order of keys. -/
def orbitKey [LinearOrder (Tm (Tok A) ℕ)] (N : Numbering V) (t : ETm A V) : Tm (Tok A) ℕ :=
  (orbitKeys comm N t).min' (orbitKeys_nonempty comm N t)

/-- **One key per orbit**: the least key of the arrangements, under any linear order of keys. -/
theorem orbitKey_eq_iff_orbit [LinearOrder (Tm (Tok A) ℕ)] {N : Numbering V}
    (hsep : Separates N) (hinv : RenameInvariant N) {s t : ETm A V} :
    orbitKey comm N s = orbitKey comm N t ↔ t ∈ MulAction.orbit (Sym comm V) s := by
  constructor
  · intro h
    have hs := (orbitKeys comm N s).min'_mem (orbitKeys_nonempty comm N s)
    have ht := (orbitKeys comm N t).min'_mem (orbitKeys_nonempty comm N t)
    change orbitKey comm N s ∈ _ at hs
    change orbitKey comm N t ∈ _ at ht
    rw [h] at hs
    obtain ⟨u, hu, hku⟩ := (mem_orbitKeys comm).mp hs
    obtain ⟨u', hu', hku'⟩ := (mem_orbitKeys comm).mp ht
    have hv : Variant u u' := (ekey_eq_iff_variant hsep hinv).mp (hku.trans hku'.symm)
    have h1 : u' ∈ MulAction.orbit (Sym comm V) s := (mem_orbit_sym_iff comm).mpr ⟨u, hu, hv⟩
    have h2 : t ∈ MulAction.orbit (Sym comm V) u' :=
      (mem_orbit_sym_iff comm).mpr ⟨t, arr_symm comm _ _ hu', variant_refl t⟩
    rw [MulAction.orbit_eq_iff.mpr h1] at h2
    exact h2
  · intro h
    unfold orbitKey
    congr 1
    exact (key_eq_iff_orbit comm hsep hinv).mpr h

open Classical in
/-- **One key per orbit**: a finite set of terms has as many orbit keys as the orbits it meets. -/
theorem card_orbitKeys_eq_card_orbits {N : Numbering V} (hsep : Separates N)
    (hinv : RenameInvariant N) (S : Finset (ETm A V)) :
    (S.image (orbitKeys comm N)).card =
      (S.image (Quotient.mk (MulAction.orbitRel (Sym comm V) (ETm A V)))).card := by
  have hresp : ∀ a b : ETm A V, (MulAction.orbitRel (Sym comm V) (ETm A V)) a b →
      orbitKeys comm N a = orbitKeys comm N b := fun a b hab =>
    (key_eq_iff_orbit comm hsep hinv).mpr (MulAction.mem_orbit_symm.mp hab)
  have hinj : Function.Injective (Quotient.lift (s := MulAction.orbitRel (Sym comm V) (ETm A V))
      (orbitKeys comm N) hresp) := by
    intro x y hxy
    induction x using Quotient.inductionOn
    induction y using Quotient.inductionOn
    exact Quotient.sound (MulAction.mem_orbit_symm.mp ((key_eq_iff_orbit comm hsep hinv).mp hxy))
  have hfactor : S.image (orbitKeys comm N) =
      (S.image (Quotient.mk (MulAction.orbitRel (Sym comm V) (ETm A V)))).image
        (Quotient.lift (s := MulAction.orbitRel (Sym comm V) (ETm A V)) (orbitKeys comm N)
          hresp) := by
    rw [Finset.image_image]
    rfl
  rw [hfactor, Finset.card_image_of_injective _ hinj]

end ETm

/-! ### Controls -/

namespace OrbitControls

open ETm

/-- `bag` is declared unordered; every other head keeps its argument order. -/
def declared (h : String) : Prop := h = "bag"

instance : DecidablePred declared := fun h => inferInstanceAs (Decidable (h = "bag"))

/-- The two kinds of symmetry together: `(bag (g $x) (h $y))` and `(bag (h $b) (g $a))`. -/
theorem bag_one_orbit :
    (ETm.node "bag" [.node "h" [.var "b"], .node "g" [.var "a"]] : ETm String String) ∈
      MulAction.orbit (Sym declared String)
        (ETm.node "bag" [.node "g" [.var "x"], .node "h" [.var "y"]]) :=
  (key_eq_iff_orbit declared idxOf_separates idxOf_renameInvariant).mp (by decide)

/-- At depth: `(f (bag a b) c)` and `(f (bag b a) c)`. -/
theorem nested_one_orbit :
    (ETm.node "f" [.node "bag" [.atom "b", .atom "a"], .atom "c"] : ETm String String) ∈
      MulAction.orbit (Sym declared String)
        (ETm.node "f" [.node "bag" [.atom "a", .atom "b"], .atom "c"]) :=
  (key_eq_iff_orbit declared idxOf_separates idxOf_renameInvariant).mp (by decide)

/-- A head that is not declared keeps its order: `(pair (g $x) (h $y))` and
`(pair (h $b) (g $a))` are in two orbits. -/
theorem pair_two_orbits :
    (ETm.node "pair" [.node "h" [.var "b"], .node "g" [.var "a"]] : ETm String String) ∉
      MulAction.orbit (Sym declared String)
        (ETm.node "pair" [.node "g" [.var "x"], .node "h" [.var "y"]]) := by
  rw [← key_eq_iff_orbit declared idxOf_separates idxOf_renameInvariant]
  decide

/-- A bag counts its members: `(bag a a b)` and `(bag a b)` are in two orbits. -/
theorem bag_counts :
    (ETm.node "bag" [.atom "a", .atom "b"] : ETm String String) ∉
      MulAction.orbit (Sym declared String) (ETm.node "bag" [.atom "a", .atom "a", .atom "b"]) := by
  rw [← key_eq_iff_orbit declared idxOf_separates idxOf_renameInvariant]
  decide

/-- Renaming keeps the pattern of variables: `(bag (g $x) (g $x))` and `(bag (g $x) (g $y))`
are in two orbits. -/
theorem bag_keeps_links :
    (ETm.node "bag" [.node "g" [.var "x"], .node "g" [.var "y"]] : ETm String String) ∉
      MulAction.orbit (Sym declared String)
        (ETm.node "bag" [.node "g" [.var "x"], .node "g" [.var "x"]]) := by
  rw [← key_eq_iff_orbit declared idxOf_separates idxOf_renameInvariant]
  decide

end OrbitControls

end Mettapedia.InformationTheory.SymmetryKeys
