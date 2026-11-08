import Mathlib.Tactic

/-!
# Certificates that record their dependencies

A compiled route is licensed by a certificate issued under the declarations of the
moment.  More declarations are more knowledge: they may license new routes, and they
should take away only the routes whose license they bear on.  A certificate therefore
records what its route actually read: the heads it depends on, and what the declarations
said about each of them.

**What a head's declarations say** (`viewOf`): its type rows as a set, since rows that
repeat one type are one declaration; and the equations that bear on it as a multiset,
since a repeated equation answers again.  An equation whose head is a variable bears on
every head.

**Validity** (`Certificate.Valid`): every head the route depends on reads as it did when
the certificate was issued.  This file proves:
* `valid_sound`: under any meaning that reads only the views of the route's heads
  (`ReadsOnly`), a valid certificate's route still has the general meaning;
* `valid_append_unrelated`: a row that bears on none of the route's heads leaves the
  certificate valid;
* `valid_append_duplicate_decl`: a type row the environment already has leaves it valid;
* `invalid_append_catchall`: an equation whose head is a variable invalidates every
  certificate with a dependency; `invalid_append_eqn` and `invalid_append_new_decl`: so do
  a further equation and a new type of a head the route reads.

**The routes the optimizer may take** (`best`): the general route, always valid, and every
route whose certificate is valid; it takes the cheapest.  `best_le_general`: never above
the general route; `best_correct`: whatever it takes has the general meaning;
`best_append_unrelated`, `best_append_duplicate_decl`: an unrelated row or a repeated type
row leaves the best route where it was; `best_more_routes`: a new certificate never
raises the cost.  Knowledge never forces the optimizer off a valid route.

**Controls**, with the answers of a call (`answers`: each equation of the head once per
distinct type row, or once when untyped), as CeTTa's PeTTa lane answers them: a repeated
type row keeps the answers (`duplicate_decl_keeps_answers`); a distinct type row doubles
them (`distinct_decl_changes_answers`); a catch-all equation adds one
(`catchall_changes_answers`); so the certificate's view is no coarser than the meaning
allows.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.RouteCertificates

variable {H : Type} [DecidableEq H]

/-- Declaration rows over heads `H`: a type row `(: f T)` and an equation `(= (f …) b)`;
an equation whose head is a variable is `eqn none b`. -/
inductive Row (H : Type) where
  | decl (f : H) (ty : ℕ)
  | eqn (f : Option H) (body : ℕ)
  deriving DecidableEq

/-- Whether a row bears on a head. -/
def Row.bears : Row H → H → Bool
  | .decl f _, g => decide (f = g)
  | .eqn (some f) _, g => decide (f = g)
  | .eqn none _, _ => true

/-- What declarations say about a head: its types as a set, its equations as a
multiset. -/
structure View where
  types : Finset ℕ
  bodies : Multiset ℕ
  deriving DecidableEq

/-- The type of a row, when it is a type row of `f`. -/
def Row.typeOf (f : H) : Row H → Option ℕ
  | .decl g t => if g = f then some t else none
  | .eqn _ _ => none

/-- The body of a row, when it is an equation bearing on `f`. -/
def Row.bodyOf (f : H) : Row H → Option ℕ
  | .decl _ _ => none
  | .eqn (some g) b => if g = f then some b else none
  | .eqn none b => some b

/-- What an environment says about a head. -/
def viewOf (Γ : List (Row H)) (f : H) : View :=
  ⟨(Γ.filterMap (Row.typeOf f)).toFinset, ((Γ.filterMap (Row.bodyOf f) : List ℕ) : Multiset ℕ)⟩

theorem typeOf_none_of_not_bears {r : Row H} {f : H} (h : r.bears f = false) :
    r.typeOf f = none := by
  cases r with
  | decl g t => simp only [Row.bears, decide_eq_false_iff_not] at h; simp [Row.typeOf, h]
  | eqn g b => rfl

theorem bodyOf_none_of_not_bears {r : Row H} {f : H} (h : r.bears f = false) :
    r.bodyOf f = none := by
  cases r with
  | decl g t => rfl
  | eqn g b =>
    cases g with
    | none => simp [Row.bears] at h
    | some g => simp only [Row.bears, decide_eq_false_iff_not] at h; simp [Row.bodyOf, h]

/-- A row that does not bear on `f` leaves what the environment says about `f` alone. -/
theorem viewOf_append_not_bears (Γ : List (Row H)) (r : Row H) (f : H)
    (h : r.bears f = false) : viewOf (Γ ++ [r]) f = viewOf Γ f := by
  simp [viewOf, List.filterMap_append, typeOf_none_of_not_bears h, bodyOf_none_of_not_bears h]

/-- A type row the environment already has does not change any view. -/
theorem viewOf_append_duplicate_decl (Γ : List (Row H)) (g : H) (t : ℕ)
    (hmem : Row.decl g t ∈ Γ) (f : H) : viewOf (Γ ++ [.decl g t]) f = viewOf Γ f := by
  by_cases hgf : g = f
  · subst hgf
    have ht : t ∈ (Γ.filterMap (Row.typeOf g)).toFinset := by
      simp only [List.mem_toFinset, List.mem_filterMap]
      exact ⟨_, hmem, by simp [Row.typeOf]⟩
    simp only [viewOf, List.filterMap_append, List.filterMap_cons, List.filterMap_nil,
      Row.typeOf, Row.bodyOf, if_true, List.append_nil, View.mk.injEq, and_true]
    rw [List.toFinset_append]
    simp [Finset.insert_eq_of_mem ht]
  · exact viewOf_append_not_bears Γ _ f (by simp [Row.bears, hgf])

/-! ## Certificates -/

/-- A certificate: the heads its route read, and what each of them said. -/
structure Certificate (H : Type) where
  deps : List H
  seen : H → View

/-- The certificate issued under `Γ` for a route reading `deps`. -/
def issue (Γ : List (Row H)) (deps : List H) : Certificate H := ⟨deps, viewOf Γ⟩

/-- Every head the route read reads as it did. -/
def Certificate.Valid (c : Certificate H) (Γ : List (Row H)) : Prop :=
  ∀ f ∈ c.deps, viewOf Γ f = c.seen f

instance (c : Certificate H) (Γ : List (Row H)) : Decidable (c.Valid Γ) := by
  unfold Certificate.Valid
  infer_instance

theorem issue_valid (Γ : List (Row H)) (deps : List H) : (issue Γ deps).Valid Γ :=
  fun _ _ => rfl

/-- A meaning that reads only the views of `deps`. -/
def ReadsOnly {M : Type} (meaning : List (Row H) → M) (deps : List H) : Prop :=
  ∀ Γ Γ', (∀ f ∈ deps, viewOf Γ f = viewOf Γ' f) → meaning Γ = meaning Γ'

/-- **A valid certificate is sound**: the route issued under `Γ₀` still has the meaning
the general route gives under `Γ`. -/
theorem valid_sound {M : Type} (meaning : List (Row H) → M) (deps : List H)
    (hr : ReadsOnly meaning deps) (Γ₀ Γ : List (Row H)) (hv : (issue Γ₀ deps).Valid Γ) :
    meaning Γ₀ = meaning Γ :=
  hr Γ₀ Γ fun f hf => (hv f hf).symm

/-- A row that bears on none of the route's heads leaves its certificate valid. -/
theorem valid_append_unrelated (c : Certificate H) (Γ : List (Row H)) (r : Row H)
    (hv : c.Valid Γ) (hr : ∀ f ∈ c.deps, r.bears f = false) : c.Valid (Γ ++ [r]) :=
  fun f hf => (viewOf_append_not_bears Γ r f (hr f hf)).trans (hv f hf)

/-- A type row the environment already has leaves every certificate valid. -/
theorem valid_append_duplicate_decl (c : Certificate H) (Γ : List (Row H)) (g : H) (t : ℕ)
    (hmem : Row.decl g t ∈ Γ) (hv : c.Valid Γ) : c.Valid (Γ ++ [.decl g t]) :=
  fun f hf => (viewOf_append_duplicate_decl Γ g t hmem f).trans (hv f hf)

theorem bodies_append (Γ : List (Row H)) (r : Row H) (f : H) :
    (viewOf (Γ ++ [r]) f).bodies =
      (viewOf Γ f).bodies + (((r.bodyOf f).toList : List ℕ) : Multiset ℕ) := by
  simp only [viewOf, List.filterMap_append, Multiset.coe_add]
  cases h : r.bodyOf f <;> simp [h]

/-- An equation bearing on a head the route read invalidates the certificate: the head's
equations grow. -/
theorem invalid_append_eqn (c : Certificate H) (Γ : List (Row H)) (g : Option H) (b : ℕ)
    (hv : c.Valid Γ) (f : H) (hf : f ∈ c.deps) (hb : (Row.eqn g b).bears f = true) :
    ¬ c.Valid (Γ ++ [.eqn g b]) := by
  intro hv'
  have h1 := hv' f hf
  rw [← hv f hf] at h1
  have h2 := congrArg View.bodies h1
  rw [bodies_append] at h2
  have hbody : (Row.eqn g b).bodyOf f = some b := by
    cases g with
    | none => rfl
    | some g => simp only [Row.bears, decide_eq_true_eq] at hb; simp [Row.bodyOf, hb]
  rw [hbody] at h2
  have := congrArg Multiset.card h2
  simp at this

/-- **A catch-all equation invalidates every certificate with a dependency.** -/
theorem invalid_append_catchall (c : Certificate H) (Γ : List (Row H)) (b : ℕ)
    (hv : c.Valid Γ) (hdeps : c.deps ≠ []) : ¬ c.Valid (Γ ++ [.eqn none b]) := by
  obtain ⟨f, hf⟩ := List.exists_mem_of_ne_nil _ hdeps
  exact invalid_append_eqn c Γ none b hv f hf rfl

/-- A type row new to a head the route read invalidates the certificate. -/
theorem invalid_append_new_decl (c : Certificate H) (Γ : List (Row H)) (f : H) (t : ℕ)
    (hv : c.Valid Γ) (hf : f ∈ c.deps) (hnew : t ∉ (viewOf Γ f).types) :
    ¬ c.Valid (Γ ++ [.decl f t]) := by
  intro hv'
  have h1 := hv' f hf
  rw [← hv f hf] at h1
  have h2 := congrArg View.types h1
  have ht : t ∈ (viewOf (Γ ++ [.decl f t]) f).types := by
    simp [viewOf, List.filterMap_append, Row.typeOf]
  rw [h2] at ht
  exact hnew ht

/-! ## The routes the optimizer may take -/

/-- A compiled route: its meaning, its cost, and its certificate. -/
structure Route (M : Type) (H : Type) where
  meaning : M
  cost : ℕ
  cert : Certificate H

/-- The cost of the cheapest route available under `Γ`: the general route, at `general`,
or any route whose certificate is valid. -/
def best {M : Type} (general : ℕ) (routes : List (Route M H)) (Γ : List (Row H)) : ℕ :=
  ((routes.filter fun r => decide (r.cert.Valid Γ)).map Route.cost).foldr min general

theorem foldr_min_le_init (l : List ℕ) (g : ℕ) : l.foldr min g ≤ g := by
  induction l with
  | nil => exact le_rfl
  | cons a l ih => exact (min_le_right _ _).trans ih

theorem foldr_min_le_mem (l : List ℕ) (g : ℕ) {a : ℕ} (ha : a ∈ l) : l.foldr min g ≤ a := by
  induction l with
  | nil => simp at ha
  | cons b l ih =>
    rcases List.mem_cons.mp ha with rfl | ha
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (ih ha)

theorem foldr_min_mem (l : List ℕ) (g : ℕ) : l.foldr min g = g ∨ l.foldr min g ∈ l := by
  induction l with
  | nil => exact Or.inl rfl
  | cons b l ih =>
    simp only [List.foldr_cons]
    rcases le_total b (l.foldr min g) with h | h
    · right; rw [min_eq_left h]; simp
    · rw [min_eq_right h]
      rcases ih with h' | h'
      · exact Or.inl h'
      · right; exact List.mem_cons_of_mem _ h'

theorem foldr_min_mono {l l' : List ℕ} (g : ℕ) (h : ∀ a ∈ l, a ∈ l') :
    l'.foldr min g ≤ l.foldr min g := by
  rcases foldr_min_mem l g with h' | h'
  · rw [h']; exact foldr_min_le_init l' g
  · exact foldr_min_le_mem l' g (h _ h')

/-- Never above the general route. -/
theorem best_le_general {M : Type} (general : ℕ) (routes : List (Route M H))
    (Γ : List (Row H)) : best general routes Γ ≤ general :=
  foldr_min_le_init _ _

/-- The cheapest available route is the general one or a route whose certificate is
valid. -/
theorem best_mem {M : Type} (general : ℕ) (routes : List (Route M H)) (Γ : List (Row H)) :
    best general routes Γ = general ∨
      ∃ r ∈ routes, r.cert.Valid Γ ∧ r.cost = best general routes Γ := by
  unfold best
  have key : ∀ l : List ℕ, (∀ a ∈ l, ∃ r ∈ routes, r.cert.Valid Γ ∧ r.cost = a) →
      l.foldr min general = general ∨
        ∃ r ∈ routes, r.cert.Valid Γ ∧ r.cost = l.foldr min general := by
    intro l hl
    rcases foldr_min_mem l general with h | h
    · exact Or.inl h
    · obtain ⟨r, hr, hv, hc⟩ := hl _ h
      exact Or.inr ⟨r, hr, hv, hc⟩
  apply key
  intro a ha
  simp only [List.mem_map, List.mem_filter, decide_eq_true_eq] at ha
  obtain ⟨r, ⟨hr, hv⟩, rfl⟩ := ha
  exact ⟨r, hr, hv, rfl⟩

/-- **Whatever the optimizer takes has the general meaning**: the general route, or a
route whose valid certificate was issued for a meaning that reads only its heads. -/
theorem best_correct {M : Type} (meaning : List (Row H) → M) (general : ℕ)
    (routes : List (Route M H))
    (hissued : ∀ r ∈ routes, ∃ Γ₀, r.cert = issue Γ₀ r.cert.deps ∧ r.meaning = meaning Γ₀ ∧
      ReadsOnly meaning r.cert.deps)
    (Γ : List (Row H)) :
    best general routes Γ = general ∨
      ∃ r ∈ routes, r.cert.Valid Γ ∧ r.cost = best general routes Γ ∧ r.meaning = meaning Γ := by
  rcases best_mem general routes Γ with h | ⟨r, hr, hv, hc⟩
  · exact Or.inl h
  · right
    obtain ⟨Γ₀, hcert, hm, hreads⟩ := hissued r hr
    refine ⟨r, hr, hv, hc, ?_⟩
    rw [hm]
    rw [hcert] at hv
    exact valid_sound meaning _ hreads Γ₀ Γ hv

/-- An unrelated row leaves the cheapest route where it was. -/
theorem best_append_unrelated {M : Type} (general : ℕ) (routes : List (Route M H))
    (Γ : List (Row H)) (row : Row H)
    (hrow : ∀ r ∈ routes, ∀ f ∈ r.cert.deps, row.bears f = false) :
    best general routes (Γ ++ [row]) = best general routes Γ := by
  unfold best
  congr 2
  apply List.filter_congr
  intro r hr
  simp only [decide_eq_decide]
  constructor
  · intro hv f hf
    rw [← viewOf_append_not_bears Γ row f (hrow r hr f hf)]
    exact hv f hf
  · intro hv
    exact valid_append_unrelated r.cert Γ row hv (hrow r hr)

/-- A repeated type row leaves the cheapest route where it was. -/
theorem best_append_duplicate_decl {M : Type} (general : ℕ) (routes : List (Route M H))
    (Γ : List (Row H)) (g : H) (t : ℕ) (hmem : Row.decl g t ∈ Γ) :
    best general routes (Γ ++ [.decl g t]) = best general routes Γ := by
  unfold best
  congr 2
  apply List.filter_congr
  intro r _
  simp only [decide_eq_decide]
  constructor
  · intro hv f hf
    rw [← viewOf_append_duplicate_decl Γ g t hmem f]
    exact hv f hf
  · intro hv
    exact valid_append_duplicate_decl r.cert Γ g t hmem hv

/-- **More knowledge, more routes**: a new certificate never raises the cost. -/
theorem best_more_routes {M : Type} (general : ℕ) (routes : List (Route M H))
    (extra : Route M H) (Γ : List (Row H)) :
    best general (extra :: routes) Γ ≤ best general routes Γ := by
  unfold best
  apply foldr_min_mono
  intro a ha
  simp only [List.mem_map, List.mem_filter] at ha ⊢
  obtain ⟨r, ⟨hr, hv⟩, rfl⟩ := ha
  exact ⟨r, ⟨List.mem_cons_of_mem _ hr, hv⟩, rfl⟩

/-! ## Controls: the answers of a call -/

/-- The answers of a call of `f`: each equation bearing on `f` once for each distinct type
row of `f`, or once when `f` is untyped. -/
def answers (Γ : List (Row H)) (f : H) : Multiset ℕ :=
  if (viewOf Γ f).types = ∅ then (viewOf Γ f).bodies
  else (viewOf Γ f).types.card • (viewOf Γ f).bodies

theorem answers_readsOnly (f : H) : ReadsOnly (fun Γ => answers Γ f) [f] := by
  intro Γ Γ' h
  have := h f (by simp)
  simp only [answers, this]

namespace Controls

/-- `myf`, `g2`, `app`. -/
abbrev myf : ℕ := 0
abbrev g2 : ℕ := 1
abbrev app : ℕ := 2

/-- `(: myf (-> Number Number))` and `(= (myf $x) (+ $x 1))`. -/
def base : List (Row ℕ) := [.decl myf 0, .eqn (some myf) 7]

theorem duplicate_decl_keeps_answers :
    answers (base ++ [.decl myf 0]) myf = answers base myf ∧ answers base myf = {7} := by
  decide

/-- A distinct type row doubles the answers, as `distinct_declaration_rows` shows. -/
theorem distinct_decl_changes_answers :
    answers (base ++ [.decl myf 1]) myf = {7, 7} := by
  decide

/-- An equation whose head is a variable answers for every head. -/
theorem catchall_changes_answers :
    answers (base ++ [.eqn none 9]) myf = {7, 9} ∧
      answers (base ++ [.eqn none 9]) app = {9} ∧ answers base app = 0 := by
  decide

/-- A route for `myf` issued under `base`: valid after a repeated type row or a row of
`app`, refused after a distinct type row of `myf` or a catch-all equation. -/
theorem certificate_controls :
    (issue base [myf]).Valid (base ++ [.decl myf 0]) ∧
      (issue base [myf]).Valid (base ++ [.eqn (some app) 3]) ∧
      ¬ (issue base [myf]).Valid (base ++ [.decl myf 1]) ∧
      ¬ (issue base [myf]).Valid (base ++ [.eqn none 9]) := by
  decide

end Controls

end Mettapedia.Machines.RouteCertificates
