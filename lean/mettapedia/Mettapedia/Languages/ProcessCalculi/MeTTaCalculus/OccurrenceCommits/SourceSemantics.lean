import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.SourceCompilation

/-!
# The rows of a transform without a matcher, and agreement up to the theory

`SourceCompilation` enumerates rows through a matcher. This module says what the rows are without
one, and proves that a sound, complete and minimal matcher computes exactly them, each model-level
row once.

## Declarative rows

* A source steps from a substitution (`DStep`) when it picks an occurrence of the store whose label
  its pattern solves modulo `E` (read, take), finds its **semantic region** empty (absent), finds
  exactly one occurrence there (unique), or folds the whole region into a value its collection
  pattern solves (all); `let` takes a computed value. The semantic region (`semRegion`) is the set
  of values some step of the pattern reaches: no algorithm is involved.
* A row of a source list (`DRow`) chains such steps and ends with the template instantiated. An
  `every` suffix is one row whose footprint sums the footprints of a **transversal** of the
  suffix's linear rows (`Transversal`): one representative of each model-level row, every such row
  represented, none twice. Rows are compared modulo `E` (`RowEquiv`): `E`-equivalent
  substitutions, the same picks, made labels related by `E`.
* Absence of a source query means that no declarative inner row exists. It keeps
  the complete observation footprint and passes the original bindings to its
  continuation. Nested absence uses the same rule.

## Agreement (`agreement`)

For a matcher that is sound, complete and minimal, and `let` computations that respect `E`
(`Respects`):

* **soundness**: every computed row is a declarative row;
* **completeness**: every declarative row from an `E`-equivalent start is `E`-equivalent to a
  computed row;
* **minimality**: no two computed rows are `E`-equivalent.

Together: the computed rows are a transversal of the declarative ones, so the `every` footprint the
compiler builds is the declarative one up to `E` on what it makes (`every_footprint_agrees`), and a
transform fires exactly the commits of the declarative linear rows, up to `E` on made labels
(`declarative_of_fires`, `fires_of_declarative`). Without completeness or minimality the agreement fails:
`SourceControls` shows an incomplete matcher missing a row and a redundant one counting a row
twice.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources

universe uO uV uT uP

variable {O : Type uO} {V : Type uV} {T : Type uT} {P : Type uP}

/-! ## Equivalence modulo the theory -/

section Equivalences

variable (L : TermLayer V T P)

/-- Bags of values related by `E`, element by element. -/
theorem multisetRel_refl (s : Multiset T) : Multiset.Rel L.E s s :=
  Multiset.rel_refl_of_refl_on fun x _ => L.equivalence.refl x

variable {L}

theorem multisetRel_symm {s t : Multiset T} (rel : Multiset.Rel L.E s t) : Multiset.Rel L.E t s := by
  rw [← Multiset.rel_flip]
  exact rel.mono fun a _ b _ h => L.equivalence.symm h

theorem multisetRel_trans {s t u : Multiset T} (first : Multiset.Rel L.E s t)
    (second : Multiset.Rel L.E t u) : Multiset.Rel L.E s u :=
  haveI : IsTrans T L.E := ⟨fun _ _ _ => L.equivalence.trans⟩
  Multiset.Rel.trans L.E first second

theorem multisetRel_of_forall₂ {l l' : List T} (rel : List.Forall₂ L.E l l') :
    Multiset.Rel L.E (l : Multiset T) (l' : Multiset T) := by
  induction rel with
  | nil => exact Multiset.Rel.zero
  | cons head _ ih => exact Multiset.Rel.cons head ih

variable (L)

/-- Footprints equal up to `E` on what they make. -/
def FootprintEquiv (fp fp' : Footprint O T) : Prop :=
  fp.takes = fp'.takes ∧ fp.keeps = fp'.keeps ∧ fp.queries = fp'.queries ∧
    Multiset.Rel L.E fp.makes fp'.makes

/-- A pick without what it makes. -/
def Pick.strip : Pick O T → Pick O T
  | .make _ => .make 0
  | .amalgam fp => .amalgam ⟨fp.takes, fp.keeps, fp.queries, 0⟩
  | pick => pick

/-- What a pick makes. -/
def Pick.makes : Pick O T → Multiset T
  | .make labels => labels
  | .amalgam fp => fp.makes
  | _ => 0

/-- Picks equal up to `E` on what they make. -/
def PickEquiv (a b : Pick O T) : Prop := a.strip = b.strip ∧ Multiset.Rel L.E a.makes b.makes

/-- **Rows equal modulo the theory**: `E`-equivalent substitutions and picks. -/
def RowEquiv (x y : Subst V T × List (Pick O T)) : Prop :=
  SubstEquiv L.E x.1 y.1 ∧ List.Forall₂ (PickEquiv L) x.2 y.2

/-- Steps equal modulo the theory. -/
def StepEquiv (x y : Subst V T × Pick O T) : Prop := SubstEquiv L.E x.1 y.1 ∧ PickEquiv L x.2 y.2

theorem pickEquiv_equivalence : Equivalence (PickEquiv (O := O) L) :=
  ⟨fun _ => ⟨rfl, multisetRel_refl L _⟩, fun h => ⟨h.1.symm, multisetRel_symm h.2⟩,
    fun h k => ⟨h.1.trans k.1, multisetRel_trans h.2 k.2⟩⟩

theorem forall₂_trans {α : Type*} {r : α → α → Prop} (trans : ∀ a b c, r a b → r b c → r a c) :
    ∀ {l₁ l₂ l₃ : List α}, List.Forall₂ r l₁ l₂ → List.Forall₂ r l₂ l₃ → List.Forall₂ r l₁ l₃
  | [], [], [], .nil, .nil => .nil
  | _ :: _, _ :: _, _ :: _, .cons h t, .cons h' t' => .cons (trans _ _ _ h h') (forall₂_trans trans t t')

theorem forall₂_equivalence {α : Type*} {r : α → α → Prop} (equivalence : Equivalence r) :
    Equivalence (List.Forall₂ r) := by
  refine ⟨fun l => ?_, fun h => ?_, fun h k => ?_⟩
  · induction l with
    | nil => exact List.Forall₂.nil
    | cons x rest ih => exact List.Forall₂.cons (equivalence.refl x) ih
  · induction h with
    | nil => exact List.Forall₂.nil
    | cons head _ ih => exact List.Forall₂.cons (equivalence.symm head) ih
  · exact forall₂_trans (r := r) (fun _ _ _ first second => equivalence.trans first second) h k

theorem rowEquiv_equivalence : Equivalence (RowEquiv (O := O) L) :=
  ⟨fun _ => ⟨SubstEquiv.refl L.equivalence _, (forall₂_equivalence (pickEquiv_equivalence L)).refl _⟩,
    fun h => ⟨SubstEquiv.symm L.equivalence h.1, (forall₂_equivalence (pickEquiv_equivalence L)).symm h.2⟩,
    fun h k => ⟨SubstEquiv.trans L.equivalence h.1 k.1,
      (forall₂_equivalence (pickEquiv_equivalence L)).trans h.2 k.2⟩⟩

theorem stepEquiv_equivalence : Equivalence (StepEquiv (O := O) L) :=
  ⟨fun _ => ⟨SubstEquiv.refl L.equivalence _, (pickEquiv_equivalence L).refl _⟩,
    fun h => ⟨SubstEquiv.symm L.equivalence h.1, (pickEquiv_equivalence L).symm h.2⟩,
    fun h k => ⟨SubstEquiv.trans L.equivalence h.1 k.1, (pickEquiv_equivalence L).trans h.2 k.2⟩⟩

/-- The rows modulo the theory. -/
def rowSetoid : Setoid (Subst V T × List (Pick O T)) := ⟨RowEquiv L, rowEquiv_equivalence L⟩

/-- The steps modulo the theory. -/
def stepSetoid : Setoid (Subst V T × Pick O T) := ⟨StepEquiv L, stepEquiv_equivalence L⟩

variable {L}

theorem stepEquiv_of_mk_eq {x y : Subst V T × Pick O T}
    (same : Quotient.mk (stepSetoid L) x = Quotient.mk (stepSetoid L) y) : StepEquiv L x y :=
  Quotient.exact same

theorem rowEquiv_of_mk_eq {x y : Subst V T × List (Pick O T)}
    (same : Quotient.mk (rowSetoid L) x = Quotient.mk (rowSetoid L) y) : RowEquiv L x y :=
  Quotient.exact same

theorem mk_eq_of_rowEquiv {x y : Subst V T × List (Pick O T)} (equiv : RowEquiv L x y) :
    Quotient.mk (rowSetoid L) x = Quotient.mk (rowSetoid L) y :=
  Quotient.sound equiv

theorem pickEquiv_iff_eq_of_no_makes {a b : Pick O T} (sa : a.strip = a) (sb : b.strip = b)
    (ma : a.makes = 0) (mb : b.makes = 0) : PickEquiv L a b ↔ a = b := by
  constructor
  · rintro ⟨strip, -⟩
    rw [← sa, ← sb, strip]
  · rintro rfl
    exact ⟨rfl, by rw [ma]; exact Multiset.Rel.zero⟩

theorem footprint_strip (a : Pick O T) :
    a.strip.footprint.takes = a.footprint.takes ∧ a.strip.footprint.keeps = a.footprint.keeps ∧
      a.strip.footprint.queries = a.footprint.queries := by
  cases a <;> simp [Pick.strip, Pick.footprint]

theorem footprint_makes (a : Pick O T) : a.footprint.makes = a.makes := by
  cases a <;> simp [Pick.makes, Pick.footprint]

theorem PickEquiv.footprint {a b : Pick O T} (equiv : PickEquiv L a b) :
    FootprintEquiv L a.footprint b.footprint := by
  obtain ⟨strip, makes⟩ := equiv
  obtain ⟨ta, ka, ra⟩ := footprint_strip a
  obtain ⟨tb, kb, rb⟩ := footprint_strip b
  rw [strip] at ta ka ra
  refine ⟨ta.symm.trans tb, ka.symm.trans kb, ra.symm.trans rb, ?_⟩
  rw [footprint_makes, footprint_makes]
  exact makes

theorem FootprintEquiv.add {a b a' b' : Footprint O T} (first : FootprintEquiv L a a')
    (second : FootprintEquiv L b b') : FootprintEquiv L (a + b) (a' + b') := by
  obtain ⟨t, k, r, m⟩ := first
  obtain ⟨t', k', r', m'⟩ := second
  exact ⟨by simp [t, t'], by simp [k, k'], by simp [r, r'], Multiset.Rel.add m m'⟩

theorem FootprintEquiv.refl (fp : Footprint O T) : FootprintEquiv L fp fp :=
  ⟨rfl, rfl, rfl, multisetRel_refl L _⟩

theorem footprintOf_equiv {l l' : List (Pick O T)} (equiv : List.Forall₂ (PickEquiv L) l l') :
    FootprintEquiv L (footprintOf l) (footprintOf l') := by
  induction equiv with
  | nil => exact FootprintEquiv.refl _
  | cons head _ ih =>
      rw [footprintOf_cons, footprintOf_cons]
      exact head.footprint.add ih

theorem FootprintEquiv.linear_iff {fp fp' : Footprint O T} (equiv : FootprintEquiv L fp fp') :
    fp.Linear ↔ fp'.Linear := by
  unfold Footprint.Linear
  rw [equiv.1, equiv.2.1]

theorem sum_equiv_of_rel {α β : Type*} {f : α → Footprint O T} {g : β → Footprint O T}
    {A : Multiset α} {B : Multiset β} {r : α → β → Prop} (rel : Multiset.Rel r A B)
    (each : ∀ a b, r a b → FootprintEquiv L (f a) (g b)) :
    FootprintEquiv L (A.map f).sum (B.map g).sum := by
  induction rel with
  | zero => exact FootprintEquiv.refl _
  | cons head _ ih =>
      rw [Multiset.map_cons, Multiset.map_cons, Multiset.sum_cons, Multiset.sum_cons]
      exact (each _ _ head).add ih

end Equivalences

/-! ## Declarative rows -/

section Declarative

variable [DecidableEq O] (L : TermLayer V T P) (label : O → T) (S : Finset O)

open Classical in
/-- **The semantic region** of a pattern under a substitution, as a Boolean predicate. -/
noncomputable def semRegion (σ : Subst V T) (p : P) : T → Bool := fun t => decide (L.Covers σ p t)

theorem semRegion_eq_true {σ : Subst V T} {p : P} {t : T} :
    semRegion L σ p t = true ↔ L.Covers σ p t := by
  simp [semRegion]

/-- **The declarative steps of one source.** -/
inductive DStep : Source V T P → Subst V T → Subst V T × Pick O T → Prop
  | read {p : P} {σ τ : Subst V T} {o : O} :
      o ∈ S → L.Step σ p (label o) τ → DStep (.read p) σ (τ, .keep o)
  | take {p : P} {σ τ : Subst V T} {o : O} :
      o ∈ S → L.Step σ p (label o) τ → DStep (.take p) σ (τ, .take o)
  | absent {p : P} {σ : Subst V T} :
      regionOf label S (semRegion L σ p) = ∅ →
        DStep (.absent p) σ (σ, .query ⟨semRegion L σ p, ∅⟩ false)
  | unique {access : Access} {p : P} {σ τ : Subst V T} {o : O} :
      (regionOf label S (semRegion L σ p)).card = 1 → o ∈ regionOf label S (semRegion L σ p) →
        L.Step σ p (label o) τ →
          DStep (.unique access p) σ
            (τ, .query ⟨semRegion L σ p, regionOf label S (semRegion L σ p)⟩ (access = .take))
  | all {access : Access} {p coll : P} {fold : Multiset T → T} {σ τ : Subst V T} :
      L.Step σ coll (fold ((regionOf label S (semRegion L σ p)).val.map label)) τ →
        DStep (.all access p coll fold) σ
          (τ, .query ⟨semRegion L σ p, regionOf label S (semRegion L σ p)⟩ (access = .take))
  | letBind {p : P} {eval : Subst V T → List T} {σ τ : Subst V T} {i : ℕ} {value : T} :
      (eval σ)[i]? = some value → L.Step σ p value τ → DStep (.letBind p eval) σ (τ, .result i)

/-- The semantic regions a source consults. -/
noncomputable def Source.semRegions : Source V T P → Subst V T → List (T → Bool)
  | .read p, σ => [semRegion L σ p]
  | .take p, σ => [semRegion L σ p]
  | .absent p, σ => [semRegion L σ p]
  | .unique _ p, σ => [semRegion L σ p]
  | .all _ p _ _, σ => [semRegion L σ p]
  | .letBind _ _, _ => []

/-- The semantic completeness regions of a source list. -/
noncomputable def semComplRegions : SourceList V T P → Subst V T → List (T → Bool)
  | .done, _ => []
  | .cons s rest, σ => s.semRegions L σ ++ semComplRegions rest σ
  | .absent query rest, σ => semComplRegions query σ ++ semComplRegions rest σ
  | .every rest, σ => semComplRegions rest σ

/-- **A transversal** of a set of rows: its linear rows, each model-level row once. -/
structure Transversal (rowsOf : Subst V T × List (Pick O T) → Prop)
    (exts : Multiset (Subst V T × List (Pick O T))) : Prop where
  mem : ∀ x ∈ exts, rowsOf x ∧ (footprintOf x.2).Linear
  cover : ∀ y, rowsOf y → (footprintOf y.2).Linear → ∃ x ∈ exts, RowEquiv L x y
  once : (exts.map (Quotient.mk (rowSetoid L))).Nodup

/-- **The declarative rows of a source list.** -/
noncomputable def DRow (template : List P) :
    SourceList V T P → Subst V T → Subst V T × List (Pick O T) → Prop
  | .done, σ, x => ∃ labels, instTemplate L σ template = some labels ∧ x = (σ, [.make labels])
  | .cons s rest, σ, x =>
      ∃ y z, DStep L label S s σ y ∧ DRow template rest y.1 z ∧ x = (z.1, y.2 :: z.2)
  | .absent query rest, σ, x =>
      (¬ ∃ y, DRow [] query σ y) ∧ ∃ y, DRow template rest σ y ∧
        x = (y.1, .amalgam (complQueries label S (semComplRegions L query σ)) :: y.2)
  | .every rest, σ, x =>
      ∃ exts, Transversal L (DRow template rest σ) exts ∧
        x = (σ, [.amalgam ((exts.map fun y => footprintOf y.2).sum +
          complQueries label S (semComplRegions L rest σ))])

/-- A computation respects the theory: `E`-equivalent substitutions give `E`-related results. -/
def Respects (eval : Subst V T → List T) : Prop :=
  ∀ σ σ', SubstEquiv L.E σ σ' → List.Forall₂ L.E (eval σ) (eval σ')

/-- The computations of the `let` sources of a source list. -/
def SourceList.lets : SourceList V T P → List (Subst V T → List T)
  | .done => []
  | .cons (.letBind _ eval) rest => eval :: rest.lets
  | .cons _ rest => rest.lets
  | .absent query rest => query.lets ++ rest.lets
  | .every rest => rest.lets

end Declarative

/-! ## Regions agree -/

section Regions

variable [DecidableEq V] {L : TermLayer V T P} {m : Matcher V T P}

omit [DecidableEq V] in
theorem region_eq_semRegion (sound : Matcher.Sound L m) (complete : Matcher.Complete L m)
    (σ : Subst V T) (p : P) : Matcher.region m σ p = semRegion L σ p := by
  funext t
  apply Bool.eq_iff_iff.mpr
  rw [Matcher.region_eq_true_iff sound complete, semRegion_eq_true]

theorem semRegion_congr {σ σ' : Subst V T} (same : SubstEquiv L.E σ σ') (p : P) :
    semRegion L σ p = semRegion L σ' p := by
  funext t
  apply Bool.eq_iff_iff.mpr
  rw [semRegion_eq_true, semRegion_eq_true]
  exact TermLayer.covers_iff_of_substEquiv same

omit [DecidableEq V] in
theorem complRegions_eq_sem (sound : Matcher.Sound L m) (complete : Matcher.Complete L m) :
    ∀ (src : SourceList V T P) (σ : Subst V T), complRegions m src σ = semComplRegions L src σ
  | .done, _ => rfl
  | .cons s rest, σ => by
      simp only [complRegions, semComplRegions]
      rw [complRegions_eq_sem sound complete rest σ]
      cases s <;> simp [Source.regions, Source.semRegions, region_eq_semRegion sound complete]
  | .absent query rest, σ => by
      simp only [complRegions, semComplRegions,
        complRegions_eq_sem sound complete query σ, complRegions_eq_sem sound complete rest σ]
  | .every rest, σ => complRegions_eq_sem sound complete rest σ

theorem semComplRegions_congr {σ σ' : Subst V T} (same : SubstEquiv L.E σ σ') :
    ∀ src : SourceList V T P, semComplRegions L src σ = semComplRegions L src σ'
  | .done => rfl
  | .cons s rest => by
      simp only [semComplRegions]
      rw [semComplRegions_congr same rest]
      cases s <;> simp [Source.semRegions, semRegion_congr same]
  | .absent query rest => by
      simp only [semComplRegions, semComplRegions_congr same query, semComplRegions_congr same rest]
  | .every rest => semComplRegions_congr same rest

end Regions

/-! ## One source -/

section Step

variable [DecidableEq O] [DecidableEq V] {L : TermLayer V T P} {m : Matcher V T P}
  {label : O → T} {S : Finset O}

omit [DecidableEq V] in
theorem dStep_of_mem_stepRows (sound : Matcher.Sound L m) (complete : Matcher.Complete L m)
    {s : Source V T P} {σ : Subst V T} {x : Subst V T × Pick O T}
    (member : x ∈ stepRows m label S s σ) : DStep L label S s σ x := by
  have regionEq := region_eq_semRegion sound complete (m := m) σ
  cases s with
  | read p =>
      obtain ⟨o, inS, τ, answer, rfl⟩ := mem_stepRows_read.mp member
      exact DStep.read inS (sound answer)
  | take p =>
      obtain ⟨o, inS, τ, answer, rfl⟩ := mem_stepRows_take.mp member
      exact DStep.take inS (sound answer)
  | absent p =>
      obtain ⟨empty, rfl⟩ := mem_stepRows_absent.mp member
      rw [regionEq] at empty ⊢
      exact DStep.absent empty
  | unique access p =>
      obtain ⟨one, o, inX, τ, answer, rfl⟩ := mem_stepRows_unique.mp member
      rw [regionEq] at one inX ⊢
      exact DStep.unique one inX (sound answer)
  | all access p coll fold =>
      obtain ⟨τ, answer, rfl⟩ := mem_stepRows_all.mp member
      rw [regionEq] at answer ⊢
      exact DStep.all (sound answer)
  | letBind p eval =>
      obtain ⟨i, value, at_i, τ, answer, rfl⟩ := mem_stepRows_letBind.mp member
      exact DStep.letBind at_i (sound answer)

theorem forall₂_getElem? {α β : Type*} {r : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, List.Forall₂ r l l' → ∀ {i : ℕ} {b : β}, l'[i]? = some b →
      ∃ a, l[i]? = some a ∧ r a b
  | [], [], List.Forall₂.nil, i, b, h => by simp at h
  | a :: l, b' :: l', List.Forall₂.cons head tail, i, b, h => by
      cases i with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at h ⊢
          subst h
          exact ⟨a, rfl, head⟩
      | succ i =>
          simp only [List.getElem?_cons_succ] at h ⊢
          exact forall₂_getElem? tail h

omit [DecidableEq O] [DecidableEq V] in
theorem pickEquiv_refl (a : Pick O T) : PickEquiv L a a := (pickEquiv_equivalence L).refl a

/-- **One source is complete**: a declarative step from an `E`-equivalent start is matched by a
computed step. -/
theorem exists_stepRows_of_dStep (sound : Matcher.Sound L m) (complete : Matcher.Complete L m)
    {s : Source V T P} (respects : ∀ p eval, s = .letBind p eval → Respects L eval)
    {σ σ' : Subst V T} (same : SubstEquiv L.E σ σ') {y : Subst V T × Pick O T}
    (step : DStep L label S s σ' y) : ∃ x ∈ stepRows m label S s σ, StepEquiv L x y := by
  have regionEq : ∀ p, Matcher.region m σ p = semRegion L σ' p := fun p =>
    (region_eq_semRegion sound complete σ p).trans (semRegion_congr same p)
  cases step with
  | read inS stepY =>
      obtain ⟨τ, answer, equiv⟩ := complete same stepY
      exact ⟨(τ, .keep _), mem_stepRows_read.mpr ⟨_, inS, τ, answer, rfl⟩, equiv, pickEquiv_refl _⟩
  | take inS stepY =>
      obtain ⟨τ, answer, equiv⟩ := complete same stepY
      exact ⟨(τ, .take _), mem_stepRows_take.mpr ⟨_, inS, τ, answer, rfl⟩, equiv, pickEquiv_refl _⟩
  | @absent p _ empty =>
      refine ⟨(σ, .query ⟨Matcher.region m σ p, ∅⟩ false),
        mem_stepRows_absent.mpr ⟨by rw [regionEq]; exact empty, rfl⟩, same, ?_⟩
      rw [regionEq]
      exact pickEquiv_refl _
  | @unique access p _ τ' o one inX stepY =>
      obtain ⟨τ, answer, equiv⟩ := complete same stepY
      refine ⟨_, mem_stepRows_unique.mpr ⟨by rw [regionEq]; exact one, o, by rw [regionEq]; exact inX,
        τ, answer, rfl⟩, equiv, ?_⟩
      rw [regionEq]
      exact pickEquiv_refl _
  | @all access p coll fold _ τ' stepY =>
      obtain ⟨τ, answer, equiv⟩ := complete same stepY
      refine ⟨_, mem_stepRows_all.mpr ⟨τ, by rw [regionEq]; exact answer, rfl⟩, equiv, ?_⟩
      rw [regionEq]
      exact pickEquiv_refl _
  | @letBind p eval _ τ' i value at_i stepY =>
      have rel := respects p eval rfl σ σ' same
      obtain ⟨value', at_i', related⟩ := forall₂_getElem? rel at_i
      obtain ⟨τ, answer, equiv⟩ := complete same (stepY.of_equiv (L.equivalence.symm related))
      exact ⟨(τ, .result i), mem_stepRows_letBind.mpr ⟨i, value', at_i', τ, answer, rfl⟩, equiv,
        pickEquiv_refl _⟩

/-- The variables a source binds. -/
def Source.binds (L : TermLayer V T P) : Source V T P → Finset V
  | .read p => L.vars p
  | .take p => L.vars p
  | .absent _ => ∅
  | .unique _ p => L.vars p
  | .all _ _ coll _ => L.vars coll
  | .letBind p _ => L.vars p

omit [DecidableEq V] in
/-- After one source, a variable is bound exactly when it was bound or the source binds it. -/
theorem stepRows_isSome_iff (sound : Matcher.Sound L m) {s : Source V T P} {σ : Subst V T}
    {x : Subst V T × Pick O T} (member : x ∈ stepRows m label S s σ) (v : V) :
    (x.1 v).isSome ↔ (σ v).isSome ∨ v ∈ s.binds L := by
  cases s with
  | read p =>
      obtain ⟨o, -, τ, answer, rfl⟩ := mem_stepRows_read.mp member
      exact (sound answer).isSome_iff v
  | take p =>
      obtain ⟨o, -, τ, answer, rfl⟩ := mem_stepRows_take.mp member
      exact (sound answer).isSome_iff v
  | absent p =>
      obtain ⟨-, rfl⟩ := mem_stepRows_absent.mp member
      simp [Source.binds]
  | unique access p =>
      obtain ⟨-, o, -, τ, answer, rfl⟩ := mem_stepRows_unique.mp member
      exact (sound answer).isSome_iff v
  | all access p coll fold =>
      obtain ⟨τ, answer, rfl⟩ := mem_stepRows_all.mp member
      exact (sound answer).isSome_iff v
  | letBind p eval =>
      obtain ⟨i, value, -, τ, answer, rfl⟩ := mem_stepRows_letBind.mp member
      exact (sound answer).isSome_iff v

omit [DecidableEq O] [DecidableEq V] in
theorem nodup_answers (minimal : Matcher.Minimal L m) (p : P) (σ : Subst V T) (t : T)
    (pick : Pick O T) :
    ((↑(m p σ t) : Multiset (Subst V T)).map fun τ => Quotient.mk (stepSetoid L) (τ, pick)).Nodup := by
  rw [Multiset.map_coe, Multiset.coe_nodup, List.Nodup, List.pairwise_map]
  exact (minimal p σ t).imp fun {τ τ'} notEquiv same => notEquiv (stepEquiv_of_mk_eq same).1

theorem nodup_bind_of_nodup {α Q : Type*} {X : Multiset α} {f : α → Multiset Q} (nodup : X.Nodup)
    (each : ∀ o ∈ X, (f o).Nodup) (apart : ∀ o ∈ X, ∀ o' ∈ X, o ≠ o' → Disjoint (f o) (f o')) :
    (X.bind f).Nodup :=
  Multiset.nodup_bind.mpr ⟨each, Multiset.Nodup.pairwise apart nodup⟩

omit [DecidableEq O] [DecidableEq V] in
theorem pick_eq_of_equiv_keep {o o' : O} (equiv : PickEquiv L (Pick.keep o : Pick O T) (.keep o')) :
    o = o' := by
  have := equiv.1
  simp only [Pick.strip, Pick.keep.injEq] at this
  exact this

omit [DecidableEq O] [DecidableEq V] in
theorem pick_eq_of_equiv_take {o o' : O} (equiv : PickEquiv L (Pick.take o : Pick O T) (.take o')) :
    o = o' := by
  have := equiv.1
  simp only [Pick.strip, Pick.take.injEq] at this
  exact this

omit [DecidableEq O] [DecidableEq V] in
theorem pick_eq_of_equiv_result {i j : ℕ}
    (equiv : PickEquiv L (Pick.result i : Pick O T) (.result j)) : i = j := by
  have := equiv.1
  simp only [Pick.strip, Pick.result.injEq] at this
  exact this

omit [DecidableEq V] in
/-- **One source is minimal**: no two computed steps are equivalent. -/
theorem stepRows_nodup (minimal : Matcher.Minimal L m) (s : Source V T P) (σ : Subst V T) :
    ((stepRows m label S s σ).map (Quotient.mk (stepSetoid L))).Nodup := by
  cases s with
  | read p =>
      simp only [stepRows, Multiset.map_bind, Multiset.map_map]
      refine nodup_bind_of_nodup S.nodup (fun o _ => ?_) (fun o _ o' _ different => ?_)
      · exact nodup_answers minimal p σ (label o) (.keep o)
      · refine Multiset.disjoint_left.mpr fun {c} inC inC' => different ?_
        obtain ⟨τ, -, rfl⟩ := Multiset.mem_map.mp inC
        obtain ⟨τ', -, same⟩ := Multiset.mem_map.mp inC'
        exact (pick_eq_of_equiv_keep (stepEquiv_of_mk_eq same).2).symm
  | take p =>
      simp only [stepRows, Multiset.map_bind, Multiset.map_map]
      refine nodup_bind_of_nodup S.nodup (fun o _ => ?_) (fun o _ o' _ different => ?_)
      · exact nodup_answers minimal p σ (label o) (.take o)
      · refine Multiset.disjoint_left.mpr fun {c} inC inC' => different ?_
        obtain ⟨τ, -, rfl⟩ := Multiset.mem_map.mp inC
        obtain ⟨τ', -, same⟩ := Multiset.mem_map.mp inC'
        exact (pick_eq_of_equiv_take (stepEquiv_of_mk_eq same).2).symm
  | absent p =>
      simp only [stepRows]
      split_ifs <;> simp
  | unique access p =>
      simp only [stepRows]
      split_ifs with one
      · simp only [Multiset.map_bind, Multiset.map_map]
        obtain ⟨u, single⟩ := Finset.card_eq_one.mp one
        refine nodup_bind_of_nodup (Finset.nodup _) (fun o _ => ?_) (fun o inO o' inO' different => ?_)
        · exact nodup_answers minimal p σ (label o) _
        · rw [single] at inO inO'
          rw [Finset.mem_val, Finset.mem_singleton] at inO inO'
          exact absurd (inO.trans inO'.symm) different
      · simp
  | all access p coll fold =>
      simp only [stepRows, Multiset.map_map]
      exact nodup_answers minimal coll σ _ _
  | letBind p eval =>
      simp only [stepRows, Multiset.map_bind, Multiset.map_map]
      have zipNodup : ((eval σ).zipIdx 0).Nodup :=
        List.Nodup.of_map Prod.snd (by rw [List.zipIdx_map_snd]; exact List.nodup_range')
      refine nodup_bind_of_nodup (Multiset.coe_nodup.mpr zipNodup) (fun x _ => ?_)
        (fun x inX x' inX' different => ?_)
      · exact nodup_answers minimal p σ x.1 (.result x.2)
      · refine Multiset.disjoint_left.mpr fun {c} inC inC' => different ?_
        obtain ⟨τ, -, rfl⟩ := Multiset.mem_map.mp inC
        obtain ⟨τ', -, same⟩ := Multiset.mem_map.mp inC'
        have index : x'.2 = x.2 := pick_eq_of_equiv_result (stepEquiv_of_mk_eq same).2
        have atX := List.mem_zipIdx_iff_getElem?.mp (Multiset.mem_coe.mp inX)
        have atX' := List.mem_zipIdx_iff_getElem?.mp (Multiset.mem_coe.mp inX')
        rw [index, atX] at atX'
        exact Prod.ext (Option.some.inj atX') index.symm

end Step

/-! ## Rows -/

section Rows

variable [DecidableEq O] [DecidableEq V] {L : TermLayer V T P} {m : Matcher V T P}
  {label : O → T} {S : Finset O} {template : List P}

omit [DecidableEq V] in
/-- Computed rows extend their start. -/
theorem extends_of_mem_rows (sound : Matcher.Sound L m) :
    ∀ {src : SourceList V T P} {σ : Subst V T} {x : Subst V T × List (Pick O T)},
      x ∈ rows L m label S template src σ → Extends σ x.1
  | .done, σ, x, member => by
      rw [rows_done] at member
      split at member
      · rw [Multiset.mem_singleton] at member
        subst member
        exact Extends.refl _
      · simp at member
  | .cons s rest, σ, x, member => by
      obtain ⟨y, inStep, z, inRest, rfl⟩ := mem_rows_cons.mp member
      exact (extends_of_mem_stepRows sound inStep).trans (extends_of_mem_rows (x := z) sound inRest)
  | .absent query rest, σ, x, member => by
      obtain ⟨_, y, inRest, rfl⟩ := mem_rows_absent.mp member
      exact extends_of_mem_rows (x := y) sound inRest
  | .every rest, σ, x, member => by
      rw [rows_every, Multiset.mem_singleton] at member
      subst member
      exact Extends.refl _

omit [DecidableEq O] [DecidableEq V] in
/-- **Instantiating a template respects the theory.** -/
theorem instTemplate_congr {σ σ' : Subst V T} (same : SubstEquiv L.E σ σ') :
    ∀ template : List P,
      Option.Rel (List.Forall₂ L.E) (instTemplate L σ template) (instTemplate L σ' template)
  | [] => Option.Rel.some List.Forall₂.nil
  | q :: rest => by
      have head := L.inst_congr σ σ' q fun v _ => same v
      have tail := instTemplate_congr same rest
      unfold instTemplate at tail ⊢
      rw [List.mapM_cons, List.mapM_cons]
      rcases optionRel_iff.mp head with ⟨h1, h2⟩ | ⟨a, a', h1, h2, ra⟩
      · rw [h1, h2]
        exact Option.Rel.none
      · rcases optionRel_iff.mp tail with ⟨k1, k2⟩ | ⟨as, as', k1, k2, ras⟩
        · rw [h1, h2, k1, k2]
          exact Option.Rel.none
        · rw [h1, h2, k1, k2]
          exact Option.Rel.some (List.Forall₂.cons ra ras)

omit [DecidableEq O] [DecidableEq V] in
theorem pickEquiv_amalgam {F G : Footprint O T} (equiv : FootprintEquiv L F G) :
    PickEquiv L (.amalgam F) (.amalgam G) := by
  obtain ⟨t, k, r, mk⟩ := equiv
  exact ⟨by simp [Pick.strip, t, k, r], mk⟩

omit [DecidableEq O] [DecidableEq V] in
theorem lets_cons {s : Source V T P} {rest : SourceList V T P}
    (respects : ∀ eval ∈ (SourceList.cons s rest).lets, Respects L eval) :
    (∀ p eval, s = .letBind p eval → Respects L eval) ∧ ∀ eval ∈ rest.lets, Respects L eval := by
  cases s with
  | letBind p eval =>
      refine ⟨fun p' eval' same => ?_, fun e member => respects e (List.mem_cons_of_mem _ member)⟩
      cases same
      exact respects eval List.mem_cons_self
  | read p => exact ⟨fun _ _ h => (by cases h), respects⟩
  | take p => exact ⟨fun _ _ h => (by cases h), respects⟩
  | absent p => exact ⟨fun _ _ h => (by cases h), respects⟩
  | unique a p => exact ⟨fun _ _ h => (by cases h), respects⟩
  | all a p q f => exact ⟨fun _ _ h => (by cases h), respects⟩

omit [DecidableEq V] in
/-- Two steps that agree up to the theory, from one start, bind the same variables. -/
theorem substEquiv_of_rows {s : Source V T P} {σ : Subst V T} {y y' : Subst V T × Pick O T}
    (sound : Matcher.Sound L m) (inY : y ∈ stepRows m label S s σ) (inY' : y' ∈ stepRows m label S s σ)
    {z z' : Subst V T × List (Pick O T)} (growsZ : Extends y.1 z.1) (growsZ' : Extends y'.1 z'.1)
    (same : SubstEquiv L.E z.1 z'.1) : SubstEquiv L.E y.1 y'.1 := by
  intro v
  have dom := (stepRows_isSome_iff sound inY v).trans (stepRows_isSome_iff sound inY' v).symm
  cases hy : y.1 v with
  | none =>
      cases hy' : y'.1 v with
      | none => exact Option.Rel.none
      | some u' =>
          have : (y.1 v).isSome := dom.mpr (by rw [hy']; rfl)
          rw [hy] at this
          cases this
  | some u =>
      obtain ⟨u', hy'⟩ := Option.isSome_iff_exists.mp (dom.mp (by rw [hy]; rfl))
      rw [hy']
      have rel := same v
      rw [growsZ v u hy, growsZ' v u' hy'] at rel
      exact rel

/-- **Agreement.** For a sound, complete and minimal matcher, and `let` computations that respect
the theory, the computed rows are declarative rows, every declarative row from an `E`-equivalent
start is equivalent to a computed one, and no two computed rows are equivalent. -/
theorem agreementFor (sound : Matcher.Sound L m) (complete : Matcher.Complete L m)
    (minimal : Matcher.Minimal L m) :
    ∀ (src : SourceList V T P) (template : List P),
      (∀ eval ∈ src.lets, Respects L eval) → ∀ σ : Subst V T,
      (∀ x ∈ rows L m label S template src σ, DRow L label S template src σ x) ∧
      (∀ σ', SubstEquiv L.E σ σ' → ∀ y, DRow L label S template src σ' y →
        ∃ x ∈ rows L m label S template src σ, RowEquiv L x y) ∧
      ((rows L m label S template src σ).map (Quotient.mk (rowSetoid L))).Nodup
  | .done, template, _, σ => by
      refine ⟨fun x member => ?_, fun σ' same y declared => ?_, ?_⟩
      · rw [rows_done] at member
        split at member
        · rename_i labels instEq
          rw [Multiset.mem_singleton] at member
          exact ⟨labels, instEq, member⟩
        · simp at member
      · obtain ⟨labels', instEq', rfl⟩ := declared
        have rel := instTemplate_congr same template
        rw [instEq'] at rel
        rcases optionRel_iff.mp rel with ⟨-, h⟩ | ⟨labels, l', instEq, h, related⟩
        · cases h
        · cases h
          refine ⟨(σ, [.make labels]), ?_, same, List.Forall₂.cons ⟨rfl, multisetRel_of_forall₂ related⟩
            List.Forall₂.nil⟩
          rw [rows_done]
          simp only [instEq]
          exact Multiset.mem_singleton_self _
      · rw [rows_done]
        split <;> simp
  | .cons s rest, template, respects, σ => by
      obtain ⟨respectsS, respectsRest⟩ := lets_cons respects
      have ih := agreementFor sound complete minimal rest template respectsRest
      refine ⟨fun x member => ?_, fun σ' same y declared => ?_, ?_⟩
      · obtain ⟨y, inStep, z, inRest, rfl⟩ := mem_rows_cons.mp member
        exact ⟨y, z, dStep_of_mem_stepRows sound complete inStep, (ih y.1).1 z inRest, rfl⟩
      · obtain ⟨y₁, z, step, declaredRest, rfl⟩ := declared
        obtain ⟨x₁, inStep, equiv₁⟩ := exists_stepRows_of_dStep sound complete respectsS same step
        obtain ⟨x₂, inRest, equiv₂⟩ := (ih x₁.1).2.1 y₁.1 equiv₁.1 z declaredRest
        exact ⟨(x₂.1, x₁.2 :: x₂.2), mem_rows_cons.mpr ⟨x₁, inStep, x₂, inRest, rfl⟩, equiv₂.1,
          List.Forall₂.cons equiv₁.2 equiv₂.2⟩
      · simp only [rows, Multiset.map_bind, Multiset.map_map]
        have stepNodup := stepRows_nodup (label := label) (S := S) minimal s σ
        refine nodup_bind_of_nodup (Multiset.Nodup.of_map _ stepNodup) (fun y inStep => ?_)
          (fun y inY y' inY' different => ?_)
        · have restNodup := (ih y.1).2.2
          refine Multiset.Nodup.map_on (fun z inZ z' inZ' same => ?_)
            (Multiset.Nodup.of_map _ restNodup)
          have equiv := rowEquiv_of_mk_eq same
          refine Multiset.inj_on_of_nodup_map restNodup z inZ z' inZ' (mk_eq_of_rowEquiv ?_)
          exact ⟨equiv.1, (List.forall₂_cons.mp equiv.2).2⟩
        · refine Multiset.disjoint_left.mpr fun {c} inC inC' => different ?_
          obtain ⟨z, inZ, rfl⟩ := Multiset.mem_map.mp inC
          obtain ⟨z', inZ', same⟩ := Multiset.mem_map.mp inC'
          have equiv := rowEquiv_of_mk_eq same
          have pickSame := (List.forall₂_cons.mp equiv.2).1
          have stepEq : StepEquiv L y' y := ⟨substEquiv_of_rows sound inY' inY
            (extends_of_mem_rows sound inZ') (extends_of_mem_rows sound inZ) equiv.1, pickSame⟩
          exact (Multiset.inj_on_of_nodup_map stepNodup y' inY' y inY (Quotient.sound stepEq)).symm
  | .absent query rest, template, respects, σ => by
      have queryRespects : ∀ eval ∈ query.lets, Respects L eval :=
        fun eval member => respects eval (by simp [SourceList.lets, member])
      have restRespects : ∀ eval ∈ rest.lets, Respects L eval :=
        fun eval member => respects eval (by simp [SourceList.lets, member])
      have iq := agreementFor sound complete minimal query [] queryRespects
      have ir := agreementFor sound complete minimal rest template restRespects
      refine ⟨fun x member => ?_, fun σ' same y declared => ?_, ?_⟩
      · obtain ⟨empty, y, inRest, rfl⟩ := mem_rows_absent.mp member
        refine ⟨?_, y, (ir σ).1 y inRest, ?_⟩
        · rintro ⟨z, row⟩
          obtain ⟨z', member, _⟩ := (iq σ).2.1 σ (SubstEquiv.refl L.equivalence σ) z row
          simp [empty] at member
        · rw [complRegions_eq_sem sound complete]
      · obtain ⟨absent, y', restRow, rfl⟩ := declared
        obtain ⟨x', inRest, equiv⟩ := (ir σ).2.1 σ' same y' restRow
        have empty : rows L m label S [] query σ = 0 := by
          apply Multiset.eq_zero_of_forall_notMem
          intro z member
          obtain ⟨z', inOther, _⟩ := (iq σ').2.1 σ (SubstEquiv.symm L.equivalence same)
            z ((iq σ).1 z member)
          exact absent ⟨z', (iq σ').1 z' inOther⟩
        refine ⟨(x'.1, .amalgam (complQueries label S (complRegions m query σ)) :: x'.2),
          mem_rows_absent.mpr ⟨empty, x', inRest, rfl⟩, equiv.1, ?_⟩
        apply List.Forall₂.cons _ equiv.2
        rw [complRegions_eq_sem sound complete, semComplRegions_congr same]
        exact (pickEquiv_equivalence L).refl _
      · simp only [rows]
        split
        · simp only [Multiset.map_map]
          have restNodup := (ir σ).2.2
          refine Multiset.Nodup.map_on (fun z inZ z' inZ' same => ?_)
            (Multiset.Nodup.of_map _ restNodup)
          have equiv := rowEquiv_of_mk_eq same
          exact Multiset.inj_on_of_nodup_map restNodup z inZ z' inZ'
            (mk_eq_of_rowEquiv ⟨equiv.1, (List.forall₂_cons.mp equiv.2).2⟩)
        · simp
  | .every rest, template, respects, σ => by
      have ih := agreementFor sound complete minimal rest template respects
      have filteredNodup : ∀ τ : Subst V T,
          (((rows L m label S template rest τ).filter fun y => (footprintOf y.2).Linear).map
            (Quotient.mk (rowSetoid L))).Nodup := fun τ =>
        Multiset.nodup_of_le (Multiset.map_le_map (Multiset.filter_le _ _)) (ih τ).2.2
      refine ⟨fun x member => ?_, fun σ' same y declared => ?_, ?_⟩
      · rw [rows_every, Multiset.mem_singleton] at member
        subst member
        refine ⟨(rows L m label S template rest σ).filter fun y => (footprintOf y.2).Linear,
          ⟨fun x inFilter => ?_, fun y declaredY linearY => ?_, filteredNodup σ⟩, ?_⟩
        · obtain ⟨inRows, linear⟩ := Multiset.mem_filter.mp inFilter
          exact ⟨(ih σ).1 x inRows, linear⟩
        · obtain ⟨x, inRows, equiv⟩ := (ih σ).2.1 σ (SubstEquiv.refl L.equivalence σ) y declaredY
          exact ⟨x, Multiset.mem_filter.mpr ⟨inRows,
            ((footprintOf_equiv equiv.2).linear_iff).mpr linearY⟩, equiv⟩
        · unfold everyFootprint
          rw [complRegions_eq_sem sound complete]
      · obtain ⟨exts, transversal, rfl⟩ := declared
        refine ⟨(σ, [.amalgam (everyFootprint L m label S template rest σ)]),
          by rw [rows_every]; exact Multiset.mem_singleton_self _, same,
          List.Forall₂.cons (pickEquiv_amalgam ?_) List.Forall₂.nil⟩
        unfold everyFootprint
        rw [complRegions_eq_sem sound complete, semComplRegions_congr same]
        refine FootprintEquiv.add ?_ (FootprintEquiv.refl _)
        let A := (rows L m label S template rest σ).filter fun y => (footprintOf y.2).Linear
        have sameClasses : A.map (Quotient.mk (rowSetoid L)) = exts.map (Quotient.mk (rowSetoid L)) := by
          refine (Multiset.Nodup.ext (filteredNodup σ) transversal.once).mpr fun c => ?_
          constructor
          · intro inA
            obtain ⟨a, inFilter, rfl⟩ := Multiset.mem_map.mp inA
            obtain ⟨inRows, linearA⟩ := Multiset.mem_filter.mp inFilter
            obtain ⟨a', inRows', equiv'⟩ := (ih σ').2.1 σ (SubstEquiv.symm L.equivalence same) a
              ((ih σ).1 a inRows)
            obtain ⟨b, inExts, equivB⟩ := transversal.cover a' ((ih σ').1 a' inRows')
              (((footprintOf_equiv equiv'.2).linear_iff).mpr linearA)
            refine Multiset.mem_map.mpr ⟨b, inExts, mk_eq_of_rowEquiv ?_⟩
            exact (rowEquiv_equivalence L).trans equivB equiv'
          · intro inB
            obtain ⟨b, inExts, rfl⟩ := Multiset.mem_map.mp inB
            obtain ⟨declaredB, linearB⟩ := transversal.mem b inExts
            obtain ⟨x, inRows, equiv⟩ := (ih σ).2.1 σ' same b declaredB
            refine Multiset.mem_map.mpr ⟨x, Multiset.mem_filter.mpr ⟨inRows,
              ((footprintOf_equiv equiv.2).linear_iff).mpr linearB⟩, mk_eq_of_rowEquiv equiv⟩
        have rel : Multiset.Rel (RowEquiv L) A exts := by
          have := Multiset.rel_eq.mpr sameClasses
          rw [Multiset.rel_map] at this
          exact this.mono fun a _ b _ h => rowEquiv_of_mk_eq h
        exact sum_equiv_of_rel rel fun a b equiv => footprintOf_equiv equiv.2
      · rw [rows_every]
        simp

/-- Source agreement for the selected output template. -/
theorem agreement (sound : Matcher.Sound L m) (complete : Matcher.Complete L m)
    (minimal : Matcher.Minimal L m) (src : SourceList V T P)
    (respects : ∀ eval ∈ src.lets, Respects L eval) (σ : Subst V T) :
    (∀ x ∈ rows L m label S template src σ, DRow L label S template src σ x) ∧
      (∀ σ', SubstEquiv L.E σ σ' → ∀ y, DRow L label S template src σ' y →
        ∃ x ∈ rows L m label S template src σ, RowEquiv L x y) ∧
      ((rows L m label S template src σ).map (Quotient.mk (rowSetoid L))).Nodup :=
  agreementFor sound complete minimal src template respects σ

/-- **The `every` footprint is the declarative one**, up to the theory on what it makes: for any
transversal of the suffix's declarative rows. -/
theorem every_footprint_agrees (sound : Matcher.Sound L m) (complete : Matcher.Complete L m)
    (minimal : Matcher.Minimal L m) {rest : SourceList V T P}
    (respects : ∀ eval ∈ rest.lets, Respects L eval) {σ : Subst V T}
    {exts : Multiset (Subst V T × List (Pick O T))}
    (transversal : Transversal L (DRow L label S template rest σ) exts) :
    FootprintEquiv L (everyFootprint L m label S template rest σ)
      ((exts.map fun y => footprintOf y.2).sum + complQueries label S (semComplRegions L rest σ)) := by
  obtain ⟨x, member, equiv⟩ := (agreement (label := label) (S := S) (template := template) sound
    complete minimal (.every rest) respects σ).2.1 σ (SubstEquiv.refl L.equivalence σ) _
      ⟨exts, transversal, rfl⟩
  rw [rows_every, Multiset.mem_singleton] at member
  subst member
  obtain ⟨⟨strip, makes⟩, -⟩ := List.forall₂_cons.mp equiv.2
  simp only [Pick.strip, Pick.amalgam.injEq, Footprint.mk.injEq] at strip
  exact ⟨strip.1, strip.2.1, strip.2.2.1, makes⟩

/-- **What a transform fires is a commit of a declarative linear row.** -/
theorem declarative_of_fires (sound : Matcher.Sound L m) (complete : Matcher.Complete L m)
    (minimal : Matcher.Minimal L m) {t : Transform V T P}
    (respects : ∀ eval ∈ t.sources.lets, Respects L eval) {c : Commit O T}
    (fires : Fires L m label S t c) :
    ∃ y, DRow L label S t.template t.sources (fun _ => none) y ∧ (footprintOf y.2).Linear ∧
      IsCommitOf label S (footprintOf y.2) c := by
  obtain ⟨x, member, linear, commit⟩ := fires
  exact ⟨x, (agreement sound complete minimal t.sources respects _).1 x member, linear, commit⟩

/-- **Every declarative linear row is fired**, by a commit that takes, keeps and reads exactly what
the row does and makes labels `E`-related to the row's, given fresh occurrences of every label. -/
theorem fires_of_declarative (sound : Matcher.Sound L m) (complete : Matcher.Complete L m)
    (minimal : Matcher.Minimal L m) (supply : ∀ (X : Finset O) (t : T), ∃ o, o ∉ X ∧ label o = t)
    {t : Transform V T P} (respects : ∀ eval ∈ t.sources.lets, Respects L eval)
    {y : Subst V T × List (Pick O T)}
    (declared : DRow L label S t.template t.sources (fun _ => none) y)
    (linear : (footprintOf y.2).Linear) :
    ∃ c, Fires L m label S t c ∧ c.taken = (footprintOf y.2).takes.toFinset ∧
      c.kept = (footprintOf y.2).keeps.toFinset ∧ (∀ r, r ∈ c.queries ↔ r ∈ (footprintOf y.2).queries) ∧
      Multiset.Rel L.E (labels label c.made) (footprintOf y.2).makes := by
  obtain ⟨x, member, equiv⟩ := (agreement sound complete minimal t.sources respects _).2.1 _
    (SubstEquiv.refl L.equivalence _) y declared
  have fpEquiv := footprintOf_equiv equiv.2
  obtain ⟨c, commit⟩ := exists_isCommitOf (S := S) supply (footprintOf x.2)
  refine ⟨c, ⟨x, member, fpEquiv.linear_iff.mpr linear, commit⟩, ?_, ?_, fun r => ?_, ?_⟩
  · rw [commit.taken, fpEquiv.1]
  · rw [commit.kept, fpEquiv.2.1]
  · rw [commit.queries r, fpEquiv.2.2.1]
  · rw [commit.made]
    exact fpEquiv.2.2.2

end Rows

/-! ## Controls -/

namespace Controls

/-- Values are numbers, equal when they have one parity; a pattern is the variable (`none`) or a
constant. -/
def parity : TermLayer Unit ℕ (Option ℕ) where
  E a b := a % 2 = b % 2
  equivalence := ⟨fun _ => rfl, fun h => h.symm, fun h h' => h.trans h'⟩
  vars p := match p with
    | none => {()}
    | some _ => ∅
  inst σ p := match p with
    | none => σ ()
    | some n => some n
  inst_bound σ p := by
    cases p with
    | none =>
        intro bound v _
        cases v
        exact bound
    | some n => simp
  inst_local σ τ p h := by
    cases p with
    | none => exact h () (by simp)
    | some n => rfl
  inst_congr σ τ p h := by
    cases p with
    | none => exact h () (by simp)
    | some n => exact Option.Rel.some rfl

/-- A computation that reads only the parity of the bound value. -/
def readsParity : Subst Unit ℕ → List ℕ := fun σ => [(σ ()).getD 0 % 2]

/-- A computation that reads the value itself. -/
def halves : Subst Unit ℕ → List ℕ := fun σ => [(σ ()).getD 0 / 2]

/-- **Respecting the theory, positive and negative**: reading the parity gives related results for
related substitutions; halving does not, for `1` and `3`. -/
theorem respects_controls : Respects parity readsParity ∧ ¬ Respects parity halves := by
  refine ⟨fun σ σ' equiv => ?_, fun respects => ?_⟩
  · have related := equiv ()
    unfold readsParity
    refine List.Forall₂.cons ?_ List.Forall₂.nil
    generalize σ () = x at related ⊢
    generalize σ' () = y at related ⊢
    cases related with
    | none => rfl
    | @some a b h =>
        have same : a % 2 = b % 2 := h
        show a % 2 % 2 = b % 2 % 2
        simp [same]
  · have := respects (fun _ => some 1) (fun _ => some 3) (fun _ => Option.Rel.some rfl)
    simp only [halves, List.forall₂_cons, Option.getD_some] at this
    exact absurd this.1 (by show ¬ ((1 / 2) % 2 = (3 / 2) % 2); decide)

end Controls

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources
