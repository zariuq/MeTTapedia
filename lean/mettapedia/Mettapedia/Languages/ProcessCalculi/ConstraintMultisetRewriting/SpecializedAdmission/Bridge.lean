import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SpecializedAdmission.Correctness
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns
import Mathlib.Data.List.GetD

/-!
# The reference is the first-order step's admission

The instance of a rule at a state is a firing of the first-order step (`AnnotatedRuns.firstOrder`)
over the syntactic substitution action of these terms (`synAction`): its rule instance has the
rule's terms with the parameters written in and the fresh names opened (`instRule`), its selection
names the selected occurrences and the made ones (`instSelection`), and the configuration is the
state's present occurrences with trivial knowledge (`conf`).

`firstOrder_admits_iff`: on a well-formed state of the fragment, with closed parameters, for a rule
of the class, `Admits` (the reference the program is proved against) is exactly

* the frame conjuncts of shapes that the one-frame step leaves to its frame (every opened term is
  a term of the target frame; no take names the identity `0`, which the reference implementation
  reserves), and
* the first-order step's admission of the instance.

So the verdict the program computes is the step's: `Shapes` is the frame conjuncts with the step's
`Shapes`, `Fits` is `Enabled`, `Solvable` is `Consistent`, and the guards are the step's checks
at every solution.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SpecializedAdmission

open MeTTaCalculus.OccurrenceCommits (Enabled)

mutual
theorem Tm.inst_inst (σ τ φ ψ : Nat → Tm) : ∀ t : Tm,
    (t.inst τ φ).inst σ ψ = t.inst (fun k => (τ k).inst σ ψ) (fun j => (φ j).inst σ ψ)
  | .app f args => by simp only [Tm.inst, Tm.instList_inst σ τ φ ψ args]
  | .code _ => rfl
  | .name _ => rfl
  | .var _ => rfl
  | .loc _ => rfl
  | .fresh _ => rfl
theorem Tm.instList_inst (σ τ φ ψ : Nat → Tm) : ∀ ts : List Tm,
    Tm.instList σ ψ (Tm.instList τ φ ts) =
      Tm.instList (fun k => (τ k).inst σ ψ) (fun j => (φ j).inst σ ψ) ts
  | [] => rfl
  | t :: ts => by simp only [Tm.instList, Tm.inst_inst σ τ φ ψ t, Tm.instList_inst σ τ φ ψ ts]
end

/-- Syntactic substitution: a solution assigns locals; equality is identity of terms. -/
def synAction : SubstitutionAction Tm (Nat → Tm) where
  E := Eq
  equivalence := ⟨fun _ => rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩
  apply σ t := t.inst σ Tm.fresh
  identity := Tm.loc
  compose σ τ := fun k => (τ k).inst σ Tm.fresh
  apply_identity t := Tm.inst_id t
  apply_compose σ τ t := (Tm.inst_inst σ τ Tm.fresh Tm.fresh t).symm
  preserves := fun σ {_ _} h => congrArg (fun t => Tm.inst σ Tm.fresh t) h

/-- Parameters written in, the firing's own locals kept. -/
def paramSub (np : Nat) (p : List Tm) : Nat → Tm := fun k => if k < np then p.getD k default else .loc k

/-- A solution of the instance, read as an assignment of all the rule's locals. -/
def mix (np : Nat) (p : List Tm) (σ : Nat → Tm) : Nat → Tm :=
  fun k => if k < np then p.getD k default else σ k

/-- A term of the instance. -/
def instTerm (R : Rule) (s : St) (p : List Tm) (t : Tm) : Tm :=
  t.inst (paramSub R.nparams p) (openFresh s.names)

theorem getD_closed {p : List Tm} (hp : ∀ q ∈ p, q.closed = true) (k : Nat) :
    (p.getD k default).closed = true := by
  rw [List.getD_eq_getElem?_getD]
  cases h : p[k]? with
  | none => rfl
  | some q => exact hp q (List.mem_of_getElem? h)

theorem apply_instTerm (R : Rule) (s : St) (p : List Tm) (hp : ∀ q ∈ p, q.closed = true)
    (σ : Nat → Tm) (t : Tm) :
    synAction.apply σ (instTerm R s p t) = t.inst (mix R.nparams p σ) (openFresh s.names) := by
  show (t.inst (paramSub R.nparams p) (openFresh s.names)).inst σ Tm.fresh = _
  rw [Tm.inst_inst]
  apply Tm.inst_congr
  · intro k _
    by_cases hk : k < R.nparams
    · simp only [paramSub, mix, if_pos hk]
      exact Tm.inst_closed (getD_closed hp k) σ Tm.fresh
    · simp only [paramSub, mix, if_neg hk]
      rfl
  · intro j _
    rfl

theorem mix_of_sol {R : Rule} {s : St} {p : List Tm} {o : List Nat} {σ : Nat → Tm}
    (h : Sol R s p o σ) : mix R.nparams p σ = σ := by
  funext k
  simp only [mix]
  split
  · exact (h.1 k (by assumption)).symm
  · rfl

/-! ## The instance as a firing of the first-order step -/

/-- An ask, an absence or a count as a check of the first-order step; a host is none. -/
def Guard.toCheck? (f : Tm → Tm) : Guard → Option (Check Tm)
  | .ask a b => some (.equal (f a) (f b))
  | .absent q => some (.absent (f q))
  | .count q n => some (.count (f q) n)
  | .host _ _ => none

def instRule (R : Rule) (s : St) (p : List Tm) : RuleInstance Tm where
  take := R.takes.map (instTerm R s p)
  read := R.reads.map (instTerm R s p)
  tell := R.tells.map fun e => (instTerm R s p e.1, instTerm R s p e.2)
  checks := R.guards.filterMap (Guard.toCheck? (instTerm R s p))
  produce := R.makes.map (instTerm R s p)

/-- The occurrence an identity names (with a placeholder label when it is not present). -/
def rowOf (s : St) (id : Nat) : Row := ⟨id, (labelOf s id).getD default⟩

def instSelection (R : Rule) (s : St) (p : List Tm) (o : List Nat) : Selection Row where
  taken := (List.range R.takes.length).map fun u => rowOf s (o.getD u 0)
  read := (List.range R.reads.length).map fun u => rowOf s (o.getD (R.takes.length + u) 0)
  made := madeRows s.nextId (R.makes.map (instTerm R s p))

def instFiring (R : Rule) (s : St) (p : List Tm) (o : List Nat) :
    AnnotatedRuns.Firing Tm (Nat → Tm) Row :=
  ⟨instRule R s p, [], instSelection R s p o⟩

/-- The state as a configuration: its present occurrences, knowledge without equations. -/
def conf (s : St) : Configuration Tm Row := ⟨[], s.present.toFinset⟩

/-- A state as the reference implementation keeps it: distinct identities below the next one,
closed labels. -/
structure WellFormed (s : St) : Prop where
  ids : (s.present.map Row.id).Nodup
  below : ∀ row ∈ s.present, row.id < s.nextId
  closed : ∀ row ∈ s.present, row.label.closed = true

/-! ## Rows, ranges and made rows -/

theorem rowOf_mem_iff (s : St) (id : Nat) :
    rowOf s id ∈ s.present ↔ (labelOf s id).isSome = true := by
  constructor
  · intro h
    simp only [labelOf, Option.isSome_map]
    rw [List.find?_isSome]
    exact ⟨rowOf s id, h, by simp [rowOf]⟩
  · intro h
    simp only [labelOf, Option.isSome_map] at h
    obtain ⟨row, hrow⟩ := Option.isSome_iff_exists.mp h
    have hmem := List.mem_of_find?_eq_some hrow
    have hid : row.id = id := by simpa using List.find?_some hrow
    have e : rowOf s id = row := by
      simp only [rowOf, labelOf, hrow, Option.map_some, Option.getD_some]
      cases row
      simp only at hid
      rw [hid]
    rw [e]
    exact hmem

theorem rowOf_label {s : St} {id : Nat} {l : Tm} (h : labelOf s id = some l) : (rowOf s id).label = l := by
  simp [rowOf, h]

theorem rowOf_eq_iff (s : St) (a b : Nat) : rowOf s a = rowOf s b ↔ a = b :=
  ⟨fun h => congrArg Row.id h, fun h => by rw [h]⟩

theorem pairwise_range_iff (P : Nat → Nat → Prop) : ∀ n : Nat,
    (List.range n).Pairwise P ↔ ∀ u < n, ∀ v < u, P v u
  | 0 => by simp
  | n + 1 => by
      rw [List.range_succ, List.pairwise_append, pairwise_range_iff P n]
      constructor
      · rintro ⟨h1, -, h2⟩ u hu v hv
        by_cases hun : u = n
        · subst hun
          exact h2 v (List.mem_range.mpr hv) u (List.mem_singleton_self _)
        · exact h1 u (by omega) v hv
      · intro h
        refine ⟨fun u hu v hv => h u (by omega) v hv, List.pairwise_singleton _ _, fun v hv u hu => ?_⟩
        rw [List.mem_singleton] at hu
        subst hu
        exact h u (Nat.lt_succ_self _) v (List.mem_range.mp hv)

theorem madeRows_map_id : ∀ (start : Nat) (ts : List Tm),
    (madeRows start ts).map Row.id = List.range' start ts.length
  | _, [] => rfl
  | start, t :: ts => by
      simp only [madeRows, List.map_cons, madeRows_map_id (start + 1) ts, List.length_cons,
        List.range'_succ]

theorem madeRows_map_label : ∀ (start : Nat) (ts : List Tm), (madeRows start ts).map Row.label = ts
  | _, [] => rfl
  | start, t :: ts => by simp only [madeRows, List.map_cons, madeRows_map_label (start + 1) ts]

theorem madeRows_nodup (start : Nat) (ts : List Tm) : (madeRows start ts).Nodup :=
  List.Nodup.of_map Row.id (by rw [madeRows_map_id]; exact List.nodup_range')

theorem madeRows_id_ge {start : Nat} {ts : List Tm} {row : Row} (h : row ∈ madeRows start ts) :
    start ≤ row.id := by
  have hm : row.id ∈ (madeRows start ts).map Row.id := List.mem_map_of_mem h
  rw [madeRows_map_id, List.mem_range'_1] at hm
  exact hm.1

theorem forall₂_map_range {α β : Type} [Inhabited α] (P : α → β → Prop) :
    ∀ (l : List α) (g : Nat → β),
      List.Forall₂ P l ((List.range l.length).map g) ↔ ∀ u < l.length, P (l.getD u default) (g u)
  | [], _ => by simp
  | a :: l, g => by
      rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map, List.forall₂_cons,
        forall₂_map_range P l (g ∘ Nat.succ)]
      constructor
      · rintro ⟨h0, h1⟩ u hu
        cases u with
        | zero => simpa using h0
        | succ u => simpa using h1 u (by omega)
      · intro h
        exact ⟨by simpa using h 0 (by omega), fun u hu => by simpa using h (u + 1) (by omega)⟩

theorem forall₂_map_range' {α β : Type} [Inhabited α] (P : α → β → Prop) (l : List α) (n : Nat)
    (hn : l.length = n) (g : Nat → β) :
    List.Forall₂ P l ((List.range n).map g) ↔ ∀ u < n, P (l.getD u default) (g u) := by
  subst hn
  exact forall₂_map_range P l g

/-- The count of a finite set of rows, by a list without repetition, whatever decides the
predicate. -/
theorem card_filter_congr (l : List Row) (hl : l.Nodup) (P : Row → Prop) {inst : DecidablePred P}
    (Q : Row → Bool) (hPQ : ∀ x ∈ l, P x ↔ Q x = true) :
    (@Finset.filter Row P inst l.toFinset).card = (l.filter Q).length := by
  have h1 : @Finset.filter Row P inst l.toFinset = (l.filter Q).toFinset := by
    ext x
    simp only [Finset.mem_filter, List.mem_toFinset, List.mem_filter]
    constructor
    · rintro ⟨hx, hp⟩
      exact ⟨hx, (hPQ x hx).mp hp⟩
    · rintro ⟨hx, hq⟩
      exact ⟨hx, (hPQ x hx).mpr hq⟩
  rw [h1, List.toFinset_card_of_nodup (hl.filter _)]

theorem present_nodup {s : St} (hs : WellFormed s) : s.present.Nodup :=
  List.Nodup.of_map Row.id hs.ids

/-! ## Fits is `Enabled` -/

theorem mem_taken {R : Rule} {s : St} {p : List Tm} {o : List Nat} {x : Row} :
    x ∈ (instSelection R s p o).taken ↔ ∃ u < R.takes.length, x = rowOf s (o.getD u 0) := by
  simp only [instSelection, List.mem_map, List.mem_range]
  exact ⟨fun ⟨u, hu, e⟩ => ⟨u, hu, e.symm⟩, fun ⟨u, hu, e⟩ => ⟨u, hu, e.symm⟩⟩

theorem mem_read {R : Rule} {s : St} {p : List Tm} {o : List Nat} {x : Row} :
    x ∈ (instSelection R s p o).read ↔ ∃ v < R.reads.length, x = rowOf s (o.getD (R.takes.length + v) 0) := by
  simp only [instSelection, List.mem_map, List.mem_range]
  exact ⟨fun ⟨u, hu, e⟩ => ⟨u, hu, e.symm⟩, fun ⟨u, hu, e⟩ => ⟨u, hu, e.symm⟩⟩

theorem enabled_iff (R : Rule) (s : St) (hs : WellFormed s) (p : List Tm) (o : List Nat) :
    Enabled Row.label (conf s).present ((instSelection R s p o).commit (T := Tm)) ↔ Fits R s o := by
  have huses : R.uses.length = R.takes.length + R.reads.length := List.length_append
  constructor
  · rintro ⟨hts, hks, hap, -, -⟩
    refine ⟨fun u hu => ?_, fun u hu hge v hv => ?_⟩
    · rw [← rowOf_mem_iff]
      by_cases hut : u < R.takes.length
      · have hx : rowOf s (o.getD u 0) ∈ (instSelection R s p o).taken := mem_taken.mpr ⟨u, hut, rfl⟩
        have := hts (List.mem_toFinset.mpr hx)
        exact List.mem_toFinset.mp this
      · have hx : rowOf s (o.getD u 0) ∈ (instSelection R s p o).read := by
          refine mem_read.mpr ⟨u - R.takes.length, by omega, ?_⟩
          rw [show R.takes.length + (u - R.takes.length) = u by omega]
        have := hks (List.mem_toFinset.mpr hx)
        exact List.mem_toFinset.mp this
    · intro e
      have hx : rowOf s (o.getD u 0) ∈ (instSelection R s p o).read := by
        refine mem_read.mpr ⟨u - R.takes.length, by omega, ?_⟩
        rw [show R.takes.length + (u - R.takes.length) = u by omega]
      have hy : rowOf s (o.getD v 0) ∈ (instSelection R s p o).taken := mem_taken.mpr ⟨v, hv, rfl⟩
      have hd := Finset.disjoint_left.mp hap (List.mem_toFinset.mpr hy)
      apply hd
      rw [← e]
      exact List.mem_toFinset.mpr hx
  · rintro ⟨hF1, hF2⟩
    refine ⟨fun x hx => ?_, fun x hx => ?_, ?_, ?_, fun q hq => by cases hq⟩
    · obtain ⟨u, hu, rfl⟩ := mem_taken.mp (List.mem_toFinset.mp hx)
      exact List.mem_toFinset.mpr ((rowOf_mem_iff s _).mpr (hF1 u (by omega)))
    · obtain ⟨v, hv, rfl⟩ := mem_read.mp (List.mem_toFinset.mp hx)
      exact List.mem_toFinset.mpr ((rowOf_mem_iff s _).mpr (hF1 _ (by omega)))
    · apply Finset.disjoint_left.mpr
      intro x hx hx'
      obtain ⟨u, hu, rfl⟩ := mem_taken.mp (List.mem_toFinset.mp hx)
      obtain ⟨v, hv, e⟩ := mem_read.mp (List.mem_toFinset.mp hx')
      exact hF2 (R.takes.length + v) (by omega) (by omega) u hu ((rowOf_eq_iff s _ _).mp e).symm
    · apply Finset.disjoint_left.mpr
      intro x hx hx'
      have h1 := madeRows_id_ge (List.mem_toFinset.mp hx)
      have h2 := hs.below x (List.mem_toFinset.mp hx')
      omega

/-! ## Solvable is `Consistent`, the guards are the checks -/

theorem uses_getD_left {R : Rule} {u : Nat} (hu : u < R.takes.length) :
    R.uses.getD u default = R.takes.getD u default := by
  simp only [Rule.uses]
  rw [List.getD_append _ _ _ _ hu]

theorem uses_getD_right {R : Rule} (v : Nat) :
    R.uses.getD (R.takes.length + v) default = R.reads.getD v default := by
  simp only [Rule.uses]
  rw [List.getD_append_right _ _ _ _ (Nat.le_add_right _ _), Nat.add_sub_cancel_left]

theorem map_getD {f : Tm → Tm} {l : List Tm} {u : Nat} (hu : u < l.length) :
    (l.map f).getD u default = f (l.getD u default) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hu,
    Option.map_some, Option.getD_some]

theorem models_problem_iff (R : Rule) (s : St) (hs : WellFormed s) (p : List Tm)
    (hp : ∀ q ∈ p, q.closed = true) (o : List Nat) (hF : Fits R s o) (σ : Nat → Tm) :
    synAction.Models σ ((instSelection R s p o).problem Row.label (instRule R s p) (conf s)) ↔
      Sol R s p o (mix R.nparams p σ) := by
  have huses : R.uses.length = R.takes.length + R.reads.length := List.length_append
  -- each selected label is present, closed, and its row's label
  have hlab : ∀ u < R.uses.length, ∃ l, labelOf s (o.getD u 0) = some l ∧
      (rowOf s (o.getD u 0)).label = l ∧ synAction.apply σ l = l := by
    intro u hu
    obtain ⟨l, hl⟩ := Option.isSome_iff_exists.mp (hF.1 u hu)
    have hmem := (rowOf_mem_iff s _).mpr (hF.1 u hu)
    refine ⟨l, hl, rowOf_label hl, ?_⟩
    have hc := hs.closed _ hmem
    rw [rowOf_label hl] at hc
    exact Tm.inst_closed hc σ Tm.fresh
  simp only [Selection.problem, conf, List.nil_append, SubstitutionAction.models_append]
  rw [Selection.models_equations_iff synAction σ Row.label (by simp [instRule, instSelection]),
    Selection.models_equations_iff synAction σ Row.label (by simp [instRule, instSelection])]
  simp only [instRule, instSelection]
  rw [forall₂_map_range' _ (R.takes.map (instTerm R s p)) R.takes.length (by simp),
    forall₂_map_range' _ (R.reads.map (instTerm R s p)) R.reads.length (by simp)]
  constructor
  · rintro ⟨⟨ht, hr⟩, htell⟩
    refine ⟨fun k hk => by simp [mix, hk], fun u hu => ?_, fun e he => ?_⟩
    · obtain ⟨l, hl, hrl, hσl⟩ := hlab u hu
      rw [hl]
      congr 1
      by_cases hut : u < R.takes.length
      · have h : synAction.apply σ ((R.takes.map (instTerm R s p)).getD u default) =
            synAction.apply σ (rowOf s (o.getD u 0)).label := ht u hut
        rw [map_getD hut, apply_instTerm R s p hp, hrl, hσl] at h
        rw [uses_getD_left hut, h]
      · have hv : u - R.takes.length < R.reads.length := by omega
        have e : R.takes.length + (u - R.takes.length) = u := by omega
        have h : synAction.apply σ ((R.reads.map (instTerm R s p)).getD (u - R.takes.length) default) =
            synAction.apply σ (rowOf s (o.getD (R.takes.length + (u - R.takes.length)) 0)).label :=
          hr _ hv
        rw [map_getD hv, apply_instTerm R s p hp, e, hrl, hσl] at h
        have hu' := uses_getD_right (R := R) (u - R.takes.length)
        rw [e] at hu'
        rw [hu']
        exact h.symm
    · have h := htell (instTerm R s p e.1, instTerm R s p e.2) (List.mem_map_of_mem he)
      simp only [SubstitutionAction.Solves, apply_instTerm R s p hp] at h
      exact h
  · rintro ⟨-, hu, htell⟩
    refine ⟨⟨fun u hut => ?_, fun v hv => ?_⟩, fun e he => ?_⟩
    · obtain ⟨l, hl, hrl, hσl⟩ := hlab u (by omega)
      have h := hu u (by omega)
      rw [hl, uses_getD_left hut] at h
      show synAction.apply σ ((R.takes.map (instTerm R s p)).getD u default) =
        synAction.apply σ (rowOf s (o.getD u 0)).label
      rw [map_getD hut, apply_instTerm R s p hp, hrl, hσl]
      exact (Option.some.inj h).symm
    · obtain ⟨l, hl, hrl, hσl⟩ := hlab (R.takes.length + v) (by omega)
      have h := hu (R.takes.length + v) (by omega)
      rw [hl, uses_getD_right] at h
      show synAction.apply σ ((R.reads.map (instTerm R s p)).getD v default) =
        synAction.apply σ (rowOf s (o.getD (R.takes.length + v) 0)).label
      rw [map_getD hv, apply_instTerm R s p hp, hrl, hσl]
      exact (Option.some.inj h).symm
    · obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
      show synAction.apply σ (instTerm R s p e'.1) = synAction.apply σ (instTerm R s p e'.2)
      rw [apply_instTerm R s p hp, apply_instTerm R s p hp]
      exact htell e' he'

theorem check_holds_iff (R : Rule) (s : St) (hs : WellFormed s) (p : List Tm)
    (hp : ∀ q ∈ p, q.closed = true) (σ : Nat → Tm) (host : String → List Tm → Prop) :
    ∀ (g : Guard) (c : Check Tm), Guard.toCheck? (instTerm R s p) g = some c →
      (c.Holds synAction σ Row.label (conf s).present ↔ g.Holds host s (mix R.nparams p σ))
  | .ask a b, c, h => by
      simp only [Guard.toCheck?, Option.some.injEq] at h
      subst h
      show synAction.apply σ (instTerm R s p a) = synAction.apply σ (instTerm R s p b) ↔ _
      rw [apply_instTerm R s p hp, apply_instTerm R s p hp]
      rfl
  | .absent q, c, h => by
      simp only [Guard.toCheck?, Option.some.injEq] at h
      subst h
      show (∀ o ∈ (conf s).present, ¬ synAction.apply σ (instTerm R s p q) = synAction.apply σ o.label) ↔
        ∀ row ∈ s.present, row.label ≠ q.inst (mix R.nparams p σ) (openFresh s.names)
      rw [apply_instTerm R s p hp]
      constructor
      · intro h' row hrow e
        apply h' row (List.mem_toFinset.mpr hrow)
        rw [← e]
        exact (Tm.inst_closed (hs.closed row hrow) σ Tm.fresh).symm
      · intro h' row hrow e
        apply h' row (List.mem_toFinset.mp hrow)
        rw [e]
        exact (Tm.inst_closed (hs.closed row (List.mem_toFinset.mp hrow)) σ Tm.fresh).symm
  | .count q n, c, h => by
      simp only [Guard.toCheck?, Option.some.injEq] at h
      subst h
      show (Check.matches synAction σ Row.label (conf s).present (instTerm R s p q)).card = n ↔ _
      unfold Check.matches
      simp only [conf]
      rw [card_filter_congr s.present (present_nodup hs) _
        (fun row => decide (row.label = q.inst (mix R.nparams p σ) (openFresh s.names)))]
      · exact Iff.rfl
      · intro row hrow
        rw [decide_eq_true_eq]
        have hc : synAction.apply σ row.label = row.label := Tm.inst_closed (hs.closed row hrow) σ Tm.fresh
        show synAction.apply σ (instTerm R s p q) = synAction.apply σ row.label ↔ _
        rw [apply_instTerm R s p hp, hc]
        exact eq_comm
  | .host _ _, c, h => by simp [Guard.toCheck?] at h

/-! ## The bridge -/

/-- **The reference is the first-order step's admission**, with the frame conjuncts the one-frame
step leaves to its frame. -/
theorem firstOrder_admits_iff (R : Rule) (hR : InClass R) (s : St) (hs : WellFormed s)
    (p : List Tm) (hp : ∀ q ∈ p, q.closed = true) (o : List Nat) (host : String → List Tm → Prop) :
    Admits R s p o host ↔
      ((∀ t ∈ R.opened, ∀ a ∈ t.atoms, AtomAtFrame R s p a) ∧ (∀ u < R.takes.length, o.getD u 0 ≠ 0)) ∧
      (AnnotatedRuns.firstOrder synAction Row.label).Admits (s := conf s) (instFiring R s p o) := by
  have hfo : (AnnotatedRuns.firstOrder synAction Row.label).Admits (s := conf s) (instFiring R s p o) ↔
      (instSelection R s p o).Valid synAction Row.label (instRule R s p) (conf s) :=
    PredicateQueryAdmission.valid_empty_iff _ _ _ _ _
  rw [hfo]
  have hnodup := taken_nodup_iff R s p o
  constructor
  · rintro ⟨⟨hframe, hnz, hdist⟩, hF, ⟨σ₀, hσ₀⟩, hg⟩
    refine ⟨⟨hframe, hnz⟩, ⟨hnodup.mpr hdist, madeRows_nodup _ _, by simp [instRule, instSelection],
      by simp [instRule, instSelection], madeRows_map_label _ _, (enabled_iff R s hs p o).mpr hF,
      ⟨σ₀, ?_⟩, ?_⟩⟩
    · rw [models_problem_iff R s hs p hp o hF, mix_of_sol hσ₀]
      exact hσ₀
    · intro c hc σ hσ
      obtain ⟨g, hgm, hgc⟩ := List.mem_filterMap.mp hc
      have hsol := (models_problem_iff R s hs p hp o hF σ).mp hσ
      exact (check_holds_iff R s hs p hp σ host g c hgc).mpr (hg g hgm _ hsol)
  · rintro ⟨⟨hframe, hnz⟩, hv⟩
    have hF := (enabled_iff R s hs p o).mp hv.occurrences
    obtain ⟨σ₀, hσ₀⟩ := hv.consistent
    refine ⟨⟨hframe, hnz, hnodup.mp hv.take_distinct⟩, hF,
      ⟨_, (models_problem_iff R s hs p hp o hF σ₀).mp hσ₀⟩, fun g hgm σ hσ => ?_⟩
    have hm : synAction.Models σ ((instSelection R s p o).problem Row.label (instRule R s p) (conf s)) := by
      rw [models_problem_iff R s hs p hp o hF, mix_of_sol hσ]
      exact hσ
    cases hgc : Guard.toCheck? (instTerm R s p) g with
    | none =>
        cases g with
        | host h args => exact absurd (hR.noHostGuards _ hgm) (by simp [Guard.isHost])
        | _ => simp [Guard.toCheck?] at hgc
    | some c =>
        have hcm : c ∈ (instRule R s p).checks := List.mem_filterMap.mpr ⟨g, hgm, hgc⟩
        have := (check_holds_iff R s hs p hp σ host g c hgc).mp (hv.checks c hcm σ hm)
        rw [mix_of_sol hσ] at this
        exact this
where
  taken_nodup_iff (R : Rule) (s : St) (p : List Tm) (o : List Nat) :
      (instSelection R s p o).taken.Nodup ↔ ∀ u < R.takes.length, ∀ v < u, o.getD u 0 ≠ o.getD v 0 := by
    show ((List.range R.takes.length).map fun u => rowOf s (o.getD u 0)).Nodup ↔ _
    unfold List.Nodup
    rw [List.pairwise_map, pairwise_range_iff]
    simp only [ne_eq, rowOf_eq_iff]
    constructor
    · intro h u hu v hv e
      exact h u hu v hv e.symm
    · intro h u hu v hv e
      exact h u hu v hv e.symm

/-- **The program admits exactly when the first-order step admits the instance**, with the frame
conjuncts, on well-formed states and closed parameters, for every rule of the class. -/
theorem specialized_admits_iff_firstOrder (R : Rule) (hR : InClass R) (s : St) (hs : WellFormed s)
    (p : List Tm) (hp : ∀ q ∈ p, q.closed = true) (o : List Nat) :
    ((compile R).admits ⟨p, o⟩ s).1 = .admitted ↔
      ((∀ t ∈ R.opened, ∀ a ∈ t.atoms, AtomAtFrame R s p a) ∧ (∀ u < R.takes.length, o.getD u 0 ≠ 0)) ∧
      (AnnotatedRuns.firstOrder synAction Row.label).Admits (s := conf s) (instFiring R s p o) := by
  rw [← firstOrder_admits_iff R hR s hs p hp o (fun _ _ => True)]
  have hv := (specialized_admission R hR s p o (fun _ _ => True)).1
  constructor
  · intro h
    rw [h] at hv
    exact hv
  · intro hA
    rcases hval : ((compile R).admits ⟨p, o⟩ s).1 with _ | r
    · rfl
    · rw [hval] at hv
      exfalso
      cases r with
      | shapes => exact hv hA.1
      | fits => exact hv.2 hA.2.1
      | unsolvable => exact hv.2.2 hA.2.2.1
      | guard i =>
          obtain ⟨-, -, -, g, hg, hno, -⟩ := hv
          exact hno (hA.2.2.2 g (List.mem_of_getElem? hg))

#print axioms firstOrder_admits_iff
#print axioms specialized_admits_iff_firstOrder

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SpecializedAdmission
