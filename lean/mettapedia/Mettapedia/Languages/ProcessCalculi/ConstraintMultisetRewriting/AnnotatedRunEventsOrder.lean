import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunEvents

/-!
# Prefixes of traces are initial parts of configurations

A trace is a prefix of another when some run of the second begins with a run of the first. A
configuration `U` is an initial part of `X` (`Extends`) when its firings are among those of `X`,
every cause in `X` of a member of `U` is in `U`, and `U` records the order `X` records between its
members. In the fragment of `AnnotatedRunEvents`:

* **A prefix gives an initial part** (`prefix_extends`).
* **An initial part gives a prefix** (`extends_prefix`): what is left of a configuration after an
  initial part is a configuration from where the initial part ends (`residual_isConfiguration`),
  so a run of it continues the run of the initial part to a run of the whole.
* Hence, for runs of the fragment, `u` extends to a run round equivalent to `w` exactly when the
  configuration of `u` is an initial part of that of `w` (`prefix_iff_extends`): the bijection of
  traces and configurations respects their orders.
* **Events persist** (`causes_eq_of_extends`, `events_mono`, `events_prefix`): in an initial part
  a member has the causes it has in the whole, so every event of a prefix is an event of every
  extension.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunEvents

open AnnotatedRuns
open AnnotatedRunUnfolding (Flow ReadBeforeTake InhibitsAt)
open MeTTaCalculus.OccurrenceCommits (regionOf mem_regionOf fire mem_fire)

/-! ## Precedence in a concatenation -/

section Precedence

variable {α : Type*}

theorem precedes_append_left_mem : ∀ {u v : List α} {g f : α}, (u ++ v).Nodup → f ∈ u →
    Precedes (u ++ v) g f → g ∈ u
  | [], _, _, _, _, hf, _ => by simp at hf
  | a :: u, v, g, f, nodup, hf, h => by
      rw [List.cons_append, precedes_cons] at h
      have fresh : a ∉ u ++ v := (List.nodup_cons.mp nodup).1
      rcases h with ⟨rfl, _⟩ | h
      · exact List.mem_cons_self
      · rcases List.mem_cons.mp hf with rfl | hfu
        · exact absurd h.mem_right fresh
        · exact List.mem_cons_of_mem _
            (precedes_append_left_mem (List.nodup_cons.mp nodup).2 hfu h)

theorem precedes_append_iff_left : ∀ {u v : List α} {g h : α}, (u ++ v).Nodup → g ∈ u → h ∈ u →
    (Precedes (u ++ v) g h ↔ Precedes u g h)
  | [], _, _, _, _, hg, _ => by simp at hg
  | a :: u, v, g, h, nodup, hg, hh => by
      rw [List.cons_append, precedes_cons, precedes_cons]
      have fresh : a ∉ u ++ v := (List.nodup_cons.mp nodup).1
      have freshU : a ∉ u := fun inU => fresh (List.mem_append_left _ inU)
      by_cases ga : g = a
      · subst ga
        have left : ¬ Precedes (u ++ v) g h := fun p => fresh p.mem_left
        have right : ¬ Precedes u g h := fun p => freshU p.mem_left
        rcases List.mem_cons.mp hh with rfl | hhu
        · exact iff_of_false (fun p => p.elim (fun q => fresh q.2) left)
            (fun p => p.elim (fun q => freshU q.2) right)
        · exact ⟨fun _ => Or.inl ⟨rfl, hhu⟩, fun _ => Or.inl ⟨rfl, List.mem_append_left _ hhu⟩⟩
      · have hgu : g ∈ u := (List.mem_cons.mp hg).resolve_left ga
        rcases List.mem_cons.mp hh with rfl | hhu
        · exact iff_of_false (fun p => p.elim (fun q => ga q.1) fun q => fresh q.mem_right)
            (fun p => p.elim (fun q => ga q.1) fun q => freshU q.mem_right)
        · rw [precedes_append_iff_left (List.nodup_cons.mp nodup).2 hgu hhu]
          exact ⟨fun p => p.elim (fun q => absurd q.1 ga) Or.inr,
            fun p => p.elim (fun q => absurd q.1 ga) Or.inr⟩

theorem precedes_append_iff_right : ∀ {u v : List α} {g h : α}, g ∉ u →
    (Precedes (u ++ v) g h ↔ Precedes v g h)
  | [], _, _, _, _ => by simp
  | a :: u, v, g, h, hg => by
      rw [List.cons_append, precedes_cons]
      have ga : g ≠ a := fun same => hg (same ▸ List.mem_cons_self)
      rw [precedes_append_iff_right (fun inU => hg (List.mem_cons_of_mem _ inU))]
      exact ⟨fun p => p.elim (fun q => absurd q.1 ga) id, Or.inr⟩

theorem precedes_append_cross {u v : List α} {g h : α} (hg : g ∈ u) (hh : h ∈ v) :
    Precedes (u ++ v) g h := by
  induction u with
  | nil => simp at hg
  | cons a u ih =>
      rw [List.cons_append, precedes_cons]
      rcases List.mem_cons.mp hg with rfl | hgu
      · exact Or.inl ⟨rfl, List.mem_append_right _ hh⟩
      · exact Or.inr (ih hgu)

end Precedence

universe uT uS uO
variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]

/-! ## Initial parts -/

/-- `U` is an initial part of `X`: its firings are among those of `X`, every cause in `X` of a
member is a member, and it records the order `X` records between its members. -/
structure Extends (U X : Config T S O) : Prop where
  subset : U.firings ⊆ X.firings
  down : ∀ f ∈ U.firings, ∀ g, Edge X g f → g ∈ U.firings
  before : ∀ g h, U.before g h ↔ X.before g h ∧ g ∈ U.firings ∧ h ∈ U.firings

section Order

variable (A : SubstitutionAction T S) (label : O → T)

/-- **A prefix gives an initial part.** -/
theorem prefix_extends {C : Configuration T O} {u v : List (Firing T S O)}
    (run : Executable A label C (u ++ v)) (fragment : Fragment C (u ++ v)) :
    Extends (configOf label u) (configOf label (u ++ v)) where
  subset f hf := mem_configOf_firings.mpr (List.mem_append_left _ (mem_configOf_firings.mp hf))
  down f hf g edge := mem_configOf_firings.mpr
    (precedes_append_left_mem fragment.nodup (mem_configOf_firings.mp hf)
      (precedes_of_edge A label run fragment edge))
  before g h := by
    rw [configOf_before, configOf_before, mem_configOf_firings, mem_configOf_firings]
    constructor
    · rintro ⟨precedes, pair⟩
      have hg := precedes.mem_left
      have hh := precedes.mem_right
      exact ⟨⟨(precedes_append_iff_left fragment.nodup hg hh).mpr precedes, pair⟩, hg, hh⟩
    · rintro ⟨⟨precedes, pair⟩, hg, hh⟩
      exact ⟨(precedes_append_iff_left fragment.nodup hg hh).mp precedes, pair⟩

theorem executable_append : ∀ {C : Configuration T O} {u v : List (Firing T S O)},
    Executable A label C u → Executable A label (follow label C u) v → Executable A label C (u ++ v)
  | _, [], _, _, later => later
  | _, _ :: _, _, run, later => ⟨run.1, executable_append run.2 later⟩

theorem presentAfter_shift {C D : Configuration T O} {U P : Finset (Firing T S O)}
    (base : D.present = presentAfter C U) [DecidableEq (Firing T S O)]
    (apart : ∀ o, (∃ g ∈ U, o ∈ g.selection.taken) → ∀ g ∈ P, o ∉ g.selection.made) :
    presentAfter D P = presentAfter C (U ∪ P) := by
  ext o
  have inD : o ∈ D.present ↔ (o ∈ C.present ∨ ∃ g ∈ U, o ∈ g.selection.made) ∧
      ∀ g ∈ U, o ∉ g.selection.taken := by
    rw [base]
    exact mem_presentAfter
  rw [mem_presentAfter, mem_presentAfter, inD]
  by_cases taken : ∃ g ∈ U, o ∈ g.selection.taken
  · obtain ⟨g, hg, tg⟩ := taken
    constructor
    · intro left
      rcases left.1 with inDPart | ⟨h, hh, made⟩
      · exact absurd tg (inDPart.2 g hg)
      · exact absurd made (apart o ⟨g, hg, tg⟩ h hh)
    · intro right
      exact absurd tg (right.2 g (Finset.mem_union_left _ hg))
  · have notTaken : ∀ g ∈ U, o ∉ g.selection.taken := fun g hg t => taken ⟨g, hg, t⟩
    constructor
    · intro left
      have notP := left.2
      have allNot : ∀ g ∈ U ∪ P, o ∉ g.selection.taken := by
        intro g hg
        rcases Finset.mem_union.mp hg with hgU | hgP
        · exact notTaken g hgU
        · exact notP g hgP
      rcases left.1 with inDPart | ⟨h, hh, made⟩
      · rcases inDPart.1 with present | ⟨h, hh, made⟩
        · exact ⟨Or.inl present, allNot⟩
        · exact ⟨Or.inr ⟨h, Finset.mem_union_left _ hh, made⟩, allNot⟩
      · exact ⟨Or.inr ⟨h, Finset.mem_union_right _ hh, made⟩, allNot⟩
    · intro right
      refine ⟨?_, fun g hg => right.2 g (Finset.mem_union_right _ hg)⟩
      rcases right.1 with present | ⟨h, hh, made⟩
      · exact Or.inl ⟨Or.inl present, notTaken⟩
      · rcases Finset.mem_union.mp hh with hU | hP
        · exact Or.inl ⟨Or.inr ⟨h, hU, made⟩, notTaken⟩
        · exact Or.inr ⟨h, hP, made⟩

theorem regionOf_presentAfter_union_outside [DecidableEq (Firing T S O)] {C : Configuration T O}
    {P Q : Finset (Firing T S O)} {region : T → Bool}
    (outside : ∀ g ∈ Q, ∀ o, (o ∈ g.selection.taken ∨ o ∈ g.selection.made) →
      region (label o) = false) :
    regionOf label (presentAfter C (P ∪ Q)) region = regionOf label (presentAfter C P) region := by
  ext o
  rw [mem_regionOf, mem_regionOf, mem_presentAfter, mem_presentAfter]
  constructor
  · rintro ⟨⟨source, notTaken⟩, inside⟩
    refine ⟨⟨?_, fun g hg => notTaken g (Finset.mem_union_left _ hg)⟩, inside⟩
    rcases source with present | ⟨g, hg, made⟩
    · exact Or.inl present
    · rcases Finset.mem_union.mp hg with hP | hQ
      · exact Or.inr ⟨g, hP, made⟩
      · have out := outside g hQ o (Or.inr made)
        rw [inside] at out
        exact absurd out (by decide)
  · rintro ⟨⟨source, notTaken⟩, inside⟩
    refine ⟨⟨?_, fun g hg => ?_⟩, inside⟩
    · rcases source with present | ⟨g, hg, made⟩
      · exact Or.inl present
      · exact Or.inr ⟨g, Finset.mem_union_left _ hg, made⟩
    · rcases Finset.mem_union.mp hg with hP | hQ
      · exact notTaken g hP
      · intro taken
        have out := outside g hQ o (Or.inl taken)
        rw [inside] at out
        exact absurd out (by decide)

end Order

/-! ## What is left after an initial part -/

open Classical in
/-- What is left of a configuration after an initial part, with the order it records there. -/
noncomputable def residual (X U : Config T S O) : Config T S O :=
  ⟨X.firings \ U.firings, fun g h => X.before g h ∧ g ∉ U.firings ∧ h ∉ U.firings⟩

omit [DecidableEq O] in
theorem mem_residual {X U : Config T S O} {g : Firing T S O} :
    g ∈ (residual X U).firings ↔ g ∈ X.firings ∧ g ∉ U.firings := by
  classical
  simp [residual]

section Residual

variable (A : SubstitutionAction T S) (label : O → T)

/-- **What is left after an initial part is a configuration from where the part ends.** -/
theorem residual_isConfiguration {C : Configuration T O} {X : Config T S O}
    {u : List (Firing T S O)} (config : IsConfiguration A label C X)
    (run : Executable A label C u) (fragment : Fragment C u)
    (initial : Extends (configOf label u) X) :
    IsConfiguration A label (follow label C u) (residual X (configOf label u)) := by
  classical
  have present : (follow label C u).present = presentAfter C (configOf label u).firings :=
    follow_present_eq A label run fragment
  have inX : ∀ {g : Firing T S O}, g ∈ (configOf label u).firings → g ∈ X.firings :=
    fun hg => initial.subset hg
  have takenGone : ∀ o (g : Firing T S O), g ∈ (configOf label u).firings → o ∈ g.selection.taken →
      ∀ f ∈ (residual X (configOf label u)).firings,
        o ∉ f.selection.taken ∧ o ∉ f.selection.read := by
    intro o g hg tg f hf
    obtain ⟨fX, fU⟩ := mem_residual.mp hf
    have ne : g ≠ f := fun same => fU (same ▸ hg)
    refine ⟨fun tf => config.takes g (inX hg) f fX ne o tg tf, fun rf => ?_⟩
    exact fU (initial.down g hg f ⟨fX, inX hg, Or.inr (Or.inl ⟨o, rf, tg⟩)⟩)
  have remade : ∀ o, (∃ g ∈ (configOf label u).firings, o ∈ g.selection.taken) →
      ∀ f ∈ (residual X (configOf label u)).firings, o ∉ f.selection.made := by
    rintro o ⟨g, hg, tg⟩ f hf mf
    obtain ⟨fX, fU⟩ := mem_residual.mp hf
    exact fU (initial.down g hg f ⟨fX, inX hg, Or.inl ⟨o, mf, Or.inl tg⟩⟩)
  refine ⟨fun f hf => config.static f (mem_residual.mp hf).1,
    fun f hf => config.shape f (mem_residual.mp hf).1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f hf o made inPresent
    obtain ⟨fX, fU⟩ := mem_residual.mp hf
    rw [present, mem_presentAfter] at inPresent
    rcases inPresent.1 with old | ⟨g, hg, madeG⟩
    · exact config.fresh f fX o made old
    · exact config.makers g (inX hg) f fX (fun same => fU (same ▸ hg)) o madeG made
  · intro f hf g hg ne
    exact config.makers f (mem_residual.mp hf).1 g (mem_residual.mp hg).1 ne
  · intro f hf g hg ne
    exact config.takes f (mem_residual.mp hf).1 g (mem_residual.mp hg).1 ne
  · intro f hf o used
    obtain ⟨fX, _⟩ := mem_residual.mp hf
    by_cases taken : ∃ g ∈ (configOf label u).firings, o ∈ g.selection.taken
    · obtain ⟨g, hg, tg⟩ := taken
      have gone := takenGone o g hg tg f hf
      rcases used with t | r
      · exact absurd t gone.1
      · exact absurd r gone.2
    · have notTaken : ∀ g ∈ (configOf label u).firings, o ∉ g.selection.taken :=
        fun g hg t => taken ⟨g, hg, t⟩
      rcases config.closed f fX o used with old | ⟨g, hg, madeG⟩
      · exact Or.inl (present ▸ mem_presentAfter.mpr ⟨Or.inl old, notTaken⟩)
      · by_cases gU : g ∈ (configOf label u).firings
        · exact Or.inl (present ▸ mem_presentAfter.mpr ⟨Or.inr ⟨g, gU, madeG⟩, notTaken⟩)
        · exact Or.inr ⟨g, mem_residual.mpr ⟨hg, gU⟩, madeG⟩
  · intro f hf g hg ne inhibits
    obtain ⟨fX, fU⟩ := mem_residual.mp hf
    obtain ⟨gX, gU⟩ := mem_residual.mp hg
    rcases config.oriented f fX g gX ne inhibits with before | before
    · exact Or.inl ⟨before, fU, gU⟩
    · exact Or.inr ⟨before, gU, fU⟩
  · rintro g h ⟨before, gU, hU⟩
    obtain ⟨gX, hX, ne, pair⟩ := config.before_spec g h before
    exact ⟨mem_residual.mpr ⟨gX, gU⟩, mem_residual.mpr ⟨hX, hU⟩, ne, pair⟩
  · intro g cycle
    have edgeLift : ∀ {a b : Firing T S O}, Edge (residual X (configOf label u)) a b → Edge X a b := by
      rintro a b ⟨ha, hb, relation⟩
      refine ⟨(mem_residual.mp ha).1, (mem_residual.mp hb).1, ?_⟩
      rcases relation with flow | read | ⟨before, _⟩
      · exact Or.inl flow
      · exact Or.inr (Or.inl read)
      · exact Or.inr (Or.inr before)
    have lift : ∀ {a b : Firing T S O}, Relation.TransGen (Edge (residual X (configOf label u))) a b →
        Relation.TransGen (Edge X) a b := by
      intro a b path
      induction path with
      | single edge => exact .single (edgeLift edge)
      | tail _ edge ih => exact ih.tail (edgeLift edge)
    exact config.acyclic g (lift cycle)
  · intro q hq query member σ
    obtain ⟨qX, qU⟩ := mem_residual.mp hq
    rw [presentAfter_shift (C := C) present
      (fun o t f hf => remade o t f (mem_writersBefore.mp hf).1)]
    have split : (configOf label u).firings ∪ writersBefore label (residual X (configOf label u)) q =
        writersBefore label X q ∪ ((configOf label u).firings.filter
          fun g => g ∉ writersBefore label X q) := by
      ext g
      rw [Finset.mem_union, Finset.mem_union, Finset.mem_filter, mem_writersBefore, mem_writersBefore]
      constructor
      · rintro (gU | ⟨gR, inhibits, before, _, _⟩)
        · by_cases w : g ∈ writersBefore label X q
          · exact Or.inl (mem_writersBefore.mp w)
          · exact Or.inr ⟨gU, fun inW => w (mem_writersBefore.mpr inW)⟩
        · exact Or.inl ⟨(mem_residual.mp gR).1, inhibits, before⟩
      · rintro (⟨gX, inhibits, before⟩ | ⟨gU, _⟩)
        · by_cases gU : g ∈ (configOf label u).firings
          · exact Or.inl gU
          · exact Or.inr ⟨mem_residual.mpr ⟨gX, gU⟩, inhibits, before, gU, qU⟩
        · exact Or.inl gU
    rw [split, regionOf_presentAfter_union_outside label]
    · exact config.observed q qX query member σ
    · intro g hg o written
      obtain ⟨gU, notWriter⟩ := Finset.mem_filter.mp hg
      cases inside : query.region σ (label o) with
      | false => rfl
      | true =>
          exfalso
          have inhibits : Inhibits label g q := ⟨σ, query, member, o, written, inside⟩
          have ne : g ≠ q := fun same => qU (same ▸ gU)
          rcases config.oriented g (inX gU) q qX ne inhibits with before | before
          · exact notWriter (mem_writersBefore.mpr ⟨inX gU, inhibits, before⟩)
          · exact qU (initial.down g gU q ⟨qX, inX gU, Or.inr (Or.inr before)⟩)
  · obtain ⟨σ, base, all⟩ := config.joint
    refine ⟨σ, ?_, fun f hf => all f (mem_residual.mp hf).1⟩
    rw [follow_equations, A.models_append, models_flatMap_added A label]
    exact ⟨base, fun f hf => all f (inX (mem_configOf_firings.mpr hf))⟩

/-- **An initial part gives a prefix**: a run of an initial part of a configuration continues to a
run of the whole configuration. -/
theorem extends_prefix {C : Configuration T O} {X : Config T S O} {u : List (Firing T S O)}
    (config : IsConfiguration A label C X) (run : Executable A label C u) (fragment : Fragment C u)
    (initial : Extends (configOf label u) X) :
    ∃ v, Executable A label C (u ++ v) ∧ Fragment C (u ++ v) ∧ configOf label (u ++ v) = X := by
  classical
  obtain ⟨v, runV, fragmentV, sameV⟩ :=
    exists_run A label _ rfl (residual_isConfiguration A label config run fragment initial)
  have memV : ∀ g, g ∈ v ↔ g ∈ X.firings ∧ g ∉ (configOf label u).firings := by
    intro g
    rw [← mem_configOf_firings (label := label) (w := v), sameV]
    exact mem_residual
  have memU : ∀ g, g ∈ u ↔ g ∈ (configOf label u).firings := fun g => mem_configOf_firings.symm
  have inX : ∀ {g : Firing T S O}, g ∈ u ++ v → g ∈ X.firings := by
    intro g hg
    rcases List.mem_append.mp hg with hu | hv
    · exact initial.subset ((memU g).mp hu)
    · exact ((memV g).mp hv).1
  have beforeV : ∀ g h, beforeOf label v g h ↔ X.before g h ∧ g ∉ (configOf label u).firings ∧
      h ∉ (configOf label u).firings := fun g h =>
    Iff.of_eq (congrFun (congrFun (congrArg Config.before sameV) g) h)
  have nodup : (u ++ v).Nodup := by
    refine List.nodup_append.mpr ⟨fragment.nodup, fragmentV.nodup, ?_⟩
    intro a ha b hb same
    subst same
    exact ((memV a).mp hb).2 ((memU a).mp ha)
  refine ⟨v, executable_append A label run runV, ⟨fun g hg => config.static g (inX hg), nodup,
    fun g hg => config.fresh g (inX hg), fun g hg h hh ne => config.makers g (inX hg) h (inX hh) ne⟩,
    Config.ext ?_ ?_⟩
  · ext g
    rw [mem_configOf_firings, List.mem_append]
    constructor
    · intro hg
      exact inX (List.mem_append.mpr hg)
    · intro hg
      by_cases gU : g ∈ (configOf label u).firings
      · exact Or.inl ((memU g).mpr gU)
      · exact Or.inr ((memV g).mpr ⟨hg, gU⟩)
  · funext g h
    apply propext
    rw [configOf_before]
    constructor
    · rintro ⟨precedes, pair⟩
      by_cases gu : g ∈ u
      · by_cases hu : h ∈ u
        · have inPart : beforeOf label u g h :=
            ⟨(precedes_append_iff_left nodup gu hu).mp precedes, pair⟩
          exact ((initial.before g h).mp inPart).1
        · have hv : h ∈ v := (List.mem_append.mp precedes.mem_right).resolve_left hu
          have gX := initial.subset ((memU g).mp gu)
          have hX := ((memV h).mp hv).1
          have ne : g ≠ h := fun same => hu (same ▸ gu)
          have oriented : X.before g h ∨ X.before h g := by
            rcases pair with inhibits | inhibits
            · exact config.oriented g gX h hX ne inhibits
            · exact (config.oriented h hX g gX ne.symm inhibits).symm
          rcases oriented with before | before
          · exact before
          · exact absurd (initial.down g ((memU g).mp gu) h ⟨hX, gX, Or.inr (Or.inr before)⟩)
              ((memV h).mp hv).2
      · have inV := (precedes_append_iff_right (v := v) gu).mp precedes
        exact ((beforeV g h).mp ⟨inV, pair⟩).1
    · intro before
      obtain ⟨gX, hX, ne, pair⟩ := config.before_spec g h before
      by_cases gU : g ∈ (configOf label u).firings
      · by_cases hU : h ∈ (configOf label u).firings
        · obtain ⟨precedes, _⟩ := (initial.before g h).mpr ⟨before, gU, hU⟩
          exact ⟨(precedes_append_iff_left nodup ((memU g).mpr gU) ((memU h).mpr hU)).mpr precedes,
            pair⟩
        · exact ⟨precedes_append_cross ((memU g).mpr gU) ((memV h).mpr ⟨hX, hU⟩), pair⟩
      · by_cases hU : h ∈ (configOf label u).firings
        · exact absurd (initial.down h hU g ⟨gX, hX, Or.inr (Or.inr before)⟩) gU
        · obtain ⟨precedes, _⟩ := (beforeV g h).mpr ⟨before, gU, hU⟩
          exact ⟨(precedes_append_iff_right (fun gu => gU ((memU g).mp gu))).mpr precedes, pair⟩

/-- **The bijection respects the orders.** For runs of the fragment from `C`, `u` extends to a run
round equivalent to `w` exactly when the configuration of `u` is an initial part of that of
`w`. -/
theorem prefix_iff_extends {C : Configuration T O} {u w : List (Firing T S O)}
    (runU : Executable A label C u) (fragmentU : Fragment C u)
    (runW : Executable A label C w) (fragmentW : Fragment C w) :
    (∃ v, Executable A label C (u ++ v) ∧ Fragment C (u ++ v) ∧ RoundEquiv A label C (u ++ v) w) ↔
      Extends (configOf label u) (configOf label w) := by
  constructor
  · rintro ⟨v, run, fragment, equivalent⟩
    rw [← configOf_eq_of_roundEquiv A label equivalent fragment.static]
    exact prefix_extends A label run fragment
  · intro initial
    obtain ⟨v, run, fragment, same⟩ :=
      extends_prefix A label (configOf_isConfiguration A label runW fragmentW) runU fragmentU initial
    exact ⟨v, run, fragment, roundEquiv_of_configOf_eq A label run runW fragment fragmentW same⟩

end Residual

/-! ## Events persist -/

omit [DecidableEq O] in
/-- In an initial part, a member has the causes it has in the whole. -/
theorem causes_eq_of_extends {U X : Config T S O} (initial : Extends U X) {f : Firing T S O}
    (hf : f ∈ U.firings) : causes U f = causes X f := by
  ext g
  change Relation.TransGen (Edge U) g f ↔ Relation.TransGen (Edge X) g f
  constructor
  · intro path
    clear hf
    induction path with
    | single edge =>
        obtain ⟨ha, hb, relation⟩ := edge
        refine .single ⟨initial.subset ha, initial.subset hb, ?_⟩
        rcases relation with flow | read | before
        · exact Or.inl flow
        · exact Or.inr (Or.inl read)
        · exact Or.inr (Or.inr ((initial.before _ _).mp before).1)
    | tail _ edge ih =>
        obtain ⟨ha, hb, relation⟩ := edge
        refine ih.tail ⟨initial.subset ha, initial.subset hb, ?_⟩
        rcases relation with flow | read | before
        · exact Or.inl flow
        · exact Or.inr (Or.inl read)
        · exact Or.inr (Or.inr ((initial.before _ _).mp before).1)
  · intro path
    revert hf
    induction path with
    | single edge =>
        intro hf
        have hg := initial.down _ hf _ edge
        obtain ⟨_, _, relation⟩ := edge
        refine .single ⟨hg, hf, ?_⟩
        rcases relation with flow | read | before
        · exact Or.inl flow
        · exact Or.inr (Or.inl read)
        · exact Or.inr (Or.inr ((initial.before _ _).mpr ⟨before, hg, hf⟩))
    | tail _ edge ih =>
        intro hf
        have hc := initial.down _ hf _ edge
        obtain ⟨_, _, relation⟩ := edge
        refine (ih hc).tail ⟨hc, hf, ?_⟩
        rcases relation with flow | read | before
        · exact Or.inl flow
        · exact Or.inr (Or.inl read)
        · exact Or.inr (Or.inr ((initial.before _ _).mpr ⟨before, hc, hf⟩))

omit [DecidableEq O] in
/-- **Events persist**: every event of an initial part is an event of the whole. -/
theorem events_mono {U X : Config T S O} (initial : Extends U X) : events U ⊆ events X := by
  rintro ⟨f, K⟩ ⟨hf, hK⟩
  refine ⟨initial.subset hf, ?_⟩
  change K = causes X f
  change K = causes U f at hK
  rw [hK, causes_eq_of_extends initial hf]

/-- Along a run of the fragment, the events of a prefix are events of the whole run. -/
theorem events_prefix (A : SubstitutionAction T S) (label : O → T) {C : Configuration T O}
    {u v : List (Firing T S O)} (run : Executable A label C (u ++ v))
    (fragment : Fragment C (u ++ v)) :
    events (configOf label u) ⊆ events (configOf label (u ++ v)) :=
  events_mono (prefix_extends A label run fragment)

#print axioms causes_eq_of_extends
#print axioms events_mono
#print axioms events_prefix
#print axioms precedes_append_left_mem
#print axioms precedes_append_iff_left
#print axioms precedes_append_iff_right
#print axioms prefix_extends
#print axioms executable_append
#print axioms presentAfter_shift
#print axioms regionOf_presentAfter_union_outside
#print axioms residual_isConfiguration
#print axioms extends_prefix
#print axioms prefix_iff_extends

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunEvents
