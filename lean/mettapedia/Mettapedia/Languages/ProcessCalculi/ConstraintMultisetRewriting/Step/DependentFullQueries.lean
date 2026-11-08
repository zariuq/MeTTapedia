import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentFullIndependence

/-!
# Predicate queries natural in the frame, and firings carried along morphisms of frames

A predicate query of the dependent full step (`Query`) has a region at each solution of its own
frame. Such a region cannot be read at another frame: nothing carries a row of a later frame back.
**A natural query** (`NaturalQuery`) has patterns at its frame and one test for every frame; its
region at a solution `τ` is the test on the patterns and the row, both read along `τ`
(`NaturalQuery.region`). Its region reads through solutions, so it is a predicate query of the step
(`NaturalQuery.toQuery`).

**Natural queries move along substitutions** (`NaturalQuery.move`): the patterns are read along the
substitution, the test and the answer stay. Moving is functorial (`move_id`, `move_comp`), and a
moved query at a solution is the query at the composite (`region_move`, `holds_move`). Absence and
counting of a pattern are natural (`absent`, `count`), with the regions and answers of R91's
`Query.absent` and `Query.count` (`absent_holds_iff`, `count_holds_iff`).

**Firings carried along a morphism of frames** (`Natural`, `Natural.move`, `Local.move`). A firing
without helpers whose queries are natural moves along `σ : Δ' ⟶ Δ`: its patterns, made rows, tells
and guards are read along `σ`, its queries are moved, and its selection is unchanged.
* Its information is the old information read along `σ` (`information_move`).
* Its guards and queries at a solution are the old ones at the composite (`holds_move`).
* It is admitted wherever the old firing is admitted and the moved information is still solvable
  (`admits_move`); along an isomorphism of telescopes admission is preserved and reflected
  (`admits_move_iff`).
* Its result is the old result carried along `σ` (`after_move`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
namespace DependentFull

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head} {levels : LevelModel rules L}
  {O : Type}

/-! ## The action of the frames -/

theorem act_act {Δ Δ' Θ : Context rules} (σ : Δ' ⟶ Δ) (τ : Θ ⟶ Δ') (t : TotalTerm Δ) :
    (frames levels).act τ ((frames levels).act σ t) = (frames levels).act (τ ≫ σ) t :=
  (ContextualDependentEta.reindex_comp t τ σ).symm

theorem act_one' {Δ : Context rules} (t : TotalTerm Δ) : (frames levels).act (𝟙 Δ) t = t :=
  (frames levels).act_id t

theorem applyStore_applyStore {Δ Δ' Θ : Context rules} (σ : Δ' ⟶ Δ) (τ : Θ ⟶ Δ')
    (K : EquationStore (TotalTerm Δ)) :
    (frames levels).applyStore τ ((frames levels).applyStore σ K) = (frames levels).applyStore (τ ≫ σ) K := by
  unfold Frames.applyStore
  rw [List.map_map]
  refine List.map_congr_left fun e _ => ?_
  show ((frames levels).act τ ((frames levels).act σ e.1), (frames levels).act τ ((frames levels).act σ e.2)) = _
  rw [act_act, act_act]

/-- Two queries with the same region at a solution and the same answers hold together. -/
theorem Query.holds_congr {Δ : Context rules} {q q' : Query levels O Δ} {present : Finset O}
    {row : O → TotalTerm Δ} {Θ : Context rules} {τ : Θ ⟶ Δ}
    (regions : ∀ t, q.region τ t ↔ q'.region τ t) (answers : ∀ seen, q.answer seen ↔ q'.answer seen) :
    q.Holds present row τ ↔ q'.Holds present row τ := by
  constructor
  · rintro ⟨seen, members, answer⟩
    exact ⟨seen, fun o => (members o).trans (and_congr Iff.rfl (regions _)), (answers seen).mp answer⟩
  · rintro ⟨seen, members, answer⟩
    exact ⟨seen, fun o => (members o).trans (and_congr Iff.rfl (regions _).symm), (answers seen).mpr answer⟩

/-! ## Natural queries -/

variable (levels O) in
/-- **A predicate query natural in the frame**: patterns at its frame, a test at every frame that
reads through the frame equivalence, and an answer on the region of present rows. -/
structure NaturalQuery (Δ : Context rules) where
  patterns : List (TotalTerm Δ)
  test : ∀ {Θ : Context rules}, List (TotalTerm Θ) → TotalTerm Θ → Prop
  reads : ∀ {Θ : Context rules} (ps : List (TotalTerm Θ)) {s t : TotalTerm Θ},
    (frames levels).E s t → (test ps s ↔ test ps t)
  answer : Finset O → Prop

namespace NaturalQuery

variable {Δ Δ' : Context rules}

/-- Its region at a solution: the test on the patterns and the row, both read along the solution. -/
def region (q : NaturalQuery levels O Δ) {Θ : Context rules} (τ : Θ ⟶ Δ) (t : TotalTerm Δ) : Prop :=
  q.test (q.patterns.map ((frames levels).act τ)) ((frames levels).act τ t)

/-- **A natural query is a predicate query of the step.** -/
def toQuery (q : NaturalQuery levels O Δ) : Query levels O Δ where
  region τ t := q.region τ t
  reads := fun {_} _ {_ _} same => q.reads _ same
  answer := q.answer

/-- **Moving a natural query along a substitution**: the patterns are read along it. -/
def move (σ : Δ' ⟶ Δ) (q : NaturalQuery levels O Δ) : NaturalQuery levels O Δ' :=
  ⟨q.patterns.map ((frames levels).act σ), q.test, q.reads, q.answer⟩

theorem move_id (q : NaturalQuery levels O Δ) : q.move (𝟙 Δ) = q := by
  obtain ⟨patterns, test, reads, answer⟩ := q
  show (⟨patterns.map ((frames levels).act (𝟙 Δ)), test, reads, answer⟩ : NaturalQuery levels O Δ) = _
  rw [show (frames levels).act (𝟙 Δ) = id from funext act_one', List.map_id]

theorem move_comp {Θ : Context rules} (σ : Δ' ⟶ Δ) (ρ : Θ ⟶ Δ') (q : NaturalQuery levels O Δ) :
    (q.move σ).move ρ = q.move (ρ ≫ σ) := by
  show (⟨(q.patterns.map ((frames levels).act σ)).map ((frames levels).act ρ), q.test, q.reads, q.answer⟩ :
    NaturalQuery levels O Θ) = ⟨q.patterns.map ((frames levels).act (ρ ≫ σ)), q.test, q.reads, q.answer⟩
  rw [List.map_map, show (frames levels).act ρ ∘ (frames levels).act σ = (frames levels).act (ρ ≫ σ) from
    funext (act_act σ ρ)]

/-- **A moved query, at a solution, is the query at the composite.** -/
theorem region_move (σ : Δ' ⟶ Δ) (q : NaturalQuery levels O Δ) {Θ : Context rules} (τ : Θ ⟶ Δ')
    (t : TotalTerm Δ) :
    (q.move σ).region τ ((frames levels).act σ t) ↔ q.region (τ ≫ σ) t := by
  show q.test ((q.patterns.map ((frames levels).act σ)).map ((frames levels).act τ))
      ((frames levels).act τ ((frames levels).act σ t)) ↔
    q.test (q.patterns.map ((frames levels).act (τ ≫ σ))) ((frames levels).act (τ ≫ σ) t)
  rw [List.map_map, show (frames levels).act τ ∘ (frames levels).act σ = (frames levels).act (τ ≫ σ) from
    funext (act_act σ τ), act_act]

/-- **A moved query holds at a solution exactly when the query holds at the composite**, on the rows
read along the substitution. -/
theorem holds_move (σ : Δ' ⟶ Δ) (q : NaturalQuery levels O Δ) (present : Finset O)
    (row : O → TotalTerm Δ) {Θ : Context rules} (τ : Θ ⟶ Δ') :
    (q.move σ).toQuery.Holds present (fun o => (frames levels).act σ (row o)) τ ↔
      q.toQuery.Holds present row (τ ≫ σ) := by
  constructor
  · rintro ⟨seen, members, answer⟩
    exact ⟨seen, fun o => (members o).trans (and_congr Iff.rfl (region_move σ q τ (row o))), answer⟩
  · rintro ⟨seen, members, answer⟩
    exact ⟨seen, fun o => (members o).trans (and_congr Iff.rfl (region_move σ q τ (row o)).symm), answer⟩

/-! ### Absence and counting are natural -/

variable (levels) in
/-- A row matches one of the patterns. -/
def matchesAny {Θ : Context rules} (ps : List (TotalTerm Θ)) (t : TotalTerm Θ) : Prop :=
  ∃ p ∈ ps, (frames levels).E p t

theorem matchesAny_reads {Θ : Context rules} (ps : List (TotalTerm Θ)) {s t : TotalTerm Θ}
    (same : (frames levels).E s t) : matchesAny levels ps s ↔ matchesAny levels ps t :=
  ⟨fun ⟨p, member, matched⟩ => ⟨p, member, ((frames levels).equivalence Θ).trans matched same⟩,
    fun ⟨p, member, matched⟩ =>
      ⟨p, member, ((frames levels).equivalence Θ).trans matched (((frames levels).equivalence Θ).symm same)⟩⟩

variable (levels O) in
/-- **The natural absence query of a pattern.** -/
def absent (pattern : TotalTerm Δ) : NaturalQuery levels O Δ :=
  ⟨[pattern], matchesAny levels, matchesAny_reads, fun seen => seen = ∅⟩

variable (levels O) in
/-- **The natural counting query of a pattern.** -/
def count (pattern : TotalTerm Δ) (number : Nat) : NaturalQuery levels O Δ :=
  ⟨[pattern], matchesAny levels, matchesAny_reads, fun seen => seen.card = number⟩

theorem matchesAny_singleton {Θ : Context rules} (p t : TotalTerm Θ) :
    matchesAny levels [p] t ↔ (frames levels).E p t :=
  ⟨fun ⟨p', member, matched⟩ => by
    obtain rfl := List.mem_singleton.mp member
    exact matched, fun matched => ⟨p, List.mem_singleton_self p, matched⟩⟩

/-- **The natural absence query is R91's absence query.** -/
theorem absent_holds_iff (pattern : TotalTerm Δ) (present : Finset O) (row : O → TotalTerm Δ)
    {Θ : Context rules} (τ : Θ ⟶ Δ) :
    (absent levels O pattern).toQuery.Holds present row τ ↔
      (Query.absent levels O pattern).Holds present row τ :=
  Query.holds_congr (fun _ => matchesAny_singleton _ _) fun _ => Iff.rfl

/-- **The natural counting query is R91's counting query.** -/
theorem count_holds_iff (pattern : TotalTerm Δ) (number : Nat) (present : Finset O)
    (row : O → TotalTerm Δ) {Θ : Context rules} (τ : Θ ⟶ Δ) :
    (count levels O pattern number).toQuery.Holds present row τ ↔
      (Query.count levels O pattern number).Holds present row τ :=
  Query.holds_congr (fun _ => matchesAny_singleton _ _) fun _ => Iff.rfl

/-- Moving the absence query of a pattern is the absence query of the moved pattern. -/
theorem move_absent (σ : Δ' ⟶ Δ) (pattern : TotalTerm Δ) :
    (absent levels O pattern).move σ = absent levels O ((frames levels).act σ pattern) := rfl

theorem move_count (σ : Δ' ⟶ Δ) (pattern : TotalTerm Δ) (number : Nat) :
    (count levels O pattern number).move σ = count levels O ((frames levels).act σ pattern) number := rfl

end NaturalQuery

/-! ## Made rows along a substitution -/

namespace Make

variable {Δ Δ' : Context rules}

/-- A made row read along a substitution. -/
def reindex (m : Make Δ) (σ : Δ' ⟶ Δ) : Make Δ' := ⟨m.type.reindex σ, subst σ.substitution m.code⟩

theorem WellTyped.reindex {m : Make Δ} (typed : m.WellTyped) (σ : Δ' ⟶ Δ) : (m.reindex σ).WellTyped :=
  typed.substitute σ.typed

/-- **The checked row of a reindexed made row is the old row read along the substitution.** -/
theorem row_reindex (m : Make Δ) (typed : m.WellTyped) (σ : Δ' ⟶ Δ) :
    (m.reindex σ).row (typed.reindex σ) = (frames levels).act σ (m.row typed) := rfl

end Make

/-! ## Firings with natural queries, carried along morphisms of frames -/

variable (levels O) in
/-- **A firing without helpers whose predicate queries are natural.** -/
structure Natural (Δ : Context rules) where
  taken : List O
  read : List O
  takes : List (TotalTerm Δ)
  reads : List (TotalTerm Δ)
  makes : List (O × Make Δ)
  tells : EquationStore (TotalTerm Δ)
  guards : EquationStore (TotalTerm Δ)
  queries : List (NaturalQuery levels O Δ)

namespace Natural

variable {Δ Δ' : Context rules}

/-- The firing of the step it is. -/
def toPlain (f : Natural levels O Δ) : Plain levels O Δ :=
  ⟨f.taken, f.read, f.takes, f.reads, f.makes, f.tells, f.guards, f.queries.map NaturalQuery.toQuery⟩

/-- **The firing carried along a substitution.** -/
def move (σ : Δ' ⟶ Δ) (f : Natural levels O Δ) : Natural levels O Δ' :=
  ⟨f.taken, f.read, f.takes.map ((frames levels).act σ), f.reads.map ((frames levels).act σ),
    f.makes.map fun m => (m.1, m.2.reindex σ), (frames levels).applyStore σ f.tells,
    (frames levels).applyStore σ f.guards, f.queries.map (NaturalQuery.move σ)⟩

end Natural

theorem Local.mk_congr {Δ : Context rules} {K K' : EquationStore (TotalTerm Δ)} {P P' : Finset O}
    {label label' : O → TotalTerm Δ} (knowledge : K = K') (present : P = P') (labels : label = label') :
    (⟨K, P, label⟩ : Local rules O Δ) = ⟨K', P', label'⟩ := by
  subst knowledge
  subst present
  subst labels
  rfl

/-- **A state carried along a substitution**: its knowledge and labels read along it. -/
def Local.move {Δ Δ' : Context rules} (σ : Δ' ⟶ Δ) (c : Local rules O Δ) : Local rules O Δ' :=
  ⟨c.knowledge.map fun e => (e.1.reindex σ, e.2.reindex σ), c.present, fun o => (c.label o).reindex σ⟩

theorem pairs_move {Δ Δ' : Context rules} (σ : Δ' ⟶ Δ) (label : O → TotalTerm Δ) :
    ∀ (patterns : List (TotalTerm Δ)) (selected : List O),
      pairs (fun o => (frames levels).act σ (label o)) (patterns.map ((frames levels).act σ)) selected =
        (frames levels).applyStore σ (pairs label patterns selected)
  | [], _ => rfl
  | _ :: _, [] => rfl
  | _ :: patterns, _ :: selected => congrArg (List.cons _) (pairs_move σ label patterns selected)

/-- **Relabelling commutes with reading along a substitution.** -/
theorem relabel_move [DecidableEq O] {Δ Δ' : Context rules} (σ : Δ' ⟶ Δ) (row : O → TotalTerm Δ) :
    ∀ (makes : List (O × Make Δ)) (typed : ∀ m ∈ makes, m.2.WellTyped)
      (typed' : ∀ m ∈ makes.map (fun m => (m.1, m.2.reindex σ)), m.2.WellTyped),
      relabel (fun o => (frames levels).act σ (row o)) (makes.map fun m => (m.1, m.2.reindex σ)) typed' =
        fun o => (frames levels).act σ (relabel row makes typed o)
  | [], _, _ => rfl
  | m :: rest, typed, typed' => by
      funext o
      by_cases same : o = m.1
      · simp only [List.map_cons, relabel, if_pos same]
        rfl
      · simp only [List.map_cons, relabel, if_neg same]
        exact congrFun (relabel_move σ row rest _ _) o

namespace Natural

variable {Δ Δ' : Context rules} (σ : Δ' ⟶ Δ) (f : Natural levels O Δ)

theorem made_move : (f.move σ).toPlain.made = f.toPlain.made := by
  show (f.makes.map fun m => (m.1, m.2.reindex σ)).map Prod.fst = f.makes.map Prod.fst
  rw [List.map_map]
  rfl

theorem selection_move : (f.move σ).toPlain.selection = f.toPlain.selection := by
  show (⟨f.taken, f.read, (f.move σ).toPlain.made⟩ : Selection O) = ⟨f.taken, f.read, f.toPlain.made⟩
  rw [made_move]

theorem own_move (label : O → TotalTerm Δ) :
    (f.move σ).toPlain.own (fun o => (frames levels).act σ (label o)) =
      (frames levels).applyStore σ (f.toPlain.own label) := by
  show pairs _ (f.takes.map ((frames levels).act σ)) f.taken ++ pairs _ (f.reads.map ((frames levels).act σ)) f.read ++
      (frames levels).applyStore σ f.tells = _
  rw [pairs_move, pairs_move]
  unfold Plain.own Frames.applyStore
  rw [List.map_append, List.map_append]
  rfl

/-- **The information of a moved firing is the old information read along the substitution.** -/
theorem information_move (c : Local rules O Δ) :
    (f.move σ).toPlain.information (c.move σ) = (frames levels).applyStore σ (f.toPlain.information c) := by
  show (frames levels).applyStore σ c.knowledge ++
      (f.move σ).toPlain.own (fun o => (frames levels).act σ (c.label o)) = _
  rw [own_move]
  unfold Plain.information Frames.applyStore
  rw [List.map_append]

/-- **Guards and queries of a moved firing at a solution are the old ones at the composite.** -/
theorem holds_move (c : Local rules O Δ) {Θ : Context rules} (τ : Θ ⟶ Δ') :
    (f.move σ).toPlain.Holds (c.move σ) τ ↔ f.toPlain.Holds c (τ ≫ σ) := by
  unfold Plain.Holds
  refine and_congr (Frames.models_applyStore (X := frames levels) σ τ f.guards) ?_
  show (∀ q ∈ (f.queries.map (NaturalQuery.move σ)).map NaturalQuery.toQuery,
      q.Holds c.present (fun o => (frames levels).act σ (c.label o)) τ) ↔
    ∀ q ∈ f.queries.map NaturalQuery.toQuery, q.Holds c.present c.label (τ ≫ σ)
  simp only [List.map_map, List.forall_mem_map, Function.comp]
  exact forall₂_congr fun q _ => NaturalQuery.holds_move σ q c.present c.label τ

theorem shapes_move (shapes : f.toPlain.Shapes) : (f.move σ).toPlain.Shapes := by
  obtain ⟨taken, made, takes, reads, typed⟩ := shapes
  refine ⟨taken, (made_move σ f).symm ▸ made, (List.length_map _).trans takes,
    (List.length_map _).trans reads, fun m member => ?_⟩
  obtain ⟨m', member', rfl⟩ := List.mem_map.mp member
  exact (typed m' member').reindex σ

variable [DecidableEq O]

/-- **A moved firing is admitted** wherever the old firing is admitted and the moved information is
still solvable. -/
theorem admits_move {c : Local rules O Δ} (admitted : f.toPlain.Admits c)
    (solvable : (frames levels).Solvable ((frames levels).applyStore σ (f.toPlain.information c))) :
    (f.move σ).toPlain.Admits (c.move σ) := by
  obtain ⟨shapes, enabled, -, asked⟩ := admitted
  refine ⟨shapes_move σ f shapes, ?_, by rw [information_move]; exact solvable, ?_⟩
  · show Enabled _ c.present ((f.move σ).toPlain.selection.commit (T := Unit))
    rw [selection_move]
    exact enabled
  · rw [information_move]
    intro b τ solved
    exact (holds_move σ f c τ).mpr (asked b _ ((Frames.models_applyStore (X := frames levels) σ τ _).mp solved))

/-- **Along an isomorphism of telescopes, admission is preserved and reflected.** -/
theorem admits_move_iff (e : Δ' ≅ Δ) (c : Local rules O Δ) :
    (f.move e.hom).toPlain.Admits (c.move e.hom) ↔ f.toPlain.Admits c := by
  constructor
  · rintro ⟨shapes, enabled, solvable, asked⟩
    refine ⟨⟨shapes.1, (made_move e.hom f) ▸ shapes.2.1, (List.length_map _).symm.trans shapes.2.2.1,
      (List.length_map _).symm.trans shapes.2.2.2.1, fun m member => ?_⟩, ?_, ?_, ?_⟩
    · have typed := shapes.2.2.2.2 (m.1, m.2.reindex e.hom) (List.mem_map.mpr ⟨m, member, rfl⟩)
      have back := typed.reindex e.inv
      have same : (m.2.reindex e.hom).reindex e.inv = m.2 := by
        show (⟨(m.2.type.reindex e.hom).reindex e.inv, subst e.inv.substitution (subst e.hom.substitution m.2.code)⟩ :
          Make Δ) = m.2
        rw [← TypeOver.reindex_comp, e.inv_hom_id, TypeOver.reindex_id]
        rw [show subst e.inv.substitution (subst e.hom.substitution m.2.code) =
            subst (e.inv ≫ e.hom).substitution m.2.code from subst_subComp _ _ _, e.inv_hom_id]
        exact congrArg (Make.mk m.2.type) (subst_ids m.2.code)
      rw [same] at back
      exact back
    · rw [selection_move] at enabled
      exact enabled
    · rw [information_move] at solvable
      exact Frames.solvable_of_applyStore (X := frames levels) e.hom solvable
    · rw [information_move] at asked
      intro b τ solved
      have moved : (frames levels).Models (τ ≫ e.inv) ((frames levels).applyStore e.hom (f.toPlain.information c)) := by
        refine (Frames.models_applyStore (X := frames levels) e.hom (τ ≫ e.inv) _).mpr ?_
        show (frames levels).Models ((τ ≫ e.inv) ≫ e.hom) _
        rw [Category.assoc, e.inv_hom_id, Category.comp_id]
        exact solved
      have holds := (holds_move e.hom f c (τ ≫ e.inv)).mp (asked b _ moved)
      rw [Category.assoc, e.inv_hom_id, Category.comp_id] at holds
      exact holds
  · intro admitted
    refine admits_move e.hom f admitted ?_
    obtain ⟨b, τ, solved⟩ := admitted.2.2.1
    refine ⟨b, τ ≫ e.inv, (Frames.models_applyStore (X := frames levels) e.hom (τ ≫ e.inv) _).mpr ?_⟩
    show (frames levels).Models ((τ ≫ e.inv) ≫ e.hom) _
    rw [Category.assoc, e.inv_hom_id, Category.comp_id]
    exact solved

/-- **The result of a moved firing is the old result carried along the substitution.** -/
theorem after_move (c : Local rules O Δ) (typed : ∀ m ∈ f.makes, m.2.WellTyped)
    (typed' : ∀ m ∈ (f.move σ).makes, m.2.WellTyped) :
    (f.move σ).toPlain.after (c.move σ) typed' = (f.toPlain.after c typed).move σ := by
  have labels : relabel (fun o => (frames levels).act σ (c.label o)) (f.move σ).makes typed' =
      fun o => (frames levels).act σ (relabel c.label f.makes typed o) :=
    relabel_move σ c.label f.makes typed typed'
  exact Local.mk_congr (information_move σ f c)
    (congrArg (fun s : Selection O => fire c.present (s.commit (T := Unit))) (selection_move σ f)) labels

end Natural

end DependentFull

#print axioms DependentFull.act_act
#print axioms DependentFull.Query.holds_congr
#print axioms DependentFull.NaturalQuery.move_id
#print axioms DependentFull.NaturalQuery.move_comp
#print axioms DependentFull.NaturalQuery.region_move
#print axioms DependentFull.NaturalQuery.holds_move
#print axioms DependentFull.NaturalQuery.absent_holds_iff
#print axioms DependentFull.NaturalQuery.count_holds_iff
#print axioms DependentFull.Make.row_reindex
#print axioms DependentFull.Natural.information_move
#print axioms DependentFull.Natural.holds_move
#print axioms DependentFull.Natural.admits_move
#print axioms DependentFull.Natural.admits_move_iff
#print axioms DependentFull.Natural.after_move

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
