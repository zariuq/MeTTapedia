import Mettapedia.GSLT.Causality.HistoryCover
import Mettapedia.GSLT.Causality.EventConcurrency
import Mathlib.Algebra.FreeMonoid.Basic

/-!
# The history construction

A theory that keeps its past records, with every configuration, the word of
events that led to it, and each step appends its own event. This module makes
that precise and proves what it buys.

* **Events that respect the equations.** A history theory needs events that do
  not change when a configuration is replaced by an equal one. Every GSLT has
  such events: a step between two equation classes. With them every GSLT has a
  history theory, whose configurations are a term and a word in the free
  monoid of events.
* **One parent.** When an event names the class it starts from, a
  configuration of the history theory has at most one parent: its word ends
  with the event of the last step, and the word before is the rest. The base
  theory may have several parents for one term; recording the event removes
  the choice.
* **The universal cover.** For a presentation with occurrences, the histories
  out of a root are the paths out of it. They form a tree over the reduction
  graph: the same history state is never reached twice, each occurrence out of
  a term lifts to exactly one extension, and every rooted cover of the
  occurrence graph receives exactly one map from the tree.
* **Erasures.** An erasure identifies histories with the same endpoints,
  compatibly with concatenation. Erasures form a complete lattice from the
  tree (nothing identified) to the base (all histories with the same endpoints
  identified), and the order-forgetting erasure of commuting steps lies
  strictly between them in examples.
* **What may be forgotten for free.** A part of the history can be erased
  without loss exactly when it is a function of the endpoint. A valuation
  descends through an erasure exactly when the erasure lies below the
  valuation's own erasure.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.HistoryMonad

open Mettapedia.GSLT
open Mettapedia.GSLT.Core.InteractionEvent
open Mettapedia.GSLT.Causality.OccurrenceHistory

universe uTerm v uSite uEvent uPoint uTile

/-! ## 1. Events that respect the equations, and the history theory -/

section EventHistory

variable {S : GSLT.{uTerm}} {E : Type uTerm}

/-- A labelling of the steps of a theory by events, unchanged when a
configuration is replaced by an equal one. -/
structure EventLabels (S : GSLT.{uTerm}) (E : Type uTerm) where
  labelled : S.Term → S.Term → E → Prop
  sound : ∀ {source target : S.Term} {event : E}, labelled source target event →
    S.Step source target
  resp_left : ∀ {source source' target : S.Term} {event : E},
    S.Equiv source source' → labelled source target event →
      ∃ target', labelled source' target' event ∧ S.Equiv target target'
  resp_right : ∀ {source target target' : S.Term} {event : E},
    labelled source target event → S.Equiv target target' →
      labelled source target' event

namespace EventLabels

/-- Each labelled step grades by the one-letter word of its event. -/
def grading (labels : EventLabels S E) : S.StepSpend (FreeMonoid E) where
  graded source target word := ∃ event, labels.labelled source target event ∧
    word = FreeMonoid.of event
  sound := by
    rintro source target word ⟨event, labelled, -⟩
    exact labels.sound labelled
  resp_left := by
    rintro source source' target word equal ⟨event, labelled, rfl⟩
    obtain ⟨target', labelled', equal'⟩ := labels.resp_left equal labelled
    exact ⟨target', ⟨event, labelled', rfl⟩, equal'⟩
  resp_right := by
    rintro source target target' word ⟨event, labelled, rfl⟩ equal
    exact ⟨event, labels.resp_right labelled equal, rfl⟩

/-- Every step carries an event. -/
def Total (labels : EventLabels S E) : Prop :=
  ∀ {source target : S.Term}, S.Step source target → ∃ event, labels.labelled source target event

theorem grading_total {labels : EventLabels S E} (total : labels.Total) :
    labels.grading.Total := by
  intro source target step
  obtain ⟨event, labelled⟩ := total step
  exact ⟨FreeMonoid.of event, event, labelled, rfl⟩

/-- An event names the class it starts from: two steps with one event start
from equal configurations. -/
def NamesSource (labels : EventLabels S E) : Prop :=
  ∀ {source source' target target' : S.Term} {event : E},
    labels.labelled source target event → labels.labelled source' target' event →
      S.Equiv source source'

end EventLabels

/-- **The history theory.** A configuration is a term with the word of events
that led to it, and each step appends its own event. -/
def history (labels : EventLabels S E) : GSLT :=
  S.spendLift labels.grading

theorem history_step_iff (labels : EventLabels S E) {x y : S.Term × FreeMonoid E} :
    (history labels).Step x y ↔
      ∃ event, labels.labelled x.1 y.1 event ∧ y.2 = x.2 * FreeMonoid.of event := by
  constructor
  · rintro ⟨word, ⟨event, labelled, rfl⟩, appended⟩
    exact ⟨event, labelled, appended⟩
  · rintro ⟨event, labelled, appended⟩
    exact ⟨FreeMonoid.of event, ⟨event, labelled, rfl⟩, appended⟩

/-- Attach the empty history. -/
def historyUnit (labels : EventLabels S E) (total : labels.Total) :
    GSLT.Morphism S (history labels) :=
  WriterGSLT.embedMorphism labels.grading (EventLabels.grading_total total)

/-- Strip the history. -/
def historyStrip (labels : EventLabels S E) (total : labels.Total) :
    GSLT.Morphism (history labels) S :=
  WriterGSLT.eraseMorphism labels.grading (EventLabels.grading_total total)

/-- Stripping the empty history gives the configuration back. -/
theorem historyStrip_comp_unit (labels : EventLabels S E) (total : labels.Total) :
    GSLT.Morphism.comp (historyStrip labels total) (historyUnit labels total) =
      GSLT.Morphism.id S :=
  WriterGSLT.erase_comp_embed labels.grading (EventLabels.grading_total total)

variable (S) in
/-- **Every theory has events that respect its equations**: a step from one
equation class to another. -/
def classLabels :
    EventLabels S (Quotient S.equations × Quotient S.equations) where
  labelled source target event :=
    S.Step source target ∧ event = (Quotient.mk _ source, Quotient.mk _ target)
  sound := And.left
  resp_left := by
    rintro source source' target event equal ⟨step, rfl⟩
    obtain ⟨target', step', equal'⟩ := S.rewrites_resp_left equal step
    refine ⟨target', ⟨step', ?_⟩, equal'⟩
    rw [Quotient.sound (s := S.equations) equal, Quotient.sound (s := S.equations) equal']
  resp_right := by
    rintro source target target' event ⟨step, rfl⟩ equal
    exact ⟨S.rewrites_resp_right step equal, by rw [Quotient.sound (s := S.equations) equal]⟩

theorem classLabels_total : (classLabels S).Total :=
  fun step => ⟨_, step, rfl⟩

theorem classLabels_namesSource : (classLabels S).NamesSource := by
  rintro source source' target target' event ⟨-, rfl⟩ ⟨-, same⟩
  exact Quotient.exact (s := S.equations) (congrArg Prod.fst same)

/-- **Every configuration of a history theory has at most one parent**, when
events name their source: the word after a step ends with the step's event, and
the word before it is the rest. -/
theorem history_unique_parent (labels : EventLabels S E) (names : labels.NamesSource)
    {x x' y : S.Term × FreeMonoid E}
    (step : (history labels).Step x y) (step' : (history labels).Step x' y) :
    (history labels).Equiv x x' := by
  obtain ⟨event, labelled, appended⟩ := (history_step_iff labels).mp step
  obtain ⟨event', labelled', appended'⟩ := (history_step_iff labels).mp step'
  have words : FreeMonoid.toList x.2 ++ [event] = FreeMonoid.toList x'.2 ++ [event'] := by
    have same := congrArg FreeMonoid.toList (appended.symm.trans appended')
    simpa using same
  obtain ⟨before, last⟩ := List.append_inj' words rfl
  have events : event = event' := List.singleton_inj.mp last
  subst events
  exact ⟨names labelled labelled', FreeMonoid.toList.injective before⟩

/-- Every theory has a history theory in which every configuration has at most
one parent. -/
theorem classHistory_unique_parent {x x' y : S.Term × FreeMonoid
      (Quotient S.equations × Quotient S.equations)}
    (step : (history (classLabels S)).Step x y) (step' : (history (classLabels S)).Step x' y) :
    (history (classLabels S)).Equiv x x' :=
  history_unique_parent (classLabels S) classLabels_namesSource step step'

end EventHistory

/-! ### Control: the base may have two parents where the history has one -/

namespace MergeControl

/-- Two terms that both step to a third. -/
def mergeTheory : GSLT where
  Term := Fin 3
  equations := ⟨Eq, eq_equivalence⟩
  rewrites source target := (source = 0 ∨ source = 1) ∧ target = 2
  rewrites_resp_left := by
    intro source source' target equal step
    exact ⟨target, equal ▸ step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    exact equal ▸ step

def first : mergeTheory.Term := (0 : Fin 3)
def second : mergeTheory.Term := (1 : Fin 3)
def meet : mergeTheory.Term := (2 : Fin 3)

theorem first_ne_second : ¬ mergeTheory.Equiv first second :=
  fun same => absurd (show (0 : Fin 3) = 1 from same) (by decide)

/-- In the base, the third term has two parents that are not equal. -/
theorem base_two_parents :
    mergeTheory.Step first meet ∧ mergeTheory.Step second meet ∧
      ¬ mergeTheory.Equiv first second :=
  ⟨⟨Or.inl rfl, rfl⟩, ⟨Or.inr rfl, rfl⟩, first_ne_second⟩

/-- In the history theory, the two steps into the third term end in different
configurations: their words differ. -/
theorem history_separates_parents :
    ∃ y y' : mergeTheory.Term × FreeMonoid
        (Quotient mergeTheory.equations × Quotient mergeTheory.equations),
      (history (classLabels mergeTheory)).Step (first, 1) y ∧
        (history (classLabels mergeTheory)).Step (second, 1) y' ∧
        y.1 = y'.1 ∧ ¬ (history (classLabels mergeTheory)).Equiv y y' := by
  refine ⟨(meet, FreeMonoid.of (Quotient.mk _ first, Quotient.mk _ meet)),
    (meet, FreeMonoid.of (Quotient.mk _ second, Quotient.mk _ meet)),
    (history_step_iff _).mpr ⟨_, ⟨⟨Or.inl rfl, rfl⟩, rfl⟩, by simp⟩,
    (history_step_iff _).mpr ⟨_, ⟨⟨Or.inr rfl, rfl⟩, rfl⟩, by simp⟩, rfl, ?_⟩
  rintro ⟨-, words⟩
  have events := FreeMonoid.of_injective words
  have firsts : mergeTheory.Equiv first second :=
    Quotient.exact (s := mergeTheory.equations) (congrArg Prod.fst events)
  exact first_ne_second firsts

end MergeControl


/-! ## 2. The tree of histories over a presentation -/

section Cover

variable {theory : GSLT.{uTerm}} {P : InteractionPresentation.{uSite, uEvent} theory}

/-- **The events of a history determine it.** Two paths from one term with the
same word of occurrences are the same history. -/
theorem element_eq_of_events : ∀ {s t t' : theory.Term} (p : OccurrencePath P s t)
    (q : OccurrencePath P s t'), Element.events p = Element.events q →
      (⟨t, p⟩ : Element P s) = ⟨t', q⟩
  | _, _, _, .refl _, .refl _, _ => rfl
  | _, _, _, .refl _, .cons _ _, same => by simp [Element.events] at same
  | _, _, _, .cons _ _, .refl _, same => by simp [Element.events] at same
  | _, _, _, .cons o rest, .cons o' rest', same => by
      simp only [Element.events, List.cons.injEq] at same
      obtain ⟨head, tail⟩ := same
      cases head
      cases element_eq_of_events rest rest' tail
      rfl

/-- The history state, a term with its word of occurrences, determines the
history. -/
theorem toWriter_injective {root : theory.Term} :
    Function.Injective (Element.toWriter (P := P) (root := root)) := by
  rintro ⟨t, p⟩ ⟨t', q⟩ same
  exact element_eq_of_events p q (congrArg Prod.snd same)

theorem events_extend {root t : theory.Term} (e : Element P root)
    (o : Occurrence P e.target t) :
    Element.events (e.extend o).path = Element.events e.path ++ [⟨e.target, t, o⟩] := by
  simp [Element.extend, Element.events_append, Element.events]

/-- **A history has one parent.** Two extensions are equal only when they
extend the same history by the same occurrence. -/
theorem extend_injective {root t t' : theory.Term} {e e' : Element P root}
    {o : Occurrence P e.target t} {o' : Occurrence P e'.target t'}
    (same : e.extend o = e'.extend o') :
    e = e' ∧ (⟨e.target, t, o⟩ : AnyOccurrence P) = ⟨e'.target, t', o'⟩ := by
  have words := congrArg (fun x : Element P root => Element.events x.path) same
  simp only [events_extend] at words
  obtain ⟨before, last⟩ := List.append_inj' words rfl
  exact ⟨element_eq_of_events e.path e'.path before, List.singleton_inj.mp last⟩

/-- Every history is the empty one or an extension of a shorter one. -/
theorem eq_origin_or_extend : ∀ {s t : theory.Term} (p : OccurrencePath P s t),
    (⟨t, p⟩ : Element P s) = originElement P s ∨
      ∃ (e : Element P s) (t' : theory.Term) (o : Occurrence P e.target t'),
        (⟨t, p⟩ : Element P s) = e.extend o ∧
          (Element.events e.path).length < (Element.events p).length
  | _, _, .refl _ => Or.inl rfl
  | _, _, .cons o rest => by
      right
      rcases eq_origin_or_extend rest with isOrigin | ⟨e, t', o', isExtension, shorter⟩
      · change (⟨_, rest⟩ : Element P _) = ⟨_, .refl _⟩ at isOrigin
        cases isOrigin
        exact ⟨originElement P _, _, o, rfl, by simp [Element.events, originElement]⟩
      · obtain ⟨target, path⟩ := e
        change (⟨_, rest⟩ : Element P _) =
          ⟨_, OccurrencePath.append path (.cons o' (.refl _))⟩ at isExtension
        cases isExtension
        refine ⟨⟨target, .cons o path⟩, _, o', rfl, ?_⟩
        simp only [Element.events, List.length_cons]
        exact Nat.succ_lt_succ shorter

/-- **A rooted cover of the occurrence graph**: points above terms, a base
point above the root, and a lift of every occurrence out of a point's term. -/
structure RootedCover (P : InteractionPresentation.{uSite, uEvent} theory)
    (root : theory.Term) where
  Point : Type uPoint
  proj : Point → theory.Term
  base : Point
  base_proj : proj base = root
  lift : ∀ (x : Point) {t : theory.Term}, Occurrence P (proj x) t → Point
  lift_proj : ∀ (x : Point) {t : theory.Term} (o : Occurrence P (proj x) t),
    proj (lift x o) = t

namespace RootedCover

variable {root : theory.Term} (C : RootedCover.{uTerm, uSite, uEvent, uPoint} P root)

/-- Lift a path from a point above its source. -/
def liftPath : ∀ {s t : theory.Term}, OccurrencePath P s t → (x : C.Point) →
    C.proj x = s → C.Point
  | _, _, .refl _, x, _ => x
  | _, _, .cons o rest, x, above => liftPath rest (C.lift x (above ▸ o)) (C.lift_proj x _)

theorem liftPath_proj : ∀ {s t : theory.Term} (p : OccurrencePath P s t) (x : C.Point)
    (above : C.proj x = s), C.proj (C.liftPath p x above) = t
  | _, _, .refl _, _, above => above
  | _, _, .cons _ rest, _, _ => liftPath_proj rest _ _

theorem liftPath_append : ∀ {s m t : theory.Term} (p : OccurrencePath P s m)
    (q : OccurrencePath P m t) (x : C.Point) (above : C.proj x = s),
    C.liftPath (OccurrencePath.append p q) x above =
      C.liftPath q (C.liftPath p x above) (C.liftPath_proj p x above)
  | _, _, _, .refl _, _, _, _ => rfl
  | _, _, _, .cons _ rest, q, _, _ => liftPath_append rest q _ _

theorem lift_congr {x y : C.Point} (same : x = y) {s t : theory.Term}
    (o : Occurrence P s t) (projX : C.proj x = s) (projY : C.proj y = s) :
    C.lift x (projX.symm ▸ o) = C.lift y (projY.symm ▸ o) := by
  subst same
  rfl

/-- The point a history reaches. -/
def ofElement (e : Element P root) : C.Point :=
  C.liftPath e.path C.base C.base_proj

theorem ofElement_proj (e : Element P root) : C.proj (C.ofElement e) = e.target :=
  C.liftPath_proj e.path C.base C.base_proj

theorem ofElement_origin : C.ofElement (originElement P root) = C.base :=
  rfl

theorem ofElement_extend (e : Element P root) {t : theory.Term}
    (o : Occurrence P e.target t) :
    C.ofElement (e.extend o) = C.lift (C.ofElement e) ((C.ofElement_proj e).symm ▸ o) := by
  unfold ofElement Element.extend
  rw [C.liftPath_append]
  rfl

/-- **The tree of histories maps to every rooted cover in exactly one way.**
The map sends the empty history to the base point and commutes with
extension; any map that does so is this one. -/
theorem ofElement_unique (f : Element P root → C.Point)
    (f_proj : ∀ e, C.proj (f e) = e.target)
    (f_origin : f (originElement P root) = C.base)
    (f_extend : ∀ (e : Element P root) {t : theory.Term} (o : Occurrence P e.target t),
      f (e.extend o) = C.lift (f e) ((f_proj e).symm ▸ o)) :
    ∀ e, f e = C.ofElement e := by
  suffices ∀ n (e : Element P root), (Element.events e.path).length = n → f e = C.ofElement e
    from fun e => this _ e rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n smaller =>
    rintro ⟨t, p⟩ rfl
    rcases eq_origin_or_extend p with isOrigin | ⟨e, t', o, isExtension, shorter⟩
    · rw [isOrigin, f_origin]
      exact C.ofElement_origin.symm
    · rw [isExtension, f_extend, C.ofElement_extend]
      exact C.lift_congr (smaller _ shorter e rfl) o (f_proj e) (C.ofElement_proj e)

end RootedCover

variable (P) in
/-- The tree of histories out of a root, as a rooted cover. -/
def historyCover (root : theory.Term) : RootedCover P root where
  Point := Element P root
  proj e := e.target
  base := originElement P root
  base_proj := rfl
  lift e _ o := e.extend o
  lift_proj _ _ _ := rfl

/-- **The tree of histories is the universal cover**: the map to any rooted
cover is the unique cover map, and the map to the tree itself is the
identity. -/
theorem historyCover_ofElement {root : theory.Term} (e : Element P root) :
    (historyCover P root).ofElement e = e :=
  ((historyCover P root).ofElement_unique id (fun _ => rfl) rfl (fun _ _ _ => rfl) e).symm

/-- **Forgetting the history is lossless exactly when the base is already a
tree**: the endpoint determines the history iff every term has at most one path
from the root. -/
theorem forget_injective_iff {root : theory.Term} :
    Function.Injective (fun e : Element P root => e.target) ↔
      ∀ t, Subsingleton (OccurrencePath P root t) := by
  constructor
  · intro injective t
    refine ⟨fun p q => ?_⟩
    have same := injective (a₁ := ⟨t, p⟩) (a₂ := ⟨t, q⟩) rfl
    cases same
    rfl
  · rintro unique ⟨t, p⟩ ⟨t', q⟩ (same : t = t')
    subst same
    rw [Subsingleton.elim p q]

end Cover

/-! ## 3. Erasures -/

section Erasures

variable {theory : GSLT.{uTerm}} {P : InteractionPresentation.{uSite, uEvent} theory}

variable (P) in
/-- **An erasure of history** identifies histories with the same endpoints,
compatibly with concatenation. -/
structure Erasure where
  rel : ∀ {s t : theory.Term}, OccurrencePath P s t → OccurrencePath P s t → Prop
  equivalence : ∀ {s t : theory.Term}, Equivalence (@rel s t)
  append : ∀ {s m t : theory.Term} {p p' : OccurrencePath P s m}
    {q q' : OccurrencePath P m t},
    rel p p' → rel q q' → rel (OccurrencePath.append p q) (OccurrencePath.append p' q')

namespace Erasure

theorem ext {first second : Erasure P}
    (same : ∀ {s t : theory.Term} (p q : OccurrencePath P s t),
      first.rel p q ↔ second.rel p q) : first = second := by
  obtain ⟨rel, equivalence, append⟩ := first
  obtain ⟨rel', equivalence', append'⟩ := second
  have relations : @rel = @rel' := by
    funext s t p q
    exact propext (same p q)
  subst relations
  rfl

/-- One erasure identifies at most what another identifies. -/
structure Below (first second : Erasure P) : Prop where
  apply : ∀ {s t : theory.Term} (p q : OccurrencePath P s t), first.rel p q → second.rel p q

instance : PartialOrder (Erasure P) where
  le := Below
  le_refl _ := ⟨fun _ _ related => related⟩
  le_trans _ _ _ firstSecond secondThird :=
    ⟨fun p q related => secondThird.apply p q (firstSecond.apply p q related)⟩
  le_antisymm _ _ firstSecond secondFirst :=
    ext fun p q => ⟨firstSecond.apply p q, secondFirst.apply p q⟩

theorem le_iff {first second : Erasure P} : first ≤ second ↔ Below first second :=
  Iff.rfl

instance : InfSet (Erasure P) where
  sInf erasures :=
    { rel := fun p q => ∀ erasure ∈ erasures, erasure.rel p q
      equivalence :=
        ⟨fun _ erasure _ => erasure.equivalence.refl _,
          fun related erasure member => erasure.equivalence.symm (related erasure member),
          fun first second erasure member =>
            erasure.equivalence.trans (first erasure member) (second erasure member)⟩
      append := fun first second erasure member =>
        erasure.append (first erasure member) (second erasure member) }

/-- Erasures form a complete lattice. -/
instance : CompleteLattice (Erasure P) :=
  completeLatticeOfInf (Erasure P) fun _ =>
    ⟨fun _ member => le_iff.mpr ⟨fun _ _ related => related _ member⟩,
      fun _ lower => le_iff.mpr ⟨fun p q related _ member =>
        (le_iff.mp (lower member)).apply p q related⟩⟩

variable (P) in
/-- The tree: nothing is identified. -/
def cover : Erasure P where
  rel p q := p = q
  equivalence := eq_equivalence
  append first second := by rw [first, second]

variable (P) in
/-- The base: all histories with the same endpoints are identified. -/
def base : Erasure P where
  rel _ _ := True
  equivalence := ⟨fun _ => trivial, fun _ => trivial, fun _ _ => trivial⟩
  append _ _ := trivial

theorem cover_eq_bot : cover P = ⊥ :=
  le_antisymm (le_iff.mpr ⟨fun p _ same => same ▸ (⊥ : Erasure P).equivalence.refl p⟩)
    bot_le

theorem base_eq_top : base P = ⊤ :=
  le_antisymm le_top (le_iff.mpr ⟨fun _ _ _ => trivial⟩)

/-- An erasure **folds** when it identifies two different histories. -/
def Folds (erasure : Erasure P) : Prop :=
  ∃ (s t : theory.Term) (p q : OccurrencePath P s t), erasure.rel p q ∧ p ≠ q

/-- An erasure folds exactly when it is not the tree. -/
theorem folds_iff_ne_bot (erasure : Erasure P) : erasure.Folds ↔ erasure ≠ ⊥ := by
  rw [← cover_eq_bot]
  constructor
  · rintro ⟨s, t, p, q, related, different⟩ same
    subst same
    exact different related
  · intro different
    by_contra none
    apply different
    refine le_antisymm (le_iff.mpr ⟨fun p q related => ?_⟩) (cover_eq_bot ▸ bot_le)
    by_contra unequal
    exact none ⟨_, _, p, q, related, unequal⟩

/-- **The order-forgetting erasure**: trace equivalence over a system of
tiles. -/
def trace (T : EventConcurrency.TileSystem.{uSite, uEvent, uTile} P) : Erasure P where
  rel p q := EventConcurrency.TraceEq T p q
  equivalence := EventConcurrency.TraceEq.is_equivalence T
  append first second :=
    .trans (.cong_right _ first) (.cong_left _ second)

/-- The erasure a valuation cannot see through: histories with the same value. -/
def kernel {A : Type*} [AddMonoid A] (v : OccurrenceValuation P A) : Erasure P where
  rel p q := v.onPath p = v.onPath q
  equivalence := ⟨fun _ => rfl, fun same => same.symm, fun first second => first.trans second⟩
  append first second := by
    rw [OccurrenceValuation.onPath_append, OccurrenceValuation.onPath_append, first, second]

/-- **A valuation survives an erasure exactly when the erasure lies below the
valuation's kernel.** The erasures a valuation survives are those below one
erasure. -/
theorem survives_iff_le_kernel {A : Type*} [AddMonoid A] (v : OccurrenceValuation P A)
    (erasure : Erasure P) :
    (∀ {s t : theory.Term} (p q : OccurrencePath P s t), erasure.rel p q →
      v.onPath p = v.onPath q) ↔ erasure ≤ kernel v :=
  ⟨fun survives => le_iff.mpr ⟨fun p q related => survives p q related⟩,
    fun below _ _ p q related => (le_iff.mp below).apply p q related⟩

/-- A valuation descends to traces exactly when the trace erasure lies below
its kernel. -/
theorem descends_iff_trace_le_kernel
    (T : EventConcurrency.TileSystem.{uSite, uEvent, uTile} P) {A : Type*} [AddMonoid A]
    (v : OccurrenceValuation P A) :
    EventConcurrency.Descends T v ↔ trace T ≤ kernel v := by
  constructor
  · intro descends
    exact le_iff.mpr ⟨fun p q related => descends p q related⟩
  · intro below s t p q related
    exact (le_iff.mp below).apply p q related

end Erasure

end Erasures


/-! ### Controls: the order-forgetting erasure lies strictly between -/

namespace ErasureControls

open EventConcurrency

/-- On the grid, forgetting the order of the two commuting flips folds the
tree: the two routes around the square are different and identified. -/
theorem grid_trace_folds : (Erasure.trace (siteTiles gridIndep)).Folds :=
  ⟨_, _, gridTile.path, gridTile.pathSwap', TraceEq.tile (T := siteTiles gridIndep) gridTile,
    fun same => grid_not_tile_invariant_sites (congrArg OccurrencePath.sites same)⟩

/-- One step from `false` to `true`. -/
def twinTheory : GSLT where
  Term := Bool
  equations := ⟨Eq, eq_equivalence⟩
  rewrites source target := source = false ∧ target = true
  rewrites_resp_left := by
    intro source source' target equal step
    exact ⟨target, equal ▸ step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    exact equal ▸ step

/-- Two sites for the same step. -/
def twinPresentation : InteractionPresentation twinTheory where
  Site := Bool
  Event _ source target := PLift (source = false ∧ target = true)
  sound evidence := evidence.down

/-- No tiles at all. -/
def noTiles : TileSystem twinPresentation where
  Tile _ := Empty
  target tile := tile.elim
  route tile := tile.elim
  swapped tile := tile.elim

def fromFalse : twinTheory.Term := false
def toTrue : twinTheory.Term := true

/-- The step through one site. -/
def twinPath (site : Bool) : OccurrencePath twinPresentation fromFalse toTrue :=
  .cons ⟨site, ⟨⟨rfl, rfl⟩⟩⟩ (.refl toTrue)

theorem twinPaths_ne : twinPath false ≠ twinPath true := by
  intro same
  have sites := congrArg OccurrencePath.sites same
  simp only [twinPath, OccurrencePath.sites] at sites
  exact Bool.false_ne_true (List.cons.inj sites).1

/-- **The order-forgetting erasure is not the base**: with two sites for one
step and no tiles, the two histories have the same endpoints and are not
identified. -/
theorem trace_ne_base : Erasure.trace noTiles ≠ Erasure.base twinPresentation := by
  intro same
  have related : (Erasure.trace noTiles).rel (twinPath false) (twinPath true) := by
    rw [same]
    trivial
  exact twinPaths_ne (TraceEq.eq_of_no_tile noTiles (fun _ => True) (fun _ holds => holds)
    (fun _ tile => tile.elim) related trivial)

end ErasureControls

/-! ## 4. What may be forgotten for free -/

section Recoverable

variable {theory : GSLT.{uTerm}} {P : InteractionPresentation.{uSite, uEvent} theory}

/-- A reading of the histories out of a root is **recoverable from the state**
when it is a function of the endpoint. -/
def StateRecoverable {root : theory.Term} {X : Type*}
    (read : ∀ {t : theory.Term}, OccurrencePath P root t → X) : Prop :=
  ∃ fromState : theory.Term → X, ∀ {t : theory.Term} (p : OccurrencePath P root t),
    read p = fromState t

/-- **A reading may be erased without loss exactly when histories with the same
endpoint read the same**: then the endpoint recovers it. -/
theorem stateRecoverable_iff {root : theory.Term} {X : Type*} [Nonempty X]
    (read : ∀ {t : theory.Term}, OccurrencePath P root t → X) :
    StateRecoverable read ↔
      ∀ {t : theory.Term} (p q : OccurrencePath P root t), read p = read q := by
  classical
  constructor
  · rintro ⟨fromState, recovers⟩ t p q
    exact (recovers p).trans (recovers q).symm
  · intro constant
    refine ⟨fun t => if h : Nonempty (OccurrencePath P root t) then read (Classical.choice h)
      else Classical.ofNonempty, fun p => ?_⟩
    simp only [dif_pos (Nonempty.intro p)]
    exact constant p _

/-- A reading is recoverable from the state exactly when the base erasure lies
below its kernel. -/
theorem stateRecoverable_iff_base_le {root : theory.Term} {A : Type*} [AddMonoid A]
    [Nonempty A] (v : OccurrenceValuation P A) :
    StateRecoverable (fun {t} (p : OccurrencePath P root t) => v.onPath p) ↔
      ∀ {t : theory.Term} (p q : OccurrencePath P root t),
        (Erasure.base P).rel p q → (Erasure.kernel v).rel p q := by
  rw [stateRecoverable_iff]
  exact ⟨fun constant _ p q _ => constant p q, fun below _ p q => below p q trivial⟩

end Recoverable

end Mettapedia.GSLT.Causality.HistoryMonad
