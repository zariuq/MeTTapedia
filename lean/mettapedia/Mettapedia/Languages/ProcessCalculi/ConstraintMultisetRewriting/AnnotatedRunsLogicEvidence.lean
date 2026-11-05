import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsLogic
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsPeak
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsLedger
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunEvidenceControls
import Mathlib.CategoryTheory.Pi.Basic

/-!
# Proof-relevant predicates over runs: evidence, and its propositional truncation

The doctrine of histories asks of a history only whether it satisfies a predicate. Here a
predicate holds of a history by named evidence.

## The fibration of evidence

* **Fibres** (`EvFiber root x`): families of types of evidence over the histories ending at `x`,
  with fibrewise maps of evidence as arrows. **Reindexing** along a run `p` reads the evidence of
  `h ≫ p` as evidence for `h` (`reindexEv`); it is strictly functorial (`reindexEv_id`,
  `reindexEv_comp`).
* The **total category** is the contravariant Grothendieck construction (`EvTotal`), fibred over
  the base (`evProjection_fibered`).
* **Quantifiers with evidence** (`existsEv`, `forallEv`): an adjunction of evidence transformers,
  not of truth values (`existsEquiv`, `forallEquiv`).

## The doctrine of histories is the propositional truncation

* `trunc E` is the set of histories that have evidence. It commutes with reindexing on the nose
  (`trunc_reindex`), with existence (`trunc_existsEv`) and, using choice, with universality
  (`trunc_forallEv`).
* **Poset reflection**: `trunc E ≤ trunc F` exactly when there is a map of evidence `E ⟶ F`
  (`trunc_le_iff_nonempty_hom`); a set of histories, read as a family of propositions (`iota`),
  is recovered by truncation (`trunc_iota`), maps into it are unique (`iota_hom_subsingleton`),
  and `trunc E ≤ φ` exactly when there is a map `E ⟶ iota φ` (`trunc_le_iff`).
* **A morphism of fibrations** (`truncTotal`): truncation is a functor from the total category of
  evidence to the total category of the doctrine of histories, over the base
  (`truncTotal_projection`), sending the chosen cartesian lifts to the chosen cartesian lifts
  (`truncTotal_lift`, `truncTotal_lift_cartesian`), and every strongly cartesian arrow to a
  strongly cartesian arrow (`truncTotal_cartesian`).
* **The persistent level** (`restrict_range_eq_trunc`): a copresheaf of evidence over runs with its
  map to histories is a proof-relevant persistent predicate; its image, a persistent predicate of
  the run topos, is class by class the truncation of the fibres of the map.

## Readings, and where the other layers sit

A reading of evidence is a function out of it. A reading through the history cannot tell two
pieces of evidence for one history apart (`throughHistory_not_separates`). Every account of runs
is such a reading (`accountReading_not_separates`): annotations that are functors on the run
category live at the level of the doctrine of histories.

Three evidence families over runs of the candidate step:

* **Round schedules** (`schedules`): decompositions of the run into rounds, each a round where the
  earlier ones left the configuration. The boundary peak (`boundaryPeak`) reads them.
* **Ledgers** (`ledgers`): run-length ledgers expanding to the run's receipt annotation. Their
  number of records reads them.
* **Rich realizations** (`realizations`): environment-free rich runs of the evidence-rich history
  layer whose successful firings are the run. Their attempt charge reads them.

Separating examples, each two pieces of evidence for one history that truncation identifies:

* `ScheduleControls.schedules_separated_by_peak`: the producer and the consumer as one round, or
  as two rounds: boundary peak 0 and 1;
* `LedgerEvidenceControls.ledgers_separated_by_records`: one ledger record or two for one receipt;
* `RealizationControls.realizations_separated_by_charge`: the taker fired directly, or after a
  refused attempt: attempt charge 0 and 13.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Functor Opposite

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns

open Mettapedia.CategoryTheory.PredicateDoctrine
open Mettapedia.GSLT.Causality.OccurrenceHistory (OccurrencePath)

/-! ## The fibration of evidence over a category -/

section Evidence

universe w uB vB

variable {B : Type uB} [Category.{vB} B] (root : B)

/-- **Evidence over histories**: a type of evidence for each history ending at `x`. -/
abbrev EvFiber (x : B) := (root ⟶ x) → Type (max w vB)

/-- **Reindexing evidence along a run**: the evidence for `h ≫ p` is evidence for `h`. -/
def reindexEv {x y : B} (p : x ⟶ y) : EvFiber.{w} root y ⥤ EvFiber.{w} root x :=
  Pi.comap (fun _ : root ⟶ y => Type (max w vB)) fun h => h ≫ p

theorem reindexEv_id (x : B) : reindexEv.{w} root (𝟙 x) = 𝟭 (EvFiber.{w} root x) :=
  (congrArg (fun g : (root ⟶ x) → (root ⟶ x) =>
    (Pi.comap (fun _ : root ⟶ x => Type (max w vB)) g : EvFiber.{w} root x ⥤ EvFiber.{w} root x))
    (funext Category.comp_id)).trans rfl

theorem reindexEv_comp {x y z : B} (f : x ⟶ y) (g : y ⟶ z) :
    reindexEv.{w} root (f ≫ g) = reindexEv.{w} root g ⋙ reindexEv.{w} root f :=
  (congrArg (fun k : (root ⟶ x) → (root ⟶ z) =>
    (Pi.comap (fun _ : root ⟶ z => Type (max w vB)) k : EvFiber.{w} root z ⥤ EvFiber.{w} root x))
    (funext fun h => (Category.assoc h f g).symm)).trans rfl

/-- The strict indexed category of evidence. -/
def evidenceFunctor : Bᵒᵖ ⥤ Cat where
  obj x := Cat.of (EvFiber.{w} root x.unop)
  map f := (reindexEv.{w} root f.unop).toCatHom
  map_id x := by
    apply Cat.ext
    exact reindexEv_id.{w} root x.unop
  map_comp f g := by
    apply Cat.ext
    exact reindexEv_comp.{w} root g.unop f.unop

/-- **The total category of evidence**: the contravariant Grothendieck construction. -/
abbrev EvTotal := Pseudofunctor.CoGrothendieck (evidenceFunctor.{w} root).toPseudofunctor'

abbrev evProjection : EvTotal.{w} root ⥤ B :=
  Pseudofunctor.CoGrothendieck.forget (evidenceFunctor.{w} root).toPseudofunctor'

theorem evProjection_fibered : IsFibered (evProjection.{w} root) := inferInstance

/-- The chosen cartesian lift of evidence along a run. -/
abbrev evLift {x y : B} (E : EvFiber.{w} root y) (p : x ⟶ y) :
    Pseudofunctor.CoGrothendieck.domainCartesianLift
      (F := (evidenceFunctor.{w} root).toPseudofunctor') E p ⟶ (⟨y, E⟩ : EvTotal.{w} root) :=
  Pseudofunctor.CoGrothendieck.cartesianLift (F := (evidenceFunctor.{w} root).toPseudofunctor') E p

theorem evLift_cartesian {x y : B} (E : EvFiber.{w} root y) (p : x ⟶ y) :
    IsStronglyCartesian (evProjection.{w} root) p (evLift root E p) :=
  Pseudofunctor.CoGrothendieck.isStronglyCartesian_homCartesianLift
    (F := (evidenceFunctor.{w} root).toPseudofunctor') E p

variable {root}

/-- **The propositional truncation**: the histories that have evidence. -/
def trunc {x : B} (E : EvFiber.{w} root x) : Set (root ⟶ x) := {h | Nonempty (E h)}

/-- **A set of histories as a family of propositions.** -/
abbrev iota {x : B} (φ : Set (root ⟶ x)) : EvFiber.{w} root x := fun h => ULift (PLift (h ∈ φ))

theorem trunc_reindex {x y : B} (p : x ⟶ y) (F : EvFiber.{w} root y) :
    trunc ((reindexEv.{w} root p).obj F) = (historyDoctrine root).reindex p (trunc F) := rfl

theorem trunc_iota {x : B} (φ : Set (root ⟶ x)) : trunc (iota.{w} φ) = φ :=
  Set.ext fun _ => ⟨fun ⟨u⟩ => u.down.down, fun member => ⟨⟨⟨member⟩⟩⟩⟩

theorem iota_hom_subsingleton {x : B} (E : EvFiber.{w} root x) (φ : Set (root ⟶ x)) :
    Subsingleton (E ⟶ iota.{w} φ) :=
  ⟨fun _ _ => funext fun _ => ConcreteCategory.hom_ext _ _ fun _ => Subsingleton.elim _ _⟩

/-- **The truncation is the poset reflection**: one truncation lies below another exactly when
there is a map of evidence. -/
theorem trunc_le_iff_nonempty_hom {x : B} (E F : EvFiber.{w} root x) :
    trunc E ≤ trunc F ↔ Nonempty (E ⟶ F) := by
  constructor
  · intro below
    exact ⟨fun h => TypeCat.ofHom fun e => Classical.choice (below ⟨e⟩)⟩
  · rintro ⟨α⟩ h ⟨e⟩
    exact ⟨α h e⟩

/-- **The reflection**: truncation lies below a set exactly when the evidence maps into it. -/
theorem trunc_le_iff {x : B} (E : EvFiber.{w} root x) (φ : Set (root ⟶ x)) :
    trunc E ≤ φ ↔ Nonempty (E ⟶ iota.{w} φ) := by
  constructor
  · intro below
    exact ⟨fun h => TypeCat.ofHom fun e => ⟨⟨below ⟨e⟩⟩⟩⟩
  · rintro ⟨α⟩ h ⟨e⟩
    exact (α h e).down.down

/-! ### Quantifiers with evidence -/

/-- **Existence along a run, with evidence**: a history ending with the run, and evidence for it. -/
def existsEv {x y : B} (p : x ⟶ y) (E : EvFiber.{w} root x) : EvFiber.{w} root y :=
  fun k => Σ h : {h : root ⟶ x // h ≫ p = k}, E h.1

/-- **Universality along a run, with evidence**: evidence for every history ending with the run. -/
def forallEv {x y : B} (p : x ⟶ y) (E : EvFiber.{w} root x) : EvFiber.{w} root y :=
  fun k => ∀ h : {h : root ⟶ x // h ≫ p = k}, E h.1

/-- **Existence is left adjoint to reindexing, as a bijection of evidence transformers.** -/
def existsEquiv {x y : B} (p : x ⟶ y) (E : EvFiber.{w} root x) (F : EvFiber.{w} root y) :
    (existsEv p E ⟶ F) ≃ (E ⟶ (reindexEv.{w} root p).obj F) where
  toFun α := fun h => TypeCat.ofHom fun e => α (h ≫ p) ⟨⟨h, rfl⟩, e⟩
  invFun β := fun k => TypeCat.ofHom fun pair => pair.1.2 ▸ β pair.1.1 pair.2
  left_inv α := by
    refine funext fun k => ConcreteCategory.hom_ext _ _ ?_
    rintro ⟨⟨h, rfl⟩, e⟩
    rfl
  right_inv β := funext fun _ => ConcreteCategory.hom_ext _ _ fun _ => rfl

/-- **Universality is right adjoint to reindexing, as a bijection of evidence transformers.** -/
def forallEquiv {x y : B} (p : x ⟶ y) (E : EvFiber.{w} root x) (F : EvFiber.{w} root y) :
    ((reindexEv.{w} root p).obj F ⟶ E) ≃ (F ⟶ forallEv p E) where
  toFun α := fun k => TypeCat.ofHom fun f h => α h.1 (cast (congrArg F h.2.symm) f)
  invFun β := fun h => TypeCat.ofHom fun f => β (h ≫ p) f ⟨h, rfl⟩
  left_inv α := funext fun _ => ConcreteCategory.hom_ext _ _ fun _ => rfl
  right_inv β := by
    refine funext fun k => ConcreteCategory.hom_ext _ _ fun f => ?_
    funext h
    obtain ⟨h, same⟩ := h
    subst same
    rfl

theorem trunc_existsEv {x y : B} (p : x ⟶ y) (E : EvFiber.{w} root x) :
    trunc (existsEv p E) = (historyFirstOrder root).existsAlong p (trunc E) := by
  ext k
  constructor
  · rintro ⟨⟨⟨h, same⟩, e⟩⟩
    exact ⟨h, ⟨e⟩, same⟩
  · rintro ⟨h, ⟨e⟩, same⟩
    exact ⟨⟨⟨h, same⟩, e⟩⟩

/-- With choice, truncation commutes with universality. -/
theorem trunc_forallEv {x y : B} (p : x ⟶ y) (E : EvFiber.{w} root x) :
    trunc (forallEv p E) = (historyFirstOrder root).forallAlong p (trunc E) := by
  ext k
  rw [forall_iff]
  constructor
  · rintro ⟨all⟩ h same
    exact ⟨all ⟨h, same⟩⟩
  · intro all
    exact ⟨fun h => Classical.choice (all h.1 h.2)⟩

/-! ### Truncation is a morphism of fibrations -/

variable (root)

/-- **Truncation on total categories.** -/
def truncTotal : EvTotal.{w} root ⥤ (historyDoctrine root).Total where
  obj a := ⟨a.base, trunc a.fiber⟩
  map {a b} f := ((historyDoctrine root).totalHomEquiv ⟨a.base, trunc a.fiber⟩
      ⟨b.base, trunc b.fiber⟩).symm
    ⟨f.base, fun h ⟨e⟩ =>
      ⟨(f.fiber : ∀ h : root ⟶ a.base, a.fiber h ⟶ b.fiber (h ≫ f.base)) h e⟩⟩
  map_id _ := historyTotal_hom_ext root rfl
  map_comp _ _ := historyTotal_hom_ext root rfl

/-- **Truncation lies over the base.** -/
theorem truncTotal_projection :
    truncTotal.{w} root ⋙ (historyDoctrine root).projection = evProjection.{w} root := rfl

/-- **Truncation sends the chosen lifts to the chosen lifts.** -/
theorem truncTotal_lift {x y : B} (E : EvFiber.{w} root y) (p : x ⟶ y) :
    (truncTotal.{w} root).map (evLift root E p) = (historyDoctrine root).lift (trunc E) p :=
  historyTotal_hom_ext root rfl

/-- **Truncation preserves cartesian lifts.** -/
theorem truncTotal_lift_cartesian {x y : B} (E : EvFiber.{w} root y) (p : x ⟶ y) :
    IsStronglyCartesian (historyDoctrine root).projection p
      ((truncTotal.{w} root).map (evLift root E p)) := by
  rw [truncTotal_lift]
  exact (historyDoctrine root).lift_cartesian (trunc E) p

/-- **Truncation preserves every strongly cartesian arrow**: a cartesian arrow is a vertical
isomorphism followed by the chosen lift, and truncation sends both to cartesian arrows. So it is
a morphism of fibrations. -/
theorem truncTotal_cartesian {R : B} {a b : EvTotal.{w} root} (f : R ⟶ b.base) (φ : a ⟶ b)
    [IsStronglyCartesian (evProjection.{w} root) f φ] :
    IsStronglyCartesian (historyDoctrine root).projection f ((truncTotal.{w} root).map φ) := by
  have := evLift_cartesian root b.fiber f
  have fac := IsCartesian.fac (evProjection.{w} root) f (evLift root b.fiber f) φ
  have : IsHomLift (historyDoctrine root).projection (𝟙 R)
      ((truncTotal.{w} root).mapIso (IsCartesian.domainUniqueUpToIso (evProjection.{w} root) f
        (evLift root b.fiber f) φ)).hom :=
    IsHomLift.of_fac _ _ _
      (IsHomLift.domain_eq (evProjection.{w} root) (𝟙 R)
        (IsCartesian.domainUniqueUpToIso (evProjection.{w} root) f (evLift root b.fiber f) φ).hom)
      (IsHomLift.codomain_eq (evProjection.{w} root) (𝟙 R)
        (IsCartesian.domainUniqueUpToIso (evProjection.{w} root) f (evLift root b.fiber f) φ).hom)
      (IsHomLift.fac (evProjection.{w} root) (𝟙 R)
        (IsCartesian.domainUniqueUpToIso (evProjection.{w} root) f (evLift root b.fiber f) φ).hom)
  have := truncTotal_lift_cartesian root b.fiber f
  have composite : IsStronglyCartesian (historyDoctrine root).projection (𝟙 R ≫ f)
      (((truncTotal.{w} root).mapIso (IsCartesian.domainUniqueUpToIso (evProjection.{w} root) f
        (evLift root b.fiber f) φ)).hom ≫ (truncTotal.{w} root).map (evLift root b.fiber f)) :=
    inferInstance
  rw [Category.id_comp, Functor.mapIso_hom, ← Functor.map_comp,
    IsCartesian.domainUniqueUpToIso_hom, fac] at composite
  exact composite

/-! ### Readings -/

variable {root}

/-- Two pieces of evidence for one history that a reading tells apart. -/
def Separates {x : B} {E : EvFiber.{w} root x} {M : Type*} (read : ∀ h, E h → M) : Prop :=
  ∃ (h : root ⟶ x) (e e' : E h), read h e ≠ read h e'

/-- **A reading through the history tells no evidence apart.** -/
theorem throughHistory_not_separates {x : B} {E : EvFiber.{w} root x} {M : Type*}
    (g : (root ⟶ x) → M) : ¬ Separates (E := E) (fun h _ => g h) :=
  fun ⟨_, _, _, differ⟩ => differ rfl

end Evidence

/-! ## Evidence over runs of the candidate step -/

universe uT uS uO
variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]

section RunEvidence

variable (A : SubstitutionAction T S) (label : O → T) (C₀ : Configuration T O)

/-- **An account of runs is a reading through the history**, so it tells no evidence apart. -/
theorem accountReading_not_separates {M : Type*} [Monoid M]
    (account : Mettapedia.Effects.RunAccount (Runs A label) M) {y : Runs A label}
    (E : EvFiber.{0} (runObject A label C₀) y) :
    ¬ Separates (E := E) (fun h _ => account.of h) :=
  throughHistory_not_separates _

/-- **The support of persistent evidence is the evidence truncation, class by class.** A copresheaf of
evidence over runs with its map to histories is a proof-relevant persistent predicate; its image
is a persistent predicate of the run topos, and read at each class it is the truncation of the
fibres of the map. -/
theorem restrict_range_eq_trunc {E : Runs A label ⥤ Type (max uT uS uO)}
    (π : E ⟶ histories A label C₀) (y : Runs A label) :
    restrict (Subfunctor.range π) y =
      trunc.{0} (fun h : runObject A label C₀ ⟶ y => {e : E.obj y // π.app y e = h}) := by
  ext h
  constructor
  · rintro ⟨e, same⟩
    exact ⟨⟨e, same⟩⟩
  · rintro ⟨⟨e, same⟩⟩
    exact ⟨e, same⟩

/-- **Round schedules**: decompositions of the run into rounds, each a round where the earlier
ones left the configuration. -/
def schedules (y : Runs A label) : EvFiber.{0} (runObject A label C₀) y :=
  fun h => {rounds : List (List (Firing T S O)) //
    RoundRun A label C₀ rounds ∧ rounds.flatten = OccurrencePath.sites h}

/-- The boundary peak of a schedule. -/
def boundaryPeak {y : Runs A label} (h : runObject A label C₀ ⟶ y) :
    schedules A label C₀ y h → ℤ :=
  fun schedule => (boundaryProfile schedule.1).peak

/-- **A schedule is a run**: its firings run from `C₀`. -/
theorem schedule_executable {y : Runs A label} {h : runObject A label C₀ ⟶ y}
    (schedule : schedules A label C₀ y h) : Executable A label C₀ (OccurrencePath.sites h) :=
  (congrArg (Executable A label C₀) schedule.2.2).mp (schedule.2.1.executable A label)

/-- **The account of a site annotation is the product over the run's firings.** -/
theorem siteAccount_of_eq {M : Type*} [Monoid M] (grade : Firing T S O → M) :
    ∀ {x y : (theory A label).Term} (p : OccurrencePath (presentation A label) x y),
      (siteAccount A label grade).of p = ((OccurrencePath.sites p).map grade).prod
  | _, _, .refl _ => rfl
  | _, _, .cons o rest => by
      have later := siteAccount_of_eq grade rest
      change grade o.site * (siteAccount A label grade).of rest = grade o.site *
        ((OccurrencePath.sites rest).map grade).prod
      rw [later]

/-- **Ledgers of a receipt annotation**: run-length ledgers expanding to the run's receipt. -/
def ledgers (charges : Firing T S O → List Mettapedia.Machines.NativeCostLedger.Event)
    (y : Runs A label) : EvFiber.{0} (runObject A label C₀) y :=
  fun h => ULift {ledger : Mettapedia.Machines.NativeCostLedger.Ledger //
    Mettapedia.Algebra.RunLengthEvents.expand ledger =
      FreeMonoid.toList ((receiptAccount A label charges).of h)}

/-- The admission and update of a firing, as a step relation on configurations. -/
def firingStep (f : Firing T S O) (C C' : Configuration T O) : Prop :=
  f.Valid A label C ∧ C' = f.result label C

/-- **Rich realizations**: environment-free rich runs from `C₀` whose successful firings are the
run. -/
def realizations (Rich Attempt Environment : Type (max uT uS uO)) (forget : Rich → Firing T S O)
    (y : Runs A label) : EvFiber.{0} (runObject A label C₀) y :=
  fun h => {events : List (AnnotatedRunEvidence.Event Rich Attempt Environment) //
    AnnotatedRunEvidence.NoEnvironment events ∧
      AnnotatedRunEvidence.Run forget (firingStep A label) (fun _ _ _ => False) C₀ events
        (follow label C₀ (OccurrencePath.sites h)) ∧
      AnnotatedRunEvidence.firingWord forget events = OccurrencePath.sites h}

/-- **A rich realization is a run of the thin firings**, by the evidence layer's projection. -/
theorem realization_projects (Rich Attempt Environment : Type (max uT uS uO))
    (forget : Rich → Firing T S O) {y : Runs A label} {h : runObject A label C₀ ⟶ y}
    (r : realizations A label C₀ Rich Attempt Environment forget y h) :
    AnnotatedRunEvidence.FiringRun (firingStep A label) C₀ (OccurrencePath.sites h)
      (follow label C₀ (OccurrencePath.sites h)) :=
  (congrArg (fun w => AnnotatedRunEvidence.FiringRun (firingStep A label) C₀ w
    (follow label C₀ (OccurrencePath.sites h))) r.2.2.2).mp (r.2.2.1.forget_noEnvironment r.2.1)

end RunEvidence

/-! ## Separating examples -/

namespace ScheduleControls

open Mettapedia.Logic.LP
open ConstraintMultisetRewriting.Controls (signature A)
open AnnotatedRuns.Controls (Run)
open AnnotatedRuns.PeakControls (label consumer producer start consumer_producer_round)

/-- A sub-list of a round is a round. -/
theorem round_sublist {C : Configuration (Term signature) Nat} {round round' : List Run}
    (isRound : Round A label C round) (sub : round'.Sublist round) : Round A label C round' := by
  refine ⟨fun f member => isRound.valid f (sub.subset member), ?_,
    isRound.compatible.sublist sub⟩
  obtain ⟨σ, solved⟩ := isRound.joint
  refine ⟨σ, fun e member => solved e ?_⟩
  simp only [jointProblem, List.mem_append, List.mem_flatMap] at member ⊢
  rcases member with inBase | ⟨f, inRound, inAdded⟩
  · exact Or.inl inBase
  · exact Or.inr ⟨f, sub.subset inRound, inAdded⟩

theorem producer_consumer_round : Round A label start [producer, consumer] :=
  consumer_producer_round.perm A label (List.Perm.swap producer consumer [])

/-- The producer, then the consumer, as a path from the start. -/
theorem producer_consumer_path :
    ∃ h : runObject A label start ⟶ classOf A label (follow label start [producer, consumer]),
      OccurrencePath.sites h = [producer, consumer] :=
  exists_path A label start _ (producer_consumer_round.executable A label) _ rfl

/-- One round. -/
theorem one_round : RoundRun A label start [[producer, consumer]] := by
  refine ⟨producer_consumer_round, ?_⟩
  obtain ⟨σ, solved⟩ := (producer_consumer_round.executable A label).2.2
  exact ⟨σ, solved⟩

/-- Two rounds. -/
theorem two_rounds : RoundRun A label start [[producer], [consumer]] :=
  ⟨round_sublist producer_consumer_round ((List.nil_sublist [consumer]).cons_cons producer),
    (producer_consumer_round.cons A label).2, (producer_consumer_round.executable A label).2.2⟩

theorem one_round_peak : (boundaryProfile [[producer, consumer]]).peak = 0 := by decide

theorem two_rounds_peak : (boundaryProfile [[producer], [consumer]]).peak = 1 := by decide

/-- **Separating example: the boundary peak tells two schedules of one run apart.** The producer
and the consumer as one round peak at `0` above the start; as two rounds, at `1`. Both are
evidence that the run is scheduled in rounds, and truncation identifies them. -/
theorem schedules_separated_by_peak :
    ∃ h : runObject A label start ⟶ classOf A label (follow label start [producer, consumer]),
      ∃ s s' : schedules A label start _ h,
        s.1 = [[producer, consumer]] ∧ s'.1 = [[producer], [consumer]] ∧
          boundaryPeak A label start h s = 0 ∧ boundaryPeak A label start h s' = 1 ∧
          h ∈ trunc (schedules A label start _) := by
  obtain ⟨h, hSites⟩ := producer_consumer_path
  exact ⟨h, ⟨[[producer, consumer]], one_round, hSites.symm⟩,
    ⟨[[producer], [consumer]], two_rounds, hSites.symm⟩, rfl, rfl, one_round_peak, two_rounds_peak,
    ⟨⟨[[producer, consumer]], one_round, hSites.symm⟩⟩⟩

theorem schedules_separates :
    Separates (E := schedules A label start (classOf A label (follow label start [producer, consumer])))
      (boundaryPeak A label start) := by
  obtain ⟨h, s, s', -, -, peak, peak', -⟩ := schedules_separated_by_peak
  exact ⟨h, s, s', by rw [peak, peak']; decide⟩

end ScheduleControls

namespace LedgerEvidenceControls

open Mettapedia.Logic.LP
open ConstraintMultisetRewriting.Controls (signature A)
open AnnotatedRuns.Controls (label Run taker reader start taker_then_reader)
open Mettapedia.Machines.NativeCostLedger (Event Ledger)

/-- The taker charges one heap lookup at identity `8`, the reader one at identity `9`. -/
def charges (f : Run) : List Event :=
  if f.selection.taken = [] then [AnnotatedRuns.LedgerControls.second]
  else [AnnotatedRuns.LedgerControls.first]

/-- The run of the taker and then the reader. -/
theorem taker_reader_path :
    ∃ h : runObject A label start ⟶ classOf A label (follow label start [taker, reader]),
      OccurrencePath.sites h = [taker, reader] :=
  exists_path A label start _ taker_then_reader _ rfl

theorem receipt_eq {y : Runs A label} (h : runObject A label start ⟶ y)
    (hSites : OccurrencePath.sites h = [taker, reader]) :
    FreeMonoid.toList ((receiptAccount A label charges).of h) =
      [AnnotatedRuns.LedgerControls.first] ++ [AnnotatedRuns.LedgerControls.second] := by
  have product := siteAccount_of_eq A label (fun f => FreeMonoid.ofList (charges f)) h
  have listed : ((OccurrencePath.sites h).map fun f => FreeMonoid.ofList (charges f)).prod =
      FreeMonoid.ofList [AnnotatedRuns.LedgerControls.first] *
        (FreeMonoid.ofList [AnnotatedRuns.LedgerControls.second] * 1) :=
    (congrArg (fun l : List Run => (l.map fun f => FreeMonoid.ofList (charges f)).prod) hSites).trans
      rfl
  change FreeMonoid.toList ((siteAccount A label fun f => FreeMonoid.ofList (charges f)).of h) = _
  rw [product, listed, mul_one, FreeMonoid.toList_mul, FreeMonoid.toList_ofList,
    FreeMonoid.toList_ofList]

/-- The number of records of a ledger. -/
def records {y : Runs A label} (h : runObject A label start ⟶ y) :
    ledgers A label start charges y h → ℕ :=
  fun ledger => ledger.down.1.length

/-- **Separating example: one receipt, two ledgers.** Compressing the whole receipt gives one
record; compressing each firing's charges gives two. Both expand to the receipt, so both are
evidence for it and truncation identifies them; their number of records tells them apart. -/
theorem ledgers_separated_by_records :
    ∃ h : runObject A label start ⟶ classOf A label (follow label start [taker, reader]),
      ∃ ledger ledger' : ledgers A label start charges _ h,
        records h ledger = 1 ∧ records h ledger' = 2 := by
  obtain ⟨h, hSites⟩ := taker_reader_path
  obtain ⟨one, two, same⟩ := AnnotatedRuns.LedgerControls.compression_merges_runs
  refine ⟨h, ⟨⟨compress 255 ([AnnotatedRuns.LedgerControls.first] ++
      [AnnotatedRuns.LedgerControls.second]), ?_⟩⟩,
    ⟨⟨compress 255 [AnnotatedRuns.LedgerControls.first] ++
      compress 255 [AnnotatedRuns.LedgerControls.second], ?_⟩⟩, one, two⟩
  · rw [receipt_eq h hSites, expand_compress]
  · rw [receipt_eq h hSites, ← same, expand_compress]

end LedgerEvidenceControls

namespace RealizationControls

open Mettapedia.Logic.LP
open ConstraintMultisetRewriting.Controls (signature A)
open AnnotatedRuns.Controls (label Run taker start taker_valid)
open AnnotatedRunEvidence (FiringEvidence AttemptRecord EnvironmentEvent Provenance Event
  NoEnvironment firingWord attemptCharge)

abbrev Rich := FiringEvidence Run Nat (Provenance Nat Nat Nat) Nat Nat (List Nat)
abbrev Attempt := AttemptRecord (List Nat) Nat Nat Nat
abbrev Env := EnvironmentEvent Nat Nat Nat

/-- The taker, with a solver witness, provenance, search world, round and query evidence. -/
def richTaker : Rich where
  firing := taker
  witness := 11
  provenance := ⟨4, 5, some 6⟩
  world := 7
  round := 0
  queryEvidence := [1, 3]

def forget (r : Rich) : Run := r.firing

/-- The taker fired directly. -/
def direct : List (Event Rich Attempt Env) := [.fired richTaker]

/-- The taker fired after a refused attempt that charged `13`. -/
def afterRefusal : List (Event Rich Attempt Env) :=
  [.attempted AnnotatedRunEvidence.Controls.refusal, .fired richTaker]

theorem taker_runs : Executable A label start [taker] := ⟨taker_valid, taker_valid.firing.consistent⟩

theorem taker_path :
    ∃ h : runObject A label start ⟶ classOf A label (follow label start [taker]),
      OccurrencePath.sites h = [taker] :=
  exists_path A label start _ taker_runs _ rfl

theorem fired_run : AnnotatedRunEvidence.Run forget (firingStep A label) (fun _ _ _ => False) start
    direct (follow label start [taker]) :=
  .firing (middle := taker.result label start) ⟨taker_valid, rfl⟩ (.nil _)

theorem refused_then_fired_run : AnnotatedRunEvidence.Run forget (firingStep A label)
    (fun _ _ _ => False) start afterRefusal (follow label start [taker]) :=
  .attempted fired_run

/-- The attempt charge of a realization. -/
def charge {y : Runs A label} (h : runObject A label start ⟶ y) :
    realizations A label start Rich Attempt Env forget y h → ℕ :=
  fun r => attemptCharge r.1

/-- **Separating example: one firing history, two rich realizations.** The taker fired
directly, or after a refused attempt. Both are environment-free rich runs whose successful
firings are the run, so truncation identifies them; their attempt charges are `0` and `13`. -/
theorem realizations_separated_by_charge :
    ∃ h : runObject A label start ⟶ classOf A label (follow label start [taker]),
      ∃ r r' : realizations A label start Rich Attempt Env forget _ h,
        r.1 = direct ∧ r'.1 = afterRefusal ∧ charge h r = 0 ∧ charge h r' = 13 := by
  obtain ⟨h, hSites⟩ := taker_path
  have runs : ∀ events : List (Event Rich Attempt Env),
      AnnotatedRunEvidence.Run forget (firingStep A label) (fun _ _ _ => False)
      start events (follow label start [taker]) →
      AnnotatedRunEvidence.Run forget (firingStep A label) (fun _ _ _ => False) start events
        (follow label start (OccurrencePath.sites h)) := fun events run =>
    (congrArg (fun w => AnnotatedRunEvidence.Run forget (firingStep A label) (fun _ _ _ => False)
      start events (follow label start w)) hSites).mpr run
  exact ⟨h, ⟨direct, .firing richTaker .nil, runs _ fired_run, (rfl : _ = [taker]).trans hSites.symm⟩,
    ⟨afterRefusal, .attempted _ (.firing richTaker .nil), runs _ refused_then_fired_run,
      (rfl : _ = [taker]).trans hSites.symm⟩, rfl, rfl, rfl, rfl⟩

end RealizationControls

#print axioms reindexEv_id
#print axioms reindexEv_comp
#print axioms evidenceFunctor
#print axioms evProjection_fibered
#print axioms evLift_cartesian
#print axioms trunc_reindex
#print axioms trunc_iota
#print axioms iota_hom_subsingleton
#print axioms trunc_le_iff_nonempty_hom
#print axioms trunc_le_iff
#print axioms existsEquiv
#print axioms forallEquiv
#print axioms trunc_existsEv
#print axioms trunc_forallEv
#print axioms truncTotal
#print axioms truncTotal_projection
#print axioms truncTotal_lift
#print axioms truncTotal_lift_cartesian
#print axioms truncTotal_cartesian
#print axioms throughHistory_not_separates
#print axioms accountReading_not_separates
#print axioms restrict_range_eq_trunc
#print axioms schedule_executable
#print axioms siteAccount_of_eq
#print axioms realization_projects
#print axioms ScheduleControls.round_sublist
#print axioms ScheduleControls.two_rounds
#print axioms ScheduleControls.schedules_separated_by_peak
#print axioms ScheduleControls.schedules_separates
#print axioms LedgerEvidenceControls.receipt_eq
#print axioms LedgerEvidenceControls.ledgers_separated_by_records
#print axioms RealizationControls.realizations_separated_by_charge

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns
