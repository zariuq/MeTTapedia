import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsPredicates
import Mettapedia.CategoryTheory.CopresheafToposDoctrine

/-!
# Higher-order logic over runs: the copresheaf topos of the run category

The doctrine of histories (`AnnotatedRunsPredicates`) is first order. A higher-order doctrine
needs a generic predicate on a cartesian closed base, and the run category has neither.

## Why the run category alone cannot carry it

`historyDoctrine_no_generic`: on any category in which no loop fixes an arrow out of the root
(`NoStabilizers`), the doctrine of histories has **no generic predicate**. Classifying the true
predicate and the false predicate at the root forces both characteristic maps at the classifier
to be identities, so true and false would coincide there. Runs are words of firings, so no
nonempty run fixes a history (`runs_noStabilizers`), and the doctrine of histories over runs has
no generic predicate (`runs_no_generic`). This holds whatever the root.

Nor is the run category cartesian: two classes whose stores have no solution and whose occurrences
differ admit no firing, so no class is terminal (`no_terminal_of_dead`, `not_cartesian_of_dead`;
for the control signature `LogicControls.runs_not_cartesian`). A `PredicateDoctrine.HigherOrder`
doctrine cannot even be stated on it.

## The base that carries it: copresheaves on runs

`runLogic` is the subobject doctrine of the copresheaf topos `Runs ⥤ Type` from
`CopresheafToposDoctrine`: a `PredicateDoctrine.HigherOrder` doctrine with the cosieves as truth
values. Read Kripke–Joyal style, the stages are configuration classes and a stage `y` is
accessible from `x` along every run from `x` to `y`.

* **Histories** from `C₀` form the representable copresheaf `histories C₀`: at a class, the runs
  from `C₀` to it; a run extends them.
* **Persistent predicates** are its subfunctors (`Persistent C₀`): sets of histories closed under
  extension by runs. Implication and negation are Kripke's (`forces_himp_iff`,
  `forces_compl_iff`): `S ⇨ T` holds of a history when every extension that satisfies `S`
  satisfies `T`.
* The higher-order fragment is the whole topos logic: predicates on `X ⊗ Y` are maps
  `Y ⟶ (X ⟹ Ω)` (`CopresheafToposDoctrine.comprehension`), so quantifiers over predicates on
  histories range over the power object of `histories C₀`.

## How the Boolean doctrine of histories sits inside

A predicate of the doctrine of histories, read at every class, is a family of sets of runs. The
persistent predicates are exactly the families that every run carries into themselves: each run
is a Hoare triple of the family with itself (`persistent_iff`, `restrict_hoare`). Hence:

* **an embedding** (`restrict_injective`, `restrict_inf`, `restrict_sup`, `restrict_top`,
  `restrict_bot`): persistent predicates are a sublattice of families of history predicates;
* **with both adjoints** (`once_le_iff`, `le_henceforth_iff`): `once φ`, the histories with a
  prefix in `φ`, is the least persistent predicate above `φ`; `henceforth φ`, the histories all
  of whose extensions lie in `φ`, is the greatest persistent predicate below `φ`;
* **not a Heyting embedding** (`restrict_himp_le`, `LogicControls.restrict_compl_ne`): Kripke
  implication lies below Boolean implication, and negation is not preserved;
* **sections** (`sectionOf`, `sectionOf_projection`): a persistent predicate is a section of the
  fibration of the doctrine of histories, each run being a Hoare triple of it with itself.

Controls, on the taker and the reader:

* negative: `lastTaker_not_persistent`, "the last firing was the taker", is a predicate of the
  doctrine of histories that is not persistent: the reader extends `[taker]` to
  `[taker, reader]`;
* positive: `takerFired`, "the taker fired", is persistent;
* negative: `excluded_middle_fails`: at the empty history, "the taker fired" or its Kripke
  negation fails, since the taker has not fired and can still fire, while the Boolean
  complement holds there (`boolean_excluded_middle`);
* the truth values at the start are not two (`start_truth_values`): the empty cosieve, the
  cosieve of runs that fire the taker, and the maximal cosieve are three distinct ones.
-/

set_option autoImplicit false

open CategoryTheory Opposite

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns

open Mettapedia.CategoryTheory.PredicateDoctrine
open Mettapedia.CategoryTheory.CopresheafToposDoctrine (higherOrder doctrine omega truth
  characteristic characteristicCosieve subfunctor_ext mem_himp_iff mem_compl_iff)
open Mettapedia.GSLT.Causality.OccurrenceHistory (OccurrencePath)

/-! ## The doctrine of histories has no generic predicate on its own base -/

section NoGeneric

universe uB vB

variable {B : Type uB} [Category.{vB} B] (root : B)

/-- No loop fixes an arrow out of the root. -/
def NoStabilizers : Prop := ∀ ⦃x : B⦄ (h : root ⟶ x) (v : x ⟶ x), h ≫ v = h → v = 𝟙 x

/-- **Without stabilizing loops, the doctrine of histories has no generic predicate.** -/
theorem historyDoctrine_no_generic (free : NoStabilizers root) :
    IsEmpty (GenericPredicate B (historyDoctrine root)) := by
  constructor
  intro G
  have topLoop : G.characteristic G.object ⊤ = 𝟙 G.object := by
    have extended := G.characteristic_reindex (G.characteristic root ⊤)
      (⊤ : (historyDoctrine root).Fiber G.object)
    rw [(historyDoctrine root).reindex_top] at extended
    exact free _ _ extended.symm
  have botLoop : G.characteristic G.object ⊥ = 𝟙 G.object := by
    have extended := G.characteristic_reindex (G.characteristic root ⊥)
      (⊥ : (historyDoctrine root).Fiber G.object)
    rw [(historyDoctrine root).reindex_bot] at extended
    exact free _ _ extended.symm
  have topBot : (⊤ : (historyDoctrine root).Fiber G.object) = ⊥ := by
    rw [← G.classifies G.object ⊤, ← G.classifies G.object ⊥, topLoop, botLoop]
  have member : G.characteristic root ⊤ ∈ (⊤ : Set (root ⟶ G.object)) := Set.mem_univ _
  rw [show (⊤ : Set (root ⟶ G.object)) = ⊥ from topBot] at member
  exact member

/-- Arrows of the total category of the doctrine of histories are determined by their runs. -/
theorem historyTotal_hom_ext {a b : (historyDoctrine root).Total} {f g : a ⟶ b}
    (same : f.base = g.base) : f = g :=
  ((historyDoctrine root).totalHomEquiv a b).injective (Subtype.ext same)

end NoGeneric

universe uT uS uO
variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]

section RunTopos

variable (A : SubstitutionAction T S) (label : O → T)

/-- **No nonempty run fixes a history.** -/
theorem runs_noStabilizers (C₀ : Configuration T O) : NoStabilizers (runObject A label C₀) := by
  intro x h v same
  have sitesEq : OccurrencePath.sites h ++ OccurrencePath.sites v = OccurrencePath.sites h :=
    (OccurrencePath.sites_append h v).symm.trans (congrArg OccurrencePath.sites same)
  have lengths : (OccurrencePath.sites h).length + (OccurrencePath.sites v).length =
      (OccurrencePath.sites h).length :=
    (List.length_append ..).symm.trans (congrArg List.length sitesEq)
  have empty : OccurrencePath.sites v = [] := List.eq_nil_of_length_eq_zero (by omega)
  exact path_ext A label v (𝟙 x) (empty.trans rfl)

/-- **The doctrine of histories over runs has no generic predicate**, from any root. -/
theorem runs_no_generic (C₀ : Configuration T O) :
    IsEmpty (GenericPredicate (Runs A label) (historyDoctrine (runObject A label C₀))) :=
  historyDoctrine_no_generic _ (runs_noStabilizers A label C₀)

/-- **Two configurations without solutions and with different occurrences leave no terminal class.**
No firing is admitted where the store has no solution, so the only run out of such a class is
empty, and a terminal class would equal both. -/
theorem no_terminal_of_dead (C D : Configuration T O) (deadC : ¬ A.Consistent C.equations)
    (deadD : ¬ A.Consistent D.equations) (apart : C.present ≠ D.present) (t : Runs A label) :
    IsEmpty (Limits.IsTerminal t) := by
  constructor
  intro terminal
  have toC := terminal.from (runObject A label C)
  have toD := terminal.from (runObject A label D)
  have atC : t = classOf A label C :=
    (target_eq A label toC C rfl).trans (congrArg (fun w => classOf A label (follow label C w))
      (sites_eq_nil_of_inconsistent A label toC C rfl deadC))
  have atD : t = classOf A label D :=
    (target_eq A label toD D rfl).trans (congrArg (fun w => classOf A label (follow label D w))
      (sites_eq_nil_of_inconsistent A label toD D rfl deadD))
  exact apart (Quotient.exact (atC.symm.trans atD)).2

open MonoidalCategory in
/-- **Without a terminal class the run category is not cartesian**, so no cartesian closed
structure, and no `PredicateDoctrine.HigherOrder` doctrine, lives on it. -/
theorem not_cartesian_of_dead (C D : Configuration T O) (deadC : ¬ A.Consistent C.equations)
    (deadD : ¬ A.Consistent D.equations) (apart : C.present ≠ D.present) :
    IsEmpty (CartesianMonoidalCategory (Runs A label)) := by
  constructor
  intro cartesian
  exact (no_terminal_of_dead A label C D deadC deadD apart (𝟙_ (Runs A label))).false
    CartesianMonoidalCategory.isTerminalTensorUnit

/-- **The higher-order doctrine over runs**: the subobject doctrine of the copresheaf topos on
the run category. -/
abbrev runLogic := higherOrder.{0} (Runs A label)

/-- **Histories from `C₀`**: at a class, the runs from `C₀` to it. -/
abbrev histories (C₀ : Configuration T O) := coyoneda.obj (op (runObject A label C₀))

/-- **Persistent predicates on histories**: sets of histories closed under extension by runs. -/
abbrev Persistent (C₀ : Configuration T O) := (runLogic A label).Fiber (histories A label C₀)

variable {A label} {C₀ : Configuration T O}

/-- A persistent predicate read at one class: a predicate of the doctrine of histories there. -/
def restrict (S : Persistent A label C₀) (y : Runs A label) :
    (runPredicates A label C₀).Fiber y :=
  S.obj y

/-- **Kripke implication on histories.** -/
theorem forces_himp_iff (S S' : Persistent A label C₀) {x : Runs A label}
    (h : runObject A label C₀ ⟶ x) :
    h ∈ restrict (S ⇨ S') x ↔
      ∀ ⦃y : Runs A label⦄ (p : x ⟶ y), h ≫ p ∈ restrict S y → h ≫ p ∈ restrict S' y :=
  Iff.rfl

/-- **Kripke negation on histories**: no extension satisfies the predicate. -/
theorem forces_compl_iff (S : Persistent A label C₀) {x : Runs A label}
    (h : runObject A label C₀ ⟶ x) :
    h ∈ restrict Sᶜ x ↔ ∀ ⦃y : Runs A label⦄ (p : x ⟶ y), h ≫ p ∉ restrict S y :=
  mem_compl_iff (F := histories A label C₀) S x h

/-- **Every run is a Hoare triple of a persistent predicate with itself.** -/
theorem restrict_hoare (S : Persistent A label C₀) {x y : Runs A label} (p : x ⟶ y) :
    restrict S x ≤ (runPredicates A label C₀).reindex p (restrict S y) :=
  fun _ member => S.map p member

/-- **Persistent predicates are exactly the families every run carries into themselves.** -/
theorem persistent_iff (φ : ∀ y : Runs A label, (runPredicates A label C₀).Fiber y) :
    (∃ S : Persistent A label C₀, ∀ y, restrict S y = φ y) ↔
      ∀ ⦃x y : Runs A label⦄ (p : x ⟶ y), φ x ≤ (runPredicates A label C₀).reindex p (φ y) := by
  constructor
  · rintro ⟨S, same⟩ x y p
    rw [← same x, ← same y]
    exact restrict_hoare S p
  · intro carried
    exact ⟨⟨fun y => φ y, fun p _ member => carried p member⟩, fun _ => rfl⟩

theorem restrict_injective : Function.Injective (restrict (A := A) (label := label) (C₀ := C₀)) :=
  fun _ _ same => Subfunctor.ext same

theorem restrict_inf (S S' : Persistent A label C₀) (y : Runs A label) :
    restrict (S ⊓ S') y = restrict S y ⊓ restrict S' y := rfl

theorem restrict_sup (S S' : Persistent A label C₀) (y : Runs A label) :
    restrict (S ⊔ S') y = restrict S y ⊔ restrict S' y := rfl

theorem restrict_top (y : Runs A label) : restrict (⊤ : Persistent A label C₀) y = ⊤ := rfl

theorem restrict_bot (y : Runs A label) : restrict (⊥ : Persistent A label C₀) y = ⊥ := rfl

/-- **Kripke implication lies below Boolean implication.** -/
theorem restrict_mono {S S' : Persistent A label C₀} (below : S ≤ S') (y : Runs A label) :
    restrict S y ≤ restrict S' y :=
  (Subfunctor.le_def _ _).mp below y

theorem restrict_himp_le (S S' : Persistent A label C₀) (y : Runs A label) :
    restrict (S ⇨ S') y ≤ (restrict S y ⇨ restrict S' y) :=
  le_himp_iff.mpr (restrict_mono himp_inf_le y)

/-- **Once**: the histories with a prefix in `φ`. -/
def once (φ : ∀ y : Runs A label, (runPredicates A label C₀).Fiber y) : Persistent A label C₀ where
  obj y := {k | ∃ (x : Runs A label) (h : runObject A label C₀ ⟶ x) (p : x ⟶ y), h ∈ φ x ∧ h ≫ p = k}
  map {y y'} q k := by
    rintro ⟨x, h, p, member, rfl⟩
    exact ⟨x, h, p ≫ q, member, (Category.assoc h p q).symm⟩

/-- **Henceforth**: the histories all of whose extensions lie in `φ`. -/
def henceforth (φ : ∀ y : Runs A label, (runPredicates A label C₀).Fiber y) :
    Persistent A label C₀ where
  obj x := {h | ∀ ⦃y : Runs A label⦄ (p : x ⟶ y), h ≫ p ∈ φ y}
  map {x x'} q h holds y p := by
    change (h ≫ q) ≫ p ∈ φ y
    rw [Category.assoc]
    exact holds (q ≫ p)

/-- **Once is the least persistent predicate above a family.** -/
theorem once_le_iff (φ : ∀ y : Runs A label, (runPredicates A label C₀).Fiber y)
    (S : Persistent A label C₀) : once φ ≤ S ↔ ∀ y, φ y ≤ restrict S y := by
  constructor
  · intro below y h member
    have inOnce : h ∈ (once φ).obj y := ⟨y, h, 𝟙 y, member, Category.comp_id h⟩
    exact (Subfunctor.le_def _ _).mp below y inOnce
  · intro below
    refine (Subfunctor.le_def _ _).mpr fun y k => ?_
    rintro ⟨x, h, p, member, rfl⟩
    exact S.map p (below x member)

/-- **Henceforth is the greatest persistent predicate below a family.** -/
theorem le_henceforth_iff (φ : ∀ y : Runs A label, (runPredicates A label C₀).Fiber y)
    (S : Persistent A label C₀) : S ≤ henceforth φ ↔ ∀ y, restrict S y ≤ φ y := by
  constructor
  · intro below y h member
    have holds := (Subfunctor.le_def _ _).mp below y member (𝟙 y)
    rwa [Category.comp_id] at holds
  · intro below
    refine (Subfunctor.le_def _ _).mpr fun x h member y p => ?_
    exact below y (S.map p member)

/-- Firings of a composite run. -/
theorem mem_sites_comp {x y z : Runs A label} (p : x ⟶ y) (q : y ⟶ z) (f : Firing T S O) :
    f ∈ OccurrencePath.sites (p ≫ q) ↔ f ∈ OccurrencePath.sites p ∨ f ∈ OccurrencePath.sites q :=
  (congrArg (fun l => f ∈ l) (OccurrencePath.sites_append p q)).to_iff.trans List.mem_append

/-- **A persistent predicate is a section of the fibration of history predicates**: each class
carries the predicate there, and each run is a Hoare triple of it with itself. -/
def sectionOf (S : Persistent A label C₀) :
    Runs A label ⥤ (historyDoctrine (runObject A label C₀)).Total where
  obj x := ⟨x, restrict S x⟩
  map {x y} p := ((historyDoctrine (runObject A label C₀)).totalHomEquiv ⟨x, restrict S x⟩
    ⟨y, restrict S y⟩).symm ⟨p, restrict_hoare S p⟩
  map_id _ := historyTotal_hom_ext _ rfl
  map_comp _ _ := historyTotal_hom_ext _ rfl

theorem sectionOf_projection (S : Persistent A label C₀) :
    sectionOf S ⋙ (historyDoctrine (runObject A label C₀)).projection = 𝟭 (Runs A label) := rfl

end RunTopos

/-! ## Controls -/

namespace LogicControls

open Mettapedia.Logic.LP
open ConstraintMultisetRewriting.Controls (signature A)
open AnnotatedRuns.Controls (label Run taker reader start taker_valid taker_then_reader)

/-- A store without solutions. -/
def deadStore : EquationStore (Term signature) :=
  [(.const 0, ConstraintMultisetRewriting.Controls.f (.const 0))]

theorem deadStore_inconsistent : ¬ A.Consistent deadStore := by
  rintro ⟨σ, solved⟩
  have holds := solved _ (List.mem_singleton_self _)
  change (Term.const 0 : Term signature) = Term.app () _ at holds
  cases holds

/-- **The run category of the control signature has no terminal object, so it is not
cartesian.** -/
theorem runs_not_cartesian : IsEmpty (CartesianMonoidalCategory (Runs A label)) :=
  not_cartesian_of_dead A label ⟨deadStore, ∅⟩ ⟨deadStore, {0}⟩ deadStore_inconsistent
    deadStore_inconsistent (by decide)

/-- "The taker fired." -/
def takerFiredAt (y : Runs A label) : (runPredicates A label start).Fiber y :=
  {p | taker ∈ OccurrencePath.sites p}

/-- "The last firing was the taker." -/
def lastTaker (y : Runs A label) : (runPredicates A label start).Fiber y :=
  {p | (OccurrencePath.sites p).getLast? = some taker}

/-- **Positive control: "the taker fired" is persistent.** -/
def takerFired : Persistent A label start where
  obj y := takerFiredAt y
  map {y y'} q p member := by
    exact (mem_sites_comp p q taker).mpr (Or.inl member)

/-- The run of the taker and then the reader, split after the taker. -/
theorem taker_then_reader_split :
    ∃ (m : Runs A label) (first : runObject A label start ⟶ m)
      (second : m ⟶ classOf A label (follow label start [taker, reader])),
      OccurrencePath.sites first = [taker] ∧ OccurrencePath.sites second = [reader] := by
  obtain ⟨p, pSites⟩ := exists_path A label start [taker, reader] taker_then_reader _ rfl
  obtain ⟨m, first, second, -, firstSites, secondSites⟩ := split A label p [taker] [reader] pSites
  exact ⟨m, first, second, firstSites, secondSites⟩

/-- **Negative control: "the last firing was the taker" is not persistent.** The reader extends
`[taker]`, whose last firing is the taker, to `[taker, reader]`, whose last firing is not. -/
theorem lastTaker_not_persistent :
    ¬ ∃ P : Persistent A label start, ∀ y, restrict P y = lastTaker y := by
  intro persistent
  have carried := (persistent_iff lastTaker).mp persistent
  obtain ⟨m, first, second, firstSites, secondSites⟩ := taker_then_reader_split
  have inFirst : first ∈ lastTaker m :=
    (congrArg List.getLast? firstSites).trans rfl
  have extended : (OccurrencePath.sites (first ≫ second)).getLast? = some taker :=
    carried second inFirst
  have joined : (OccurrencePath.sites first ++ OccurrencePath.sites second).getLast? = some taker :=
    (congrArg List.getLast? (OccurrencePath.sites_append first second)).symm.trans extended
  have readerLast : (OccurrencePath.sites first ++ OccurrencePath.sites second).getLast? =
      some reader :=
    (congrArg (fun l => (l ++ OccurrencePath.sites second).getLast?) firstSites).trans
      ((congrArg (fun l => ([taker] ++ l).getLast?) secondSites).trans rfl)
  exact AnnotationControls.taker_ne_reader (Option.some.inj (joined.symm.trans readerLast))

/-- The empty history at the start. -/
abbrev emptyHistory : runObject A label start ⟶ runObject A label start := 𝟙 _

theorem emptyHistory_not_fired : emptyHistory ∉ restrict takerFired (runObject A label start) :=
  fun member => by cases member

/-- The run of the taker from the start, as an extension of the empty history, fires the taker. -/
theorem first_fires {m : Runs A label} (first : runObject A label start ⟶ m)
    (firstSites : OccurrencePath.sites first = [taker]) :
    emptyHistory ≫ first ∈ restrict takerFired m :=
  (congrArg (fun l => taker ∈ l) firstSites).mpr (List.mem_singleton_self _)

/-- **Negative control: excluded middle fails for a persistent predicate.** At the empty history,
the taker has not fired, and it can still fire, so neither "the taker fired" nor its Kripke
negation holds. -/
theorem excluded_middle_fails : takerFired ⊔ takerFiredᶜ ≠ (⊤ : Persistent A label start) := by
  intro excluded
  have member : emptyHistory ∈ restrict (takerFired ⊔ takerFiredᶜ) (runObject A label start) :=
    (congrArg (fun X => emptyHistory ∈ restrict X (runObject A label start)) excluded).mpr
      (Set.mem_univ _)
  rcases member with fired | never
  · exact emptyHistory_not_fired fired
  · obtain ⟨m, first, -, firstSites, -⟩ := taker_then_reader_split
    exact (forces_compl_iff takerFired emptyHistory).mp never first (first_fires first firstSites)

/-- **In the doctrine of histories excluded middle holds**: there the empty history lies in the
Boolean complement of "the taker fired". -/
theorem boolean_excluded_middle :
    emptyHistory ∈ (restrict takerFired (runObject A label start))ᶜ :=
  emptyHistory_not_fired

/-- **The restriction does not preserve negation.** -/
theorem restrict_compl_ne :
    restrict takerFiredᶜ (runObject A label start) ≠
      (restrict takerFired (runObject A label start))ᶜ := by
  intro same
  have member : emptyHistory ∈ restrict takerFiredᶜ (runObject A label start) :=
    (congrArg (fun X => emptyHistory ∈ X) same).mpr boolean_excluded_middle
  obtain ⟨m, first, -, firstSites, -⟩ := taker_then_reader_split
  exact (forces_compl_iff takerFired emptyHistory).mp member first (first_fires first firstSites)

/-- The truth value of "the taker fired" at the empty history: the cosieve of runs from the start
that fire the taker. -/
abbrev takerCosieve := characteristicCosieve.{0} takerFired emptyHistory

/-- **The truth values at the start are not two.** The empty cosieve, the cosieve of runs that
fire the taker, and the maximal cosieve are distinct. -/
theorem start_truth_values :
    (⊥ : Subfunctor (coyoneda.obj (op (runObject A label start)))) ≠ takerCosieve ∧
      takerCosieve ≠ (⊤ : Subfunctor (coyoneda.obj (op (runObject A label start)))) := by
  obtain ⟨m, first, -, firstSites, -⟩ := taker_then_reader_split
  have firstIn : first ∈ takerCosieve.obj m := first_fires first firstSites
  refine ⟨fun same => ?_, fun same => ?_⟩
  · exact (congrArg (fun X : Subfunctor (coyoneda.obj (op (runObject A label start))) =>
      first ∈ X.obj m) same).mpr firstIn
  · have member : 𝟙 (runObject A label start) ∈ takerCosieve.obj (runObject A label start) :=
      (congrArg (fun X : Subfunctor (coyoneda.obj (op (runObject A label start))) =>
        𝟙 (runObject A label start) ∈ X.obj (runObject A label start)) same).mpr (Set.mem_univ _)
    exact emptyHistory_not_fired member

end LogicControls

#print axioms historyDoctrine_no_generic
#print axioms historyTotal_hom_ext
#print axioms runs_noStabilizers
#print axioms runs_no_generic
#print axioms no_terminal_of_dead
#print axioms not_cartesian_of_dead
#print axioms runLogic
#print axioms forces_himp_iff
#print axioms forces_compl_iff
#print axioms restrict_hoare
#print axioms persistent_iff
#print axioms restrict_injective
#print axioms restrict_mono
#print axioms restrict_himp_le
#print axioms mem_sites_comp
#print axioms once
#print axioms henceforth
#print axioms once_le_iff
#print axioms le_henceforth_iff
#print axioms sectionOf
#print axioms sectionOf_projection
#print axioms LogicControls.deadStore_inconsistent
#print axioms LogicControls.runs_not_cartesian
#print axioms LogicControls.takerFired
#print axioms LogicControls.lastTaker_not_persistent
#print axioms LogicControls.first_fires
#print axioms LogicControls.excluded_middle_fails
#print axioms LogicControls.boolean_excluded_middle
#print axioms LogicControls.restrict_compl_ne
#print axioms LogicControls.start_truth_values

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns
