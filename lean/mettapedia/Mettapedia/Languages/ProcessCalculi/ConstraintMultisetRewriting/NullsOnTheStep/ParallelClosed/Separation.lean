import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.ParallelClosed.Presentations
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.ParallelClosed.StepSource

/-!
# The separation, instantiated, and the translations that show it is not vacuous

Source: the step under the absence-guarded program (`source`, from `StepSource`), whose parallel
composition is the union of configurations on composable pairs. It is switchable
(`source_switchable`). Absence is one source of switchability: over first-order terms a program with
no check at all is switchable through a tell on an unknown the neighbour's knowledge constrains, and
the same separations hold for it (`PositiveTell`).

## Targets (each persistent)

* **Every presentation with a parallel context rule**, read modulo its equations
  (`presentationCalculus`, persistent by `presentationCalculus_persistent`):
  `no_uniformTranslation_presentation`. Rho's presentation is an instance
  (`no_uniformTranslation_rhoCalc`).
* **The reduction of every rho rule set of the tree** on rho processes modulo structural
  congruence (`rhoCalculus`, persistent by `rhoCalculus_persistent`, through
  `RhoScopedParallelEvents.step_join`): `no_uniformTranslation_rho`.
* **Every calculus of positive bag rules** (`bagCalculus`): `no_uniformTranslation_bag`.

Every statement is about uniform translations (`UniformTranslation`: homomorphic on parallel
composition up to the target's static equivalence, preserving and reflecting reachable success). On
every target, success is that one fixed term is a parallel component: a fixed pattern `ω` for
presentations, a fixed process `c` for rho, the row `T` for bags. The output barbs of rho (an output
on some name) are not taken as the success observation here.

## The hypotheses are needed (`Controls`)

Each translation below satisfies every hypothesis of `no_uniformTranslation` but one.

* **Homomorphic and preserving, not reflecting** (`Controls.rows_into_maker`): send a configuration
  to the bag of its rows, in a target that can always make `T`.
* **Homomorphic and reflecting, not preserving** (`Controls.rows_into_inert`): the bag of rows, in a
  target with no rules. On rho processes, the constant null process is homomorphic and reflecting
  and not preserving (`Controls.zero_into_rho`).
* **Preserving and reflecting, not homomorphic** (`Controls.owner_translation`): the characteristic
  function of reachable success (`Controls.owner`: the bag holding `T` when the configuration can
  succeed, the empty bag otherwise), into the bag calculus with no rules. It preserves and reflects
  success by its definition, a case on success, and is not homomorphic on parallel composition. It
  is not built from the configuration's rows, so it is a control for homomorphism, not an
  interpreter of the step. A presentation whose rule tests the rows of the whole store is
  `RuleSyntax.Presentation.wholeStore` (`whole_presents_absence`); the translation of the source
  into it built from the rows preserves and reflects reachable success and is not homomorphic on
  parallel composition (`Interpreter.interpret_succeeds_iff`, `Interpreter.interpret_not_homomorphic`).
* **The target property is needed** (`Controls.identity_into_source`): the identity is a uniform
  translation of the source into itself, and the source is not persistent.
* **The source property is needed**: a program that fires and is not switchable has a uniform
  translation into a persistent bag calculus (`Monotone.relayTranslation`).

## The existing theorems as instances

`Composition.FrameClosed` and `Composition.ParClosed` are `ClosedBeside` at the union of
multisets and at the parallel composition of terms (`frameClosed_iff`, `parClosed_iff`), and the
reduction of every rho rule set is closed beside (`rho_closedBeside`). `no_reaction_is_absence` and
`rho_step_not_join_sensitive` are re-derived from `not_iff_of_switchedOff`
(`no_reaction_is_absence_instance`, `rho_step_not_join_sensitive_instance`); `parClosed_not_absence`
is the same argument at `parClosed_iff`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.ParallelClosed

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextualStep (BasePremiseEvaluator)
open NamesOnTheStep NamesOnTheStep.IssuingControls
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.Composition
  (unionOf)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Equivalence (Rule Reduces)

/-! ## Into every presentation with a parallel context rule -/

/-- **No uniform translation of the step with an absence-guarded program into any presentation with
a parallel context rule**, read modulo its equations, for every success term `ω`. -/
theorem no_uniformTranslation_presentation {base : BasePremiseEvaluator} {language : LanguageDef}
    {kind : CollType} (has : HasParallelContextRule kind language) (ω : Pattern) :
    IsEmpty (UniformTranslation source (presentationCalculus base language kind ω)) :=
  isEmpty_uniformTranslation source_switchable (presentationCalculus_persistent has ω)

/-- **Instance: rho's presentation.** -/
theorem no_uniformTranslation_rhoCalc (base : BasePremiseEvaluator) (ω : Pattern) :
    IsEmpty (UniformTranslation source (presentationCalculus base rhoCalc .hashBag ω)) :=
  no_uniformTranslation_presentation rhoCalc_hasParallelContextRule ω

/-! ## Into the reduction of every rho rule set -/

section Rho

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open RhoSchema RhoQuotationClassFibres

variable {Index : Type*} (rules : Index → RhoScopedParallelEvents.ProcessRule)
  (admitted : Index → Prop) (context : Ctx sig)

/-- **The reduction of a rho rule set as a calculus with a parallel composition**: rho processes
modulo structural congruence, the rule set's reduction, parallel composition, and success "`c` is a
parallel component". -/
def rhoCalculus (c : Process context) : ParallelCalculus where
  Term := Process context
  step := RhoScopedParallelEvents.Step (rules := rules) (admitted := admitted)
  par := join
  composable _ _ := True
  success := Composition.Component c
  same := Eq

/-- The reduction of every rho rule set is closed beside. -/
theorem rho_closedBeside :
    ClosedBeside (RhoScopedParallelEvents.Step (rules := rules) (admitted := admitted)
      (context := context)) join :=
  fun _ _ u step => RhoScopedParallelEvents.step_join step u

/-- **The reduction of every rho rule set is persistent**: closed beside, and a parallel component
of `P` is a parallel component of `P` beside anything. -/
theorem rhoCalculus_persistent (c : Process context) :
    (rhoCalculus rules admitted context c).Persistent where
  closed := rho_closedBeside rules admitted context
  persists := by
    rintro P u ⟨rest, rfl⟩
    exact ⟨join rest u, RhoScopedParallelPathReadout.join_assoc c rest u⟩
  respects := ParallelCalculus.respects_of_eq fun _ _ same => same

/-- **No uniform translation of the step with an absence-guarded program into the reduction of any
rho rule set**, for every success component `c`. -/
theorem no_uniformTranslation_rho (c : Process context) :
    IsEmpty (UniformTranslation source (rhoCalculus rules admitted context c)) :=
  isEmpty_uniformTranslation source_switchable (rhoCalculus_persistent rules admitted context c)

/-- **`rho_step_not_join_sensitive`, as an instance of the general relation-level theorem.** -/
theorem rho_step_not_join_sensitive_instance {R : Process context → Process context → Prop}
    {first second extra : Process context} (holds : R first second)
    (switchedOff : ¬ R (join first extra) (join second extra)) :
    ¬ ∀ x y, RhoScopedParallelEvents.Step (rules := rules) (admitted := admitted) x y ↔ R x y :=
  not_iff_of_switchedOff (rho_closedBeside rules admitted context)
    ⟨first, second, extra, holds, switchedOff⟩

end Rho

/-! ## Into every calculus of positive bag rules -/

/-- **A calculus of bag rules**: bags of ground terms, the rules' reduction, the sum of bags, and
success "a `T` is present". -/
def bagCalculus (Γ : Rule Expr → Prop) : ParallelCalculus where
  Term := Multiset Expr
  step := Reduces Γ
  par := (· + ·)
  composable _ _ := True
  success M := factT ∈ M
  same := Eq

/-- **Positive bag rules are persistent.** -/
theorem bagCalculus_persistent {Γ : Rule Expr → Prop} (positive : ∀ ρ, Γ ρ → ρ.Positive) :
    (bagCalculus Γ).Persistent where
  closed := fun _ _ u step =>
    Mettapedia.GSLT.Coordination.ConsensusNumbers.positive_reduces_frame positive step u
  persists := fun _ _ present => Multiset.mem_add.mpr (Or.inl present)
  respects := ParallelCalculus.respects_of_eq fun _ _ same => same

/-- **No uniform translation of the step with an absence-guarded program into positive bag
rules.** -/
theorem no_uniformTranslation_bag {Γ : Rule Expr → Prop} (positive : ∀ ρ, Γ ρ → ρ.Positive) :
    IsEmpty (UniformTranslation source (bagCalculus Γ)) :=
  isEmpty_uniformTranslation source_switchable (bagCalculus_persistent positive)

/-! ## The existing theorems as instances -/

section Existing

variable {A : Type*}

open StoreComposition

/-- `FrameClosed` is closure beside, at the sum of multisets. -/
theorem frameClosed_iff (R : Multiset A → Multiset A → Prop) :
    Composition.FrameClosed R ↔ ClosedBeside R (· + ·) := Iff.rfl

/-- `ParClosed` is closure beside, at the parallel composition of terms. -/
theorem parClosed_iff (R : Term A → Term A → Prop) :
    Composition.ParClosed R ↔ ClosedBeside R Term.join := Iff.rfl

/-- **`no_reaction_is_absence`, as an instance**: the absence step is switched off beside `c`. -/
theorem absentStep_switchedOff (c a : A) :
    SwitchedOffBeside (Composition.AbsentStep c a) (· + ·) :=
  ⟨0, {a}, {c}, ⟨Multiset.notMem_zero c, (Multiset.zero_add _).symm⟩, fun step => step.1 (by simp)⟩

theorem no_reaction_is_absence_instance (c a : A) (react : Reaction A) :
    ¬ ∀ before after, StoreStep react before after ↔ Composition.AbsentStep c a before after :=
  not_iff_of_switchedOff (Composition.storeStep_frameClosed react) (absentStep_switchedOff c a)

end Existing

/-! ## The hypotheses are needed -/

namespace Controls

/-- The rows of a configuration, as a bag. -/
def rows (C : Conf) : Multiset Expr := C.present.val.map Prod.fst

/-- **The bag of rows is homomorphic**: on disjoint stores, the rows of the union are the sum. -/
theorem rows_unionOf {C D : Conf} (disjoint : Disjoint C.present D.present) :
    rows (unionOf C D) = rows C + rows D := by
  change (C.present ∪ D.present).val.map Prod.fst = _
  rw [← Finset.disjUnion_eq_union _ _ disjoint]
  exact Multiset.map_add _ _ _

/-- Rows are present exactly when an occurrence carries them. -/
theorem mem_rows {C : Conf} {e : Expr} : e ∈ rows C ↔ ∃ o ∈ C.present, o.1 = e := by
  simp [rows]

/-- A bag of rules with no rule never moves: reachable success is success now. -/
theorem inert_succeeds_iff (M : Multiset Expr) :
    (bagCalculus fun _ => False).Succeeds M ↔ factT ∈ M := by
  constructor
  · rintro ⟨M', run, present⟩
    rcases Relation.ReflTransGen.cases_head run with rfl | ⟨_, ⟨_, never, _⟩, _⟩
    · exact present
    · exact never.elim
  · intro present
    exact ParallelCalculus.succeeds_of_success _ present

/-- The rule that makes `T` from nothing. -/
def makeT : Rule Expr := ⟨0, 0, {factT}, fun _ => false⟩

/-- In the calculus of `makeT`, every bag succeeds. -/
theorem maker_succeeds (M : Multiset Expr) : (bagCalculus (· = makeT)).Succeeds M :=
  ⟨makeT.result M, .single ⟨makeT, rfl, ⟨by simp [Rule.redex, makeT], fun _ _ => rfl⟩, rfl⟩,
    by simp [bagCalculus, Rule.result, makeT]⟩

/-- **Homomorphic and preserving, not reflecting.** The bag of rows into the calculus of `makeT`
(positive, so persistent) is homomorphic on composable configurations and preserves reachable
success; it does not reflect it at the empty store beside the store holding `U`. -/
theorem rows_into_maker :
    (bagCalculus (· = makeT)).Persistent ∧
      (∀ s s', source.composable s s' → rows (source.par s s') = rows s + rows s') ∧
      (∀ s, source.Succeeds s → (bagCalculus (· = makeT)).Succeeds (rows s)) ∧
      ¬ ∀ s, (bagCalculus (· = makeT)).Succeeds (rows s) → source.Succeeds s :=
  ⟨bagCalculus_persistent (fun ρ isMake x => by rw [isMake]; rfl),
    fun _ _ composable => rows_unionOf composable.1,
    fun s _ => maker_succeeds (rows s),
    fun reflects => beside_blocked (reflects _ (maker_succeeds _))⟩

/-- **Homomorphic and reflecting, not preserving.** The bag of rows into the calculus with no rule
(persistent) is homomorphic and reflects reachable success; it does not preserve it at the empty
store, where `spawn` makes `T`. -/
theorem rows_into_inert :
    (bagCalculus fun _ => False).Persistent ∧
      (∀ s s', source.composable s s' → rows (source.par s s') = rows s + rows s') ∧
      (∀ s, (bagCalculus fun _ => False).Succeeds (rows s) → source.Succeeds s) ∧
      ¬ ∀ s, source.Succeeds s → (bagCalculus fun _ => False).Succeeds (rows s) := by
  refine ⟨bagCalculus_persistent (fun _ never => never.elim),
    fun _ _ composable => rows_unionOf composable.1, fun s succeeds => ?_, fun preserves => ?_⟩
  · obtain ⟨o, present, isT⟩ := mem_rows.mp ((inert_succeeds_iff _).mp succeeds)
    exact ParallelCalculus.succeeds_of_success _ ⟨o, present, isT⟩
  · have shows := (inert_succeeds_iff _).mp (preserves alone alone_succeeds)
    simp [rows, alone, Separations.emptyS] at shows

/-- **The characteristic function of reachable success**, as a bag: `T` when the configuration can
succeed, nothing otherwise. It is a classical case on success, not a map built from the
configuration's rows. -/
noncomputable def owner (C : Conf) : Multiset Expr := by
  classical
  exact if source.Succeeds C then {factT} else 0

/-- **Preserving and reflecting, not homomorphic.** The characteristic function of success (`owner`),
into the calculus with no rule (persistent), preserves and reflects reachable success by its
definition, and is not homomorphic on parallel composition: the union of the empty store and the
store holding `U` goes to nothing, while the empty store alone goes to `T`. -/
theorem owner_translation :
    (bagCalculus fun _ => False).Persistent ∧
      (∀ s, source.Succeeds s → (bagCalculus fun _ => False).Succeeds (owner s)) ∧
      (∀ s, (bagCalculus fun _ => False).Succeeds (owner s) → source.Succeeds s) ∧
      ¬ ∀ s s', source.composable s s' → owner (source.par s s') = owner s + owner s' := by
  classical
  refine ⟨bagCalculus_persistent (fun _ never => never.elim), fun s succeeds => ?_,
    fun s shows => ?_, fun homomorphic => ?_⟩
  · apply (inert_succeeds_iff _).mpr
    simp [owner, succeeds]
  · by_contra failing
    have shown := (inert_succeeds_iff _).mp shows
    simp [owner, failing] at shown
  · have split := homomorphic alone blocker alone_blocker_composable
    have composite : owner (unionOf alone blocker) = 0 := by
      simp [owner, beside_blocked]
    have part : owner alone = {factT} := by
      simp [owner, alone_succeeds]
    change owner (unionOf alone blocker) = owner alone + owner blocker at split
    rw [composite, part] at split
    have present : factT ∈ ({factT} + owner blocker : Multiset Expr) := by simp
    rw [← split] at present
    simp at present

/-- **The target property is needed**: the identity is a uniform translation of the source into
itself, and the source is not persistent. -/
def identity_into_source : UniformTranslation source source where
  map := id
  homomorphic _ _ _ := rfl
  preserves _ succeeds := succeeds
  reflects _ succeeds := succeeds

theorem source_not_persistent : ¬ source.Persistent := fun persistent =>
  persistent.not_switchable source_switchable

section RhoControl

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open RhoSchema RhoQuotationClassFibres

/-- In a rho rule set that admits no rule, the null process never shows the output process. -/
theorem zero_never_visible {Index : Type*} (rules : Index → RhoScopedParallelEvents.ProcessRule) :
    ¬ (rhoCalculus rules (fun _ => False) [] visible).Succeeds (zero []) := by
  rintro ⟨P, run, component⟩
  rcases Relation.ReflTransGen.cases_head run with rfl | ⟨_, step, _⟩
  · exact Composition.not_component_zero visible Composition.visible_nonnull component
  · obtain ⟨root, _, _, _⟩ := (RhoScopedParallelEvents.step_iff_root_surrounding _ _).mp step
    exact root.1.2

/-- **Homomorphic and reflecting, not preserving, on rho processes.** The constant null process is
homomorphic on parallel composition (the null process is its unit) and reflects reachable success
(it never shows the output process), and it does not preserve success at the empty store. -/
theorem zero_into_rho {Index : Type*} (rules : Index → RhoScopedParallelEvents.ProcessRule) :
    (rhoCalculus rules (fun _ => False) [] visible).Persistent ∧
      (∀ s s', source.composable s s' → zero [] = join (zero []) (zero [])) ∧
      (∀ s : Conf, (rhoCalculus rules (fun _ => False) [] visible).Succeeds (zero []) →
        source.Succeeds s) ∧
      ¬ ∀ s : Conf, source.Succeeds s →
        (rhoCalculus rules (fun _ => False) [] visible).Succeeds (zero []) :=
  ⟨rhoCalculus_persistent rules _ [] visible, fun _ _ _ => (join_zero_right (zero [])).symm,
    fun _ shows => (zero_never_visible rules shows).elim,
    fun preserves => zero_never_visible rules (preserves alone alone_succeeds)⟩

end RhoControl

end Controls

#print axioms no_uniformTranslation_presentation
#print axioms no_uniformTranslation_rhoCalc
#print axioms rho_closedBeside
#print axioms rhoCalculus_persistent
#print axioms no_uniformTranslation_rho
#print axioms rho_step_not_join_sensitive_instance
#print axioms bagCalculus_persistent
#print axioms no_uniformTranslation_bag
#print axioms no_reaction_is_absence_instance
#print axioms Controls.rows_unionOf
#print axioms Controls.rows_into_maker
#print axioms Controls.rows_into_inert
#print axioms Controls.owner_translation
#print axioms Controls.source_not_persistent
#print axioms Controls.zero_into_rho

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.ParallelClosed
