import Mettapedia.OSLF.Syntax.IntrinsicScopedConditionalModelPresheaf
import Mathlib.CategoryTheory.PathCategory.Basic

/-!
# Finite histories of a contextual substitution-operational model

At each context and sort, the model's actual evidence values are edges of
a quiver. Free paths retain the ordered occurrences. Model morphisms and
contextual substitutions act on those paths by their prescribed actions
on individual events. No image predicate is used in this construction.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.IntrinsicScopedConditionalModelHistory

open _root_.CategoryTheory
open Mettapedia.OSLF.Binding.BindingSubstitutionAlgebra
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalSubstitution
open Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial (Judgment)
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalPolynomial

universe u
universe uV uW uT vV vW vT
variable {S : Signature} {M : List (MetaArity S)}
variable (R : List (Rule S M))

/-- Extend a quiver map to its free finite-path categories. -/
def liftQuiverMap {V : Type uV} [Quiver.{vV} V]
    {W : Type uW} [Quiver.{vW} W]
    (f : V ⥤q W) : Paths V ⥤ Paths W :=
  Paths.lift (f ⋙q Paths.of W)

/-- Free-path extension preserves composition of generator maps. -/
theorem liftQuiverMap_comp
    {V : Type uV} [Quiver.{vV} V]
    {W : Type uW} [Quiver.{vW} W]
    {T : Type uT} [Quiver.{vT} T]
    (f : V ⥤q W) (g : W ⥤q T) :
    liftQuiverMap (f ⋙q g) = liftQuiverMap f ⋙ liftQuiverMap g := by
  symm
  apply Paths.lift_unique
  fapply Prefunctor.ext
  · intro state
    rfl
  · intro source target event
    rfl

/-- One program state of a fixed sort in a contextual operational model. -/
@[ext]
structure State {A : BindingCloneAlgebra.Algebra.{u} S}
    (Y : SubstitutionModel R A) (Γ : Ctx S) (sort : S.Srt) where
  term : A.substitution.Carrier Γ sort

/-- A quiver edge is an individual model event at precisely these endpoints. -/
instance modelQuiver {A : BindingCloneAlgebra.Algebra.{u} S}
    (Y : SubstitutionModel R A) (Γ : Ctx S) (sort : S.Srt) :
    Quiver (State R Y Γ sort) where
  Hom source target :=
    Y.evidence.carrier ()
      (⟨Γ, sort, (source.term, target.term)⟩ : Judgment A)

/-- Free finite histories of retained firing occurrences. -/
abbrev HistoryCategory {A : BindingCloneAlgebra.Algebra.{u} S}
    (Y : SubstitutionModel R A) (Γ : Ctx S) (sort : S.Srt) :=
  Paths (State R Y Γ sort)

/-- A model interpretation maps the endpoints and the individual evidence
of every generating event. -/
def mapGenerators {A : BindingCloneAlgebra.Algebra.{u} S}
    {Y Z : SubstitutionModel R A}
    (h : SubstitutionModel.Hom R Y Z) (Γ : Ctx S) (sort : S.Srt) :
    State R Y Γ sort ⥤q State R Z Γ sort where
  obj state := ⟨state.term⟩
  map {source target} event :=
    h.evidence.toFun ()
      (⟨Γ, sort, (source.term, target.term)⟩ : Judgment A) event

/-- An interpretation of one-step evidence extends uniquely to ordered
finite histories, preserving identity and concatenation. -/
def mapHistories {A : BindingCloneAlgebra.Algebra.{u} S}
    {Y Z : SubstitutionModel R A}
    (h : SubstitutionModel.Hom R Y Z) (Γ : Ctx S) (sort : S.Srt) :
    HistoryCategory R Y Γ sort ⥤ HistoryCategory R Z Γ sort :=
  liftQuiverMap (mapGenerators R h Γ sort)

/-- On a singleton history, the functor gives exactly the model's own
map of the generating event. -/
theorem mapHistories_generator {A : BindingCloneAlgebra.Algebra.{u} S}
    {Y Z : SubstitutionModel R A}
    (h : SubstitutionModel.Hom R Y Z) (Γ : Ctx S) (sort : S.Srt)
    {source target : State R Y Γ sort} (event : source ⟶ target) :
    (mapHistories R h Γ sort).map event.toPath =
      Quiver.Hom.toPath ((mapGenerators R h Γ sort).map event) :=
  Paths.lift_toPath _ event

/-- Identity model interpretation acts identically on every finite
event history. -/
theorem mapHistories_id {A : BindingCloneAlgebra.Algebra.{u} S}
    (Y : SubstitutionModel R A) (Γ : Ctx S) (sort : S.Srt) :
    mapHistories R (SubstitutionModel.Hom.id Y) Γ sort =
      𝟭 (HistoryCategory R Y Γ sort) := by
  symm
  apply Paths.lift_unique
  fapply Prefunctor.ext
  · intro state
    rfl
  · intro source target event
    rfl

/-- Interpreting histories through two model morphisms is the same as
interpreting them through their composite. -/
theorem mapHistories_comp {A : BindingCloneAlgebra.Algebra.{u} S}
    {X Y Z : SubstitutionModel R A}
    (first : SubstitutionModel.Hom R X Y)
    (later : SubstitutionModel.Hom R Y Z)
    (Γ : Ctx S) (sort : S.Srt) :
    mapHistories R (SubstitutionModel.Hom.comp first later) Γ sort =
      mapHistories R first Γ sort ⋙ mapHistories R later Γ sort := by
  symm
  apply Paths.lift_unique
  fapply Prefunctor.ext
  · intro state
    rfl
  · intro source target event
    rfl

/-- A map between full authored interpretations changes the binding-equation
base as well as the evidence. It therefore acts on the contextual vertices
and every retained edge of a finite history. -/
def relativeMapGenerators {E : List (EqAxiom S M)}
    {X Y : SubstitutionOperationalModel R E}
    (h : SubstitutionOperationalModel.Hom (R := R) X Y)
    (Γ : Ctx S) (sort : S.Srt) :
    State R X.model Γ sort ⥤q State R Y.model Γ sort where
  obj state := ⟨h.base.raw.map state.term⟩
  map {source target} event :=
    h.evidence.toFun ()
      (⟨Γ, sort, (source.term, target.term)⟩ : Judgment X.base.algebra)
      event

/-- The full interpretation map extends to all finite event histories,
retaining ordered firings even as authored equations identify states. -/
def relativeMapHistories {E : List (EqAxiom S M)}
    {X Y : SubstitutionOperationalModel R E}
    (h : SubstitutionOperationalModel.Hom (R := R) X Y)
    (Γ : Ctx S) (sort : S.Srt) :
    HistoryCategory R X.model Γ sort ⥤
      HistoryCategory R Y.model Γ sort :=
  liftQuiverMap (relativeMapGenerators R h Γ sort)

/-- On a one-step path, the full interpretation uses exactly the
evidence map of the authored operational-model morphism. -/
theorem relativeMapHistories_generator {E : List (EqAxiom S M)}
    {X Y : SubstitutionOperationalModel R E}
    (h : SubstitutionOperationalModel.Hom (R := R) X Y)
    (Γ : Ctx S) (sort : S.Srt)
    {source target : State R X.model Γ sort}
    (event : source ⟶ target) :
    (relativeMapHistories R h Γ sort).map event.toPath =
      Quiver.Hom.toPath ((relativeMapGenerators R h Γ sort).map event) :=
  Paths.lift_toPath _ event

/-- Identity of a full authored interpretation acts identically on its
histories. -/
theorem relativeMapHistories_id {E : List (EqAxiom S M)}
    (X : SubstitutionOperationalModel R E)
    (Γ : Ctx S) (sort : S.Srt) :
    relativeMapHistories R (SubstitutionOperationalModel.Hom.id X)
      Γ sort = 𝟭 (HistoryCategory R X.model Γ sort) := by
  symm
  apply Paths.lift_unique
  fapply Prefunctor.ext
  · intro state
    rfl
  · intro source target event
    rfl

/-- Composition of full authored interpretations composes their history
functors, including the program-state and evidence components. -/
theorem relativeMapHistories_comp {E : List (EqAxiom S M)}
    {X Y Z : SubstitutionOperationalModel R E}
    (first : SubstitutionOperationalModel.Hom (R := R) X Y)
    (later : SubstitutionOperationalModel.Hom (R := R) Y Z)
    (Γ : Ctx S) (sort : S.Srt) :
    relativeMapHistories R
      (SubstitutionOperationalModel.Hom.comp first later) Γ sort =
      relativeMapHistories R first Γ sort ⋙
        relativeMapHistories R later Γ sort := by
  symm
  apply Paths.lift_unique
  fapply Prefunctor.ext
  · intro state
    rfl
  · intro source target event
    rfl

/-- The model's contextual substitution action is a map of its event
quivers, including their source and target terms. -/
def substituteGenerators {A : BindingCloneAlgebra.Algebra.{u} S}
    (Y : SubstitutionModel R A) {Γ Δ : Ctx S}
    (σ : Environment S A.substitution.Carrier Γ Δ) (sort : S.Srt) :
    State R Y Γ sort ⥤q State R Y Δ sort where
  obj state := ⟨A.substitution.substitute σ state.term⟩
  map {source target} event :=
    Y.act (⟨Γ, sort, (source.term, target.term)⟩ : Judgment A)
      event σ
      (⟨Δ, sort,
        (A.substitution.substitute σ source.term,
          A.substitution.substitute σ target.term)⟩ : Judgment A) rfl

/-- Substituting a context throughout an event history retains its ordered
individual firings. -/
def substituteHistories {A : BindingCloneAlgebra.Algebra.{u} S}
    (Y : SubstitutionModel R A) {Γ Δ : Ctx S}
    (σ : Environment S A.substitution.Carrier Γ Δ) (sort : S.Srt) :
    HistoryCategory R Y Γ sort ⥤ HistoryCategory R Y Δ sort :=
  liftQuiverMap (substituteGenerators R Y σ sort)

/-- Substitution of a one-event history uses the model's stipulated action
on the same individual evidence value. -/
theorem substituteHistories_generator
    {A : BindingCloneAlgebra.Algebra.{u} S}
    (Y : SubstitutionModel R A) {Γ Δ : Ctx S}
    (σ : Environment S A.substitution.Carrier Γ Δ) (sort : S.Srt)
    {source target : State R Y Γ sort} (event : source ⟶ target) :
    (substituteHistories R Y σ sort).map event.toPath =
      Quiver.Hom.toPath ((substituteGenerators R Y σ sort).map event) :=
  Paths.lift_toPath _ event

/-- Interpreting an event and then substituting agrees with substituting
its source evidence and then interpreting it, at every generating edge. -/
theorem mapGenerators_substitute
    {A : BindingCloneAlgebra.Algebra.{u} S}
    {Y Z : SubstitutionModel R A}
    (h : SubstitutionModel.Hom R Y Z)
    {Γ Δ : Ctx S}
    (σ : Environment S A.substitution.Carrier Γ Δ) (sort : S.Srt) :
    mapGenerators R h Γ sort ⋙q substituteGenerators R Z σ sort =
      substituteGenerators R Y σ sort ⋙q mapGenerators R h Δ sort := by
  fapply Prefunctor.ext
  · intro state
    rfl
  · intro source target event
    exact (h.preserves
      (⟨Γ, sort, (source.term, target.term)⟩ : Judgment A)
      event σ
      (⟨Δ, sort,
        (A.substitution.substitute σ source.term,
          A.substitution.substitute σ target.term)⟩ : Judgment A)
      rfl).symm

/-- Model interpretation and contextual substitution commute on every
finite history, including concatenated paths. -/
theorem mapHistories_substitute
    {A : BindingCloneAlgebra.Algebra.{u} S}
    {Y Z : SubstitutionModel R A}
    (h : SubstitutionModel.Hom R Y Z)
    {Γ Δ : Ctx S}
    (σ : Environment S A.substitution.Carrier Γ Δ) (sort : S.Srt) :
    mapHistories R h Γ sort ⋙ substituteHistories R Z σ sort =
      substituteHistories R Y σ sort ⋙ mapHistories R h Δ sort := by
  calc
    mapHistories R h Γ sort ⋙ substituteHistories R Z σ sort =
        liftQuiverMap
          (mapGenerators R h Γ sort ⋙q substituteGenerators R Z σ sort) :=
      (liftQuiverMap_comp _ _).symm
    _ = liftQuiverMap
          (substituteGenerators R Y σ sort ⋙q mapGenerators R h Δ sort) := by
      rw [mapGenerators_substitute]
    _ = substituteHistories R Y σ sort ⋙ mapHistories R h Δ sort :=
      liftQuiverMap_comp _ _

#print axioms mapHistories
#print axioms mapHistories_generator
#print axioms mapHistories_id
#print axioms mapHistories_comp
#print axioms relativeMapHistories
#print axioms relativeMapHistories_generator
#print axioms relativeMapHistories_id
#print axioms relativeMapHistories_comp
#print axioms substituteHistories
#print axioms substituteHistories_generator
#print axioms mapGenerators_substitute
#print axioms mapHistories_substitute

end Mettapedia.OSLF.Binding.IntrinsicScopedConditionalModelHistory
