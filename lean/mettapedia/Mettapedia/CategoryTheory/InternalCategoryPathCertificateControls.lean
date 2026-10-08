import Mettapedia.CategoryTheory.InternalCategoryPathUniversal
import Mettapedia.CategoryTheory.CertificateActionCategory
import Mathlib.Algebra.FreeMonoid.Basic

/-!
# Nonconstant current-state certificates along complete retained paths

The state-indexed family Fin (n + 1) changes with the current endpoint.
Individual events have an independently authored action on that family and
a free-word occurrence receipt. The future adds a new zero branch to every
certificate function and moves all old branches, preserving whole functions.
The free-path extension earns the resulting path action, including the
complete future square. Endpoint equality cannot recover its receipt.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.InternalCategoryPathCertificateControls

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open InternalCategoryPathDiagram

abbrev family (state : Nat) := Fin (state + 1)
abbrev Evidence := CertificateActionCategory.Objects family (FreeMonoid Nat)

/-- The uppermost certificate moves; all earlier branches remain distinct. -/
def grow : (state : Nat) → family state → family (state + 1)
  | 0, _ => 1
  | state + 1, certificate => Fin.cases 0 (fun old => (grow state old).succ) certificate

def eventAction (origin state : Nat) :
    (show Evidence from state) ⟶ (show Evidence from state + 1) :=
  ⟨FreeMonoid.of origin, grow state⟩

/-- Whole function transport includes the independently new zero branch. -/
def successor : Evidence ⥤ Evidence where
  obj state := (show Nat from state) + 1
  map action := ⟨action.1, Fin.cases 0 (fun old => (action.2 old).succ)⟩
  map_id state := by
    apply Prod.ext
    · rfl
    · funext certificate
      cases certificate using Fin.cases <;> rfl
  map_comp before after := by
    apply Prod.ext
    · rfl
    · funext certificate
      cases certificate using Fin.cases <;> rfl

abbrev Stage := WalkingParallelPair

def vertices : Stage ⥤ Type where
  obj _ := Nat
  map change := match change with
    | .id _ => 𝟙 _
    | .left => TypeCat.ofHom Nat.succ
    | .right => TypeCat.ofHom Nat.succ
  map_id _ := rfl
  map_comp before after := by cases before <;> cases after <;> rfl

def events : Stage ⥤ Type where
  obj _ := Nat × Nat
  map change := match change with
    | .id _ => 𝟙 _
    | .left => TypeCat.ofHom (fun supplied => (supplied.1, supplied.2 + 1))
    | .right => TypeCat.ofHom (fun supplied => (supplied.1, supplied.2 + 1))
  map_id _ := rfl
  map_comp before after := by cases before <;> cases after <;> rfl

def source : events ⟶ vertices where
  app _ := TypeCat.ofHom Prod.snd
  naturality _ _ change := by cases change <;> rfl

def target : events ⟶ vertices where
  app _ := TypeCat.ofHom (fun supplied => supplied.2 + 1)
  naturality _ _ change := by cases change <;> rfl

def graph : InternalGraph (Stage ⥤ Type) := ⟨vertices, events, source, target⟩

abbrev evidenceDiagram : Stage ⥤ Cat.{0,0} where
  obj _ := Cat.of Evidence
  map change := match change with
    | .id _ => 𝟙 _
    | .left => successor.toCatHom
    | .right => successor.toCatHom
  map_id _ := rfl
  map_comp before after := by cases before <;> cases after <;> rfl

def eventsAt (context : Stage) : Vertex graph context ⥤q (evidenceDiagram.obj context) where
  obj state := state
  map {first last} supplied := by
    obtain ⟨⟨origin, state⟩, firstRead, lastRead⟩ := supplied
    change state = first at firstRead
    change state + 1 = last at lastRead
    subst first
    subst last
    exact eventAction origin state

theorem eventsAt_read (context : Stage) (origin state : Nat) :
    (eventsAt context).map (⟨(origin, state), rfl, rfl⟩ :
      (show Vertex graph context from state) ⟶ (show Vertex graph context from state + 1)) =
        eventAction origin state := rfl

theorem futureSquare :
    restriction graph WalkingParallelPairHom.left ⋙q eventsAt .one =
      eventsAt .zero ⋙q successor.toPrefunctor := by
  refine Prefunctor.ext' (fun _ => rfl) ?_
  intro first last supplied
  obtain ⟨⟨origin, state⟩, firstRead, lastRead⟩ := supplied
  change state = first at firstRead
  change state + 1 = last at lastRead
  subst first
  subst last
  have reading :
      (restriction graph WalkingParallelPairHom.left).map
          (⟨(origin, state), rfl, rfl⟩ :
            (show Vertex graph .zero from state) ⟶ (show Vertex graph .zero from state + 1)) =
        (⟨(origin, state + 1), rfl, rfl⟩ :
          (show Vertex graph .one from state + 1) ⟶ (show Vertex graph .one from state + 2)) := by
    apply Subtype.ext
    rfl
  change (eventsAt .one).map ((restriction graph WalkingParallelPairHom.left).map
      (⟨(origin, state), rfl, rfl⟩ :
        (show Vertex graph .zero from state) ⟶ (show Vertex graph .zero from state + 1))) =
    Quiver.homOfEq (successor.map ((eventsAt .zero).map
      (⟨(origin, state), rfl, rfl⟩ :
        (show Vertex graph .zero from state) ⟶ (show Vertex graph .zero from state + 1)))) rfl rfl
  rw [reading, eventsAt_read, eventsAt_read, Quiver.homOfEq_rfl]
  rfl

def eventInterpretation : quiverDiagram graph ⟶ evidenceDiagram ⋙ Quiv.forget where
  app := eventsAt
  naturality context _ change := by
    cases change with
    | left => exact futureSquare
    | right => exact futureSquare
    | id =>
      change restriction graph (𝟙 context) ⋙q eventsAt context =
        eventsAt context ⋙q Prefunctor.id _
      rw [restriction_id, Prefunctor.id_comp, Prefunctor.comp_id]

abbrev pathAction := InternalCategoryPathUniversal.internalFunctor graph evidenceDiagram eventInterpretation

theorem event_read (origin state : Nat) :
    pathAction.edge.app .zero (edge graph .zero (origin, state)) =
      (⟨state, state + 1, eventAction origin state⟩ :
        InternalCategoryDiagram.Arrow (evidenceDiagram.obj .zero)) := by
  rw [InternalCategoryPathUniversal.complete_event]
  change (⟨state, state + 1, (eventsAt .zero).map
    (⟨(origin, state), rfl, rfl⟩ :
      (show Vertex graph .zero from state) ⟶ (show Vertex graph .zero from state + 1))⟩ :
    InternalCategoryDiagram.Arrow (evidenceDiagram.obj .zero)) = _
  rw [eventsAt_read]

def first : InternalCategoryDiagram.Arrow ((diagram graph).obj .zero) := edge graph .zero (7, 0)
def second : InternalCategoryDiagram.Arrow ((diagram graph).obj .zero) := edge graph .zero (9, 1)
def both : InternalCategoryDiagram.Arrow ((diagram graph).obj .zero) :=
  InternalCategoryDiagram.Arrow.compose first second rfl

def interpretedBoth : InternalCategoryDiagram.Arrow (evidenceDiagram.obj .zero) :=
  pathAction.edge.app .zero both

theorem complete_both_read :
    interpretedBoth = (⟨(show Evidence from (0 : Nat)), (show Evidence from (2 : Nat)),
      eventAction 7 0 ≫ eventAction 9 1⟩ :
      InternalCategoryDiagram.Arrow (evidenceDiagram.obj .zero)) := by
  unfold interpretedBoth both
  rw [InternalCategoryPathUniversal.complete_composition]
  exact (InternalCategoryDiagram.Arrow.compose_congr
    (event_read 7 0) (event_read 9 1) _ rfl).trans (by
      dsimp only [InternalCategoryDiagram.Arrow.compose]
      rw [eqToHom_refl, Category.id_comp]
      rfl)

theorem complete_both_action :
    interpretedBoth.2.2 = eventAction 7 0 ≫ eventAction 9 1 := by
  have pairRead := (Sigma.mk.inj complete_both_read).2
  have arrowRead := (Sigma.mk.inj (eq_of_heq pairRead)).2
  exact eq_of_heq arrowRead

theorem supplied_certificate_changes_to_the_current_type :
    interpretedBoth.2.2.2 (0 : Fin 1) = (2 : Fin 3) := by
  rw [complete_both_action]
  rfl

theorem the_complete_receipt_records_both_occurrences :
    FreeMonoid.toList interpretedBoth.2.2.1 = [7, 9] := by
  rw [complete_both_action]
  rfl

def futureBoth : InternalCategoryDiagram.Arrow ((diagram graph).obj .one) :=
  (category graph).edge.map WalkingParallelPairHom.left both

def interpretedFuture : InternalCategoryDiagram.Arrow (evidenceDiagram.obj .one) :=
  pathAction.edge.app .one futureBoth

theorem future_keeps_the_complete_certificate_action :
    interpretedFuture = InternalCategoryDiagram.Arrow.map successor interpretedBoth :=
  (InternalCategoryPathUniversal.complete_future graph evidenceDiagram eventInterpretation
    WalkingParallelPairHom.left both).symm

theorem complete_future_action :
    interpretedFuture.2.2 = successor.map interpretedBoth.2.2 := by
  have pairRead := (Sigma.mk.inj future_keeps_the_complete_certificate_action).2
  have arrowRead := (Sigma.mk.inj (eq_of_heq pairRead)).2
  exact eq_of_heq arrowRead

theorem the_future_old_branch_is_updated :
    interpretedFuture.2.2.2 (1 : Fin 2) = (3 : Fin 4) := by
  rw [complete_future_action, complete_both_action]
  rfl

theorem the_future_new_branch_is_retained :
    interpretedFuture.2.2.2 (0 : Fin 2) = (0 : Fin 4) := by
  rw [complete_future_action, complete_both_action]
  rfl

theorem a_constant_certificate_replacement_is_rejected :
    interpretedFuture.2.2.2 (0 : Fin 2) ≠ interpretedFuture.2.2.2 (1 : Fin 2) := by
  rw [the_future_new_branch_is_retained, the_future_old_branch_is_updated]
  decide

theorem future_keeps_both_occurrences :
    FreeMonoid.toList interpretedFuture.2.2.1 = [7, 9] := by
  rw [complete_future_action, complete_both_action]
  rfl

def receiptRead (path : InternalCategoryDiagram.Arrow ((diagram graph).obj .zero)) : List Nat :=
  FreeMonoid.toList (pathAction.edge.app .zero path).2.2.1

theorem same_endpoints_cannot_recover_actual_receipts :
    ¬ ∃ decode : Nat × Nat → List Nat,
      ∀ path : InternalCategoryDiagram.Arrow ((diagram graph).obj .zero),
        decode (path.1, path.2.1) = receiptRead path := by
  rintro ⟨decode, correct⟩
  have seven := correct (edge graph .zero (7, 0))
  have eight := correct (edge graph .zero (8, 0))
  have clash := seven.symm.trans eight
  unfold receiptRead at clash
  rw [event_read, event_read] at clash
  change ([7] : List Nat) = [8] at clash
  cases clash

end Mettapedia.CategoryTheory.InternalCategoryPathCertificateControls
