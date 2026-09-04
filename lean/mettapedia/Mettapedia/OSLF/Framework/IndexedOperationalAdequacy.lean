import Mettapedia.GSLT.Logic.HennessyMilnerTransport
import Mettapedia.OSLF.Framework.HennessyMilnerNativeTypes
import Mettapedia.OSLF.Framework.GSLTQuotientCoherence

/-!
# Hennessy–Milner adequacy through the indexed operational language

The indexed operational language moves equation classes between fibres of a
diagram and returns them as commands.  This module routes its material
through the equation-aware Hennessy–Milner theory of the sole generated
OSLF.

* Every labeled system descends to the semantic theory of its GSLT, and the
  quotient map is a cover: formulas, logical equivalence, and bisimilarity
  are the same on authored terms and on their classes.
* Returning a fibre state as a command is a cover: the native types of a
  fibre are exactly the native types of its returned commands.
* An explicit transport request is a translation but not a cover.  Its
  transport step escapes the fibre, which is precisely why transport is
  visible control state rather than fibre behaviour.
* Along a covered stage map, every fibre formula is preserved and reflected;
  along a merely forward stage map, the negation-free formulas are
  preserved.  Native types therefore transport exactly along covered routes
  and laxly along forward routes, matching the exact and lax modal transport
  of the indexed modal functor at the level of formulas.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.IndexedOperationalAdequacy

open CategoryTheory
open Mettapedia.GSLT
open Mettapedia.GSLT.HennessyMilner
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.IndexedOperational.Command
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.OSLF.Framework.HennessyMilnerNativeTypes

universe uTerm uAtom uLabel uIndex vIndex uObservation

/-! ## Descent of a labeled system to the semantic theory -/

variable {S : GSLT.{uTerm}}

/-- The labeled system induced on equation classes. -/
def onSemantic (M : System.{uAtom, uLabel} S) : System.{uAtom, uLabel} (semanticTheory S) where
  Atom := M.Atom
  observes atom := Quotient.lift (M.observes atom)
    (fun _ _ equivalent => propext (M.observes_resp atom equivalent))
  observes_resp := by
    intro atom left right equal
    have equal : left = right := equal
    subst equal
    exact Iff.rfl
  Label := M.Label
  act label source target := ∃ redex contractum : S.Term,
    Quotient.mk S.equations redex = source ∧ Quotient.mk S.equations contractum = target ∧
      M.act label redex contractum
  act_resp_left := by
    intro label left right target equal step
    have equal : left = right := equal
    subst equal
    exact ⟨target, step, rfl⟩
  act_resp_right := by
    intro label source target target' step equal
    have equal : target = target' := equal
    subst equal
    exact step

/-- The quotient map is a cover of labeled systems. -/
def quotientCover (M : System.{uAtom, uLabel} S) : SystemCover M (onSemantic M) where
  mapTerm := Quotient.mk S.equations
  mapAtom := id
  mapLabel := id
  mapEquiv := fun equivalent => Quotient.sound equivalent
  observes_iff := fun _ _ => Iff.rfl
  mapAct := fun step => ⟨_, _, rfl, rfl, step⟩
  liftAct := by
    intro label source target' step
    obtain ⟨redex, contractum, redexClass, contractumClass, step⟩ := step
    obtain ⟨target, step', equivalent⟩ :=
      M.act_resp_left (Quotient.exact redexClass) step
    refine ⟨target, step', ?_⟩
    show Quotient.mk S.equations target = target'
    rw [← contractumClass]
    exact Quotient.sound (S.equations.iseqv.symm equivalent)

/-- Satisfaction on a class is satisfaction at any representative. -/
theorem sat_onSemantic_mk (M : System.{uAtom, uLabel} S) (formula : Formula M.Atom M.Label)
    (term : S.Term) :
    (onSemantic M).sat formula (Quotient.mk S.equations term) ↔ M.sat formula term := by
  have := (quotientCover M).sat_map formula term
  change (onSemantic M).sat (Formula.map id id formula) _ ↔ _ at this
  rwa [Formula.map_id] at this

/-- Bisimilarity of authored terms is bisimilarity of their classes. -/
theorem bisimilar_iff_onSemantic (M : System.{uAtom, uLabel} S) (left right : S.Term) :
    M.Bisimilar left right ↔
      (onSemantic M).Bisimilar (Quotient.mk S.equations left) (Quotient.mk S.equations right) :=
  ((quotientCover M).bisimilar_map_iff (fun atom => ⟨atom, rfl⟩) (fun label => ⟨label, rfl⟩)
    left right).symm

/-- The descended system's bisimilarity is the class-level bisimilarity of
the adequacy theorem. -/
theorem onSemantic_bisimilar_iff_bisimilarClass (M : System.{uAtom, uLabel} S)
    (left right : Quotient S.equations) :
    (onSemantic M).Bisimilar left right ↔ M.bisimilarClass left right := by
  induction left using Quotient.inductionOn with
  | _ left =>
  induction right using Quotient.inductionOn with
  | _ right =>
  rw [M.bisimilarClass_mk]
  exact (bisimilar_iff_onSemantic M left right).symm

/-- For the unlabeled step system the descended steps are the semantic
steps of the quotient GSLT. -/
theorem onSemantic_ofObserved_act_iff (observed : ObservedGSLT.{uAtom} S)
    (observes_resp : ∀ (atom : observed.Atom) {left right : S.Term},
      S.Equiv left right → (observed.observes atom left ↔ observed.observes atom right))
    (source target : SemanticTerm S) :
    (onSemantic (System.ofObserved observed observes_resp)).act () source target ↔
      SemanticStep S source target := by
  constructor
  · rintro ⟨redex, contractum, sourceClass, targetClass, step⟩
    exact ⟨redex, contractum, sourceClass, step, targetClass⟩
  · rintro ⟨redex, contractum, sourceClass, step, targetClass⟩
    exact ⟨redex, contractum, sourceClass, targetClass, step⟩

/-! ## Fibres and commands of an indexed diagram -/

variable {Index : Type uIndex} [CategoryTheory.Category.{vIndex} Index]

/-- The step system of one fibre, observed through a transport observer. -/
def fibreSystem (diagram : Diagram.{uTerm, uIndex, vIndex} Index)
    (observer : TransportObserver diagram) (stage : Index) :
    System (semanticTheory (diagram.obj stage).theory) :=
  System.ofObserved ⟨observer.Result, fun result state => observer.observe stage state = result⟩
    (by
      intro result left right equal
      have equal : left = right := equal
      subst equal
      exact Iff.rfl)

/-- The step system of the command machine, observed through the same
transport observer. -/
def commandSystem (diagram : Diagram.{uTerm, uIndex, vIndex} Index)
    (observer : TransportObserver diagram) :
    System (commandGSLT diagram) :=
  System.ofObserved
    ⟨observer.Result, fun result command => TransportObserver.observeCommand diagram observer command = result⟩
    (by
      intro result left right equal
      have equal : left = right := equal
      subst equal
      exact Iff.rfl)

/-- Returning a fibre state as a command is a cover. -/
def atCover (diagram : Diagram.{uTerm, uIndex, vIndex} Index)
    (observer : TransportObserver diagram) (stage : Index) :
    SystemCover (fibreSystem diagram observer stage) (commandSystem diagram observer) where
  mapTerm := Command.at stage
  mapAtom := id
  mapLabel := id
  mapEquiv := by
    intro left right equal
    have equal : left = right := equal
    subst equal
    rfl
  observes_iff := fun _ _ => Iff.rfl
  mapAct := fun step => ⟨.fibre step⟩
  liftAct := by
    intro _ source target' step
    obtain ⟨step⟩ := step
    cases step with
    | fibre step => exact ⟨_, step, rfl⟩

/-- A fibre formula holds at a returned command exactly when it holds at the
fibre state. -/
theorem at_sat_iff (diagram : Diagram.{uTerm, uIndex, vIndex} Index)
    (observer : TransportObserver diagram) (stage : Index)
    (formula : Formula observer.Result Unit)
    (state : SemanticTerm (diagram.obj stage).theory) :
    (commandSystem diagram observer).sat formula (.at stage state) ↔
      (fibreSystem diagram observer stage).sat formula state := by
  have := (atCover diagram observer stage).sat_map formula state
  change (commandSystem diagram observer).sat (Formula.map id id formula) _ ↔ _ at this
  rwa [Formula.map_id] at this

/-- Returned commands are bisimilar exactly when their fibre states are. -/
theorem at_bisimilar_iff (diagram : Diagram.{uTerm, uIndex, vIndex} Index)
    (observer : TransportObserver diagram) (stage : Index)
    (left right : SemanticTerm (diagram.obj stage).theory) :
    (commandSystem diagram observer).Bisimilar (.at stage left) (.at stage right) ↔
      (fibreSystem diagram observer stage).Bisimilar left right :=
  (atCover diagram observer stage).bisimilar_map_iff (fun atom => ⟨atom, rfl⟩)
    (fun label => ⟨label, rfl⟩) left right

/-- The native type a fibre formula generates on the command machine is
inhabited by a returned command exactly when the fibre's native type is
inhabited by the state. -/
theorem at_nativeType_iff (diagram : Diagram.{uTerm, uIndex, vIndex} Index)
    (observer : TransportObserver diagram) (stage : Index)
    (formula : Formula observer.Result Unit)
    (state : SemanticTerm (diagram.obj stage).theory) :
    (gsltOSLF (commandGSLT diagram)).satisfies (S := ()) (.at stage state)
        (formulaNativeType (commandSystem diagram observer) formula).pred ↔
      (gsltOSLF (semanticTheory (diagram.obj stage).theory)).satisfies (S := ()) state
        (formulaNativeType (fibreSystem diagram observer stage) formula).pred :=
  at_sat_iff diagram observer stage formula state

/-! ## Transport requests are translations, not covers -/

/-- Wrapping a fibre state in a transport request is a translation. -/
def viaTranslation (diagram : Diagram.{uTerm, uIndex, vIndex} Index)
    (observer : TransportObserver diagram) {source target : Index} (route : source ⟶ target) :
    SystemTranslation (fibreSystem diagram observer source) (commandSystem diagram observer) where
  mapTerm := Command.via route
  mapAtom := id
  mapLabel := id
  mapEquiv := by
    intro left right equal
    have equal : left = right := equal
    subst equal
    rfl
  observes_iff := fun _ _ => Iff.rfl
  mapAct := fun step => ⟨.underVia route step⟩

/-- No cover wraps fibre states in a transport request: the transport step
leaves the image of the fibre. -/
theorem via_not_covered (diagram : Diagram.{uTerm, uIndex, vIndex} Index)
    (observer : TransportObserver diagram) {source target : Index} (route : source ⟶ target)
    (cover : SystemCover (fibreSystem diagram observer source) (commandSystem diagram observer))
    (mapVia : ∀ state, cover.mapTerm state = Command.via route state)
    (state : SemanticTerm (diagram.obj source).theory) : False := by
  have escape : (commandSystem diagram observer).act (cover.mapLabel ()) (cover.mapTerm state)
      (.at target (transportTerm diagram route state)) := by
    rw [mapVia]
    exact ⟨.applyVia route state⟩
  obtain ⟨lifted, _, equal⟩ := cover.liftAct escape
  rw [mapVia lifted] at equal
  have equal : (Command.via route lifted : Command diagram) =
    .at target (transportTerm diagram route state) := equal
  cases equal

/-! ## Transport along stage maps -/

/-- A forward stage map is a translation of fibre systems. -/
def routeTranslation (diagram : Diagram.{uTerm, uIndex, vIndex} Index)
    (observer : TransportObserver diagram) {source target : Index} (route : source ⟶ target) :
    SystemTranslation (fibreSystem diagram observer source) (fibreSystem diagram observer target) where
  mapTerm := transportTerm diagram route
  mapAtom := id
  mapLabel := id
  mapEquiv := by
    intro left right equal
    have equal : left = right := equal
    subst equal
    rfl
  observes_iff := by
    intro result state
    show observer.observe source state = result ↔
      observer.observe target (transportTerm diagram route state) = result
    rw [observer.natural route state]
  mapAct := fun step => transported_fibre_step diagram route step

/-- Negation-free fibre formulas are preserved along every forward stage
map. -/
theorem route_psat (diagram : Diagram.{uTerm, uIndex, vIndex} Index)
    (observer : TransportObserver diagram) {source target : Index} (route : source ⟶ target)
    (formula : PosFormula observer.Result Unit) {state : SemanticTerm (diagram.obj source).theory}
    (holds : (fibreSystem diagram observer source).psat formula state) :
    (fibreSystem diagram observer target).psat formula (transportTerm diagram route state) := by
  have := (routeTranslation diagram observer route).psat_map formula holds
  change (fibreSystem diagram observer target).psat (PosFormula.map id id formula) _ at this
  rwa [PosFormula.map_id] at this

/-- A covered stage map is a cover of fibre systems. -/
def routeCover (diagram : CoveredDiagram.{uTerm, uIndex, vIndex} Index)
    (observer : TransportObserver diagram.toOperational) {source target : Index}
    (route : source ⟶ target) :
    SystemCover (fibreSystem diagram.toOperational observer source)
      (fibreSystem diagram.toOperational observer target) where
  toSystemTranslation := routeTranslation diagram.toOperational observer route
  liftAct := by
    intro _ state target' step
    induction state using Quotient.inductionOn with
    | _ representative =>
    induction target' using Quotient.inductionOn with
    | _ targetRepresentative =>
    change SemanticStep (diagram.obj target).theory
      (Quotient.mk _ ((diagram.map route).mapTerm representative))
      (Quotient.mk _ targetRepresentative) at step
    have authored := (semanticStep_mk_iff_step _ _ _).mp step
    obtain ⟨sourceTarget, sourceStep, equal⟩ := (diagram.map route).cover.liftStep authored
    refine ⟨Quotient.mk _ sourceTarget, semanticStep_mk sourceStep, ?_⟩
    show Quotient.mk _ ((diagram.map route).mapTerm sourceTarget) = Quotient.mk _ targetRepresentative
    rw [equal]
    rfl

/-- Along a covered stage map every fibre formula is preserved and
reflected. -/
theorem route_sat_iff (diagram : CoveredDiagram.{uTerm, uIndex, vIndex} Index)
    (observer : TransportObserver diagram.toOperational) {source target : Index}
    (route : source ⟶ target) (formula : Formula observer.Result Unit)
    (state : SemanticTerm (diagram.obj source).theory) :
    (fibreSystem diagram.toOperational observer target).sat formula
        (transportTerm diagram.toOperational route state) ↔
      (fibreSystem diagram.toOperational observer source).sat formula state := by
  have := (routeCover diagram observer route).sat_map formula state
  change (fibreSystem diagram.toOperational observer target).sat (Formula.map id id formula) _ ↔ _
    at this
  rwa [Formula.map_id] at this

/-- Covered stage maps are exact for bisimilarity. -/
theorem route_bisimilar_iff (diagram : CoveredDiagram.{uTerm, uIndex, vIndex} Index)
    (observer : TransportObserver diagram.toOperational) {source target : Index}
    (route : source ⟶ target) (left right : SemanticTerm (diagram.obj source).theory) :
    (fibreSystem diagram.toOperational observer target).Bisimilar
        (transportTerm diagram.toOperational route left)
        (transportTerm diagram.toOperational route right) ↔
      (fibreSystem diagram.toOperational observer source).Bisimilar left right :=
  (routeCover diagram observer route).bisimilar_map_iff (fun atom => ⟨atom, rfl⟩)
    (fun label => ⟨label, rfl⟩) left right

/-- Native types generated by fibre formulas transport exactly along covered
stage maps. -/
theorem route_nativeType_iff (diagram : CoveredDiagram.{uTerm, uIndex, vIndex} Index)
    (observer : TransportObserver diagram.toOperational) {source target : Index}
    (route : source ⟶ target) (formula : Formula observer.Result Unit)
    (state : SemanticTerm (diagram.obj source).theory) :
    (gsltOSLF (semanticTheory (diagram.obj target).theory)).satisfies (S := ())
        (transportTerm diagram.toOperational route state)
        (formulaNativeType (fibreSystem diagram.toOperational observer target) formula).pred ↔
      (gsltOSLF (semanticTheory (diagram.obj source).theory)).satisfies (S := ()) state
        (formulaNativeType (fibreSystem diagram.toOperational observer source) formula).pred :=
  route_sat_iff diagram observer route formula state

#print axioms sat_onSemantic_mk
#print axioms onSemantic_bisimilar_iff_bisimilarClass
#print axioms at_nativeType_iff
#print axioms via_not_covered
#print axioms route_psat
#print axioms route_nativeType_iff

end Mettapedia.OSLF.Framework.IndexedOperationalAdequacy
