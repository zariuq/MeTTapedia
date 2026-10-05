import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ScopedCommunicationInversion
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveHeaderInvariant

/-!
# Retaining active origins through scoped structural equations

A marking follows the constructor tree of an existing process. Marks belong
only to actual input/output prefixes and private binders; they are not labels
attached to a reduction after the fact. Static transport swaps binder marks
with the actual binder exchange, moves them with extrusion, and copies the
same server origins during replication unfolding. Suspended input bodies have
their own constructor markings but are not active selections.

The marked static relation erases to the existing structural relation. Every
existing static derivation lifts in both directions at its supplied endpoints.
This is a syntax refinement for tracing origins, not another execution theory.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveMarking

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ScopedActiveFrontier
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ScopedCommunicationInversion
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveHeaderInvariant

universe u

/-- A mark is part of a genuine prefix or restriction constructor. -/
inductive Tree (Label : Type u) where
  | var
  | nil
  | par (first second : Tree Label)
  | inp1 (origin : Label) (body : Tree Label)
  | inp2 (origin : Label) (body : Tree Label)
  | out1 (origin : Label)
  | out2 (origin : Label)
  | nu (origin : Label) (body : Tree Label)
  | rep (body : Tree Label)
  deriving DecidableEq

/-- A marking has exactly the shape of its supplied scoped process. All
subjects, payloads and continuation bodies still belong to that process. -/
inductive Fits {Label : Type u} : {Γ : Ctx sig} → Tree Label → Proc Γ → Prop where
  | var {Γ} (name : Var Γ Srt.pr) : Fits .var (.var name)
  | nil {Γ} : Fits .nil (nil : Proc Γ)
  | par {Γ} {p q : Proc Γ} {first second : Tree Label} :
      Fits first p → Fits second q → Fits (.par first second) (par p q)
  | inp1 {Γ} (origin : Label) (channel : Name Γ) {body : Proc (.nm :: Γ)}
      {marked : Tree Label} : Fits marked body → Fits (.inp1 origin marked) (inp1 channel body)
  | inp2 {Γ} (origin : Label) (channel : Name Γ) {body : Proc (.nm :: .nm :: Γ)}
      {marked : Tree Label} : Fits marked body → Fits (.inp2 origin marked) (inp2 channel body)
  | out1 {Γ} (origin : Label) (channel datum : Name Γ) :
      Fits (.out1 origin) (out1 channel datum)
  | out2 {Γ} (origin : Label) (channel first second : Name Γ) :
      Fits (.out2 origin) (out2 channel first second)
  | nu {Γ} (origin : Label) {body : Proc (.nm :: Γ)} {marked : Tree Label} :
      Fits marked body → Fits (.nu origin marked) (nu body)
  | rep {Γ} {body : Proc Γ} {marked : Tree Label} :
      Fits marked body → Fits (.rep marked) (rep body)

/-- Reindexing actual variables never changes a prefix's origin. -/
theorem Fits.rename {Label : Type u} {Γ Δ : Ctx sig} {marked : Tree Label}
    {process : Proc Γ} (fits : Fits marked process) (environment : Ren sig Γ Δ) :
    Fits marked (Mettapedia.OSLF.Binding.rename environment process) := by
  induction fits generalizing Δ with
  | var name => exact .var _
  | nil => exact .nil
  | par _ _ firstIH secondIH => exact .par (firstIH _) (secondIH _)
  | inp1 origin channel _ ih => exact .inp1 origin _ (ih _)
  | inp2 origin channel _ ih => exact .inp2 origin _ (ih _)
  | out1 origin channel datum => exact .out1 origin _ _
  | out2 origin channel first second => exact .out2 origin _ _ _
  | nu origin _ ih => exact .nu origin (ih _)
  | rep _ ih => exact .rep (ih _)

/-- A name map can identify channels, but it cannot invent constructor marks. -/
theorem Fits.ofRename {Label : Type u} : ∀ {Γ Δ : Ctx sig}
    (environment : Ren sig Γ Δ) (process : Proc Γ) (marked : Tree Label),
    Fits marked (Mettapedia.OSLF.Binding.rename environment process) → Fits marked process
  | _, _, _, .var name, _, fits => by cases fits; exact .var name
  | _, _, _, .op .nil .nil, _, fits => by cases fits; exact .nil
  | _, _, environment, .op .par (.cons first (.cons second .nil)), _, fits => by
      cases fits with
      | par firstFits secondFits =>
          exact .par (Fits.ofRename environment first _ firstFits)
            (Fits.ofRename environment second _ secondFits)
  | _, _, environment, .op .inp1 (.cons channel (.cons body .nil)), _, fits => by
      cases fits with
      | inp1 origin _ bodyFits =>
          exact .inp1 origin channel (Fits.ofRename (liftRen environment [.nm]) body _ bodyFits)
  | _, _, environment, .op .inp2 (.cons channel (.cons body .nil)), _, fits => by
      cases fits with
      | inp2 origin _ bodyFits =>
          exact .inp2 origin channel (Fits.ofRename (liftRen environment [.nm, .nm]) body _ bodyFits)
  | _, _, _, .op .out1 (.cons channel (.cons datum .nil)), _, fits => by
      cases fits with
      | out1 origin _ _ => exact .out1 origin channel datum
  | _, _, _, .op .out2 (.cons channel (.cons first (.cons second .nil))), _, fits => by
      cases fits with
      | out2 origin _ _ _ => exact .out2 origin channel first second
  | _, _, environment, .op .nu (.cons body .nil), _, fits => by
      cases fits with
      | nu origin bodyFits => exact .nu origin (Fits.ofRename (liftRen environment [.nm]) body _ bodyFits)
  | _, _, environment, .op .rep (.cons body .nil), _, fits => by
      cases fits with
      | rep bodyFits => exact .rep (Fits.ofRename environment body _ bodyFits)
termination_by _ _ _ process _ => termSize process
decreasing_by all_goals simp only [termSize, argsSize]; omega

/-- Directional tracing of the actual static generators. Replication may
contract a duplicate occurrence with a different mark; it retains the server's
own marks. Thus transport preserves origin inclusion, not a false bijection. -/
inductive Transport {Label : Type u} : {Γ : Ctx sig} →
    Tree Label → Proc Γ → Tree Label → Proc Γ → Prop where
  | refl {Γ} (marked : Tree Label) (process : Proc Γ) : Transport marked process marked process
  | trans {Γ} {m n o : Tree Label} {p q r : Proc Γ} :
      Transport m p n q → Transport n q o r → Transport m p o r
  | parComm {Γ} (m n : Tree Label) (p q : Proc Γ) :
      Transport (.par m n) (par p q) (.par n m) (par q p)
  | parAssoc {Γ} (m n o : Tree Label) (p q r : Proc Γ) :
      Transport (.par (.par m n) o) (par (par p q) r)
        (.par m (.par n o)) (par p (par q r))
  | parAssocBack {Γ} (m n o : Tree Label) (p q r : Proc Γ) :
      Transport (.par m (.par n o)) (par p (par q r))
        (.par (.par m n) o) (par (par p q) r)
  | parUnit {Γ} (m : Tree Label) (p : Proc Γ) :
      Transport (.par m .nil) (par p nil) m p
  | parUnitBack {Γ} (m : Tree Label) (p : Proc Γ) :
      Transport m p (.par m .nil) (par p nil)
  | nuUnused {Γ} (origin : Label) (m : Tree Label) (p : Proc Γ) :
      Transport (.nu origin m) (nu (weaken p)) m p
  | nuUnusedBack {Γ} (origin : Label) (m : Tree Label) (p : Proc Γ) :
      Transport m p (.nu origin m) (nu (weaken p))
  | nuPar {Γ} (origin : Label) (m n : Tree Label)
      (p : Proc (.nm :: Γ)) (q : Proc Γ) :
      Transport (.par (.nu origin m) n) (par (nu p) q)
        (.nu origin (.par m n)) (nu (par p (weaken q)))
  | nuParBack {Γ} (origin : Label) (m n : Tree Label)
      (p : Proc (.nm :: Γ)) (q : Proc Γ) :
      Transport (.nu origin (.par m n)) (nu (par p (weaken q)))
        (.par (.nu origin m) n) (par (nu p) q)
  | nuSwap {Γ} (outer inner : Label) (m : Tree Label) (p : Proc (.nm :: .nm :: Γ)) :
      Transport (.nu outer (.nu inner m)) (nu (nu p))
        (.nu inner (.nu outer m)) (nu (nu (rename swapRen p)))
  | nuSwapBack {Γ} (outer inner : Label) (m : Tree Label) (p : Proc (.nm :: .nm :: Γ)) :
      Transport (.nu inner (.nu outer m)) (nu (nu (rename swapRen p)))
        (.nu outer (.nu inner m)) (nu (nu p))
  | repUnfold {Γ} (m : Tree Label) (p : Proc Γ) :
      Transport (.rep m) (rep p) (.par m (.rep m)) (par p (rep p))
  | repFold {Γ} (copy server : Tree Label) (p : Proc Γ) :
      Transport (.par copy (.rep server)) (par p (rep p)) (.rep server) (rep p)
  | par {Γ} {m n o k : Tree Label} {p q r s : Proc Γ} :
      Transport m p n q → Transport o r k s →
        Transport (.par m o) (par p r) (.par n k) (par q s)
  | nu {Γ} (origin : Label) {m n : Tree Label} {p q : Proc (.nm :: Γ)} :
      Transport m p n q → Transport (.nu origin m) (nu p) (.nu origin n) (nu q)
  | inp1 {Γ} (origin : Label) (channel : Name Γ)
      {m n : Tree Label} {p q : Proc (.nm :: Γ)} :
      Transport m p n q → Transport (.inp1 origin m) (inp1 channel p)
        (.inp1 origin n) (inp1 channel q)
  | inp2 {Γ} (origin : Label) (channel : Name Γ)
      {m n : Tree Label} {p q : Proc (.nm :: .nm :: Γ)} :
      Transport m p n q → Transport (.inp2 origin m) (inp2 channel p)
        (.inp2 origin n) (inp2 channel q)
  | rep {Γ} {m n : Tree Label} {p q : Proc Γ} :
      Transport m p n q → Transport (.rep m) (rep p) (.rep n) (rep q)

/-- Forgetting marks yields a derivation using the existing equations. -/
theorem Transport.erase {Label : Type u} {Γ : Ctx sig} {m n : Tree Label}
    {p q : Proc Γ} (tracked : Transport m p n q) : StructuralEq p q := by
  induction tracked with
  | refl => exact .refl _
  | trans _ _ firstIH secondIH => exact .trans firstIH secondIH
  | parComm => exact .parComm _ _
  | parAssoc => exact .parAssoc _ _ _
  | parAssocBack => exact .symm (.parAssoc _ _ _)
  | parUnit => exact .parUnit _
  | parUnitBack => exact .symm (.parUnit _)
  | nuUnused => exact .nuUnused _
  | nuUnusedBack => exact .symm (.nuUnused _)
  | nuPar => exact .nuPar _ _
  | nuParBack => exact .symm (.nuPar _ _)
  | nuSwap => exact .nuSwap _
  | nuSwapBack => exact .symm (.nuSwap _)
  | repUnfold => exact .repUnfold _
  | repFold => exact .symm (.repUnfold _)
  | par _ _ firstIH secondIH => exact .par firstIH secondIH
  | nu _ _ ih => exact .nu ih
  | inp1 _ _ _ ih => exact .inp1 _ ih
  | inp2 _ _ _ ih => exact .inp2 _ ih
  | rep _ ih => exact .rep ih

/-- Every actual static proof transports any valid constructor marking in
either direction. Replication contraction is deliberately allowed to discard
an equal duplicate, while no active origin is introduced. -/
theorem structural_lift {Label : Type u} (fresh : Label) {Γ : Ctx sig}
    {p q : Proc Γ} (equal : StructuralEq p q) :
    (∀ (m : Tree Label), Fits m p → ∃ n, Fits n q ∧ Transport m p n q) ∧
    (∀ (n : Tree Label), Fits n q → ∃ m, Fits m p ∧ Transport n q m p) := by
  induction equal with
  | refl => exact ⟨fun m fits => ⟨m, fits, .refl _ _⟩, fun m fits => ⟨m, fits, .refl _ _⟩⟩
  | symm _ ih => exact ⟨ih.2, ih.1⟩
  | trans _ _ firstIH secondIH =>
      constructor
      · intro m fits
        rcases firstIH.1 m fits with ⟨n, fitN, first⟩
        rcases secondIH.1 n fitN with ⟨o, fitO, second⟩
        exact ⟨o, fitO, .trans first second⟩
      · intro o fits
        rcases secondIH.2 o fits with ⟨n, fitN, second⟩
        rcases firstIH.2 n fitN with ⟨m, fitM, first⟩
        exact ⟨m, fitM, .trans second first⟩
  | parComm p q =>
      constructor <;> intro marked fits <;> cases fits with
      | par left right => exact ⟨_, .par right left, .parComm _ _ _ _⟩
  | parAssoc p q r =>
      constructor
      · intro marked fits
        cases fits with
        | par first third => cases first with
          | par first second => exact ⟨_, .par first (.par second third), .parAssoc _ _ _ _ _ _⟩
      · intro marked fits
        cases fits with
        | par first later => cases later with
          | par second third => exact ⟨_, .par (.par first second) third, .parAssocBack _ _ _ _ _ _⟩
  | parUnit p =>
      constructor
      · intro marked fits
        cases fits with
        | par first empty => cases empty; exact ⟨_, first, .parUnit _ _⟩
      · intro marked fits
        exact ⟨_, .par fits .nil, .parUnitBack _ _⟩
  | nuUnused p =>
      constructor
      · intro marked fits
        cases fits with
        | nu origin body => exact ⟨_, Fits.ofRename _ p _ body, .nuUnused origin _ p⟩
      · intro marked fits
        exact ⟨_, .nu fresh (fits.rename _), .nuUnusedBack fresh _ p⟩
  | nuPar p q =>
      constructor
      · intro marked fits
        cases fits with
        | par privateFits frameFits => cases privateFits with
          | nu origin bodyFits => exact ⟨_, .nu origin (.par bodyFits (frameFits.rename _)), .nuPar origin _ _ p q⟩
      · intro marked fits
        cases fits with
        | nu origin bodyFits => cases bodyFits with
          | par privateFits frameFits =>
            exact ⟨_, .par (.nu origin privateFits) (Fits.ofRename _ q _ frameFits), .nuParBack origin _ _ p q⟩
  | nuSwap p =>
      constructor
      · intro marked fits
        cases fits with
        | nu outer innerFits => cases innerFits with
          | nu inner bodyFits => exact ⟨_, .nu inner (.nu outer (bodyFits.rename _)), .nuSwap outer inner _ p⟩
      · intro marked fits
        cases fits with
        | nu inner outerFits => cases outerFits with
          | nu outer bodyFits => exact ⟨_, .nu outer (.nu inner (Fits.ofRename _ p _ bodyFits)), .nuSwapBack outer inner _ p⟩
  | repUnfold p =>
      constructor
      · intro marked fits
        cases fits with
        | rep bodyFits => exact ⟨_, .par bodyFits (.rep bodyFits), .repUnfold _ p⟩
      · intro marked fits
        cases fits with
        | par first replicated => cases replicated with
          | rep server => exact ⟨_, .rep server, .repFold _ _ p⟩
  | par _ _ firstIH secondIH =>
      constructor
      · intro marked fits
        cases fits with
        | par first second =>
          rcases firstIH.1 _ first with ⟨m, fitM, trackM⟩
          rcases secondIH.1 _ second with ⟨n, fitN, trackN⟩
          exact ⟨_, .par fitM fitN, .par trackM trackN⟩
      · intro marked fits
        cases fits with
        | par first second =>
          rcases firstIH.2 _ first with ⟨m, fitM, trackM⟩
          rcases secondIH.2 _ second with ⟨n, fitN, trackN⟩
          exact ⟨_, .par fitM fitN, .par trackM trackN⟩
  | nu _ ih =>
      constructor
      · intro marked fits
        cases fits with
        | nu origin bodyFits =>
          rcases ih.1 _ bodyFits with ⟨m, fitM, trackM⟩
          exact ⟨_, .nu origin fitM, .nu origin trackM⟩
      · intro marked fits
        cases fits with
        | nu origin bodyFits =>
          rcases ih.2 _ bodyFits with ⟨m, fitM, trackM⟩
          exact ⟨_, .nu origin fitM, .nu origin trackM⟩
  | inp1 channel _ ih =>
      constructor
      · intro marked fits
        cases fits with
        | inp1 origin _ bodyFits =>
          rcases ih.1 _ bodyFits with ⟨m, fitM, trackM⟩
          exact ⟨_, .inp1 origin channel fitM, .inp1 origin channel trackM⟩
      · intro marked fits
        cases fits with
        | inp1 origin _ bodyFits =>
          rcases ih.2 _ bodyFits with ⟨m, fitM, trackM⟩
          exact ⟨_, .inp1 origin channel fitM, .inp1 origin channel trackM⟩
  | inp2 channel _ ih =>
      constructor
      · intro marked fits
        cases fits with
        | inp2 origin _ bodyFits =>
          rcases ih.1 _ bodyFits with ⟨m, fitM, trackM⟩
          exact ⟨_, .inp2 origin channel fitM, .inp2 origin channel trackM⟩
      · intro marked fits
        cases fits with
        | inp2 origin _ bodyFits =>
          rcases ih.2 _ bodyFits with ⟨m, fitM, trackM⟩
          exact ⟨_, .inp2 origin channel fitM, .inp2 origin channel trackM⟩
  | rep _ ih =>
      constructor
      · intro marked fits
        cases fits with
        | rep bodyFits =>
          rcases ih.1 _ bodyFits with ⟨m, fitM, trackM⟩
          exact ⟨_, .rep fitM, .rep trackM⟩
      · intro marked fits
        cases fits with
        | rep bodyFits =>
          rcases ih.2 _ bodyFits with ⟨m, fitM, trackM⟩
          exact ⟨_, .rep fitM, .rep trackM⟩

/-- The selected constructor retains an actual active-context address.
Suspended input bodies are not traversed. -/
inductive Selection {Label : Type u} : Header → Label → Tree Label → Type u where
  | inp1 (origin : Label) (body : Tree Label) : Selection .input1 origin (.inp1 origin body)
  | inp2 (origin : Label) (body : Tree Label) : Selection .input2 origin (.inp2 origin body)
  | out1 (origin : Label) : Selection .output1 origin (.out1 origin)
  | out2 (origin : Label) : Selection .output2 origin (.out2 origin)
  | left {header origin first} (second : Tree Label) :
      Selection header origin first → Selection header origin (.par first second)
  | right {header origin second} (first : Tree Label) :
      Selection header origin second → Selection header origin (.par first second)
  | nu {header origin body} (binder : Label) :
      Selection header origin body → Selection header origin (.nu binder body)
  | rep {header origin body} :
      Selection header origin body → Selection header origin (.rep body)

inductive AddressStep where
  | left
  | right
  | scope
  | replicated
  deriving DecidableEq, Repr

def Selection.address {Label : Type u} : {header : Header} → {origin : Label} →
    {marked : Tree Label} → Selection header origin marked → List AddressStep
  | _, _, _, .inp1 .. => []
  | _, _, _, .inp2 .. => []
  | _, _, _, .out1 .. => []
  | _, _, _, .out2 .. => []
  | _, _, _, .left _ selected => .left :: selected.address
  | _, _, _, .right _ selected => .right :: selected.address
  | _, _, _, .nu _ selected => .scope :: selected.address
  | _, _, _, .rep selected => .replicated :: selected.address

/-- Every target prefix selected after static transport has a genuinely
selected original constructor of the same arity and origin. Contraction may
remove an original duplicate, so the converse is deliberately not asserted. -/
theorem Transport.selection_back {Label : Type u} {Γ : Ctx sig} {m n : Tree Label}
    {p q : Proc Γ} (tracked : Transport m p n q) (header : Header) (origin : Label) :
    Nonempty (Selection header origin n) → Nonempty (Selection header origin m) := by
  induction tracked with
  | refl => exact id
  | trans _ _ firstIH secondIH => exact fun selected => firstIH (secondIH selected)
  | parComm =>
      rintro ⟨selected⟩
      cases selected with
      | left _ selected => exact ⟨.right _ selected⟩
      | right _ selected => exact ⟨.left _ selected⟩
  | parAssoc =>
      rintro ⟨selected⟩
      cases selected with
      | left _ selected => exact ⟨.left _ (.left _ selected)⟩
      | right _ selected => cases selected with
          | left _ selected => exact ⟨.left _ (.right _ selected)⟩
          | right _ selected => exact ⟨.right _ selected⟩
  | parAssocBack =>
      rintro ⟨selected⟩
      cases selected with
      | left _ selected => cases selected with
          | left _ selected => exact ⟨.left _ selected⟩
          | right _ selected => exact ⟨.right _ (.left _ selected)⟩
      | right _ selected => exact ⟨.right _ (.right _ selected)⟩
  | parUnit => exact fun ⟨selected⟩ => ⟨.left _ selected⟩
  | parUnitBack =>
      rintro ⟨selected⟩
      cases selected with
      | left _ selected => exact ⟨selected⟩
      | right _ selected => cases selected
  | nuUnused => exact fun ⟨selected⟩ => ⟨.nu _ selected⟩
  | nuUnusedBack =>
      rintro ⟨selected⟩
      cases selected with
      | nu _ selected => exact ⟨selected⟩
  | nuPar =>
      rintro ⟨selected⟩
      cases selected with
      | nu _ selected => cases selected with
          | left _ selected => exact ⟨.left _ (.nu _ selected)⟩
          | right _ selected => exact ⟨.right _ selected⟩
  | nuParBack =>
      rintro ⟨selected⟩
      cases selected with
      | left _ selected => cases selected with
          | nu _ selected => exact ⟨.nu _ (.left _ selected)⟩
      | right _ selected => exact ⟨.nu _ (.right _ selected)⟩
  | nuSwap =>
      rintro ⟨selected⟩
      cases selected with
      | nu _ selected => cases selected with
          | nu _ selected => exact ⟨.nu _ (.nu _ selected)⟩
  | nuSwapBack =>
      rintro ⟨selected⟩
      cases selected with
      | nu _ selected => cases selected with
          | nu _ selected => exact ⟨.nu _ (.nu _ selected)⟩
  | repUnfold =>
      rintro ⟨selected⟩
      cases selected with
      | left _ selected => exact ⟨.rep selected⟩
      | right _ selected => exact ⟨selected⟩
  | repFold => exact fun ⟨selected⟩ => ⟨.right _ selected⟩
  | par _ _ firstIH secondIH =>
      rintro ⟨selected⟩
      cases selected with
      | left _ selected =>
          rcases firstIH ⟨selected⟩ with ⟨original⟩
          exact ⟨.left _ original⟩
      | right _ selected =>
          rcases secondIH ⟨selected⟩ with ⟨original⟩
          exact ⟨.right _ original⟩
  | nu _ _ ih =>
      rintro ⟨selected⟩
      cases selected with
      | nu _ selected =>
          rcases ih ⟨selected⟩ with ⟨original⟩
          exact ⟨.nu _ original⟩
  | inp1 => rintro ⟨selected⟩; cases selected; exact ⟨.inp1 _ _⟩
  | inp2 => rintro ⟨selected⟩; cases selected; exact ⟨.inp2 _ _⟩
  | rep _ ih =>
      rintro ⟨selected⟩
      cases selected with
      | rep selected =>
          rcases ih ⟨selected⟩ with ⟨original⟩
          exact ⟨.rep original⟩

/-- Marks of the actual restriction telescope used by an exposure. -/
inductive ScopeMarks (Label : Type u) : {Γ Δ : Ctx sig} → Scope Γ Δ → Type u where
  | nil {Γ} : ScopeMarks Label (Scope.nil : Scope Γ Γ)
  | bind {Γ Δ} {rest : Scope (.nm :: Γ) Δ} (origin : Label) :
      ScopeMarks Label rest → ScopeMarks Label (.bind rest)

def ScopeMarks.close {Label : Type u} : {Γ Δ : Ctx sig} → {scope : Scope Γ Δ} →
    ScopeMarks Label scope → Tree Label → Tree Label
  | _, _, _, .nil, body => body
  | _, _, _, .bind origin rest, body => .nu origin (rest.close body)

def ScopeMarks.select {Label : Type u} : {Γ Δ : Ctx sig} → {scope : Scope Γ Δ} →
    (marked : ScopeMarks Label scope) → {header : Header} → {origin : Label} →
    {body : Tree Label} → Selection header origin body →
      Selection header origin (marked.close body)
  | _, _, _, .nil, _, _, _, selected => selected
  | _, _, _, .bind binder rest, _, _, _, selected => .nu binder (rest.select selected)

theorem Fits.scope_decompose {Label : Type u} : ∀ {Γ Δ : Ctx sig}
    (scope : Scope Γ Δ) (body : Proc Δ) (marked : Tree Label),
    Fits marked (scope.close body) →
      ∃ (binders : ScopeMarks Label scope) (inner : Tree Label),
        marked = binders.close inner ∧ Fits inner body
  | _, _, .nil, body, marked, fits => ⟨.nil, marked, rfl, fits⟩
  | _, _, .bind rest, body, marked, fits => by
      cases fits with
      | nu binder bodyFits =>
          rcases Fits.scope_decompose rest body _ bodyFits with ⟨binders, inner, equal, fitted⟩
          exact ⟨.bind binder binders, inner, congrArg (Tree.nu binder) equal, fitted⟩

/-- The chosen actual primitive communication retains both prefix origins
and the marking of its supplied continuation body. -/
inductive MarkedCommunication {Label : Type u} : {Γ : Ctx sig} →
    {redex reduct : Proc Γ} → Communication redex reduct → Tree Label → Type u where
  | unary {Γ} (channel datum : Name Γ) (body : Proc (.nm :: Γ))
      (outputOrigin inputOrigin : Label) (continuation : Tree Label)
      (fitted : Fits continuation body) :
      MarkedCommunication (.unary channel datum body)
        (.par (.out1 outputOrigin) (.inp1 inputOrigin continuation))
  | binary {Γ} (channel first second : Name Γ) (body : Proc (.nm :: .nm :: Γ))
      (outputOrigin inputOrigin : Label) (continuation : Tree Label)
      (fitted : Fits continuation body) :
      MarkedCommunication (.binary channel first second body)
        (.par (.out2 outputOrigin) (.inp2 inputOrigin continuation))

def MarkedCommunication.inputOrigin {Label : Type u} : {Γ : Ctx sig} →
    {redex reduct : Proc Γ} → {selected : Communication redex reduct} →
    {marked : Tree Label} → MarkedCommunication selected marked → Label
  | _, _, _, _, _, .unary _ _ _ _ input _ _ => input
  | _, _, _, _, _, .binary _ _ _ _ _ input _ _ => input

def MarkedCommunication.outputOrigin {Label : Type u} : {Γ : Ctx sig} →
    {redex reduct : Proc Γ} → {selected : Communication redex reduct} →
    {marked : Tree Label} → MarkedCommunication selected marked → Label
  | _, _, _, _, _, .unary _ _ _ output _ _ _ => output
  | _, _, _, _, _, .binary _ _ _ _ output _ _ _ => output

def MarkedCommunication.inputSelection {Label : Type u} : {Γ : Ctx sig} →
    {redex reduct : Proc Γ} → {selected : Communication redex reduct} →
    {marked : Tree Label} → (comm : MarkedCommunication selected marked) →
      Selection (inputHeader selected) comm.inputOrigin marked
  | _, _, _, _, _, .unary _ _ _ _ input continuation _ => .right _ (.inp1 input continuation)
  | _, _, _, _, _, .binary _ _ _ _ _ input continuation _ => .right _ (.inp2 input continuation)

def MarkedCommunication.outputSelection {Label : Type u} : {Γ : Ctx sig} →
    {redex reduct : Proc Γ} → {selected : Communication redex reduct} →
    {marked : Tree Label} → (comm : MarkedCommunication selected marked) →
      Selection (outputHeader selected) comm.outputOrigin marked
  | _, _, _, _, _, .unary _ _ _ output _ _ _ => .left _ (.out1 output)
  | _, _, _, _, _, .binary _ _ _ _ output _ _ _ => .left _ (.out2 output)

theorem markedCommunication_exists {Label : Type u} {Γ : Ctx sig}
    {redex reduct : Proc Γ} (selected : Communication redex reduct) {marked : Tree Label}
    (fitted : Fits marked redex) : Nonempty (MarkedCommunication selected marked) := by
  cases selected with
  | unary channel datum body =>
      cases fitted with
      | par output input =>
          cases output with
          | out1 outputOrigin _ _ =>
              cases input with
              | inp1 inputOrigin _ continuationFits => exact ⟨.unary _ _ _ _ _ _ continuationFits⟩
  | binary channel first second body =>
      cases fitted with
      | par output input =>
          cases output with
          | out2 outputOrigin _ _ _ =>
              cases input with
              | inp2 inputOrigin _ continuationFits => exact ⟨.binary _ _ _ _ _ _ _ continuationFits⟩

/-- Exact supplied syntax and telescope, together with the selected prefix
marks recovered in the original constructor tree. No fresh origin labels are
added at the primitive communication. -/
structure TracedExposure {Label : Type u} {Γ : Ctx sig} (original : Tree Label)
    {source target : Proc Γ} (exposure : Exposure source target) where
  binders : ScopeMarks Label exposure.scope
  redexMarks : Tree Label
  frameMarks : Tree Label
  continuation : MarkedCommunication exposure.selected redexMarks
  frameFits : Fits frameMarks exposure.frame
  transportedFits : Fits (binders.close (.par redexMarks frameMarks))
    (exposure.scope.close (par exposure.redex exposure.frame))
  transport : Transport original source (binders.close (.par redexMarks frameMarks))
    (exposure.scope.close (par exposure.redex exposure.frame))
  originalInput : Selection (inputHeader exposure.selected) continuation.inputOrigin original
  originalOutput : Selection (outputHeader exposure.selected) continuation.outputOrigin original

/-- An arbitrary actual static exposure recovers original active prefix
addresses, while retaining its own exact channel, payload and continuation. -/
theorem tracedExposure_exists {Label : Type u} (fresh : Label) {Γ : Ctx sig}
    {original : Tree Label} {source target : Proc Γ} (fitted : Fits original source)
    (exposure : Exposure source target) : Nonempty (TracedExposure original exposure) := by
  rcases (structural_lift fresh exposure.before).1 original fitted with ⟨transported, fitT, tracked⟩
  rcases Fits.scope_decompose exposure.scope (par exposure.redex exposure.frame) transported fitT with
    ⟨binders, inside, same, fitInside⟩
  cases fitInside with
  | @par _ _ _ first second fitRedex fitFrame =>
      rcases markedCommunication_exists exposure.selected fitRedex with ⟨communication⟩
      have inTarget := binders.select (.left second communication.inputSelection)
      have outTarget := binders.select (.left second communication.outputSelection)
      rw [same] at tracked fitT
      rcases tracked.selection_back _ _ ⟨inTarget⟩ with ⟨input⟩
      rcases tracked.selection_back _ _ ⟨outTarget⟩ with ⟨output⟩
      exact ⟨⟨binders, _, _, communication, fitFrame, fitT, tracked, input, output⟩⟩

/-- Every actual equation-saturated firing has a prefix-origin explanation
in the supplied pre-equation syntax, with real selected contextual addresses. -/
theorem modulo_step_has_traced_origins {Label : Type u} (fresh : Label) {Γ : Ctx sig}
    {original : Tree Label} {source target : Proc Γ} (fitted : Fits original source)
    (firing : StepModulo source target) :
    ∃ exposure : Exposure source target, Nonempty (TracedExposure original exposure) := by
  rcases modulo_step_exposes firing with ⟨exposure⟩
  exact ⟨exposure, tracedExposure_exists fresh fitted exposure⟩

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveMarking
