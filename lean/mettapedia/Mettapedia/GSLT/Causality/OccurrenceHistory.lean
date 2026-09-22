import Mettapedia.GSLT.Core.GSLT
import Mettapedia.GSLT.Core.GSLTConstructions
import Mettapedia.GSLT.Core.InteractionEvent
import Mettapedia.GSLT.Causality.Trace
import Mettapedia.GSLT.Dynamics.CostExactness
import Mettapedia.GSLT.LanguageDef.Cost.Elaboration.ReplayKey
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.Order.Group.Multiset
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.Data.Multiset.AddSub
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.ZeroCons

/-!
# Occurrence paths, zoom licence, independence tiles, writer cover

Prime zoom is a lattice of erasures on one GSLT, not two evaluators.

1. Licence: on the reachable envelope from a root, memoizing the history
   potential by current term is sound iff that potential is constant on
   term-key fibres. Exact costs satisfy this; dissipative cost does not.
   The term key is not an exact replay of the extended state.
2. Proof-relevant paths: homs are occurrence evidence, not `PLift Step`.
   Additive valuations are functors to the one-object additive category.
3. Independence tiles: swap only independent sites. Bags survive the swap;
   ordered site lists do not.
4. History as derived cover: the category of elements of `Hom(root, -)`
   maps onto `spendLift` over the free monoid of occurrences. The evaluator
   still keys on the erased term. The GSLT object and `η`/`π` morphisms
   are in `GSLT.Causality.HistoryCover`.

No LanguageDef, no stored `(term, history)` GSLT, no runtime guard.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.OccurrenceHistory

open Mettapedia.GSLT
open Mettapedia.GSLT.Core.InteractionEvent
open Mettapedia.GSLT.LanguageDef.Cost.Elaboration
open CategoryTheory

universe uSite uEvent

variable {theory : GSLT}

/-! ## 1. Licence to memoize by term -/

/-- Reachable envelope states from a chosen origin. This is the slice an
evaluator would see if it stored history; the licence says when it may
forget that storage and key only on the current term. -/
structure RootSlice (root : theory.Term) where
  state : ExtendedTerm theory
  fromRoot : EnvelopePath (S := theory) (envelopeEmbed theory root) state

namespace RootSlice

variable {root : theory.Term}

/-- Coarsest zoom: identify states with the same current term. -/
def termKey (s : RootSlice (theory := theory) root) : theory.Term :=
  s.state.current

/-- Envelope path between two slices of the same origin, via the unique
parent covering: invert back to the root, then replay. -/
def connect (s t : RootSlice (theory := theory) root) :
    EnvelopePath (S := theory) s.state t.state :=
  EnvelopePath.append (S := theory)
    (EnvelopePath.reverse (S := theory) s.fromRoot) t.fromRoot

end RootSlice

/-- On a root-slice, term-key fibre invariance of the history potential. -/
def TermKeySupportsPotential {A : Type*} [AddCommGroup A]
    (am : ActionMap theory A) (root : theory.Term) : Prop :=
  ReplayKey.Supports (RootSlice.termKey (theory := theory) (root := root))
    (fun s => historyPotential am s.state)

/-- Memoizing the potential by current term is sound iff connecting two
reachable states with the same current costs zero. Theorem 7.1 identifies
that cost with the potential difference. -/
theorem term_memoization_iff {A : Type*} [AddCommGroup A]
    (am : ActionMap theory A) (root : theory.Term) :
    TermKeySupportsPotential am root ↔
      ∀ (s t : RootSlice (theory := theory) root),
        RootSlice.termKey s = RootSlice.termKey t →
          totalEnvelopeAction am (RootSlice.connect s t) = 0 := by
  constructor
  · intro h s t sameCurrent
    have pot : historyPotential am s.state = historyPotential am t.state :=
      h sameCurrent
    have d :=
      totalEnvelopeAction_eq_historyDelta (S := theory) am (RootSlice.connect s t)
    rw [d, pot, sub_self]
  · intro h s t sameCurrent
    have tot := h s t sameCurrent
    have d :=
      totalEnvelopeAction_eq_historyDelta (S := theory) am (RootSlice.connect s t)
    rw [d] at tot
    exact (eq_of_sub_eq_zero tot).symm

theorem termKey_supports_potential_of_survives {A : Type*} [AddCommGroup A]
    (am : ActionMap theory A) (root : theory.Term)
    (h : SurvivesForgetting (S := theory) am) :
    TermKeySupportsPotential am root := by
  refine (term_memoization_iff am root).2 ?_
  intro s t sameCurrent
  exact h (RootSlice.connect s t) sameCurrent

theorem exact_licences_term_memoization {A : Type*} [AddCommGroup A]
    (am : ActionMap theory A) {φ : theory.Term → A} (hex : am.Exact φ)
    (root : theory.Term) :
    TermKeySupportsPotential am root :=
  termKey_supports_potential_of_survives am root
    (survivesForgetting_of_exact am hex)

def dissipativeStartSlice : RootSlice (theory := flipGSLT) false where
  state := dissipativeEnvelopeStart
  fromRoot := EnvelopePath.nil (S := flipGSLT) dissipativeEnvelopeStart

def dissipativeEndSlice : RootSlice (theory := flipGSLT) false where
  state := dissipativeEnvelopeEnd
  fromRoot := dissipativeEnvelopePath

theorem dissipative_slices_same_term :
    dissipativeStartSlice.termKey = dissipativeEndSlice.termKey :=
  rfl

theorem dissipative_slices_distinct :
    dissipativeStartSlice ≠ dissipativeEndSlice := by
  intro h
  have hhist :=
    congrArg (fun s : RootSlice (theory := flipGSLT) false => s.state.history) h
  simp [dissipativeStartSlice, dissipativeEndSlice, dissipativeEnvelopeStart,
    dissipativeEnvelopeEnd, envelopeEmbed, ExtendedTerm.initial, Trace.empty]
    at hhist

/-- Exact coboundary costs may be memoized by current term on a root slice. -/
theorem exactFlip_term_key_supports :
    TermKeySupportsPotential exactFlip false :=
  exact_licences_term_memoization exactFlip exactFlip_is_exact false

/-- Memoizing dissipative cost by current term is unsound: two reachable
states share a term and disagree on recorded spend. -/
theorem dissipative_term_key_not_support :
    ¬ TermKeySupportsPotential dissipativeFlip false := by
  intro h
  have eqPot : historyPotential dissipativeFlip dissipativeStartSlice.state =
      historyPotential dissipativeFlip dissipativeEndSlice.state :=
    h dissipative_slices_same_term
  have hstart : historyPotential dissipativeFlip dissipativeStartSlice.state = 0 := by
    simp [historyPotential, historyPotentialEntries, traceEntries,
      dissipativeStartSlice, dissipativeEnvelopeStart, envelopeEmbed,
      ExtendedTerm.initial, Trace.empty]
  have hend : historyPotential dissipativeFlip dissipativeEndSlice.state = 1 := by
    simp [historyPotential, historyPotentialEntries, traceEntries,
      dissipativeEndSlice, dissipativeEnvelopeEnd, dissipativeFlip]
  rw [hstart, hend] at eqPot
  exact absurd eqPot (by decide)

/-- The term key is not an exact replay of envelope state: two histories
reach the same current. Merging keys is licensed only for valuations that
survive the collision, not because the states are the same. -/
theorem flip_term_key_not_exact :
    ¬ ReplayKey.IsExact
        (RootSlice.termKey (theory := flipGSLT) (root := false)) :=
  ReplayKey.collision_prevents_exact dissipative_slices_distinct rfl

/-! ## 2. Occurrence paths -/

/-- One occurrence-specific step. Endpoints plus site plus evidence. -/
structure Occurrence (P : InteractionPresentation.{uSite, uEvent} theory)
    (source target : theory.Term) where
  site : P.Site
  evidence : P.Event site source target

namespace Occurrence

variable {P : InteractionPresentation.{uSite, uEvent} theory}

theorem step {source target : theory.Term} (o : Occurrence P source target) :
    theory.Step source target :=
  P.sound o.evidence

end Occurrence

/-- Finite paths of occurrences. This is the free category on events. -/
inductive OccurrencePath (P : InteractionPresentation.{uSite, uEvent} theory) :
    theory.Term → theory.Term → Type _ where
  | refl (t : theory.Term) : OccurrencePath P t t
  | cons {source middle target : theory.Term} :
      Occurrence P source middle → OccurrencePath P middle target →
        OccurrencePath P source target

namespace OccurrencePath

variable {P : InteractionPresentation.{uSite, uEvent} theory}

def append {source middle target : theory.Term} :
    OccurrencePath P source middle → OccurrencePath P middle target →
      OccurrencePath P source target
  | .refl _, q => q
  | .cons o rest, q => .cons o (append rest q)

@[simp] theorem refl_append {source target : theory.Term}
    (p : OccurrencePath P source target) :
    append (.refl source) p = p := rfl

@[simp] theorem append_refl {source target : theory.Term}
    (p : OccurrencePath P source target) :
    append p (.refl target) = p := by
  induction p with
  | refl => rfl
  | cons o rest ih => simp [append, ih]

theorem append_assoc {a b c d : theory.Term}
    (p : OccurrencePath P a b) (q : OccurrencePath P b c)
    (r : OccurrencePath P c d) :
    append (append p q) r = append p (append q r) := by
  induction p with
  | refl => rfl
  | cons o rest ih => simp [append, ih]

/-- Site list of a path (order-sensitive readout). -/
def sites {s t : theory.Term} : OccurrencePath P s t → List P.Site
  | .refl _ => []
  | .cons o rest => o.site :: sites rest

/-- Site bag of a path (order-insensitive readout). -/
def siteBag {s t : theory.Term} (p : OccurrencePath P s t) : Multiset P.Site :=
  (sites p : Multiset P.Site)

@[simp] theorem sites_refl (t : theory.Term) :
    sites (.refl (P := P) t) = [] :=
  rfl

@[simp] theorem sites_cons {s m t : theory.Term}
    (o : Occurrence P s m) (rest : OccurrencePath P m t) :
    sites (.cons o rest) = o.site :: sites rest :=
  rfl

@[simp] theorem siteBag_refl (t : theory.Term) :
    siteBag (.refl (P := P) t) = 0 :=
  Multiset.coe_nil

theorem sites_cast {s t t' : theory.Term} (h : t = t')
    (p : OccurrencePath P s t') :
    sites (h ▸ p) = sites p := by
  cases h
  rfl

end OccurrencePath

/-- Terms with occurrence-paths as arrows. Parameterised by the presentation
so distinct event families yield distinct hom-sets. -/
def OccurrenceCat (_P : InteractionPresentation.{uSite, uEvent} theory) :=
  theory.Term

instance (P : InteractionPresentation.{uSite, uEvent} theory) :
    Category (OccurrenceCat P) where
  Hom := fun s t => OccurrencePath P s t
  id := fun t => OccurrencePath.refl t
  comp := fun f g => OccurrencePath.append f g
  id_comp := fun f => OccurrencePath.refl_append f
  comp_id := fun f => OccurrencePath.append_refl f
  assoc := fun f g h => OccurrencePath.append_assoc f g h

/-- One-object category of an additive monoid, composition in path order
(first then second). This is the unflipped target for a valuation functor. -/
def AddOneObj (_A : Type*) := Unit

instance (A : Type*) [AddMonoid A] : Category (AddOneObj A) where
  Hom _ _ := A
  id _ := (0 : A)
  comp f g := f + g
  id_comp := fun f => zero_add f
  comp_id := fun f => add_zero f
  assoc := fun f g h => add_assoc f g h

/-- Additive valuation of occurrences; composition is addition. -/
structure OccurrenceValuation
    (P : InteractionPresentation.{uSite, uEvent} theory) (A : Type*)
    [AddMonoid A] where
  grade : ∀ {s t : theory.Term}, Occurrence P s t → A

namespace OccurrenceValuation

variable {P : InteractionPresentation.{uSite, uEvent} theory}
  {A : Type*} [AddMonoid A] (v : OccurrenceValuation P A)

def onPath {s t : theory.Term} : OccurrencePath P s t → A
  | .refl _ => 0
  | .cons o rest => v.grade o + onPath rest

theorem onPath_id (t : theory.Term) : v.onPath (.refl t) = 0 := rfl

theorem onPath_append {s m t : theory.Term}
    (p : OccurrencePath P s m) (q : OccurrencePath P m t) :
    v.onPath (OccurrencePath.append p q) = v.onPath p + v.onPath q := by
  induction p with
  | refl => simp [onPath]
  | cons o rest ih =>
      simp [OccurrencePath.append, onPath, ih, add_assoc]

/-- A valuation is a functor from the occurrence category to the one-object
category of the additive monoid. -/
def toFunctor : CategoryTheory.Functor (OccurrenceCat P) (AddOneObj A) where
  obj _ := ()
  map p := v.onPath p
  map_id := fun t => v.onPath_id t
  map_comp := fun f g => v.onPath_append f g

end OccurrenceValuation

/-! ## 3. Independence tiles -/

/-- Independence lives on sites, which keep identity across a swap. -/
structure SiteIndependence
    (P : InteractionPresentation.{uSite, uEvent} theory) where
  indep : P.Site → P.Site → Prop
  symm : ∀ a b, indep a b → indep b a
  irrefl : ∀ a, ¬ indep a a

/-- A commuting square of two independent occurrences. This is the generated
2-cell of a Mazurkiewicz swap, not a dummy `True` on endpoints. -/
structure IndependenceTile
    (P : InteractionPresentation.{uSite, uEvent} theory)
    (indep : SiteIndependence P) (source : theory.Term) where
  first : P.Enabled source
  altFirst : P.Enabled source
  second : P.Enabled first.target
  altSecond : P.Enabled altFirst.target
  independent : indep.indep first.site altFirst.site
  close : second.target = altSecond.target
  sameFirst : first.site = altSecond.site
  sameSecond : altFirst.site = second.site

namespace IndependenceTile

variable {P : InteractionPresentation.{uSite, uEvent} theory}
  {indep : SiteIndependence P} {source : theory.Term}
  (tile : IndependenceTile P indep source)

theorem independent_ne : tile.first.site ≠ tile.altFirst.site :=
  fun h => indep.irrefl tile.first.site (h ▸ tile.independent)

def occFirst : Occurrence P source tile.first.target :=
  ⟨tile.first.site, tile.first.evidence⟩

def occSecond : Occurrence P tile.first.target tile.second.target :=
  ⟨tile.second.site, tile.second.evidence⟩

def occAltFirst : Occurrence P source tile.altFirst.target :=
  ⟨tile.altFirst.site, tile.altFirst.evidence⟩

def occAltSecond : Occurrence P tile.altFirst.target tile.altSecond.target :=
  ⟨tile.altSecond.site, tile.altSecond.evidence⟩

def path : OccurrencePath P source tile.second.target :=
  .cons tile.occFirst (.cons tile.occSecond (.refl tile.second.target))

def pathSwap : OccurrencePath P source tile.altSecond.target :=
  .cons tile.occAltFirst (.cons tile.occAltSecond (.refl tile.altSecond.target))

def pathSwap' : OccurrencePath P source tile.second.target :=
  tile.close ▸ tile.pathSwap

theorem sites_pathSwap' :
    OccurrencePath.sites tile.pathSwap' = OccurrencePath.sites tile.pathSwap :=
  OccurrencePath.sites_cast tile.close tile.pathSwap

theorem bag_survives_swap :
    OccurrencePath.siteBag tile.path =
      OccurrencePath.siteBag tile.pathSwap' := by
  unfold OccurrencePath.siteBag
  rw [tile.sites_pathSwap']
  simp [path, pathSwap, OccurrencePath.sites, occFirst, occSecond,
    occAltFirst, occAltSecond]
  rw [tile.sameFirst, tile.sameSecond]
  exact List.Perm.swap _ _ _

/-- A valuation descends along the Mazurkiewicz swap iff it is constant on
the two routes of every independence tile. -/
def TileInvariant {A : Type*} [AddMonoid A]
    (v : OccurrenceValuation P A) : Prop :=
  ∀ {src : theory.Term} (tl : IndependenceTile P indep src),
    v.onPath tl.path = v.onPath tl.pathSwap'

end IndependenceTile

def bagValuation (P : InteractionPresentation.{uSite, uEvent} theory) :
    OccurrenceValuation P (Multiset P.Site) where
  grade := fun o => {o.site}

theorem bagValuation_onPath {P : InteractionPresentation.{uSite, uEvent} theory}
    {s t : theory.Term} (p : OccurrencePath P s t) :
    (bagValuation P).onPath p = OccurrencePath.siteBag p := by
  induction p with
  | refl =>
      simp [OccurrenceValuation.onPath, OccurrencePath.siteBag]
  | cons o rest ih =>
      calc
        (bagValuation P).onPath (.cons o rest)
            = {o.site} + (bagValuation P).onPath rest := rfl
        _ = {o.site} + OccurrencePath.siteBag rest := by rw [ih]
        _ = o.site ::ₘ (OccurrencePath.sites rest : Multiset P.Site) :=
          Multiset.singleton_add _ _
        _ = (o.site :: OccurrencePath.sites rest : Multiset P.Site) :=
          Multiset.cons_coe _ _
        _ = OccurrencePath.siteBag (.cons o rest) := rfl

theorem bagValuation_tile_invariant
    {P : InteractionPresentation.{uSite, uEvent} theory}
    (indep : SiteIndependence P) :
    IndependenceTile.TileInvariant (indep := indep) (bagValuation P) := by
  intro src tl
  rw [bagValuation_onPath tl.path, bagValuation_onPath tl.pathSwap']
  exact IndependenceTile.bag_survives_swap tl

/-! Grid canary: flip-x and flip-y on `Bool × Bool`. -/

def gridTheory : GSLT where
  Term := Bool × Bool
  equations := ⟨Eq, eq_equivalence⟩
  rewrites := fun p q => q = (!p.1, p.2) ∨ q = (p.1, !p.2)
  rewrites_resp_left := by
    intro p p' q hpq hstep
    exact ⟨q, hpq ▸ hstep, rfl⟩
  rewrites_resp_right := by
    intro p q q' hstep hqq
    exact hqq ▸ hstep

inductive GridSite where
  | horiz
  | vert
  deriving DecidableEq

def gridPresentation : InteractionPresentation gridTheory where
  Site := GridSite
  Event := fun site p q =>
    match site with
    | .horiz => PLift (q = (!p.1, p.2))
    | .vert => PLift (q = (p.1, !p.2))
  sound := by
    intro site p q evidence
    cases site with
    | horiz => exact Or.inl evidence.down
    | vert => exact Or.inr evidence.down

def gridIndep : SiteIndependence gridPresentation where
  indep a b := a ≠ b
  symm := fun _ _ h => h.symm
  irrefl := fun _ h => h rfl

def gridOrigin : gridTheory.Term := (false, false)

def gridHoriz : gridPresentation.Enabled gridOrigin where
  site := .horiz
  target := (true, false)
  evidence := ⟨rfl⟩

def gridVert : gridPresentation.Enabled gridOrigin where
  site := .vert
  target := (false, true)
  evidence := ⟨rfl⟩

def gridHorizThenVert : gridPresentation.Enabled (true, false) where
  site := .vert
  target := (true, true)
  evidence := ⟨rfl⟩

def gridVertThenHoriz : gridPresentation.Enabled (false, true) where
  site := .horiz
  target := (true, true)
  evidence := ⟨rfl⟩

def gridTile : IndependenceTile gridPresentation gridIndep gridOrigin where
  first := gridHoriz
  altFirst := gridVert
  second := gridHorizThenVert
  altSecond := gridVertThenHoriz
  independent := by intro h; cases h
  close := rfl
  sameFirst := rfl
  sameSecond := rfl

theorem grid_eq_iff (a b : gridTheory.Term) :
    gridTheory.Equiv a b ↔ a = b :=
  Iff.rfl

theorem grid_order_sensitive :
    OccurrencePath.sites gridTile.path ≠
      OccurrencePath.sites gridTile.pathSwap := by
  simp [IndependenceTile.path, IndependenceTile.pathSwap,
    IndependenceTile.occFirst, IndependenceTile.occSecond,
    IndependenceTile.occAltFirst, IndependenceTile.occAltSecond,
    OccurrencePath.sites, gridTile, gridHoriz, gridVert,
    gridHorizThenVert, gridVertThenHoriz]
  intro h
  injection h with hhead _
  cases hhead

theorem grid_bag_survives :
    OccurrencePath.siteBag gridTile.path =
      OccurrencePath.siteBag gridTile.pathSwap :=
  IndependenceTile.bag_survives_swap gridTile

theorem grid_not_tile_invariant_sites :
    OccurrencePath.sites gridTile.path ≠
      OccurrencePath.sites gridTile.pathSwap' :=
  grid_order_sensitive

/-! ## 4. History as derived writer cover -/

/-- Bundled occurrence, the generator of the free history monoid. -/
structure AnyOccurrence (P : InteractionPresentation.{uSite, uEvent} theory) where
  source : theory.Term
  target : theory.Term
  occ : Occurrence P source target

/-- Concatenation monoid on occurrence words. Local so it does not orphan a
global `List` instance. -/
local instance listAppendMonoid {α : Type*} : Monoid (List α) where
  mul := List.append
  mul_assoc := List.append_assoc
  one := []
  one_mul := List.nil_append
  mul_one := List.append_nil

/-- Category of elements of `Hom(root, -)`: a path from the origin. -/
structure Element (P : InteractionPresentation.{uSite, uEvent} theory)
    (root : theory.Term) where
  target : theory.Term
  path : OccurrencePath P root target

namespace Element

variable {P : InteractionPresentation.{uSite, uEvent} theory}
  {root : theory.Term}

def forget (e : Element P root) : theory.Term := e.target

/-- A morphism of elements is a continuation whose concatenation recovers
the longer path. -/
structure Hom (e₁ e₂ : Element P root) where
  rest : OccurrencePath P e₁.target e₂.target
  factor : OccurrencePath.append e₁.path rest = e₂.path

namespace Hom

@[ext] theorem ext {e₁ e₂ : Element P root} (f g : Hom e₁ e₂)
    (h : f.rest = g.rest) : f = g := by
  cases f
  cases g
  cases h
  rfl

def id (e : Element P root) : Hom e e where
  rest := .refl e.target
  factor := OccurrencePath.append_refl e.path

def comp {e₁ e₂ e₃ : Element P root} (f : Hom e₁ e₂) (g : Hom e₂ e₃) :
    Hom e₁ e₃ where
  rest := OccurrencePath.append f.rest g.rest
  factor := by
    rw [← OccurrencePath.append_assoc, f.factor, g.factor]

end Hom

instance : Category (Element P root) where
  Hom := Hom
  id := Hom.id
  comp := fun f g => Hom.comp f g
  id_comp := fun f => Hom.ext _ _ (OccurrencePath.refl_append f.rest)
  comp_id := fun f => Hom.ext _ _ (OccurrencePath.append_refl f.rest)
  assoc := fun f g h =>
    Hom.ext _ _ (OccurrencePath.append_assoc f.rest g.rest h.rest)

/-- Discrete fibration: remember only the current term. -/
def forgetFunctor : CategoryTheory.Functor (Element P root) (OccurrenceCat P) where
  obj e := e.target
  map f := f.rest
  map_id := fun _ => rfl
  map_comp := fun _ _ => rfl

def events {s t : theory.Term} : OccurrencePath P s t → List (AnyOccurrence P)
  | .refl _ => []
  | .cons o rest => ⟨_, _, o⟩ :: events rest

theorem events_append {s m t : theory.Term}
    (p : OccurrencePath P s m) (q : OccurrencePath P m t) :
    events (OccurrencePath.append p q) = events p ++ events q := by
  induction p with
  | refl => simp [events, OccurrencePath.append]
  | cons o rest ih => simp [events, OccurrencePath.append, ih]

/-- Writer state: current term and the occurrence word. Not evaluator state;
this is the total space of the cover. -/
def toWriter (e : Element P root) : theory.Term × List (AnyOccurrence P) :=
  (e.target, events e.path)

theorem forget_eq_writer_fst (e : Element P root) :
    e.forget = (toWriter e).1 := rfl

/-- Extending by one occurrence appends exactly that letter. -/
def extend {t : theory.Term} (e : Element P root)
    (o : Occurrence P e.target t) : Element P root :=
  ⟨t, OccurrencePath.append e.path (.cons o (.refl t))⟩

theorem toWriter_extend {t : theory.Term} (e : Element P root)
    (o : Occurrence P e.target t) :
    toWriter (e.extend o) = (t, (toWriter e).2 ++ [⟨e.target, t, o⟩]) := by
  simp [toWriter, extend, events_append, events]

/-- The continuation of `extend` is a morphism of elements. -/
def extendHom {t : theory.Term} (e : Element P root)
    (o : Occurrence P e.target t) : Hom e (e.extend o) where
  rest := .cons o (.refl t)
  factor := rfl

end Element

/-- One-letter grading: a step is an occurrence, the grade is that letter.
Requires discrete equations: events mention source and target, so they
cannot be transported along a nontrivial `Equiv`. -/
def occurrenceGrading (P : InteractionPresentation.{uSite, uEvent} theory)
    (eq_iff : ∀ a b : theory.Term, theory.Equiv a b ↔ a = b) :
    theory.StepSpend (List (AnyOccurrence P)) where
  graded := fun s t v =>
    ∃ o : Occurrence P s t, v = [⟨s, t, o⟩]
  sound := by
    rintro s t v ⟨o, _⟩
    exact o.step
  resp_left := by
    intro s s' t v heq hg
    have hs : s = s' := (eq_iff s s').1 heq
    subst hs
    exact ⟨t, hg, (eq_iff t t).2 rfl⟩
  resp_right := by
    intro s t t' v hg heq
    have ht : t = t' := (eq_iff t t').1 heq
    subst ht
    exact hg

/-- The origin element is the unit of the writer. -/
def originElement (P : InteractionPresentation.{uSite, uEvent} theory)
    (root : theory.Term) : Element P root :=
  ⟨root, .refl root⟩

theorem origin_writer (P : InteractionPresentation.{uSite, uEvent} theory)
    (root : theory.Term) :
    (originElement P root).toWriter = (root, []) := rfl

/-- Extending any element by one occurrence is a `spendLift` step. -/
theorem extend_is_spendLift_step
    (P : InteractionPresentation.{uSite, uEvent} theory)
    (eq_iff : ∀ a b : theory.Term, theory.Equiv a b ↔ a = b)
    {root t : theory.Term} (e : Element P root)
    (o : Occurrence P e.target t) :
    (theory.spendLift (occurrenceGrading P eq_iff)).Step
      (e.toWriter) ((e.extend o).toWriter) := by
  refine ⟨[⟨e.target, t, o⟩], ⟨o, rfl⟩, ?_⟩
  rw [Element.toWriter_extend]
  rfl

/-- Extending the origin by one occurrence is a `spendLift` step from the
unit accumulator. -/
theorem extend_origin_is_spendLift_step
    (P : InteractionPresentation.{uSite, uEvent} theory)
    (eq_iff : ∀ a b : theory.Term, theory.Equiv a b ↔ a = b)
    {root t : theory.Term} (o : Occurrence P root t) :
    (theory.spendLift (occurrenceGrading P eq_iff)).Step
      ((originElement P root).toWriter)
      (((originElement P root).extend o).toWriter) :=
  extend_is_spendLift_step P eq_iff (originElement P root) o

theorem spendLift_erases_occurrence_history
    (P : InteractionPresentation.{uSite, uEvent} theory)
    (eq_iff : ∀ a b : theory.Term, theory.Equiv a b ↔ a = b)
    {s t : theory.Term × List (AnyOccurrence P)}
    (step : (theory.spendLift (occurrenceGrading P eq_iff)).Step s t) :
    theory.Step s.1 t.1 :=
  GSLT.spendLift_erase_step (occurrenceGrading P eq_iff) step

def gridHorizOcc : Occurrence gridPresentation gridOrigin (true, false) :=
  ⟨gridHoriz.site, gridHoriz.evidence⟩

theorem grid_extend_is_spendLift :
    (gridTheory.spendLift (occurrenceGrading gridPresentation grid_eq_iff)).Step
      ((originElement gridPresentation gridOrigin).toWriter)
      (((originElement gridPresentation gridOrigin).extend gridHorizOcc).toWriter) :=
  extend_origin_is_spendLift_step gridPresentation grid_eq_iff gridHorizOcc

theorem grid_spendLift_erases :
    gridTheory.Step
      ((originElement gridPresentation gridOrigin).toWriter).1
      (((originElement gridPresentation gridOrigin).extend gridHorizOcc).toWriter).1 :=
  spendLift_erases_occurrence_history gridPresentation grid_eq_iff
    grid_extend_is_spendLift

#print axioms exact_licences_term_memoization
#print axioms dissipative_term_key_not_support
#print axioms flip_term_key_not_exact
#print axioms term_memoization_iff
#print axioms OccurrenceValuation.toFunctor
#print axioms bagValuation_tile_invariant
#print axioms grid_order_sensitive
#print axioms grid_bag_survives
#print axioms extend_is_spendLift_step
#print axioms grid_extend_is_spendLift
#print axioms grid_spendLift_erases

end Mettapedia.GSLT.Causality.OccurrenceHistory
