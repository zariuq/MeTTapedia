import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsPaths

/-!
# Static traces of paths are trace equivalence of words

The static independence of the candidate step (`AnnotatedRuns.siteIndependence`, the
Mazurkiewicz independence of firings) gives the tile system `EventConcurrency.siteTiles` on the
paths of the run category. Its generated congruence and the Mazurkiewicz trace equivalence of
words agree exactly (`staticTraceEq_iff_traceEquiv`), as the contextual ones do
(`AnnotatedRuns.traceEq_iff_roundEquiv`).

Hence, on the paths from each configuration, every static trace lies inside one contextual trace
(`static_le_contextual`), and strictly: a guard that holds in every solution and a tell form one
contextual trace in their two orders and two static traces
(`StaticPathControls.contextual_strictly_coarser_paths`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns

open Mettapedia.GSLT
open Mettapedia.GSLT.Core.InteractionEvent
open Mettapedia.GSLT.Causality.OccurrenceHistory (OccurrencePath IndependenceTile SiteIndependence)

universe uSite uEvent

/-- The swapped route of an independence tile fires its second event, then its first. -/
theorem tile_pathSwap'_sites {theory : GSLT} {P : InteractionPresentation.{uSite, uEvent} theory}
    {indep : SiteIndependence P} {s : theory.Term} (tile : IndependenceTile P indep s) :
    OccurrencePath.sites tile.pathSwap' = [tile.second.site, tile.first.site] := by
  rw [tile.sites_pathSwap']
  change [tile.altFirst.site, tile.altSecond.site] = _
  rw [tile.sameSecond, ← tile.sameFirst]

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns

open Mettapedia.GSLT.Causality.OccurrenceHistory (OccurrencePath IndependenceTile)
open Mettapedia.GSLT.Causality.EventConcurrency (TraceEq Trace siteTiles)
open Mettapedia.GSLT.Distinction.CausalGluing (TraceEquiv Swap)
open GuardFreeProcessOrders (SameUpTo)

universe uT uS uO
variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]

section Static

variable (A : SubstitutionAction T S) (label : O → T)

theorem executable_suffix : ∀ (C : Configuration T O) (u v : List (Firing T S O)),
    Executable A label C (u ++ v) → Executable A label (follow label C u) v
  | _, [], _, executable => executable
  | _, _ :: u, v, executable => executable_suffix _ u v executable.2

/-- The route of a static tile fires its first firing, then its second. -/
theorem staticRoute_sites {x : (theory A label).Term}
    (square : IndependenceTile (presentation A label) (siteIndependence A label) x) :
    OccurrencePath.sites ((siteTiles (siteIndependence A label)).route square) =
      [square.first.site, square.second.site] := rfl

/-- The swapped route of a static tile fires its second firing, then its first. -/
theorem staticSwapped_sites {x : (theory A label).Term}
    (square : IndependenceTile (presentation A label) (siteIndependence A label) x) :
    OccurrencePath.sites ((siteTiles (siteIndependence A label)).swapped square) =
      [square.second.site, square.first.site] :=
  tile_pathSwap'_sites square

/-- **Statically trace-equivalent paths have trace-equivalent words.** -/
theorem traceEquiv_of_staticTraceEq {x y : (theory A label).Term}
    {p q : OccurrencePath (presentation A label) x y}
    (related : TraceEq (siteTiles (siteIndependence A label)) p q) :
    TraceEquiv (MazurkiewiczIndependent label) (OccurrencePath.sites p) (OccurrencePath.sites q) := by
  induction related with
  | refl _ => exact .refl _
  | symm _ ih => exact .symm _ _ ih
  | trans _ _ first second => exact .trans _ _ _ first second
  | tile square =>
      have independent : MazurkiewiczIndependent label square.first.site square.second.site :=
        square.sameSecond ▸ square.independent
      have swap : TraceEquiv (MazurkiewiczIndependent label) [square.first.site, square.second.site]
          [square.second.site, square.first.site] :=
        .rel _ _ (Swap.swap [] [] independent)
      exact (staticRoute_sites A label square).symm ▸ (staticSwapped_sites A label square).symm ▸ swap
  | cong_left pre _ ih =>
      exact (OccurrencePath.sites_append _ _).symm ▸ (OccurrencePath.sites_append _ _).symm ▸
        Mettapedia.GSLT.Distinction.CausalGluing.TraceEquiv.append_left _ ih
  | cong_right post _ ih =>
      exact (OccurrencePath.sites_append _ _).symm ▸ (OccurrencePath.sites_append _ _).symm ▸
        Mettapedia.GSLT.Distinction.CausalGluing.TraceEquiv.append_right _ ih

/-- **Trace-equivalent runs are statically trace-equivalent paths.** -/
theorem staticTraceEq_of_traceEquiv {C : Configuration T O} {w w' : List (Firing T S O)}
    (equivalent : TraceEquiv (MazurkiewiczIndependent label) w w') :
    Executable A label C w → ∀ {y : (theory A label).Term}
      (p q : OccurrencePath (presentation A label) (classOf A label C) y),
      OccurrencePath.sites p = w → OccurrencePath.sites q = w' →
        TraceEq (siteTiles (siteIndependence A label)) p q := by
  induction equivalent with
  | rel _ _ swapped =>
      cases swapped with
      | @swap u v f g independent =>
          intro executable y p q pSites qSites
          obtain ⟨m, p₁, p₂, rfl, p₁Sites, p₂Sites⟩ := split A label p u _ pSites
          obtain ⟨m', q₁, q₂, rfl, q₁Sites, q₂Sites⟩ := split A label q u _ qSites
          have middle : m = classOf A label (follow label C u) :=
            p₁Sites ▸ target_eq A label p₁ C rfl
          have middle' : m' = classOf A label (follow label C u) :=
            q₁Sites ▸ target_eq A label q₁ C rfl
          subst middle
          subst middle'
          obtain rfl := path_ext A label p₁ q₁ (p₁Sites.trans q₁Sites.symm)
          refine TraceEq.cong_left p₁ ?_
          obtain ⟨fValid, gValid, _⟩ := executable_suffix A label C u _ executable
          obtain ⟨m₂, p₃, s, rfl, p₃Sites, sSites⟩ := split A label p₂ [f, g] v p₂Sites
          have after : m₂ = classOf A label (follow label (follow label C u) [f, g]) :=
            p₃Sites ▸ target_eq A label p₃ (follow label C u) rfl
          subst after
          have firstRoute : p₃ = (siteTiles (siteIndependence A label)).route
              (tile A label independent fValid gValid) :=
            path_ext A label _ _
              (p₃Sites.trans (staticRoute_sites A label (tile A label independent fValid gValid)).symm)
          subst firstRoute
          have secondRoute : q₂ = OccurrencePath.append
              ((siteTiles (siteIndependence A label)).swapped (tile A label independent fValid gValid)) s := by
            refine path_ext A label _ _ (q₂Sites.trans (Eq.trans ?_ (OccurrencePath.sites_append _ _).symm))
            exact (congrArg (fun l => g :: f :: l) sSites.symm).trans
              (congrArg (· ++ OccurrencePath.sites s)
                (staticSwapped_sites A label (tile A label independent fValid gValid)).symm)
          subst secondRoute
          exact TraceEq.cong_right s
            (.tile (T := siteTiles (siteIndependence A label)) (tile A label independent fValid gValid))
  | refl _ =>
      intro _ y p q pSites qSites
      obtain rfl := path_ext A label p q (pSites.trans qSites.symm)
      exact .refl _
  | symm _ _ first ih =>
      intro executable y p q pSites qSites
      exact .symm (ih ((mazurkiewicz_executable A label first C).1.mpr executable) q p qSites pSites)
  | trans _ middleWord _ first second ih₁ ih₂ =>
      intro executable y p q pSites qSites
      have middleRuns := (mazurkiewicz_executable A label first C).1.mp executable
      have ends : classOf A label (follow label C middleWord) = y := by
        have atEnd := target_eq A label p C rfl
        rw [pSites] at atEnd
        exact ((Quotient.sound ((mazurkiewicz_executable A label first C).2 executable)).symm.trans
          atEnd.symm : _)
      obtain ⟨r, rSites⟩ := exists_path A label C middleWord middleRuns y ends
      exact .trans (ih₁ executable p r pSites rSites) (ih₂ middleRuns r q rSites qSites)

/-- **Path-level static traces are word-level trace equivalence.** -/
theorem staticTraceEq_iff_traceEquiv {C : Configuration T O} {y : (theory A label).Term}
    (p q : OccurrencePath (presentation A label) (classOf A label C) y) :
    TraceEq (siteTiles (siteIndependence A label)) p q ↔
      TraceEquiv (MazurkiewiczIndependent label) (OccurrencePath.sites p) (OccurrencePath.sites q) := by
  refine ⟨traceEquiv_of_staticTraceEq A label, fun equivalent => ?_⟩
  by_cases consistent : A.Consistent C.equations
  · exact staticTraceEq_of_traceEquiv A label equivalent
      (executable_of_path A label p C rfl consistent) p q rfl rfl
  · have pNil := sites_eq_nil_of_inconsistent A label p C rfl consistent
    have qNil := sites_eq_nil_of_inconsistent A label q C rfl consistent
    obtain rfl := path_ext A label p q (pNil.trans qNil.symm)
    exact .refl _

/-- **Every static trace lies inside one contextual trace.** -/
theorem static_le_contextual {C : Configuration T O} {y : (theory A label).Term}
    {p q : OccurrencePath (presentation A label) (classOf A label C) y}
    (related : TraceEq (siteTiles (siteIndependence A label)) p q) :
    TraceEq (concurrency A label).tiles p q := by
  have words := traceEquiv_of_staticTraceEq A label related
  by_cases consistent : A.Consistent C.equations
  · have runs := executable_of_path A label p C rfl consistent
    exact (traceEq_iff_roundEquiv A label p q).mpr
      (traceEquiv_roundEquiv A label ((traceEquiv_irreflexive_iff label).mp words) C runs)
  · have pNil := sites_eq_nil_of_inconsistent A label p C rfl consistent
    have qNil := sites_eq_nil_of_inconsistent A label q C rfl consistent
    obtain rfl := path_ext A label p q (pNil.trans qNil.symm)
    exact .refl _

end Static

/-! ## Controls -/

namespace StaticPathControls

open Mettapedia.Logic.LP
open ConstraintMultisetRewriting.Controls (signature A)
open AnnotatedRuns.Controls (label Run teller)
open AnnotatedRuns.RoundControls (trivialAsker teller_trivialAsker_round contextual_strictly_coarser)

/-- **Negative control: the contextual traces of paths are strictly coarser than the static ones.**
The tell `X = 1` and the guard `Y = Y` form a round. Their two orders are two paths with one
source and one target, one contextual trace and two static traces. -/
theorem contextual_strictly_coarser_paths :
    ∃ p q : OccurrencePath (presentation A label) (classOf A label AnnotatedRuns.Controls.empty)
      (classOf A label (follow label AnnotatedRuns.Controls.empty [teller, trivialAsker])),
      OccurrencePath.sites p = [teller, trivialAsker] ∧
        OccurrencePath.sites q = [trivialAsker, teller] ∧
        TraceEq (concurrency A label).tiles p q ∧
        ¬ TraceEq (siteTiles (siteIndependence A label)) p q := by
  obtain ⟨p, pSites⟩ := exists_path A label AnnotatedRuns.Controls.empty _
    (teller_trivialAsker_round.executable A label) _ rfl
  obtain ⟨q, qSites⟩ := exists_path A label AnnotatedRuns.Controls.empty [trivialAsker, teller]
    (teller_trivialAsker_round.executable_perm A label (List.Perm.swap _ _ [])) _
    (Quotient.sound (teller_trivialAsker_round.follow_perm A label (List.Perm.swap _ _ [])))
  refine ⟨p, q, pSites, qSites, ?_, fun static => ?_⟩
  · refine (traceEq_iff_roundEquiv A label p q).mpr ?_
    exact pSites.symm ▸ qSites.symm ▸ contextual_strictly_coarser.1
  · have words := (staticTraceEq_iff_traceEquiv A label p q).mp static
    have words' := cast (congrArg (fun l : List Run =>
      TraceEquiv (MazurkiewiczIndependent label) l (OccurrencePath.sites q)) pSites) words
    have words'' := cast (congrArg (TraceEquiv (MazurkiewiczIndependent label)
      [teller, trivialAsker]) qSites) words'
    exact contextual_strictly_coarser.2 ((traceEquiv_irreflexive_iff label).mp words'')

end StaticPathControls

#print axioms tile_pathSwap'_sites
#print axioms staticRoute_sites
#print axioms staticSwapped_sites
#print axioms traceEquiv_of_staticTraceEq
#print axioms staticTraceEq_of_traceEquiv
#print axioms staticTraceEq_iff_traceEquiv
#print axioms static_le_contextual
#print axioms StaticPathControls.contextual_strictly_coarser_paths

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns
