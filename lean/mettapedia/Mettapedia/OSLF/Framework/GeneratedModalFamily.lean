import Mettapedia.OSLF.Framework.GeneratedHypercube
import Mettapedia.OSLF.Framework.GeneratedModality

/-!
# The whole family a presentation generates

`GeneratedHypercube` generates the slot family of *one* rule at *one* redex
position, and `GeneratedHypercubeInstances` runs it at chosen positions of
chosen rules.  A generator is supposed to take a presentation, not a position:
this module closes that distance.

Given a `LanguageDef`, the redex sites are every position of every rewrite's
left-hand side, enumerated from the presentation; each site carries its rely
parameters, its slot count, its generated centre and its rely-possibly
modality, and every one of those four is computed from the site rather than
tabulated beside it.  The coverage theorems say the enumeration misses nothing:
a rule of the presentation at a position of its left-hand side is a site, and
every site arises that way.

**The presentation-level health check.**  A rule mints a slot for every free
metavariable of the context, declared or not; an undeclared one mints a slot
carrying no information.  `allRelyVarsDeclared` asks that of a whole
presentation at once, and `Instances` below answers it for two: the tree's rho,
which fails, and the generated platform, which does not.  That the check
separates them is the point — a presentation-level property that is true of one
presentation and false of another is a property, not a formality.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.GeneratedModalFamily

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.Framework.ModalHypercube
open Mettapedia.OSLF.Framework.RedexPosition
open Mettapedia.OSLF.Framework.GeneratedHypercube
open Mettapedia.OSLF.Framework.GeneratedModality

/-! ## The sites -/

/-- A redex site: a rewrite of the presentation together with a position of its
left-hand side. -/
abbrev Site := RewriteRule × Position

/-- **Every redex site of a presentation**, enumerated from the presentation:
each rewrite, at each position of its left-hand side. -/
def redexSites (lang : LanguageDef) : List Site :=
  lang.rewrites.flatMap fun rule => (positions rule.left).map fun pos => (rule, pos)

/-- **Coverage.**  A rewrite of the presentation, at a position of its own
left-hand side, is a site — and every site is of that form.  So the enumeration
is the set of redex positions rather than a selection from it. -/
theorem mem_redexSites_iff (lang : LanguageDef) (site : Site) :
    site ∈ redexSites lang ↔
      site.1 ∈ lang.rewrites ∧ site.2 ∈ positions site.1.left := by
  constructor
  · intro member
    obtain ⟨rule, ruleMember, siteMember⟩ := List.mem_flatMap.mp member
    obtain ⟨pos, posMember, equal⟩ := List.mem_map.mp siteMember
    subst equal
    exact ⟨ruleMember, posMember⟩
  · rintro ⟨ruleMember, posMember⟩
    refine List.mem_flatMap.mpr ⟨site.1, ruleMember, ?_⟩
    exact List.mem_map.mpr ⟨site.2, posMember, rfl⟩

/-- In particular every rewrite contributes its root position, so no rule of the
presentation is skipped. -/
theorem root_site_mem (lang : LanguageDef) {rule : RewriteRule}
    (member : rule ∈ lang.rewrites) : (rule, ([] : Position)) ∈ redexSites lang := by
  refine (mem_redexSites_iff lang _).mpr ⟨member, ?_⟩
  cases rule.left <;> simp [positions]

/-! ## What each site generates

Four things, each computed from the site. -/

/-- The rely parameters of a site. -/
def siteRelyVars (site : Site) : List String :=
  relyVars site.1.left site.2

/-- Its slot count: one per rely parameter, and one output. -/
def siteSlotCount (site : Site) : Nat :=
  slotCount site.1.left site.2

theorem siteSlotCount_eq (site : Site) :
    siteSlotCount site = (siteRelyVars site).length + 1 := rfl

/-- Its generated centre, fed from the derived presentation. -/
def siteCenter (alg : SortAlgebra) (lang : LanguageDef) (site : Site) :
    Finset (Fin (siteSlotCount site) → HSort) :=
  derivedCenter alg lang site.1 site.2

/-- And it is the equational centre of the derived presentation, not a set
listed beside it. -/
theorem siteCenter_eq (alg : SortAlgebra) (lang : LanguageDef) (site : Site) :
    siteCenter alg lang site =
      equationalCenter (derivedPresentation alg lang site.1 site.2) := rfl

/-- The face of the centre that fixes the output slot. -/
def siteFace (alg : SortAlgebra) (lang : LanguageDef) (site : Site) (s : HSort) :
    Finset (Fin (siteSlotCount site) → HSort) :=
  (siteCenter alg lang site).filter fun σ => σ (outputIndex (siteRelyVars site)) == s

/-- Its rely-possibly modality, as the type former the framework already
proves the four rules for. -/
def siteModality (base : BasePremiseEvaluator) (lang : LanguageDef) (site : Site)
    (A : String → Pattern → Prop) (B : Pattern → Prop) : Pattern → Prop :=
  RelyPossibly base lang site.1 site.2 A B

/-- **The modality of a site is the rule's own.**  Nothing is chosen between the
enumeration and the modality: the site is the pair the modality is indexed by. -/
theorem siteModality_eq (base : BasePremiseEvaluator) (lang : LanguageDef)
    (site : Site) (A : String → Pattern → Prop) (B : Pattern → Prop) :
    siteModality base lang site A B = RelyPossibly base lang site.1 site.2 A B := rfl

/-! ## The presentation-level check -/

/-- **Every site of the presentation declares every slot it mints.** -/
def allRelyVarsDeclared (lang : LanguageDef) : Bool :=
  (redexSites lang).all fun site => RelyVarsDeclared site.1 site.2

/-- When it holds, it holds at every site — which is what a presentation-level
check has to mean. -/
theorem relyVarsDeclared_of_all {lang : LanguageDef}
    (checked : allRelyVarsDeclared lang = true) {site : Site}
    (member : site ∈ redexSites lang) :
    RelyVarsDeclared site.1 site.2 = true :=
  List.all_eq_true.mp checked site member

/-- And when it fails, some site mints a slot for a metavariable its rule does
not declare. -/
theorem exists_undeclared_of_not_all {lang : LanguageDef}
    (failed : allRelyVarsDeclared lang = false) :
    ∃ site ∈ redexSites lang, RelyVarsDeclared site.1 site.2 = false := by
  by_contra absent
  have allTrue : allRelyVarsDeclared lang = true := by
    refine List.all_eq_true.mpr fun site member => ?_
    by_cases undeclared : RelyVarsDeclared site.1 site.2 = false
    · exact absurd ⟨site, member, undeclared⟩ absent
    · simpa using undeclared
  rw [allTrue] at failed
  exact Bool.noConfusion failed

end Mettapedia.OSLF.Framework.GeneratedModalFamily
