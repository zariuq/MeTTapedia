import Mettapedia.Languages.GF.OSLFBridge
import Mettapedia.Languages.GF.English.InterfaceContrast
import Mettapedia.OSLF.Framework.TypeSynthesis

/-!
# GF Interface Refinement and Quotient Maps

Interface-level theorem bundle for:
1. refinement of observational equivalences via interface factorization;
2. canonical quotient map induced by that refinement;
3. LF-only vs LF+PF distinction in a general (relation-level) form.

Conceptual source note:
- Interface-refinement framing follows the TUG/Hyperseed perspective:
  finer interfaces preserve more distinctions; coarser interfaces collapse them.
-/

namespace Mettapedia.Languages.GF.English.InterfaceRefinement

open Mettapedia.Languages.GF
open Mettapedia.Languages.GF.Abstract
open Mettapedia.Languages.GF.OSLFBridge
open Mettapedia.Languages.GF.English.Linearization
open Mettapedia.Languages.GF.English.InterfaceContrast
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.MeTTaIL.Syntax

/-! ## Generic interface refinement and quotient map -/

/-- Observational equivalence induced by an observation map. -/
def ObsEq {α β : Type*} (obs : α → β) : α → α → Prop :=
  fun x y => obs x = obs y

/-- Setoid induced by an observation map. -/
def obsSetoid {α β : Type*} (obs : α → β) : Setoid α where
  r := ObsEq obs
  iseqv := by
    constructor
    · intro x
      rfl
    · intro x y hxy
      exact hxy.symm
    · intro x y z hxy hyz
      exact hxy.trans hyz

/-- If a coarse interface factors through a finer one, then fine-observation
equivalence refines coarse-observation equivalence. -/
theorem obsEq_refines_of_factor
    {α βFine βCoarse : Type*}
    (obsFine : α → βFine) (obsCoarse : α → βCoarse)
    (project : βFine → βCoarse)
    (hfactor : ∀ x, obsCoarse x = project (obsFine x))
    {x y : α} :
    ObsEq obsFine x y → ObsEq obsCoarse x y := by
  intro hxy
  unfold ObsEq at hxy ⊢
  rw [hfactor x, hfactor y, hxy]

/-- Canonical map from the finer-interface quotient to the coarser-interface
quotient induced by interface factorization. -/
def quotientMap_of_refinement
    {α βFine βCoarse : Type*}
    (obsFine : α → βFine) (obsCoarse : α → βCoarse)
    (project : βFine → βCoarse)
    (hfactor : ∀ x, obsCoarse x = project (obsFine x)) :
    Quotient (obsSetoid obsFine) → Quotient (obsSetoid obsCoarse) :=
  Quotient.lift
    (fun x => Quotient.mk (obsSetoid obsCoarse) x)
    (by
      intro x y hxy
      exact Quotient.sound
        (obsEq_refines_of_factor obsFine obsCoarse project hfactor hxy))

/-- The canonical quotient map induced by interface refinement is surjective. -/
theorem quotientMap_of_refinement_surjective
    {α βFine βCoarse : Type*}
    (obsFine : α → βFine) (obsCoarse : α → βCoarse)
    (project : βFine → βCoarse)
    (hfactor : ∀ x, obsCoarse x = project (obsFine x)) :
    Function.Surjective
      (quotientMap_of_refinement obsFine obsCoarse project hfactor) := by
  intro q
  refine Quotient.inductionOn q ?_
  intro x
  exact ⟨Quotient.mk (obsSetoid obsFine) x, rfl⟩

/-- Quotient maps induced by interface refinement compose.
Refining in two steps and forgetting in two steps is extensionally identical
to forgetting in one composed step. -/
theorem quotientMap_of_refinement_comp
    {α β1 β2 β3 : Type*}
    (obs1 : α → β1) (obs2 : α → β2) (obs3 : α → β3)
    (p12 : β1 → β2) (p23 : β2 → β3)
    (h12 : ∀ x, obs2 x = p12 (obs1 x))
    (h23 : ∀ x, obs3 x = p23 (obs2 x)) :
    quotientMap_of_refinement obs1 obs3 (p23 ∘ p12)
        (by
          intro x
          calc
            obs3 x = p23 (obs2 x) := h23 x
            _ = p23 (p12 (obs1 x)) := by rw [h12 x]
            _ = (p23 ∘ p12) (obs1 x) := rfl)
      =
    (quotientMap_of_refinement obs2 obs3 p23 h23) ∘
      (quotientMap_of_refinement obs1 obs2 p12 h12) := by
  funext q
  refine Quotient.inductionOn q ?_
  intro x
  rfl

/-! ## LF-only vs LF+PF interfaces (function-equality layer) -/

/-- LF-only observation (abstract tree to pattern). -/
def lfObs (t : AbstractNode) : Pattern :=
  gfAbstractToPattern t

/-- LF+PF observation (pattern + linearized English surface form). -/
def lfPfObs (t : AbstractNode) : Pattern × String :=
  (gfAbstractToPattern t, linearizeTree {} t .Nom .Sg)

/-- Interface factorization: LF is the first projection of LF+PF. -/
theorem lf_factor_through_lfpf (t : AbstractNode) :
    lfObs t = (lfPfObs t).1 := rfl

/-- Fine LF+PF equality implies coarse LF-only equality. -/
theorem lfpf_refines_lf
    {t1 t2 : AbstractNode} :
    ObsEq lfPfObs t1 t2 → ObsEq lfObs t1 t2 :=
  obsEq_refines_of_factor lfPfObs lfObs Prod.fst lf_factor_through_lfpf

/-- Canonical quotient map from LF+PF classes to LF-only classes. -/
def lfpf_to_lf_quotient_map :
    Quotient (obsSetoid lfPfObs) → Quotient (obsSetoid lfObs) :=
  quotientMap_of_refinement lfPfObs lfObs Prod.fst lf_factor_through_lfpf

/-- The LF+PF→LF quotient map is surjective. -/
theorem lfpf_to_lf_quotient_map_surjective :
    Function.Surjective lfpf_to_lf_quotient_map :=
  quotientMap_of_refinement_surjective lfPfObs lfObs Prod.fst lf_factor_through_lfpf

/-! ## LF-only vs LF+PF (relation-level theorem family) -/

/-- LF-only interface as consequence in the GF reduction relation. -/
def LFOnlyConsequence (t1 t2 : AbstractNode) : Prop :=
  langReduces gfRGLLanguageDef (gfAbstractToPattern t1) (gfAbstractToPattern t2)

/-- LF+PF interface: LF-only consequence plus PF identity. -/
def LFPFConsequence (t1 t2 : AbstractNode) : Prop :=
  LFOnlyConsequence t1 t2 ∧
  linearizeTree {} t1 .Nom .Sg = linearizeTree {} t2 .Nom .Sg

/-- LF+PF consequence implies LF-only consequence. -/
theorem lfpf_consequence_refines_lf
    {t1 t2 : AbstractNode} :
    LFPFConsequence t1 t2 → LFOnlyConsequence t1 t2 :=
  And.left

/-- If PF distinguishes two trees, they cannot be equivalent under LF+PF
even when LF-only consequence holds. -/
theorem lf_only_with_pf_distinct_not_lfpf
    {t1 t2 : AbstractNode}
    (_hlf : LFOnlyConsequence t1 t2)
    (hpf : linearizeTree {} t1 .Nom .Sg ≠ linearizeTree {} t2 .Nom .Sg) :
    ¬ LFPFConsequence t1 t2 := by
  intro h
  exact hpf h.2

/-- Concrete bridge: the active/passive witness instantiates the general
LF-only vs LF+PF distinction theorem family. -/
theorem active_passive_instantiates_interface_distinction :
    LFOnlyConsequence activeClause passiveClause ∧
    ¬ LFPFConsequence activeClause passiveClause := by
  refine ⟨?_, ?_⟩
  · simpa [LFOnlyConsequence] using active_reduces_to_passive
  · exact lf_only_with_pf_distinct_not_lfpf
      (t1 := activeClause) (t2 := passiveClause)
      (by simpa [LFOnlyConsequence] using active_reduces_to_passive)
      active_pf_string_ne_passive_pf_string

/-- Certified-bridge variant:
if runtime PF linearization agrees with the total certified surface procedure on
the active/passive witness pair, the same LF-only vs LF+PF distinction follows
without invoking reflective execution for the PF inequality step. -/
theorem active_passive_instantiates_interface_distinction_of_certified_bridge
    (hActive :
      linearizeTree {} activeClause .Nom .Sg = activeSurfaceCertified)
    (hPassive :
      linearizeTree {} passiveClause .Nom .Sg = passiveSurfaceCertified) :
    LFOnlyConsequence activeClause passiveClause ∧
    ¬ LFPFConsequence activeClause passiveClause := by
  refine ⟨?_, ?_⟩
  · simpa [LFOnlyConsequence] using active_reduces_to_passive
  · exact lf_only_with_pf_distinct_not_lfpf
      (t1 := activeClause) (t2 := passiveClause)
      (by simpa [LFOnlyConsequence] using active_reduces_to_passive)
      (active_pf_string_ne_passive_pf_string_of_certified_bridge hActive hPassive)

end Mettapedia.Languages.GF.English.InterfaceRefinement
