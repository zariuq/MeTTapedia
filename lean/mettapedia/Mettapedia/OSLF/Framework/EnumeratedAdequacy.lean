import Mettapedia.OSLF.Framework.LanguageIndexedModalFunctor
import Mettapedia.OSLF.Framework.FormulaAdequacy
import Mettapedia.OSLF.Framework.HennessyMilnerNativeTypes
import Mettapedia.GSLT.Logic.MinimalEnablingContext

/-!
# Image-finiteness from a successor-class enumeration

Every Hennessy–Milner adequacy theorem in this development carries
image-finiteness modulo the equations as a hypothesis.  A finite
successor-class enumeration, the runtime contract of a quotient endpoint,
discharges that hypothesis for every labeled system whose labeled steps are
steps of the theory from a term determined by the label: the unlabeled
forward system, the context-labeled systems (interface contexts and
least-enabling contexts alike), and hence the OSLF box-free fragment and the
context-decorated formula language.  Adequacy for such a theory is therefore
unconditional once its stepper is proved complete.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.EnumeratedAdequacy

open Mettapedia.GSLT
open Mettapedia.GSLT.HennessyMilner
open Mettapedia.GSLT.MinimalEnablingContext
open Mettapedia.OSLF.Framework.LanguageIndexedModalFunctor.EffectiveStructure
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.OSLF.Framework.ConcreteHennessyMilnerBridge
open Mettapedia.OSLF.Framework.HennessyMilnerNativeTypes
open Mettapedia.OSLF.Formula.Adequacy

universe uTerm uAtom uLabel uContext uRule

variable {S : GSLT.{uTerm}}

/-- A labeled system whose steps are theory steps from a label-determined
term is image-finite modulo the equations whenever the theory has a finite
successor-class enumeration. -/
theorem imageFiniteModulo_of_enumeration (M : System.{uAtom, uLabel} S)
    (enumeration : SuccessorClassEnumeration S) (plug : M.Label → S.Term → S.Term)
    (act_step : ∀ {label : M.Label} {source target : S.Term},
      M.act label source target → S.Step (plug label source) target) :
    M.ImageFiniteModulo := by
  intro label term
  refine ⟨{ target | target ∈ enumeration.successors (plug label term) },
    List.finite_toSet _, ?_⟩
  intro target step
  obtain ⟨representative, member, equivalent⟩ :=
    enumeration.complete (plug label term) target (act_step step)
  exact ⟨representative, member, equivalent⟩

/-! ## The forward system and the OSLF box-free fragment -/

theorem forwardSystem_imageFiniteModulo (enumeration : SuccessorClassEnumeration S)
    (I : String → EquationPredicate S) : (forwardSystem S I).ImageFiniteModulo :=
  imageFiniteModulo_of_enumeration (forwardSystem S I) enumeration (fun _ term => term)
    (fun step => step)

/-- Box-free OSLF equivalence is bisimilarity, unconditionally, for a theory
with a finite successor-class enumeration. -/
theorem forwardEquivalent_iff_bisimilar_of_enumeration
    (enumeration : SuccessorClassEnumeration S) (I : String → EquationPredicate S)
    (left right : S.Term) :
    ForwardEquivalent S I left right ↔ (forwardSystem S I).Bisimilar left right :=
  Mettapedia.OSLF.Formula.Adequacy.forwardEquivalent_iff_bisimilar S I
    (forwardSystem_imageFiniteModulo enumeration I) left right

/-- The same statement through the generated native types of the forward
formula language. -/
theorem forwardFormulaNativeTypes_equivalent_iff_bisimilar
    (enumeration : SuccessorClassEnumeration S) (I : String → EquationPredicate S)
    (left right : S.Term) :
    (∀ formula : Formula String Unit,
      ((gsltOSLF S).satisfies (S := ()) left
          (formulaNativeType (forwardSystem S I) formula).pred ↔
       (gsltOSLF S).satisfies (S := ()) right
          (formulaNativeType (forwardSystem S I) formula).pred)) ↔
      (forwardSystem S I).Bisimilar left right :=
  formulaNativeTypes_equivalent_iff_bisimilar (forwardSystem S I)
    (forwardSystem_imageFiniteModulo enumeration I) left right

/-! ## Context-labeled systems -/

/-- The interface-context system is image-finite modulo the equations. -/
theorem contextual_imageFiniteModulo [HasMinimalContexts S] (plugResp : PlugRespectsEquiv S)
    (enumeration : SuccessorClassEnumeration S) :
    (contextual (⟨PEmpty, fun atom _ => atom.elim⟩ : ObservedGSLT.{0} S)
      (fun atom => atom.elim) plugResp).ImageFiniteModulo :=
  imageFiniteModulo_of_enumeration _ enumeration (fun K term => K.plug term) (fun step => step)

/-- Context-decorated adequacy, unconditionally, for a theory with a finite
successor-class enumeration. -/
theorem contextBisimilar_iff_hmlEquiv_of_enumeration [HasMinimalContexts S]
    (plugResp : PlugRespectsEquiv S) (enumeration : SuccessorClassEnumeration S)
    (left right : S.Term) :
    contextBisimilar plugResp left right ↔ HMLFormula.hmlEquiv S left right :=
  contextBisimilar_iff_hmlEquiv plugResp (contextual_imageFiniteModulo plugResp enumeration)
    left right

/-- The least-enabling-context system is image-finite modulo the equations. -/
theorem leastEnabler_imageFiniteModulo (rules : ContextualRules.{uContext, uRule} S)
    (observations : ContextualRules.Observations.{uAtom} S)
    (enumeration : SuccessorClassEnumeration S) :
    (rules.hmlSystem observations).ImageFiniteModulo :=
  imageFiniteModulo_of_enumeration _ enumeration (fun context source => rules.plug context source)
    (fun act => rules.act_step act)

#print axioms imageFiniteModulo_of_enumeration
#print axioms forwardEquivalent_iff_bisimilar_of_enumeration
#print axioms contextBisimilar_iff_hmlEquiv_of_enumeration
#print axioms leastEnabler_imageFiniteModulo

end Mettapedia.OSLF.Framework.EnumeratedAdequacy
