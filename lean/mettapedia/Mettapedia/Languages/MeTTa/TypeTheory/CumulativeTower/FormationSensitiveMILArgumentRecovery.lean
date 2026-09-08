import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.FormationSensitiveTelescopeSpine
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.FormationSensitiveMILEliminationIota
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.FormationSensitivePreservationInstances

/-!
# Dependent argument recovery for the native hypothesis eliminator

The generic declaration-telescope theorem recovers the actual parameters,
indices and constructor fields from arbitrary formation-sensitive typings.
No assumption that the input was produced by canonical quotation is made.
Pi conversion qualification for the native iota package remains explicit;
the theorem does not infer it from separately formed rule endpoints.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
namespace FormationSensitiveMILArgumentRecovery

open Presentation Presentation.Declaration IntrinsicMILHypothesis
open FormationSensitive (DeclarationSpine ContextFormation)
open FormationSensitiveMIL (Typing)

variable {n : Nat}

def universes : FormationSensitive.UniverseRegularity rules :=
  FormationSensitive.towerUniverseRegularity.includeSignature rawSignature

def parameterSubstitution (sorts primitives motive primitiveCase chainCase : Tower.Tm n) :
    Sub Tower.Head 5 n :=
  consSub chainCase (consSub primitiveCase (consSub motive
    (consSub primitives (consSub sorts Fin.elim0))))

def eliminatorContext : Tower.Ctx 8 :=
  .snoc contextSPMPCSourceTarget
    (hypothesisApp (.var 6) (.var 5) (.var 1) (.var 0))

def eliminatorResult : Tower.Tm 8 := motiveApp (.var 5) (.var 2) (.var 1) (.var 0)

def eliminatorSubstitution
    (sorts primitives motive primitiveCase chainCase source target hypothesis : Tower.Tm n) :
    Sub Tower.Head 8 n :=
  consSub hypothesis (consSub target (consSub source
    (parameterSubstitution sorts primitives motive primitiveCase chainCase)))

theorem eliminateSpine (context : Tower.Ctx n) :
    DeclarationSpine rules context (.const eliminateName) (liftClosed eliminateType) := by
  apply DeclarationSpine.constant (u := .sort eliminateDeclarationLevel)
  · exact combinedType_of_signature Tower.rules rawSignature rfl typeOf_eliminate
  · exact FormationSensitiveMILElimination.eliminateType_hasType
  · exact .sort _

/-- Common inversion, independent of the hypothesis constructor. The
returned replay uses the original observed result and all its adjustments. -/
theorem eliminateArguments (boundary : PiConversionBoundary rules)
    {context : Tower.Ctx n} (formed : ContextFormation rules context)
    {sorts primitives motive primitiveCase chainCase source target hypothesis displayed : Tower.Tm n}
    (observed : Typing context
      (eliminateApp sorts primitives motive primitiveCase chainCase source target hypothesis)
      displayed) :
    FormationSensitive.CtxMor rules contextSPMPrimitiveChain context
        (parameterSubstitution sorts primitives motive primitiveCase chainCase) ∧
      Typing context source sorts ∧ Typing context target sorts ∧
      Typing context hypothesis (hypothesisApp sorts primitives source target) ∧
      (∀ {replacement}, Typing context replacement (motiveApp motive source target hypothesis) →
        Typing context replacement displayed) := by
  obtain ⟨typed, _, _, replay⟩ := DeclarationSpine.recoverTelescope universes boundary formed
    eliminatorContext eliminatorResult
    (eliminatorSubstitution sorts primitives motive primitiveCase chainCase source target hypothesis)
    (eliminateSpine context) observed
  have parameters := typed.dropNewest.dropNewest.dropNewest
  have sourceTyped := typed (2 : Fin 8)
  have targetTyped := typed (1 : Fin 8)
  have hypothesisTyped := typed (0 : Fin 8)
  exact ⟨parameters, sourceTyped, targetTyped, hypothesisTyped, replay⟩

def primitiveContext : Tower.Ctx 5 :=
  .snoc (.snoc (.snoc contextSP (.var 1)) (.var 2))
    (.app (.app (.var 2) (.var 1)) (.var 0))

def primitiveResult : Tower.Tm 5 :=
  hypothesisApp (.var 4) (.var 3) (.var 2) (.var 1)

def primitiveSubstitution (sorts primitives source target symbol : Tower.Tm n) :
    Sub Tower.Head 5 n :=
  consSub symbol (consSub target (consSub source
    (consSub primitives (consSub sorts Fin.elim0))))

theorem primitiveSpine (context : Tower.Ctx n) :
    DeclarationSpine rules context (.const primitiveName) (liftClosed primitiveType) := by
  apply DeclarationSpine.constant (u := .sort primitiveDeclarationLevel)
  · exact combinedType_of_signature Tower.rules rawSignature rfl typeOf_primitive
  · exact FormationSensitiveMIL.primitiveType_hasType
  · exact .sort _

/-- Constructor inversion recovers the symbol's true dependent family,
regardless of the constructor term's subsequently displayed type. -/
theorem primitiveArgument (boundary : PiConversionBoundary rules)
    {context : Tower.Ctx n} (formed : ContextFormation rules context)
    {sorts primitives source target symbol displayed : Tower.Tm n}
    (observed : Typing context (primitiveApp sorts primitives source target symbol) displayed) :
    Typing context symbol (.app (.app primitives source) target) := by
  obtain ⟨typed, _, _, _⟩ := DeclarationSpine.recoverTelescope universes boundary formed
    primitiveContext primitiveResult (primitiveSubstitution sorts primitives source target symbol)
    (primitiveSpine context) observed
  exact typed (0 : Fin 5)

def chainContext : Tower.Ctx 7 :=
  .snoc
    (.snoc (.snoc (.snoc (.snoc contextSP (.var 1)) (.var 2)) (.var 3))
      (hypothesisApp (.var 4) (.var 3) (.var 2) (.var 1)))
    (hypothesisApp (.var 5) (.var 4) (.var 2) (.var 1))

def chainResult : Tower.Tm 7 :=
  hypothesisApp (.var 6) (.var 5) (.var 4) (.var 2)

def chainSubstitution (sorts primitives source middle target earlier later : Tower.Tm n) :
    Sub Tower.Head 7 n :=
  consSub later (consSub earlier (consSub target (consSub middle (consSub source
    (consSub primitives (consSub sorts Fin.elim0))))))

theorem chainSpine (context : Tower.Ctx n) :
    DeclarationSpine rules context (.const chainName) (liftClosed chainType) := by
  apply DeclarationSpine.constant (u := .sort chainDeclarationLevel)
  · exact combinedType_of_signature Tower.rules rawSignature rfl typeOf_chain
  · exact FormationSensitiveMIL.chainType_hasType
  · exact .sort _

/-- The chain's intermediate index and both source programs are recovered
without forgetting either constituent receipt. -/
theorem chainArguments (boundary : PiConversionBoundary rules)
    {context : Tower.Ctx n} (formed : ContextFormation rules context)
    {sorts primitives source middle target earlier later displayed : Tower.Tm n}
    (observed : Typing context
      (chainApp sorts primitives source middle target earlier later) displayed) :
    Typing context middle sorts ∧
      Typing context earlier (hypothesisApp sorts primitives source middle) ∧
      Typing context later (hypothesisApp sorts primitives middle target) := by
  obtain ⟨typed, _, _, _⟩ := DeclarationSpine.recoverTelescope universes boundary formed
    chainContext chainResult (chainSubstitution sorts primitives source middle target earlier later)
    (chainSpine context) observed
  exact ⟨typed (3 : Fin 7), typed (1 : Fin 7), typed (0 : Fin 7)⟩

#print axioms universes
#print axioms eliminateSpine
#print axioms eliminateArguments
#print axioms primitiveSpine
#print axioms primitiveArgument
#print axioms chainSpine
#print axioms chainArguments

end FormationSensitiveMILArgumentRecovery
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
