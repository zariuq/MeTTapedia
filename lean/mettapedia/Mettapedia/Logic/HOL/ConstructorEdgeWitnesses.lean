import Mettapedia.Logic.HOL.ConstructorPositionProgramProofs
import Mettapedia.Logic.HOL.ConstantExpansionProofsFree

/-!
# Original-row index witnesses from guarded edges

Readback preserves the edge's existential index, the original row relation
and the child's root-index proof. No selected index or functionality axiom
is introduced.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.IndexedConstructorGuards.PositionPrograms

open FiniteConstructorEncoding CurriedPredicates
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ : Ctx Base}
    {constructors : ConstructorPrograms Const Γ} (positions : PositionPrograms constructors)
    {space : Ty Base}
    (construct : Term Const Γ
      (constructors.number ⇒ payloadType constructors.fields ⇒ (constructors.number ⇒ space) ⇒ space))

def edgeIndexScope : Subst Const Γ (constructors.index :: Γ) := fun index => .var (.vs index)

def originalEdgeWitness (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence))
    (slot : Term Const Γ constructors.number) (child : Term Const Γ space) : Formula Const Γ :=
  let rho : Subst Const Γ (constructors.index :: Γ) := edgeIndexScope (constructors := constructors)
  let shifted := constructors.subst rho
  let data := substituteArguments rho _ arguments
  .ex (.and (applyArguments _ (shifted.allowed occurrence) data)
    (.and (applyArguments _ (.app (.app ((positions.subst rho).graph occurrence) (HOL.subst rho slot)) (.var .vz)) data)
      (shifted.rootIndex (HOL.subst rho construct) (HOL.subst rho child) (.var .vz))))

def edgeGuardReadback {assumptions : List (Formula Const Γ)}
    (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence))
    (slot : Term Const Γ constructors.number) (child : Term Const Γ space)
    (present : ProofSyntax Const assumptions
      (positions.edgeGuard construct (encode constructors.fields occurrence arguments) slot child)) :
    ProofSyntax Const assumptions (positions.originalEdgeWitness construct occurrence arguments slot child) := by
  apply ProofSyntax.impE (ContextualTrinity.exImp ?_) present
  apply ProofSyntax.allI
  apply ProofSyntax.impI
  let rho : Subst Const Γ (constructors.index :: Γ) := edgeIndexScope (constructors := constructors)
  let shifted := positions.subst rho
  let data := substituteArguments rho _ arguments
  let antecedent := Term.and
    (shifted.childGuard (HOL.subst rho (encode constructors.fields occurrence arguments)) (HOL.subst rho slot) (.var .vz))
    ((constructors.subst rho).rootIndex (HOL.subst rho construct) (HOL.subst rho child) (.var .vz))
  let localAssumptions := antecedent :: weakenHyps assumptions
  have encoded : ProofSyntax Const localAssumptions
      (shifted.childGuard (encode constructors.fields occurrence data) (HOL.subst rho slot) (.var .vz)) := by
    apply ProofSyntax.castIndices rfl ?_ (ProofSyntax.andEL (ProofSyntax.hyp 0))
    rw [encode_subst]
  let fields := shifted.childReadback occurrence data (HOL.subst rho slot) (.var .vz) encoded
  exact .andI (.andEL fields) (.andI (.andER fields) (.andER (.hyp 0)))

theorem edgeGuardReadback_free {assumptions : List (Formula Const Γ)}
    (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence))
    (slot : Term Const Γ constructors.number) (child : Term Const Γ space)
    (present : ProofSyntax Const assumptions
      (positions.edgeGuard construct (encode constructors.fields occurrence arguments) slot child))
    (free : present.FunctionExtensionalityFree) :
    (positions.edgeGuardReadback construct occurrence arguments slot child present).FunctionExtensionalityFree := by
  unfold edgeGuardReadback
  refine ⟨?_, free⟩
  apply (ContextualTrinity.exImp_free _).mpr
  refine ⟨?_, ?_⟩
  · apply childReadback_free
    apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    trivial
  · constructor
    · apply childReadback_free
      apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
      trivial
    · trivial

def edgeProgramReadback {assumptions : List (Formula Const Γ)}
    (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence))
    (slot : Term Const Γ constructors.number) (child : Term Const Γ space)
    (present : ProofSyntax Const assumptions
      (.app (.app (.app (positions.edgeProgram construct)
        (encode constructors.fields occurrence arguments)) slot) child)) :
    ProofSyntax Const assumptions (positions.originalEdgeWitness construct occurrence arguments slot child) :=
  positions.edgeGuardReadback construct occurrence arguments slot child
    (.impE (.eqPropEL (positions.edgeProgram_beta construct _ slot child)) present)

theorem edgeProgramReadback_free {assumptions : List (Formula Const Γ)}
    (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence))
    (slot : Term Const Γ constructors.number) (child : Term Const Γ space)
    (present : ProofSyntax Const assumptions
      (.app (.app (.app (positions.edgeProgram construct)
        (encode constructors.fields occurrence arguments)) slot) child))
    (free : present.FunctionExtensionalityFree) :
    (positions.edgeProgramReadback construct occurrence arguments slot child present).FunctionExtensionalityFree :=
  positions.edgeGuardReadback_free construct occurrence arguments slot child _
    ⟨positions.edgeProgram_beta_free construct _ slot child, free⟩

#print axioms edgeGuardReadback_free
#print axioms edgeProgramReadback_free

end Mettapedia.Logic.HOL.IndexedConstructorGuards.PositionPrograms
