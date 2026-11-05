import Mettapedia.Logic.HOL.ConstructorIndexSelection

/-!
# A retained edge supplies its child's root at a checked row index

The original edge witness retains the admitted constructor row, its field
relation and its root-index proof. A supplied, uniformly guarded index
comparison transports that root proof before the witness scope is closed.
No equality of child values is inferred from equality of their indices.
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
  {Δ : List (Formula Const Γ)}

def rootAtRequestedIndex (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence))
    (slot : Term Const Γ constructors.number) (child : Term Const Γ space)
    (requested : Term Const Γ constructors.index)
    (edge : ProofSyntax Const Δ (.app (.app (.app (positions.edgeProgram construct)
      (encode constructors.fields occurrence arguments)) slot) child))
    (comparison : ProofSyntax Const Δ (positions.indexComparison occurrence arguments slot requested)) :
    ProofSyntax Const Δ (.app (.app (constructors.rootProgram construct) child) requested) := by
  have witness := positions.edgeProgramReadback construct occurrence arguments slot child edge
  apply ProofSyntax.exE witness
  let rho : Subst Const Γ (constructors.index :: Γ) := edgeIndexScope (constructors := constructors)
  let data := substituteArguments rho _ arguments
  let body := Term.and (applyArguments _ ((constructors.subst rho).allowed occurrence) data)
    (.and (applyArguments _ (.app (.app ((positions.subst rho).graph occurrence) (HOL.subst rho slot)) (.var .vz)) data)
      ((constructors.subst rho).rootIndex (HOL.subst rho construct) (HOL.subst rho child) (.var .vz)))
  let hypotheses := body :: weakenHyps Δ
  have present : ProofSyntax Const hypotheses body := .hyp 0
  have equal : ProofSyntax Const hypotheses (.eq (.var .vz) (HOL.subst rho requested)) :=
    .impE (ContextualTrinity.instantiateFresh ((comparison.rename Rename.weaken).prepend body))
      (.andI (.andEL present) (.andEL (.andER present)))
  have rootProof : ProofSyntax Const hypotheses
      (.app (.app (HOL.subst rho (constructors.rootProgram construct)) (HOL.subst rho child)) (.var .vz)) := by
    apply ProofSyntax.castIndices rfl ?_
      (.impE (.eqPropER ((constructors.subst rho).rootProgram_beta
        (HOL.subst rho construct) (HOL.subst rho child) (.var .vz))) (.andER (.andER present)))
    exact congrArg (fun function => Term.app (.app function (HOL.subst rho child)) (.var .vz))
      (constructors.rootProgram_subst construct rho).symm
  have atIndex := ProofSyntax.impE (.eqPropEL (.eqAppArg
    (.app (HOL.subst rho (constructors.rootProgram construct)) (HOL.subst rho child)) equal)) rootProof
  apply ProofSyntax.castIndices rfl ?_ atIndex
  change HOL.subst rho (.app (.app (constructors.rootProgram construct) child) requested) = _
  exact subst_ofRename Rename.weaken _

theorem rootAtRequestedIndex_free (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence))
    (slot : Term Const Γ constructors.number) (child : Term Const Γ space)
    (requested : Term Const Γ constructors.index)
    (edge : ProofSyntax Const Δ (.app (.app (.app (positions.edgeProgram construct)
      (encode constructors.fields occurrence arguments)) slot) child))
    (comparison : ProofSyntax Const Δ (positions.indexComparison occurrence arguments slot requested))
    (edgeFree : edge.FunctionExtensionalityFree) (comparisonFree : comparison.FunctionExtensionalityFree) :
    (positions.rootAtRequestedIndex construct occurrence arguments slot child requested edge comparison).FunctionExtensionalityFree := by
  unfold rootAtRequestedIndex
  refine ⟨positions.edgeProgramReadback_free construct occurrence arguments slot child edge edgeFree,?_⟩
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  constructor
  · constructor
    · apply (ContextualTrinity.instantiateFresh_free _).mpr
      simpa only [ProofSyntax.prepend,ProofSyntax.functionExtensionalityFree_mono,
        ProofSyntax.functionExtensionalityFree_rename] using comparisonFree
    · trivial
  · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    exact ⟨ConstructorPrograms.rootProgram_beta_free _ _ _ _,True.intro⟩

#print axioms rootAtRequestedIndex
#print axioms rootAtRequestedIndex_free
end Mettapedia.Logic.HOL.IndexedConstructorGuards.PositionPrograms
