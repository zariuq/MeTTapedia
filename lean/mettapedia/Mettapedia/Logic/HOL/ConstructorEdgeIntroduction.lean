import Mettapedia.Logic.HOL.ConstructorPositionProgramProofs
import Mettapedia.Logic.HOL.ConstructorPositionSubstitution

/-!
# Retained edge introduction at a supplied original child index

The original guarded position and the child's actual root-index proof share
the same existential index. This is the constructive converse to edge
readback; it assumes neither an index-selection oracle nor functionality.
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

def edgeGuardFromIndex (payload : Term Const Γ (payloadType constructors.fields))
    (slot : Term Const Γ constructors.number) (child : Term Const Γ space) (index : Term Const Γ constructors.index)
    (position : ProofSyntax Const Δ (positions.childGuard payload slot index))
    (root : ProofSyntax Const Δ (constructors.rootIndex construct child index)) :
    ProofSyntax Const Δ (positions.edgeGuard construct payload slot child) := by
  apply ProofSyntax.exI index
  apply ProofSyntax.castIndices rfl ?_ (.andI position root)
  have cancel {type : Ty Base} (term : Term Const Γ type) :
      HOL.subst (Subst.single index) (HOL.subst (fun entry => Term.var (.vs entry)) term) = term := by
    rw [HOL.subst_comp]
    exact ProofSyntax.term_subst_of_identity (fun _ => rfl) term
  simp only [instantiate,HOL.subst,childGuard_subst,ConstructorPrograms.rootIndex_subst,Subst.single,cancel]
  cases constructors with
  | mk fields number indexType numeral allowed result =>
    cases positions with
    | mk graph =>
      have numeralSame : (fun n => HOL.subst (Subst.single index)
          (HOL.subst (fun entry => Term.var (.vs entry)) (numeral n))) = numeral :=
        funext (fun n => cancel (numeral n))
      have allowedSame : (fun occurrence => HOL.subst (Subst.single index)
          (HOL.subst (fun entry => Term.var (.vs entry)) (allowed occurrence))) = allowed :=
        funext (fun occurrence => cancel (allowed occurrence))
      have resultSame : (fun occurrence => HOL.subst (Subst.single index)
          (HOL.subst (fun entry => Term.var (.vs entry)) (result occurrence))) = result :=
        funext (fun occurrence => cancel (result occurrence))
      have graphSame : (fun occurrence => HOL.subst (Subst.single index)
          (HOL.subst (fun entry => Term.var (.vs entry)) (graph occurrence))) = graph :=
        funext (fun occurrence => cancel (graph occurrence))
      simp only [PositionPrograms.subst,ConstructorPrograms.subst]
      rw [numeralSame,allowedSame,resultSame,graphSame]

theorem edgeGuardFromIndex_free (payload : Term Const Γ (payloadType constructors.fields))
    (slot : Term Const Γ constructors.number) (child : Term Const Γ space) (index : Term Const Γ constructors.index)
    (position : ProofSyntax Const Δ (positions.childGuard payload slot index))
    (root : ProofSyntax Const Δ (constructors.rootIndex construct child index))
    (positionFree : position.FunctionExtensionalityFree) (rootFree : root.FunctionExtensionalityFree) :
    (positions.edgeGuardFromIndex construct payload slot child index position root).FunctionExtensionalityFree := by
  unfold edgeGuardFromIndex
  exact (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr ⟨positionFree,rootFree⟩

def edgeProgramFromIndex (payload : Term Const Γ (payloadType constructors.fields))
    (slot : Term Const Γ constructors.number) (child : Term Const Γ space) (index : Term Const Γ constructors.index)
    (position : ProofSyntax Const Δ (positions.childGuard payload slot index))
    (root : ProofSyntax Const Δ (constructors.rootIndex construct child index)) :
    ProofSyntax Const Δ (.app (.app (.app (positions.edgeProgram construct) payload) slot) child) :=
  .impE (.eqPropER (positions.edgeProgram_beta construct payload slot child))
    (positions.edgeGuardFromIndex construct payload slot child index position root)

theorem edgeProgramFromIndex_free (payload : Term Const Γ (payloadType constructors.fields))
    (slot : Term Const Γ constructors.number) (child : Term Const Γ space) (index : Term Const Γ constructors.index)
    (position : ProofSyntax Const Δ (positions.childGuard payload slot index))
    (root : ProofSyntax Const Δ (constructors.rootIndex construct child index))
    (positionFree : position.FunctionExtensionalityFree) (rootFree : root.FunctionExtensionalityFree) :
    (positions.edgeProgramFromIndex construct payload slot child index position root).FunctionExtensionalityFree :=
  ⟨positions.edgeProgram_beta_free _ _ _ _,positions.edgeGuardFromIndex_free _ _ _ _ _ position root positionFree rootFree⟩

def edgeFromOriginal (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence))
    (slot : Term Const Γ constructors.number) (child : Term Const Γ space) (index : Term Const Γ constructors.index)
    (allowed : ProofSyntax Const Δ (applyArguments _ (constructors.allowed occurrence) arguments))
    (related : ProofSyntax Const Δ (applyArguments _ (.app (.app (positions.graph occurrence) slot) index) arguments))
    (root : ProofSyntax Const Δ (constructors.rootIndex construct child index)) :
    ProofSyntax Const Δ (.app (.app (.app (positions.edgeProgram construct)
      (encode constructors.fields occurrence arguments)) slot) child) :=
  positions.edgeProgramFromIndex construct _ slot child index
    (positions.childFromOriginal occurrence arguments slot index allowed related) root

theorem edgeFromOriginal_free (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence))
    (slot : Term Const Γ constructors.number) (child : Term Const Γ space) (index : Term Const Γ constructors.index)
    (allowed : ProofSyntax Const Δ (applyArguments _ (constructors.allowed occurrence) arguments))
    (related : ProofSyntax Const Δ (applyArguments _ (.app (.app (positions.graph occurrence) slot) index) arguments))
    (root : ProofSyntax Const Δ (constructors.rootIndex construct child index))
    (allowedFree : allowed.FunctionExtensionalityFree) (relatedFree : related.FunctionExtensionalityFree)
    (rootFree : root.FunctionExtensionalityFree) :
    (positions.edgeFromOriginal construct occurrence arguments slot child index allowed related root).FunctionExtensionalityFree :=
  positions.edgeProgramFromIndex_free _ _ _ _ _ _ root
    (positions.childFromOriginal_free _ _ _ _ allowed related allowedFree relatedFree) rootFree

#print axioms edgeFromOriginal_free
end Mettapedia.Logic.HOL.IndexedConstructorGuards.PositionPrograms
