import Mettapedia.Logic.HOL.ProofSyntaxTypeSubstitution
import Mettapedia.Logic.HOL.ProofSyntaxConstantSubstitution

/-!
# Retained interpretation by simple types and closed terms

Base symbols may become compound simple types, and constants may become closed
terms rather than single symbols. The interpretation reuses type substitution
and constant expansion. It retains the supplied inference tree and hypothesis
occurrences. No injectivity, reflection or arbitrary model reduct is asserted.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Logic.HOL
universe u u' v v'
variable {Base : Type u} {Base' : Type u'} {Const : Ty Base → Type v} {Const' : Ty Base' → Type v'}

namespace ProofSyntax

theorem functionExtensionalityFree_mapTypes
    (types : Base → Ty Base') (constants : ∀ {type}, Const type → Const' (Ty.substitute types type))
    {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {formula : Formula Const Γ}
    (proof : ProofSyntax Const Δ formula) :
    (ProofSyntax.mapTypes types constants proof).FunctionExtensionalityFree ↔ proof.FunctionExtensionalityFree := by
  induction proof <;>
    simp_all only [mapTypes, functionExtensionalityFree_castIndices, FunctionExtensionalityFree]

theorem functionExtensionalityFree_substConst {Target : Ty Base → Type v'}
    (images : ∀ {type}, Const type → ClosedTerm Target type)
    {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {formula : Formula Const Γ}
    (proof : ProofSyntax Const Δ formula) :
    (ProofSyntax.substConst images proof).FunctionExtensionalityFree ↔ proof.FunctionExtensionalityFree := by
  induction proof <;> dsimp only [substConst]
  all_goals try rw [functionExtensionalityFree_castIndices]
  all_goals simp_all only [functionExtensionalityFree_castIndices, FunctionExtensionalityFree]

theorem functionExtensionalityFree_mapConst {Symbols : Ty Base → Type v'}
    (constants : ∀ {type}, Const type → Symbols type)
    {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {formula : Formula Const Γ}
    (proof : ProofSyntax Const Δ formula) :
    (ProofSyntax.mapConst constants proof).FunctionExtensionalityFree ↔ proof.FunctionExtensionalityFree := by
  dsimp only [ProofSyntax.mapConst]
  rw [functionExtensionalityFree_castIndices]
  exact functionExtensionalityFree_substConst _ proof

end ProofSyntax

structure TermInterpretation (Base : Type u) (Const : Ty Base → Type v)
    (Target : Type u') (Symbols : Ty Target → Type v') where
  types : Base → Ty Target
  constants : ∀ {type}, Const type → ClosedTerm Symbols (Ty.substitute types type)

namespace TermInterpretation
variable (interpretation : TermInterpretation Base Const Base' Const')

def term {Γ : Ctx Base} {type : Ty Base} (source : Term Const Γ type) :
    Term Const' (Γ.map (Ty.substitute interpretation.types)) (Ty.substitute interpretation.types type) :=
  HOL.substConst (fun code => code) (HOL.mapTypes interpretation.types interpretation.constants source)

def proof {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {formula : Formula Const Γ}
    (source : ProofSyntax Const Δ formula) :
    ProofSyntax Const' (Δ.map interpretation.term) (interpretation.term formula) :=
  ProofSyntax.castIndices (by rw [List.map_map]; rfl) rfl
    (ProofSyntax.substConst (fun code => code)
      (ProofSyntax.mapTypes interpretation.types interpretation.constants source))

theorem proof_nodeCount {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {formula : Formula Const Γ}
    (source : ProofSyntax Const Δ formula) :
    (interpretation.proof source).nodeCount = source.nodeCount := by
  simp only [proof, ProofSyntax.nodeCount_castIndices, ProofSyntax.substConst_nodeCount, ProofSyntax.nodeCount_mapTypes]

theorem proof_free {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {formula : Formula Const Γ}
    (source : ProofSyntax Const Δ formula) (free : source.FunctionExtensionalityFree) :
    (interpretation.proof source).FunctionExtensionalityFree := by
  simpa only [proof, ProofSyntax.functionExtensionalityFree_castIndices,
    ProofSyntax.functionExtensionalityFree_substConst, ProofSyntax.functionExtensionalityFree_mapTypes] using free

end TermInterpretation
#print axioms TermInterpretation.proof
#print axioms TermInterpretation.proof_nodeCount
#print axioms TermInterpretation.proof_free
end Mettapedia.Logic.HOL
