import Mettapedia.Logic.HOL.ConstructorGuardReadback
import Mettapedia.Logic.HOL.ConstructorPositionPrograms

/-!
# Reading original child-index relations from encoded payload guards

The retained guard proof recovers both the original field guard and the
declared row relation at the supplied slot and index. The converse rebuilds
the guard from those proofs. No functionality or uniqueness of child indices
is assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.IndexedConstructorGuards.PositionPrograms

open FiniteConstructorEncoding CurriedPredicates
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ : Ctx Base}
    {constructors : ConstructorPrograms Const Γ} (positions : PositionPrograms constructors)
    {assumptions : List (Formula Const Γ)}

def childReadback (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence))
    (slot : Term Const Γ constructors.number) (index : Term Const Γ constructors.index)
    (present : ProofSyntax Const assumptions
      (positions.childGuard (encode constructors.fields occurrence arguments) slot index)) :
    ProofSyntax Const assumptions
      (.and (applyArguments _ (constructors.allowed occurrence) arguments)
        (applyArguments _ (.app (.app (positions.graph occurrence) slot) index) arguments)) :=
  .impE (.eqPropEL (conjoin_beta _ (constructors.allowed occurrence)
    (.app (.app (positions.graph occurrence) slot) index) arguments))
    (ConstructorDataPredicates.readOnEncoded constructors.fields (positions.childCondition slot index)
      occurrence arguments present)

theorem childReadback_free (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence))
    (slot : Term Const Γ constructors.number) (index : Term Const Γ constructors.index)
    (present : ProofSyntax Const assumptions
      (positions.childGuard (encode constructors.fields occurrence arguments) slot index))
    (free : present.FunctionExtensionalityFree) :
    (positions.childReadback occurrence arguments slot index present).FunctionExtensionalityFree :=
  ⟨conjoin_beta_free _ _ _ _, ConstructorDataPredicates.readOnEncoded_free _ _ _ _ present free⟩

def childFromOriginal (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence))
    (slot : Term Const Γ constructors.number) (index : Term Const Γ constructors.index)
    (allowed : ProofSyntax Const assumptions (applyArguments _ (constructors.allowed occurrence) arguments))
    (related : ProofSyntax Const assumptions
      (applyArguments _ (.app (.app (positions.graph occurrence) slot) index) arguments)) :
    ProofSyntax Const assumptions
      (positions.childGuard (encode constructors.fields occurrence arguments) slot index) :=
  ConstructorDataPredicates.introduce constructors.fields (positions.childCondition slot index) occurrence arguments
    (conjoin_intro _ arguments allowed related)

theorem childFromOriginal_free (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence))
    (slot : Term Const Γ constructors.number) (index : Term Const Γ constructors.index)
    (allowed : ProofSyntax Const assumptions (applyArguments _ (constructors.allowed occurrence) arguments))
    (related : ProofSyntax Const assumptions
      (applyArguments _ (.app (.app (positions.graph occurrence) slot) index) arguments))
    (allowedFree : allowed.FunctionExtensionalityFree) (relatedFree : related.FunctionExtensionalityFree) :
    (positions.childFromOriginal occurrence arguments slot index allowed related).FunctionExtensionalityFree :=
  ConstructorDataPredicates.introduce_free _ _ _ _ _ (conjoin_intro_free _ _ _ _ allowedFree relatedFree)

theorem childGuard_iff_original (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence))
    (slot : Term Const Γ constructors.number) (index : Term Const Γ constructors.index) :
    Nonempty (ProofSyntax Const assumptions
      (positions.childGuard (encode constructors.fields occurrence arguments) slot index)) ↔
      Nonempty (ProofSyntax Const assumptions
        (.and (applyArguments _ (constructors.allowed occurrence) arguments)
          (applyArguments _ (.app (.app (positions.graph occurrence) slot) index) arguments))) :=
  ⟨fun ⟨proof⟩ => ⟨positions.childReadback occurrence arguments slot index proof⟩,
    fun ⟨proof⟩ => ⟨positions.childFromOriginal occurrence arguments slot index (.andEL proof) (.andER proof)⟩⟩

#print axioms childReadback_free
#print axioms childFromOriginal_free
#print axioms childGuard_iff_original

end Mettapedia.Logic.HOL.IndexedConstructorGuards.PositionPrograms
