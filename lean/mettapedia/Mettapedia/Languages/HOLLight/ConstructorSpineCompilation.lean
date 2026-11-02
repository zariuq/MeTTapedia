import Mettapedia.Logic.HOL.IndexedConstructorRowClauses
import Mettapedia.Languages.HOLLight.InterpretedCompilation

/-!
# Compiling a datatype spine with schematic motives and child conditions

The original constructor inventory and operations remain in their source
context. Five additional parameters hold the tag, payload, children, motive
and child condition. Explicit original-field row clauses remain hypotheses;
no universally quantified arbitrary-condition method is assumed. The typed
interpretation supplies the selected native carriers and operations.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.HOLLight.ConstructorSpineCompilation

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open HOL HOL.FiniteConstructorEncoding

universe u v
variable {Base : Type u} {Const : HOL.Ty Base → Type v} {Γ : HOL.Ctx Base}
    (inventory : IndexedConstructorGuards.ConstructorPrograms Const Γ) {space : HOL.Ty Base}
    (constructor : HOL.Term Const Γ
      (inventory.number ⇒ payloadType inventory.fields ⇒ (inventory.number ⇒ space) ⇒ space))

abbrev context : HOL.Ctx Base :=
  (payloadType inventory.fields ⇒ .prop) :: (space ⇒ inventory.index ⇒ .prop) ::
    (inventory.number ⇒ space) :: payloadType inventory.fields :: inventory.number :: Γ

def sourceScope : HOL.Subst Const Γ (context inventory (space := space)) :=
  HOL.Subst.ofRename (fun index => .vs (.vs (.vs (.vs (.vs index)))))

def constructors : IndexedConstructorGuards.ConstructorPrograms Const (context inventory (space := space)) :=
  inventory.subst (sourceScope inventory)

def construct : HOL.Term Const (context inventory (space := space))
    (inventory.number ⇒ payloadType inventory.fields ⇒ (inventory.number ⇒ space) ⇒ space) :=
  HOL.subst (sourceScope inventory) constructor

def condition : HOL.Term Const (context inventory (space := space)) (payloadType inventory.fields ⇒ .prop) :=
  .var .vz

def property : HOL.Term Const (context inventory (space := space)) (space ⇒ inventory.index ⇒ .prop) :=
  .var (.vs .vz)

def children : HOL.Term Const (context inventory (space := space)) (inventory.number ⇒ space) :=
  .var (.vs (.vs .vz))

def payload : HOL.Term Const (context inventory (space := space)) (payloadType inventory.fields) :=
  .var (.vs (.vs (.vs .vz)))

def tag : HOL.Term Const (context inventory (space := space)) inventory.number :=
  .var (.vs (.vs (.vs (.vs .vz))))

def assumptions : List (HOL.Formula Const (context inventory (space := space))) :=
  (constructors inventory).spineAssumptions (construct inventory constructor)
    (children inventory) (condition inventory) (property inventory) (tag inventory) (payload inventory)

def conclusion : HOL.Formula Const (context inventory (space := space)) :=
  .app (IndexedPredicateInduction.lift ((constructors inventory).rootProgram (construct inventory constructor))
    (property inventory))
    (.app (.app (.app (construct inventory constructor) (tag inventory)) (payload inventory)) (children inventory))

def proof : HOL.ProofSyntax Const (assumptions inventory constructor) (conclusion inventory constructor) :=
  (constructors inventory).spineProof (construct inventory constructor) (children inventory)
    (condition inventory) (property inventory) (tag inventory) (payload inventory)

theorem proof_free : (proof inventory constructor).FunctionExtensionalityFree :=
  (constructors inventory).spineProof_free (construct inventory constructor) (children inventory)
    (condition inventory) (property inventory) (tag inventory) (payload inventory)

variable (interpretation : HOL.TermInterpretation Base Const AtomicTy Symbol)

@[irreducible, noinline] def compile
    (names : ReverseTranslation.Naming ((context inventory (space := space)).map
      (HOL.Ty.substitute interpretation.types))) :
    RetainedCompilation.Compiled emptyAxiomPolicy names
      (((assumptions inventory constructor).map interpretation.term).map ImpredicativeConnectives.expand)
      (ImpredicativeConnectives.expand (interpretation.term (conclusion inventory constructor))) :=
  InterpretedCompilation.compile interpretation (proof inventory constructor) (proof_free inventory constructor)
    names ("indexed-constructor-spine", 0)

#print axioms proof_free
#print axioms compile

end Mettapedia.Languages.HOLLight.ConstructorSpineCompilation
