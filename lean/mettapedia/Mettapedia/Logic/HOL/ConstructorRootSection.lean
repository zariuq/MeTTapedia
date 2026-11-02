import Mettapedia.Logic.HOL.CurriedGuardProgramProofs

/-!
# A recursive-element predicate at one declared root index

The predicate is an explicit section of the original root programme. Its
retained beta proof returns the actual root-index judgment, so using it as
an element guard does not replace root evidence by an unconnected predicate.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.IndexedConstructorGuards.ConstructorPrograms
open FiniteConstructorEncoding
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ : Ctx Base}
    (constructors : ConstructorPrograms Const Γ) {space : Ty Base}
    (construct : Term Const Γ
      (constructors.number ⇒ payloadType constructors.fields ⇒ (constructors.number ⇒ space) ⇒ space))
    {Δ : List (Formula Const Γ)}

def rootAt (index : Term Const Γ constructors.index) : Term Const Γ (space ⇒ .prop) :=
  .lam (.app (.app (weaken (constructors.rootProgram construct)) (.var .vz)) (weaken index))

def rootAt_programBeta (index : Term Const Γ constructors.index) (point : Term Const Γ space) :
    ProofSyntax Const Δ (.eq (.app (constructors.rootAt construct index) point)
      (.app (.app (constructors.rootProgram construct) point) index)) := by
  apply ProofSyntax.castIndices rfl ?_ (.beta point
    (.app (.app (weaken (constructors.rootProgram construct)) (.var .vz)) (weaken index)))
  simp only [instantiate,HOL.subst,PredicateFixedPoint.subst_single_weaken,Subst.single]
  rfl

theorem rootAt_programBeta_free (index : Term Const Γ constructors.index) (point : Term Const Γ space) :
    (constructors.rootAt_programBeta (Δ := Δ) construct index point).FunctionExtensionalityFree := by
  unfold rootAt_programBeta
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  trivial

def rootAt_beta (index : Term Const Γ constructors.index) (point : Term Const Γ space) :
    ProofSyntax Const Δ (.eq (.app (constructors.rootAt construct index) point) (constructors.rootIndex construct point index)) :=
  .eqTrans (constructors.rootAt_programBeta construct index point)
    (constructors.rootProgram_beta construct point index)

theorem rootAt_beta_free (index : Term Const Γ constructors.index) (point : Term Const Γ space) :
    (constructors.rootAt_beta (Δ := Δ) construct index point).FunctionExtensionalityFree :=
  ⟨constructors.rootAt_programBeta_free _ _ _,constructors.rootProgram_beta_free _ _ _⟩

def rootAt_elim (index : Term Const Γ constructors.index) (point : Term Const Γ space)
    (present : ProofSyntax Const Δ (.app (constructors.rootAt construct index) point)) :
    ProofSyntax Const Δ (constructors.rootIndex construct point index) :=
  .impE (.eqPropEL (constructors.rootAt_beta construct index point)) present

theorem rootAt_elim_free (index : Term Const Γ constructors.index) (point : Term Const Γ space)
    (present : ProofSyntax Const Δ (.app (constructors.rootAt construct index) point)) (free : present.FunctionExtensionalityFree) :
    (constructors.rootAt_elim construct index point present).FunctionExtensionalityFree :=
  ⟨constructors.rootAt_beta_free _ _ _,free⟩

def rootAt_intro (index : Term Const Γ constructors.index) (point : Term Const Γ space)
    (present : ProofSyntax Const Δ (constructors.rootIndex construct point index)) :
    ProofSyntax Const Δ (.app (constructors.rootAt construct index) point) :=
  .impE (.eqPropER (constructors.rootAt_beta construct index point)) present

theorem rootAt_intro_free (index : Term Const Γ constructors.index) (point : Term Const Γ space)
    (present : ProofSyntax Const Δ (constructors.rootIndex construct point index)) (free : present.FunctionExtensionalityFree) :
    (constructors.rootAt_intro construct index point present).FunctionExtensionalityFree :=
  ⟨constructors.rootAt_beta_free _ _ _,free⟩

#print axioms rootAt_elim_free
end Mettapedia.Logic.HOL.IndexedConstructorGuards.ConstructorPrograms
