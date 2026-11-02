import Mettapedia.Logic.HOL.GeneratedFamilyPredicate

/-!
# Recursive-space predicates with open constructor and guard parameters

All five operations retain their actual surrounding HOL context. The existing
positive-code compiler supplies monotonicity and fixed-point proofs; the
closed signature is recovered by an exact code comparison. Substitution acts
on every open operation, including beneath the constructor and slot binders.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.RecursiveSpacePredicate
universe u v w
variable {Base : Type u} {Const : Ty Base → Type v} {Γ Ξ : Ctx Base}

structure Contextual (Const : Ty Base → Type v) (Γ : Ctx Base) where
  number : Ty Base
  payload : Ty Base
  space : Ty Base
  bottom : Term Const Γ space
  construct : Term Const Γ (number ⇒ payload ⇒ (number ⇒ space) ⇒ space)
  validShape : Term Const Γ (number ⇒ payload ⇒ .prop)
  active : Term Const Γ (payload ⇒ number ⇒ .prop)
  validEdge : Term Const Γ (payload ⇒ number ⇒ space ⇒ .prop)

namespace Contextual
variable (signature : Contextual Const Γ)

theorem eq_of_fields {first second : Contextual Const Γ}
    (number : first.number = second.number) (payload : first.payload = second.payload)
    (space : first.space = second.space) (bottom : HEq first.bottom second.bottom)
    (construct : HEq first.construct second.construct) (shape : HEq first.validShape second.validShape)
    (active : HEq first.active second.active) (edge : HEq first.validEdge second.validEdge) : first = second := by
  cases first
  cases second
  cases number
  cases payload
  cases space
  cases bottom
  cases construct
  cases shape
  cases active
  cases edge
  rfl

universe u' v'
variable {Target : Type u'} {Symbols : Ty Target → Type v'}

/-- Read all operations at the mapped carriers and the same variable positions. -/
def read (reading : TermInterpretation Base Const Target Symbols) :
    Contextual Symbols (Γ.map (Ty.substitute reading.types)) where
  number := Ty.substitute reading.types signature.number
  payload := Ty.substitute reading.types signature.payload
  space := Ty.substitute reading.types signature.space
  bottom := reading.term signature.bottom
  construct := reading.term signature.construct
  validShape := reading.term signature.validShape
  active := reading.term signature.active
  validEdge := reading.term signature.validEdge

def subst (theta : Subst Const Γ Ξ) : Contextual Const Ξ where
  number := signature.number
  payload := signature.payload
  space := signature.space
  bottom := HOL.subst theta signature.bottom
  construct := HOL.subst theta signature.construct
  validShape := HOL.subst theta signature.validShape
  active := HOL.subst theta signature.active
  validEdge := HOL.subst theta signature.validEdge

def code : PositivePredicate.Code Const signature.space (signature.space :: Γ) :=
  .ex (domain := signature.number) (.ex (domain := signature.payload)
    (.ex (domain := signature.number ⇒ signature.space)
      (.conj
        (.atom (.app (.app (weaken (weaken (weaken (weaken signature.validShape))))
          (.var (.vs (.vs .vz)))) (.var (.vs .vz))))
        (.conj
          (.atom (.eq (.var (.vs (.vs (.vs .vz))))
            (.app (.app (.app (weaken (weaken (weaken (weaken signature.construct))))
              (.var (.vs (.vs .vz)))) (.var (.vs .vz))) (.var .vz))))
          (.all (domain := signature.number)
            (.conj
              (.guard (.app (.app (weaken (weaken (weaken (weaken (weaken signature.active)))))
                (.var (.vs (.vs .vz)))) (.var .vz))
                (.conj
                  (.atom (.app (.app (.app (weaken (weaken (weaken (weaken (weaken signature.validEdge)))))
                    (.var (.vs (.vs .vz)))) (.var .vz)) (.app (.var (.vs .vz)) (.var .vz))))
                  (.member (.app (.var (.vs .vz)) (.var .vz)))))
              (.atom (.imp
                (.not (.app (.app (weaken (weaken (weaken (weaken (weaken signature.active)))))
                  (.var (.vs (.vs .vz)))) (.var .vz)))
                (.eq (.app (.var (.vs .vz)) (.var .vz))
                  (weaken (weaken (weaken (weaken (weaken signature.bottom))))))))))))))

def operator : Term Const Γ (PredicateFixedPoint.Operator signature.space) := signature.code.operator
def least : Term Const Γ (signature.space ⇒ .prop) := PredicateFixedPoint.least signature.operator

@[simp] theorem read_code (reading : TermInterpretation Base Const Target Symbols) :
    signature.code.read reading = (signature.read reading).code := by
  simp only [code, read, PositivePredicate.Code.read, TermInterpretation.term_app,
    TermInterpretation.term_weaken, TermInterpretation.term_eq, TermInterpretation.term_var,
    TermInterpretation.term_imp, TermInterpretation.term_not, Var.mapTypes]

@[simp] theorem read_operator (reading : TermInterpretation Base Const Target Symbols) :
    reading.term signature.operator = (signature.read reading).operator := by
  rw [operator, PositivePredicate.Code.operator_read, read_code]
  rfl

@[simp] theorem read_least (reading : TermInterpretation Base Const Target Symbols) :
    reading.term signature.least = (signature.read reading).least := by
  simp only [least, PredicateFixedPoint.read_least, read_operator]

@[simp] theorem code_subst (theta : Subst Const Γ Ξ) :
    signature.code.subst (Subst.lift theta) = (signature.subst theta).code := by
  simp [code, subst, PositivePredicate.Code.subst, HOL.subst, subst_weaken, Subst.lift, Rename.weaken]

@[simp] theorem subst_operator (theta : Subst Const Γ Ξ) :
    HOL.subst theta signature.operator = (signature.subst theta).operator := by
  rw [operator, ← PositivePredicate.Code.operator_subst, code_subst]
  rfl

@[simp] theorem subst_least (theta : Subst Const Γ Ξ) :
    HOL.subst theta signature.least = (signature.subst theta).least := by
  simp only [least, PredicateFixedPoint.subst_least, subst_operator]

@[simp] theorem rename_operator (theta : Rename Base Γ Ξ) :
    HOL.rename theta signature.operator = (signature.subst (Subst.ofRename theta)).operator := by
  simpa only [subst_ofRename] using signature.subst_operator (Subst.ofRename theta)

@[simp] theorem rename_least (theta : Rename Base Γ Ξ) :
    HOL.rename theta signature.least = (signature.subst (Subst.ofRename theta)).least := by
  simpa only [subst_ofRename] using signature.subst_least (Subst.ofRename theta)

def monotonicity {assumptions : List (Formula Const Γ)} :
    ProofSyntax Const assumptions (PredicateFixedPoint.monotone signature.operator) := signature.code.operator_monotone

def fixedPoint {assumptions : List (Formula Const Γ)} :
    ProofSyntax Const assumptions (PredicateFixedPoint.equation signature.operator) := signature.code.fixed_point

theorem monotonicity_free {assumptions : List (Formula Const Γ)} :
    (signature.monotonicity (assumptions := assumptions)).FunctionExtensionalityFree :=
  signature.code.operator_monotone_functionExtensionalityFree

theorem fixedPoint_free {assumptions : List (Formula Const Γ)} :
    (signature.fixedPoint (assumptions := assumptions)).FunctionExtensionalityFree :=
  signature.code.fixed_point_functionExtensionalityFree

variable (model : HenkinModel.{u,v,w} Base Const) (full : model.FullDomains)
include full

theorem operator_meaning (values : model.Valuation Γ)
    (predicate : Ty.denote model.Carrier (signature.space ⇒ .prop))
    (point : Ty.denote model.Carrier signature.space) :
    (model.denote signature.operator values predicate point).down ↔
      ∃ tag payload children,
        (model.denote signature.validShape values tag payload).down ∧
        point = model.denote signature.construct values tag payload children ∧
        ∀ slot,
          ((model.denote signature.active values payload slot).down →
            (model.denote signature.validEdge values payload slot (children slot)).down ∧
              (predicate (children slot)).down) ∧
          (¬ (model.denote signature.active values payload slot).down →
            children slot = model.denote signature.bottom values) := by
  have admitted : ∀ type value, model.adm type value := full
  simp only [operator, PositivePredicate.Code.operator, code, PositivePredicate.Code.rename,
    PositivePredicate.Code.interpret, HenkinModel.denote, PreModel.denote, HOL.rename,
    weaken, rename_comp, Soundness.denote_rename, PreModel.extend, Rename.lift, Rename.weaken]
  simp only [model.eqv_iff_eq_of_fullDomains full, admitted, true_and, forall_true_left]
  rfl

end Contextual

namespace Signature
def contextual (signature : Signature Const) : Contextual Const [] where
  number := signature.number
  payload := signature.payload
  space := signature.space
  bottom := signature.bottom
  construct := signature.construct
  validShape := signature.validShape
  active := signature.active
  validEdge := signature.validEdge

theorem contextual_code (signature : Signature Const) : signature.contextual.code = signature.code := by
  simp only [Contextual.code, contextual, code, weakenCtx_cons, weakenCtx_nil]

theorem contextual_operator (signature : Signature Const) : signature.contextual.operator = signature.operator := by
  unfold Contextual.operator operator
  rw [contextual_code]

theorem contextual_least (signature : Signature Const) : signature.contextual.least = PredicateFixedPoint.least signature.operator := by
  rw [Contextual.least, contextual_operator]
end Signature

#print axioms Contextual.code_subst
#print axioms Contextual.operator_meaning
#print axioms Contextual.fixedPoint_free
#print axioms Signature.contextual_code

end Mettapedia.Logic.HOL.RecursiveSpacePredicate

namespace Mettapedia.Logic.HOL.IndexedConstructorGuards.PositionPrograms
open FiniteConstructorEncoding
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ : Ctx Base}
  {constructors : ConstructorPrograms Const Γ} (positions : PositionPrograms constructors) {space : Ty Base}

def contextual (bottom : Term Const Γ space)
    (construct : Term Const Γ (constructors.number ⇒ payloadType constructors.fields ⇒ (constructors.number ⇒ space) ⇒ space)) :
    RecursiveSpacePredicate.Contextual Const Γ where
  number := constructors.number
  payload := payloadType constructors.fields
  space := space
  bottom := bottom
  construct := construct
  validShape := constructors.shapeProgram
  active := positions.activeProgram
  validEdge := positions.edgeProgram construct

theorem contextual_operator_closed {closedConstructors : ConstructorPrograms Const []}
    (closedPositions : PositionPrograms closedConstructors) (bottom : ClosedTerm Const space)
    (construct : ClosedTerm Const (closedConstructors.number ⇒ payloadType closedConstructors.fields ⇒
      (closedConstructors.number ⇒ space) ⇒ space)) :
    (closedPositions.contextual bottom construct).operator = closedPositions.operator bottom construct :=
  (closedPositions.signature bottom construct).contextual_operator

theorem contextual_member_closed {closedConstructors : ConstructorPrograms Const []}
    (closedPositions : PositionPrograms closedConstructors) (bottom : ClosedTerm Const space)
    (construct : ClosedTerm Const (closedConstructors.number ⇒ payloadType closedConstructors.fields ⇒
      (closedConstructors.number ⇒ space) ⇒ space)) :
    (closedPositions.contextual bottom construct).least = closedPositions.member bottom construct :=
  (closedPositions.signature bottom construct).contextual_least

end Mettapedia.Logic.HOL.IndexedConstructorGuards.PositionPrograms
