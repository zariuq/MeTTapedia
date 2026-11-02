import Mettapedia.Logic.HOL.IndexedVectorPredicate
import Mettapedia.Logic.HOL.UniversalArgumentProofs

/-!
# Least positional lookup for indexed vectors

Lookup is the least curried relation closed under the head and tail rules.
The head lies at zero; passing through a cons advances both the vector index
and the local position. The rules retain the original constructor arguments.
Their closure and elimination are object-language HOL proof programs.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.IndexedVectorPositions
open FiniteConstructorEncoding
universe u v
variable {Base : Type u} {Const : Ty Base → Type v}
    (signature : IndexedVectorPredicate.Signature Const) {Γ Ξ : Ctx Base}

abbrev Relation := signature.number ⇒ signature.vector ⇒ signature.number ⇒ signature.element ⇒ .prop
abbrev HeadFields := [signature.number, signature.element, signature.vector]
abbrev TailFields := [signature.number, signature.element, signature.vector, signature.number, signature.element]

def holds (relation : Term Const Γ (Relation signature))
    (index : Term Const Γ signature.number) (vector : Term Const Γ signature.vector)
    (position : Term Const Γ signature.number) (element : Term Const Γ signature.element) : Formula Const Γ :=
  .app (.app (.app (.app relation index) vector) position) element

@[simp] theorem subst_holds (images : Subst Const Γ Ξ) (relation : Term Const Γ (Relation signature))
    (index : Term Const Γ signature.number) (vector : Term Const Γ signature.vector)
    (position : Term Const Γ signature.number) (element : Term Const Γ signature.element) :
    HOL.subst images (holds signature relation index vector position element) =
      holds signature (HOL.subst images relation) (HOL.subst images index) (HOL.subst images vector)
        (HOL.subst images position) (HOL.subst images element) := rfl

def headBody (relation : Term Const Γ (Relation signature)) : ArgumentBody Const Γ (HeadFields signature) :=
  fun images fields => holds signature (HOL.subst images relation)
    (.app (weakenCtx _ signature.successor) fields.1)
    (signature.consValue fields.1 fields.2.1 fields.2.2.1) (weakenCtx _ signature.zero) fields.2.1

def tailBody (relation : Term Const Γ (Relation signature)) : ArgumentBody Const Γ (TailFields signature) :=
  fun images fields => .imp
    (holds signature (HOL.subst images relation) fields.1 fields.2.2.1 fields.2.2.2.1 fields.2.2.2.2.1)
    (holds signature (HOL.subst images relation) (.app (weakenCtx _ signature.successor) fields.1)
      (signature.consValue fields.1 fields.2.1 fields.2.2.1)
      (.app (weakenCtx _ signature.successor) fields.2.2.2.1) fields.2.2.2.2.1)

theorem headBody_natural (relation : Term Const Γ (Relation signature)) : NaturalBody (headBody signature relation) := by
  intro Δ Ω earlier later fields
  simp only [headBody, subst_holds, HOL.subst, subst_weakenCtx,
    IndexedVectorPredicate.Signature.subst_consValue, HOL.subst_comp, substituteArguments]
  rfl

theorem tailBody_natural (relation : Term Const Γ (Relation signature)) : NaturalBody (tailBody signature relation) := by
  intro Δ Ω earlier later fields
  simp only [tailBody, HOL.subst, subst_holds, subst_weakenCtx,
    IndexedVectorPredicate.Signature.subst_consValue, HOL.subst_comp, substituteArguments]
  rfl

def headRule (relation : Term Const Γ (Relation signature)) : Formula Const Γ :=
  forallArguments (HeadFields signature) (headBody signature relation)

def tailRule (relation : Term Const Γ (Relation signature)) : Formula Const Γ :=
  forallArguments (TailFields signature) (tailBody signature relation)

theorem headRule_subst (images : Subst Const Γ Ξ) (relation : Term Const Γ (Relation signature)) :
    HOL.subst images (headRule signature relation) = headRule signature (HOL.subst images relation) := by
  unfold headRule
  rw [forallArguments_subst _ _ _ (headBody_natural signature relation)]
  apply congrArg (forallArguments (HeadFields signature))
  funext laterContext later fields
  simp only [headBody, HOL.subst_comp]
  rfl

theorem tailRule_subst (images : Subst Const Γ Ξ) (relation : Term Const Γ (Relation signature)) :
    HOL.subst images (tailRule signature relation) = tailRule signature (HOL.subst images relation) := by
  unfold tailRule
  rw [forallArguments_subst _ _ _ (tailBody_natural signature relation)]
  apply congrArg (forallArguments (TailFields signature))
  funext laterContext later fields
  simp only [tailBody, HOL.subst_comp]
  rfl

def closed (relation : Term Const Γ (Relation signature)) : Formula Const Γ :=
  .and (headRule signature relation) (tailRule signature relation)

@[simp] theorem closed_subst (images : Subst Const Γ Ξ) (relation : Term Const Γ (Relation signature)) :
    HOL.subst images (closed signature relation) = closed signature (HOL.subst images relation) := by
  simp only [closed, HOL.subst, headRule_subst, tailRule_subst]

def lookup (index : Term Const Γ signature.number) (vector : Term Const Γ signature.vector)
    (position : Term Const Γ signature.number) (element : Term Const Γ signature.element) : Formula Const Γ :=
  .all (σ := Relation signature) (.imp (closed signature (.var .vz))
    (holds signature (.var .vz) (weaken index) (weaken vector) (weaken position) (weaken element)))

@[simp] theorem lookup_subst (images : Subst Const Γ Ξ)
    (index : Term Const Γ signature.number) (vector : Term Const Γ signature.vector)
    (position : Term Const Γ signature.number) (element : Term Const Γ signature.element) :
    HOL.subst images (lookup signature index vector position element) =
      lookup signature (HOL.subst images index) (HOL.subst images vector)
        (HOL.subst images position) (HOL.subst images element) := by
  simp only [lookup, HOL.subst, closed_subst, subst_holds, subst_weaken, Subst.lift]

@[simp] theorem lookup_rename (rho : Rename Base Γ Ξ)
    (index : Term Const Γ signature.number) (vector : Term Const Γ signature.vector)
    (position : Term Const Γ signature.number) (element : Term Const Γ signature.element) :
    HOL.rename rho (lookup signature index vector position element) =
      lookup signature (HOL.rename rho index) (HOL.rename rho vector)
        (HOL.rename rho position) (HOL.rename rho element) := by
  simpa only [subst_ofRename] using lookup_subst signature (Subst.ofRename rho) index vector position element

variable {Δ : List (Formula Const Γ)}

def headAt (relation : Term Const Γ (Relation signature)) (index : Term Const Γ signature.number)
    (head : Term Const Γ signature.element) (tail : Term Const Γ signature.vector)
    (rule : ProofSyntax Const Δ (headRule signature relation)) :
    ProofSyntax Const Δ (holds signature relation (.app (weakenCtx Γ signature.successor) index)
      (signature.consValue index head tail) (weakenCtx Γ signature.zero) head) := by
  apply ProofSyntax.castIndices rfl ?_
    (forallArguments_elim _ _ (headBody_natural signature relation) (index, head, tail, PUnit.unit) rule)
  simp only [headBody, HOL.subst_id]

def tailAt (relation : Term Const Γ (Relation signature)) (index : Term Const Γ signature.number)
    (head : Term Const Γ signature.element) (tail : Term Const Γ signature.vector)
    (position : Term Const Γ signature.number) (element : Term Const Γ signature.element)
    (rule : ProofSyntax Const Δ (tailRule signature relation)) :
    ProofSyntax Const Δ (.imp (holds signature relation index tail position element)
      (holds signature relation (.app (weakenCtx Γ signature.successor) index)
        (signature.consValue index head tail) (.app (weakenCtx Γ signature.successor) position) element)) := by
  apply ProofSyntax.castIndices rfl ?_
    (forallArguments_elim _ _ (tailBody_natural signature relation)
      (index, head, tail, position, element, PUnit.unit) rule)
  simp only [tailBody, HOL.subst_id]

def eliminate (relation : Term Const Γ (Relation signature)) (index : Term Const Γ signature.number)
    (vector : Term Const Γ signature.vector) (position : Term Const Γ signature.number)
    (element : Term Const Γ signature.element)
    (present : ProofSyntax Const Δ (lookup signature index vector position element))
    (rules : ProofSyntax Const Δ (closed signature relation)) :
    ProofSyntax Const Δ (holds signature relation index vector position element) := by
  apply ProofSyntax.impE (ProofSyntax.castIndices rfl ?_ (.allE relation present)) rules
  simp only [instantiate, HOL.subst, closed_subst, subst_holds, Subst.single,
    PredicateFixedPoint.subst_single_weaken]

def here (index : Term Const Γ signature.number) (head : Term Const Γ signature.element)
    (tail : Term Const Γ signature.vector) :
    ProofSyntax Const Δ (lookup signature (.app (weakenCtx Γ signature.successor) index)
      (signature.consValue index head tail) (weakenCtx Γ signature.zero) head) := by
  refine .allI (.impI ?_)
  apply ProofSyntax.castIndices rfl ?_
    (headAt signature (.var .vz) (weaken index) (weaken head) (weaken tail) (.andEL (.hyp 0)))
  simp only [holds, IndexedVectorPredicate.Signature.consValue, weaken, rename, rename_weakenCtx]

def there (index : Term Const Γ signature.number) (head : Term Const Γ signature.element)
    (tail : Term Const Γ signature.vector) (position : Term Const Γ signature.number)
    (element : Term Const Γ signature.element)
    (present : ProofSyntax Const Δ (lookup signature index tail position element)) :
    ProofSyntax Const Δ (lookup signature (.app (weakenCtx Γ signature.successor) index)
      (signature.consValue index head tail) (.app (weakenCtx Γ signature.successor) position) element) := by
  refine .allI (.impI ?_)
  let relation : Term Const (Relation signature :: Γ) (Relation signature) := .var .vz
  let premise := closed signature relation
  let hypotheses := premise :: weakenHyps Δ
  have given : ProofSyntax Const hypotheses (lookup signature (weaken index) (weaken tail) (weaken position) (weaken element)) :=
    ProofSyntax.castIndices rfl (lookup_rename signature Rename.weaken index tail position element)
      ((PredicateFixedPoint.weakenProof present).prepend premise)
  have previous := eliminate signature relation (weaken index) (weaken tail) (weaken position) (weaken element)
    given (.hyp (Δ := hypotheses) ⟨0, by simp [hypotheses]⟩)
  apply ProofSyntax.castIndices rfl ?_
    (.impE (tailAt signature relation (weaken index) (weaken head) (weaken tail) (weaken position) (weaken element)
      (.andER (.hyp (Δ := hypotheses) ⟨0, by simp [hypotheses]⟩))) previous)
  simp only [relation, holds, IndexedVectorPredicate.Signature.consValue, weaken, rename, rename_weakenCtx]

theorem headAt_free (relation : Term Const Γ (Relation signature)) (index : Term Const Γ signature.number)
    (head : Term Const Γ signature.element) (tail : Term Const Γ signature.vector)
    (rule : ProofSyntax Const Δ (headRule signature relation)) (free : rule.FunctionExtensionalityFree) :
    (headAt signature relation index head tail rule).FunctionExtensionalityFree := by
  unfold headAt
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact forallArguments_elim_free _ _ _ _ rule free

theorem tailAt_free (relation : Term Const Γ (Relation signature)) (index : Term Const Γ signature.number)
    (head : Term Const Γ signature.element) (tail : Term Const Γ signature.vector)
    (position : Term Const Γ signature.number) (element : Term Const Γ signature.element)
    (rule : ProofSyntax Const Δ (tailRule signature relation)) (free : rule.FunctionExtensionalityFree) :
    (tailAt signature relation index head tail position element rule).FunctionExtensionalityFree := by
  unfold tailAt
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact forallArguments_elim_free _ _ _ _ rule free

theorem eliminate_free (relation : Term Const Γ (Relation signature)) (index : Term Const Γ signature.number)
    (vector : Term Const Γ signature.vector) (position : Term Const Γ signature.number)
    (element : Term Const Γ signature.element)
    (present : ProofSyntax Const Δ (lookup signature index vector position element))
    (rules : ProofSyntax Const Δ (closed signature relation))
    (presentFree : present.FunctionExtensionalityFree) (rulesFree : rules.FunctionExtensionalityFree) :
    (eliminate signature relation index vector position element present rules).FunctionExtensionalityFree := by
  simpa only [eliminate, ProofSyntax.FunctionExtensionalityFree, ProofSyntax.functionExtensionalityFree_castIndices]
    using And.intro presentFree rulesFree

theorem here_free (index : Term Const Γ signature.number) (head : Term Const Γ signature.element)
    (tail : Term Const Γ signature.vector) : (here (Δ := Δ) signature index head tail).FunctionExtensionalityFree := by
  unfold here
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact headAt_free signature _ _ _ _ _ True.intro

theorem there_free (index : Term Const Γ signature.number) (head : Term Const Γ signature.element)
    (tail : Term Const Γ signature.vector) (position : Term Const Γ signature.number)
    (element : Term Const Γ signature.element)
    (present : ProofSyntax Const Δ (lookup signature index tail position element))
    (free : present.FunctionExtensionalityFree) :
    (there signature index head tail position element present).FunctionExtensionalityFree := by
  unfold there
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  constructor
  · exact tailAt_free signature _ _ _ _ _ _ _ True.intro
  · apply eliminate_free
    · simpa only [ProofSyntax.functionExtensionalityFree_castIndices, PredicateFixedPoint.weakenProof,
        ProofSyntax.prepend, ProofSyntax.functionExtensionalityFree_mono,
        ProofSyntax.functionExtensionalityFree_rename] using free
    · trivial

abbrev Fields := [signature.number, signature.vector, signature.number, signature.element]

def body : ArgumentBody Const Γ (Fields signature) := fun _ fields =>
  lookup signature fields.1 fields.2.1 fields.2.2.1 fields.2.2.2.1

theorem body_natural : NaturalBody (body (Γ := Γ) signature) := by
  intro Δ Ω earlier later fields
  simp only [body, lookup_subst, substituteArguments]

def code : Term Const Γ (Relation signature) := abstractArguments (Fields signature) (body signature)

theorem code_subst (images : Subst Const Γ Ξ) : HOL.subst images (code (Γ := Γ) signature) = code (Γ := Ξ) signature := by
  unfold code
  rw [abstractArguments_subst _ _ _ (body_natural signature)]
  rfl

def code_apply (index : Term Const Γ signature.number) (vector : Term Const Γ signature.vector)
    (position : Term Const Γ signature.number) (element : Term Const Γ signature.element) :
    ProofSyntax Const Δ (.eq (holds signature (code signature) index vector position element)
      (lookup signature index vector position element)) :=
  abstractArguments_beta _ _ (body_natural signature) (index, vector, position, element, PUnit.unit)

theorem code_apply_free (index : Term Const Γ signature.number) (vector : Term Const Γ signature.vector)
    (position : Term Const Γ signature.number) (element : Term Const Γ signature.element) :
    (code_apply (Δ := Δ) signature index vector position element).FunctionExtensionalityFree :=
  abstractArguments_beta_free _ _ _ _

#print axioms here_free
#print axioms there_free
#print axioms eliminate_free
#print axioms code_apply_free
end Mettapedia.Logic.HOL.IndexedVectorPositions
