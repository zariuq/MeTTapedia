import Mettapedia.Languages.OpenTheory.ExtensionalHOLInterpretation

/-!
# Derived equality rules of the OpenTheory primitive kernel

This module states the primitive OpenTheory rules and HOL Light's derived
equality rules (`equal.ml`, and the rules for truth in `bool.ml`) on one
provability interface:

* `KernelProvable policy hyp concl`: some theorem of the least closure of the
  nine primitive rules under the axiom policy `policy` has the hypothesis set
  `hyp` and a conclusion whose canonical term is `concl`.

Conclusions are de Bruijn terms.  A provable conclusion is a closed Boolean
term (`KernelProvable.inferType`), so rules need typing premises only for the
terms they introduce.  Hypothesis sets are the kernel's alpha-canonical finite
sets, with HOL Light's bookkeeping: `eqMp`, `mkComb` and `trans` take the union
of the hypothesis sets, `deductAntisym` removes each conclusion from the other
side, `proveHyp` removes the proved hypothesis.

The primitive rules are `refl`, `assume`, `eqMp`, `mkComb`, `abs`, `betaConv`,
`deductAntisym`, `subst` and `axiom`.  The derived equality rules are
`apTerm`, `apThm`, `sym`, `trans`, `alpha`, `convRule`, `betaConvTwice`,
`proveHyp`, `addAssum`, `weaken`, `truth`, `eqtElim` and `eqtIntro`.

The module also supplies the syntactic infrastructure for the connective and
eta libraries: closed terms are fixed by `instantiateAt` and by `closeFreeAt`
of an absent variable, and every finite set of terms has a fresh variable
(`exists_fresh_var`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.OpenTheory

open Mettapedia.Logic

namespace DBTerm

/-! ## Loose indices and instantiation -/

theorem LooseBelow.mono : ∀ {depth depth' : Nat} {term : DBTerm},
    term.LooseBelow depth → depth ≤ depth' → term.LooseBelow depth'
  | _, _, .const _ _, _, _ => trivial
  | _, _, .free _, _, _ => trivial
  | _, _, .bound _, hloose, hle => Nat.lt_of_lt_of_le hloose hle
  | _, _, .app _ _, hloose, hle => ⟨LooseBelow.mono hloose.1 hle, LooseBelow.mono hloose.2 hle⟩
  | _, _, .abs _ body, hloose, hle =>
      LooseBelow.mono (term := body) hloose (Nat.succ_le_succ hle)

/-- Instantiation at a depth above every loose index changes nothing. -/
theorem instantiateAt_of_looseBelow (replacement : DBTerm) :
    ∀ {depth : Nat} {term : DBTerm}, term.LooseBelow depth →
      instantiateAt replacement depth term = term
  | _, .const _ _, _ => by simp [instantiateAt]
  | _, .free _, _ => by simp [instantiateAt]
  | _, .bound _, hloose => by simp [instantiateAt, Nat.ne_of_lt hloose]
  | _, .app _ _, hloose => by
      simp only [instantiateAt]
      rw [instantiateAt_of_looseBelow replacement hloose.1,
        instantiateAt_of_looseBelow replacement hloose.2]
  | _, .abs _ body, hloose => by
      simp only [instantiateAt]
      rw [instantiateAt_of_looseBelow replacement (term := body) hloose]

/-- A closed well-typed term is fixed by instantiation at every depth. -/
theorem instantiateAt_closed {term : DBTerm} {ty : Ty} (checked : term.inferType [] = some ty)
    (replacement : DBTerm) (depth : Nat) : instantiateAt replacement depth term = term :=
  instantiateAt_of_looseBelow replacement
    (LooseBelow.mono (looseBelow_of_inferType checked) (Nat.zero_le depth))

/-! ## Free variables -/

/-- The names of the free variables of a term. -/
def freeNames : DBTerm → Finset Name
  | .const _ _ => ∅
  | .free sourceVar => {sourceVar.name}
  | .bound _ => ∅
  | .app function argument => function.freeNames ∪ argument.freeNames
  | .abs _ body => body.freeNames

theorem name_mem_freeNames {sourceVar : SourceVar} {term : DBTerm}
    (occurrence : FreeOccurrence sourceVar term) : sourceVar.name ∈ term.freeNames := by
  induction occurrence with
  | here => simp [freeNames]
  | appFunction _ ih => exact Finset.mem_union_left _ ih
  | appArgument _ ih => exact Finset.mem_union_right _ ih
  | absBody _ ih => exact ih

theorem not_freeOccurrence_of_freeNames_eq_empty {term : DBTerm}
    (empty : term.freeNames = ∅) (sourceVar : SourceVar) :
    ¬ FreeOccurrence sourceVar term := fun occurrence => by
  have := name_mem_freeNames occurrence
  rw [empty] at this
  exact Finset.notMem_empty _ this

/-- Closing an absent variable changes nothing. -/
theorem closeFreeAt_of_not_freeOccurrence {sourceVar : SourceVar} :
    ∀ {term : DBTerm}, ¬ FreeOccurrence sourceVar term →
      ∀ depth, closeFreeAt sourceVar depth term = term
  | .const _ _, _, _ => by simp [closeFreeAt]
  | .free other, absent, _ => by
      have different : sourceVar ≠ other := by
        rintro rfl
        exact absent .here
      exact closeFreeAt_other sourceVar other _ different
  | .bound _, _, _ => by simp [closeFreeAt]
  | .app function argument, absent, depth => by
      simp only [closeFreeAt]
      rw [closeFreeAt_of_not_freeOccurrence (fun h => absent (.appFunction h)) depth,
        closeFreeAt_of_not_freeOccurrence (fun h => absent (.appArgument h)) depth]
  | .abs _ body, absent, depth => by
      simp only [closeFreeAt]
      rw [closeFreeAt_of_not_freeOccurrence (term := body) (fun h => absent (.absBody h))]

/-! ## Typing -/

theorem inferType_app_of {context : List Ty} {function argument : DBTerm}
    {domain codomain : Ty}
    (hfunction : function.inferType context = some (.function domain codomain))
    (hargument : argument.inferType context = some domain) :
    (DBTerm.app function argument).inferType context = some codomain :=
  inferType_app_eq_some_iff.mpr ⟨domain, hfunction, hargument⟩

theorem inferType_abs_of {context : List Ty} {domain codomain : Ty} {body : DBTerm}
    (hbody : body.inferType (domain :: context) = some codomain) :
    (DBTerm.abs domain body).inferType context = some (.function domain codomain) :=
  inferType_abs_eq_some_iff.mpr ⟨codomain, hbody, rfl⟩

theorem inferType_equality_const (context : List Ty) (operand : Ty) :
    (DBTerm.const Const.equality (Ty.equality operand)).inferType context =
      some (.function operand (.function operand Ty.bool)) := by
  rw [DBTerm.inferType.eq_1]
  rfl

theorem inferType_equalityDB_iff {context : List Ty} {operand : Ty} {left right : DBTerm}
    {ty : Ty} :
    (CanonicalTerm.equalityDB operand left right).inferType context = some ty ↔
      left.inferType context = some operand ∧ right.inferType context = some operand ∧
        ty = Ty.bool := by
  constructor
  · intro h
    obtain ⟨d₁, houter, hright⟩ := inferType_app_eq_some_iff.mp h
    obtain ⟨d₀, hconst, hleft⟩ := inferType_app_eq_some_iff.mp houter
    rw [inferType_equality_const] at hconst
    obtain ⟨rfl, hrest⟩ := Ty.function_inj (Option.some.inj hconst)
    obtain ⟨rfl, rfl⟩ := Ty.function_inj hrest
    exact ⟨hleft, hright, rfl⟩
  · rintro ⟨hleft, hright, rfl⟩
    exact inferType_app_of (inferType_app_of (inferType_equality_const _ _) hleft) hright

theorem inferType_equalityDB {context : List Ty} {operand : Ty} {left right : DBTerm}
    (hleft : left.inferType context = some operand)
    (hright : right.inferType context = some operand) :
    (CanonicalTerm.equalityDB operand left right).inferType context = some Ty.bool :=
  inferType_equalityDB_iff.mpr ⟨hleft, hright, rfl⟩

/-- Inferred types are unique. -/
theorem inferType_unique {context : List Ty} {term : DBTerm} {ty ty' : Ty}
    (h : term.inferType context = some ty) (h' : term.inferType context = some ty') :
    ty = ty' :=
  Option.some.inj (h.symm.trans h')

/-- Instantiating the outermost binder of a context by a closed term of the
binder's type: the instance is typed only if the body is.  This is the
converse of `inferType_instantiateAt`. -/
theorem inferType_of_inferType_instantiateAt {replacement : DBTerm} {targetTy : Ty}
    (replacementChecked : replacement.inferType [] = some targetTy) :
    ∀ (term : DBTerm) (context : List Ty) {ty : Ty},
      (instantiateAt replacement context.length term).inferType context = some ty →
        term.inferType (context ++ [targetTy]) = some ty
  | .const _ _, _, _, h => by simpa [instantiateAt] using h
  | .free _, _, _, h => by simpa [instantiateAt] using h
  | .bound index, context, ty, h => by
      by_cases target : index = context.length
      · subst index
        simp only [instantiateAt, if_pos] at h
        have hweak := inferType_weaken_empty replacementChecked context
        rw [inferType_unique h hweak]
        simp
      · simp only [instantiateAt, if_neg target, DBTerm.inferType.eq_3] at h
        have hlt : index < context.length := (List.getElem?_eq_some_iff.mp h).1
        simp only [DBTerm.inferType.eq_3]
        rw [List.getElem?_append_left hlt]
        exact h
  | .app function argument, context, ty, h => by
      simp only [instantiateAt] at h
      obtain ⟨domain, hfunction, hargument⟩ := inferType_app_eq_some_iff.mp h
      exact inferType_app_of
        (inferType_of_inferType_instantiateAt replacementChecked function context hfunction)
        (inferType_of_inferType_instantiateAt replacementChecked argument context hargument)
  | .abs domain body, context, ty, h => by
      simp only [instantiateAt] at h
      obtain ⟨codomain, hbody, rfl⟩ := inferType_abs_eq_some_iff.mp h
      have hbody' := inferType_of_inferType_instantiateAt replacementChecked body
        (domain :: context) (by simpa using hbody)
      exact inferType_abs_of (by simpa using hbody')

/-- A term whose loose indices lie below the length of a context has the same
type under every extension of that context. -/
theorem inferType_append_of_looseBelow :
    ∀ {term : DBTerm} {context : List Ty} (extra : List Ty),
      term.LooseBelow context.length →
        term.inferType (context ++ extra) = term.inferType context
  | .const _ _, _, _, _ => by simp
  | .free _, _, _, _ => by simp
  | .bound _, _, _, hloose => by
      simp only [DBTerm.inferType.eq_3]
      exact List.getElem?_append_left hloose
  | .app _ _, _, extra, hloose => by
      simp only [DBTerm.inferType.eq_4]
      rw [inferType_append_of_looseBelow extra hloose.1,
        inferType_append_of_looseBelow extra hloose.2]
  | .abs domain body, context, extra, hloose => by
      simp only [DBTerm.inferType.eq_5]
      rw [show domain :: (context ++ extra) = (domain :: context) ++ extra from rfl,
        inferType_append_of_looseBelow (term := body) (context := domain :: context) extra
          hloose]

/-- A closed term has the same type under every context. -/
theorem inferType_of_looseBelow_zero {term : DBTerm} (closed : term.LooseBelow 0)
    (context : List Ty) : term.inferType context = term.inferType [] :=
  inferType_append_of_looseBelow (context := []) context closed

end DBTerm

/-! ## Fresh variables -/

/-- Infinitely many names: the namespaces of every length. -/
instance : Infinite Name :=
  Infinite.of_injective (fun length : Nat => (⟨List.replicate length "", ""⟩ : Name))
    fun left right h => by
      simpa using congrArg (fun name : Name => name.namespaceComponents.length) h

/-- The names of the free variables of a hypothesis set. -/
def hypothesesFreeNames (hyp : Finset CanonicalTerm) : Finset Name :=
  hyp.biUnion fun term => term.term.freeNames

theorem not_freeInHypotheses_of_name_notMem {sourceVar : SourceVar}
    {hyp : Finset CanonicalTerm} (fresh : sourceVar.name ∉ hypothesesFreeNames hyp) :
    ¬ FreeInHypotheses sourceVar hyp := by
  rintro ⟨term, hterm, occurrence⟩
  exact fresh (Finset.mem_biUnion.mpr ⟨term, hterm, DBTerm.name_mem_freeNames occurrence⟩)

theorem freeInHypotheses_mono {sourceVar : SourceVar} {hyp hyp' : Finset CanonicalTerm}
    (subset : hyp ⊆ hyp') (occurs : FreeInHypotheses sourceVar hyp) :
    FreeInHypotheses sourceVar hyp' := by
  obtain ⟨term, hterm, occurrence⟩ := occurs
  exact ⟨term, subset hterm, occurrence⟩

/-- **Fresh variables.**  At every type there is a variable free in no
hypothesis of a finite set and in no term of a finite list. -/
theorem exists_fresh_var (ty : Ty) (hyp : Finset CanonicalTerm) (terms : List DBTerm) :
    ∃ sourceVar : SourceVar, sourceVar.ty = ty ∧ ¬ FreeInHypotheses sourceVar hyp ∧
      ∀ term ∈ terms, ¬ DBTerm.FreeOccurrence sourceVar term := by
  obtain ⟨name, hname⟩ := Infinite.exists_notMem_finset
    (hypothesesFreeNames hyp ∪ terms.foldr (fun term names => term.freeNames ∪ names) ∅)
  refine ⟨⟨name, ty⟩, rfl, not_freeInHypotheses_of_name_notMem fun h =>
    hname (Finset.mem_union_left _ h), fun term hterm occurrence => hname
      (Finset.mem_union_right _ ?_)⟩
  have hmem := DBTerm.name_mem_freeNames occurrence
  clear hname occurrence
  induction terms with
  | nil => simp at hterm
  | cons head tail ih =>
      rcases List.mem_cons.mp hterm with rfl | htail
      · exact Finset.mem_union_left _ hmem
      · exact Finset.mem_union_right _ (ih htail)

/-! ## Truth -/

namespace DerivedRules

theorem inferType_identityBool {context : List Ty} :
    PrimitiveSentences.identityBool.inferType context = some (.function Ty.bool Ty.bool) :=
  DBTerm.inferType_abs_of (by simp)

theorem inferType_truthDB {context : List Ty} :
    PrimitiveSentences.truthDB.inferType context = some Ty.bool :=
  DBTerm.inferType_equalityDB inferType_identityBool inferType_identityBool

/-- The checked truth term `T`. -/
def truthTerm : CanonicalTerm := ⟨PrimitiveSentences.truthDB, Ty.bool, inferType_truthDB⟩

end DerivedRules

/-! ## The provability interface -/

/-- Some theorem of the least closure of the primitive rules under `policy`
has hypothesis set `hyp` and a conclusion with canonical term `concl`. -/
def KernelProvable (policy : AxiomPolicy) (hyp : Finset CanonicalTerm) (concl : DBTerm) :
    Prop :=
  ∃ out : Theorem, Derives (PolicyPrimitiveRule policy) out ∧
    out.sequent.hyp = hyp ∧ out.sequent.concl.term = concl

/-- For a checked conclusion, provability is derivability of the exact
sequent. -/
theorem kernelProvable_iff_derives_sequent {policy : AxiomPolicy}
    {hyp : Finset CanonicalTerm} (concl : CanonicalTerm) :
    KernelProvable policy hyp concl.term ↔
      ∃ out : Theorem, Derives (PolicyPrimitiveRule policy) out ∧
        out.sequent = ⟨hyp, concl⟩ := by
  constructor
  · rintro ⟨out, hout, hhyp, hconcl⟩
    exact ⟨out, hout, Sequent.ext hhyp (CanonicalTerm.ext_term hconcl)⟩
  · rintro ⟨out, hout, hsequent⟩
    exact ⟨out, hout, by rw [hsequent], by rw [hsequent]⟩

namespace KernelProvable

open CanonicalTerm (equalityDB)
open DBTerm

variable {policy : AxiomPolicy}

/-- A provable conclusion is a closed Boolean term. -/
theorem inferType {hyp : Finset CanonicalTerm} {concl : DBTerm}
    (h : KernelProvable policy hyp concl) : concl.inferType [] = some Ty.bool := by
  obtain ⟨out, hout, -, rfl⟩ := h
  rw [out.sequent.concl.checked]
  exact congrArg some (derives_isBool hout).1

/-- Every hypothesis of a provable sequent is Boolean. -/
theorem hyp_isBool {hyp : Finset CanonicalTerm} {concl : DBTerm}
    (h : KernelProvable policy hyp concl) : ∀ term ∈ hyp, term.IsBool := by
  obtain ⟨out, hout, rfl, -⟩ := h
  exact (derives_isBool hout).2

/-- The Boolean checked term of a provable conclusion. -/
def conclTerm {hyp : Finset CanonicalTerm} {concl : DBTerm}
    (h : KernelProvable policy hyp concl) : CanonicalTerm :=
  ⟨concl, Ty.bool, h.inferType⟩

@[simp] theorem conclTerm_term {hyp : Finset CanonicalTerm} {concl : DBTerm}
    (h : KernelProvable policy hyp concl) : h.conclTerm.term = concl := rfl

/-- The operands of a provable equation have its operand type. -/
theorem inferType_equality_operands {hyp : Finset CanonicalTerm} {operand : Ty}
    {left right : DBTerm}
    (h : KernelProvable policy hyp (equalityDB operand left right)) :
    left.inferType [] = some operand ∧ right.inferType [] = some operand := by
  obtain ⟨hleft, hright, -⟩ := inferType_equalityDB_iff.mp h.inferType
  exact ⟨hleft, hright⟩

theorem congr_hyp {hyp hyp' : Finset CanonicalTerm} {concl : DBTerm}
    (h : KernelProvable policy hyp concl) (equal : hyp = hyp') :
    KernelProvable policy hyp' concl :=
  equal ▸ h

/-! ### Primitive rules -/

private theorem derives_of_step (request : PrimitiveRequest) (out : Theorem)
    (premisesDerive :
      ∀ premise ∈ request.premises, Derives (PolicyPrimitiveRule policy) premise)
    (inputsAllowed : request.InputAxiomsAllowed policy)
    (step : PrimitiveStep request out) : Derives (PolicyPrimitiveRule policy) out :=
  Derives.node request.premises out ⟨request, rfl, inputsAllowed, step⟩ premisesDerive

/-- REFL: `⊢ a = a`. -/
theorem refl {term : DBTerm} {ty : Ty} (checked : term.inferType [] = some ty) :
    KernelProvable policy ∅ (equalityDB ty term term) := by
  let operand : CanonicalTerm := ⟨term, ty, checked⟩
  let equality : CanonicalTerm :=
    ⟨equalityDB ty term term, Ty.bool, inferType_equalityDB checked checked⟩
  refine ⟨Theorem.emptyResult ∅ equality, derives_of_step (.core (.refl operand)) _
    (by simp [PrimitiveRequest.premises]) trivial
    ⟨.core (.refl equality ⟨rfl, rfl⟩ ⟨rfl, rfl, rfl⟩)⟩, rfl, rfl⟩

/-- ASSUME: `p ⊢ p` for a Boolean term `p`. -/
theorem assume (term : CanonicalTerm) (hbool : term.IsBool) :
    KernelProvable policy {term} term.term :=
  ⟨Theorem.emptyResult {term} term, derives_of_step (.core (.assume term)) _
    (by simp [PrimitiveRequest.premises]) trivial
    ⟨.core (.assume hbool ⟨rfl, rfl, rfl⟩)⟩, rfl, rfl⟩

/-- EQ_MP: from `A ⊢ p = q` and `B ⊢ p` derive `A ∪ B ⊢ q`. -/
theorem eqMp {hypEq hyp : Finset CanonicalTerm} {left right : DBTerm}
    (hequality : KernelProvable policy hypEq (equalityDB Ty.bool left right))
    (hpremise : KernelProvable policy hyp left) :
    KernelProvable policy (hypEq ∪ hyp) right := by
  have hright := (inferType_equality_operands hequality).2
  obtain ⟨equalityThm, hderivesEq, rfl, hconclEq⟩ := hequality
  obtain ⟨premiseThm, hderives, rfl, hconcl⟩ := hpremise
  let rightTerm : CanonicalTerm := ⟨right, Ty.bool, hright⟩
  have hleftBool : premiseThm.sequent.concl.ty = Ty.bool := (derives_isBool hderives).1
  refine ⟨Theorem.unionResult equalityThm premiseThm
      (equalityThm.sequent.hyp ∪ premiseThm.sequent.hyp) rightTerm,
    derives_of_step (.core (.eqMp equalityThm premiseThm)) _ ?_
      ⟨derives_only_authorized_axioms policy hderivesEq,
        derives_only_authorized_axioms policy hderives⟩
      ⟨.core (.eqMp premiseThm.sequent.concl rightTerm ⟨hleftBool, ?_⟩ rfl
        ⟨rfl, rfl, rfl⟩)⟩, rfl, rfl⟩
  · intro premise hmem
    simp only [PrimitiveRequest.premises, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl
    · exact hderivesEq
    · exact hderives
  · rw [hconclEq, hleftBool, hconcl]

/-- MK_COMB: from `A ⊢ f = g` and `B ⊢ x = y` derive `A ∪ B ⊢ f x = g y`. -/
theorem mkComb {hypFunction hypArgument : Finset CanonicalTerm} {domain codomain : Ty}
    {functionLeft functionRight argumentLeft argumentRight : DBTerm}
    (hfunction : KernelProvable policy hypFunction
      (equalityDB (.function domain codomain) functionLeft functionRight))
    (hargument : KernelProvable policy hypArgument
      (equalityDB domain argumentLeft argumentRight)) :
    KernelProvable policy (hypFunction ∪ hypArgument)
      (equalityDB codomain (.app functionLeft argumentLeft)
        (.app functionRight argumentRight)) := by
  obtain ⟨hfl, hfr⟩ := inferType_equality_operands hfunction
  obtain ⟨hal, har⟩ := inferType_equality_operands hargument
  obtain ⟨functionThm, hderivesF, rfl, hconclF⟩ := hfunction
  obtain ⟨argumentThm, hderivesA, rfl, hconclA⟩ := hargument
  let fl : CanonicalTerm := ⟨functionLeft, _, hfl⟩
  let fr : CanonicalTerm := ⟨functionRight, _, hfr⟩
  let al : CanonicalTerm := ⟨argumentLeft, _, hal⟩
  let ar : CanonicalTerm := ⟨argumentRight, _, har⟩
  let appl : CanonicalTerm :=
    ⟨.app functionLeft argumentLeft, codomain, inferType_app_of hfl hal⟩
  let appr : CanonicalTerm :=
    ⟨.app functionRight argumentRight, codomain, inferType_app_of hfr har⟩
  let equality : CanonicalTerm :=
    ⟨equalityDB codomain appl.term appr.term, Ty.bool,
      inferType_equalityDB appl.checked appr.checked⟩
  refine ⟨Theorem.unionResult functionThm argumentThm
      (functionThm.sequent.hyp ∪ argumentThm.sequent.hyp) equality,
    derives_of_step (.core (.app functionThm argumentThm)) _ ?_
      ⟨derives_only_authorized_axioms policy hderivesF,
        derives_only_authorized_axioms policy hderivesA⟩
      ⟨.core (.app fl fr al ar appl appr equality ⟨rfl, hconclF⟩ ⟨rfl, hconclA⟩
        ⟨domain, codomain, Ty.destFunction?_function _ _, rfl, rfl⟩
        ⟨domain, codomain, Ty.destFunction?_function _ _, rfl, rfl⟩
        ⟨rfl, rfl⟩ ⟨rfl, rfl, rfl⟩)⟩, rfl, rfl⟩
  intro premise hmem
  simp only [PrimitiveRequest.premises, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl
  · exact hderivesF
  · exact hderivesA

/-- ABS: from `A ⊢ l = r`, with `v` not free in `A`, derive
`A ⊢ (λv. l) = (λv. r)`. -/
theorem abs {hyp : Finset CanonicalTerm} {ty : Ty} {left right : DBTerm} (sourceVar : SourceVar)
    (h : KernelProvable policy hyp (equalityDB ty left right))
    (fresh : ¬ FreeInHypotheses sourceVar hyp) :
    KernelProvable policy hyp
      (equalityDB (.function sourceVar.ty ty)
        (.abs sourceVar.ty (closeFreeAt sourceVar 0 left))
        (.abs sourceVar.ty (closeFreeAt sourceVar 0 right))) := by
  obtain ⟨hl, hr⟩ := inferType_equality_operands h
  obtain ⟨input, hderives, rfl, hconcl⟩ := h
  let l : CanonicalTerm := ⟨left, ty, hl⟩
  let r : CanonicalTerm := ⟨right, ty, hr⟩
  let equality : CanonicalTerm :=
    ⟨equalityDB (.function sourceVar.ty ty) (l.abstractFree sourceVar).term
      (r.abstractFree sourceVar).term, Ty.bool,
      inferType_equalityDB (l.abstractFree sourceVar).checked (r.abstractFree sourceVar).checked⟩
  refine ⟨Theorem.preserveAxiomsResult input input.sequent.hyp equality,
    derives_of_step (.binding (.abs sourceVar input)) _ ?_
      (derives_only_authorized_axioms policy hderives)
      ⟨.binding (.abs fresh l r (l.abstractFree sourceVar) (r.abstractFree sourceVar) equality
        ⟨rfl, hconcl⟩ rfl rfl ⟨rfl, rfl⟩ ⟨rfl, rfl, rfl⟩)⟩, rfl, rfl⟩
  intro premise hmem
  simp only [PrimitiveRequest.premises, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rw [hmem]
  exact hderives

/-- BETA_CONV: `⊢ (λx. t) u = t[u/x]` for every checked closed redex. -/
theorem betaConv {domain ty : Ty} {body argument : DBTerm}
    (checked : (DBTerm.app (.abs domain body) argument).inferType [] = some ty) :
    KernelProvable policy ∅
      (equalityDB ty (.app (.abs domain body) argument) (instantiateAt argument 0 body)) := by
  obtain ⟨domain', habs, hargument⟩ := inferType_app_eq_some_iff.mp checked
  obtain ⟨codomain, hbody, hfun⟩ := inferType_abs_eq_some_iff.mp habs
  obtain ⟨rfl, rfl⟩ := Ty.function_inj hfun.symm
  let redex : CanonicalTerm := ⟨.app (.abs domain body) argument, _, checked⟩
  let argumentTerm : CanonicalTerm := ⟨argument, _, hargument⟩
  let reduced : CanonicalTerm :=
    ⟨instantiateAt argument 0 body, _,
      inferType_instantiateAt argument body domain hargument [] (by simpa using hbody)⟩
  let equality : CanonicalTerm :=
    ⟨equalityDB codomain redex.term reduced.term, Ty.bool,
      inferType_equalityDB redex.checked reduced.checked⟩
  exact ⟨Theorem.emptyResult ∅ equality, derives_of_step (.binding (.betaConv redex)) _
    (by simp [PrimitiveRequest.premises]) trivial
    ⟨.binding (.betaConv reduced equality ⟨domain, body, argumentTerm, rfl, rfl⟩
      ⟨rfl, rfl⟩ ⟨rfl, rfl, rfl⟩)⟩, rfl, rfl⟩

/-- DEDUCT_ANTISYM_RULE: from `A ⊢ p` and `B ⊢ q` derive
`(A - {q}) ∪ (B - {p}) ⊢ p = q`. -/
theorem deductAntisym {hypLeft hypRight : Finset CanonicalTerm} (left right : CanonicalTerm)
    (hleft : KernelProvable policy hypLeft left.term)
    (hright : KernelProvable policy hypRight right.term) :
    KernelProvable policy (hypLeft.erase right ∪ hypRight.erase left)
      (equalityDB Ty.bool left.term right.term) := by
  obtain ⟨leftThm, hderivesL, rfl, hconclL⟩ := hleft
  obtain ⟨rightThm, hderivesR, rfl, hconclR⟩ := hright
  have hl : leftThm.sequent.concl = left := CanonicalTerm.ext_term hconclL
  have hr : rightThm.sequent.concl = right := CanonicalTerm.ext_term hconclR
  have hlBool : leftThm.sequent.concl.ty = Ty.bool := (derives_isBool hderivesL).1
  have hrBool : rightThm.sequent.concl.ty = Ty.bool := (derives_isBool hderivesR).1
  let equality : CanonicalTerm :=
    ⟨equalityDB Ty.bool left.term right.term, Ty.bool, inferType_equalityDB
      (by rw [← hl, ← hlBool]; exact leftThm.sequent.concl.checked)
      (by rw [← hr, ← hrBool]; exact rightThm.sequent.concl.checked)⟩
  refine ⟨Theorem.unionResult leftThm rightThm
      ((leftThm.sequent.hyp.erase rightThm.sequent.concl) ∪
        (rightThm.sequent.hyp.erase leftThm.sequent.concl)) equality,
    derives_of_step (.core (.deductAntisym leftThm rightThm)) _ ?_
      ⟨derives_only_authorized_axioms policy hderivesL,
        derives_only_authorized_axioms policy hderivesR⟩
      ⟨.core (.deductAntisym equality ⟨hlBool.trans hrBool.symm, ?_⟩ ⟨rfl, rfl, rfl⟩)⟩,
    by simp [Theorem.unionResult, hl, hr], rfl⟩
  · intro premise hmem
    simp only [PrimitiveRequest.premises, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl
    · exact hderivesL
    · exact hderivesR
  · rw [hlBool, hl, hr]

/-- INST and INST_TYPE: a type-correct simultaneous substitution applied to
the hypotheses and the conclusion. -/
theorem subst {hyp : Finset CanonicalTerm} {concl : DBTerm}
    (substitution : TypeCorrectTermSubstitution) (h : KernelProvable policy hyp concl) :
    KernelProvable policy (substitution.applyHypotheses hyp)
      (substitution.raw.applyDB concl) := by
  obtain ⟨input, hderives, rfl, rfl⟩ := h
  refine ⟨substituteTheorem substitution input,
    derives_of_step (.subst substitution input) _ ?_
      (derives_only_authorized_axioms policy hderives)
      ⟨.subst (substituteTheorem_semantics substitution input)⟩, rfl, rfl⟩
  intro premise hmem
  simp only [PrimitiveRequest.premises, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rw [hmem]
  exact hderives

/-- An admitted axiom sequent is provable. -/
theorem «axiom» (sequent : Sequent) (admitted : policy sequent) (hbool : sequent.IsBool) :
    KernelProvable policy sequent.hyp sequent.concl.term :=
  ⟨Theorem.axiomResult sequent hbool, derives_of_step (.core (.axiom sequent)) _
    (by simp [PrimitiveRequest.premises]) admitted
    ⟨.core (.axiom hbool ⟨rfl, rfl, rfl⟩)⟩, rfl, rfl⟩

/-! ### Derived equality rules -/

/-- AP_TERM: from `A ⊢ x = y` derive `A ⊢ f x = f y`. -/
theorem apTerm {hyp : Finset CanonicalTerm} {domain codomain : Ty}
    {function left right : DBTerm}
    (hfunction : function.inferType [] = some (.function domain codomain))
    (h : KernelProvable policy hyp (equalityDB domain left right)) :
    KernelProvable policy hyp
      (equalityDB codomain (.app function left) (.app function right)) :=
  (mkComb (refl hfunction) h).congr_hyp (Finset.empty_union hyp)

/-- AP_THM: from `A ⊢ f = g` derive `A ⊢ f x = g x`. -/
theorem apThm {hyp : Finset CanonicalTerm} {domain codomain : Ty}
    {left right argument : DBTerm}
    (h : KernelProvable policy hyp (equalityDB (.function domain codomain) left right))
    (hargument : argument.inferType [] = some domain) :
    KernelProvable policy hyp
      (equalityDB codomain (.app left argument) (.app right argument)) :=
  (mkComb h (refl hargument)).congr_hyp (Finset.union_empty hyp)

/-- SYM: from `A ⊢ l = r` derive `A ⊢ r = l`. -/
theorem sym {hyp : Finset CanonicalTerm} {ty : Ty} {left right : DBTerm}
    (h : KernelProvable policy hyp (equalityDB ty left right)) :
    KernelProvable policy hyp (equalityDB ty right left) := by
  have hleft := (inferType_equality_operands h).1
  have congruence := mkComb (apTerm (inferType_equality_const [] ty) h) (refl hleft)
  exact (eqMp congruence (refl hleft)).congr_hyp (by simp)

/-- TRANS: from `A ⊢ a = b` and `B ⊢ b = c` derive `A ∪ B ⊢ a = c`. -/
theorem trans {hyp hyp' : Finset CanonicalTerm} {ty : Ty} {first middle last : DBTerm}
    (hfirst : KernelProvable policy hyp (equalityDB ty first middle))
    (hlast : KernelProvable policy hyp' (equalityDB ty middle last)) :
    KernelProvable policy (hyp ∪ hyp') (equalityDB ty first last) := by
  have hleft := (inferType_equality_operands hfirst).1
  have congruence := apTerm (inferType_app_of (inferType_equality_const [] ty) hleft) hlast
  exact (eqMp congruence hfirst).congr_hyp (Finset.union_comm hyp' hyp)

/-- ALPHA: alpha-equivalent named terms are provably equal. -/
theorem alpha {left right : SourceTerm} {ty : Ty} (halpha : left.AlphaEq right)
    (hleft : left.inferType = some ty) :
    KernelProvable policy ∅ (equalityDB ty (left.toDB []) (right.toDB [])) := by
  rw [← (SourceTerm.alphaEq_iff_toDB_eq left right).mp halpha]
  exact refl (by simpa using (inferType_toDB [] left).trans hleft)

/-- CONV_RULE: rewrite a conclusion by an equation without hypotheses. -/
theorem convRule {hyp : Finset CanonicalTerm} {left right : DBTerm}
    (hconv : KernelProvable policy ∅ (equalityDB Ty.bool left right))
    (h : KernelProvable policy hyp left) : KernelProvable policy hyp right :=
  (eqMp hconv h).congr_hyp (Finset.empty_union hyp)

/-- Two successive beta conversions:
`⊢ (λx y. t) a b = t[a/x][b/y]`. -/
theorem betaConvTwice {first second : Ty} {ty : Ty} {body left right : DBTerm}
    (checked : (DBTerm.app (.app (.abs first (.abs second body)) left) right).inferType [] =
      some ty) :
    KernelProvable policy ∅
      (equalityDB ty (.app (.app (.abs first (.abs second body)) left) right)
        (instantiateAt right 0 (instantiateAt left 1 body))) := by
  obtain ⟨second', hinner, hright⟩ := inferType_app_eq_some_iff.mp checked
  have hstep : instantiateAt left 0 (.abs second body) =
      .abs second (instantiateAt left 1 body) := by
    simp [instantiateAt]
  have hfirst := betaConv (policy := policy) hinner
  rw [hstep] at hfirst
  have hsecond := apThm hfirst hright
  have hreduced := betaConv (policy := policy) (inferType_equality_operands hsecond).2
  exact (trans hsecond hreduced).congr_hyp (Finset.empty_union ∅)

/-- PROVE_HYP: from `A ⊢ a` and `B ⊢ b` derive `A ∪ (B - {a}) ⊢ b`. -/
theorem proveHyp {hyp hyp' : Finset CanonicalTerm} {concl : DBTerm} (proved : CanonicalTerm)
    (hproved : KernelProvable policy hyp proved.term)
    (h : KernelProvable policy hyp' concl) :
    KernelProvable policy (hyp ∪ hyp'.erase proved) concl := by
  refine (eqMp (deductAntisym proved h.conclTerm hproved h) hproved).congr_hyp ?_
  ext term
  simp only [Finset.mem_union, Finset.mem_erase]
  tauto

/-- ADD_ASSUM: from `A ⊢ q` derive `A ∪ {p} ⊢ q` for a Boolean term `p`. -/
theorem addAssum {hyp : Finset CanonicalTerm} {concl : DBTerm} (term : CanonicalTerm)
    (hbool : term.IsBool) (h : KernelProvable policy hyp concl) :
    KernelProvable policy (insert term hyp) concl := by
  refine (proveHyp term (assume term hbool) h).congr_hyp ?_
  ext other
  simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_erase, Finset.mem_insert]
  by_cases hother : other = term <;> simp [hother]

/-- Weakening to a Boolean superset of the hypotheses. -/
theorem weaken {hyp hyp' : Finset CanonicalTerm} {concl : DBTerm}
    (h : KernelProvable policy hyp concl) (subset : hyp ⊆ hyp')
    (hbool : ∀ term ∈ hyp', term.IsBool) : KernelProvable policy hyp' concl := by
  suffices extended : ∀ extra : Finset CanonicalTerm, (∀ term ∈ extra, term.IsBool) →
      KernelProvable policy (extra ∪ hyp) concl by
    exact (extended hyp' hbool).congr_hyp (Finset.union_eq_left.mpr subset)
  intro extra hextra
  induction extra using Finset.induction_on with
  | empty => exact h.congr_hyp (Finset.empty_union hyp).symm
  | @insert term extra _ ih =>
      rw [Finset.insert_union]
      exact addAssum term (hextra term (Finset.mem_insert_self term extra))
        (ih fun other hother => hextra other (Finset.mem_insert_of_mem hother))

/-! ### Truth -/

/-- TRUTH: `⊢ T`. -/
theorem truth : KernelProvable policy ∅ PrimitiveSentences.truthDB :=
  refl DerivedRules.inferType_identityBool

/-- EQT_ELIM: from `A ⊢ t = T` derive `A ⊢ t`. -/
theorem eqtElim {hyp : Finset CanonicalTerm} {term : DBTerm}
    (h : KernelProvable policy hyp (equalityDB Ty.bool term PrimitiveSentences.truthDB)) :
    KernelProvable policy hyp term :=
  (eqMp (sym h) truth).congr_hyp (Finset.union_empty hyp)

/-- EQT_INTRO: from `A ⊢ t` derive `A ⊢ t = T`. -/
theorem eqtIntro {hyp : Finset CanonicalTerm} {term : DBTerm}
    (h : KernelProvable policy hyp term) :
    KernelProvable policy hyp (equalityDB Ty.bool term PrimitiveSentences.truthDB) :=
  weaken (deductAntisym h.conclTerm DerivedRules.truthTerm h truth)
    (Finset.union_subset (Finset.erase_subset _ _) (by simp)) h.hyp_isBool

end KernelProvable

end Mettapedia.Languages.OpenTheory

