import Mettapedia.Languages.Agda.Structural.Rules
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalCongruence

/-!
# Interpreting the six elimination-spine root declarations

These laws hold for arbitrary local valuations in arbitrary open contexts.
The source of each root rule determines all of that rule's parameters.
Type-valued maps relate actual polynomial constructor shapes to the
separately defined structural root family; neither map truncates evidence
to a proposition.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Structural.Authored

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.SemanticContextualMetavariables
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalPolynomial
open Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial (Judgment)

abbrev algebra := BindingCloneAlgebra.terms sig
abbrev Val (M : List (MetaArity sig)) (Γ : Ctx sig) := Valuation (M := M) algebra Γ

def emptyClose (Γ : Ctx sig) : Sub sig [] Γ := fun _ var => nomatch var

theorem close_unique {Γ : Ctx sig} (close : Sub sig [] Γ) : close = emptyClose Γ := by
  funext resultSort var
  nomatch var

def eval0 {M : List (MetaArity sig)} {Γ : Ctx sig} {resultSort : Srt}
    (values : Val M Γ) (term : STerm M [] resultSort) : Term sig Γ resultSort :=
  interpretSchema algebra values (fun _ var => .var var) (emptyClose Γ) term

def evalUnder {M : List (MetaArity sig)} {Γ : Ctx sig} {resultSort : Srt}
    (binders : Ctx sig) (values : Val M Γ) (term : STerm M (binders ++ []) resultSort) :
    Term sig (binders ++ Γ) resultSort :=
  interpretSchema algebra values (weakenEnvironment algebra binders (fun _ var => .var var))
    (algebra.substitution.liftEnvironment (emptyClose Γ) binders) term

@[simp] theorem eval0_lam {M Γ} (v : Val M Γ) (body : STerm M [.term] .term) :
    eval0 v (lamS body) = lam (evalUnder [.term] v body) := rfl
@[simp] theorem eval0_lamNoAbs {M Γ} (v : Val M Γ) (body : STerm M [] .term) :
    eval0 v (lamNoAbsS body) = lamNoAbs (eval0 v body) := rfl
@[simp] theorem eval0_eliminate {M Γ} (v : Val M Γ)
    (head : STerm M [] .term) (spine : STerm M [] .spine) :
    eval0 v (eliminateS head spine) = eliminate (eval0 v head) (eval0 v spine) := rfl
@[simp] theorem eval0_apply {M Γ} (v : Val M Γ) (argument : STerm M [] .term) :
    eval0 v (applyS argument) = apply (eval0 v argument) := rfl
@[simp] theorem eval0_nil {M Γ} (v : Val M Γ) : eval0 v nilS = nil := rfl
@[simp] theorem eval0_cons {M Γ} (v : Val M Γ)
    (head : STerm M [] .elim) (tail : STerm M [] .spine) :
    eval0 v (consS head tail) = cons (eval0 v head) (eval0 v tail) := rfl
@[simp] theorem eval0_append {M Γ} (v : Val M Γ)
    (first second : STerm M [] .spine) :
    eval0 v (appendS first second) = append (eval0 v first) (eval0 v second) := rfl

@[simp] theorem eval0_betaArgument {Γ} (v : Val betaMetas Γ) : eval0 v betaArgument = v 1 := bind_id _
@[simp] theorem eval0_betaRest {Γ} (v : Val betaMetas Γ) : eval0 v betaRest = v 2 := bind_id _
@[simp] theorem eval0_noAbsBody {Γ} (v : Val betaNoAbsMetas Γ) : eval0 v noAbsBody = v 0 := bind_id _
@[simp] theorem eval0_noAbsArgument {Γ} (v : Val betaNoAbsMetas Γ) : eval0 v noAbsArgument = v 1 := bind_id _
@[simp] theorem eval0_noAbsRest {Γ} (v : Val betaNoAbsMetas Γ) : eval0 v noAbsRest = v 2 := bind_id _
@[simp] theorem eval0_emptyHead {Γ} (v : Val emptyMetas Γ) : eval0 v emptyHead = v 0 := bind_id _
@[simp] theorem eval0_appendHead {Γ} (v : Val elimAppendMetas Γ) : eval0 v appendHead = v 0 := bind_id _
@[simp] theorem eval0_appendFirst {Γ} (v : Val elimAppendMetas Γ) : eval0 v appendFirst = v 1 := bind_id _
@[simp] theorem eval0_appendSecond {Γ} (v : Val elimAppendMetas Γ) : eval0 v appendSecond = v 2 := bind_id _
@[simp] theorem eval0_appendEmptyRest {Γ} (v : Val appendEmptyMetas Γ) : eval0 v appendEmptyRest = v 0 := bind_id _
@[simp] theorem eval0_appendConsHead {Γ} (v : Val appendConsMetas Γ) : eval0 v appendConsHead = v 0 := bind_id _
@[simp] theorem eval0_appendConsFirst {Γ} (v : Val appendConsMetas Γ) : eval0 v appendConsFirst = v 1 := bind_id _
@[simp] theorem eval0_appendConsSecond {Γ} (v : Val appendConsMetas Γ) : eval0 v appendConsSecond = v 2 := bind_id _

@[simp] theorem evalUnder_betaBody {Γ} (v : Val betaMetas Γ) :
    evalUnder [.term] v (betaBody (.var .zero)) = v 0 :=
  IntrinsicScopedLocalCongruence.interpret_slot v 0

@[simp] theorem eval0_betaBody {Γ} (v : Val betaMetas Γ) (argument : STerm betaMetas [] .term) :
    eval0 v (betaBody argument) = inst (v 0) (eval0 v argument) := by
  change bind _ (v 0) = bind (extend (eval0 v argument)) (v 0)
  congr 1
  funext resultSort var
  cases var <;> rfl

abbrev betaIndex : Fin roots.length := ⟨0, by decide⟩
abbrev noAbsIndex : Fin roots.length := ⟨1, by decide⟩
abbrev emptyIndex : Fin roots.length := ⟨2, by decide⟩
abbrev elimAppendIndex : Fin roots.length := ⟨3, by decide⟩
abbrev appendEmptyIndex : Fin roots.length := ⟨4, by decide⟩
abbrev appendConsIndex : Fin roots.length := ⟨5, by decide⟩

theorem root_context_empty (index : Fin roots.length) :
    (roots.get index).2.conclusion.ctx = [] := by
  rcases index with ⟨i, h⟩
  match i with
  | 0 | 1 | 2 | 3 | 4 | 5 => rfl
  | n + 6 => simp only [roots, List.length_cons, List.length_nil] at h; omega

def occurrence {Γ : Ctx sig} (index : Fin roots.length)
    (values : Val (roots.get index).1 Γ) : Instance roots algebra where
  index := index
  ambient := Γ
  valuation := values
  close := by rw [root_context_empty index]; exact emptyClose Γ

theorem occurrence_complete (event : Instance roots algebra) :
    event = occurrence event.index event.valuation := by
  rcases event with ⟨index, Γ, values, close⟩
  congr 1
  funext resultSort var
  have impossible : Var ([] : Ctx sig) resultSort := root_context_empty index ▸ var
  nomatch impossible

theorem beta_conclusion {Γ} (v : Val betaMetas Γ) :
    conclusionJudgment roots algebra (occurrence betaIndex v) =
      (⟨Γ, .term, eliminate (lam (v 0)) (cons (apply (v 1)) (v 2)),
        eliminate (inst (v 0) (v 1)) (v 2)⟩ : Judgment algebra) := by
  change (⟨Γ, .term, eval0 v beta.conclusion.lhs, eval0 v beta.conclusion.rhs⟩ : Judgment algebra) = _
  simp only [beta, rootRule, eval0_eliminate, eval0_lam,
    eval0_cons, eval0_apply, eval0_betaArgument, eval0_betaRest, eval0_betaBody]
  exact congrArg (fun body : Tm (.term :: Γ) =>
    (⟨Γ, .term, eliminate (lam body) (cons (apply (v 1)) (v 2)),
      eliminate (inst (v 0) (v 1)) (v 2)⟩ : Judgment algebra)) (evalUnder_betaBody v)

theorem noAbs_conclusion {Γ} (v : Val betaNoAbsMetas Γ) :
    conclusionJudgment roots algebra (occurrence noAbsIndex v) =
      (⟨Γ, .term, eliminate (lamNoAbs (v 0)) (cons (apply (v 1)) (v 2)),
        eliminate (v 0) (v 2)⟩ : Judgment algebra) := by
  change (⟨Γ, .term, eval0 v betaNoAbs.conclusion.lhs, eval0 v betaNoAbs.conclusion.rhs⟩ : Judgment algebra) = _
  simp only [betaNoAbs, rootRule, eval0_eliminate, eval0_lamNoAbs,
    eval0_cons, eval0_apply, eval0_noAbsBody, eval0_noAbsArgument, eval0_noAbsRest]

theorem empty_conclusion {Γ} (v : Val emptyMetas Γ) :
    conclusionJudgment roots algebra (occurrence emptyIndex v) =
      (⟨Γ, .term, eliminate (v 0) nil, v 0⟩ : Judgment algebra) := by
  change (⟨Γ, .term, eval0 v eliminateEmpty.conclusion.lhs, eval0 v eliminateEmpty.conclusion.rhs⟩ : Judgment algebra) = _
  simp only [eliminateEmpty, rootRule, eval0_eliminate, eval0_nil, eval0_emptyHead]

theorem elimAppend_conclusion {Γ} (v : Val elimAppendMetas Γ) :
    conclusionJudgment roots algebra (occurrence elimAppendIndex v) =
      (⟨Γ, .term, eliminate (eliminate (v 0) (v 1)) (v 2),
        eliminate (v 0) (append (v 1) (v 2))⟩ : Judgment algebra) := by
  change (⟨Γ, .term, eval0 v eliminateAppend.conclusion.lhs, eval0 v eliminateAppend.conclusion.rhs⟩ : Judgment algebra) = _
  simp only [eliminateAppend, rootRule, eval0_eliminate, eval0_append,
    eval0_appendHead, eval0_appendFirst, eval0_appendSecond]

theorem appendEmpty_conclusion {Γ} (v : Val appendEmptyMetas Γ) :
    conclusionJudgment roots algebra (occurrence appendEmptyIndex v) =
      (⟨Γ, .spine, append nil (v 0), v 0⟩ : Judgment algebra) := by
  change (⟨Γ, .spine, eval0 v appendEmpty.conclusion.lhs, eval0 v appendEmpty.conclusion.rhs⟩ : Judgment algebra) = _
  simp only [appendEmpty, rootRule, eval0_append, eval0_nil, eval0_appendEmptyRest]

theorem appendCons_conclusion {Γ} (v : Val appendConsMetas Γ) :
    conclusionJudgment roots algebra (occurrence appendConsIndex v) =
      (⟨Γ, .spine, append (cons (v 0) (v 1)) (v 2),
        cons (v 0) (append (v 1) (v 2))⟩ : Judgment algebra) := by
  change (⟨Γ, .spine, eval0 v appendCons.conclusion.lhs, eval0 v appendCons.conclusion.rhs⟩ : Judgment algebra) = _
  simp only [appendCons, rootRule, eval0_append, eval0_cons,
    eval0_appendConsHead, eval0_appendConsFirst, eval0_appendConsSecond]

def betaValues {Γ} (body : Tm (.term :: Γ)) (argument : Tm Γ) (rest : Spine Γ) : Val betaMetas Γ
  | ⟨0, _⟩ => body
  | ⟨1, _⟩ => argument
  | ⟨2, _⟩ => rest
def noAbsValues {Γ} (body argument : Tm Γ) (rest : Spine Γ) : Val betaNoAbsMetas Γ
  | ⟨0, _⟩ => body
  | ⟨1, _⟩ => argument
  | ⟨2, _⟩ => rest
def emptyValues {Γ} (head : Tm Γ) : Val emptyMetas Γ
  | ⟨0, _⟩ => head
def elimAppendValues {Γ} (head : Tm Γ) (first second : Spine Γ) : Val elimAppendMetas Γ
  | ⟨0, _⟩ => head
  | ⟨1, _⟩ => first
  | ⟨2, _⟩ => second
def appendEmptyValues {Γ} (rest : Spine Γ) : Val appendEmptyMetas Γ
  | ⟨0, _⟩ => rest
def appendConsValues {Γ} (head : Elim Γ) (first second : Spine Γ) : Val appendConsMetas Γ
  | ⟨0, _⟩ => head
  | ⟨1, _⟩ => first
  | ⟨2, _⟩ => second

theorem betaValues_recover {Γ} (v : Val betaMetas Γ) : betaValues (v 0) (v 1) (v 2) = v :=
  funext fun | ⟨0, _⟩ => rfl | ⟨1, _⟩ => rfl | ⟨2, _⟩ => rfl
theorem noAbsValues_recover {Γ} (v : Val betaNoAbsMetas Γ) : noAbsValues (v 0) (v 1) (v 2) = v :=
  funext fun | ⟨0, _⟩ => rfl | ⟨1, _⟩ => rfl | ⟨2, _⟩ => rfl
theorem emptyValues_recover {Γ} (v : Val emptyMetas Γ) : emptyValues (v 0) = v :=
  funext fun | ⟨0, _⟩ => rfl
theorem elimAppendValues_recover {Γ} (v : Val elimAppendMetas Γ) : elimAppendValues (v 0) (v 1) (v 2) = v :=
  funext fun | ⟨0, _⟩ => rfl | ⟨1, _⟩ => rfl | ⟨2, _⟩ => rfl
theorem appendEmptyValues_recover {Γ} (v : Val appendEmptyMetas Γ) : appendEmptyValues (v 0) = v :=
  funext fun | ⟨0, _⟩ => rfl
theorem appendConsValues_recover {Γ} (v : Val appendConsMetas Γ) : appendConsValues (v 0) (v 1) (v 2) = v :=
  funext fun | ⟨0, _⟩ => rfl | ⟨1, _⟩ => rfl | ⟨2, _⟩ => rfl

private theorem beta_source_injective {Γ : Ctx sig} :
    Function.Injective (fun data : Tm (.term :: Γ) × Tm Γ × Spine Γ => eliminate (lam data.1) (cons (apply data.2.1) data.2.2)) := by
  rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ same
  cases same
  rfl

/-- The actual source schema recovers every local beta parameter. -/
theorem beta_source_recovers {Γ} {v w : Val betaMetas Γ}
    (same : eval0 v beta.conclusion.lhs = eval0 w beta.conclusion.lhs) : v = w := by
  simp only [beta, rootRule, eval0_eliminate, eval0_lam, eval0_cons, eval0_apply, eval0_betaArgument, eval0_betaRest, evalUnder_betaBody v, evalUnder_betaBody w] at same
  have parameters := @beta_source_injective Γ
    (v 0, v 1, v 2) (w 0, w 1, w 2) same
  exact (betaValues_recover v).symm.trans
    ((congrArg (fun data : Tm (.term :: Γ) × Tm Γ × Spine Γ => betaValues data.1 data.2.1 data.2.2) parameters).trans
      (betaValues_recover w))

private theorem noAbs_source_injective {Γ : Ctx sig} :
    Function.Injective (fun data : Tm Γ × Tm Γ × Spine Γ => eliminate (lamNoAbs data.1) (cons (apply data.2.1) data.2.2)) := by
  rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ same
  cases same
  rfl

/-- The actual source schema recovers every local noAbs parameter. -/
theorem noAbs_source_recovers {Γ} {v w : Val betaNoAbsMetas Γ}
    (same : eval0 v betaNoAbs.conclusion.lhs = eval0 w betaNoAbs.conclusion.lhs) : v = w := by
  simp only [betaNoAbs, rootRule, eval0_eliminate, eval0_lamNoAbs, eval0_cons, eval0_apply, eval0_noAbsBody, eval0_noAbsArgument, eval0_noAbsRest] at same
  have parameters := @noAbs_source_injective Γ
    (v 0, v 1, v 2) (w 0, w 1, w 2) same
  exact (noAbsValues_recover v).symm.trans
    ((congrArg (fun data : Tm Γ × Tm Γ × Spine Γ => noAbsValues data.1 data.2.1 data.2.2) parameters).trans
      (noAbsValues_recover w))

private theorem empty_source_injective {Γ : Ctx sig} :
    Function.Injective (fun data : Tm Γ => eliminate data nil) := by
  intro a b same
  cases same
  rfl

/-- The actual source schema recovers every local empty parameter. -/
theorem empty_source_recovers {Γ} {v w : Val emptyMetas Γ}
    (same : eval0 v eliminateEmpty.conclusion.lhs = eval0 w eliminateEmpty.conclusion.lhs) : v = w := by
  simp only [eliminateEmpty, rootRule, eval0_eliminate, eval0_nil, eval0_emptyHead] at same
  have parameters := empty_source_injective same
  exact (emptyValues_recover v).symm.trans
    ((congrArg (fun data : Tm Γ => emptyValues data) parameters).trans
      (emptyValues_recover w))

private theorem elimAppend_source_injective {Γ : Ctx sig} :
    Function.Injective (fun data : Tm Γ × Spine Γ × Spine Γ => eliminate (eliminate data.1 data.2.1) data.2.2) := by
  rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ same
  cases same
  rfl

/-- The actual source schema recovers every local elimAppend parameter. -/
theorem elimAppend_source_recovers {Γ} {v w : Val elimAppendMetas Γ}
    (same : eval0 v eliminateAppend.conclusion.lhs = eval0 w eliminateAppend.conclusion.lhs) : v = w := by
  simp only [eliminateAppend, rootRule, eval0_eliminate, eval0_appendHead, eval0_appendFirst, eval0_appendSecond] at same
  have parameters := @elimAppend_source_injective Γ
    (v 0, v 1, v 2) (w 0, w 1, w 2) same
  exact (elimAppendValues_recover v).symm.trans
    ((congrArg (fun data : Tm Γ × Spine Γ × Spine Γ => elimAppendValues data.1 data.2.1 data.2.2) parameters).trans
      (elimAppendValues_recover w))

private theorem appendEmpty_source_injective {Γ : Ctx sig} :
    Function.Injective (fun data : Spine Γ => append nil data) := by
  intro a b same
  cases same
  rfl

/-- The actual source schema recovers every local appendEmpty parameter. -/
theorem appendEmpty_source_recovers {Γ} {v w : Val appendEmptyMetas Γ}
    (same : eval0 v appendEmpty.conclusion.lhs = eval0 w appendEmpty.conclusion.lhs) : v = w := by
  simp only [appendEmpty, rootRule, eval0_append, eval0_nil, eval0_appendEmptyRest] at same
  have parameters := appendEmpty_source_injective same
  exact (appendEmptyValues_recover v).symm.trans
    ((congrArg (fun data : Spine Γ => appendEmptyValues data) parameters).trans
      (appendEmptyValues_recover w))

private theorem appendCons_source_injective {Γ : Ctx sig} :
    Function.Injective (fun data : Elim Γ × Spine Γ × Spine Γ => append (cons data.1 data.2.1) data.2.2) := by
  rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ same
  cases same
  rfl

/-- The actual source schema recovers every local appendCons parameter. -/
theorem appendCons_source_recovers {Γ} {v w : Val appendConsMetas Γ}
    (same : eval0 v appendCons.conclusion.lhs = eval0 w appendCons.conclusion.lhs) : v = w := by
  simp only [appendCons, rootRule, eval0_append, eval0_cons, eval0_appendConsHead, eval0_appendConsFirst, eval0_appendConsSecond] at same
  have parameters := @appendCons_source_injective Γ
    (v 0, v 1, v 2) (w 0, w 1, w 2) same
  exact (appendConsValues_recover v).symm.trans
    ((congrArg (fun data : Elim Γ × Spine Γ × Spine Γ => appendConsValues data.1 data.2.1 data.2.2) parameters).trans
      (appendConsValues_recover w))

/-- For each fixed root label the entire local valuation is recoverable
from its interpreted source in the free binding algebra. -/
theorem root_source_recovers_valuation {Γ : Ctx sig} (index : Fin roots.length)
    (first second : Val (roots.get index).1 Γ)
    (same : (conclusionJudgment roots algebra (occurrence index first)).2.2.1 =
      (conclusionJudgment roots algebra (occurrence index second)).2.2.1) : first = second := by
  rcases index with ⟨i, bound⟩
  match i with
  | 0 => exact beta_source_recovers same
  | 1 => exact noAbs_source_recovers same
  | 2 => exact empty_source_recovers same
  | 3 => exact elimAppend_source_recovers same
  | 4 => exact appendEmpty_source_recovers same
  | 5 => exact appendCons_source_recovers same
  | n + 6 =>
      exfalso
      simp only [roots, List.length_cons, List.length_nil] at bound
      omega

/-- Structural root evidence at an exact scoped endpoint pair. -/
def RootAt (j : Judgment algebra) : Type := Root j.2.2.1 j.2.2.2

def rootFromValues {Γ : Ctx sig} : (index : Fin roots.length) →
    (values : Val (roots.get index).1 Γ) →
    RootAt (conclusionJudgment roots algebra (occurrence index values))
  | ⟨0, _⟩, values => Eq.mpr (congrArg RootAt (beta_conclusion values))
      (Root.beta (values (0 : Fin 3)) (values (1 : Fin 3)) (values (2 : Fin 3)))
  | ⟨1, _⟩, values => Eq.mpr (congrArg RootAt (noAbs_conclusion values))
      (Root.betaNoAbs (values (0 : Fin 3)) (values (1 : Fin 3)) (values (2 : Fin 3)))
  | ⟨2, _⟩, values => Eq.mpr (congrArg RootAt (empty_conclusion values))
      (Root.eliminateEmpty (values (0 : Fin 1)))
  | ⟨3, _⟩, values => Eq.mpr (congrArg RootAt (elimAppend_conclusion values))
      (Root.eliminateAppend (values (0 : Fin 3)) (values (1 : Fin 3)) (values (2 : Fin 3)))
  | ⟨4, _⟩, values => Eq.mpr (congrArg RootAt (appendEmpty_conclusion values))
      (Root.appendEmpty (values (0 : Fin 1)))
  | ⟨5, _⟩, values => Eq.mpr (congrArg RootAt (appendCons_conclusion values))
      (Root.appendCons (values (0 : Fin 3)) (values (1 : Fin 3)) (values (2 : Fin 3)))
  | ⟨n + 6, bound⟩, _ => by
      simp only [roots, List.length_cons, List.length_nil] at bound
      omega

def rootOfOccurrence (event : Instance roots algebra) :
    RootAt (conclusionJudgment roots algebra event) :=
  (congrArg (conclusionJudgment roots algebra) (occurrence_complete event)).symm ▸
    rootFromValues event.index event.valuation

def rootOfShape {j : Judgment algebra} (shape : Shape roots algebra j) : RootAt j :=
  shape.2 ▸ rootOfOccurrence shape.1

/-- Every structural root constructor has its authored label and its exact
local valuation as a polynomial constructor shape. -/
def shapeOfRoot {Γ : Ctx sig} {resultSort : Srt} {source target : Term sig Γ resultSort} :
    Root source target → Shape roots algebra ⟨Γ, resultSort, source, target⟩
  | .beta body argument rest =>
      ⟨occurrence betaIndex (betaValues body argument rest), beta_conclusion _⟩
  | .betaNoAbs body argument rest =>
      ⟨occurrence noAbsIndex (noAbsValues body argument rest), noAbs_conclusion _⟩
  | .eliminateEmpty head => ⟨occurrence emptyIndex (emptyValues head), empty_conclusion _⟩
  | .eliminateAppend head first second =>
      ⟨occurrence elimAppendIndex (elimAppendValues head first second), elimAppend_conclusion _⟩
  | .appendEmpty rest => ⟨occurrence appendEmptyIndex (appendEmptyValues rest), appendEmpty_conclusion _⟩
  | .appendCons head first second =>
      ⟨occurrence appendConsIndex (appendConsValues head first second), appendCons_conclusion _⟩

private theorem mpr_heq {α β : Type} (same : α = β) (value : β) :
    HEq (same.mpr value) value := by
  cases same
  rfl

theorem rootOfShape_shapeOfRoot {Γ : Ctx sig} {resultSort : Srt}
    {source target : Term sig Γ resultSort} (root : Root source target) :
    rootOfShape (shapeOfRoot root) = root := by
  cases root <;> simp only [shapeOfRoot, rootOfShape, rootOfOccurrence, rootFromValues, occurrence]
  all_goals
    apply eq_of_heq
    exact (eqRec_heq _ _).trans (mpr_heq _ _)

#print axioms beta_conclusion
#print axioms occurrence_complete
#print axioms betaValues_recover
#print axioms root_source_recovers_valuation
#print axioms rootOfOccurrence
#print axioms shapeOfRoot
#print axioms rootOfShape_shapeOfRoot

end Mettapedia.Languages.Agda.Structural.Authored
