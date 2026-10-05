import Mettapedia.Languages.MeTTa.PrimeCandidates.Trinity.Triangle
import Mettapedia.Languages.MeTTa.PrimeCandidates.Trinity.Reverse.Program
import Mettapedia.Languages.MeTTa.PrimeCandidates.Trinity.Append.Extensional
import Mettapedia.GSLT.Core.NonFactorization
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Algorithmic.NeutralHeads
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.DeclarationRewriting
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectConfluence

/-!
# Two reversals of a list as sets, and the three faces joined

`Program.lean` runs the two reversals and types them. This module reads them as sets and
joins the three faces.

**The sets, on their own.** On the set of lists of `Append.Extensional`, the plain reversal
(`setRev`) and the reversal onto an accumulator (`setRevOnto`) are defined by the recursion of
the set of lists (`ZFSetInductive.recFun`), each by its two equations of the source
(`setRev_nil`, `setRev_cons`, `setRevOnto_nil`, `setRevOnto_cons`). Nothing of the type
theory or of running is used. By induction on the set of lists, an accumulator holds what the
plain reversal appends (`setRevOnto_eq_setAppend`, through the associativity of the append on
sets, `Append.setAppend_assoc`), so **the two are one function** (`setRev_eq_setRevOnto`): their
traced graphs over the set of lists are one set (`setRev_graph_eq`).

**What is typed means these sets** (`toTerm_value`). In the set model of the program
(relative to `CofinalInaccessibles`) the value of the term of an expression is the set of the
expression; `rev` and `rev-onto` mean `setRev` and `setRevOnto` at every list because the
model satisfies their typed equations (`model_rev`, `model_revOnto`) and on sets those have
exactly one solution (`setRev_unique`, `setRevOnto_unique`). The two functions
`λ l. rev l` and `λ l. rev-onto nil l` have one value in the model, the traced graph of the
reversal (`model_revFn_eq_revOntoNilFn`).

**The three faces joined.** The triangle of the program (`reversalTriangle`) maps what runs
to its typed term, the typed term to its set in the model, and what runs directly to the set
of the value it reaches; it commutes by proof (`meaning_typing`). The two programs `rev l`
and `rev-onto nil l` reach one set on every face (`bothReversals_one_set`). **The cost is not
a function of the set** (`cost_not_from_set`): for every list of at least one element the two
programs reach one set with different numbers of steps (`cost_differs_at_every_length`). The
triangle is not exact (`reversalTriangle_loses`).

**Which face sees which difference.** Running sees the cost: `(n + 1)(n + 2) / 2` steps
against `n + 1`. Sets see one graph. The judgment equates the two at every closed list
(`rev_typedEqual_revOnto`, `revFn_app_typedEqual`). Whether it equates them at an unknown list
is not decided here. The question for the two functions is the same question: by η for
functions, `λ l. rev l` and `λ l. rev-onto nil l` are equal exactly when `rev l` and
`rev-onto nil l` are equal at the variable of a context `l : list` (`revFn_typedEqual_iff`).
The set model cannot decide it, since it gives the two one value.

**What running shows at an unknown list, and why it is not enough.** Every root step of the
program starts at a spine of a constant that computes (`rulesWith_rootStep_shape`, for every
list of declarations). At the variable, `rev l` takes no step, and `rev-onto nil l` unfolds to
`rev-onto~scrutinee-first l nil`, which takes no step; the two are different terms with different
heads (`reversals_normal_forms_differ`). The rewriting of the program is Church–Rosser
(`reversalRules_churchRosser`, by the theorem for admissible lists of declarations over the
object package, whose equations speak only of declared names: `objectNamesDeclared`), so the
two reversals at an unknown list are not convertible (`reversals_not_convertible`). That does
not separate them in the judgment, which has η: `rev` and `λ l. rev l` are different terms that
take no step (`rev_takes_no_step`, `revFn_takes_no_step`), and they are equal
(`rev_typedEqual_revFn`). So two different normal forms of a Church–Rosser rewriting can be one
term of the judgment. What separates terms in a judgment with η is the comparison
of the conversion algorithm: two stuck terms with different heads are equal at no type where
the algorithm is complete (`Normalization.not_equal_of_neutral_heads`). The heads here are
`rev` and `rev-onto~scrutinee-first`. Completeness of the conversion algorithm is proved for the
object package, and not for the object package with a list of declarations; that is what
deciding the question needs. Positive control: a pair the rewriting relates,
`rev-onto nil (cons a l)` and `rev-onto (cons a nil) l` at variables, is equal in the judgment
(`revOnto_cons_typedEqual`).

Positive examples: the list of zero, one and two reversed is the list of two, one and zero as
sets (`setRev_zeroOneTwo`), and a palindrome is its own reversal (`setRev_palindrome`).
Negative example: the wrong equation that appends at the front,
`rev' (cons a as) = append (cons a nil) (rev' as)`, defines the identity on lists
(`setWrongRev_eq_self`), a different set from the reversal (`setWrongRev_ne_setRev`), and the
typed term of `rev` does not mean it (`wrongRev_not_meaning`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.Trinity.Reverse

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
open Presentation Presentation.TypedEquality Presentation.TypedEquality.Annotated
open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
open CodeModel
open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseClosure (CofinalInaccessibles)
open ZFSetInductive (Fits recFun nameCode recFun_constructor numeral_zero_ne_one)
open ZFSetDependentProducts (graph graph_congr)
open ZFSetTraceProducts (traceLam traceApp traceApp_graph_beta)
open Mettapedia.Languages.MeTTa.PrimeCandidates.Trinity.Append
  (NumExpr listSignature listSignature_distinct listSet nilSet consSet nilSet_mem consSet_mem
    list_induct setAppend setAppend_nil setAppend_cons setAppend_mem setAppend_nil_right
    setAppend_assoc consSet_ne_of_head_ne program_num program_zero program_suc program_list program_nil
    program_cons model_append)
open Mettapedia.Computability.ComputationalTrinity
open Mettapedia.GSLT.Core.NonFactorization

universe u

/-! ## The plain reversal on sets -/

/-- **What the recursion of the plain reversal does at a constructor**: the empty list at the
empty list; at a number `a` before a list whose reversal is `r`, the append of `r` and the
one-element list of `a`. -/
noncomputable def revCase (i : Nat) (args recs : List ZFSet.{u}) : ZFSet.{u} :=
  if i = 0 then nilSet
  else
    match args, recs with
    | a :: _, r :: _ => setAppend r (consSet a nilSet)
    | _, _ => ∅

/-- **The plain reversal on sets**, by the recursion of the set of lists. -/
noncomputable def setRev : ZFSet.{u} → ZFSet.{u} := recFun (sig := listSignature) revCase

/-- The first equation of `rev`, between sets. -/
theorem setRev_nil : setRev nilSet.{u} = nilSet :=
  recFun_constructor (sig := listSignature) listSignature_distinct revCase (i := 0)
    (c := ⟨nameCode nilN, []⟩) (args := []) rfl Fits.nil

/-- The second equation of `rev`, between sets. -/
theorem setRev_cons {a l : ZFSet.{u}} (ha : a ∈ ZFSet.omega) (hl : l ∈ listSet) :
    setRev (consSet a l) = setAppend (setRev l) (consSet a nilSet) :=
  recFun_constructor (sig := listSignature) listSignature_distinct revCase (i := 1)
    (c := ⟨nameCode consN,
      [ZFSetInductive.Field.ofSet ZFSet.omega, ZFSetInductive.Field.recursive]⟩)
    (args := [a, l]) rfl (Fits.ofSet ha (Fits.recursive hl Fits.nil))

/-- The reversal of a list is a list. -/
theorem setRev_mem : ∀ l, l ∈ listSet.{u} → setRev l ∈ listSet.{u} :=
  list_induct (P := fun l => setRev l ∈ listSet) (by rw [setRev_nil]; exact nilSet_mem)
    (fun a l ha hl ih => by
      rw [setRev_cons ha hl]
      exact setAppend_mem _ ih _ (consSet_mem ha nilSet_mem))

/-- **The plain reversal is the only function on lists with its two equations.** -/
theorem setRev_unique (g : ZFSet.{u} → ZFSet.{u}) (nil : g nilSet = nilSet)
    (cons : ∀ a l, a ∈ ZFSet.omega → l ∈ listSet → g (consSet a l) = setAppend (g l) (consSet a nilSet)) :
    ∀ l, l ∈ listSet → g l = setRev l :=
  list_induct (P := fun l => g l = setRev l) (by rw [nil, setRev_nil])
    (fun a l ha hl ih => by rw [cons a l ha hl, setRev_cons ha hl, ih])

/-! ## The reversal onto an accumulator on sets -/

/-- **What the recursion of the accumulator reversal does at a constructor**: every list gives
a function of the accumulator, coded as a traced graph over the set of lists; the identity at
the empty list, and at a number `a` before a list whose function is `r`, the function that
applies `r` to `a` before the accumulator. -/
noncomputable def revOntoCase (i : Nat) (args recs : List ZFSet.{u}) : ZFSet.{u} :=
  if i = 0 then traceLam (graph listSet fun acc => acc)
  else
    match args, recs with
    | a :: _, r :: _ => traceLam (graph listSet fun acc => traceApp r (consSet a acc))
    | _, _ => ∅

/-- The function of a list, by the recursion of the set of lists. -/
noncomputable def revOntoFun : ZFSet.{u} → ZFSet.{u} := recFun (sig := listSignature) revOntoCase

/-- **The accumulator reversal on sets**: the function of the list, at the accumulator. -/
noncomputable def setRevOnto (acc l : ZFSet.{u}) : ZFSet.{u} := traceApp (revOntoFun l) acc

theorem revOntoFun_nil : revOntoFun nilSet.{u} = traceLam (graph listSet fun acc => acc) :=
  recFun_constructor (sig := listSignature) listSignature_distinct revOntoCase (i := 0)
    (c := ⟨nameCode nilN, []⟩) (args := []) rfl Fits.nil

theorem revOntoFun_cons {a l : ZFSet.{u}} (ha : a ∈ ZFSet.omega) (hl : l ∈ listSet) :
    revOntoFun (consSet a l) =
      traceLam (graph listSet fun acc => traceApp (revOntoFun l) (consSet a acc)) :=
  recFun_constructor (sig := listSignature) listSignature_distinct revOntoCase (i := 1)
    (c := ⟨nameCode consN,
      [ZFSetInductive.Field.ofSet ZFSet.omega, ZFSetInductive.Field.recursive]⟩)
    (args := [a, l]) rfl (Fits.ofSet ha (Fits.recursive hl Fits.nil))

/-- The first equation of `rev-onto`, between sets. -/
theorem setRevOnto_nil {acc : ZFSet.{u}} (hacc : acc ∈ listSet) : setRevOnto acc nilSet = acc := by
  rw [setRevOnto, revOntoFun_nil, traceApp_graph_beta _ hacc]

/-- The second equation of `rev-onto`, between sets. -/
theorem setRevOnto_cons {acc a l : ZFSet.{u}} (hacc : acc ∈ listSet) (ha : a ∈ ZFSet.omega)
    (hl : l ∈ listSet) : setRevOnto acc (consSet a l) = setRevOnto (consSet a acc) l := by
  rw [setRevOnto, revOntoFun_cons ha hl, traceApp_graph_beta _ hacc]
  rfl

/-- A list reversed onto a list is a list. -/
theorem setRevOnto_mem : ∀ l, l ∈ listSet.{u} → ∀ acc, acc ∈ listSet.{u} →
    setRevOnto acc l ∈ listSet.{u} :=
  list_induct (P := fun l => ∀ acc, acc ∈ listSet → setRevOnto acc l ∈ listSet)
    (fun acc hacc => by rw [setRevOnto_nil hacc]; exact hacc)
    (fun a l ha hl ih acc hacc => by
      rw [setRevOnto_cons hacc ha hl]
      exact ih _ (consSet_mem ha hacc))

/-- **The accumulator reversal is the only function on lists with its two equations.** -/
theorem setRevOnto_unique (g : ZFSet.{u} → ZFSet.{u} → ZFSet.{u})
    (nil : ∀ acc, acc ∈ listSet → g acc nilSet = acc)
    (cons : ∀ acc a l, acc ∈ listSet → a ∈ ZFSet.omega → l ∈ listSet →
      g acc (consSet a l) = g (consSet a acc) l) :
    ∀ l, l ∈ listSet → ∀ acc, acc ∈ listSet → g acc l = setRevOnto acc l :=
  list_induct (P := fun l => ∀ acc, acc ∈ listSet → g acc l = setRevOnto acc l)
    (fun acc hacc => by rw [nil acc hacc, setRevOnto_nil hacc])
    (fun a l ha hl ih acc hacc => by
      rw [cons acc a l hacc ha hl, setRevOnto_cons hacc ha hl, ih _ (consSet_mem ha hacc)])

/-! ## The two are one function -/

/-- **The accumulator holds what the plain reversal appends**, between sets. -/
theorem setRevOnto_eq_setAppend : ∀ l, l ∈ listSet.{u} → ∀ acc, acc ∈ listSet.{u} →
    setRevOnto acc l = setAppend (setRev l) acc :=
  list_induct (P := fun l => ∀ acc, acc ∈ listSet → setRevOnto acc l = setAppend (setRev l) acc)
    (fun acc hacc => by rw [setRevOnto_nil hacc, setRev_nil, setAppend_nil hacc])
    (fun a l ha hl ih acc hacc => by
      have one : consSet a nilSet ∈ listSet.{u} := consSet_mem ha nilSet_mem
      rw [setRevOnto_cons hacc ha hl, ih _ (consSet_mem ha hacc), setRev_cons ha hl,
        setAppend_assoc _ (setRev_mem l hl) _ one _ hacc, setAppend_cons ha nilSet_mem hacc,
        setAppend_nil hacc])

/-- **The two reversals are one function on lists.** -/
theorem setRev_eq_setRevOnto {l : ZFSet.{u}} (hl : l ∈ listSet) : setRev l = setRevOnto nilSet l := by
  rw [setRevOnto_eq_setAppend l hl _ nilSet_mem, setAppend_nil_right _ (setRev_mem l hl)]

/-- **One traced graph**: the two reversals have one graph over the set of lists. -/
theorem setRev_graph_eq :
    traceLam (graph listSet.{u} setRev) = traceLam (graph listSet.{u} (setRevOnto nilSet)) :=
  congrArg traceLam (graph_congr fun _ hl => setRev_eq_setRevOnto hl)

/-! ## Examples on sets -/

/-- Positive example: **the list of zero, one and two, reversed, is the list of two, one and
zero**, as sets. -/
theorem setRev_zeroOneTwo :
    setRev (consSet (NumExpr.toSet .zero) (consSet (NumExpr.toSet oneN)
        (consSet (NumExpr.toSet twoN) nilSet))) =
      consSet (NumExpr.toSet twoN) (consSet (NumExpr.toSet oneN)
        (consSet (NumExpr.toSet .zero) nilSet.{u})) := by
  have h0 := NumExpr.toSet_mem.{u} .zero
  have h1 := NumExpr.toSet_mem.{u} oneN
  have h2 := NumExpr.toSet_mem.{u} twoN
  have l2 : consSet (NumExpr.toSet twoN) nilSet.{u} ∈ listSet := consSet_mem h2 nilSet_mem
  have l12 := consSet_mem h1 l2
  rw [setRev_cons h0 l12, setRev_cons h1 l2, setRev_cons h2 nilSet_mem, setRev_nil,
    setAppend_nil (consSet_mem h2 nilSet_mem), setAppend_cons h2 nilSet_mem (consSet_mem h1 nilSet_mem),
    setAppend_nil (consSet_mem h1 nilSet_mem),
    setAppend_cons h2 (consSet_mem h1 nilSet_mem) (consSet_mem h0 nilSet_mem),
    setAppend_cons h1 nilSet_mem (consSet_mem h0 nilSet_mem), setAppend_nil (consSet_mem h0 nilSet_mem)]

/-- Positive example: **a palindrome is its own reversal**, as sets. -/
theorem setRev_palindrome :
    setRev (consSet (NumExpr.toSet .zero) (consSet (NumExpr.toSet oneN)
        (consSet (NumExpr.toSet .zero) nilSet))) =
      consSet (NumExpr.toSet .zero) (consSet (NumExpr.toSet oneN)
        (consSet (NumExpr.toSet .zero) nilSet.{u})) := by
  have h0 := NumExpr.toSet_mem.{u} .zero
  have h1 := NumExpr.toSet_mem.{u} oneN
  have l0 : consSet (NumExpr.toSet .zero) nilSet.{u} ∈ listSet := consSet_mem h0 nilSet_mem
  have l10 := consSet_mem h1 l0
  rw [setRev_cons h0 l10, setRev_cons h1 l0, setRev_cons h0 nilSet_mem, setRev_nil,
    setAppend_nil l0, setAppend_cons h0 nilSet_mem (consSet_mem h1 nilSet_mem),
    setAppend_nil (consSet_mem h1 nilSet_mem), setAppend_cons h0 (consSet_mem h1 nilSet_mem) l0,
    setAppend_cons h1 nilSet_mem l0, setAppend_nil l0]

/-- What the recursion of a **wrong** reversal does: at a number before a list, the
one-element list of the number before the result, `rev' (cons a as) = append (cons a nil)
(rev' as)`. -/
noncomputable def wrongRevCase (i : Nat) (args recs : List ZFSet.{u}) : ZFSet.{u} :=
  if i = 0 then nilSet
  else
    match args, recs with
    | a :: _, r :: _ => setAppend (consSet a nilSet) r
    | _, _ => ∅

/-- The wrong reversal on sets. -/
noncomputable def setWrongRev : ZFSet.{u} → ZFSet.{u} := recFun (sig := listSignature) wrongRevCase

/-- Negative example: **the wrong equation defines the identity on lists.** -/
theorem setWrongRev_eq_self : ∀ l, l ∈ listSet.{u} → setWrongRev l = l :=
  list_induct (P := fun l => setWrongRev l = l)
    (recFun_constructor (sig := listSignature) listSignature_distinct wrongRevCase (i := 0)
      (c := ⟨nameCode nilN, []⟩) (args := []) rfl Fits.nil)
    (fun a l ha hl ih => by
      have step : setWrongRev (consSet a l) = setAppend (consSet a nilSet) (setWrongRev l) :=
        recFun_constructor (sig := listSignature) listSignature_distinct wrongRevCase (i := 1)
          (c := ⟨nameCode consN,
            [ZFSetInductive.Field.ofSet ZFSet.omega, ZFSetInductive.Field.recursive]⟩)
          (args := [a, l]) rfl (Fits.ofSet ha (Fits.recursive hl Fits.nil))
      rw [step, ih, setAppend_cons ha nilSet_mem hl, setAppend_nil hl])

/-- The list of zero and one, as a set. -/
noncomputable abbrev zeroOneSet : ZFSet.{u} :=
  consSet (NumExpr.toSet .zero) (consSet (NumExpr.toSet oneN) nilSet)

theorem zeroOneSet_mem : zeroOneSet.{u} ∈ listSet :=
  consSet_mem (NumExpr.toSet_mem .zero) (consSet_mem (NumExpr.toSet_mem oneN) nilSet_mem)

theorem setRev_zeroOne :
    setRev zeroOneSet.{u} = consSet (NumExpr.toSet oneN) (consSet (NumExpr.toSet .zero) nilSet) := by
  have h0 := NumExpr.toSet_mem.{u} .zero
  have h1 := NumExpr.toSet_mem.{u} oneN
  rw [setRev_cons h0 (consSet_mem h1 nilSet_mem), setRev_cons h1 nilSet_mem, setRev_nil,
    setAppend_nil (consSet_mem h1 nilSet_mem), setAppend_cons h1 nilSet_mem (consSet_mem h0 nilSet_mem),
    setAppend_nil (consSet_mem h0 nilSet_mem)]

/-- Negative example: **the wrong reversal is a different set from the reversal**: they differ
at the list of zero and one. -/
theorem setWrongRev_ne_setRev : setWrongRev zeroOneSet.{u} ≠ setRev zeroOneSet := by
  rw [setWrongRev_eq_self _ zeroOneSet_mem, setRev_zeroOne]
  exact consSet_ne_of_head_ne numeral_zero_ne_one

/-! ## The source, read as sets -/

/-- **The set of a list expression**: the constructors, the append on sets, and the two
reversals on sets. -/
noncomputable def RevExpr.toSet : RevExpr → ZFSet.{u}
  | .nil => nilSet
  | .cons head tail => consSet head.toSet tail.toSet
  | .append left right => setAppend left.toSet right.toSet
  | .rev list => setRev list.toSet
  | .revOnto acc list => setRevOnto acc.toSet list.toSet

/-- Every list expression is read as a list. -/
theorem RevExpr.toSet_mem : ∀ e : RevExpr, (e.toSet : ZFSet.{u}) ∈ listSet
  | .nil => nilSet_mem
  | .cons head tail => consSet_mem head.toSet_mem tail.toSet_mem
  | .append left right => setAppend_mem _ left.toSet_mem _ right.toSet_mem
  | .rev list => setRev_mem _ list.toSet_mem
  | .revOnto acc list => setRevOnto_mem _ list.toSet_mem _ acc.toSet_mem

/-- **The six equations hold between sets**: a step of the source does not change the set. -/
theorem RevExpr.Step.toSet_eq {e e' : RevExpr} (step : RevExpr.Step e e') :
    (e.toSet : ZFSet.{u}) = e'.toSet := by
  induction step with
  | appendNil right => exact setAppend_nil right.toSet_mem
  | appendCons head tail right =>
      exact setAppend_cons head.toSet_mem tail.toSet_mem right.toSet_mem
  | revNil => exact setRev_nil
  | revCons head tail => exact setRev_cons head.toSet_mem tail.toSet_mem
  | revOntoNil acc => exact setRevOnto_nil acc.toSet_mem
  | revOntoCons acc head tail =>
      exact setRevOnto_cons acc.toSet_mem head.toSet_mem tail.toSet_mem
  | consTail _ ih =>
      show consSet _ _ = consSet _ _
      rw [ih]
  | appendLeft _ ih =>
      show setAppend _ _ = setAppend _ _
      rw [ih]
  | appendRight _ ih =>
      show setAppend _ _ = setAppend _ _
      rw [ih]
  | revArg _ ih =>
      show setRev _ = setRev _
      rw [ih]
  | revOntoAcc _ ih =>
      show setRevOnto _ _ = setRevOnto _ _
      rw [ih]
  | revOntoList _ ih =>
      show setRevOnto _ _ = setRevOnto _ _
      rw [ih]

/-- A sequence of steps does not change the set. -/
theorem RevExpr.toSet_eq_of_steps {e e' : RevExpr}
    (steps : Relation.ReflTransGen RevExpr.Step e e') : (e.toSet : ZFSet.{u}) = e'.toSet := by
  induction steps with
  | refl => rfl
  | tail _ step ih => exact ih.trans step.toSet_eq

/-- The two reversals of every closed list are one set. -/
theorem rev_toSet_eq_revOnto (l : RevExpr) :
    ((RevExpr.rev l).toSet : ZFSet.{u}) = (RevExpr.revOnto .nil l).toSet :=
  setRev_eq_setRevOnto l.toSet_mem

/-! ## What is typed means these sets -/

section Model

variable (h : CofinalInaccessibles.{u})

/-- The assignment of the model of the program. -/
local notation "C" => objectDeclarationsConsts h reversalProgram

/-- The names of the program of the lists, the append and `append-nil` keep their values in
the model of the program. -/
theorem keep {c : DeclName} (declared : objectProgram.constantType c ≠ none) :
    C c = objectDeclarationsConsts h listProgram c :=
  declarationsConsts_after [.definition (.explicit revIsRevOntoDef),
    .definition (.recursive revOntoAppendDef),
    .definition (.explicit revOntoDef), .definition (.recursive revOntoFirstDef),
    .definition (.recursive revDef), .definition (.recursive appendAssocDef)]
    reversalProgram_admissible declared

theorem my_num : C numN = ZFSet.omega := (keep h (by decide)).trans (program_num h)

theorem my_list : C listN = listSet := (keep h (by decide)).trans (program_list h)

theorem my_nil : C nilN = nilSet := (keep h (by decide)).trans (program_nil h)

theorem my_cons {a l : ZFSet.{u}} (ha : a ∈ ZFSet.omega) (hl : l ∈ listSet) :
    traceApp (traceApp (C consN) a) l = consSet a l := by
  rw [keep h (by decide)]
  exact program_cons h ha hl

theorem my_append {l ys : ZFSet.{u}} (hl : l ∈ listSet) (hys : ys ∈ listSet) :
    traceApp (traceApp (C appendN) l) ys = setAppend l ys := by
  rw [keep h (by decide)]
  exact model_append h hl hys

/-- The term of a numeral means its set. -/
theorem my_num_value : ∀ n : NumExpr, ev (objHeads h) C n.toTerm Fin.elim0 = n.toSet
  | .zero => (keep h (by decide)).trans (program_zero h)
  | .suc n => by
      show traceApp (C sucN) (ev (objHeads h) C n.toTerm Fin.elim0) = insert n.toSet n.toSet
      rw [my_num_value n, keep h (by decide), program_suc h, suc_apply h n.toSet_mem]

theorem sound {s : CStatement Tower.Head} (derivation : CDerivable objectReversal s) :
    Holds (objHeads h) C s :=
  objectDeclarations_sound h reversalProgram_admissible derivation

/-- **The first typed equation of `rev` holds in the model.** -/
theorem model_rev_nil : traceApp (C revN) nilSet = nilSet := by
  have equal : traceApp (C revN) (C nilN) = C nilN :=
    (sound h (rev_nil_in (Γ := .nil) extReversal.ontoRev) Fin.elim0 (sat_nil _ _ _)).1
  rwa [my_nil h] at equal

/-- **The second typed equation of `rev` holds in the model at every number and list.** -/
theorem model_rev_cons {a l : ZFSet.{u}} (ha : a ∈ ZFSet.omega) (hl : l ∈ listSet) :
    traceApp (C revN) (consSet a l) = setAppend (traceApp (C revN) l) (consSet a nilSet) := by
  let Γ : CCtx Tower.Head 2 := .snoc (.snoc .nil cnum) clist
  have equation := sound h (rev_cons_in (Γ := Γ) extReversal.ontoRev (.var 1) (.var 0))
  have typing := sound h (crev_in (Γ := Γ) extReversal.ontoRev (.var 0))
  let ρ : Env.{u} 2 := extend (extend Fin.elim0 a) l
  have sat : Sat (objHeads h) C Γ ρ := by
    refine (sat_snoc _ _).mpr ⟨(sat_snoc _ _).mpr ⟨sat_nil _ _ _, ?_⟩, ?_⟩
    · show a ∈ C numN
      rw [my_num h]
      exact ha
    · show l ∈ C listN
      rw [my_list h]
      exact hl
  have equal : traceApp (C revN) (traceApp (traceApp (C consN) a) l) =
      traceApp (traceApp (C appendN) (traceApp (C revN) l))
        (traceApp (traceApp (C consN) a) (C nilN)) := (equation ρ sat).1
  have member : traceApp (C revN) l ∈ listSet := by
    have inList : traceApp (C revN) l ∈ C listN := typing ρ sat
    rwa [my_list h] at inList
  rw [my_nil h, my_cons h ha hl, my_cons h ha nilSet_mem,
    my_append h member (consSet_mem ha nilSet_mem)] at equal
  exact equal

/-- **The model's `rev` is the reversal on sets** at every list. -/
theorem model_rev {l : ZFSet.{u}} (hl : l ∈ listSet) : traceApp (C revN) l = setRev l :=
  setRev_unique (fun l => traceApp (C revN) l) (model_rev_nil h)
    (fun _ _ ha hl => model_rev_cons h ha hl) l hl

/-- **The first typed equation of `rev-onto` holds in the model at every accumulator.** -/
theorem model_revOnto_nil {acc : ZFSet.{u}} (hacc : acc ∈ listSet) :
    traceApp (traceApp (C revOntoN) acc) nilSet = acc := by
  let Γ : CCtx Tower.Head 1 := .snoc .nil clist
  have equation := sound h (revOnto_nil_in (Γ := Γ) extReversal (.var 0))
  let ρ : Env.{u} 1 := extend Fin.elim0 acc
  have sat : Sat (objHeads h) C Γ ρ := by
    refine (sat_snoc _ _).mpr ⟨sat_nil _ _ _, ?_⟩
    show acc ∈ C listN
    rw [my_list h]
    exact hacc
  have equal : traceApp (traceApp (C revOntoN) acc) (C nilN) = acc := (equation ρ sat).1
  rwa [my_nil h] at equal

/-- **The second typed equation of `rev-onto` holds in the model** at every accumulator,
number and list. -/
theorem model_revOnto_cons {acc a l : ZFSet.{u}} (hacc : acc ∈ listSet) (ha : a ∈ ZFSet.omega)
    (hl : l ∈ listSet) :
    traceApp (traceApp (C revOntoN) acc) (consSet a l) =
      traceApp (traceApp (C revOntoN) (consSet a acc)) l := by
  let Γ : CCtx Tower.Head 3 := .snoc (.snoc (.snoc .nil clist) cnum) clist
  have equation := sound h (revOnto_cons_in (Γ := Γ) extReversal (.var 2) (.var 1) (.var 0))
  let ρ : Env.{u} 3 := extend (extend (extend Fin.elim0 acc) a) l
  have sat : Sat (objHeads h) C Γ ρ := by
    refine (sat_snoc _ _).mpr ⟨(sat_snoc _ _).mpr ⟨(sat_snoc _ _).mpr ⟨sat_nil _ _ _, ?_⟩, ?_⟩, ?_⟩
    · show acc ∈ C listN
      rw [my_list h]
      exact hacc
    · show a ∈ C numN
      rw [my_num h]
      exact ha
    · show l ∈ C listN
      rw [my_list h]
      exact hl
  have equal : traceApp (traceApp (C revOntoN) acc) (traceApp (traceApp (C consN) a) l) =
      traceApp (traceApp (C revOntoN) (traceApp (traceApp (C consN) a) acc)) l :=
    (equation ρ sat).1
  rwa [my_cons h ha hl, my_cons h ha hacc] at equal

/-- **The model's `rev-onto` is the accumulator reversal on sets** at every two lists. -/
theorem model_revOnto {acc l : ZFSet.{u}} (hacc : acc ∈ listSet) (hl : l ∈ listSet) :
    traceApp (traceApp (C revOntoN) acc) l = setRevOnto acc l :=
  setRevOnto_unique (fun acc l => traceApp (traceApp (C revOntoN) acc) l)
    (fun _ hacc => model_revOnto_nil h hacc)
    (fun _ _ _ hacc ha hl => model_revOnto_cons h hacc ha hl) l hl acc hacc

/-- **What is typed means these sets**: in the set model of the program, the value of the
term of a list expression is the set of the expression. -/
theorem toTerm_value : ∀ e : RevExpr, ev (objHeads h) C e.toTerm Fin.elim0 = e.toSet
  | .nil => my_nil h
  | .cons head tail => by
      show traceApp (traceApp (C consN) (ev (objHeads h) C head.toTerm Fin.elim0))
          (ev (objHeads h) C tail.toTerm Fin.elim0) = consSet head.toSet tail.toSet
      rw [my_num_value h head, toTerm_value tail]
      exact my_cons h head.toSet_mem tail.toSet_mem
  | .append left right => by
      show traceApp (traceApp (C appendN) (ev (objHeads h) C left.toTerm Fin.elim0))
          (ev (objHeads h) C right.toTerm Fin.elim0) = setAppend left.toSet right.toSet
      rw [toTerm_value left, toTerm_value right]
      exact my_append h left.toSet_mem right.toSet_mem
  | .rev list => by
      show traceApp (C revN) (ev (objHeads h) C list.toTerm Fin.elim0) = setRev list.toSet
      rw [toTerm_value list]
      exact model_rev h list.toSet_mem
  | .revOnto acc list => by
      show traceApp (traceApp (C revOntoN) (ev (objHeads h) C acc.toTerm Fin.elim0))
          (ev (objHeads h) C list.toTerm Fin.elim0) = setRevOnto acc.toSet list.toSet
      rw [toTerm_value acc, toTerm_value list]
      exact model_revOnto h acc.toSet_mem list.toSet_mem

/-- The value of `λ l. rev l` in the model is the traced graph of the reversal. -/
theorem model_revFn : ev (objHeads h) C revFn Fin.elim0 = traceLam (graph listSet setRev) := by
  show traceLam (graph (C listN) fun x => traceApp (C revN) x) = _
  rw [my_list h]
  exact congrArg traceLam (graph_congr fun _ hl => model_rev h hl)

/-- The value of `λ l. rev-onto nil l` in the model is the traced graph of the accumulator
reversal from the empty accumulator. -/
theorem model_revOntoNilFn :
    ev (objHeads h) C revOntoNilFn Fin.elim0 = traceLam (graph listSet (setRevOnto nilSet)) := by
  show traceLam (graph (C listN) fun x => traceApp (traceApp (C revOntoN) (C nilN)) x) = _
  rw [my_list h, my_nil h]
  exact congrArg traceLam (graph_congr fun _ hl => model_revOnto h nilSet_mem hl)

/-- **The set model gives the two functions one value**: `λ l. rev l` and
`λ l. rev-onto nil l` mean one traced graph. So the set model cannot tell them apart, whatever
the judgment does. -/
theorem model_revFn_eq_revOntoNilFn :
    ev (objHeads h) C revFn Fin.elim0 = ev (objHeads h) C revOntoNilFn Fin.elim0 := by
  rw [model_revFn h, model_revOntoNilFn h]
  exact setRev_graph_eq

end Model

/-! ## The three faces joined -/

/-- A closed term of the program that is a list, with its typing. -/
abbrev TypedRevList : Type := { t : CTm Tower.Head 0 // CTyped objectReversal .nil t clist }

/-- **What runs is typed**: the term of an expression, with the proof that it is a list. -/
def typing (e : RevExpr) : TypedRevList := ⟨e.toTerm, e.toTerm_typed⟩

/-- **What is typed means a set**: the value of a typed term in the set model of the
program. -/
noncomputable def meaning (h : CofinalInaccessibles.{u}) (t : TypedRevList) : ZFSet.{u} :=
  ev (objHeads h) (objectDeclarationsConsts h reversalProgram) t.1 Fin.elim0

/-- **The set of a value**: only the two constructors are read; an expression with an
operation left in it has no such reading, and the empty set, which is not a list, stands for
that. -/
noncomputable def constructorsSet : RevExpr → ZFSet.{u}
  | .nil => nilSet
  | .cons head tail => consSet head.toSet (constructorsSet tail)
  | _ => ∅

/-- **What runs reaches a set**: the expression is run to its value by the six equations, and
the constructors of the value are read as sets. -/
noncomputable def direct (e : RevExpr) : ZFSet.{u} := constructorsSet e.eval

theorem constructorsSet_of_isValue : ∀ {e : RevExpr}, e.IsValue →
    (constructorsSet e : ZFSet.{u}) = e.toSet
  | .nil, _ => rfl
  | .cons head tail, value => by
      show consSet head.toSet (constructorsSet tail) = consSet head.toSet tail.toSet
      rw [constructorsSet_of_isValue (e := tail) value]
  | .append _ _, value => value.elim
  | .rev _, value => value.elim
  | .revOnto _ _, value => value.elim

/-- **Running agrees with the sets**: the set reached by running an expression is the set of
the expression. -/
theorem direct_eq_toSet (e : RevExpr) : (direct e : ZFSet.{u}) = e.toSet :=
  (constructorsSet_of_isValue (RevExpr.eval_isValue e)).trans
    (RevExpr.toSet_eq_of_steps (RevExpr.reaches_eval e)).symm

/-- **The three ways to a set agree**: the value of the typed term of an expression, in the
set model of the program, is the set reached by running the expression. -/
theorem meaning_typing (h : CofinalInaccessibles.{u}) (e : RevExpr) :
    meaning h (typing e) = direct e :=
  (toTerm_value h e).trans (direct_eq_toSet e).symm

/-- **The triangle of the three faces of the two reversals**: running, typing and sets, with
the map from running to sets built on its own and the commutation proved. -/
noncomputable def reversalTriangle (h : CofinalInaccessibles.{u}) : Comparison.{0, 0, u + 1} Closed :=
  triangleOfThree
    (fun e : ULift.{u + 1} RevExpr => (ULift.up (typing e.down) : ULift.{u + 1} TypedRevList))
    (fun t => meaning h t.down) (fun e => direct e.down) fun e => meaning_typing h e.down

/-- **The two programs reach one set, on every face**: run, the values are one; as sets, the
sets are one; typed, the terms mean one set in the model. -/
theorem bothReversals_one_set (h : CofinalInaccessibles.{u}) (l : RevExpr) :
    (direct (.rev l) : ZFSet.{u}) = direct (.revOnto .nil l) ∧
      ((RevExpr.rev l).toSet : ZFSet.{u}) = (RevExpr.revOnto .nil l).toSet ∧
      meaning h (typing (.rev l)) = meaning h (typing (.revOnto .nil l)) :=
  ⟨congrArg constructorsSet (RevExpr.eval_rev_eq_revOnto l), rev_toSet_eq_revOnto l,
    (meaning_typing h _).trans
      ((congrArg constructorsSet (RevExpr.eval_rev_eq_revOnto l)).trans (meaning_typing h _).symm)⟩

/-- **At every length from one on, the two programs reach one set with different numbers of
steps.** -/
theorem cost_differs_at_every_length {v : RevExpr} (hv : v.IsValue) (long : 1 ≤ v.length) :
    (direct (.rev v) : ZFSet.{u}) = direct (.revOnto .nil v) ∧
      (RevExpr.rev v).cost ≠ (RevExpr.revOnto .nil v).cost :=
  ⟨congrArg constructorsSet (RevExpr.eval_rev_eq_revOnto v),
    Nat.ne_of_gt (RevExpr.cost_rev_ne_revOnto hv long)⟩

/-- The two reversals of the list of zero and one reach one set in six and in three steps. -/
noncomputable def costFiber :
    NonTrivialFiber (fun e : RevExpr => (direct e : ZFSet.{u})) RevExpr.cost where
  left := .rev zeroOne
  right := .revOnto .nil zeroOne
  sameShadow := congrArg constructorsSet (RevExpr.eval_rev_eq_revOnto zeroOne)
  differentValue := by decide

/-- **The cost of running is not a function of the set reached.** -/
theorem cost_not_from_set :
    ¬ Factors (fun e : RevExpr => (direct e : ZFSet.{u})) RevExpr.cost :=
  costFiber.not_factors

/-- **The triangle is not exact**: the two reversals of the list of zero and one are different
expressions with one set. -/
theorem reversalTriangle_loses (h : CofinalInaccessibles.{u}) :
    (reversalTriangle h).LosesProgramInformation :=
  triangleOfThree_loses _ _ _ _ (left := ⟨.rev zeroOne⟩) (right := ⟨.revOnto .nil zeroOne⟩)
    (fun same => absurd (congrArg ULift.down same) (by decide))
    (congrArg constructorsSet (RevExpr.eval_rev_eq_revOnto zeroOne))

/-- Negative example: **read with the wrong reversal on the set side, the typed term of `rev`
does not mean that set.** At the list of zero and one the typed term means the list of one
and zero, and the wrong reversal gives the list of zero and one. -/
theorem wrongRev_not_meaning (h : CofinalInaccessibles.{u}) :
    meaning h (typing (.rev zeroOne)) ≠ setWrongRev zeroOneSet := by
  rw [show meaning h (typing (.rev zeroOne)) = setRev zeroOneSet from toTerm_value h _]
  exact fun same => setWrongRev_ne_setRev same.symm

/-! ## Different as terms: what decides it -/

section Terms

open Presentation.TypedEquality.Normalization

/-! ### The judgment has η: the two functions, and a function and its η-expansion -/

/-- The context of one list. -/
abbrev oneList : CCtx Tower.Head 1 := .snoc .nil clist

/-- Applied to the variable, `λ l. rev l` is `rev` at the variable, by β. -/
theorem revFn_beta :
    CEqual objectReversal oneList (.app (revFn.rename wk) (.var 0)) (crev (.var 0)) clist :=
  .betaPi (A := clist) (B := clist) (body := crev (.var 0))
    (extReversal.ontoList.liftLists listFn_typed_one) (LevelTower.IsUniverse.sort _)
    (crev_in extReversal.ontoRev (.var 0)) (.var 0)

/-- Applied to the variable, `λ l. rev-onto nil l` is `rev-onto nil` at the variable, by β. -/
theorem revOntoNilFn_beta :
    CEqual objectReversal oneList (.app (revOntoNilFn.rename wk) (.var 0))
      (crevOnto cnil (.var 0)) clist :=
  .betaPi (A := clist) (B := clist) (body := crevOnto cnil (.var 0))
    (extReversal.ontoList.liftLists listFn_typed_one) (LevelTower.IsUniverse.sort _)
    (crevOnto_in extReversal (nil_in extReversal.ontoList) (.var 0)) (.var 0)

/-- **The two functions are equal exactly when the two reversals are equal at an unknown
list**: one way by applying both to the variable of a context `l : list` and β, the other by
η for functions (`CDerivable.etaPi`). -/
theorem revFn_typedEqual_iff :
    CEqual objectReversal .nil revFn revOntoNilFn (.pi clist clist) ↔
      CEqual objectReversal oneList (crev (.var 0)) (crevOnto cnil (.var 0)) clist := by
  constructor
  · intro functions
    have applied : CEqual objectReversal oneList (.app (revFn.rename wk) (.var 0))
        (.app (revOntoNilFn.rename wk) (.var 0)) clist :=
      .appCong (B := clist) (functions.weaken (E := clist)) (.refl (.var 0))
    exact .trans (.symm revFn_beta) (.trans applied revOntoNilFn_beta)
  · intro pointwise
    exact .etaPi revFn_typed revOntoNilFn_typed
      (.trans revFn_beta (.trans pointwise (.symm revOntoNilFn_beta)))

/-- **η equates two different terms**: `rev` and `λ l. rev l` are equal at `Π list list`.
Neither takes a step of the program's rewriting (`rev_takes_no_step`, `revFn_takes_no_step`),
and they are different terms. -/
theorem rev_typedEqual_revFn :
    CEqual objectReversal .nil (.const revN) revFn (.pi clist clist) :=
  .etaPi (rev_in extReversal.ontoRev) revFn_typed (.symm revFn_beta)

/-- `rev` and `λ l. rev l` are different terms. -/
theorem rev_erase_ne_revFn_erase : (CTm.const revN : CTm Tower.Head 0).erase ≠ revFn.erase :=
  nofun

/-! ### The rewriting of the program -/

/-- The rules of the program, erased. -/
abbrev reversalRules := rulesWith objectRules reversalProgram

/-- The explicit definitions of the program, the authored reversal and the theorem, take
arguments. -/
theorem reversalProgram_arguments : ExplicitArguments reversalProgram := by
  intro ε member
  simp only [List.mem_cons, Declaration.definition.injEq, Definition.explicit.injEq,
    reduceCtorEq, List.not_mem_nil, or_false, false_or] at member
  rcases member with rfl | rfl <;> decide

/-- **The rewriting of the program is Church–Rosser**: the program is an admissible list of
declarations over the object package. -/
theorem reversalRules_churchRosser : ConversionCoherence.ChurchRosser reversalRules :=
  reversalProgram_admissible.churchRosser objectConstructors objectNamesDeclared
    reversalProgram_arguments

theorem objectRoles_rev : objectRoles revN = .rigid := by
  rw [objectRoles_of (by decide) (by decide) (by decide) (by decide)]
  rfl

theorem objectRoles_revOntoFirst : objectRoles revOntoFirstN = .rigid := by
  rw [objectRoles_of (by decide) (by decide) (by decide) (by decide)]
  rfl

theorem objectRoles_nil : objectRoles nilN = .rigid := by
  rw [objectRoles_of (by decide) (by decide) (by decide) (by decide)]
  rfl

/-- At a spine of `rev`, a root step is an instance of an equation of `rev`. -/
theorem rootStep_rev {n : Nat} {args : List (Tm Tower.Head n)} {u : Tm Tower.Head n}
    (step : reversalRules.computation.step (appSpine (.const revN) args) u) :
    EquationInstance (.recursive revDef) (appSpine (.const revN) args) :=
  reversalProgram_admissible.rootStep_defined objectShape (D := .recursive revDef)
    (by repeat (first | exact List.mem_cons_self | apply List.mem_cons_of_mem))
    (fun _ _ role => nomatch objectRoles_rev.symm.trans role) step

/-- At a spine of `rev-onto~scrutinee-first`, a root step is an instance of one of its
equations. -/
theorem rootStep_revOntoFirst {n : Nat} {args : List (Tm Tower.Head n)} {u : Tm Tower.Head n}
    (step : reversalRules.computation.step (appSpine (.const revOntoFirstN) args) u) :
    EquationInstance (.recursive revOntoFirstDef) (appSpine (.const revOntoFirstN) args) :=
  reversalProgram_admissible.rootStep_defined objectShape (D := .recursive revOntoFirstDef)
    (by repeat (first | exact List.mem_cons_self | apply List.mem_cons_of_mem))
    (fun _ _ role => nomatch objectRoles_revOntoFirst.symm.trans role) step

/-! ### Normal forms -/

/-- One step of the program's rewriting. -/
local notation "Steps" => StepCore reversalRules.computation reversalRules.headEq

/-- **A variable takes no step.** -/
theorem var_takes_no_step {n : Nat} (i : Fin n) (u : Tm Tower.Head n) : ¬ Steps (.var i) u := by
  intro step
  cases step with
  | root root =>
      obtain ⟨c, args, same, -⟩ := rulesWith_rootStep_shape objectShape root
      have head := congrArg spineConst same
      rw [spineConst_appSpine] at head
      cases head

/-- **`nil` takes no step.** -/
theorem nil_takes_no_step {n : Nat} (u : Tm Tower.Head n) : ¬ Steps (.const nilN) u := by
  intro step
  cases step with
  | root root =>
      refine rulesWith_rootStep_not_head objectShape (c := nilN)
        (fun _ _ role => nomatch objectRoles_nil.symm.trans role) (fun d member same => ?_)
        (fun D member same => ?_) [] u root
      · simp only [List.mem_cons, Declaration.datatype.injEq, reduceCtorEq, List.not_mem_nil,
          or_false, false_or] at member
        subst member
        exact absurd same (by decide)
      · simp only [List.mem_cons, Declaration.definition.injEq, reduceCtorEq, List.not_mem_nil,
          or_false] at member
        rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          exact absurd same (by decide)

/-- **`rev` alone takes no step.** -/
theorem rev_takes_no_step {n : Nat} (u : Tm Tower.Head n) : ¬ Steps (.const revN) u := by
  intro step
  cases step with
  | root root =>
      obtain ⟨e, member, σ, same⟩ := rootStep_rev (args := []) root
      rw [Definition.equations, revDef_equations] at member
      rcases List.mem_cons.mp member with rfl | member
      · cases same
      · rcases List.mem_singleton.mp member with rfl
        cases same

/-- **`rev` at a variable takes no step**: its equations need `nil` or a `cons` there. -/
theorem revAt_takes_no_step {n : Nat} (i : Fin n) (u : Tm Tower.Head n) :
    ¬ Steps (crev (.var i) : CTm Tower.Head n).erase u := by
  intro step
  cases step with
  | root root =>
      obtain ⟨e, member, σ, same⟩ := rootStep_rev (args := [.var i]) root
      rw [Definition.equations, revDef_equations] at member
      rcases List.mem_cons.mp member with rfl | member
      · cases same
      · rcases List.mem_singleton.mp member with rfl
        cases same
  | congAppFun inner => exact rev_takes_no_step _ inner
  | congAppArg inner => exact var_takes_no_step _ _ inner

/-- **`λ l. rev l` takes no step.** -/
theorem revFn_takes_no_step (u : Tm Tower.Head 0) : ¬ Steps revFn.erase u := by
  intro step
  cases step with
  | root root =>
      obtain ⟨c, args, same, -⟩ := rulesWith_rootStep_shape objectShape root
      have head := congrArg spineConst same
      rw [spineConst_appSpine] at head
      cases head
  | congLam inner => exact revAt_takes_no_step 0 _ inner

/-- `rev-onto~scrutinee-first` alone takes no step. -/
theorem revOntoFirst_takes_no_step {n : Nat} (u : Tm Tower.Head n) :
    ¬ Steps (.const revOntoFirstN) u := by
  intro step
  cases step with
  | root root =>
      obtain ⟨e, member, σ, same⟩ := rootStep_revOntoFirst (args := []) root
      rw [Definition.equations, revOntoFirst_equations] at member
      rcases List.mem_cons.mp member with rfl | member
      · cases same
      · rcases List.mem_singleton.mp member with rfl
        cases same

/-- `rev-onto~scrutinee-first` at a variable takes no step. -/
theorem revOntoFirstAt_takes_no_step {n : Nat} (i : Fin n) (u : Tm Tower.Head n) :
    ¬ Steps (.app (.const revOntoFirstN) (.var i)) u := by
  intro step
  cases step with
  | root root =>
      obtain ⟨e, member, σ, same⟩ := rootStep_revOntoFirst (args := [.var i]) root
      rw [Definition.equations, revOntoFirst_equations] at member
      rcases List.mem_cons.mp member with rfl | member
      · cases same
      · rcases List.mem_singleton.mp member with rfl
        cases same
  | congAppFun inner => exact revOntoFirst_takes_no_step _ inner
  | congAppArg inner => exact var_takes_no_step _ _ inner

/-- **`rev-onto~scrutinee-first l nil` takes no step at a variable `l`**: its equations need `nil`
or a `cons` at the list. -/
theorem revOntoFirstNil_takes_no_step {n : Nat} (i : Fin n) (u : Tm Tower.Head n) :
    ¬ Steps (crevOntoFirst (.var i) cnil : CTm Tower.Head n).erase u := by
  intro step
  cases step with
  | root root =>
      obtain ⟨e, member, σ, same⟩ := rootStep_revOntoFirst (args := [.var i, .const nilN]) root
      rw [Definition.equations, revOntoFirst_equations] at member
      rcases List.mem_cons.mp member with rfl | member
      · cases same
      · rcases List.mem_singleton.mp member with rfl
        cases same
  | congAppFun inner => exact revOntoFirstAt_takes_no_step _ _ inner
  | congAppArg inner => exact nil_takes_no_step _ inner

/-- **`rev-onto nil l` unfolds at a variable `l`** to `rev-onto~scrutinee-first l nil`, by the
equation of the authored reversal. -/
theorem revOntoNil_step {n : Nat} (i : Fin n) :
    Steps (crevOnto cnil (.var i) : CTm Tower.Head n).erase
      (crevOntoFirst (.var i) cnil : CTm Tower.Head n).erase :=
  .root (objectReversal.erase_step
    ((definition_stepsWithin objectChurch (.explicit revOntoDef) firstStage
      [.definition (.explicit revIsRevOntoDef), .definition (.recursive revOntoAppendDef)]).step
      ⟨revOntoEquation, List.mem_cons_self, fun j => [.var i, cnil].getD j.val cnil, rfl, rfl⟩))

/-- **The two reversals at an unknown list reach two different terms that take no step**:
`rev l` takes none, `rev-onto nil l` takes one, to `rev-onto~scrutinee-first l nil`, which takes
none, and the two are different terms with different heads. -/
theorem reversals_normal_forms_differ :
    (∀ u, ¬ Steps (crev (.var 0) : CTm Tower.Head 1).erase u) ∧
      Steps (crevOnto cnil (.var 0) : CTm Tower.Head 1).erase
        (crevOntoFirst (.var 0) cnil : CTm Tower.Head 1).erase ∧
      (∀ u, ¬ Steps (crevOntoFirst (.var 0) cnil : CTm Tower.Head 1).erase u) ∧
      eliminationHead (crev (.var 0) : CTm Tower.Head 1).erase ≠
        eliminationHead (crevOntoFirst (.var 0) cnil : CTm Tower.Head 1).erase :=
  ⟨revAt_takes_no_step 0, revOntoNil_step 0, revOntoFirstNil_takes_no_step 0, by decide⟩

/-- **The two reversals at an unknown list are not convertible**: the rewriting is
Church–Rosser, `rev-onto nil l` steps to `rev-onto~scrutinee-first l nil`, and that and `rev l` are
different terms that take no step, so they have no common reduct. -/
theorem reversals_not_convertible :
    ¬ Conv reversalRules.headEq (crev (.var 0) : CTm Tower.Head 1).erase
      (crevOnto cnil (.var 0) : CTm Tower.Head 1).erase reversalRules.computation := by
  intro conv
  have toFirst := Relation.EqvGen.trans _ _ _ conv (.rel _ _ (revOntoNil_step 0))
  obtain ⟨common, fromRev, fromFirst⟩ := reversalRules_churchRosser toFirst
  have rev := ConstructorSystem.Normal.stepStar (fun {u} => revAt_takes_no_step 0 u) fromRev
  have first := ConstructorSystem.Normal.stepStar
    (fun {u} => revOntoFirstNil_takes_no_step 0 u) fromFirst
  exact reversals_normal_forms_differ.2.2.2 (congrArg eliminationHead (rev.symm.trans first))

/-! ### Controls -/

/-- Positive control: a pair the rewriting relates, `rev-onto nil (cons a l)` and
`rev-onto (cons a nil) l` at a variable number `a` and a variable list `l`, is equal in the
judgment; nothing above refutes it. -/
theorem revOnto_cons_typedEqual :
    CEqual objectReversal (.snoc (.snoc .nil cnum) clist)
      (crevOnto cnil (ccons (.var 1) (.var 0))) (crevOnto (ccons (.var 1) cnil) (.var 0)) clist :=
  revOnto_cons_in extReversal (nil_in extReversal.ontoList) (.var 1) (.var 0)

end Terms

end Mettapedia.Languages.MeTTa.PrimeCandidates.Trinity.Reverse
