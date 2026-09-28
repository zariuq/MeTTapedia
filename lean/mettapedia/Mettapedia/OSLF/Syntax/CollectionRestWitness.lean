import Mettapedia.OSLF.Syntax.BindingSignature
import Mettapedia.OSLF.Syntax.StepRelationCaptureWitness

/-!
# Rest splicing is not substitution, and it declines silently

The binding applier's collection case does something substitution does not do:
it inspects the *shape* of the value a metavariable is bound to.  A rest
variable is spliced only when its binding is a collection of the same kind with
no rest of its own; in every other case the rest is left unresolved and the rule
still fires.

Two consequences are recorded here.  A rule fires and produces a term still
mentioning a rule variable, which no substitution should ever do -- and it does
so *silently*, with no failure to observe.  And the result depends on data that
substitution cannot see: the same rule, the same variable, values that differ
only in collection kind, and one is spliced while the other is not.
-/

namespace Mettapedia.OSLF.Binding

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match

set_option autoImplicit false

namespace CollectionRest

/-- `wrap(R)  ~>  {  | R }`: a rule that rebuilds a collection around whatever
its rest variable stands for. -/
def spliceRule : RewriteRule where
  name := "splice"
  typeContext := []
  premises := []
  left := .apply "wrap" [.fvar "R"]
  right := .collection .vec [] (some "R")

def spliceLang : LanguageDef where
  name := "splice"
  types := []
  terms := []
  equations := []
  rewrites := [spliceRule]

def elemC : Pattern := .apply "c" []

/-- A value of the same kind, with no rest: this one is spliced. -/
def matchingValue : Pattern := .collection .vec [elemC] none

/-- The same elements, a different kind. -/
def otherKindValue : Pattern := .collection .hashBag [elemC] none

/-- The same elements and kind, but carrying a rest of its own. -/
def nestedRestValue : Pattern := .collection .vec [elemC] (some "S")

theorem splices_when_shape_matches :
    rewriteStep spliceLang (.apply "wrap" [matchingValue])
      = [.collection .vec [elemC] none] := by
  decide +kernel

/-- **A different collection kind is not spliced**, and the rule still fires. -/
theorem declines_on_other_kind :
    rewriteStep spliceLang (.apply "wrap" [otherKindValue])
      = [.collection .vec [] (some "R")] := by
  decide +kernel

/-- **A value with a rest of its own is not spliced either.** -/
theorem declines_on_nested_rest :
    rewriteStep spliceLang (.apply "wrap" [nestedRestValue])
      = [.collection .vec [] (some "R")] := by
  decide +kernel

/-- **The rule fires and its own variable survives into the reduct.**  No
substitution may do that: after firing, a rule variable is not a term of the
language, it is a name the rule has left behind. -/
theorem reduct_still_mentions_the_rule_variable :
    ∀ u ∈ rewriteStep spliceLang (.apply "wrap" [otherKindValue]),
      u = .collection .vec [] (some "R") := by
  rw [declines_on_other_kind]
  intro u hu
  simp only [List.mem_singleton] at hu
  exact hu

/-- **And it declines silently**: the step relation reports a reduct in every
case, so nothing downstream can tell the spliced result from the unspliced
one by observing whether the rule fired. -/
theorem no_failure_is_reported :
    (rewriteStep spliceLang (.apply "wrap" [matchingValue])).length = 1
      ∧ (rewriteStep spliceLang (.apply "wrap" [otherKindValue])).length = 1
      ∧ (rewriteStep spliceLang (.apply "wrap" [nestedRestValue])).length = 1 := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- **The outcome depends on the value's kind**, which substitution has no
business reading: two values with the same elements are treated differently. -/
theorem outcome_depends_on_the_value_s_shape :
    rewriteStep spliceLang (.apply "wrap" [matchingValue])
      ≠ rewriteStep spliceLang (.apply "wrap" [otherKindValue]) := by
  rw [splices_when_shape_matches, declines_on_other_kind]
  decide

end CollectionRest

namespace CollectionRestRepair

/-! # Splicing is instantiation

The defect above is not a bug in a traversal: it is what happens when a
variable standing for *a run of elements* is given the sort of a single term.
Nothing can then be substituted for it, so the applier inspects the value's
shape instead and declines when the shape disappoints it.

Giving sequences their own sort makes the declared tail metavariable's
splicing ordinary instantiation: no shape is inspected and no case declines.
That is not a general variable-elimination result. This example's base
signature still contains `restOp name`; instantiation preserves that operator,
and erasure turns it into an unresolved pattern rest. The groundness controls
below distinguish the two cases.
-/

/-- Two sorts: elements, and runs of elements. -/
inductive Srt where
  | el
  | seq
  deriving DecidableEq

inductive Op : Srt → Type where
  | atomOp (name : String) : Op Srt.el
  | collOp : Op Srt.el
  | nilOp : Op Srt.seq
  | restOp (name : String) : Op Srt.seq
  | consOp : Op Srt.seq

/-- A collection holds one run; a run is nil or an element followed by a run. -/
abbrev minSig : Signature where
  Srt := Srt
  Op := Op
  arity := fun {_} o => match o with
    | .atomOp _ => []
    | .collOp => [([], Srt.seq)]
    | .nilOp => []
    | .restOp _ => []
    | .consOp => [([], Srt.el), ([], Srt.seq)]

/-- One metavariable, at the sequence sort: it stands for a run, not a term. -/
abbrev restMetas : List (MetaArity minSig) := [([], Srt.seq)]

abbrev restSig : Signature := withMetas minSig restMetas

def atomA : Term minSig [] Srt.el := Term.op (S := minSig) (Op.atomOp "a") Args.nil

def atomA' : Term restSig [] Srt.el :=
  Term.op (S := restSig) (Sum.inl (Op.atomOp "a")) Args.nil

/-- `{ a | R }`: one explicit element, then the rest variable in tail position. -/
def restSchema : Term restSig [] Srt.el :=
  Term.op (S := restSig) (Sum.inl Op.collOp)
    (.cons
      (Term.op (S := restSig) (Sum.inl Op.consOp)
        (.cons atomA'
          (.cons (Term.op (S := restSig) (Sum.inr (MetaOp.mk ⟨0, by decide⟩)) .nil) .nil)))
      .nil)

def restBody (v : Term minSig [] Srt.seq) :
    (i : Fin restMetas.length) → Term minSig (restMetas.get i).1 (restMetas.get i).2
  | ⟨0, _⟩ => v
  | ⟨_ + 2, h⟩ => by simp [restMetas] at h

/-- The empty argument list is the identity substitution on the empty context. -/
theorem argsToSub_nil_eq_id :
    argsToSub (S := minSig) (bs := []) (Γ := ([] : Ctx minSig)) Args.nil
      = fun _ x => Term.var x := by
  funext _ x
  cases x

/-- Splicing the declared metavariable is instantiation, for every sequence
value. Names already in base operators are not eliminated. -/
theorem splice_is_instantiation (v : Term minSig [] Srt.seq) :
    instantiate (restBody v) restSchema
      = Term.op (S := minSig) Op.collOp
          (.cons (Term.op (S := minSig) Op.consOp (.cons atomA (.cons v .nil))) .nil) := by
  show Term.op (S := minSig) Op.collOp
      (.cons (Term.op (S := minSig) Op.consOp
        (.cons atomA (.cons (bind (argsToSub Args.nil) v) .nil))) .nil) = _
  rw [argsToSub_nil_eq_id, bind_id]

/-- **Including values that the current applier silently declines**: a run that
itself ends in a further rest variable is spliced like any other, because a run
is a run. -/
theorem splices_a_run_ending_in_a_rest
    (w : Term minSig [] Srt.seq) (b : Term minSig [] Srt.el) :
    instantiate (restBody (Term.op (S := minSig) Op.consOp (.cons b (.cons w .nil))))
        restSchema
      = Term.op (S := minSig) Op.collOp
          (.cons (Term.op (S := minSig) Op.consOp
            (.cons atomA
              (.cons (Term.op (S := minSig) Op.consOp (.cons b (.cons w .nil))) .nil))) .nil) :=
  splice_is_instantiation _

/-- **A value of the wrong sort is not a value.**  Where the current applier has
a case that declines, the presentation has no term: an element cannot be offered
where a run is required. -/
theorem an_element_is_not_a_run :
    ∀ (i : Fin restMetas.length), (restMetas.get i).2 = Srt.seq := by
  intro i
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨_ + 2, h⟩ => simp [restMetas] at h

/-! ## Erasure is sort-indexed, and that is the whole obstruction to merging

A run is not a term, so erasing one does not give a `Pattern`: it gives the
elements and the rest that a `Pattern.collection` carries inline.  Erasure is
therefore indexed by the sort, with one function per sort rather than one
function over all of them.  That is the entire cost of folding the sequence sort
into the pattern presentation, and it is recorded here in working form so the
fold is mechanical rather than exploratory.

On closed terms there is no dead branch at all: a variable at the sequence sort
cannot occur, because contexts hold only elements. -/

/-- What a term of each sort erases to.  A run is not a term, so it does not
erase to a `Pattern`: it erases to the elements and the rest that a collection
carries inline.  This indexing is the entire cost of folding the sequence sort
into the pattern presentation. -/
def EraseTy : Srt → Type
  | Srt.el => Pattern
  | Srt.seq => List Pattern × Option String

def varIdx : {Γ : Ctx minSig} → {s : Srt} → Var Γ s → Nat
  | _, _, .zero => 0
  | _, _, .succ w => varIdx w + 1

/-- Erasure, one case per sort.  The only case that cannot arise is a
variable at the sequence sort, and the theorem below says why. -/
def eraseT : {Γ : Ctx minSig} → {s : Srt} → Term minSig Γ s → EraseTy s
  | _, Srt.el, .var v => Pattern.bvar (varIdx v)
  | _, Srt.seq, .var _ => ([], none)
  | _, _, .op (.atomOp name) _ => Pattern.apply name []
  | _, _, .op .collOp (.cons l .nil) =>
      Pattern.collection .vec (eraseT l).1 (eraseT l).2
  | _, _, .op .nilOp _ => ([], none)
  | _, _, .op (.restOp name) _ => ([], some name)
  | _, _, .op .consOp (.cons hd (.cons tl .nil)) =>
      (eraseT hd :: (eraseT tl).1, (eraseT tl).2)

/-- **The unreachable case is unreachable.**  Contexts hold elements, so no
variable ever has the sequence sort, and the case above is justified rather
than arbitrary. -/
theorem no_seq_var : ∀ (n : Nat), Var (List.replicate n Srt.el) Srt.seq → False
  | 0, v => nomatch v
  | n + 1, v => by
      cases v with
      | succ w => exact no_seq_var n w

/-- **Erasing the spliced term gives the collection the applier was trying to
build**: the explicit element, then the run's elements, then the run's own rest
if it has one. -/
theorem erase_of_splice (v : Term minSig [] Srt.seq) :
    eraseT (instantiate (restBody v) restSchema)
      = .collection .vec (.apply "a" [] :: (eraseT v).1) (eraseT v).2 := by
  rw [splice_is_instantiation]
  rfl

/-- A run ending in a rest keeps that rest, rather than being refused. -/
theorem erase_of_splice_with_rest (name : String) :
    eraseT (instantiate (restBody (Term.op (S := minSig) (Op.restOp name) Args.nil))
        restSchema)
      = .collection .vec [.apply "a" []] (some name) := by
  rw [erase_of_splice]
  rfl

/-- A base rest operator survives the typed splice as an unresolved MeTTa
variable. The base signature alone does not guarantee ground execution data. -/
theorem erased_splice_with_base_rest_is_not_ground (name : String) :
    (eraseT (instantiate
      (restBody (Term.op (S := minSig) (Op.restOp name) Args.nil))
      restSchema)).isGround = false := by
  rw [erase_of_splice_with_rest]
  rfl

/-- And a closed run splices to a rest-free collection. -/
theorem erase_of_splice_closed (b : String) :
    eraseT (instantiate
        (restBody (Term.op (S := minSig) Op.consOp
          (.cons (Term.op (S := minSig) (Op.atomOp b) Args.nil)
            (.cons (Term.op (S := minSig) Op.nilOp Args.nil) .nil))))
        restSchema)
      = .collection .vec [.apply "a" [], .apply b []] none := by
  rw [erase_of_splice]
  rfl

/-- In contrast, the actual closed input run erases to ground data. -/
theorem erased_closed_splice_is_ground (b : String) :
    (eraseT (instantiate
        (restBody (Term.op (S := minSig) Op.consOp
          (.cons (Term.op (S := minSig) (Op.atomOp b) Args.nil)
            (.cons (Term.op (S := minSig) Op.nilOp Args.nil) .nil))))
        restSchema)).isGround = true := by
  rw [erase_of_splice_closed]
  rfl

end CollectionRestRepair

end Mettapedia.OSLF.Binding
