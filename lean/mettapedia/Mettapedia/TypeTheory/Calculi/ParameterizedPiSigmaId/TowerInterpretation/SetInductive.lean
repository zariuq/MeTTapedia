import Mettapedia.Logic.HOL.Embedding.ZFSetInductive
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.IotaKnowledge
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.MappedSchemas

/-!
# Simple inductive types in the set tower

A simple inductive type has constructors whose fields are the type itself or closed types
(`Normalization.Field`, `ctorType`, `recType`). Its set is the least set closed under its
constructors (`ZFSetInductive.carrier`). This module reads the declaration of such a type in
the set tower, and shows that a package extended by one has a set model.

**Curried trace functions.** A constructor and a method of the recursor take their arguments
one by one. Over the fields of a constructor, `curriedGraph` is the curried traced graph of a
function of argument lists and `curriedSet` the set of such trace functions into a family of
sets; `applyList` applies a trace function to a list of values. Applied to arguments that fit
the fields, the graph gives the function's value (`applyList_curriedGraph`), and a member of
the set gives a member of the family (`applyList_mem`).

**The recursor.** A method for constructor `i` over a motive `P` takes the fields and one
member of `P a` for each recursive field `a`, and returns a member of `P` at the constructor's
value (`caseSet`). Recursion with such methods (`methodStep`) stays in the motive
(`recursion_mem`), by induction on the carrier, and computes at a constructor by the method
(`ZFSetInductive.recFun_constructor`).

**Telescopes as lists.** The declared types of the constructors and of the recursor are
dependent function types over telescopes given entry by entry (`ofEntries`). An environment of
such a telescope is read as the list of its values, the oldest first (`envOf`, `envList`), and
it satisfies the telescope exactly when each value lies in the value of its entry at the
values before it (`sat_ofEntries`).

**The reading of a declaration** (`InductiveReading`): the type is the carrier of its
signature (`signature`: a closed field is read as the set of its type), each constructor is
the traced graph of its constructor values, and the recursor is the traced graph of the
recursion with the methods. Under a reading

* a constructor lies in the value of its declared type and gives its constructor value at
  arguments that fit (`ctor_mem`, `ctor_apply`);
* the value of the type of a method is the set of the methods over the motive's value
  (`ev_caseType`);
* the recursor lies in the value of its declared type (`rec_mem`), and at a constructor it
  gives the constructor's method applied to the fields and to its own values at the recursive
  fields (`rec_iota`);
* every computation rule of the recursor is valid at its typed instances (`iota_valid`), so
  the package of the declaration (`inductiveChurch`) has a set model (`inductive_setModel`).

**A reading exists over every base assignment** for a fresh declaration
(`FreshDeclaration`: distinct names, and closed field types whose sets do not depend on the
new names): `inductiveConsts` assigns the carrier, the graphs and the recursion in that order
(`inductiveConsts_reading`). Hence **a package extended by a fresh simple inductive declaration
has a set model** (`extension_setModel`), when the base package has one at every assignment
that agrees with the base outside the new names, and the type's universe is closed, holds the
natural numbers and the sets of the closed field types.

**A reading reads only the declaration's names and field types** (`InductiveReading.of_agrees`):
an assignment with the same sets at the type, the constructors and the recursor, and the same
sets of the closed field types, is a reading too. So the model of an extension is a model at
every such assignment at which the base has one (`extension_setModel_at`), which is what lets
a further declaration be added.

The validity of the computation rules uses one fact about the annotation of their left sides:
typed instances satisfy the telescope of the metavariables (the hypothesis `satisfies` of
`inductive_setModel`). It holds for every declaration with distinct names and closed field
types without abstraction (`iotaLeft_known`), which gives `inductive_setModel_distinct`.

Positive example: the lists of numbers over the object package of the MeTTa candidate
(`objectLists_model`, in the executable model of the candidate). Negative examples: a set of
values that does not fit the fields is not an environment of the constructor's telescope
(`sat_ctorTele`), and a signature whose only constructor is recursive has the empty carrier
(`ZFSetInductive.loop_carrier_empty`), so a declaration without a base case is read as the
empty type.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation

open Presentation Presentation.TypedEquality.Annotated
open Presentation.TypedEquality.Normalization (ofEntries)
open Presentation.TypedEquality.Impredicative.Domain (pisCtx)
open Presentation.TelescopeAbstraction (closeType)
open Mettapedia.Logic.HOL.Embedding
open ZFSetDependentProducts (graph)
open ZFSetTraceProducts (traceLam traceApp tracePiSet traceApp_graph_beta tracePiSet_congr)
open ZFSetInductive (Fits FitsPred constructorValue carrier recFun mapRec)

universe u

/-! ## Trace functions applied to lists of values -/

/-- A trace function applied to a list of values, the first first. -/
noncomputable def applyList (f : ZFSet.{u}) (args : List ZFSet.{u}) : ZFSet.{u} :=
  args.foldl traceApp f

theorem applyList_cons (f a : ZFSet.{u}) (args : List ZFSet.{u}) :
    applyList f (a :: args) = applyList (traceApp f a) args := rfl

theorem applyList_append (f : ZFSet.{u}) (args more : List ZFSet.{u}) :
    applyList f (args ++ more) = applyList (applyList f args) more :=
  List.foldl_append ..

/-! ## Curried trace functions over the fields of a constructor -/

/-- **The curried traced graph of a function of argument lists**, over the fields of a
constructor: a recursive field takes its argument from `X`, a set field from its set. -/
noncomputable def curriedGraph (X : ZFSet.{u}) :
    List ZFSetInductive.Field.{u} → (List ZFSet.{u} → ZFSet.{u}) → ZFSet.{u}
  | [], body => body []
  | .recursive :: fs, body =>
      traceLam (graph X fun a => curriedGraph X fs fun args => body (a :: args))
  | .ofSet A :: fs, body =>
      traceLam (graph A fun a => curriedGraph X fs fun args => body (a :: args))

/-- **The set of the curried trace functions** over the fields of a constructor into a family
of sets indexed by the argument lists. -/
noncomputable def curriedSet (X : ZFSet.{u}) :
    List ZFSetInductive.Field.{u} → (List ZFSet.{u} → ZFSet.{u}) → ZFSet.{u}
  | [], family => family []
  | .recursive :: fs, family =>
      tracePiSet X fun a => curriedSet X fs fun args => family (a :: args)
  | .ofSet A :: fs, family =>
      tracePiSet A fun a => curriedSet X fs fun args => family (a :: args)

/-- **β for curried graphs**: applied to arguments that fit the fields, the graph gives the
function's value. -/
theorem applyList_curriedGraph {X : ZFSet.{u}} {fs : List ZFSetInductive.Field.{u}}
    {args : List ZFSet.{u}} (fits : Fits X fs args) :
    ∀ body : List ZFSet.{u} → ZFSet.{u}, applyList (curriedGraph X fs body) args = body args := by
  induction fits with
  | nil => exact fun _ => rfl
  | @recursive fs args a member _ ih =>
    intro body
    show applyList (traceApp (traceLam (graph X fun a =>
      curriedGraph X fs fun args => body (a :: args))) a) args = _
    rw [traceApp_graph_beta _ member]
    exact ih _
  | @ofSet A fs args a member _ ih =>
    intro body
    show applyList (traceApp (traceLam (graph A fun a =>
      curriedGraph X fs fun args => body (a :: args))) a) args = _
    rw [traceApp_graph_beta _ member]
    exact ih _

/-- A curried graph lies in the set of curried trace functions into a family when the
function's values lie in the family at arguments that fit. -/
theorem curriedGraph_mem {X : ZFSet.{u}} :
    ∀ (fs : List ZFSetInductive.Field.{u}) {body family : List ZFSet.{u} → ZFSet.{u}},
      (∀ args, Fits X fs args → body args ∈ family args) →
        curriedGraph X fs body ∈ curriedSet X fs family
  | [], _, _, typed => typed [] .nil
  | .recursive :: fs, _, _, typed => traceLam_graph_mem fun a ha =>
      curriedGraph_mem fs fun args fits => typed (a :: args) (.recursive ha fits)
  | .ofSet _ :: fs, _, _, typed => traceLam_graph_mem fun a ha =>
      curriedGraph_mem fs fun args fits => typed (a :: args) (.ofSet ha fits)

/-- A curried trace function applied to arguments that fit gives a member of the family
there. -/
theorem applyList_mem {X : ZFSet.{u}} {fs : List ZFSetInductive.Field.{u}}
    {args : List ZFSet.{u}} (fits : Fits X fs args) :
    ∀ {f : ZFSet.{u}} {family : List ZFSet.{u} → ZFSet.{u}}, f ∈ curriedSet X fs family →
      applyList f args ∈ family args := by
  induction fits with
  | nil => exact fun member => member
  | recursive ha _ ih => exact fun member => ih (traceApp_mem_fibre member ha)
  | ofSet ha _ ih => exact fun member => ih (traceApp_mem_fibre member ha)

/-- The set of curried trace functions reads its family at arguments that fit. -/
theorem curriedSet_congr {X : ZFSet.{u}} :
    ∀ (fs : List ZFSetInductive.Field.{u}) {F G : List ZFSet.{u} → ZFSet.{u}},
      (∀ args, Fits X fs args → F args = G args) → curriedSet X fs F = curriedSet X fs G
  | [], _, _, same => same [] .nil
  | .recursive :: fs, _, _, same => tracePiSet_congr fun a ha =>
      curriedSet_congr fs fun args fits => same (a :: args) (.recursive ha fits)
  | .ofSet _ :: fs, _, _, same => tracePiSet_congr fun a ha =>
      curriedSet_congr fs fun args fits => same (a :: args) (.ofSet ha fits)

/-! ## Functions of induction hypotheses -/

/-- The trace functions that take a member of each listed set in turn and return a member of
the target. -/
noncomputable def arrowsSet : List ZFSet.{u} → ZFSet.{u} → ZFSet.{u}
  | [], target => target
  | D :: Ds, target => tracePiSet D fun _ => arrowsSet Ds target

/-- Such a function applied to members of the listed sets gives a member of the target. -/
theorem applyList_arrows {Ds ys : List ZFSet.{u}} {target : ZFSet.{u}}
    (members : List.Forall₂ (fun y D => y ∈ D) ys Ds) :
    ∀ {f : ZFSet.{u}}, f ∈ arrowsSet Ds target → applyList f ys ∈ target := by
  induction members with
  | nil => exact fun member => member
  | cons hy _ ih => exact fun member => ih (traceApp_mem_fibre member hy)

/-- **The curried traced graph of a function of induction hypotheses**: it takes a member of
each listed set in turn. -/
noncomputable def arrowsGraph : List ZFSet.{u} → (List ZFSet.{u} → ZFSet.{u}) → ZFSet.{u}
  | [], body => body []
  | D :: Ds, body => traceLam (graph D fun y => arrowsGraph Ds fun ys => body (y :: ys))

/-- Such a graph is a function of induction hypotheses into the target, when its values at
members of the listed sets lie in the target. -/
theorem arrowsGraph_mem {target : ZFSet.{u}} :
    ∀ (Ds : List ZFSet.{u}) {body : List ZFSet.{u} → ZFSet.{u}},
      (∀ ys, List.Forall₂ (fun y D => y ∈ D) ys Ds → body ys ∈ target) →
        arrowsGraph Ds body ∈ arrowsSet Ds target
  | [], _, typed => typed [] .nil
  | _ :: Ds, _, typed => traceLam_graph_mem fun y hy =>
      arrowsGraph_mem Ds fun ys members => typed (y :: ys) (.cons hy members)

/-- **β for graphs of functions of induction hypotheses.** -/
theorem applyList_arrowsGraph {Ds ys : List ZFSet.{u}}
    (members : List.Forall₂ (fun y D => y ∈ D) ys Ds) :
    ∀ body : List ZFSet.{u} → ZFSet.{u}, applyList (arrowsGraph Ds body) ys = body ys := by
  induction members with
  | nil => exact fun _ => rfl
  | @cons y D ys Ds hy _ ih =>
    intro body
    show applyList (traceApp (traceLam (graph D fun y =>
      arrowsGraph Ds fun ys => body (y :: ys))) y) ys = _
    rw [traceApp_graph_beta _ hy]
    exact ih _

/-! ## The recursor of a simple inductive type -/

/-- **The methods for constructor `i` over a motive**: curried trace functions that take the
fields, then a member of the motive at each recursive field, and return a member of the motive
at the constructor's value. -/
noncomputable def caseSet (X : ZFSet.{u}) (P : ZFSet.{u} → ZFSet.{u}) (i : Nat)
    (fs : List ZFSetInductive.Field.{u}) : ZFSet.{u} :=
  curriedSet X fs fun args => arrowsSet (mapRec P fs args) (P (constructorValue i args))

/-- **What the recursor does at constructor `i`**: the method at `i`, applied to the
arguments and then to the results at the recursive arguments. -/
noncomputable def methodStep (methods : List ZFSet.{u}) (i : Nat)
    (args results : List ZFSet.{u}) : ZFSet.{u} :=
  applyList (methods.getD i ∅) (args ++ results)

/-- Arguments at which a function has values in a motive at the recursive ones: they fit, and
the results lie in the motive's sets. -/
theorem fits_and_results {X : ZFSet.{u}} {f P : ZFSet.{u} → ZFSet.{u}}
    {fs : List ZFSetInductive.Field.{u}} {args : List ZFSet.{u}}
    (fitting : FitsPred (fun x => x ∈ X ∧ f x ∈ P x) fs args) :
    Fits X fs args ∧ List.Forall₂ (fun y D => y ∈ D) (mapRec f fs args) (mapRec P fs args) := by
  induction fitting with
  | nil => exact ⟨.nil, .nil⟩
  | recursive holds _ ih => exact ⟨.recursive holds.1 ih.1, .cons holds.2 ih.2⟩
  | ofSet member _ ih => exact ⟨.ofSet member ih.1, ih.2⟩

/-- **Recursion stays in the motive**: with a method in the methods' set for each
constructor, the recursion's value at a member of the carrier lies in the motive there. -/
theorem recursion_mem {sig : ZFSetInductive.Signature.{u}} {P : ZFSet.{u} → ZFSet.{u}}
    {methods : List ZFSet.{u}}
    (typed : ∀ i c, sig[i]? = some c → methods.getD i ∅ ∈ caseSet (carrier sig) P i c)
    {t : ZFSet.{u}} (member : t ∈ carrier sig) :
    recFun (sig := sig) (methodStep methods) t ∈ P t := by
  refine (ZFSetInductive.carrier_induct
    (P := fun x => x ∈ carrier sig ∧ recFun (sig := sig) (methodStep methods) x ∈ P x)
    (fun i c args atIndex fitting => ?_) member).2
  obtain ⟨fits, results⟩ := fits_and_results fitting
  refine ⟨ZFSetInductive.constructor_mem_carrier atIndex fits, ?_⟩
  rw [ZFSetInductive.recFun_constructor (methodStep methods) atIndex fits]
  show applyList (methods.getD i ∅)
    (args ++ mapRec (recFun (sig := sig) (methodStep methods)) c args) ∈ _
  rw [applyList_append]
  exact applyList_arrows results (applyList_mem fits (typed i c atIndex))

/-- **A method given by a function of the fields and the induction hypotheses**: its curried
graph over the fields and then over the hypotheses. -/
noncomputable def methodValue (X : ZFSet.{u}) (P : ZFSet.{u} → ZFSet.{u})
    (fs : List ZFSetInductive.Field.{u}) (body : List ZFSet.{u} → List ZFSet.{u} → ZFSet.{u}) :
    ZFSet.{u} :=
  curriedGraph X fs fun args => arrowsGraph (mapRec P fs args) fun results => body args results

/-- It is a method for constructor `i` when the function's values lie in the motive at the
constructor's value. -/
theorem methodValue_mem {X : ZFSet.{u}} {P : ZFSet.{u} → ZFSet.{u}} {i : Nat}
    {fs : List ZFSetInductive.Field.{u}} {body : List ZFSet.{u} → List ZFSet.{u} → ZFSet.{u}}
    (typed : ∀ args, Fits X fs args → ∀ results,
      List.Forall₂ (fun y D => y ∈ D) results (mapRec P fs args) →
        body args results ∈ P (constructorValue i args)) :
    methodValue X P fs body ∈ caseSet X P i fs :=
  curriedGraph_mem fs fun args fits =>
    arrowsGraph_mem (mapRec P fs args) fun results members => typed args fits results members

/-- **β for such a method**: applied to fields that fit and to hypotheses in the motive, it
gives the function's value. -/
theorem applyList_methodValue {X : ZFSet.{u}} {P : ZFSet.{u} → ZFSet.{u}}
    {fs : List ZFSetInductive.Field.{u}} {args results : List ZFSet.{u}}
    (body : List ZFSet.{u} → List ZFSet.{u} → ZFSet.{u}) (fits : Fits X fs args)
    (members : List.Forall₂ (fun y D => y ∈ D) results (mapRec P fs args)) :
    applyList (methodValue X P fs body) (args ++ results) = body args results := by
  rw [applyList_append, methodValue, applyList_curriedGraph fits,
    applyList_arrowsGraph members]

/-- The values of a function at the recursive arguments lie in a motive's sets there, when the
function has its values in the motive on `X`. -/
theorem mapRec_mem {X : ZFSet.{u}} {g P : ZFSet.{u} → ZFSet.{u}}
    {fs : List ZFSetInductive.Field.{u}} {args : List ZFSet.{u}} (fits : Fits X fs args)
    (typed : ∀ x ∈ X, g x ∈ P x) :
    List.Forall₂ (fun y D => y ∈ D) (mapRec g fs args) (mapRec P fs args) := by
  induction fits with
  | nil => exact .nil
  | recursive member _ ih => exact .cons (typed _ member) ih
  | ofSet _ _ ih => exact ih

/-- The methods among the arguments of the recursor: after the motive, as many as there are
constructors. -/
def methodsOf (values : List ZFSet.{u}) (count : Nat) : List ZFSet.{u} :=
  (values.drop 1).take count

theorem methodsOf_getD (values : List ZFSet.{u}) {count i : Nat} (below : i < count) :
    (methodsOf values count).getD i ∅ = values.getD (i + 1) ∅ := by
  rw [methodsOf, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_take_of_lt below, List.getElem?_drop, Nat.add_comm]

/-! ## Environments as lists -/

/-- The environment of `n` variables whose values are the first `n` entries of a list, the
oldest variable first. -/
def envOf (values : List ZFSet.{u}) (n : Nat) : Env.{u} n :=
  fun i => values.getD (n - 1 - i.val) ∅

/-- The values of an environment, the oldest variable first. -/
def envList : {n : Nat} → Env.{u} n → List ZFSet.{u}
  | 0, _ => []
  | _ + 1, η => envList (η ∘ Fin.succ) ++ [η 0]

theorem envOf_succ (values : List ZFSet.{u}) (n : Nat) :
    envOf values (n + 1) = extend (envOf values n) (values.getD n ∅) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · show values.getD (n + 1 - 1 - (j.val + 1)) ∅ = values.getD (n - 1 - j.val) ∅
    congr 1
    omega

theorem envList_length : ∀ {n : Nat} (η : Env.{u} n), (envList η).length = n
  | 0, _ => rfl
  | n + 1, η => by
    show (envList (η ∘ Fin.succ) ++ [η 0]).length = n + 1
    rw [List.length_append, envList_length]
    rfl

/-- The list of an environment read from a list is the list's start. -/
theorem envList_envOf (values : List ZFSet.{u}) :
    ∀ n, n ≤ values.length → envList (envOf values n) = values.take n
  | 0, _ => rfl
  | n + 1, le => by
    have older : envOf values (n + 1) ∘ Fin.succ = envOf values n := by
      rw [envOf_succ]
      rfl
    have newest : envOf values (n + 1) 0 = values.getD n ∅ := by
      rw [envOf_succ]
      rfl
    show envList (envOf values (n + 1) ∘ Fin.succ) ++ [envOf values (n + 1) 0] = _
    rw [older, newest, envList_envOf values n (Nat.le_of_succ_le le), List.take_add_one,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (Nat.lt_of_succ_le le)]
    rfl

/-- An environment read from a longer list is read from its start. -/
theorem envOf_append (values more : List ZFSet.{u}) (n : Nat) (le : n ≤ values.length) :
    envOf (values ++ more) n = envOf values n := by
  funext i
  show (values ++ more).getD (n - 1 - i.val) ∅ = values.getD (n - 1 - i.val) ∅
  have inside : n - 1 - i.val < values.length := by
    have := i.isLt
    omega
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left inside]

/-- An environment is read from its own list. -/
theorem envOf_envList : ∀ {n : Nat} (η : Env.{u} n), envOf (envList η) n = η
  | 0, η => funext fun i => i.elim0
  | n + 1, η => by
    show envOf (envList (η ∘ Fin.succ) ++ [η 0]) (n + 1) = η
    have length := envList_length (η ∘ Fin.succ)
    rw [envOf_succ, envOf_append _ _ n (le_of_eq length.symm), envOf_envList (η ∘ Fin.succ)]
    have newest : (envList (η ∘ Fin.succ) ++ [η 0]).getD n ∅ = η 0 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_of_eq length),
        length, Nat.sub_self]
      rfl
    rw [newest]
    exact extend_tail_head η

section Telescopes

variable {Head : Type} (heads : Head → ZFSet.{u}) (consts : DeclName → ZFSet.{u})

/-- Applying a trace function to the list of an environment is applying it to the
environment's values. -/
theorem applyList_envList (f : ZFSet.{u}) : ∀ {n : Nat} (η : Env.{u} n),
    applyList f (envList η) = applyValues f n η
  | 0, _ => rfl
  | n + 1, η => by
    show applyList f (envList (η ∘ Fin.succ) ++ [η 0]) =
      traceApp (applyValues f n (η ∘ Fin.succ)) (η 0)
    rw [applyList_append, applyList_envList f (η ∘ Fin.succ)]
    rfl

/-- **An environment satisfies a telescope given by its entries** exactly when each value
lies in the value of its entry at the values before it. -/
theorem sat_ofEntries (entry : (j : Nat) → Tm Head j) (values : List ZFSet.{u}) :
    ∀ n, Sat heads consts (liftCtx (ofEntries entry n)) (envOf values n) ↔
      ∀ j, j < n → values.getD j ∅ ∈ ev heads consts (liftTm (entry j)) (envOf values j)
  | 0 => ⟨fun _ j below => absurd below (Nat.not_lt_zero j), fun _ => sat_nil heads consts _⟩
  | n + 1 => by
    rw [envOf_succ]
    show Sat heads consts ((liftCtx (ofEntries entry n)).snoc (liftTm (entry n)))
      (extend (envOf values n) (values.getD n ∅)) ↔ _
    rw [sat_snoc, sat_ofEntries entry values n]
    constructor
    · rintro ⟨older, newest⟩ j below
      rcases Nat.lt_succ_iff_lt_or_eq.mp below with earlier | rfl
      · exact older j earlier
      · exact newest
    · intro all
      exact ⟨fun j below => all j (Nat.lt_succ_of_lt below), all n (Nat.lt_succ_self n)⟩

/-- The annotation of a dependent function type over a telescope without abstractions is the
dependent function type over the annotated telescope. -/
theorem liftTm_closeType : ∀ {n : Nat} (Γ : Ctx Head n) (C : Tm Head n),
    liftTm (closeType Γ C) = pisCtx (liftCtx Γ) (liftTm C)
  | _, .nil, _ => rfl
  | _, .snoc Γ A, C => liftTm_closeType Γ (.pi A C)

end Telescopes

/-! ## The constructors of a declaration -/

section Reading

open Presentation.TypedEquality.Normalization (ctorEntry ctorTele ctorType caseHypsSub
  caseHyps caseFields caseType appSpine)

/-- The fields of the constructors of a declaration. -/
local notation "DeclField" => TypedEquality.Normalization.Field

variable {Head : Type} (heads : Head → ZFSet.{u}) (consts : DeclName → ZFSet.{u})

/-- The set side of a field of a constructor: recursive, or the set of its closed type. -/
noncomputable def fieldSig : DeclField Head → ZFSetInductive.Field.{u}
  | .recursive => .recursive
  | .closed F => .ofSet (ev heads consts (liftTm F) Fin.elim0)

/-- The signature of the constructors of a declaration. -/
noncomputable def signature (ctors : List (DeclName × List (DeclField Head))) :
    ZFSetInductive.Signature.{u} :=
  ctors.map fun entry => entry.2.map (fieldSig heads consts)

theorem signature_getElem? {ctors : List (DeclName × List (DeclField Head))} {i : Nat}
    {k : DeclName} {fields : List (DeclField Head)} (entry : ctors[i]? = some (k, fields)) :
    (signature heads consts ctors)[i]? = some (fields.map (fieldSig heads consts)) := by
  rw [signature, List.getElem?_map, entry]
  rfl

theorem exists_of_signature_getElem? {ctors : List (DeclName × List (DeclField Head))} {i : Nat}
    {c : ZFSetInductive.Constructor.{u}} (entry : (signature heads consts ctors)[i]? = some c) :
    ∃ k fields, ctors[i]? = some (k, fields) ∧ c = fields.map (fieldSig heads consts) := by
  rw [signature, List.getElem?_map] at entry
  cases found : ctors[i]? with
  | none =>
    rw [found] at entry
    exact nomatch entry
  | some pair =>
    rw [found] at entry
    exact ⟨pair.1, pair.2, rfl, (Option.some.inj entry).symm⟩

/-- The set a field takes its argument from, the recursive fields from `X`. -/
noncomputable def fieldMembers (X : ZFSet.{u}) : DeclField Head → ZFSet.{u}
  | .recursive => X
  | .closed F => ev heads consts (liftTm F) Fin.elim0

/-- **Arguments fit the fields of a constructor** exactly when there are as many of them and
each lies in the set its field takes its argument from. -/
theorem fits_iff {X : ZFSet.{u}} : ∀ (fs : List (DeclField Head)) (values : List ZFSet.{u}),
    Fits X (fs.map (fieldSig heads consts)) values ↔
      values.length = fs.length ∧
        ∀ j, j < fs.length → values.getD j ∅ ∈ fieldMembers heads consts X (fs.getD j .recursive)
  | [], values => by
    constructor
    · intro fits
      cases fits
      exact ⟨rfl, fun j below => absurd below (Nat.not_lt_zero j)⟩
    · rintro ⟨length, -⟩
      cases values with
      | nil => exact .nil
      | cons _ _ => exact nomatch length
  | f :: fs, [] => by
    constructor
    · intro fits
      cases f <;> cases fits
    · rintro ⟨length, -⟩
      exact nomatch length
  | .recursive :: fs, a :: values => by
    constructor
    · intro fits
      cases fits with
      | recursive member rest =>
        obtain ⟨length, members⟩ := (fits_iff fs values).mp rest
        refine ⟨congrArg Nat.succ length, fun j below => ?_⟩
        cases j with
        | zero => exact member
        | succ j => exact members j (Nat.lt_of_succ_lt_succ below)
    · rintro ⟨length, members⟩
      exact .recursive (members 0 (Nat.succ_pos _)) ((fits_iff fs values).mpr
        ⟨Nat.succ.inj length, fun j below => members (j + 1) (Nat.succ_lt_succ below)⟩)
  | .closed F :: fs, a :: values => by
    constructor
    · intro fits
      cases fits with
      | ofSet member rest =>
        obtain ⟨length, members⟩ := (fits_iff fs values).mp rest
        refine ⟨congrArg Nat.succ length, fun j below => ?_⟩
        cases j with
        | zero => exact member
        | succ j => exact members j (Nat.lt_of_succ_lt_succ below)
    · rintro ⟨length, members⟩
      exact .ofSet (members 0 (Nat.succ_pos _)) ((fits_iff fs values).mpr
        ⟨Nat.succ.inj length, fun j below => members (j + 1) (Nat.succ_lt_succ below)⟩)

/-- Weakening is invisible to the extended environment, for annotations of terms. -/
theorem ev_liftTm_wk {n : Nat} (t : Tm Head n) (ρ : Env.{u} n) (x : ZFSet.{u}) :
    ev heads consts (liftTm (Presentation.rename wk t)) (extend ρ x) =
      ev heads consts (liftTm t) ρ := by
  rw [liftTm_rename, ev_rename_wk]

/-- The value of the type of a field, in any context: the set the field takes its argument
from. -/
theorem ev_fieldType (T : DeclName) (field : DeclField Head) {m : Nat} (ρ : Env.{u} m) :
    ev heads consts (liftTm (Presentation.liftClosed (field.type T) : Tm Head m)) ρ =
      fieldMembers heads consts (consts T) field := by
  rw [liftTm_liftClosed, ev_liftClosed]
  cases field <;> rfl

/-- The value of an entry of a constructor's telescope: the set its field takes its argument
from. -/
theorem ev_ctorEntry (T : DeclName) (fields : List (DeclField Head)) (j : Nat) (ρ : Env.{u} j) :
    ev heads consts (liftTm (ctorEntry T fields j)) ρ =
      fieldMembers heads consts (consts T) (fields.getD j .recursive) :=
  ev_fieldType heads consts T _ ρ

/-- **An environment satisfies the telescope of a constructor** exactly when its values fit
the constructor's fields. -/
theorem sat_ctorTele (T : DeclName) (fields : List (DeclField Head)) (values : List ZFSet.{u})
    (length : values.length = fields.length) :
    Sat heads consts (liftCtx (ctorTele T fields)) (envOf values fields.length) ↔
      Fits (consts T) (fields.map (fieldSig heads consts)) values := by
  rw [ctorTele, sat_ofEntries, fits_iff]
  constructor
  · intro members
    exact ⟨length, fun j below => by
      rw [← ev_ctorEntry heads consts T fields j (envOf values j)]
      exact members j below⟩
  · rintro ⟨-, members⟩ j below
    rw [ev_ctorEntry]
    exact members j below

/-- The value of a term applied to arguments is its value applied to their values. -/
theorem ev_appSpine {n : Nat} (ρ : Env.{u} n) : ∀ (xs : List (Tm Head n)) (f : Tm Head n),
    ev heads consts (liftTm (appSpine f xs)) ρ =
      applyList (ev heads consts (liftTm f) ρ) (xs.map fun x => ev heads consts (liftTm x) ρ)
  | [], _ => rfl
  | x :: xs, f => by
    rw [Presentation.TypedEquality.Normalization.appSpine_cons, ev_appSpine ρ xs (.app f x)]
    rfl

variable {heads consts}

/-- **A constructor's value lies in the value of its declared type**, when the type is read
as the carrier and the constructor as the traced graph of its constructor values. -/
theorem ctor_mem {T k : DeclName} {fields : List (DeclField Head)} {i : Nat}
    {sig : ZFSetInductive.Signature.{u}} (type : consts T = carrier sig)
    (atIndex : sig[i]? = some (fields.map (fieldSig heads consts)))
    (value : consts k = telescopeGraph heads consts (liftCtx (ctorTele T fields)) fun η =>
      constructorValue i (envList η)) :
    consts k ∈ ev heads consts (liftTm (ctorType T fields)) Fin.elim0 := by
  rw [value, ctorType, liftTm_closeType]
  apply telescopeGraph_mem_pisCtx
  intro η sat
  rw [← envOf_envList η] at sat
  have fits := (sat_ctorTele heads consts T fields (envList η) (envList_length η)).mp sat
  show constructorValue i (envList η) ∈ consts T
  rw [type] at fits ⊢
  exact ZFSetInductive.constructor_mem_carrier atIndex fits

/-- **A constructor applied to arguments that fit its fields** gives its constructor value. -/
theorem ctor_apply {T k : DeclName} {fields : List (DeclField Head)} {i : Nat}
    (value : consts k = telescopeGraph heads consts (liftCtx (ctorTele T fields)) fun η =>
      constructorValue i (envList η))
    {args : List ZFSet.{u}} (fits : Fits (consts T) (fields.map (fieldSig heads consts)) args) :
    applyList (consts k) args = constructorValue i args := by
  have length : args.length = fields.length := ((fits_iff heads consts fields args).mp fits).1
  have sat := (sat_ctorTele heads consts T fields args length).mpr fits
  have listed : envList (envOf args fields.length) = args := by
    rw [envList_envOf args fields.length (le_of_eq length.symm), ← length, List.take_length]
  have applied := applyValues_telescopeGraph heads consts (liftCtx (ctorTele T fields))
    (fun η => constructorValue i (envList η)) (envOf args fields.length) sat
  rw [← value, ← applyList_envList, listed] at applied
  exact applied

/-! ## The methods of the recursor -/

variable (heads consts)

/-- The value of the induction hypotheses of a case, with their data substituted. -/
theorem ev_caseHypsSub {n : Nat} (p target : Tm Head n) :
    ∀ {m : Nat} (σ : Sub Head n m) (rs : List (Tm Head n)) (ρ : Env.{u} m),
      ev heads consts (liftTm (caseHypsSub p target σ rs)) ρ =
        arrowsSet
          (rs.map fun r => traceApp (ev heads consts (liftTm (Presentation.subst σ p)) ρ)
            (ev heads consts (liftTm (Presentation.subst σ r)) ρ))
          (traceApp (ev heads consts (liftTm (Presentation.subst σ p)) ρ)
            (ev heads consts (liftTm (Presentation.subst σ target)) ρ))
  | _, _, [], _ => rfl
  | _, σ, r :: rs, ρ => by
    have weak : ∀ (x : ZFSet.{u}) (t : Tm Head n),
        ev heads consts
            (liftTm (Presentation.subst (fun i => Presentation.rename wk (σ i)) t)) (extend ρ x) =
          ev heads consts (liftTm (Presentation.subst σ t)) ρ := fun x t => by
      rw [← rename_subst wk σ t, ev_liftTm_wk]
    show tracePiSet _ (fun x => ev heads consts
        (liftTm (caseHypsSub p target (fun i => Presentation.rename wk (σ i)) rs)) (extend ρ x)) =
      tracePiSet _ fun _ => arrowsSet _ _
    congr 1
    funext x
    rw [ev_caseHypsSub p target (fun i => Presentation.rename wk (σ i)) rs (extend ρ x)]
    simp only [weak]

/-- **The value of the induction hypotheses of a case**: functions of a member of the motive
at each recursive field into the motive at the target. -/
theorem ev_caseHyps {n : Nat} (p : Tm Head n) (rs : List (Tm Head n)) (target : Tm Head n)
    (ρ : Env.{u} n) :
    ev heads consts (liftTm (caseHyps p rs target)) ρ =
      arrowsSet
        (rs.map fun r => traceApp (ev heads consts (liftTm p) ρ) (ev heads consts (liftTm r) ρ))
        (traceApp (ev heads consts (liftTm p) ρ) (ev heads consts (liftTm target) ρ)) := by
  have unfolded := ev_caseHypsSub heads consts p target Presentation.ids rs ρ
  simp only [subst_ids] at unfolded
  exact unfolded

variable {heads consts}

/-- The family of a case with some of its fields bound: at the remaining arguments, functions
of the members of the motive at the recursive fields into the motive at the constructor
applied to all the fields. -/
noncomputable def caseFamily (P : ZFSet.{u} → ZFSet.{u}) (constructor : ZFSet.{u})
    (fs : List ZFSetInductive.Field.{u}) (bound hypotheses : List ZFSet.{u}) :
    List ZFSet.{u} → ZFSet.{u} :=
  fun args =>
    arrowsSet (hypotheses ++ mapRec P fs args) (P (applyList constructor (bound ++ args)))

theorem caseFamily_recursive (P : ZFSet.{u} → ZFSet.{u}) (constructor : ZFSet.{u})
    (fs : List ZFSetInductive.Field.{u}) (bound hypotheses : List ZFSet.{u}) (a : ZFSet.{u})
    (args : List ZFSet.{u}) :
    caseFamily P constructor (.recursive :: fs) bound hypotheses (a :: args) =
      caseFamily P constructor fs (bound ++ [a]) (hypotheses ++ [P a]) args := by
  show arrowsSet (hypotheses ++ (P a :: mapRec P fs args))
      (P (applyList constructor (bound ++ a :: args))) =
    arrowsSet ((hypotheses ++ [P a]) ++ mapRec P fs args)
      (P (applyList constructor ((bound ++ [a]) ++ args)))
  rw [List.append_assoc, List.append_assoc]
  rfl

theorem caseFamily_ofSet (P : ZFSet.{u} → ZFSet.{u}) (constructor A : ZFSet.{u})
    (fs : List ZFSetInductive.Field.{u}) (bound hypotheses : List ZFSet.{u}) (a : ZFSet.{u})
    (args : List ZFSet.{u}) :
    caseFamily P constructor (.ofSet A :: fs) bound hypotheses (a :: args) =
      caseFamily P constructor fs (bound ++ [a]) hypotheses args := by
  show arrowsSet (hypotheses ++ mapRec P fs args) (P (applyList constructor (bound ++ a :: args))) =
    arrowsSet (hypotheses ++ mapRec P fs args) (P (applyList constructor ((bound ++ [a]) ++ args)))
  rw [List.append_assoc]
  rfl

theorem caseFamily_nil (P : ZFSet.{u} → ZFSet.{u}) (constructor : ZFSet.{u})
    (bound hypotheses : List ZFSet.{u}) :
    caseFamily P constructor [] bound hypotheses [] =
      arrowsSet hypotheses (P (applyList constructor bound)) := by
  show arrowsSet (hypotheses ++ mapRec P [] []) (P (applyList constructor (bound ++ []))) = _
  rw [ZFSetInductive.mapRec_nil, List.append_nil, List.append_nil]

theorem curriedSet_recursive (X : ZFSet.{u}) (fs : List ZFSetInductive.Field.{u})
    (family : List ZFSet.{u} → ZFSet.{u}) :
    curriedSet X (.recursive :: fs) family =
      tracePiSet X fun a => curriedSet X fs fun args => family (a :: args) := rfl

theorem curriedSet_ofSet (X A : ZFSet.{u}) (fs : List ZFSetInductive.Field.{u})
    (family : List ZFSet.{u} → ZFSet.{u}) :
    curriedSet X (.ofSet A :: fs) family =
      tracePiSet A fun a => curriedSet X fs fun args => family (a :: args) := rfl

/-- The value of an annotated dependent function type. -/
theorem ev_liftTm_pi {n : Nat} (A : Tm Head n) (B : Tm Head (n + 1)) (ρ : Env.{u} n) :
    ev heads consts (liftTm (.pi A B)) ρ =
      tracePiSet (ev heads consts (liftTm A) ρ) fun x => ev heads consts (liftTm B) (extend ρ x) :=
  rfl

/-- **The value of the type of a method with some of its fields bound**: curried trace
functions over the remaining fields into the family of the case. -/
theorem ev_caseFields (T k : DeclName) (fs : List (DeclField Head)) :
    ∀ {n : Nat} (p : Tm Head n) (xs recs : List (Tm Head n)) (ρ : Env.{u} n),
      ev heads consts (liftTm (caseFields T k fs p xs recs)) ρ =
        curriedSet (consts T) (fs.map (fieldSig heads consts))
          (caseFamily (fun a => traceApp (ev heads consts (liftTm p) ρ) a) (consts k)
            (fs.map (fieldSig heads consts)) (xs.map fun x => ev heads consts (liftTm x) ρ)
            (recs.map fun r =>
              traceApp (ev heads consts (liftTm p) ρ) (ev heads consts (liftTm r) ρ))) := by
  induction fs with
  | nil =>
    intro n p xs recs ρ
    have unfolded : caseFields T k [] p xs recs = caseHyps p recs (appSpine (.const k) xs) := rfl
    rw [unfolded, ev_caseHyps, ev_appSpine]
    exact (caseFamily_nil _ _ _ _).symm
  | cons f fs ih =>
    intro n p xs recs ρ
    cases f with
    | recursive =>
      have unfolded : caseFields T k (.recursive :: fs) p xs recs =
          .pi (.const T) (caseFields T k fs (Presentation.rename wk p)
            (xs.map (Presentation.rename wk) ++ [.var 0])
            (recs.map (Presentation.rename wk) ++ [.var 0])) := rfl
      rw [unfolded, ev_liftTm_pi]
      refine Eq.trans ?_ (curriedSet_recursive _ _ _).symm
      refine congrArg (tracePiSet (consts T)) (funext fun a => ?_)
      rw [ih]
      congr 1
      funext args
      refine Eq.trans ?_ (caseFamily_recursive _ _ (fs.map (fieldSig heads consts)) _ _ a
        args).symm
      simp only [List.map_append, List.map_map, List.map_cons, List.map_nil, Function.comp_def,
        ev_liftTm_wk]
      rfl
    | closed F =>
      have unfolded : caseFields T k (.closed F :: fs) p xs recs =
          .pi (Presentation.liftClosed F) (caseFields T k fs (Presentation.rename wk p)
            (xs.map (Presentation.rename wk) ++ [.var 0])
            (recs.map (Presentation.rename wk))) := rfl
      rw [unfolded, ev_liftTm_pi, liftTm_liftClosed, ev_liftClosed]
      refine Eq.trans ?_ (curriedSet_ofSet _ _ _ _).symm
      refine congrArg (tracePiSet _) (funext fun a => ?_)
      rw [ih]
      congr 1
      funext args
      refine Eq.trans ?_ (caseFamily_ofSet _ _ _ (fs.map (fieldSig heads consts)) _ _ a
        args).symm
      simp only [List.map_append, List.map_map, List.map_cons, List.map_nil, Function.comp_def,
        ev_liftTm_wk]
      rfl

/-- **The value of the type of a method** is the set of the methods for its constructor over
the motive's value, when the constructor applied to fitting arguments gives its constructor
value. -/
theorem ev_caseType {T k : DeclName} {fields : List (DeclField Head)} {i : Nat}
    (apply : ∀ args, Fits (consts T) (fields.map (fieldSig heads consts)) args →
      applyList (consts k) args = constructorValue i args)
    {n : Nat} (p : Tm Head n) (ρ : Env.{u} n) :
    ev heads consts (liftTm (caseType T k fields p)) ρ =
      caseSet (consts T) (fun a => traceApp (ev heads consts (liftTm p) ρ) a) i
        (fields.map (fieldSig heads consts)) := by
  rw [caseType, ev_caseFields T k fields p [] [] ρ]
  refine curriedSet_congr _ fun args fits => ?_
  show arrowsSet ([] ++ mapRec _ _ args) (traceApp _ (applyList (consts k) ([] ++ args))) = _
  rw [List.nil_append, List.nil_append, apply args fits]

/-! ## The recursor of a declaration -/

section Recursor

open Presentation.TypedEquality.Normalization (motiveTy recEntry recTele recBody recType
  recEntry_method recEntry_scrutinee)

variable (heads consts) (T : DeclName) (v : Head)
  (ctors : List (DeclName × List (DeclField Head)))

theorem signature_length : (signature heads consts ctors).length = ctors.length :=
  List.length_map ..

/-- Each constructor of the declaration, applied to arguments that fit its fields, gives its
constructor value. -/
def ConstructorsApply : Prop :=
  ∀ {i : Nat} {k : DeclName} {fields : List (DeclField Head)}, ctors[i]? = some (k, fields) →
    ∀ args, Fits (consts T) (fields.map (fieldSig heads consts)) args →
      applyList (consts k) args = constructorValue i args

/-- **The arguments of the recursor**, as a list of values: a motive, a method for each
constructor over it, and a member of the type. -/
structure RecursorArguments (values : List ZFSet.{u}) : Prop where
  motive : values.getD 0 ∅ ∈ tracePiSet (consts T) fun _ => heads v
  methods : ∀ i c, (signature heads consts ctors)[i]? = some c →
    values.getD (i + 1) ∅ ∈ caseSet (consts T) (fun a => traceApp (values.getD 0 ∅) a) i c
  scrutinee : values.getD (ctors.length + 1) ∅ ∈ consts T

/-- The oldest variable of an environment read from a list has the list's first value. -/
theorem envOf_last (values : List ZFSet.{u}) (i : Nat) :
    envOf values (i + 1) (Fin.last i) = values.getD 0 ∅ := by
  show values.getD (i + 1 - 1 - i) ∅ = _
  rw [Nat.add_sub_cancel, Nat.sub_self]

variable {heads consts T ctors}

/-- **An environment satisfies the telescope of the recursor** exactly when its values are
arguments of the recursor. -/
theorem sat_recTele (apply : ConstructorsApply heads consts T ctors) (values : List ZFSet.{u}) :
    Sat heads consts (liftCtx (recTele T v ctors)) (envOf values (ctors.length + 2)) ↔
      RecursorArguments heads consts T v ctors values := by
  rw [recTele, sat_ofEntries]
  constructor
  · intro members
    refine ⟨members 0 (Nat.succ_pos _), fun i c atIndex => ?_, ?_⟩
    · obtain ⟨k, fields, entry, rfl⟩ := exists_of_signature_getElem? heads consts atIndex
      have below : i < ctors.length := ZFSetInductive.some_index_lt entry
      have member := members (i + 1) (by omega)
      rw [recEntry_method T v ctors entry, ev_caseType (apply entry)] at member
      have motive : ev heads consts (liftTm (.var (Fin.last i) : Tm Head (i + 1)))
          (envOf values (i + 1)) = values.getD 0 ∅ := envOf_last values i
      rw [motive] at member
      exact member
    · have member := members (ctors.length + 1) (Nat.lt_succ_self _)
      rw [recEntry_scrutinee] at member
      exact member
  · intro arguments j below
    cases j with
    | zero => exact arguments.motive
    | succ i =>
      cases entry : ctors[i]? with
      | some pair =>
        obtain ⟨k, fields⟩ := pair
        have motive : ev heads consts (liftTm (.var (Fin.last i) : Tm Head (i + 1)))
            (envOf values (i + 1)) = values.getD 0 ∅ := envOf_last values i
        rw [recEntry_method T v ctors entry, ev_caseType (apply entry), motive]
        exact arguments.methods i _ (signature_getElem? heads consts entry)
      | none =>
        have last : i = ctors.length := by
          have := List.getElem?_eq_none_iff.mp entry
          omega
        subst last
        rw [recEntry_scrutinee]
        exact arguments.scrutinee

variable {rec : DeclName}

/-- **The recursor's value lies in the value of its declared type**, when the type is read as
the carrier, the constructors give their constructor values, and the recursor is the traced
graph of the recursion with the methods. -/
theorem rec_mem (type : consts T = carrier (signature heads consts ctors))
    (apply : ConstructorsApply heads consts T ctors)
    (value : consts rec = telescopeGraph heads consts (liftCtx (recTele T v ctors)) fun η =>
      recFun (sig := signature heads consts ctors)
        (methodStep (methodsOf (envList η) ctors.length)) (η 0)) :
    consts rec ∈ ev heads consts (liftTm (recType T v ctors)) Fin.elim0 := by
  rw [value, recType, liftTm_closeType]
  apply telescopeGraph_mem_pisCtx
  intro η sat
  have arguments : RecursorArguments heads consts T v ctors (envList η) := by
    rw [← envOf_envList η] at sat
    exact (sat_recTele v apply (envList η)).mp sat
  have scrutinee : η 0 = (envList η).getD (ctors.length + 1) ∅ := by
    conv_lhs => rw [← envOf_envList η]
    rfl
  have motive : η (Fin.last (ctors.length + 1)) = (envList η).getD 0 ∅ := by
    conv_lhs => rw [← envOf_envList η]
    exact envOf_last (envList η) (ctors.length + 1)
  show recFun (sig := signature heads consts ctors)
      (methodStep (methodsOf (envList η) ctors.length)) (η 0) ∈
    traceApp (η (Fin.last (ctors.length + 1))) (η 0)
  rw [motive, scrutinee]
  refine recursion_mem (P := fun a => traceApp ((envList η).getD 0 ∅) a)
    (fun i c atIndex => ?_) (by rw [← type]; exact arguments.scrutinee)
  have below : i < ctors.length := by
    have := ZFSetInductive.some_index_lt atIndex
    rwa [signature_length] at this
  rw [methodsOf_getD _ below, ← type]
  exact arguments.methods i c atIndex

/-- **The recursor applied to its arguments** is the recursion with the methods at the
member. -/
theorem rec_apply (apply : ConstructorsApply heads consts T ctors)
    (value : consts rec = telescopeGraph heads consts (liftCtx (recTele T v ctors)) fun η =>
      recFun (sig := signature heads consts ctors)
        (methodStep (methodsOf (envList η) ctors.length)) (η 0))
    {values : List ZFSet.{u}} (length : values.length = ctors.length + 2)
    (arguments : RecursorArguments heads consts T v ctors values) :
    applyList (consts rec) values =
      recFun (sig := signature heads consts ctors)
        (methodStep (methodsOf values ctors.length)) (values.getD (ctors.length + 1) ∅) := by
  have sat := (sat_recTele v apply values).mpr arguments
  have listed : envList (envOf values (ctors.length + 2)) = values := by
    rw [envList_envOf values _ (le_of_eq length.symm), ← length, List.take_length]
  have applied := applyValues_telescopeGraph heads consts (liftCtx (recTele T v ctors))
    (fun η => recFun (sig := signature heads consts ctors)
      (methodStep (methodsOf (envList η) ctors.length)) (η 0))
    (envOf values (ctors.length + 2)) sat
  rw [← value, ← applyList_envList, listed] at applied
  exact applied

/-- **The computation of the recursor at a constructor**: applied to a motive, methods and a
constructor at arguments that fit its fields, the recursor gives the constructor's method
applied to the arguments and to the recursor's values at the recursive arguments. -/
theorem rec_iota (type : consts T = carrier (signature heads consts ctors))
    (apply : ConstructorsApply heads consts T ctors)
    (value : consts rec = telescopeGraph heads consts (liftCtx (recTele T v ctors)) fun η =>
      recFun (sig := signature heads consts ctors)
        (methodStep (methodsOf (envList η) ctors.length)) (η 0))
    {motive : ZFSet.{u}} {methods args : List ZFSet.{u}} {i : Nat} {k : DeclName}
    {fields : List (DeclField Head)} (entry : ctors[i]? = some (k, fields))
    (count : methods.length = ctors.length)
    (motiveTyped : motive ∈ tracePiSet (consts T) fun _ => heads v)
    (methodsTyped : ∀ j c, (signature heads consts ctors)[j]? = some c →
      methods.getD j ∅ ∈ caseSet (consts T) (fun a => traceApp motive a) j c)
    (fits : Fits (consts T) (fields.map (fieldSig heads consts)) args) :
    applyList (consts rec) (motive :: methods ++ [applyList (consts k) args]) =
      applyList (methods.getD i ∅)
        (args ++ mapRec (fun a => applyList (consts rec) (motive :: methods ++ [a]))
          (fields.map (fieldSig heads consts)) args) := by
  have atMember : ∀ t ∈ consts T, applyList (consts rec) (motive :: methods ++ [t]) =
      recFun (sig := signature heads consts ctors) (methodStep methods) t := by
    intro t member
    have length : (motive :: methods ++ [t]).length = ctors.length + 2 := by
      simp [count]
    have last : (motive :: methods ++ [t]).getD (ctors.length + 1) ∅ = t := by
      show (methods ++ [t]).getD ctors.length ∅ = t
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_of_eq count), count,
        Nat.sub_self]
      rfl
    have these : methodsOf (motive :: methods ++ [t]) ctors.length = methods := by
      show (methods ++ [t]).take ctors.length = methods
      exact List.take_left' count
    have arguments : RecursorArguments heads consts T v ctors (motive :: methods ++ [t]) := by
      refine ⟨motiveTyped, fun j c atIndex => ?_, by rw [last]; exact member⟩
      have below : j < methods.length := by
        have := ZFSetInductive.some_index_lt atIndex
        rwa [signature_length, ← count] at this
      have same : (methods ++ [t]).getD j ∅ = methods.getD j ∅ := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_left below,
          ← List.getD_eq_getElem?_getD]
      show (methods ++ [t]).getD j ∅ ∈ caseSet (consts T) (fun a => traceApp motive a) j c
      rw [same]
      exact methodsTyped j c atIndex
    rw [rec_apply v apply value length arguments, last, these]
  have atIndex := signature_getElem? heads consts entry
  have fits' : Fits (carrier (signature heads consts ctors))
      (fields.map (fieldSig heads consts)) args := type ▸ fits
  have member : constructorValue i args ∈ consts T := by
    rw [type]
    exact ZFSetInductive.constructor_mem_carrier atIndex fits'
  rw [apply entry args fits, atMember _ member,
    ZFSetInductive.recFun_constructor (methodStep methods) atIndex fits']
  show applyList (methods.getD i ∅) (args ++ _) = _
  congr 2
  exact ZFSetInductive.mapRec_congr fits fun a ha => (atMember a ha).symm

end Recursor

/-! ## The package of a declaration in the set tower -/

section Package

open Presentation.TypedEquality.Normalization (recEntry recTele recType recEntry_method recApp
  recArgs)

variable (heads consts) (T : DeclName) (v : Head)
  (ctors : List (DeclName × List (DeclField Head))) (rec : DeclName)

/-- **The reading of a declaration in the set tower**: the type is the carrier of its
signature, each constructor is the traced graph of its constructor values, and the recursor is
the traced graph of the recursion with the methods. -/
structure InductiveReading : Prop where
  type : consts T = carrier (signature heads consts ctors)
  ctor : ∀ {i : Nat} {k : DeclName} {fields : List (DeclField Head)},
    ctors[i]? = some (k, fields) →
      consts k = telescopeGraph heads consts (liftCtx (ctorTele T fields)) fun η =>
        constructorValue i (envList η)
  recursor : consts rec = telescopeGraph heads consts (liftCtx (recTele T v ctors)) fun η =>
    recFun (sig := signature heads consts ctors)
      (methodStep (methodsOf (envList η) ctors.length)) (η 0)

variable {heads consts T v ctors rec}

theorem InductiveReading.apply (reading : InductiveReading heads consts T v ctors rec) :
    ConstructorsApply heads consts T ctors :=
  fun entry _ fits => ctor_apply (reading.ctor entry) fits

variable (heads consts)

/-- The values of the variables of an environment, the oldest first. -/
theorem map_finRange_reverse : ∀ {N : Nat} (η : Env.{u} N),
    (List.finRange N).reverse.map η = envList η
  | 0, _ => rfl
  | N + 1, η => by
    rw [List.finRange_succ, List.reverse_cons, List.map_append, ← List.map_reverse,
      List.map_map]
    show (List.finRange N).reverse.map (η ∘ Fin.succ) ++ [η 0] = _
    rw [map_finRange_reverse (η ∘ Fin.succ)]
    rfl

/-- The values of the metavariables of a schema are the values of the environment. -/
theorem ev_metaVars {N : Nat} (η : Env.{u} N) :
    (metaVars N).map (fun t => ev heads consts (liftTm t) η) = envList η := by
  rw [metaVars, List.map_map]
  exact map_finRange_reverse η

/-- The value of an application of the recursor. -/
theorem ev_recApp {n : Nat} (ρ : Env.{u} n) (pre : List (Tm Head n)) (t : Tm Head n) :
    ev heads consts (liftTm (recApp rec pre t)) ρ =
      applyList (consts rec)
        (pre.map (fun x => ev heads consts (liftTm x) ρ) ++ [ev heads consts (liftTm t) ρ]) := by
  rw [recApp, ev_appSpine, List.map_append]
  rfl

/-- The values at the recursive arguments, read from the arguments' values. -/
theorem map_recArgs_values {n : Nat} (g : ZFSet.{u} → ZFSet.{u}) (value : Tm Head n → ZFSet.{u}) :
    ∀ (fs : List (DeclField Head)) (as : List (Tm Head n)),
      (recArgs fs as).map (fun a => g (value a)) =
        mapRec g (fs.map (fieldSig heads consts)) (as.map value)
  | .recursive :: fs, a :: as => by
    show g (value a) :: (recArgs fs as).map (fun a => g (value a)) =
      g (value a) :: mapRec g (fs.map (fieldSig heads consts)) (as.map value)
    rw [map_recArgs_values g value fs as]
  | .closed _ :: fs, _ :: as => map_recArgs_values g value fs as
  | [], _ => rfl
  | .recursive :: _, [] => rfl
  | .closed _ :: _, [] => rfl

/-- The value of an entry of a list of terms that the list has. -/
theorem ev_getD {n : Nat} (ρ : Env.{u} n) (ts : List (Tm Head n)) {j : Nat}
    (below : j < ts.length) (default : Tm Head n) :
    ev heads consts (liftTm (ts.getD j default)) ρ =
      (ts.map fun t => ev heads consts (liftTm t) ρ).getD j ∅ := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem below]
  rfl

/-- **The value of the left side of a computation rule**: the recursor applied to the motive
and the methods, and then to the constructor applied to the fields. -/
theorem ev_iotaLeft (k : DeclName) (c a : Nat) (η : Env.{u} (1 + c + a)) :
    ev heads consts (liftTm (iotaLeft rec k c a)) η =
      applyList (consts rec)
        ((envList η).take (1 + c) ++ [applyList (consts k) ((envList η).drop (1 + c))]) := by
  rw [iotaLeft, ev_recApp, ev_appSpine, List.map_take, List.map_drop, ev_metaVars]
  rfl

/-- **The value of the right side of a computation rule**: the constructor's method applied
to the fields and to the recursor's values at the recursive fields. -/
theorem ev_iotaRight (c : Nat) {i : Nat} (below : i < c) (fields : List (DeclField Head))
    (η : Env.{u} (1 + c + fields.length)) :
    ev heads consts (liftTm (iotaRight rec c i fields)) η =
      applyList (((envList η).take (1 + c)).getD (1 + i) ∅)
        ((envList η).drop (1 + c) ++
          mapRec (fun x => applyList (consts rec) ((envList η).take (1 + c) ++ [x]))
            (fields.map (fieldSig heads consts)) ((envList η).drop (1 + c))) := by
  have inside :
      1 + i < ((metaVars (Head := Head) (1 + c + fields.length)).take (1 + c)).length := by
    rw [List.length_take, length_metaVars]
    omega
  rw [iotaRight, ev_appSpine, ev_getD heads consts η _ inside, List.map_append, List.map_map,
    List.map_take, List.map_drop, ev_metaVars]
  congr 2
  have calls : ((fun x => ev heads consts (liftTm x) η) ∘
      recApp rec ((metaVars (1 + c + fields.length)).take (1 + c))) =
      fun a => (fun x => applyList (consts rec) ((envList η).take (1 + c) ++ [x]))
        (ev heads consts (liftTm a) η) := by
    funext a
    show ev heads consts (liftTm (recApp rec _ a)) η = _
    rw [ev_recApp, List.map_take, ev_metaVars]
  rw [calls]
  have selected := map_recArgs_values heads consts
    (fun x => applyList (consts rec) ((envList η).take (1 + c) ++ [x]))
    (fun a => ev heads consts (liftTm a) η) fields
    ((metaVars (1 + c + fields.length)).drop (1 + c))
  rw [List.map_drop, ev_metaVars] at selected
  exact selected

variable {heads consts}

/-- **A computation rule of the recursor is valid at its typed instances**, when typed
instances of its left side satisfy the telescope of its metavariables. -/
theorem iota_valid (reading : InductiveReading heads consts T v ctors rec)
    (decls : DeclName → Option (CTm Head 0)) {i : Nat} {k : DeclName}
    {fields : List (DeclField Head)} (entry : ctors[i]? = some (k, fields))
    (satisfies : ∀ η : Env.{u} (1 + ctors.length + fields.length),
      TypedInstance heads consts decls (iotaLeft rec k ctors.length fields.length) η →
        Sat heads consts (liftCtx (iotaTele T v ctors fields)) η) :
    SchemaValid heads consts decls (iotaLeft rec k ctors.length fields.length)
      (iotaRight rec ctors.length i fields) := by
  intro η typed
  have below : i < ctors.length := ZFSetInductive.some_index_lt entry
  have sat := satisfies η typed
  rw [← envOf_envList η, iotaTele, sat_ofEntries] at sat
  have length : (envList η).length = 1 + ctors.length + fields.length := envList_length η
  rw [elabLeft_firstOrder decls (firstOrder_iotaLeft rec k _ _)]
  have right : elabRight decls (iotaLeft rec k ctors.length fields.length)
      (iotaRight rec ctors.length i fields) = liftTm (iotaRight rec ctors.length i fields) :=
    elab_lamFree decls (lamFree_iotaRight rec _ i fields) _ _ _
  rw [right]
  show ev heads consts (liftTm (iotaLeft rec k ctors.length fields.length)) η = _
  rw [ev_iotaLeft, ev_iotaRight heads consts _ below]
  generalize envList η = values at sat length
  cases values with
  | nil => exact absurd length (by simp; omega)
  | cons motive rest =>
    have restLength : rest.length = ctors.length + fields.length := by
      simp only [List.length_cons] at length
      omega
    have taken : (motive :: rest).take (1 + ctors.length) = motive :: rest.take ctors.length := by
      rw [Nat.add_comm, List.take_succ_cons]
    have dropped : (motive :: rest).drop (1 + ctors.length) = rest.drop ctors.length := by
      rw [Nat.add_comm, List.drop_succ_cons]
    have count : (rest.take ctors.length).length = ctors.length := by
      rw [List.length_take, restLength]
      omega
    rw [taken, dropped]
    have motiveTyped : motive ∈ tracePiSet (consts T) fun _ => heads v := by
      have member := sat 0 (by omega)
      have unfolded : iotaEntry T v ctors fields 0 = recEntry T v ctors 0 :=
        if_pos (Nat.zero_le _)
      rw [unfolded] at member
      exact member
    have methodsTyped : ∀ j c, (signature heads consts ctors)[j]? = some c →
        (rest.take ctors.length).getD j ∅ ∈
          caseSet (consts T) (fun a => traceApp motive a) j c := by
      intro j c atIndex
      obtain ⟨kj, fieldsj, entryj, rfl⟩ := exists_of_signature_getElem? heads consts atIndex
      have belowj : j < ctors.length := ZFSetInductive.some_index_lt entryj
      have member := sat (j + 1) (by omega)
      have unfolded : iotaEntry T v ctors fields (j + 1) = recEntry T v ctors (j + 1) :=
        if_pos (Nat.succ_le_of_lt belowj)
      have first : ev heads consts (liftTm (.var (Fin.last j) : Tm Head (j + 1)))
          (envOf (motive :: rest) (j + 1)) = motive := envOf_last (motive :: rest) j
      rw [unfolded, recEntry_method T v ctors entryj, ev_caseType (reading.apply entryj),
        first] at member
      have same : (rest.take ctors.length).getD j ∅ = (motive :: rest).getD (j + 1) ∅ := by
        rw [List.getD_cons_succ, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          List.getElem?_take_of_lt belowj]
      rw [same]
      exact member
    have fits : Fits (consts T) (fields.map (fieldSig heads consts)) (rest.drop ctors.length) := by
      refine (fits_iff heads consts fields _).mpr ⟨by rw [List.length_drop, restLength]; omega,
        fun j belowj => ?_⟩
      have member := sat (ctors.length + 1 + j) (by omega)
      have unfolded : iotaEntry T v ctors fields (ctors.length + 1 + j) =
          Presentation.liftClosed ((fields.getD j .recursive).type T) := by
        rw [iotaEntry, if_neg (by omega), Nat.add_sub_cancel_left]
      rw [unfolded, ev_fieldType] at member
      have same : (rest.drop ctors.length).getD j ∅ =
          (motive :: rest).getD (ctors.length + 1 + j) ∅ := by
        rw [show ctors.length + 1 + j = (ctors.length + j) + 1 by omega, List.getD_cons_succ,
          List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop]
      rw [same]
      exact member
    have method : (motive :: rest.take ctors.length).getD (1 + i) ∅ =
        (rest.take ctors.length).getD i ∅ := by
      rw [Nat.add_comm, List.getD_cons_succ]
    rw [method]
    exact rec_iota v reading.type reading.apply reading.recursor entry count motiveTyped
      methodsTyped fits

/-- **The package of a simple inductive declaration has a set model** at every reading of the
declaration in which the type's set is a member of its universe: the constructors and the
recursor lie in their declared types, and the computation rules of the recursor hold at their
typed instances. The closed field types have no abstraction, and typed instances of the left
sides satisfy the telescopes of their metavariables. -/
theorem inductive_setModel {w : Head} (target : Rules Head)
    (universes : ZFSetReplayInterpretation.UniverseModel target heads)
    (headEq : ∀ {h h' : Head}, target.headEq h h' → heads h = heads h')
    (free : FieldsLamFree ctors) (reading : InductiveReading heads consts T v ctors rec)
    (typeMember : consts T ∈ heads w)
    (satisfies : ∀ {i : Nat} {k : DeclName} {fields : List (DeclField Head)},
      ctors[i]? = some (k, fields) → ∀ η : Env.{u} (1 + ctors.length + fields.length),
        TypedInstance heads consts (elabDeclarations (inductiveDecls T w ctors rec v))
            (iotaLeft rec k ctors.length fields.length) η →
          Sat heads consts (liftCtx (iotaTele T v ctors fields)) η) :
    SetModel heads consts (inductiveChurch target T w ctors rec v) := by
  show SetModel heads consts (ChurchRules.ofSchemas (inductiveRules target T w ctors rec v)
    (iotaSchema rec ctors) (iota_presents rec ctors))
  refine SetModel.ofSchemas (present := iota_presents rec ctors) { universes with } headEq
    (fun {c Ty} declared => ?_) ?_
  · rcases inductiveChurch_constantType target free declared with
      ⟨rfl, rfl⟩ | ⟨i, fields, entry, rfl⟩ | ⟨rfl, rfl⟩
    · exact typeMember
    · exact ctor_mem reading.type (signature_getElem? heads consts entry) (reading.ctor entry)
    · exact rec_mem v reading.type reading.apply reading.recursor
  · intro arity L R rule
    obtain ⟨i, name, fields, entry, same⟩ := rule
    cases same
    exact iota_valid reading _ entry (satisfies entry)

/-- **The same for every declaration with distinct names**: the knowledge of each left side is
the telescope of its metavariables (`iotaLeft_known`). -/
theorem inductive_setModel_distinct {w : Head} (target : Rules Head)
    (universes : ZFSetReplayInterpretation.UniverseModel target heads)
    (headEq : ∀ {h h' : Head}, target.headEq h h' → heads h = heads h')
    (distinct : DistinctNames T ctors rec) (free : FieldsLamFree ctors)
    (reading : InductiveReading heads consts T v ctors rec) (typeMember : consts T ∈ heads w) :
    SetModel heads consts (inductiveChurch target T w ctors rec v) :=
  inductive_setModel target universes headEq free reading typeMember
    fun entry _ typed => typed.sat (iotaLeft_known distinct free entry)

end Package

/-! ## A reading over a base assignment -/

section Existence

open Presentation.TypedEquality.Normalization (recEntry recTele recEntry_method)

variable (heads : Head → ZFSet.{u}) (base : DeclName → ZFSet.{u}) (T : DeclName) (v : Head)
  (ctors : List (DeclName × List (DeclField Head))) (rec : DeclName)

/-- An assignment agrees with the base outside the names of the declaration. -/
def AgreesOutside (consts : DeclName → ZFSet.{u}) : Prop :=
  ∀ c, c ≠ T → c ∉ ctors.map (·.1) → c ≠ rec → consts c = base c

/-- **A declaration is fresh over a base assignment**: its names are distinct, and its closed
field types have the same sets at every assignment that agrees with the base outside its
names. -/
structure FreshDeclaration : Prop extends DistinctNames T ctors rec where
  fields : ∀ consts, AgreesOutside base T ctors rec consts → ∀ entry ∈ ctors,
    ∀ F, (.closed F : DeclField Head) ∈ entry.2 →
      ev heads consts (liftTm F) Fin.elim0 = ev heads base (liftTm F) Fin.elim0

/-- The constructors read over an assignment: each is the traced graph of its constructor
values. -/
noncomputable def withCtors (consts : DeclName → ZFSet.{u}) :
    List (DeclName × List (DeclField Head)) → Nat → DeclName → ZFSet.{u}
  | [], _ => consts
  | (k, fields) :: rest, i =>
      Function.update (withCtors consts rest (i + 1)) k
        (telescopeGraph heads consts (liftCtx (ctorTele T fields)) fun η =>
          constructorValue i (envList η))

/-- **The assignment that reads a declaration over a base**: the type is the carrier, the
constructors are their graphs, and the recursor is the graph of the recursion. -/
noncomputable def inductiveConsts : DeclName → ZFSet.{u} :=
  Function.update
    (withCtors heads T (Function.update base T (carrier (signature heads base ctors))) ctors 0)
    rec
    (telescopeGraph heads
      (withCtors heads T (Function.update base T (carrier (signature heads base ctors))) ctors 0)
      (liftCtx (recTele T v ctors)) fun η =>
        recFun (sig := signature heads
            (withCtors heads T (Function.update base T (carrier (signature heads base ctors)))
              ctors 0) ctors)
          (methodStep (methodsOf (envList η) ctors.length)) (η 0))

variable {heads base T v ctors rec}

theorem withCtors_of_not_mem (consts : DeclName → ZFSet.{u}) :
    ∀ (rest : List (DeclName × List (DeclField Head))) (i : Nat) {name : DeclName},
      name ∉ rest.map (·.1) → withCtors heads T consts rest i name = consts name
  | [], _, _, _ => rfl
  | (k, fields) :: rest, i, name, absent => by
    have other : name ≠ k := fun same => absent (by rw [same]; exact List.mem_cons_self)
    show Function.update (withCtors heads T consts rest (i + 1)) k _ name = _
    rw [Function.update_of_ne other]
    exact withCtors_of_not_mem consts rest (i + 1)
      fun member => absent (List.mem_cons_of_mem _ member)

theorem withCtors_at (consts : DeclName → ZFSet.{u}) :
    ∀ (rest : List (DeclName × List (DeclField Head))) (i : Nat) {j : Nat} {k : DeclName}
      {fields : List (DeclField Head)}, (rest.map (·.1)).Nodup → rest[j]? = some (k, fields) →
        withCtors heads T consts rest i k =
          telescopeGraph heads consts (liftCtx (ctorTele T fields)) fun η =>
            constructorValue (i + j) (envList η)
  | (k', fields') :: rest, i, 0, k, fields, _, entry => by
    obtain ⟨rfl, rfl⟩ : k' = k ∧ fields' = fields := by simpa using entry
    show Function.update (withCtors heads T consts rest (i + 1)) k' _ k' = _
    rw [Function.update_self]
    rfl
  | (k', fields') :: rest, i, j + 1, k, fields, nodup, entry => by
    have entry' : rest[j]? = some (k, fields) := by simpa using entry
    have present : k ∈ rest.map (·.1) :=
      List.mem_map.mpr ⟨(k, fields), List.mem_of_getElem? entry', rfl⟩
    have nodup' := List.nodup_cons.mp nodup
    have other : k ≠ k' := fun same => nodup'.1 (same ▸ present)
    show Function.update (withCtors heads T consts rest (i + 1)) k' _ k = _
    rw [Function.update_of_ne other, withCtors_at consts rest (i + 1) nodup'.2 entry',
      show i + 1 + j = i + (j + 1) by omega]

/-- The field sets are the base's at every assignment that agrees with it outside the names
of a fresh declaration. -/
theorem signature_of_agrees (fresh : FreshDeclaration heads base T ctors rec)
    {consts : DeclName → ZFSet.{u}} (agrees : AgreesOutside base T ctors rec consts) :
    signature heads consts ctors = signature heads base ctors := by
  refine List.map_congr_left fun entry member => ?_
  refine List.map_congr_left fun field memberField => ?_
  cases field with
  | recursive => rfl
  | closed F =>
    show ZFSetInductive.Field.ofSet _ = ZFSetInductive.Field.ofSet _
    rw [fresh.fields consts agrees entry member F memberField]

theorem fieldMembers_of_agrees (fresh : FreshDeclaration heads base T ctors rec)
    {consts : DeclName → ZFSet.{u}} (agrees : AgreesOutside base T ctors rec consts)
    {entry : DeclName × List (DeclField Head)} (member : entry ∈ ctors) (X : ZFSet.{u})
    {field : DeclField Head} (memberField : field ∈ entry.2) :
    fieldMembers heads consts X field = fieldMembers heads base X field := by
  cases field with
  | recursive => rfl
  | closed F => exact fresh.fields consts agrees entry member F memberField

/-- A traced graph over a telescope given by its entries reads the values of the entries. -/
theorem telescopeGraph_ofEntries_congr {consts consts' : DeclName → ZFSet.{u}}
    (entry : (j : Nat) → Tm Head j) :
    ∀ (n : Nat) (body : Env.{u} n → ZFSet.{u}),
      (∀ j, j < n → ∀ ρ : Env.{u} j,
        ev heads consts (liftTm (entry j)) ρ = ev heads consts' (liftTm (entry j)) ρ) →
      telescopeGraph heads consts (liftCtx (ofEntries entry n)) body =
        telescopeGraph heads consts' (liftCtx (ofEntries entry n)) body
  | 0, _, _ => rfl
  | n + 1, body, same => by
    show telescopeGraph heads consts (liftCtx (ofEntries entry n)) (fun η =>
        traceLam (graph (ev heads consts (liftTm (entry n)) η) fun x => body (extend η x))) =
      telescopeGraph heads consts' (liftCtx (ofEntries entry n)) (fun η =>
        traceLam (graph (ev heads consts' (liftTm (entry n)) η) fun x => body (extend η x)))
    rw [telescopeGraph_ofEntries_congr entry n _ fun j below => same j (Nat.lt_succ_of_lt below)]
    congr 1
    funext η
    rw [same n (Nat.lt_succ_self n) η]

/-- The field sets of one constructor are the base's at every assignment that agrees with it
outside the names of a fresh declaration. -/
theorem fieldSigs_of_agrees (fresh : FreshDeclaration heads base T ctors rec)
    {consts : DeclName → ZFSet.{u}} (agrees : AgreesOutside base T ctors rec consts)
    {entry : DeclName × List (DeclField Head)} (member : entry ∈ ctors) :
    entry.2.map (fieldSig heads consts) = entry.2.map (fieldSig heads base) := by
  refine List.map_congr_left fun field memberField => ?_
  cases field with
  | recursive => rfl
  | closed F =>
    show ZFSetInductive.Field.ofSet _ = ZFSetInductive.Field.ofSet _
    rw [fresh.fields consts agrees entry member F memberField]

/-- The value of an entry of a constructor's telescope, at an assignment that agrees with the
base outside the names of a fresh declaration. -/
theorem ev_ctorEntry_of_agrees (fresh : FreshDeclaration heads base T ctors rec)
    {consts : DeclName → ZFSet.{u}} (agrees : AgreesOutside base T ctors rec consts)
    {entry : DeclName × List (DeclField Head)} (member : entry ∈ ctors) (j : Nat)
    (ρ : Env.{u} j) :
    ev heads consts (liftTm (ctorEntry T entry.2 j)) ρ =
      fieldMembers heads base (consts T) (entry.2.getD j .recursive) := by
  rw [ev_ctorEntry]
  cases found : entry.2.getD j .recursive with
  | recursive => rfl
  | closed F => exact fresh.fields consts agrees entry member F (closed_mem_of_getD found)

/-- **The assignment that reads a fresh declaration over a base is a reading of it.** -/
theorem inductiveConsts_reading (fresh : FreshDeclaration heads base T ctors rec) :
    InductiveReading heads (inductiveConsts heads base T v ctors rec) T v ctors rec := by
  -- The three stages: the type, the constructors, the recursor.
  generalize typedEq : Function.update base T (carrier (signature heads base ctors)) = typed
  generalize builtEq : withCtors heads T typed ctors 0 = built
  have finalEq : inductiveConsts heads base T v ctors rec =
      Function.update built rec (telescopeGraph heads built (liftCtx (recTele T v ctors))
        fun η => recFun (sig := signature heads built ctors)
          (methodStep (methodsOf (envList η) ctors.length)) (η 0)) := by
    rw [inductiveConsts, typedEq, builtEq]
  generalize inductiveConsts heads base T v ctors rec = final at finalEq
  have typedAgrees : AgreesOutside base T ctors rec typed := fun c notT _ _ => by
    rw [← typedEq, Function.update_of_ne notT]
  have builtAgrees : AgreesOutside base T ctors rec built := fun c notT notCtor notRec => by
    rw [← builtEq, withCtors_of_not_mem typed ctors 0 notCtor]
    exact typedAgrees c notT notCtor notRec
  have finalAgrees : AgreesOutside base T ctors rec final := fun c notT notCtor notRec => by
    rw [finalEq, Function.update_of_ne notRec]
    exact builtAgrees c notT notCtor notRec
  have typedT : typed T = carrier (signature heads base ctors) := by
    rw [← typedEq, Function.update_self]
  have builtT : built T = typed T := by
    rw [← builtEq, withCtors_of_not_mem typed ctors 0 fresh.typeNotCtor]
  have finalT : final T = built T := by
    rw [finalEq, Function.update_of_ne fresh.recNotType.symm]
  have finalCtor : ∀ {i : Nat} {k : DeclName} {fields : List (DeclField Head)},
      ctors[i]? = some (k, fields) → final k = built k := by
    intro i k fields entry
    have present : k ∈ ctors.map (·.1) :=
      List.mem_map.mpr ⟨(k, fields), List.mem_of_getElem? entry, rfl⟩
    have other : k ≠ rec := fun same => fresh.recNotCtor (same ▸ present)
    rw [finalEq, Function.update_of_ne other]
  refine ⟨?_, fun {i k fields} entry => ?_, ?_⟩
  · rw [finalT, builtT, typedT, signature_of_agrees fresh finalAgrees]
  · have member : (k, fields) ∈ ctors := List.mem_of_getElem? entry
    rw [finalCtor entry, ← builtEq, withCtors_at typed ctors 0 fresh.ctorsNodup entry,
      Nat.zero_add]
    refine telescopeGraph_ofEntries_congr (ctorEntry T fields) fields.length _ fun j _ ρ => ?_
    rw [ev_ctorEntry_of_agrees fresh typedAgrees member j ρ,
      ev_ctorEntry_of_agrees fresh finalAgrees member j ρ, finalT, builtT]
  · have signatures : signature heads built ctors = signature heads final ctors := by
      rw [signature_of_agrees fresh builtAgrees, signature_of_agrees fresh finalAgrees]
    have recValue : final rec = telescopeGraph heads built (liftCtx (recTele T v ctors))
        fun η => recFun (sig := signature heads built ctors)
          (methodStep (methodsOf (envList η) ctors.length)) (η 0) := by
      rw [finalEq, Function.update_self]
    rw [recValue, signatures]
    refine telescopeGraph_ofEntries_congr (recEntry T v ctors) (ctors.length + 2) _
      fun j _ ρ => ?_
    cases j with
    | zero =>
      show tracePiSet (built T) (fun _ => heads v) = tracePiSet (final T) fun _ => heads v
      rw [finalT]
    | succ j =>
      cases entry : ctors[j]? with
      | none =>
        have unfolded : recEntry T v ctors (j + 1) = .const T := by simp [recEntry, entry]
        rw [unfolded]
        exact finalT.symm
      | some pair =>
        obtain ⟨k, fields⟩ := pair
        have member : (k, fields) ∈ ctors := List.mem_of_getElem? entry
        rw [recEntry_method T v ctors entry, caseType, ev_caseFields, ev_caseFields,
          fieldSigs_of_agrees fresh builtAgrees member,
          fieldSigs_of_agrees fresh finalAgrees member, finalCtor entry, finalT]
        rfl

variable (heads base T v ctors rec) in
/-- The assignment that reads a declaration agrees with the base outside the declaration's
names. -/
theorem inductiveConsts_agrees :
    AgreesOutside base T ctors rec (inductiveConsts heads base T v ctors rec) :=
  fun c notT notCtor notRec => by
    rw [inductiveConsts, Function.update_of_ne notRec, withCtors_of_not_mem _ ctors 0 notCtor,
      Function.update_of_ne notT]

/-- The type's set is a member of a closed universe that holds the natural numbers and the
sets of the closed field types. -/
theorem inductiveConsts_type_mem (fresh : FreshDeclaration heads base T ctors rec) {U : ZFSet.{u}}
    (closed : ZFSetUniverseClosure.Closed U) (omega : ZFSet.omega ∈ U)
    (fieldSets : ∀ entry ∈ ctors, ∀ F, (.closed F : DeclField Head) ∈ entry.2 →
      ev heads base (liftTm F) Fin.elim0 ∈ U) :
    inductiveConsts heads base T v ctors rec T ∈ U := by
  rw [(inductiveConsts_reading (v := v) fresh).type,
    signature_of_agrees fresh (inductiveConsts_agrees heads base T v ctors rec)]
  refine ZFSetInductive.carrier_mem closed omega fun c member A field => ?_
  obtain ⟨entry, memberEntry, rfl⟩ := List.mem_map.mp member
  obtain ⟨declared, memberField, same⟩ := List.mem_map.mp field
  cases declared with
  | recursive => exact nomatch same
  | closed F =>
    obtain rfl : ev heads base (liftTm F) Fin.elim0 = A := by
      injection same
    exact fieldSets entry memberEntry F memberField

/-- **A reading reads only the declaration's names and field types**: an assignment with the
same sets at the type, the constructors and the recursor, and the same sets of the closed field
types, is a reading too. -/
theorem InductiveReading.of_agrees {consts consts' : DeclName → ZFSet.{u}}
    (reading : InductiveReading heads consts T v ctors rec) (type : consts' T = consts T)
    (ctor : ∀ entry ∈ ctors, consts' entry.1 = consts entry.1) (recursor : consts' rec = consts rec)
    (fields : ∀ entry ∈ ctors, ∀ F, (.closed F : DeclField Head) ∈ entry.2 →
      ev heads consts' (liftTm F) Fin.elim0 = ev heads consts (liftTm F) Fin.elim0) :
    InductiveReading heads consts' T v ctors rec := by
  have fieldSigs : ∀ entry ∈ ctors,
      entry.2.map (fieldSig heads consts') = entry.2.map (fieldSig heads consts) := by
    intro entry member
    refine List.map_congr_left fun field memberField => ?_
    cases field with
    | recursive => rfl
    | closed F =>
      show ZFSetInductive.Field.ofSet _ = ZFSetInductive.Field.ofSet _
      rw [fields entry member F memberField]
  have signatures : signature heads consts' ctors = signature heads consts ctors :=
    List.map_congr_left fun entry member => fieldSigs entry member
  have entries : ∀ entry ∈ ctors, ∀ (j : Nat) (ρ : Env.{u} j),
      ev heads consts (liftTm (ctorEntry T entry.2 j)) ρ =
        ev heads consts' (liftTm (ctorEntry T entry.2 j)) ρ := by
    intro entry member j ρ
    rw [ev_ctorEntry, ev_ctorEntry]
    cases found : entry.2.getD j .recursive with
    | recursive => exact type.symm
    | closed F => exact (fields entry member F (closed_mem_of_getD found)).symm
  refine ⟨?_, fun {i k fs} entry => ?_, ?_⟩
  · rw [type, reading.type, signatures]
  · have member : (k, fs) ∈ ctors := List.mem_of_getElem? entry
    rw [ctor (k, fs) member, reading.ctor entry]
    exact telescopeGraph_ofEntries_congr (ctorEntry T fs) fs.length _
      fun j _ ρ => entries (k, fs) member j ρ
  · rw [recursor, reading.recursor, signatures]
    refine telescopeGraph_ofEntries_congr (recEntry T v ctors) (ctors.length + 2) _
      fun j _ ρ => ?_
    cases j with
    | zero =>
      show tracePiSet (consts T) (fun _ => heads v) = tracePiSet (consts' T) fun _ => heads v
      rw [type]
    | succ j =>
      cases entry : ctors[j]? with
      | none =>
        have unfolded : recEntry T v ctors (j + 1) = .const T := by simp [recEntry, entry]
        rw [unfolded]
        exact type.symm
      | some pair =>
        obtain ⟨k, fs⟩ := pair
        have member : (k, fs) ∈ ctors := List.mem_of_getElem? entry
        rw [recEntry_method T v ctors entry, caseType, ev_caseFields, ev_caseFields,
          fieldSigs (k, fs) member, ctor (k, fs) member, type]
        rfl

/-- **A package extended by a simple inductive declaration has a set model at every assignment
that reads the declaration and at which the base package has one.** -/
theorem extension_setModel_at {R : Rules Head} (B : ChurchRules R) {w : Head}
    {consts : DeclName → ZFSet.{u}} (baseModel : SetModel heads consts B)
    (distinct : DistinctNames T ctors rec) (free : FieldsLamFree ctors)
    (reading : InductiveReading heads consts T v ctors rec) (typeMember : consts T ∈ heads w) :
    SetModel heads consts (B.sum (inductiveChurch R T w ctors rec v)) :=
  SetModel.sum baseModel
    (inductive_setModel_distinct R baseModel.universes baseModel.headEq distinct free reading
      typeMember)

/-- **A package extended by a fresh simple inductive declaration has a set model.** The base
package has a set model at every assignment that agrees with the base assignment outside the
declaration's names; the declaration's closed field types have no abstraction and their sets
lie in the universe of the type, which is closed and holds the natural numbers. The model is
at the assignment that reads the declaration over the base. -/
theorem extension_setModel {R : Rules Head} (B : ChurchRules R) {w : Head}
    (baseModel : ∀ consts, AgreesOutside base T ctors rec consts → SetModel heads consts B)
    (fresh : FreshDeclaration heads base T ctors rec) (free : FieldsLamFree ctors)
    (closed : ZFSetUniverseClosure.Closed (heads w)) (omega : ZFSet.omega ∈ heads w)
    (fieldSets : ∀ entry ∈ ctors, ∀ F, (.closed F : DeclField Head) ∈ entry.2 →
      ev heads base (liftTm F) Fin.elim0 ∈ heads w) :
    SetModel heads (inductiveConsts heads base T v ctors rec)
      (B.sum (inductiveChurch R T w ctors rec v)) :=
  extension_setModel_at B (baseModel _ (inductiveConsts_agrees heads base T v ctors rec))
    fresh.toDistinctNames free (inductiveConsts_reading fresh)
    (inductiveConsts_type_mem fresh closed omega fieldSets)

end Existence

end Reading

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
