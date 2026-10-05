import Mettapedia.Logic.HOL.Embedding.ZFSetInductive
import Mettapedia.Logic.HOL.Embedding.ZFSetTraceProducts

/-!
# Carriers of inductive signatures with function fields

A field is recursive, one fixed set, or the functions from a fixed set into the
carrier. A constructor is its list of fields, and the value of constructor `i` is the
constructor value of simple signatures whose tag is the numeral `i`.
The carrier is the least set of those values at fitting arguments. It is
collected as the image of path codes: a code is a function from finite lists of
moves to node labels. The union of the finite iterates of one step is not that
carrier once a function field ranges over an infinite set.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.Embedding.ZFSetInductiveFunctions

open ZFSetHenkinInterpretation ZFSetUniverseClosure ZFSetDependentProducts
open ZFSetIndexedClosure ZFSetList ZFSetTraceProducts
open ZFSetInductive (constructorValue tuple tuple_mem constructorValue_tag
  constructorValue_args constructorValue_injective constructorValue_ne_empty numeral_mem_of_omega)
open Mettapedia.SetTheory.ZFSetOrderedPair (first second first_pair second_pair)
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
  (numeral numeral_injective numeral_mem_omega numeral_succ mem_omega_iff range_numeral
    natOf numeral_natOf natOf_numeral finiteSets omega_not_mem_finiteSets finiteRankStage_mem)
open scoped ZFSet Ordinal

universe u

/-! ## Signatures -/

/-- A field is recursive, one fixed set, or the functions from one fixed set into
the carrier. -/
inductive Field : Type (u + 1) where
  | recursive : Field
  | ofSet : ZFSet.{u} → Field
  | ofFun : ZFSet.{u} → Field

abbrev Constructor := List Field

abbrev Signature := List Constructor

/-- Arguments fit a constructor relative to a set of recursive values. A function
argument fits when it lies in the trace function set with that constant fibre. -/
inductive Fits (X : ZFSet.{u}) : List Field.{u} → List ZFSet.{u} → Prop where
  | nil : Fits X [] []
  | recursive {fs : List Field.{u}} {args : List ZFSet.{u}} {a : ZFSet.{u}} :
      a ∈ X → Fits X fs args → Fits X (Field.recursive :: fs) (a :: args)
  | ofSet {A : ZFSet.{u}} {fs : List Field.{u}} {args : List ZFSet.{u}} {a : ZFSet.{u}} :
      a ∈ A → Fits X fs args → Fits X (Field.ofSet A :: fs) (a :: args)
  | ofFun {A : ZFSet.{u}} {fs : List Field.{u}} {args : List ZFSet.{u}} {f : ZFSet.{u}} :
      f ∈ tracePiSet A (fun _ => X) → Fits X fs args →
        Fits X (Field.ofFun A :: fs) (f :: args)

/-- Fitting with a predicate in place of the set of recursive values. A function
argument is the trace of the graph of its values, and the predicate holds at
each value. -/
inductive FitsPred (P : ZFSet.{u} → Prop) : List Field.{u} → List ZFSet.{u} → Prop where
  | nil : FitsPred P [] []
  | recursive {fs : List Field.{u}} {args : List ZFSet.{u}} {a : ZFSet.{u}} :
      P a → FitsPred P fs args → FitsPred P (Field.recursive :: fs) (a :: args)
  | ofSet {A : ZFSet.{u}} {fs : List Field.{u}} {args : List ZFSet.{u}} {a : ZFSet.{u}} :
      a ∈ A → FitsPred P fs args → FitsPred P (Field.ofSet A :: fs) (a :: args)
  | ofFun {A : ZFSet.{u}} {fs : List Field.{u}} {args : List ZFSet.{u}} {f : ZFSet.{u}} :
      f = traceLam (graph A (fun a => traceApp f a)) →
        (∀ a, a ∈ A → P (traceApp f a)) → FitsPred P fs args →
          FitsPred P (Field.ofFun A :: fs) (f :: args)

theorem mem_tracePiSet_of_total {A f X : ZFSet.{u}}
    (total : f = traceLam (graph A (fun a => traceApp f a)))
    (values : ∀ a, a ∈ A → traceApp f a ∈ X) :
    f ∈ tracePiSet A (fun _ => X) := by
  have hg : graph A (fun a => traceApp f a) ∈ piSet A (fun _ => X) :=
    graph_mem_piSet values
  exact total ▸ mem_tracePiSet.mpr ⟨graph A (fun a => traceApp f a), hg, rfl⟩

theorem total_of_mem_tracePiSet {A X f : ZFSet.{u}}
    (hf : f ∈ tracePiSet A (fun _ => X)) :
    f = traceLam (graph A (fun a => traceApp f a)) ∧ ∀ a, a ∈ A → traceApp f a ∈ X := by
  refine ⟨?_, fun a ha => traceApp_mem ⟨f, hf⟩ ⟨a, ha⟩⟩
  have same : (⟨f, hf⟩ : Elements (tracePiSet A (fun _ => X))) =
      traceEncode (traceValue ⟨f, hf⟩) := (trace_eta _).symm
  have hfEq : f = (traceEncode (traceValue ⟨f, hf⟩)).1 := congrArg Subtype.val same
  have body : (traceEncode (traceValue ⟨f, hf⟩)).1 =
      traceLam (graph A (extendFunction (traceValue ⟨f, hf⟩))) := rfl
  rw [hfEq, body]
  apply congrArg traceLam
  apply graph_congr
  intro a ha
  rw [traceApp_graph_beta (extendFunction (traceValue ⟨f, hf⟩)) ha]

theorem fits_of_fitsPred {X : ZFSet.{u}} {fs : List Field.{u}} {args : List ZFSet.{u}}
    (fitting : FitsPred (fun a => a ∈ X) fs args) : Fits X fs args := by
  induction fitting with
  | nil => exact Fits.nil
  | recursive member _ ih => exact Fits.recursive member ih
  | ofSet member _ ih => exact Fits.ofSet member ih
  | ofFun total values _ ih =>
      exact Fits.ofFun (mem_tracePiSet_of_total total values) ih

theorem mem_of_get? {α : Type*} {l : List α} {i : Nat} {a : α}
    (present : l[i]? = some a) : a ∈ l :=
  List.mem_of_getElem? present

/-! ## Elements generated by the constructors -/

mutual

inductive InCarrier (sig : Signature.{u}) : ZFSet.{u} → Prop where
  | intro {i : Nat} {c : Constructor} {args : List ZFSet.{u}}
      (atIndex : sig[i]? = some c) (fitting : Deriv sig c args) :
      InCarrier sig (constructorValue (numeral i) args)

inductive Deriv (sig : Signature.{u}) : List Field.{u} → List ZFSet.{u} → Prop where
  | nil : Deriv sig [] []
  | recursive {fs : List Field.{u}} {args : List ZFSet.{u}} {a : ZFSet.{u}}
      (member : InCarrier sig a) (rest : Deriv sig fs args) :
      Deriv sig (Field.recursive :: fs) (a :: args)
  | ofSet {A : ZFSet.{u}} {fs : List Field.{u}} {args : List ZFSet.{u}} {a : ZFSet.{u}}
      (member : a ∈ A) (rest : Deriv sig fs args) :
      Deriv sig (Field.ofSet A :: fs) (a :: args)
  | ofFun {A : ZFSet.{u}} {fs : List Field.{u}} {args : List ZFSet.{u}} {f : ZFSet.{u}}
      (total : f = traceLam (graph A (fun b => traceApp f b)))
      (values : ∀ b, b ∈ A → InCarrier sig (traceApp f b))
      (rest : Deriv sig fs args) :
      Deriv sig (Field.ofFun A :: fs) (f :: args)

end

theorem deriv_fitsPred {sig : Signature.{u}} {c : Constructor} {args : List ZFSet.{u}}
    (fitting : Deriv sig c args) : FitsPred (InCarrier sig) c args :=
  match fitting with
  | .nil => FitsPred.nil
  | .recursive member rest => FitsPred.recursive member (deriv_fitsPred rest)
  | .ofSet member rest => FitsPred.ofSet member (deriv_fitsPred rest)
  | .ofFun total values rest => FitsPred.ofFun total values (deriv_fitsPred rest)

theorem fitsPred_deriv {sig : Signature.{u}} {c : Constructor} {args : List ZFSet.{u}}
    (fitting : FitsPred (InCarrier sig) c args) : Deriv sig c args := by
  induction fitting with
  | nil => exact Deriv.nil
  | recursive member _ ih => exact Deriv.recursive member ih
  | ofSet member _ ih => exact Deriv.ofSet member ih
  | ofFun total values _ ih => exact Deriv.ofFun total values ih

/-- A property that holds of every constructor value whose recursive arguments
and function values satisfy it holds of every generated element. -/
theorem inCarrier_induct {sig : Signature.{u}} {P : ZFSet.{u} → Prop}
    (step : ∀ {i : Nat} {c : Constructor} {args : List ZFSet.{u}},
      sig[i]? = some c → FitsPred P c args → P (constructorValue (numeral i) args))
    {x : ZFSet.{u}} (hx : InCarrier sig x) : P x :=
  InCarrier.rec
    (motive_1 := fun y _ => P y)
    (motive_2 := fun c args _ => FitsPred P c args)
    (fun atIndex _ fitsP => step atIndex fitsP)
    FitsPred.nil
    (fun _ _ hp hrest => FitsPred.recursive hp hrest)
    (fun member _ hrest => FitsPred.ofSet member hrest)
    (fun total _ _ ihValues hrest => FitsPred.ofFun total (fun b hb => ihValues b hb) hrest)
    hx

/-! ## Immediate arguments -/

inductive Arg : ZFSet.{u} → List Field.{u} → List ZFSet.{u} → Prop where
  | recHere {fs : List Field.{u}} {args : List ZFSet.{u}} {a : ZFSet.{u}} :
      Arg a (Field.recursive :: fs) (a :: args)
  | funHere {A : ZFSet.{u}} {fs : List Field.{u}} {args : List ZFSet.{u}} {f b : ZFSet.{u}} :
      b ∈ A → Arg (traceApp f b) (Field.ofFun A :: fs) (f :: args)
  | skip {y : ZFSet.{u}} {field : Field.{u}} {fs : List Field.{u}} {args : List ZFSet.{u}}
      {a : ZFSet.{u}} :
      Arg y fs args → Arg y (field :: fs) (a :: args)

def Immediate (sig : Signature.{u}) (y x : ZFSet.{u}) : Prop :=
  ∃ i c args, sig[i]? = some c ∧ x = constructorValue (numeral i) args ∧
    Deriv sig c args ∧ Arg y c args

theorem arg_inCarrier {sig : Signature.{u}} {c : Constructor} {args : List ZFSet.{u}} {y : ZFSet.{u}}
    (fitting : Deriv sig c args) (h : Arg y c args) : InCarrier sig y := by
  induction h with
  | recHere =>
      cases fitting with
      | recursive member _ => exact member
  | funHere hb =>
      cases fitting with
      | ofFun _ values _ => exact values _ hb
  | skip _ ih =>
      cases fitting with
      | recursive _ rest => exact ih rest
      | ofSet _ rest => exact ih rest
      | ofFun _ _ rest => exact ih rest

theorem arg_of_immediate {sig : Signature.{u}} {y : ZFSet.{u}} {i : Nat} {c : Constructor}
    {args : List ZFSet.{u}}
    (hy : Immediate sig y (constructorValue (numeral i) args))
    (atIndex : sig[i]? = some c) : Arg y c args := by
  obtain ⟨j, d, ds, atJ, equal, _, harg⟩ := hy
  have indexEq : i = j := numeral_injective (constructorValue_tag equal)
  have argsEq : args = ds := constructorValue_args equal
  cases indexEq
  cases argsEq
  have ctorEq : d = c := by
    have tags : some d = some c := by
      rw [← atJ, ← atIndex]
    exact Option.some_inj.mp tags
  cases ctorEq
  exact harg

theorem immediate_inCarrier {sig : Signature.{u}} {y x : ZFSet.{u}}
    (hy : Immediate sig y x) : InCarrier sig y := by
  obtain ⟨_, _, _, _, _, fitting, harg⟩ := hy
  exact arg_inCarrier fitting harg

theorem inCarrier_acc {sig : Signature.{u}} {x : ZFSet.{u}} (hx : InCarrier sig x) :
    Acc (Immediate sig) x :=
  InCarrier.rec
    (motive_1 := fun y _ => Acc (Immediate sig) y)
    (motive_2 := fun c args _ => ∀ y, Arg y c args → Acc (Immediate sig) y)
    (fun {i c args} atIndex _ subAcc =>
      Acc.intro (constructorValue (numeral i) args) (fun y hy =>
        subAcc y (arg_of_immediate hy atIndex)))
    (fun _ hy => by cases hy)
    (fun {fs args a} _ _ accA accRest y hy => by
      cases hy with
      | recHere => exact accA
      | skip h => exact accRest y h)
    (fun {_A _fs _args _a} _ _ accRest y hy => by
      cases hy with
      | skip h => exact accRest y h)
    (fun {_A _fs _args _f} _ _ _ accValues accRest y hy => by
      cases hy with
      | funHere hb => exact accValues _ hb
      | skip h => exact accRest y h)
    hx

theorem immediate_wf (sig : Signature.{u}) : WellFounded (Immediate sig) :=
  ⟨fun x => Acc.intro x (fun _ hy => inCarrier_acc (immediate_inCarrier hy))⟩

theorem arg_immediate {sig : Signature.{u}} {i : Nat} {c : Constructor}
    {args : List ZFSet.{u}} {y : ZFSet.{u}}
    (atIndex : sig[i]? = some c) (fitting : Deriv sig c args) (h : Arg y c args) :
    Immediate sig y (constructorValue (numeral i) args) :=
  ⟨i, c, args, atIndex, rfl, fitting, h⟩

/-! ## Recursion -/

noncomputable def mapResults (ev : ZFSet.{u} → ZFSet.{u}) :
    List Field.{u} → List ZFSet.{u} → List ZFSet.{u}
  | Field.recursive :: fs, a :: args => ev a :: mapResults ev fs args
  | Field.ofSet _ :: fs, _ :: args => mapResults ev fs args
  | Field.ofFun A :: fs, f :: args =>
      traceLam (graph A (fun b => ev (traceApp f b))) :: mapResults ev fs args
  | _, _ => []

theorem mapResults_recursive (ev : ZFSet.{u} → ZFSet.{u}) (fs : List Field.{u})
    (a : ZFSet.{u}) (args : List ZFSet.{u}) :
    mapResults ev (Field.recursive :: fs) (a :: args) = ev a :: mapResults ev fs args := rfl

theorem mapResults_ofSet (ev : ZFSet.{u} → ZFSet.{u}) (A : ZFSet.{u}) (fs : List Field.{u})
    (a : ZFSet.{u}) (args : List ZFSet.{u}) :
    mapResults ev (Field.ofSet A :: fs) (a :: args) = mapResults ev fs args := rfl

theorem mapResults_ofFun (ev : ZFSet.{u} → ZFSet.{u}) (A : ZFSet.{u}) (fs : List Field.{u})
    (f : ZFSet.{u}) (args : List ZFSet.{u}) :
    mapResults ev (Field.ofFun A :: fs) (f :: args) =
      traceLam (graph A (fun b => ev (traceApp f b))) :: mapResults ev fs args := rfl

theorem mapResults_nil (ev : ZFSet.{u} → ZFSet.{u}) (args : List ZFSet.{u}) :
    mapResults ev [] args = [] := rfl

theorem mapResults_agree {ev₁ ev₂ : ZFSet.{u} → ZFSet.{u}} {sig : Signature.{u}}
    {c : Constructor} {args : List ZFSet.{u}}
    (fitting : Deriv sig c args) (h : ∀ y, Arg y c args → ev₁ y = ev₂ y) :
    mapResults ev₁ c args = mapResults ev₂ c args :=
  match fitting with
  | .nil => rfl
  | .recursive (a := a) (fs := fs) (args := tail) _ rest => by
      rw [mapResults_recursive, mapResults_recursive, h a Arg.recHere,
        mapResults_agree (c := fs) (args := tail) rest (fun y hy => h y (Arg.skip hy))]
  | .ofSet (fs := fs) (args := tail) _ rest => by
      rw [mapResults_ofSet, mapResults_ofSet]
      exact mapResults_agree (c := fs) (args := tail) rest (fun y hy => h y (Arg.skip hy))
  | .ofFun (A := A) (f := f) (fs := fs) (args := tail) _ _ rest => by
      rw [mapResults_ofFun, mapResults_ofFun]
      refine congrArg₂ List.cons ?_
        (mapResults_agree (c := fs) (args := tail) rest (fun y hy => h y (Arg.skip hy)))
      apply congrArg traceLam
      apply graph_congr
      intro b hb
      exact h (traceApp f b) (Arg.funHere hb)

noncomputable def totalize (sig : Signature.{u}) (x : ZFSet.{u})
    (ih : ∀ y, Immediate sig y x → ZFSet.{u}) (y : ZFSet.{u}) : ZFSet.{u} :=
  @dite _ (Immediate sig y x) (Classical.propDecidable _) (fun h => ih y h) (fun _ => ∅)

theorem totalize_immediate {sig : Signature.{u}} {x y : ZFSet.{u}}
    (ih : ∀ z, Immediate sig z x → ZFSet.{u}) (h : Immediate sig y x) :
    totalize sig x ih y = ih y h := by
  unfold totalize
  rw [dif_pos h]

noncomputable def recBody (sig : Signature.{u})
    (step : Nat → List ZFSet.{u} → List ZFSet.{u} → ZFSet.{u})
    (x : ZFSet.{u}) (ih : ∀ y, Immediate sig y x → ZFSet.{u}) : ZFSet.{u} :=
  @Classical.epsilon ZFSet.{u} ⟨∅⟩ fun result =>
    ∀ i c args, sig[i]? = some c → constructorValue (numeral i) args = x →
      Deriv sig c args → result = step i args (mapResults (totalize sig x ih) c args)

noncomputable def recFun (sig : Signature.{u})
    (step : Nat → List ZFSet.{u} → List ZFSet.{u} → ZFSet.{u}) (x : ZFSet.{u}) : ZFSet.{u} :=
  WellFounded.fix (immediate_wf sig) (fun x ih => recBody sig step x ih) x

theorem recFun_unfold (sig : Signature.{u})
    (step : Nat → List ZFSet.{u} → List ZFSet.{u} → ZFSet.{u}) (x : ZFSet.{u}) :
    recFun sig step x = recBody sig step x (fun y _ => recFun sig step y) := by
  unfold recFun
  exact WellFounded.fix_eq (immediate_wf sig) (fun x ih => recBody sig step x ih) x

theorem mapResults_totalize (sig : Signature.{u})
    (step : Nat → List ZFSet.{u} → List ZFSet.{u} → ZFSet.{u})
    {i : Nat} {c : Constructor} {args : List ZFSet.{u}}
    (atIndex : sig[i]? = some c) (fitting : Deriv sig c args) :
    mapResults (totalize sig (constructorValue (numeral i) args)
        (fun y _ => recFun sig step y)) c args =
      mapResults (recFun sig step) c args := by
  apply mapResults_agree fitting
  intro y hy
  exact totalize_immediate (fun z _ => recFun sig step z) (arg_immediate atIndex fitting hy)

theorem recFun_constructor (sig : Signature.{u})
    (step : Nat → List ZFSet.{u} → List ZFSet.{u} → ZFSet.{u})
    {i : Nat} {c : Constructor} {args : List ZFSet.{u}}
    (atIndex : sig[i]? = some c) (fitting : Deriv sig c args) :
    recFun sig step (constructorValue (numeral i) args) =
      step i args (mapResults (recFun sig step) c args) := by
  rw [recFun_unfold]
  let pred : ZFSet.{u} → Prop := fun result =>
    ∀ j d ds, sig[j]? = some d →
      constructorValue (numeral j) ds = constructorValue (numeral i) args →
        Deriv sig d ds →
          result = step j ds
            (mapResults (totalize sig (constructorValue (numeral i) args)
              (fun y _ => recFun sig step y)) d ds)
  have existsValue : ∃ result, pred result := by
    refine ⟨step i args (mapResults (recFun sig step) c args), ?_⟩
    intro j d ds atJ equal fitting'
    obtain ⟨tags, rfl⟩ := constructorValue_injective.mp equal
    cases numeral_injective tags
    have ctorEq : d = c := by
      have tags : some d = some c := by rw [← atJ, ← atIndex]
      exact Option.some_inj.mp tags
    cases ctorEq
    rw [mapResults_totalize sig step atIndex fitting']
  have spec := Classical.epsilon_spec_aux ⟨(∅ : ZFSet.{u})⟩ pred existsValue
  change recBody sig step (constructorValue (numeral i) args) (fun y _ => recFun sig step y) = _
  have applied := spec i c args atIndex rfl fitting
  rw [mapResults_totalize sig step atIndex fitting] at applied
  exact applied

theorem recFun_unique (sig : Signature.{u})
    (step : Nat → List ZFSet.{u} → List ZFSet.{u} → ZFSet.{u})
    (g : ZFSet.{u} → ZFSet.{u})
    (equations : ∀ {i : Nat} {c : Constructor} {args : List ZFSet.{u}},
      sig[i]? = some c → Deriv sig c args →
        g (constructorValue (numeral i) args) = step i args (mapResults g c args))
    {x : ZFSet.{u}} (hx : InCarrier sig x) : g x = recFun sig step x :=
  InCarrier.rec
    (motive_1 := fun y _ => g y = recFun sig step y)
    (motive_2 := fun c args _ => mapResults g c args = mapResults (recFun sig step) c args)
    (fun atIndex fitting agree => by
      rw [equations atIndex fitting, recFun_constructor sig step atIndex fitting, agree])
    rfl
    (fun _ _ hp hrest => by
      rw [mapResults_recursive, mapResults_recursive, hp, hrest])
    (fun _ _ hrest => by rw [mapResults_ofSet, mapResults_ofSet, hrest])
    (fun _ _ _ ihValues ihRest => by
      rw [mapResults_ofFun, mapResults_ofFun, ihRest]
      apply congrArg (fun head => head :: mapResults (recFun sig step) _ _)
      apply congrArg traceLam
      apply graph_congr
      intro b hb
      exact ihValues b hb)
    hx

/-! ## Membership of a generated element -/

theorem traceLam_graph_mem {U A f : ZFSet.{u}} (closed : Closed U) (hA : A ∈ U)
    (values : ∀ a, a ∈ A → traceApp f a ∈ U) :
    traceLam (graph A (fun a => traceApp f a)) ∈ U :=
  closed.traceLam_mem (closed.replacement_mem hA (fun a => ZFSet.pair a (traceApp f a))
    (fun a ha => closed.pair_mem (closed.transitive _ hA ha) (values a ha)))

theorem fitsPred_arg_mem {U : ZFSet.{u}} (closed : Closed U) {c : Constructor}
    {args : List ZFSet.{u}}
    (sets : ∀ A, Field.ofSet A ∈ c → A ∈ U)
    (domains : ∀ A, Field.ofFun A ∈ c → A ∈ U)
    (fitting : FitsPred (fun a => a ∈ U) c args) :
    ∀ a, a ∈ args → a ∈ U := by
  induction fitting with
  | nil =>
      intro a ha
      cases ha
  | recursive member _ ih =>
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact member
      · exact ih (fun A hA => sets A (List.mem_cons_of_mem _ hA))
          (fun A hA => domains A (List.mem_cons_of_mem _ hA)) b hb
  | ofSet member _ ih =>
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact closed.transitive _ (sets _ List.mem_cons_self) member
      · exact ih (fun A hA => sets A (List.mem_cons_of_mem _ hA))
          (fun A hA => domains A (List.mem_cons_of_mem _ hA)) b hb
  | ofFun total values _ ih =>
      rename_i domA _ _ _ _
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · have hA : domA ∈ U := domains domA List.mem_cons_self
        rw [total]
        exact traceLam_graph_mem closed hA values
      · exact ih (fun A hA => sets A (List.mem_cons_of_mem _ hA))
          (fun A hA => domains A (List.mem_cons_of_mem _ hA)) b hb

theorem inCarrier_mem {sig : Signature.{u}} {U : ZFSet.{u}} (closed : Closed U)
    (hω : ZFSet.omega ∈ U)
    (fields : ∀ c, c ∈ sig →
      (∀ A, Field.ofSet A ∈ c → A ∈ U) ∧ (∀ A, Field.ofFun A ∈ c → A ∈ U))
    {x : ZFSet.{u}} (hx : InCarrier sig x) : x ∈ U :=
  inCarrier_induct
    (fun {i c args} atIndex fitting => by
      have hc : c ∈ sig := mem_of_get? atIndex
      have argsMem := fitsPred_arg_mem closed (fields c hc).1 (fields c hc).2 fitting
      exact closed.pair_mem (numeral_mem_of_omega closed hω i)
        (tuple_mem closed (closed.empty_mem hω) args argsMem))
    hx

/-! ## Path codes -/

def fieldSets : Field.{u} → List ZFSet.{u}
  | .recursive => []
  | .ofSet A => [A]
  | .ofFun _ => []

def fieldDomains : Field.{u} → List ZFSet.{u}
  | .recursive => []
  | .ofSet _ => []
  | .ofFun A => [A]

def constructorSets : Constructor → List ZFSet.{u}
  | [] => []
  | field :: fs => fieldSets field ++ constructorSets fs

def constructorDomains : Constructor → List ZFSet.{u}
  | [] => []
  | field :: fs => fieldDomains field ++ constructorDomains fs

def signatureSets : Signature.{u} → List ZFSet.{u}
  | [] => []
  | c :: cs => constructorSets c ++ signatureSets cs

def signatureDomains : Signature.{u} → List ZFSet.{u}
  | [] => []
  | c :: cs => constructorDomains c ++ signatureDomains cs

def unionList : List ZFSet.{u} → ZFSet.{u}
  | [] => ∅
  | a :: as => a ∪ unionList as

def dataBound (sig : Signature.{u}) : ZFSet.{u} := unionList (signatureSets sig)

def payloadBody (sig : Signature.{u}) : ZFSet.{u} := unionList (signatureDomains sig)

def payloadSet (sig : Signature.{u}) : ZFSet.{u} := insert ∅ (payloadBody sig)

theorem subset_unionList_of_mem {a : ZFSet.{u}} {as : List ZFSet.{u}} (h : a ∈ as) :
    a ⊆ unionList as := by
  induction as with
  | nil => cases h
  | cons head tail ih =>
      intro x hx
      rcases List.mem_cons.mp h with rfl | h
      · exact ZFSet.mem_union.mpr (Or.inl hx)
      · exact ZFSet.mem_union.mpr (Or.inr (ih h hx))

theorem mem_constructorSets_ofSet {c : Constructor} {A : ZFSet.{u}}
    (h : Field.ofSet A ∈ c) : A ∈ constructorSets c := by
  induction c with
  | nil => cases h
  | cons field fs ih =>
      rcases List.mem_cons.mp h with rfl | h
      · exact List.mem_append.mpr (Or.inl List.mem_cons_self)
      · exact List.mem_append.mpr (Or.inr (ih h))

theorem mem_constructorDomains_ofFun {c : Constructor} {A : ZFSet.{u}}
    (h : Field.ofFun A ∈ c) : A ∈ constructorDomains c := by
  induction c with
  | nil => cases h
  | cons field fs ih =>
      rcases List.mem_cons.mp h with rfl | h
      · exact List.mem_append.mpr (Or.inl List.mem_cons_self)
      · exact List.mem_append.mpr (Or.inr (ih h))

theorem mem_signatureSets_ofSet {sig : Signature.{u}} {c : Constructor} {A : ZFSet.{u}}
    (hc : c ∈ sig) (hA : Field.ofSet A ∈ c) : A ∈ signatureSets sig := by
  induction sig with
  | nil => cases hc
  | cons head tail ih =>
      rcases List.mem_cons.mp hc with rfl | hc
      · exact List.mem_append.mpr (Or.inl (mem_constructorSets_ofSet hA))
      · exact List.mem_append.mpr (Or.inr (ih hc))

theorem mem_signatureDomains_ofFun {sig : Signature.{u}} {c : Constructor} {A : ZFSet.{u}}
    (hc : c ∈ sig) (hA : Field.ofFun A ∈ c) : A ∈ signatureDomains sig := by
  induction sig with
  | nil => cases hc
  | cons head tail ih =>
      rcases List.mem_cons.mp hc with rfl | hc
      · exact List.mem_append.mpr (Or.inl (mem_constructorDomains_ofFun hA))
      · exact List.mem_append.mpr (Or.inr (ih hc))

theorem ofSet_subset_dataBound {sig : Signature.{u}} {c : Constructor} {A : ZFSet.{u}}
    (hc : c ∈ sig) (hA : Field.ofSet A ∈ c) : A ⊆ dataBound sig :=
  subset_unionList_of_mem (mem_signatureSets_ofSet hc hA)

theorem ofFun_subset_payloadBody {sig : Signature.{u}} {c : Constructor} {A : ZFSet.{u}}
    (hc : c ∈ sig) (hA : Field.ofFun A ∈ c) : A ⊆ payloadBody sig :=
  subset_unionList_of_mem
    (mem_signatureDomains_ofFun hc hA)

theorem mem_payloadSet_left (sig : Signature.{u}) : (∅ : ZFSet.{u}) ∈ payloadSet sig :=
  ZFSet.mem_insert_iff.mpr (Or.inl rfl)

theorem mem_payloadSet_of_body {sig : Signature.{u}} {a : ZFSet.{u}} (ha : a ∈ payloadBody sig) :
    a ∈ payloadSet sig :=
  ZFSet.mem_insert_iff.mpr (Or.inr ha)

theorem mem_payloadSet_of_domain {sig : Signature.{u}} {c : Constructor} {A a : ZFSet.{u}}
    (hc : c ∈ sig) (hA : Field.ofFun A ∈ c) (ha : a ∈ A) : a ∈ payloadSet sig :=
  mem_payloadSet_of_body (ofFun_subset_payloadBody hc hA ha)

/-- A move toward a recursive argument. The tag is `0`, the index is a numeral,
and the payload is empty, so an empty domain element stays distinguishable. -/
def moveRec (k : Nat) : ZFSet.{u} := ZFSet.pair (ZFSet.pair (numeral 0) (numeral k)) ∅

/-- A move toward the value of a function argument at one domain element. -/
def moveFun (k : Nat) (a : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.pair (ZFSet.pair (numeral 1) (numeral k)) a

noncomputable def moveIndex (m : ZFSet.{u}) : ZFSet.{u} := second (first m)

noncomputable def movePayload (m : ZFSet.{u}) : ZFSet.{u} := second m

def tagIndex : ZFSet.{u} := ZFSet.prod ({numeral 0, numeral 1} : ZFSet.{u}) ZFSet.omega

def moveSet (sig : Signature.{u}) : ZFSet.{u} := ZFSet.prod tagIndex (payloadSet sig)

theorem moveIndex_rec (k : Nat) : moveIndex (moveRec k) = numeral k := by
  unfold moveIndex moveRec
  rw [first_pair, second_pair]

theorem movePayload_rec (k : Nat) : movePayload (moveRec k) = ∅ := by
  unfold movePayload moveRec
  rw [second_pair]

theorem moveIndex_fun (k : Nat) (a : ZFSet.{u}) : moveIndex (moveFun k a) = numeral k := by
  unfold moveIndex moveFun
  rw [first_pair, second_pair]

theorem movePayload_fun (k : Nat) (a : ZFSet.{u}) : movePayload (moveFun k a) = a := by
  unfold movePayload moveFun
  rw [second_pair]

theorem tagZero_mem : numeral 0 ∈ ({numeral 0, numeral 1} : ZFSet.{u}) :=
  ZFSet.mem_pair.mpr (Or.inl rfl)

theorem tagOne_mem : numeral (1 : Nat) ∈ ({numeral 0, numeral 1} : ZFSet.{u}) :=
  ZFSet.mem_pair.mpr (Or.inr rfl)

theorem moveRec_mem (sig : Signature.{u}) (k : Nat) : moveRec k ∈ moveSet sig := by
  refine ZFSet.pair_mem_prod.mpr ⟨?_, mem_payloadSet_left sig⟩
  exact ZFSet.pair_mem_prod.mpr ⟨tagZero_mem, numeral_mem_omega k⟩

theorem moveFun_mem {sig : Signature.{u}} {k : Nat} {a : ZFSet.{u}} (ha : a ∈ payloadSet sig) :
    moveFun k a ∈ moveSet sig := by
  refine ZFSet.pair_mem_prod.mpr ⟨?_, ha⟩
  exact ZFSet.pair_mem_prod.mpr ⟨tagOne_mem, numeral_mem_omega k⟩

noncomputable def paths (sig : Signature.{u}) : ZFSet.{u} := listCode (moveSet sig)

def absentLabel : ZFSet.{u} := ZFSet.pair (numeral 0) ∅

def presentLabel (sig : Signature.{u}) (i : Nat) (sets : List (Elements (dataBound sig))) :
    ZFSet.{u} :=
  ZFSet.pair (numeral (i + 1)) (encode sets)

noncomputable def labelSet (sig : Signature.{u}) : ZFSet.{u} :=
  ZFSet.prod ZFSet.omega (listCode (dataBound sig))

theorem absentLabel_mem (sig : Signature.{u}) : absentLabel ∈ labelSet sig := by
  refine ZFSet.pair_mem_prod.mpr ⟨numeral_mem_omega 0, ?_⟩
  exact ZFSet.mem_range_self (f := encode (a := dataBound sig)) []

theorem presentLabel_mem (sig : Signature.{u}) (i : Nat) (xs : List (Elements (dataBound sig))) :
    presentLabel sig i xs ∈ labelSet sig :=
  ZFSet.pair_mem_prod.mpr ⟨numeral_mem_omega (i + 1), ZFSet.mem_range_self xs⟩

theorem presentLabel_injective {sig : Signature.{u}} {i j : Nat}
    {xs ys : List (Elements (dataBound sig))}
    (h : presentLabel sig i xs = presentLabel sig j ys) : i = j ∧ xs = ys := by
  have firstEq : numeral (i + 1) = numeral (j + 1) := by
    have tags := congrArg first h
    rw [presentLabel, presentLabel, first_pair, first_pair] at tags
    exact tags
  have secondEq : encode xs = encode ys := by
    have bodies := congrArg second h
    rw [presentLabel, presentLabel, second_pair, second_pair] at bodies
    exact bodies
  exact ⟨Nat.succ_injective (numeral_injective firstEq), encode_injective _ secondEq⟩

theorem decode_encode_any {a : ZFSet.{u}} (xs : List (Elements a)) (hp : encode xs ∈ listCode a) :
    decode ⟨encode xs, hp⟩ = xs :=
  encode_injective a (encode_decode ⟨encode xs, hp⟩)

noncomputable def setArgs (sig : Signature.{u}) (c : Constructor) (args : List ZFSet.{u}) :
    List (Elements (dataBound sig)) :=
  match c with
  | [] => []
  | .recursive :: fs =>
      match args with
      | [] => []
      | _ :: rest => setArgs sig fs rest
  | .ofSet _ :: fs =>
      match args with
      | [] => []
      | a :: rest =>
          @dite _ (a ∈ dataBound sig) (Classical.propDecidable _)
            (fun h => ⟨a, h⟩ :: setArgs sig fs rest) (fun _ => setArgs sig fs rest)
  | .ofFun _ :: fs =>
      match args with
      | [] => []
      | _ :: rest => setArgs sig fs rest

theorem setArgs_recursive (sig : Signature.{u}) (fs : List Field.{u}) (a : ZFSet.{u})
    (args : List ZFSet.{u}) :
    setArgs sig (Field.recursive :: fs) (a :: args) = setArgs sig fs args := rfl

theorem setArgs_ofFun (sig : Signature.{u}) (A : ZFSet.{u}) (fs : List Field.{u})
    (f : ZFSet.{u}) (args : List ZFSet.{u}) :
    setArgs sig (Field.ofFun A :: fs) (f :: args) = setArgs sig fs args := rfl

theorem setArgs_nil (sig : Signature.{u}) (args : List ZFSet.{u}) : setArgs sig [] args = [] := rfl

theorem setArgs_ofSet_pos (sig : Signature.{u}) (A : ZFSet.{u}) (fs : List Field.{u})
    (a : ZFSet.{u}) (args : List ZFSet.{u}) (ha : a ∈ dataBound sig) :
    setArgs sig (Field.ofSet A :: fs) (a :: args) = ⟨a, ha⟩ :: setArgs sig fs args := by
  conv_lhs => simp only [setArgs]
  rw [dif_pos ha]

noncomputable def labelsOf {sig : Signature.{u}} (root : ZFSet.{u})
    (child : ZFSet.{u} → ZFSet.{u}) :
    List (Elements (moveSet sig)) → ZFSet.{u}
  | [] => root
  | m :: rest => traceApp (child m.1) (encode rest)

noncomputable def labelAt (sig : Signature.{u}) (root : ZFSet.{u})
    (child : ZFSet.{u} → ZFSet.{u}) (p : ZFSet.{u}) : ZFSet.{u} :=
  @dite _ (p ∈ paths sig) (Classical.propDecidable _)
    (fun hp => labelsOf root child (decode ⟨p, hp⟩)) (fun _ => absentLabel)

theorem labelAt_encode {sig : Signature.{u}} (root : ZFSet.{u}) (child : ZFSet.{u} → ZFSet.{u})
    (xs : List (Elements (moveSet sig))) :
    labelAt sig root child (encode xs) = labelsOf root child xs := by
  have hp : encode xs ∈ paths sig := ZFSet.mem_range_self xs
  unfold labelAt
  rw [dif_pos hp, decode_encode_any xs hp]

noncomputable def absentCode (sig : Signature.{u}) : ZFSet.{u} :=
  traceLam (graph (paths sig) (fun _ => absentLabel))

noncomputable def resultAt (sig : Signature.{u}) (recs : List ZFSet.{u}) (c : Constructor)
    (k : Nat) (payload : ZFSet.{u}) : ZFSet.{u} :=
  match c with
  | [] => absentCode sig
  | .recursive :: fs =>
      match recs, k with
      | [], _ => absentCode sig
      | r :: _, 0 => r
      | _ :: rs, k + 1 => resultAt sig rs fs k payload
  | .ofSet _ :: fs =>
      match k with
      | 0 => absentCode sig
      | k + 1 => resultAt sig recs fs k payload
  | .ofFun A :: fs =>
      match recs, k with
      | [], _ => absentCode sig
      | r :: _, 0 =>
          @dite _ (payload ∈ A) (Classical.propDecidable _)
            (fun _ => traceApp r payload) (fun _ => absentCode sig)
      | _ :: rs, k + 1 => resultAt sig rs fs k payload

theorem resultAt_rec_zero (sig : Signature.{u}) (r : ZFSet.{u}) (rs : List ZFSet.{u})
    (fs : List Field.{u}) (payload : ZFSet.{u}) :
    resultAt sig (r :: rs) (Field.recursive :: fs) 0 payload = r := rfl

theorem resultAt_rec_succ (sig : Signature.{u}) (r : ZFSet.{u}) (rs : List ZFSet.{u})
    (fs : List Field.{u}) (k : Nat) (payload : ZFSet.{u}) :
    resultAt sig (r :: rs) (Field.recursive :: fs) (k + 1) payload =
      resultAt sig rs fs k payload := rfl

theorem resultAt_set_zero (sig : Signature.{u}) (recs : List ZFSet.{u}) (A : ZFSet.{u})
    (fs : List Field.{u}) (payload : ZFSet.{u}) :
    resultAt sig recs (Field.ofSet A :: fs) 0 payload = absentCode sig := rfl

theorem resultAt_set_succ (sig : Signature.{u}) (recs : List ZFSet.{u}) (A : ZFSet.{u})
    (fs : List Field.{u}) (k : Nat) (payload : ZFSet.{u}) :
    resultAt sig recs (Field.ofSet A :: fs) (k + 1) payload =
      resultAt sig recs fs k payload := rfl

theorem resultAt_fun_succ (sig : Signature.{u}) (r : ZFSet.{u}) (rs : List ZFSet.{u})
    (A : ZFSet.{u}) (fs : List Field.{u}) (k : Nat) (payload : ZFSet.{u}) :
    resultAt sig (r :: rs) (Field.ofFun A :: fs) (k + 1) payload =
      resultAt sig rs fs k payload := rfl

theorem resultAt_fun_pos (sig : Signature.{u}) (r : ZFSet.{u}) (rs : List ZFSet.{u})
    (A : ZFSet.{u}) (fs : List Field.{u}) (payload : ZFSet.{u}) (h : payload ∈ A) :
    resultAt sig (r :: rs) (Field.ofFun A :: fs) 0 payload = traceApp r payload := by
  conv_lhs => simp only [resultAt]
  rw [dif_pos h]

theorem resultAt_fun_neg (sig : Signature.{u}) (r : ZFSet.{u}) (rs : List ZFSet.{u})
    (A : ZFSet.{u}) (fs : List Field.{u}) (payload : ZFSet.{u}) (h : payload ∉ A) :
    resultAt sig (r :: rs) (Field.ofFun A :: fs) 0 payload = absentCode sig := by
  conv_lhs => simp only [resultAt]
  rw [dif_neg h]

theorem resultAt_nil (sig : Signature.{u}) (recs : List ZFSet.{u}) (k : Nat)
    (payload : ZFSet.{u}) : resultAt sig recs [] k payload = absentCode sig := rfl

noncomputable def assembled (sig : Signature.{u}) (i : Nat) (c : Constructor)
    (args recs : List ZFSet.{u}) : ZFSet.{u} :=
  let root := presentLabel sig i (setArgs sig c args)
  let child := fun m => resultAt sig recs c (natOf (moveIndex m)) (movePayload m)
  traceLam (graph (paths sig) (fun p => labelAt sig root child p))

theorem traceApp_assembled_nil {sig : Signature.{u}} {i : Nat} {c : Constructor}
    {args recs : List ZFSet.{u}} :
    traceApp (assembled sig i c args recs) (encode (a := moveSet sig) []) =
      presentLabel sig i (setArgs sig c args) := by
  unfold assembled
  have hp : encode (a := moveSet sig) [] ∈ paths sig := ZFSet.mem_range_self []
  rw [traceApp_graph_beta _ hp, labelAt_encode]
  rfl

theorem traceApp_assembled_cons {sig : Signature.{u}} {i : Nat} {c : Constructor}
    {args recs : List ZFSet.{u}} (m : Elements (moveSet sig))
    (xs : List (Elements (moveSet sig))) :
    traceApp (assembled sig i c args recs) (encode (m :: xs)) =
      traceApp (resultAt sig recs c (natOf (moveIndex m.1)) (movePayload m.1))
        (encode xs) := by
  unfold assembled
  have hp : encode (m :: xs) ∈ paths sig := ZFSet.mem_range_self (m :: xs)
  rw [traceApp_graph_beta _ hp, labelAt_encode]
  rfl

noncomputable def assembleStep (sig : Signature.{u}) (i : Nat) (args recs : List ZFSet.{u}) :
    ZFSet.{u} :=
  match sig[i]? with
  | some c => assembled sig i c args recs
  | none => absentCode sig

noncomputable def codeOf (sig : Signature.{u}) : ZFSet.{u} → ZFSet.{u} :=
  recFun sig (assembleStep sig)

theorem codeOf_assembled {sig : Signature.{u}} {i : Nat} {c : Constructor} {args : List ZFSet.{u}}
    (atIndex : sig[i]? = some c) (fitting : Deriv sig c args) :
    codeOf sig (constructorValue (numeral i) args) =
      assembled sig i c args (mapResults (codeOf sig) c args) := by
  rw [codeOf, recFun_constructor sig (assembleStep sig) atIndex fitting]
  unfold assembleStep
  split
  · next c' hc =>
      have ctorEq : c' = c := Option.some_inj.mp (hc.symm.trans atIndex)
      cases ctorEq
      rfl
  · next hc =>
      cases atIndex.symm.trans hc

/-! ## Codes determine the element -/

noncomputable def codeSpace (sig : Signature.{u}) : ZFSet.{u} :=
  tracePiSet (paths sig) (fun _ => labelSet sig)

theorem traceLam_ext {sig : Signature.{u}} {f g : ZFSet.{u} → ZFSet.{u}}
    (h : ∀ p, p ∈ paths sig → f p = g p) :
    traceLam (graph (paths sig) f) = traceLam (graph (paths sig) g) :=
  congrArg traceLam (graph_congr h)

theorem absentCode_mem (sig : Signature.{u}) : absentCode sig ∈ codeSpace sig := by
  refine mem_tracePiSet_of_total ?_ ?_
  · conv_lhs => unfold absentCode
    apply congrArg traceLam
    apply graph_congr
    intro p hp
    rw [absentCode, traceApp_graph_beta (fun _ => absentLabel) hp]
  · intro p hp
    rw [absentCode, traceApp_graph_beta (fun _ => absentLabel) hp]
    exact absentLabel_mem sig

theorem codeOf_is_trace {sig : Signature.{u}} {x : ZFSet.{u}} (hx : InCarrier sig x) :
    ∃ lab : ZFSet.{u} → ZFSet.{u}, codeOf sig x = traceLam (graph (paths sig) lab) := by
  cases hx with
  | intro atIndex fitting =>
      rw [codeOf_assembled atIndex fitting]
      unfold assembled
      exact ⟨_, rfl⟩

theorem resultAt_code_trace {sig : Signature.{u}} {c : Constructor} {args : List ZFSet.{u}}
    (fitting : Deriv sig c args) :
    ∀ k payload, ∃ lab : ZFSet.{u} → ZFSet.{u},
      resultAt sig (mapResults (codeOf sig) c args) c k payload =
        traceLam (graph (paths sig) lab) :=
  match fitting with
  | .nil => fun k payload => by
      rw [mapResults_nil, resultAt_nil]
      exact ⟨fun _ => absentLabel, rfl⟩
  | .recursive member rest => fun k payload => by
      cases k with
      | zero =>
          rw [mapResults_recursive, resultAt_rec_zero]
          exact codeOf_is_trace member
      | succ k =>
          rw [mapResults_recursive, resultAt_rec_succ]
          exact resultAt_code_trace rest k payload
  | .ofSet _ rest => fun k payload => by
      cases k with
      | zero =>
          rw [mapResults_ofSet, resultAt_set_zero]
          exact ⟨fun _ => absentLabel, rfl⟩
      | succ k =>
          rw [mapResults_ofSet, resultAt_set_succ]
          exact resultAt_code_trace rest k payload
  | .ofFun (A := A) (f := f) total values rest => fun k payload => by
      cases k with
      | zero =>
          match Classical.propDecidable (payload ∈ A) with
          | isTrue hmem =>
              rw [mapResults_ofFun, resultAt_fun_pos sig _ _ A _ payload hmem,
                traceApp_graph_beta _ hmem]
              exact codeOf_is_trace (values payload hmem)
          | isFalse hmem =>
              rw [mapResults_ofFun, resultAt_fun_neg sig _ _ A _ payload hmem]
              exact ⟨fun _ => absentLabel, rfl⟩
      | succ k =>
          rw [mapResults_ofFun, resultAt_fun_succ]
          exact resultAt_code_trace rest k payload

theorem views_of_assembled {sig : Signature.{u}} {i : Nat} {c : Constructor}
    {args ds recs recs' : List ZFSet.{u}}
    (h : assembled sig i c args recs = assembled sig i c ds recs')
    (leftT : ∀ k payload, ∃ lab : ZFSet.{u} → ZFSet.{u},
      resultAt sig recs c k payload = traceLam (graph (paths sig) lab))
    (rightT : ∀ k payload, ∃ lab : ZFSet.{u} → ZFSet.{u},
      resultAt sig recs' c k payload = traceLam (graph (paths sig) lab)) :
    ∀ k payload, payload ∈ payloadSet sig →
      resultAt sig recs c k payload = resultAt sig recs' c k payload := by
  intro k payload hpay
  have hmove : moveFun k payload ∈ moveSet sig := moveFun_mem hpay
  let m : Elements (moveSet sig) := ⟨moveFun k payload, hmove⟩
  have hk : natOf (moveIndex m.1) = k := by
    rw [moveIndex_fun, natOf_numeral]
  have hpayload : movePayload m.1 = payload := by
    rw [movePayload_fun]
  have point : ∀ xs : List (Elements (moveSet sig)),
      traceApp (resultAt sig recs c k payload) (encode xs) =
        traceApp (resultAt sig recs' c k payload) (encode xs) := by
    intro xs
    have happ := congrArg (fun t => traceApp t (encode (m :: xs))) h
    rw [traceApp_assembled_cons m xs, traceApp_assembled_cons m xs, hk, hpayload] at happ
    exact happ
  obtain ⟨labL, hL⟩ := leftT k payload
  obtain ⟨labR, hR⟩ := rightT k payload
  rw [hL, hR]
  apply traceLam_ext
  intro p hp
  rw [← traceApp_graph_beta labL hp, ← traceApp_graph_beta labR hp, ← hL, ← hR]
  obtain ⟨xs, rfl⟩ := mem_listCode.mp hp
  exact point xs

structure SubInj (sig : Signature.{u}) (c : Constructor) (args : List ZFSet.{u}) : Prop where
  inj : ∀ y, Arg y c args → ∀ z, InCarrier sig z → codeOf sig y = codeOf sig z → y = z

theorem SubInj.tail {sig : Signature.{u}} {field : Field.{u}} {fs : List Field.{u}}
    {a : ZFSet.{u}} {args : List ZFSet.{u}}
    (sub : SubInj sig (field :: fs) (a :: args)) : SubInj sig fs args where
  inj y hy z hz hcode := sub.inj y (Arg.skip hy) z hz hcode

theorem args_eq {sig : Signature.{u}} {c : Constructor} {args ds : List ZFSet.{u}}
    (fitting : Deriv sig c args) (fitting' : Deriv sig c ds) (sub : SubInj sig c args)
    (setsIn : ∀ A, Field.ofSet A ∈ c → A ⊆ dataBound sig)
    (domsIn : ∀ A, Field.ofFun A ∈ c → A ⊆ payloadBody sig)
    (sets : setArgs sig c args = setArgs sig c ds)
    (views : ∀ k payload, payload ∈ payloadSet sig →
      resultAt sig (mapResults (codeOf sig) c args) c k payload =
        resultAt sig (mapResults (codeOf sig) c ds) c k payload) :
    args = ds :=
  match fitting with
  | .nil => by
      match fitting' with
      | .nil => rfl
  | .recursive (fs := fs) (a := a) (args := tail) _ rest => by
      match fitting' with
      | .recursive (a := b) (args := tail') member' rest' =>
          have codeEq : codeOf sig a = codeOf sig b := by
            have v := views 0 ∅ (mem_payloadSet_left sig)
            rw [mapResults_recursive, mapResults_recursive, resultAt_rec_zero,
              resultAt_rec_zero] at v
            exact v
          have headEq : a = b := sub.inj a Arg.recHere b member' codeEq
          have setsTail : setArgs sig fs tail = setArgs sig fs tail' := by
            rw [setArgs_recursive, setArgs_recursive] at sets
            exact sets
          have viewsTail : ∀ k payload, payload ∈ payloadSet sig →
              resultAt sig (mapResults (codeOf sig) fs tail) fs k payload =
                resultAt sig (mapResults (codeOf sig) fs tail') fs k payload := by
            intro k payload hp
            have v := views (k + 1) payload hp
            rw [mapResults_recursive, mapResults_recursive, resultAt_rec_succ,
              resultAt_rec_succ] at v
            exact v
          have tailEq := args_eq rest rest' sub.tail
            (fun A hA => setsIn A (List.mem_cons_of_mem _ hA))
            (fun A hA => domsIn A (List.mem_cons_of_mem _ hA)) setsTail viewsTail
          exact congrArg₂ List.cons headEq tailEq
  | .ofSet (A := A) (fs := fs) (a := a) (args := tail) member rest => by
      match fitting' with
      | .ofSet (a := b) (args := tail') member' rest' =>
          have ha : a ∈ dataBound sig := setsIn A List.mem_cons_self member
          have hb : b ∈ dataBound sig := setsIn A List.mem_cons_self member'
          rw [setArgs_ofSet_pos sig A fs a tail ha, setArgs_ofSet_pos sig A fs b tail' hb] at sets
          have splitSets := List.cons.inj sets
          have headEq : a = b := congrArg Subtype.val splitSets.1
          have setsTail : setArgs sig fs tail = setArgs sig fs tail' := splitSets.2
          have viewsTail : ∀ k payload, payload ∈ payloadSet sig →
              resultAt sig (mapResults (codeOf sig) fs tail) fs k payload =
                resultAt sig (mapResults (codeOf sig) fs tail') fs k payload := by
            intro k payload hp
            have v := views (k + 1) payload hp
            rw [mapResults_ofSet, mapResults_ofSet, resultAt_set_succ, resultAt_set_succ] at v
            exact v
          have tailEq := args_eq rest rest' sub.tail
            (fun B hB => setsIn B (List.mem_cons_of_mem _ hB))
            (fun B hB => domsIn B (List.mem_cons_of_mem _ hB)) setsTail viewsTail
          exact congrArg₂ List.cons headEq tailEq
  | .ofFun (A := A) (f := f) (fs := fs) (args := tail) total _ rest => by
      match fitting' with
      | .ofFun (f := g) (args := tail') total' values' rest' =>
          have valueEq : ∀ b, b ∈ A → traceApp f b = traceApp g b := by
            intro b hb
            have hpay : b ∈ payloadSet sig :=
              mem_payloadSet_of_body (domsIn A List.mem_cons_self hb)
            have v := views 0 b hpay
            rw [mapResults_ofFun, mapResults_ofFun,
              resultAt_fun_pos sig _ _ A _ b hb, resultAt_fun_pos sig _ _ A _ b hb,
              traceApp_graph_beta _ hb, traceApp_graph_beta _ hb] at v
            exact sub.inj (traceApp f b) (Arg.funHere hb) (traceApp g b) (values' b hb) v
          have headEq : f = g := by
            rw [total, total']
            apply congrArg traceLam
            apply graph_congr
            exact valueEq
          have setsTail : setArgs sig fs tail = setArgs sig fs tail' := by
            rw [setArgs_ofFun, setArgs_ofFun] at sets
            exact sets
          have viewsTail : ∀ k payload, payload ∈ payloadSet sig →
              resultAt sig (mapResults (codeOf sig) fs tail) fs k payload =
                resultAt sig (mapResults (codeOf sig) fs tail') fs k payload := by
            intro k payload hp
            have v := views (k + 1) payload hp
            rw [mapResults_ofFun, mapResults_ofFun, resultAt_fun_succ, resultAt_fun_succ] at v
            exact v
          have tailEq := args_eq rest rest' sub.tail
            (fun B hB => setsIn B (List.mem_cons_of_mem _ hB))
            (fun B hB => domsIn B (List.mem_cons_of_mem _ hB)) setsTail viewsTail
          exact congrArg₂ List.cons headEq tailEq

theorem codeOf_injective {sig : Signature.{u}} {x y : ZFSet.{u}}
    (hx : InCarrier sig x) (hy : InCarrier sig y) (h : codeOf sig x = codeOf sig y) : x = y :=
  InCarrier.rec
    (motive_1 := fun x' _ => ∀ y', InCarrier sig y' → codeOf sig x' = codeOf sig y' → x' = y')
    (motive_2 := fun c args _ => SubInj sig c args)
    (fun {i c args} atIndex fitting sub z hz hcode => by
      cases hz with
      | intro atJ fitting' =>
          rw [codeOf_assembled atIndex fitting, codeOf_assembled atJ fitting'] at hcode
          have roots := congrArg (fun t => traceApp t (encode (a := moveSet sig) [])) hcode
          rw [traceApp_assembled_nil, traceApp_assembled_nil] at roots
          obtain ⟨hi, hsets⟩ := presentLabel_injective roots
          cases hi
          have ctorEq : _ = c := Option.some_inj.mp (atJ.symm.trans atIndex)
          cases ctorEq
          have hc : c ∈ sig := mem_of_get? atIndex
          have argsEq := args_eq fitting fitting' sub
            (fun A hA => ofSet_subset_dataBound hc hA)
            (fun A hA => ofFun_subset_payloadBody hc hA) hsets
            (views_of_assembled hcode (resultAt_code_trace fitting)
              (resultAt_code_trace fitting'))
          cases argsEq
          rfl)
    ⟨fun _ hy => by cases hy⟩
    (fun _ _ subA subRest => ⟨fun y hy z hz hcode => by
      cases hy with
      | recHere => exact subA z hz hcode
      | skip hskip => exact subRest.inj y hskip z hz hcode⟩)
    (fun _ _ subRest => ⟨fun y hy z hz hcode => by
      cases hy with
      | skip hskip => exact subRest.inj y hskip z hz hcode⟩)
    (fun _ _ _ ihValues subRest => ⟨fun y hy z hz hcode => by
      cases hy with
      | funHere hb => exact ihValues _ hb z hz hcode
      | skip hskip => exact subRest.inj y hskip z hz hcode⟩)
    hx y hy h

/-! ## The code of a generated element lies in the code space -/

theorem codeOf_mem_codeSpace {sig : Signature.{u}} {x : ZFSet.{u}} (hx : InCarrier sig x) :
    codeOf sig x ∈ codeSpace sig :=
  InCarrier.rec
    (motive_1 := fun y _ => codeOf sig y ∈ codeSpace sig)
    (motive_2 := fun c args _ => ∀ k payload,
      resultAt sig (mapResults (codeOf sig) c args) c k payload ∈ codeSpace sig)
    (fun {i c args} atIndex fitting labelsMem => by
      rw [codeOf_assembled atIndex fitting]
      refine mem_tracePiSet_of_total ?_ ?_
      · conv_lhs => unfold assembled
        apply congrArg traceLam
        apply graph_congr
        intro p hp
        rw [assembled, traceApp_graph_beta _ hp]
      · intro p hp
        obtain ⟨xs, rfl⟩ := mem_listCode.mp hp
        unfold assembled
        rw [traceApp_graph_beta _ hp, labelAt_encode]
        cases xs with
        | nil => exact presentLabel_mem sig i (setArgs sig c args)
        | cons m rest =>
            exact traceApp_mem
              ⟨resultAt sig (mapResults (codeOf sig) c args) c
                  (natOf (moveIndex m.1)) (movePayload m.1),
                labelsMem _ _⟩
              ⟨encode rest, ZFSet.mem_range_self rest⟩)
    (fun k payload => by
      rw [mapResults_nil, resultAt_nil]
      exact absentCode_mem sig)
    (fun _ _ childMem restMem k payload => by
      cases k with
      | zero =>
          rw [mapResults_recursive, resultAt_rec_zero]
          exact childMem
      | succ k =>
          rw [mapResults_recursive, resultAt_rec_succ]
          exact restMem k payload)
    (fun _ _ restMem k payload => by
      cases k with
      | zero =>
          rw [mapResults_ofSet, resultAt_set_zero]
          exact absentCode_mem sig
      | succ k =>
          rw [mapResults_ofSet, resultAt_set_succ]
          exact restMem k payload)
    (fun {A _fs _args _f} _ _ _ ihValues restMem => by
      intro k payload
      cases k with
      | zero =>
          cases Classical.propDecidable (payload ∈ A) with
          | isTrue hmem =>
              rw [mapResults_ofFun, resultAt_fun_pos sig _ _ A _ payload hmem,
                traceApp_graph_beta _ hmem]
              exact ihValues payload hmem
          | isFalse hmem =>
              rw [mapResults_ofFun, resultAt_fun_neg sig _ _ A _ payload hmem]
              exact absentCode_mem sig
      | succ k =>
          rw [mapResults_ofFun, resultAt_fun_succ]
          exact restMem k payload)
    hx

/-! ## The carrier -/

noncomputable def codeSet (sig : Signature.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun c => ∃ x, InCarrier sig x ∧ codeOf sig x = c) (codeSpace sig)

noncomputable def decodeTarget (sig : Signature.{u}) (c : ZFSet.{u}) : ZFSet.{u} :=
  @Classical.epsilon ZFSet.{u} ⟨∅⟩ (fun x => InCarrier sig x ∧ codeOf sig x = c)

noncomputable def carrier (sig : Signature.{u}) : ZFSet.{u} :=
  replacement (codeSet sig) (decodeTarget sig)

theorem decodeTarget_codeOf {sig : Signature.{u}} {x : ZFSet.{u}} (hx : InCarrier sig x) :
    decodeTarget sig (codeOf sig x) = x := by
  have spec := Classical.epsilon_spec_aux ⟨(∅ : ZFSet.{u})⟩
    (fun y => InCarrier sig y ∧ codeOf sig y = codeOf sig x) ⟨x, hx, rfl⟩
  exact codeOf_injective spec.1 hx spec.2

theorem mem_carrier_of_inCarrier {sig : Signature.{u}} {x : ZFSet.{u}}
    (hx : InCarrier sig x) : x ∈ carrier sig := by
  refine mem_replacement.mpr ⟨codeOf sig x, ?_, decodeTarget_codeOf hx⟩
  exact ZFSet.mem_sep.mpr ⟨codeOf_mem_codeSpace hx, x, hx, rfl⟩

theorem inCarrier_of_mem_carrier {sig : Signature.{u}} {x : ZFSet.{u}}
    (hx : x ∈ carrier sig) : InCarrier sig x := by
  obtain ⟨c, hc, rfl⟩ := mem_replacement.mp hx
  obtain ⟨_, ⟨y, hy, rfl⟩⟩ := ZFSet.mem_sep.mp hc
  rw [decodeTarget_codeOf hy]
  exact hy

theorem mem_carrier_iff {sig : Signature.{u}} {x : ZFSet.{u}} :
    x ∈ carrier sig ↔ InCarrier sig x :=
  ⟨inCarrier_of_mem_carrier, mem_carrier_of_inCarrier⟩

theorem deriv_of_fits {sig : Signature.{u}} {c : Constructor} {args : List ZFSet.{u}}
    (fitting : Fits (carrier sig) c args) : Deriv sig c args := by
  induction fitting with
  | nil => exact Deriv.nil
  | recursive member _ ih => exact Deriv.recursive (inCarrier_of_mem_carrier member) ih
  | ofSet member _ ih => exact Deriv.ofSet member ih
  | ofFun member _ ih =>
      obtain ⟨total, values⟩ := total_of_mem_tracePiSet member
      exact Deriv.ofFun total (fun a ha => inCarrier_of_mem_carrier (values a ha)) ih

theorem fitsPred_in_carrier {sig : Signature.{u}} {c : Constructor} {args : List ZFSet.{u}}
    (fitting : FitsPred (InCarrier sig) c args) :
    FitsPred (fun a => a ∈ carrier sig) c args :=
  match fitting with
  | .nil => FitsPred.nil
  | .recursive member rest =>
      FitsPred.recursive (mem_carrier_of_inCarrier member) (fitsPred_in_carrier rest)
  | .ofSet member rest => FitsPred.ofSet member (fitsPred_in_carrier rest)
  | .ofFun total values rest =>
      FitsPred.ofFun total (fun a ha => mem_carrier_of_inCarrier (values a ha))
        (fitsPred_in_carrier rest)

/-- The carrier is closed under constructor values at fitting arguments. -/
theorem carrier_closed {sig : Signature.{u}} {i : Nat} {c : Constructor} {args : List ZFSet.{u}}
    (atIndex : sig[i]? = some c) (fitting : Fits (carrier sig) c args) :
    constructorValue (numeral i) args ∈ carrier sig :=
  mem_carrier_of_inCarrier (InCarrier.intro atIndex (deriv_of_fits fitting))

/-- The carrier is contained in every set closed under the constructors. -/
theorem carrier_least {sig : Signature.{u}} {X : ZFSet.{u}}
    (closedX : ∀ {i : Nat} {c : Constructor} {args : List ZFSet.{u}},
      sig[i]? = some c → Fits X c args → constructorValue (numeral i) args ∈ X) :
    carrier sig ⊆ X := by
  intro x hx
  exact inCarrier_induct (fun atIndex fitting => closedX atIndex (fits_of_fitsPred fitting))
    (inCarrier_of_mem_carrier hx)

/-- A property preserved by constructor values holds on the carrier. -/
theorem carrier_induct {sig : Signature.{u}} {P : ZFSet.{u} → Prop}
    (step : ∀ {i : Nat} {c : Constructor} {args : List ZFSet.{u}},
      sig[i]? = some c → FitsPred P c args → P (constructorValue (numeral i) args))
    {x : ZFSet.{u}} (hx : x ∈ carrier sig) : P x :=
  inCarrier_induct step (inCarrier_of_mem_carrier hx)

/-- Every member is one constructor value at one fitting argument list. -/
theorem exists_inversion {sig : Signature.{u}} {x : ZFSet.{u}} (hx : x ∈ carrier sig) :
    ∃ i c args, sig[i]? = some c ∧ Fits (carrier sig) c args ∧
      constructorValue (numeral i) args = x := by
  cases inCarrier_of_mem_carrier hx with
  | intro atIndex fitting =>
      exact ⟨_, _, _, atIndex, fits_of_fitsPred (fitsPred_in_carrier (deriv_fitsPred fitting)), rfl⟩

theorem inversion_unique {sig : Signature.{u}} {x : ZFSet.{u}} {i j : Nat}
    {c d : Constructor} {args args' : List ZFSet.{u}}
    (atI : sig[i]? = some c) (atJ : sig[j]? = some d)
    (left : constructorValue (numeral i) args = x)
    (right : constructorValue (numeral j) args' = x) :
    i = j ∧ c = d ∧ args = args' := by
  have equal := left.trans right.symm
  obtain ⟨hi, ha⟩ := constructorValue_injective.mp equal
  cases numeral_injective hi
  cases ha
  exact ⟨rfl, Option.some_inj.mp (atI.symm.trans atJ), rfl⟩

/-- Computation: at a constructor value the recursion returns the method's value. -/
theorem recursion_constructor {sig : Signature.{u}}
    (step : Nat → List ZFSet.{u} → List ZFSet.{u} → ZFSet.{u})
    {i : Nat} {c : Constructor} {args : List ZFSet.{u}}
    (atIndex : sig[i]? = some c) (fitting : Fits (carrier sig) c args) :
    recFun sig step (constructorValue (numeral i) args) =
      step i args (mapResults (recFun sig step) c args) :=
  recFun_constructor sig step atIndex (deriv_of_fits fitting)

/-- A function that satisfies the constructor equations agrees with the recursion. -/
theorem recursion_unique {sig : Signature.{u}}
    (step : Nat → List ZFSet.{u} → List ZFSet.{u} → ZFSet.{u})
    (g : ZFSet.{u} → ZFSet.{u})
    (equations : ∀ {i : Nat} {c : Constructor} {args : List ZFSet.{u}},
      sig[i]? = some c → Fits (carrier sig) c args →
        g (constructorValue (numeral i) args) = step i args (mapResults g c args))
    {x : ZFSet.{u}} (hx : x ∈ carrier sig) : g x = recFun sig step x :=
  recFun_unique sig step g
    (fun atIndex fitting => equations atIndex
      (fits_of_fitsPred (fitsPred_in_carrier (deriv_fitsPred fitting))))
    (inCarrier_of_mem_carrier hx)

/-! ## The carrier belongs to a closed universe -/

theorem finiteRankIndex_mem_of_omega {U : ZFSet.{u}} (closed : Closed U)
    (omega : ZFSet.omega ∈ U) : finiteRankIndex ∈ U :=
  range_mem_of_index closed numeral numeral_injective (by rw [range_numeral]; exact omega)
    finiteRank fun n => finiteRankStage_mem closed (closed.empty_mem omega) n

theorem ofSet_of_mem_constructorSets {c : Constructor} {A : ZFSet.{u}}
    (h : A ∈ constructorSets c) : Field.ofSet A ∈ c := by
  induction c with
  | nil => cases h
  | cons field fs ih =>
      have hsplit : constructorSets (field :: fs) = fieldSets field ++ constructorSets fs := rfl
      rw [hsplit] at h
      rcases List.mem_append.mp h with hfield | hrest
      · cases field with
        | recursive =>
            have hempty : fieldSets Field.recursive = [] := rfl
            rw [hempty] at hfield
            cases hfield
        | ofSet B =>
            have hset : fieldSets (Field.ofSet B) = [B] := rfl
            rw [hset] at hfield
            cases List.mem_cons.mp hfield with
            | inl heq =>
                cases heq
                exact List.mem_cons_self
            | inr htail => cases htail
        | ofFun B =>
            have hempty : fieldSets (Field.ofFun B) = [] := rfl
            rw [hempty] at hfield
            cases hfield
      · exact List.mem_cons_of_mem _ (ih hrest)

theorem ofFun_of_mem_constructorDomains {c : Constructor} {A : ZFSet.{u}}
    (h : A ∈ constructorDomains c) : Field.ofFun A ∈ c := by
  induction c with
  | nil => cases h
  | cons field fs ih =>
      have hsplit : constructorDomains (field :: fs) =
          fieldDomains field ++ constructorDomains fs := rfl
      rw [hsplit] at h
      rcases List.mem_append.mp h with hfield | hrest
      · cases field with
        | recursive =>
            have hempty : fieldDomains Field.recursive = [] := rfl
            rw [hempty] at hfield
            cases hfield
        | ofSet B =>
            have hempty : fieldDomains (Field.ofSet B) = [] := rfl
            rw [hempty] at hfield
            cases hfield
        | ofFun B =>
            have hdom : fieldDomains (Field.ofFun B) = [B] := rfl
            rw [hdom] at hfield
            cases List.mem_cons.mp hfield with
            | inl heq =>
                cases heq
                exact List.mem_cons_self
            | inr htail => cases htail
      · exact List.mem_cons_of_mem _ (ih hrest)

theorem signatureSet_mem {sig : Signature.{u}} {U : ZFSet.{u}}
    (fields : ∀ c, c ∈ sig → ∀ A, Field.ofSet A ∈ c → A ∈ U)
    {A : ZFSet.{u}} (h : A ∈ signatureSets sig) : A ∈ U := by
  induction sig with
  | nil => cases h
  | cons c cs ih =>
      have happ : signatureSets (c :: cs) = constructorSets c ++ signatureSets cs := rfl
      rw [happ] at h
      rcases List.mem_append.mp h with hc | hcs
      · exact fields c List.mem_cons_self _ (ofSet_of_mem_constructorSets hc)
      · exact ih (fun d hd => fields d (List.mem_cons_of_mem _ hd)) hcs

theorem signatureDomain_mem {sig : Signature.{u}} {U : ZFSet.{u}}
    (fields : ∀ c, c ∈ sig → ∀ A, Field.ofFun A ∈ c → A ∈ U)
    {A : ZFSet.{u}} (h : A ∈ signatureDomains sig) : A ∈ U := by
  induction sig with
  | nil => cases h
  | cons c cs ih =>
      have happ : signatureDomains (c :: cs) =
          constructorDomains c ++ signatureDomains cs := rfl
      rw [happ] at h
      rcases List.mem_append.mp h with hc | hcs
      · exact fields c List.mem_cons_self _ (ofFun_of_mem_constructorDomains hc)
      · exact ih (fun d hd => fields d (List.mem_cons_of_mem _ hd)) hcs

theorem unionList_mem {U : ZFSet.{u}} (closed : Closed U) (omega : ZFSet.omega ∈ U) :
    ∀ as : List ZFSet.{u}, (∀ a, a ∈ as → a ∈ U) → unionList as ∈ U
  | [], _ => closed.empty_mem omega
  | a :: as, h =>
      closed.binaryUnion_mem (h a List.mem_cons_self)
        (unionList_mem closed omega as (fun b hb => h b (List.mem_cons_of_mem a hb)))

theorem dataBound_mem {sig : Signature.{u}} {U : ZFSet.{u}} (closed : Closed U)
    (omega : ZFSet.omega ∈ U)
    (sets : ∀ c, c ∈ sig → ∀ A, Field.ofSet A ∈ c → A ∈ U) : dataBound sig ∈ U :=
  unionList_mem closed omega (signatureSets sig) fun _ hA => signatureSet_mem sets hA

theorem payloadBody_mem {sig : Signature.{u}} {U : ZFSet.{u}} (closed : Closed U)
    (omega : ZFSet.omega ∈ U)
    (domains : ∀ c, c ∈ sig → ∀ A, Field.ofFun A ∈ c → A ∈ U) : payloadBody sig ∈ U :=
  unionList_mem closed omega (signatureDomains sig) fun _ hA => signatureDomain_mem domains hA

theorem payloadSet_mem {sig : Signature.{u}} {U : ZFSet.{u}} (closed : Closed U)
    (omega : ZFSet.omega ∈ U)
    (domains : ∀ c, c ∈ sig → ∀ A, Field.ofFun A ∈ c → A ∈ U) : payloadSet sig ∈ U := by
  rw [payloadSet, ZFSet.insert_eq]
  exact closed.binaryUnion_mem (closed.singleton_mem (closed.empty_mem omega))
    (payloadBody_mem closed omega domains)

theorem tagIndex_mem {U : ZFSet.{u}} (closed : Closed U) (omega : ZFSet.omega ∈ U) :
    tagIndex ∈ U :=
  closed.product_mem
    (closed.unorderedPair_mem (numeral_mem_of_omega closed omega 0)
      (numeral_mem_of_omega closed omega 1))
    omega

theorem moveSet_mem {sig : Signature.{u}} {U : ZFSet.{u}} (closed : Closed U)
    (omega : ZFSet.omega ∈ U)
    (domains : ∀ c, c ∈ sig → ∀ A, Field.ofFun A ∈ c → A ∈ U) : moveSet sig ∈ U :=
  closed.product_mem (tagIndex_mem closed omega) (payloadSet_mem closed omega domains)

theorem paths_mem {sig : Signature.{u}} {U : ZFSet.{u}} (closed : Closed U)
    (omega : ZFSet.omega ∈ U)
    (domains : ∀ c, c ∈ sig → ∀ A, Field.ofFun A ∈ c → A ∈ U) : paths sig ∈ U :=
  ZFSetListClosure.listCode_mem closed (moveSet_mem closed omega domains)
    (finiteRankIndex_mem_of_omega closed omega)

theorem labelSet_mem {sig : Signature.{u}} {U : ZFSet.{u}} (closed : Closed U)
    (omega : ZFSet.omega ∈ U)
    (sets : ∀ c, c ∈ sig → ∀ A, Field.ofSet A ∈ c → A ∈ U) : labelSet sig ∈ U :=
  closed.product_mem omega
    (ZFSetListClosure.listCode_mem closed (dataBound_mem closed omega sets)
      (finiteRankIndex_mem_of_omega closed omega))

theorem codeSpace_mem {sig : Signature.{u}} {U : ZFSet.{u}} (closed : Closed U)
    (omega : ZFSet.omega ∈ U)
    (fields : ∀ c, c ∈ sig →
      (∀ A, Field.ofSet A ∈ c → A ∈ U) ∧ (∀ A, Field.ofFun A ∈ c → A ∈ U)) :
    codeSpace sig ∈ U :=
  closed.tracePiSet_mem (paths_mem closed omega fun c hc => (fields c hc).2)
    (fun _ => labelSet sig)
    fun _ _ => labelSet_mem closed omega fun c hc => (fields c hc).1

theorem decodeTarget_mem {sig : Signature.{u}} {U : ZFSet.{u}} (closed : Closed U)
    (omega : ZFSet.omega ∈ U)
    (fields : ∀ c, c ∈ sig →
      (∀ A, Field.ofSet A ∈ c → A ∈ U) ∧ (∀ A, Field.ofFun A ∈ c → A ∈ U))
    {c : ZFSet.{u}} (hc : c ∈ codeSet sig) : decodeTarget sig c ∈ U := by
  obtain ⟨_, hex⟩ := ZFSet.mem_sep.mp hc
  have spec := Classical.epsilon_spec_aux ⟨(∅ : ZFSet.{u})⟩
    (fun x => InCarrier sig x ∧ codeOf sig x = c) hex
  exact inCarrier_mem closed omega fields spec.1

/-- The carrier is a member of every closed universe that contains `ω`, every set
field, and every function-field domain. -/
theorem carrier_mem {sig : Signature.{u}} {U : ZFSet.{u}} (closed : Closed U)
    (omega : ZFSet.omega ∈ U)
    (fields : ∀ c, c ∈ sig →
      (∀ A, Field.ofSet A ∈ c → A ∈ U) ∧ (∀ A, Field.ofFun A ∈ c → A ∈ U)) :
    carrier sig ∈ U := by
  rw [carrier]
  refine closed.replacement_mem (closed.separation_mem (codeSpace_mem closed omega fields) _)
    (decodeTarget sig) fun c hc => decodeTarget_mem closed omega fields hc

/-! ## Signatures without function fields -/

def eraseField : Field.{u} → Option ZFSetInductive.Field.{u}
  | .recursive => some .recursive
  | .ofSet A => some (.ofSet A)
  | .ofFun _ => none

/-- The fields of a constructor without function fields. -/
def eraseConstructor : Constructor → Option (List ZFSetInductive.Field.{u})
  | [] => some []
  | .recursive :: fs =>
      match eraseConstructor fs with
      | some fs' => some (ZFSetInductive.Field.recursive :: fs')
      | none => none
  | .ofSet A :: fs =>
      match eraseConstructor fs with
      | some fs' => some (ZFSetInductive.Field.ofSet A :: fs')
      | none => none
  | .ofFun _ :: _ => none

/-- The simple signature of a signature without function fields, its constructors numbered
from `k`: constructor `j` carries the numeral of `k + j` as its tag. -/
def eraseSignatureFrom (k : Nat) : Signature.{u} → Option ZFSetInductive.Signature.{u}
  | [] => some []
  | c :: cs =>
      match eraseConstructor c, eraseSignatureFrom (k + 1) cs with
      | some fs, some cs' => some (⟨numeral k, fs⟩ :: cs')
      | _, _ => none

/-- The simple signature of a signature without function fields: constructor `i` carries
the numeral of `i` as its tag. -/
def eraseSignature (sig : Signature.{u}) : Option ZFSetInductive.Signature.{u} :=
  eraseSignatureFrom 0 sig

theorem eraseConstructor_nil : eraseConstructor [] = some [] := rfl

theorem eraseConstructor_recursive (fs : Constructor) :
    eraseConstructor (Field.recursive :: fs) =
      match eraseConstructor fs with
      | some fs' => some (ZFSetInductive.Field.recursive :: fs')
      | none => none := rfl

theorem eraseConstructor_ofSet (A : ZFSet.{u}) (fs : Constructor) :
    eraseConstructor (Field.ofSet A :: fs) =
      match eraseConstructor fs with
      | some fs' => some (ZFSetInductive.Field.ofSet A :: fs')
      | none => none := rfl

theorem eraseConstructor_ofFun (A : ZFSet.{u}) (fs : Constructor) :
    eraseConstructor (Field.ofFun A :: fs) = none := rfl

theorem eraseSignatureFrom_nil (k : Nat) : eraseSignatureFrom k [] = some [] := rfl

theorem eraseSignatureFrom_cons (k : Nat) (c : Constructor) (cs : Signature.{u}) :
    eraseSignatureFrom k (c :: cs) =
      match eraseConstructor c, eraseSignatureFrom (k + 1) cs with
      | some fs, some cs' => some (⟨numeral k, fs⟩ :: cs')
      | _, _ => none := rfl

theorem fits_to_simple {X : ZFSet.{u}} {c : Constructor} {args : List ZFSet.{u}}
    {c' : List ZFSetInductive.Field.{u}} (fitting : Fits X c args)
    (erased : eraseConstructor c = some c') : ZFSetInductive.Fits X c' args :=
  match fitting with
  | .nil => by
      cases erased
      exact ZFSetInductive.Fits.nil
  | .recursive (fs := fs) member rest => by
      rw [eraseConstructor_recursive] at erased
      match htail : eraseConstructor fs with
      | none =>
          rw [htail] at erased
          cases erased
      | some fs' =>
          rw [htail] at erased
          cases erased
          exact ZFSetInductive.Fits.recursive member (fits_to_simple rest htail)
  | .ofSet (fs := fs) member rest => by
      rw [eraseConstructor_ofSet] at erased
      match htail : eraseConstructor fs with
      | none =>
          rw [htail] at erased
          cases erased
      | some fs' =>
          rw [htail] at erased
          cases erased
          exact ZFSetInductive.Fits.ofSet member (fits_to_simple rest htail)
  | .ofFun _ _ => by
      rw [eraseConstructor_ofFun] at erased
      cases erased

theorem fits_from_simple {X : ZFSet.{u}} {c' : List ZFSetInductive.Field.{u}}
    {args : List ZFSet.{u}} (fitting : ZFSetInductive.Fits X c' args) {c : Constructor}
    (erased : eraseConstructor c = some c') : Fits X c args :=
  match fitting with
  | .nil => by
      match c, erased with
      | [], erased =>
          cases erased
          exact Fits.nil
      | .recursive :: fs, erased =>
          rw [eraseConstructor_recursive] at erased
          match hfs : eraseConstructor fs with
          | none =>
              rw [hfs] at erased
              cases erased
          | some _ =>
              rw [hfs] at erased
              injection erased with heq
              cases heq
      | .ofSet _ :: fs, erased =>
          rw [eraseConstructor_ofSet] at erased
          match hfs : eraseConstructor fs with
          | none =>
              rw [hfs] at erased
              cases erased
          | some _ =>
              rw [hfs] at erased
              injection erased with heq
              cases heq
      | .ofFun _ :: _, erased =>
          rw [eraseConstructor_ofFun] at erased
          cases erased
  | .recursive member rest => by
      match c, erased with
      | [], erased =>
          rw [eraseConstructor_nil] at erased
          cases erased
      | .recursive :: fs, erased =>
          rw [eraseConstructor_recursive] at erased
          match hfs : eraseConstructor fs with
          | none =>
              rw [hfs] at erased
              cases erased
          | some _ =>
              rw [hfs] at erased
              injection erased with heq
              injection heq with _ htail
              cases htail
              exact Fits.recursive member (fits_from_simple rest hfs)
      | .ofSet _ :: fs, erased =>
          rw [eraseConstructor_ofSet] at erased
          match hfs : eraseConstructor fs with
          | none =>
              rw [hfs] at erased
              cases erased
          | some _ =>
              rw [hfs] at erased
              injection erased with heq
              injection heq with hfield _
              cases hfield
      | .ofFun _ :: _, erased =>
          rw [eraseConstructor_ofFun] at erased
          cases erased
  | .ofSet member rest => by
      match c, erased with
      | [], erased =>
          rw [eraseConstructor_nil] at erased
          cases erased
      | .recursive :: fs, erased =>
          rw [eraseConstructor_recursive] at erased
          match hfs : eraseConstructor fs with
          | none =>
              rw [hfs] at erased
              cases erased
          | some _ =>
              rw [hfs] at erased
              injection erased with heq
              injection heq with hfield _
              cases hfield
      | .ofSet _ :: fs, erased =>
          rw [eraseConstructor_ofSet] at erased
          match hfs : eraseConstructor fs with
          | none =>
              rw [hfs] at erased
              cases erased
          | some _ =>
              rw [hfs] at erased
              injection erased with heq
              injection heq with hfield htail
              cases hfield
              cases htail
              exact Fits.ofSet member (fits_from_simple rest hfs)
      | .ofFun _ :: _, erased =>
          rw [eraseConstructor_ofFun] at erased
          cases erased

theorem eraseFrom_atIndex {k : Nat} {sig : Signature.{u}} {sig' : ZFSetInductive.Signature.{u}}
    (h : eraseSignatureFrom k sig = some sig') {i : Nat} {c : Constructor}
    (atIndex : sig[i]? = some c) :
    ∃ fs, sig'[i]? = some ⟨numeral (k + i), fs⟩ ∧ eraseConstructor c = some fs := by
  induction sig generalizing k sig' i with
  | nil => cases atIndex
  | cons head tail ih =>
      rw [eraseSignatureFrom_cons] at h
      match hc : eraseConstructor head, ht : eraseSignatureFrom (k + 1) tail with
      | none, _ =>
          rw [hc] at h
          cases h
      | some _, none =>
          rw [hc, ht] at h
          cases h
      | some head', some tail' =>
          rw [hc, ht] at h
          cases h
          cases i with
          | zero =>
              cases atIndex
              exact ⟨head', rfl, hc⟩
          | succ i =>
              obtain ⟨fs, atTail, herase⟩ := ih ht (atIndex : tail[i]? = some c)
              refine ⟨fs, ?_, herase⟩
              rw [show k + (i + 1) = k + 1 + i by omega]
              exact atTail

theorem eraseFrom_atIndex_symm {k : Nat} {sig : Signature.{u}}
    {sig' : ZFSetInductive.Signature.{u}} (h : eraseSignatureFrom k sig = some sig') {i : Nat}
    {c' : ZFSetInductive.Constructor.{u}} (atIndex : sig'[i]? = some c') :
    ∃ c, sig[i]? = some c ∧ eraseConstructor c = some c'.fields ∧ c'.tag = numeral (k + i) := by
  induction sig generalizing k sig' i with
  | nil =>
      cases h
      cases atIndex
  | cons head tail ih =>
      rw [eraseSignatureFrom_cons] at h
      match hc : eraseConstructor head, ht : eraseSignatureFrom (k + 1) tail with
      | none, _ =>
          rw [hc] at h
          cases h
      | some _, none =>
          rw [hc, ht] at h
          cases h
      | some head', some tail' =>
          rw [hc, ht] at h
          cases h
          cases i with
          | zero =>
              cases atIndex
              exact ⟨head, rfl, hc, rfl⟩
          | succ i =>
              obtain ⟨c, atTail, herase, tag⟩ := ih ht (atIndex : tail'[i]? = some c')
              refine ⟨c, atTail, herase, ?_⟩
              rw [tag, show k + (i + 1) = k + 1 + i by omega]

/-- Without function fields the carrier is the carrier of the erased simple signature. -/
theorem carrier_eq_of_erase {sig : Signature.{u}} {sig' : ZFSetInductive.Signature.{u}}
    (h : eraseSignature sig = some sig') : carrier sig = ZFSetInductive.carrier sig' := by
  apply ZFSet.ext
  intro x
  constructor
  · intro hx
    exact carrier_least (fun {i _ _} atIndex fitting => by
      obtain ⟨fs, at', erased⟩ := eraseFrom_atIndex h atIndex
      have member := ZFSetInductive.constructor_mem_carrier at'
        (fits_to_simple fitting erased)
      rwa [Nat.zero_add] at member) hx
  · intro hx
    exact ZFSetInductive.carrier_subset_of_closed (fun i c' args present fitting => by
      obtain ⟨c, atC, erased, tag⟩ := eraseFrom_atIndex_symm h present
      rw [tag, Nat.zero_add]
      exact carrier_closed atC (fits_from_simple fitting erased)) hx

/-! ## Ordinal notations: zero, successor, and a limit over `ω` -/

namespace OrdinalNotation

def ordSignature : Signature.{u} :=
  [[], [Field.recursive], [Field.ofFun ZFSet.omega]]

def zero : ZFSet.{u} := constructorValue (numeral 0) []

def suc (x : ZFSet.{u}) : ZFSet.{u} := constructorValue (numeral 1) [x]

def limit (f : ZFSet.{u}) : ZFSet.{u} := constructorValue (numeral 2) [f]

def sucIter : Nat → ZFSet.{u}
  | 0 => zero
  | n + 1 => suc (sucIter n)

noncomputable def towerFun : ZFSet.{u} :=
  traceLam (graph ZFSet.omega (fun x => sucIter (natOf x)))

theorem towerFun_beta {x : ZFSet.{u}} (hx : x ∈ ZFSet.omega) :
    traceApp towerFun x = sucIter (natOf x) := by
  rw [towerFun]
  exact traceApp_graph_beta (fun y => sucIter (natOf y)) hx

theorem towerFun_total :
    towerFun = traceLam (graph ZFSet.omega (fun b => traceApp towerFun b)) := by
  rw [towerFun]
  apply congrArg traceLam
  apply graph_congr
  intro x hx
  exact (traceApp_graph_beta (fun y => sucIter (natOf y)) hx).symm

theorem sucIter_mem : ∀ n, sucIter n ∈ carrier ordSignature
  | 0 => carrier_closed rfl Fits.nil
  | n + 1 => carrier_closed rfl (Fits.recursive (sucIter_mem n) Fits.nil)

theorem towerFun_mem_pi :
    towerFun ∈ tracePiSet ZFSet.omega (fun _ => carrier ordSignature) :=
  mem_tracePiSet_of_total towerFun_total fun a ha => by
    rw [towerFun_beta ha]
    exact sucIter_mem (natOf a)

theorem limit_mem : limit towerFun ∈ carrier ordSignature :=
  carrier_closed rfl (Fits.ofFun towerFun_mem_pi Fits.nil)

def heightStep (i : Nat) (_args recs : List ZFSet.{u}) : ZFSet.{u} :=
  match i with
  | 0 => numeral 0
  | 1 =>
      match recs with
      | [] => ∅
      | r :: _ => insert r r
  | 2 =>
      match recs with
      | [] => ∅
      | f :: _ => f
  | _ => ∅

noncomputable def height (x : ZFSet.{u}) : ZFSet.{u} := recFun ordSignature heightStep x

theorem heightStep_zero (args recs : List ZFSet.{u}) :
    heightStep 0 args recs = numeral 0 := rfl

theorem heightStep_suc (x r : ZFSet.{u}) (rs : List ZFSet.{u}) :
    heightStep 1 [x] (r :: rs) = insert r r := rfl

theorem heightStep_limit (f g : ZFSet.{u}) (gs : List ZFSet.{u}) :
    heightStep 2 [f] (g :: gs) = g := rfl

theorem height_zero : height zero = numeral 0 := by
  rw [height, zero, recursion_constructor heightStep rfl Fits.nil, mapResults_nil,
    heightStep_zero]

theorem height_suc (x : ZFSet.{u}) (hx : x ∈ carrier ordSignature) :
    height (suc x) = insert (height x) (height x) := by
  rw [height, suc, recursion_constructor heightStep rfl (Fits.recursive hx Fits.nil),
    mapResults_recursive, heightStep_suc, height]

theorem height_sucIter : ∀ n, height (sucIter n) = numeral n
  | 0 => height_zero
  | n + 1 => by
      rw [sucIter, height_suc (sucIter n) (sucIter_mem n), height_sucIter n, numeral_succ]

theorem height_limit :
    height (limit towerFun) =
      traceLam (graph ZFSet.omega (fun a => numeral (natOf a))) := by
  rw [height, limit, recursion_constructor heightStep rfl
      (Fits.ofFun towerFun_mem_pi Fits.nil), mapResults_ofFun, mapResults_nil,
    heightStep_limit]
  apply congrArg traceLam
  apply graph_congr
  intro a ha
  rw [towerFun_beta ha, ← height, height_sucIter]

/-! ### The finite iterates do not contain the limit -/

noncomputable def ordStep (X : ZFSet.{u}) : ZFSet.{u} :=
  ({zero} : ZFSet.{u}) ∪
    (replacement X suc ∪ replacement (tracePiSet ZFSet.omega (fun _ => X)) limit)

noncomputable def ordIterate : Nat → ZFSet.{u}
  | 0 => ∅
  | n + 1 => ordStep (ordIterate n)

noncomputable def finiteUnion : ZFSet.{u} := ZFSet.sUnion (ZFSet.range ordIterate)

def Bounded : Nat → ZFSet.{u} → Prop
  | 0, _ => False
  | n + 1, x =>
      x = zero ∨ (∃ y, x = suc y ∧ Bounded n y) ∨
        ∃ f, x = limit f ∧ ∀ a, a ∈ ZFSet.omega → Bounded n (traceApp f a)

theorem zero_ne_suc (y : ZFSet.{u}) : zero ≠ suc y :=
  fun h => Nat.succ_ne_zero 0 (numeral_injective (constructorValue_tag h)).symm

theorem zero_ne_limit (f : ZFSet.{u}) : zero ≠ limit f :=
  fun h => Nat.succ_ne_zero 1 (numeral_injective (constructorValue_tag h)).symm

theorem suc_ne_limit (y f : ZFSet.{u}) : suc y ≠ limit f :=
  fun h => Nat.succ_ne_zero 0
    (Nat.succ_injective (numeral_injective (constructorValue_tag h))).symm

theorem ordIterate_bounded : ∀ n x, x ∈ ordIterate n → Bounded n x
  | 0, x, hx => (ZFSet.notMem_empty x hx).elim
  | n + 1, x, hx => by
      rw [ordIterate, ordStep] at hx
      rcases ZFSet.mem_union.mp hx with hzero | hrest
      · exact Or.inl (ZFSet.mem_singleton.mp hzero)
      · rcases ZFSet.mem_union.mp hrest with hsuc | hlim
        · obtain ⟨y, hy, rfl⟩ := mem_replacement.mp hsuc
          exact Or.inr (Or.inl ⟨y, rfl, ordIterate_bounded n y hy⟩)
        · obtain ⟨f, hf, rfl⟩ := mem_replacement.mp hlim
          exact Or.inr (Or.inr ⟨f, rfl, fun a ha =>
            ordIterate_bounded n _ (traceApp_mem ⟨f, hf⟩ ⟨a, ha⟩)⟩)

theorem sucIter_not_bounded : ∀ n, ¬ Bounded n (sucIter n)
  | 0, h => h
  | n + 1, h => by
      rcases h with hzero | hsuc | hlim
      · exact zero_ne_suc _ hzero.symm
      · obtain ⟨y, hy, hyb⟩ := hsuc
        exact sucIter_not_bounded n
          ((List.cons.inj (constructorValue_args hy)).1.symm ▸ hyb)
      · obtain ⟨f, hf, _⟩ := hlim
        exact suc_ne_limit _ f hf

theorem limit_not_bounded : ∀ n, ¬ Bounded n (limit towerFun)
  | 0, h => h
  | n + 1, h => by
      rcases h with hzero | hsuc | hlim
      · exact zero_ne_limit _ hzero.symm
      · obtain ⟨y, hy, _⟩ := hsuc
        exact suc_ne_limit y _ hy.symm
      · obtain ⟨f, hf, happ⟩ := hlim
        have hfEq : towerFun = f := (List.cons.inj (constructorValue_args hf)).1
        have hb := happ (numeral n) (numeral_mem_omega n)
        rw [← hfEq, towerFun_beta (numeral_mem_omega n), natOf_numeral] at hb
        exact sucIter_not_bounded n hb

theorem limit_not_mem_iterate (n : Nat) : limit towerFun ∉ ordIterate n :=
  fun h => limit_not_bounded n (ordIterate_bounded n _ h)

theorem sucIter_mem_iterate : ∀ n, sucIter n ∈ ordIterate (n + 1)
  | 0 => by
      rw [ordIterate, ordStep]
      exact ZFSet.mem_union.mpr (Or.inl (ZFSet.mem_singleton.mpr rfl))
  | n + 1 => by
      rw [sucIter, ordIterate, ordStep]
      exact ZFSet.mem_union.mpr (Or.inr (ZFSet.mem_union.mpr (Or.inl
        (mem_replacement.mpr ⟨sucIter n, sucIter_mem_iterate n, rfl⟩))))

theorem sucIter_mem_union (n : Nat) : sucIter n ∈ finiteUnion :=
  ZFSet.mem_sUnion.mpr ⟨ordIterate (n + 1), ZFSet.mem_range_self _, sucIter_mem_iterate n⟩

theorem towerFun_mem_union_pi :
    towerFun ∈ tracePiSet ZFSet.omega (fun _ => finiteUnion) :=
  mem_tracePiSet_of_total towerFun_total fun a ha => by
    rw [towerFun_beta ha]
    exact sucIter_mem_union (natOf a)

theorem limit_mem_step_union : limit towerFun ∈ ordStep finiteUnion := by
  rw [ordStep]
  exact ZFSet.mem_union.mpr (Or.inr (ZFSet.mem_union.mpr (Or.inr
    (mem_replacement.mpr ⟨towerFun, towerFun_mem_union_pi, rfl⟩))))

theorem limit_not_mem_union : limit towerFun ∉ finiteUnion := by
  intro h
  obtain ⟨s, hs, hx⟩ := ZFSet.mem_sUnion.mp h
  obtain ⟨n, rfl⟩ := ZFSet.mem_range.mp hs
  exact limit_not_mem_iterate n hx

theorem finite_iterates_not_closed :
    limit towerFun ∈ ordStep finiteUnion ∧ limit towerFun ∉ finiteUnion :=
  ⟨limit_mem_step_union, limit_not_mem_union⟩

/-! ### A closed universe containing the carrier contains the domain -/

theorem first_mem {U p : ZFSet.{u}} (closed : Closed U) (hp : p ∈ U) : first p ∈ U := by
  unfold first
  exact closed.union_mem (closed.separation_mem (closed.union_mem hp) _)

theorem sucIter_nonempty (k : Nat) : ∃ z, z ∈ sucIter k := by
  cases k with
  | zero => exact ⟨{numeral 0}, ZFSet.mem_pair.mpr (Or.inl rfl)⟩
  | succ _ => exact ⟨{numeral 1}, ZFSet.mem_pair.mpr (Or.inl rfl)⟩

theorem pair_mem_tower (k : Nat) : ∃ z, ZFSet.pair (numeral k) z ∈ towerFun := by
  obtain ⟨z, hz⟩ := sucIter_nonempty k
  refine ⟨z, ?_⟩
  rw [towerFun, traceLam_graph]
  exact mem_sigmaSet.mpr ⟨numeral k, numeral_mem_omega k, z,
    by rw [natOf_numeral]; exact hz, rfl⟩

theorem omega_eq_first_image : replacement towerFun first = ZFSet.omega := by
  apply ZFSet.ext
  intro x
  constructor
  · intro hx
    obtain ⟨p, hp, rfl⟩ := mem_replacement.mp hx
    rw [towerFun, traceLam_graph] at hp
    obtain ⟨y, hy, _, _, rfl⟩ := mem_sigmaSet.mp hp
    rw [first_pair]
    exact hy
  · intro hx
    obtain ⟨z, hz⟩ := pair_mem_tower (natOf x)
    rw [(numeral_natOf hx).symm]
    exact mem_replacement.mpr ⟨ZFSet.pair (numeral (natOf x)) z, hz, first_pair _ _⟩

theorem towerFun_mem_of_limit {U : ZFSet.{u}} (closed : Closed U)
    (h : limit towerFun ∈ U) : towerFun ∈ U := by
  have step1 : ({numeral 2, ZFSet.pair towerFun ∅} : ZFSet.{u}) ∈ U :=
    closed.transitive _ h (ZFSet.mem_pair.mpr (Or.inr rfl))
  have step2 : ZFSet.pair towerFun ∅ ∈ U :=
    closed.transitive _ step1 (ZFSet.mem_pair.mpr (Or.inr rfl))
  have step3 : ({towerFun} : ZFSet.{u}) ∈ U :=
    closed.transitive _ step2 (ZFSet.mem_pair.mpr (Or.inl rfl))
  exact closed.transitive _ step3 (ZFSet.mem_singleton.mpr rfl)

/-- Membership of this carrier in a closed universe forces the domain `ω` in. -/
theorem omega_of_carrier {U : ZFSet.{u}} (closed : Closed U)
    (h : carrier ordSignature ∈ U) : ZFSet.omega ∈ U := by
  have htower : towerFun ∈ U :=
    towerFun_mem_of_limit closed (closed.transitive _ h limit_mem)
  rw [← omega_eq_first_image]
  exact closed.replacement_mem htower first fun p hp =>
    first_mem closed (closed.transitive _ htower hp)

theorem carrier_not_mem_finiteSets : carrier ordSignature ∉ finiteSets :=
  fun member => omega_not_mem_finiteSets (omega_of_carrier finite_universe_closed member)

end OrdinalNotation

end Mettapedia.Logic.HOL.Embedding.ZFSetInductiveFunctions