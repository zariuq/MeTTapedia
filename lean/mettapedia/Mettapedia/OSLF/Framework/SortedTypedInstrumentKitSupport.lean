import Mettapedia.OSLF.Syntax.SortedCommutativeHereditaryWeight
import Mettapedia.OSLF.Framework.SortedTypedInstrumentContextSupport

/-!
# Actual hereditary support selected by a many-sorted instrument kit

Original constructors and designated AC1 operations retain their complete
source grammar. Each auxiliary bundle, probe and interaction constructor
requires its own head's kit permission. Support includes every stored child.
Its independently defined grammar is equivalent to zero missing-permission
weight, which descends through the actual local equations.

No inhabitant is supplied at an arbitrary source sort. Argument bundles and
fresh probes are supported only when their own instrument head is opened.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedTypedInstruments.Kit

open Mettapedia.OSLF.SortedCommutative
open scoped BigOperators

universe u v

variable {source : Mettapedia.OSLF.SortedConstructors.Signature.{u,v}}
  {Parallel : source.Srt → Prop}

abbrev Policy (source : Mettapedia.OSLF.SortedConstructors.Signature.{u,v})
    (Parallel : source.Srt → Prop) := SourceHead source Parallel → Prop

def instrumentHead : Probe source Parallel → SourceHead source Parallel
  | .ask head => head
  | .get head _ => head
  | .build head => head

def permissionWeight (opened : Policy source Parallel) (head : SourceHead source Parallel) : Nat := by
  classical
  exact if opened head then 0 else 1

theorem permissionWeight_zero_iff (opened : Policy source Parallel) (head : SourceHead source Parallel) :
    permissionWeight opened head = 0 ↔ opened head := by
  classical
  simp only [permissionWeight, ite_eq_left_iff, one_ne_zero, imp_false, not_not]

def constructorWeight (opened : Policy source Parallel) : Constructor source Parallel → Nat
  | .original _ => 0
  | .arguments head => permissionWeight opened head
  | .probe instrument => permissionWeight opened (instrumentHead instrument)
  | .cut instrument => permissionWeight opened (instrumentHead instrument)

inductive Allowed (opened : Policy source Parallel) : Constructor source Parallel → Prop where
  | original (constructor : source.Constructor) : Allowed opened (.original constructor)
  | arguments (head : SourceHead source Parallel) (permission : opened head) : Allowed opened (.arguments head)
  | probe (instrument : Probe source Parallel) (permission : opened (instrumentHead instrument)) :
      Allowed opened (.probe instrument)
  | cut (instrument : Probe source Parallel) (permission : opened (instrumentHead instrument)) :
      Allowed opened (.cut instrument)

theorem allowed_iff_weight_zero (opened : Policy source Parallel) (constructor : Constructor source Parallel) :
    Allowed opened constructor ↔ constructorWeight opened constructor = 0 := by
  cases constructor with
  | original constructor => exact ⟨fun _ => rfl, fun _ => .original constructor⟩
  | arguments head =>
    constructor
    · intro allowed
      cases allowed with
      | arguments _ permission => exact (permissionWeight_zero_iff opened head).mpr permission
    · exact fun zero => .arguments head ((permissionWeight_zero_iff opened head).mp zero)
  | probe instrument =>
    constructor
    · intro allowed
      cases allowed with
      | probe _ permission => exact (permissionWeight_zero_iff opened (instrumentHead instrument)).mpr permission
    · exact fun zero => .probe instrument ((permissionWeight_zero_iff opened (instrumentHead instrument)).mp zero)
  | cut instrument =>
    constructor
    · intro allowed
      cases allowed with
      | cut _ permission => exact (permissionWeight_zero_iff opened (instrumentHead instrument)).mpr permission
    · exact fun zero => .cut instrument ((permissionWeight_zero_iff opened (instrumentHead instrument)).mp zero)

inductive Supported (opened : Policy source Parallel) :
    {sort : Srt source Parallel} → Value (source := source) (Parallel := Parallel) sort → Prop where
  | zero {sort} (parallel : NativeParallel sort) : Supported opened (.zero parallel)
  | cut {sort} (parallel : NativeParallel sort)
      {first second : Value (source := source) (Parallel := Parallel) sort}
      (left : Supported opened first) (right : Supported opened second) :
      Supported opened (.cut parallel first second)
  | node {constructor : Constructor source Parallel}
      {arguments : (position : Fin ((signature source Parallel).arity constructor)) →
        Value (source := source) (Parallel := Parallel) ((signature source Parallel).input constructor position)}
      (allowed : Allowed opened constructor) (children : ∀ position, Supported opened (arguments position)) :
      Supported opened (.node (signature := signature source Parallel) (Parallel := NativeParallel) constructor arguments)

theorem Supported.weight_zero {opened : Policy source Parallel} {sort : Srt source Parallel}
    {supplied : Value (source := source) (Parallel := Parallel) sort} (supported : Supported opened supplied) :
    HereditaryWeight.term (constructorWeight opened) supplied = 0 := by
  induction supported with
  | zero => rfl
  | @cut sort parallel first second left right firstRead secondRead =>
    change HereditaryWeight.term (constructorWeight opened) first +
      HereditaryWeight.term (constructorWeight opened) second = 0
    rw [firstRead, secondRead]
  | @node constructor arguments allowed children inductionHypothesis =>
    change constructorWeight opened constructor +
      (∑ position, HereditaryWeight.term (constructorWeight opened) (arguments position)) = 0
    rw [(allowed_iff_weight_zero opened _).mp allowed]
    simp only [inductionHypothesis, Finset.sum_const_zero, Nat.add_zero]

theorem supported_of_weight_zero {sort : Srt source Parallel} (opened : Policy source Parallel)
    (supplied : Value (source := source) (Parallel := Parallel) sort)
    (zero : HereditaryWeight.term (constructorWeight opened) supplied = 0) : Supported opened supplied := by
  revert zero
  apply @Term.rec (signature source Parallel) NativeParallel
    (fun _ supplied => HereditaryWeight.term (constructorWeight opened) supplied = 0 → Supported opened supplied)
    (t := supplied)
  · intro sort parallel _
    exact .zero parallel
  · intro sort parallel first second firstRead secondRead zero
    change HereditaryWeight.term (constructorWeight opened) first +
      HereditaryWeight.term (constructorWeight opened) second = 0 at zero
    exact .cut parallel (firstRead (Nat.add_eq_zero_iff.mp zero).1)
      (secondRead (Nat.add_eq_zero_iff.mp zero).2)
  · intro constructor arguments inductionHypothesis zero
    change constructorWeight opened constructor +
      (∑ position, HereditaryWeight.term (constructorWeight opened) (arguments position)) = 0 at zero
    obtain ⟨constructorZero, totalZero⟩ := Nat.add_eq_zero_iff.mp zero
    refine .node ((allowed_iff_weight_zero opened constructor).mpr constructorZero) ?_
    intro position
    have bounded := Finset.single_le_sum
      (fun other _ => Nat.zero_le (HereditaryWeight.term (constructorWeight opened) (arguments other)))
      (Finset.mem_univ position)
    exact inductionHypothesis position (by omega)

theorem supported_iff_weight_zero {sort : Srt source Parallel} (opened : Policy source Parallel)
    (supplied : Value (source := source) (Parallel := Parallel) sort) :
    Supported opened supplied ↔ HereditaryWeight.term (constructorWeight opened) supplied = 0 :=
  ⟨Supported.weight_zero, supported_of_weight_zero opened supplied⟩

theorem supported_equation {sort : Srt source Parallel} (opened : Policy source Parallel)
    {first second : Value (source := source) (Parallel := Parallel) sort} (equation : Equation first second) :
    Supported opened first ↔ Supported opened second := by
  rw [supported_iff_weight_zero, supported_iff_weight_zero,
    HereditaryWeight.term_equation (constructorWeight opened) equation]

def ClassSupported (opened : Policy source Parallel) {sort : Srt source Parallel}
    (supplied : ValueClass (source := source) (Parallel := Parallel) sort) : Prop :=
  ∃ raw : Value sort, Supported opened raw ∧ classOf raw = supplied

theorem class_supported_iff_weight_zero (opened : Policy source Parallel) {sort : Srt source Parallel}
    (supplied : ValueClass (source := source) (Parallel := Parallel) sort) :
    ClassSupported opened supplied ↔ HereditaryWeight.classTerm (constructorWeight opened) supplied = 0 := by
  constructor
  · rintro ⟨raw, supported, rfl⟩
    exact supported.weight_zero
  · revert supplied
    intro supplied
    refine Quotient.inductionOn supplied ?_
    intro raw zero
    exact ⟨raw, supported_of_weight_zero opened raw zero, rfl⟩

theorem embed_supported (opened : Policy source Parallel) {sort : source.Srt} (supplied : Term source Parallel sort) :
    Supported opened (embed supplied) := by
  induction supplied with
  | @zero sort parallel => exact .zero (sort := .original sort) parallel
  | @cut sort parallel first second firstRead secondRead =>
    exact .cut (sort := .original sort) parallel firstRead secondRead
  | node constructor arguments inductionHypothesis => exact .node (.original constructor) inductionHypothesis

theorem classEmbedding_supported (opened : Policy source Parallel) {sort : source.Srt}
    (supplied : Class source Parallel sort) : ClassSupported opened (classEmbedding supplied) :=
  Quotient.inductionOn supplied (fun raw => ⟨embed raw, embed_supported opened raw, rfl⟩)

theorem Supported.monotone {first second : Policy source Parallel} (inclusion : ∀ head, first head → second head)
    {sort : Srt source Parallel} {supplied : Value (source := source) (Parallel := Parallel) sort}
    (supported : Supported first supplied) : Supported second supplied := by
  induction supported with
  | zero parallel => exact .zero parallel
  | cut parallel before after beforeRead afterRead => exact .cut parallel beforeRead afterRead
  | node allowed children inductionHypothesis =>
    refine .node ?_ inductionHypothesis
    cases allowed with
    | original constructor => exact .original constructor
    | arguments head permission => exact .arguments head (inclusion head permission)
    | probe instrument permission => exact .probe instrument (inclusion _ permission)
    | cut instrument permission => exact .cut instrument (inclusion _ permission)

theorem ClassSupported.monotone {first second : Policy source Parallel} (inclusion : ∀ head, first head → second head)
    {sort : Srt source Parallel} {supplied : ValueClass (source := source) (Parallel := Parallel) sort}
    (supported : ClassSupported first supplied) : ClassSupported second supplied := by
  obtain ⟨raw, rawSupported, read⟩ := supported
  exact ⟨raw, rawSupported.monotone inclusion, read⟩

end Mettapedia.OSLF.Framework.SortedTypedInstruments.Kit
