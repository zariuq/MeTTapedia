import Mettapedia.GSLT.LanguageDef.NativeWord64

/-!
# Typed scalar evaluation and operand order

This module combines the unsigned primitive profile with the compiler's
scalar types and Boolean operations.  Operand results are explicit inputs;
external-call admission and storage effects are not supplied by this module.
The source uses sequential monadic evaluation.  The target independently
uses the emitted left-temporary, branch, right-temporary order, including
short-circuit pruning.  Input faults are propagated rather than converted
into ordinary zero or false values.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeWord64

inductive Scalar where
  | word | byte | bool
  deriving DecidableEq, Repr

abbrev SourceValue : Scalar → Type
  | .word => Word
  | .byte => Byte
  | .bool => Bool

abbrev TargetValue : Scalar → Type
  | .word => BitVec 64
  | .byte => BitVec 8
  | .bool => Bool

def encodeValue (type : Scalar) : SourceValue type → TargetValue type :=
  match type with
  | .word => encode
  | .byte => encode
  | .bool => id

def observeValue (type : Scalar) : Except Fault (TargetValue type) → Except Fault (SourceValue type) :=
  match type with
  | .word => observe
  | .byte => observe
  | .bool => id

inductive Unary : Scalar → Scalar → Type where
  | complement : Unary .word .word
  | toByte : Unary .word .byte
  | toWord : Unary .byte .word
  | not : Unary .bool .bool

inductive Binary : Scalar → Scalar → Type where
  | word (op : WordOp) : Binary .word .word
  | compareWord (op : Comparison) : Binary .word .bool
  | compareByte (op : Comparison) : Binary .byte .bool
  | boolEq : Binary .bool .bool
  | boolNe : Binary .bool .bool
  | and : Binary .bool .bool
  | or : Binary .bool .bool

def sourceUnary {s t : Scalar} (op : Unary s t) : SourceValue s → SourceValue t :=
  match op with
  | .complement => sourceComplement
  | .toByte => sourceToByte
  | .toWord => sourceToWord
  | .not => fun (value : Bool) => decide (value = false)

def targetUnary {s t : Scalar} (op : Unary s t) : TargetValue s → TargetValue t :=
  match op with
  | .complement => targetComplement
  | .toByte => targetToByte
  | .toWord => targetToWord
  | .not => fun value => !value

def sourceComparisonOrdered {width : Nat} (op : Comparison)
    (left : Except Fault (Bounded width))
    (right : Unit → Except Fault (Bounded width)) : Except Fault Bool := do
  let a ← left
  let b ← right ()
  return sourceComparison op a b

def targetComparisonOrdered {width : Nat} (op : Comparison)
    (left : Except Fault (BitVec width))
    (right : Unit → Except Fault (BitVec width)) : Except Fault Bool :=
  match left with
  | .error fault => .error fault
  | .ok a => match right () with
      | .error fault => .error fault
      | .ok b => .ok (targetComparison op a b)

inductive BooleanOp where
  | eq | ne | and | or
  deriving DecidableEq, Repr

def sourceBoolean (op : BooleanOp) (left : Except Fault Bool)
    (right : Unit → Except Fault Bool) : Except Fault Bool := do
  let a ← left
  match op with
  | .eq => do let b ← right (); return decide (a = b)
  | .ne => do let b ← right (); return decide (a ≠ b)
  | .and => if a then right () else .ok false
  | .or => if a then .ok true else right ()

def targetBoolean (op : BooleanOp) (left : Except Fault Bool)
    (right : Unit → Except Fault Bool) : Except Fault Bool :=
  match left with
  | .error fault => .error fault
  | .ok a => match op with
      | .eq => match right () with
          | .error fault => .error fault
          | .ok b => .ok (a == b)
      | .ne => match right () with
          | .error fault => .error fault
          | .ok b => .ok (!(a == b))
      | .and => match a with
          | true => right ()
          | false => .ok false
      | .or => match a with
          | true => .ok true
          | false => right ()

def sourceScalarBinary {s t : Scalar} (op : Binary s t)
    (left : Except Fault (SourceValue s))
    (right : Unit → Except Fault (SourceValue s)) : Except Fault (SourceValue t) :=
  match op with
  | .word op => sourceOrdered op left right
  | .compareWord op => sourceComparisonOrdered op left right
  | .compareByte op => sourceComparisonOrdered op left right
  | .boolEq => sourceBoolean .eq left right
  | .boolNe => sourceBoolean .ne left right
  | .and => sourceBoolean .and left right
  | .or => sourceBoolean .or left right

def targetScalarBinary {s t : Scalar} (op : Binary s t)
    (left : Except Fault (TargetValue s))
    (right : Unit → Except Fault (TargetValue s)) : Except Fault (TargetValue t) :=
  match op with
  | .word op => targetOrdered op left right
  | .compareWord op => targetComparisonOrdered op left right
  | .compareByte op => targetComparisonOrdered op left right
  | .boolEq => targetBoolean .eq left right
  | .boolNe => targetBoolean .ne left right
  | .and => targetBoolean .and left right
  | .or => targetBoolean .or left right

theorem unary_correspondence {s t : Scalar} (op : Unary s t) (value : SourceValue s) :
    observeValue t (.ok (targetUnary op (encodeValue s value))) =
      .ok (sourceUnary op value) := by
  cases op with
  | complement => exact congrArg Except.ok (complement_correspondence value)
  | toByte => exact congrArg Except.ok (toByte_correspondence value)
  | toWord => exact congrArg Except.ok (toWord_correspondence value)
  | not => cases value <;> rfl

theorem unary_ordered_correspondence {s t : Scalar} (op : Unary s t)
    (source : Except Fault (SourceValue s)) (target : Except Fault (TargetValue s))
    (h : observeValue s target = source) :
    observeValue t (target.map (targetUnary op)) = source.map (sourceUnary op) := by
  cases op <;> cases target with
  | error fault =>
      simp only [observeValue, observe, Except.map, id_eq] at h
      subst source
      rfl
  | ok value =>
      simp only [observeValue, observe, Except.map, id_eq] at h
      subst source
      first
      | exact unary_correspondence .complement value.toFin
      | exact unary_correspondence .toByte value.toFin
      | exact unary_correspondence .toWord value.toFin
      | exact unary_correspondence .not value

theorem comparison_ordered_correspondence {width : Nat} (op : Comparison)
    (sl : Except Fault (Bounded width)) (tl : Except Fault (BitVec width))
    (sr : Unit → Except Fault (Bounded width)) (tr : Unit → Except Fault (BitVec width))
    (hl : observe tl = sl) (hr : ∀ u, observe (tr u) = sr u) :
    targetComparisonOrdered op tl tr = sourceComparisonOrdered op sl sr := by
  cases tl with
  | error fault =>
      have hl' : sl = .error fault := by simpa [observe, Except.map] using hl.symm
      rw [hl']
      rfl
  | ok a =>
      have hl' : sl = .ok a.toFin := by simpa [observe, Except.map] using hl.symm
      rw [hl']
      cases htr : tr () with
      | error fault =>
          have hr' : sr () = .error fault := by
            simpa [observe, Except.map, htr] using (hr ()).symm
          simp only [targetComparisonOrdered, htr]
          change Except.error fault = (sr ()).bind (fun b => .ok (sourceComparison op a.toFin b))
          rw [hr']
          rfl
      | ok b =>
          have hr' : sr () = .ok b.toFin := by
            simpa [observe, Except.map, htr] using (hr ()).symm
          simp only [targetComparisonOrdered, htr]
          change Except.ok (targetComparison op a b) =
            (sr ()).bind (fun b => .ok (sourceComparison op a.toFin b))
          rw [hr']
          exact congrArg Except.ok (comparison_correspondence op a.toFin b.toFin)

theorem boolean_correspondence (op : BooleanOp) (sl tl : Except Fault Bool)
    (sr tr : Unit → Except Fault Bool) (hl : tl = sl) (hr : ∀ u, tr u = sr u) :
    targetBoolean op tl tr = sourceBoolean op sl sr := by
  subst tl
  have hr' : tr = sr := funext hr
  subst tr
  cases sl with
  | error fault => rfl
  | ok a =>
      cases a <;> cases op <;> cases h : sr () <;>
        simp [targetBoolean, sourceBoolean, h]
      all_goals rename_i b; cases b <;> rfl

/-- Universal scalar primitive simulation with the exact operand evaluation order. -/
theorem scalar_binary_correspondence {s t : Scalar} (op : Binary s t)
    (sl : Except Fault (SourceValue s)) (tl : Except Fault (TargetValue s))
    (sr : Unit → Except Fault (SourceValue s)) (tr : Unit → Except Fault (TargetValue s))
    (hl : observeValue s tl = sl) (hr : ∀ u, observeValue s (tr u) = sr u) :
    observeValue t (targetScalarBinary op tl tr) = sourceScalarBinary op sl sr := by
  cases op with
  | word op => exact ordered_correspondence op sl tl sr tr hl hr
  | compareWord op => exact comparison_ordered_correspondence op sl tl sr tr hl hr
  | compareByte op => exact comparison_ordered_correspondence op sl tl sr tr hl hr
  | boolEq => exact boolean_correspondence .eq sl tl sr tr hl hr
  | boolNe => exact boolean_correspondence .ne sl tl sr tr hl hr
  | and => exact boolean_correspondence .and sl tl sr tr hl hr
  | or => exact boolean_correspondence .or sl tl sr tr hl hr

theorem and_prunes (right : Unit → Except Fault Bool) :
    targetBoolean .and (.ok false) right = .ok false := rfl

theorem or_prunes (right : Unit → Except Fault Bool) :
    targetBoolean .or (.ok true) right = .ok true := rfl

theorem and_evaluates_right (right : Unit → Except Fault Bool) :
    targetBoolean .and (.ok true) right = right () := rfl

theorem or_evaluates_right (right : Unit → Except Fault Bool) :
    targetBoolean .or (.ok false) right = right () := rfl

theorem boolean_left_fault_preserved (op : BooleanOp) (fault : Fault)
    (right : Unit → Except Fault Bool) :
    targetBoolean op (.error fault) right = .error fault := rfl

end Mettapedia.GSLT.LanguageDef.NativeWord64
