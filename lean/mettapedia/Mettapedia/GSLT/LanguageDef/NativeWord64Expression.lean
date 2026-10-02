import Mettapedia.GSLT.LanguageDef.NativeWord64Scalar

/-!
# Composition of the native scalar primitive correspondence

These typed scalar expression trees isolate the primitive layer of the
operational fragment.  Literal words and bytes carry their bounds.  Input
slots stand for already specified operand observations, including faults;
they do not grant authority to an external function.  The target tree has
bit-vector literals and is evaluated independently of the bounded-natural
source tree.

The compositional theorem preserves all results and refusals for every tree
and every related input environment.  Parsing, the compiler's Python AST,
mutable storage, function bodies, and physical execution need their own
connections to this primitive layer.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeWord64

inductive SourceExpression : Scalar → Type where
  | literal {type : Scalar} (value : SourceValue type) : SourceExpression type
  | input {type : Scalar} (slot : Nat) : SourceExpression type
  | unary {s t : Scalar} (op : Unary s t) (operand : SourceExpression s) : SourceExpression t
  | binary {s t : Scalar} (op : Binary s t)
      (left right : SourceExpression s) : SourceExpression t

inductive TargetExpression : Scalar → Type where
  | literal {type : Scalar} (value : TargetValue type) : TargetExpression type
  | input {type : Scalar} (slot : Nat) : TargetExpression type
  | unary {s t : Scalar} (op : Unary s t) (operand : TargetExpression s) : TargetExpression t
  | binary {s t : Scalar} (op : Binary s t)
      (left right : TargetExpression s) : TargetExpression t

abbrev SourceEnvironment := (type : Scalar) → Nat → Except Fault (SourceValue type)
abbrev TargetEnvironment := (type : Scalar) → Nat → Except Fault (TargetValue type)

def lowerScalar {type : Scalar} : SourceExpression type → TargetExpression type
  | .literal value => .literal (encodeValue type value)
  | .input slot => .input slot
  | .unary op operand => .unary op (lowerScalar operand)
  | .binary op left right => .binary op (lowerScalar left) (lowerScalar right)

def sourceEvaluate {type : Scalar} (environment : SourceEnvironment) :
    SourceExpression type → Except Fault (SourceValue type)
  | .literal value => .ok value
  | .input slot => environment type slot
  | .unary op operand => (sourceEvaluate environment operand).map (sourceUnary op)
  | .binary op left right => sourceScalarBinary op
      (sourceEvaluate environment left) (fun _ => sourceEvaluate environment right)

def targetEvaluate {type : Scalar} (environment : TargetEnvironment) :
    TargetExpression type → Except Fault (TargetValue type)
  | .literal value => .ok value
  | .input slot => environment type slot
  | .unary op operand => (targetEvaluate environment operand).map (targetUnary op)
  | .binary op left right => targetScalarBinary op
      (targetEvaluate environment left) (fun _ => targetEvaluate environment right)

def EnvironmentsRelated (source : SourceEnvironment) (target : TargetEnvironment) : Prop :=
  ∀ type slot, observeValue type (target type slot) = source type slot

/-- Uniform correspondence for every well-typed scalar expression, including faults. -/
theorem scalar_expression_correspondence {type : Scalar}
    (expression : SourceExpression type) (source : SourceEnvironment)
    (target : TargetEnvironment) (h : EnvironmentsRelated source target) :
    observeValue type (targetEvaluate target (lowerScalar expression)) =
      sourceEvaluate source expression := by
  induction expression with
  | @literal type value => cases type <;> rfl
  | input slot => exact h _ slot
  | unary op operand ih => exact unary_ordered_correspondence op _ _ ih
  | binary op left right ihl ihr =>
      exact scalar_binary_correspondence op _ _ _ _ ihl (fun _ => ihr)

theorem scalar_expression_success_iff {type : Scalar}
    (expression : SourceExpression type) (source : SourceEnvironment)
    (target : TargetEnvironment) (h : EnvironmentsRelated source target)
    (value : SourceValue type) :
    targetEvaluate target (lowerScalar expression) = .ok (encodeValue type value) ↔
      sourceEvaluate source expression = .ok value := by
  have hc := scalar_expression_correspondence expression source target h
  cases type with
  | word => rw [← hc]; exact (observe_ok_iff _ value).symm
  | byte => rw [← hc]; exact (observe_ok_iff _ value).symm
  | bool => rw [← hc]; rfl

theorem scalar_expression_fault_iff {type : Scalar}
    (expression : SourceExpression type) (source : SourceEnvironment)
    (target : TargetEnvironment) (h : EnvironmentsRelated source target)
    (fault : Fault) :
    targetEvaluate target (lowerScalar expression) = .error fault ↔
      sourceEvaluate source expression = .error fault := by
  have hc := scalar_expression_correspondence expression source target h
  cases type with
  | word => rw [← hc]; exact (observe_error_iff _ fault).symm
  | byte => rw [← hc]; exact (observe_error_iff _ fault).symm
  | bool => rw [← hc]; rfl

end Mettapedia.GSLT.LanguageDef.NativeWord64
