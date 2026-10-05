import Mettapedia.GSLT.LanguageDef.NativeOpsCStatement

/-!
# Const qualification at each pointer level

This declarator profile retains base const and each pointer's const separately.
Pointer levels are listed from the base type outward. It shares the complete
function reader with the emitted-C profiles, without widening their typed
operation or external-call authority. Arrays, function pointers, volatile,
restrict and atomic qualification remain outside this profile.
-/

set_option autoImplicit false
set_option Elab.async false

namespace Mettapedia.GSLT.LanguageDef.NativeOps.NativeC

structure CDeclaratorType where
  name : Name
  baseConst : Bool
  pointerConst : List Bool
  deriving DecidableEq, Repr

def CDeclaratorType.unqualified (type : CDeclaratorType) : CType :=
  ⟨type.name, type.pointerConst.length⟩

/-- Depth zero is the base; depth one is the pointer nearest the base. -/
def CDeclaratorType.constAtDepth (type : CDeclaratorType) : Nat → Option Bool
  | 0 => some type.baseConst
  | depth + 1 => type.pointerConst[depth]?

structure CDeclaratorParameter where
  type : CDeclaratorType
  name : Name
  deriving DecidableEq, Repr

abbrev CDeclaratorFunction := CFunctionSyntax CDeclaratorParameter

def constPrefix : List Token → Bool × List Token
  | .identifier ['c', 'o', 'n', 's', 't'] :: rest =>
      let next := constPrefix rest
      (true, next.2)
  | tokens => (false, tokens)

def pointerConstSuffix : Nat → List Token → Option (List Bool × List Token)
  | 0, _ => none
  | fuel + 1, .punctuation ['*'] :: rest => do
      let qualifier := constPrefix rest
      let (others, after) ← pointerConstSuffix fuel qualifier.2
      some (qualifier.1 :: others, after)
  | _ + 1, tokens => some ([], tokens)

/-- This reader accepts only declarators with a named, already admitted base
type. An unsupported qualifier cannot be mistaken for the parameter name. -/
def declaratorType? (names : TypeNames) (tokens : List Token) :
    Option (CDeclaratorType × List Token) := do
  let leading := constPrefix tokens
  match leading.2 with
  | .identifier name :: rest =>
      if !names.contains name then none else do
        let trailing := constPrefix rest
        let (qualifiers, after) ← pointerConstSuffix (tokens.length + 1) trailing.2
        some (⟨name, leading.1 || trailing.1, qualifiers⟩, after)
  | _ => none

def reservedIdentifier (name : Name) : Bool :=
  ["auto", "break", "case", "char", "const", "continue", "default", "do",
   "double", "else", "enum", "extern", "float", "for", "goto", "if", "inline",
   "int", "long", "register", "restrict", "return", "short", "signed", "sizeof",
   "static", "struct", "switch", "typedef", "union", "unsigned", "void",
   "volatile", "while", "_Alignas", "_Alignof", "_Atomic", "_Bool", "_Complex",
   "_Generic", "_Imaginary", "_Noreturn", "_Static_assert", "_Thread_local"].any
    (fun keyword => keyword.toList == name)

def declaratorParameter? (names : TypeNames) (tokens : List Token) :
    Option (CDeclaratorParameter × List Token) := do
  let (type, afterType) ← declaratorType? names tokens
  match afterType with
  | .identifier name :: rest =>
      if reservedIdentifier name then none else some (⟨type, name⟩, rest)
  | _ => none

def declaratorFunctionText? (names : TypeNames) (characters : List Char) :
    Option CDeclaratorFunction :=
  functionTextUsing? (declaratorParameter? names) names characters

theorem unqualified_pointer_depth (type : CDeclaratorType) :
    type.unqualified.pointers = type.pointerConst.length := rfl

theorem qualifier_depth_extent (type : CDeclaratorType) (depth : Nat) :
    (type.constAtDepth depth).isSome = true ↔ depth ≤ type.unqualified.pointers := by
  cases depth with
  | zero => simp [CDeclaratorType.constAtDepth]
  | succ depth =>
      simp [CDeclaratorType.constAtDepth, CDeclaratorType.unqualified]
      omega

private def exampleTypes : TypeNames := ["void".toList, "bool".toList, "Pair".toList]

theorem pointer_level_const_retained : declaratorParameter? exampleTypes
    [.identifier "Pair".toList, .punctuation ['*'], .identifier "const".toList,
     .punctuation ['*'], .identifier ['p']] =
    some (⟨⟨"Pair".toList, false, [true, false]⟩, ['p']⟩, []) := rfl

theorem base_and_pointer_const_are_distinct :
    (CDeclaratorType.mk "Pair".toList true [false, false]).constAtDepth 0 = some true ∧
    (CDeclaratorType.mk "Pair".toList false [true, false]).constAtDepth 0 = some false ∧
    (CDeclaratorType.mk "Pair".toList true [false, false]).unqualified =
      (CDeclaratorType.mk "Pair".toList false [true, false]).unqualified := by
  exact ⟨rfl, rfl, rfl⟩

theorem multiple_qualifier_levels_retained : declaratorParameter? exampleTypes
    [.identifier "const".toList, .identifier "Pair".toList,
     .punctuation ['*'], .identifier "const".toList,
     .punctuation ['*'], .identifier "const".toList, .identifier ['p']] =
    some (⟨⟨"Pair".toList, true, [true, true]⟩, ['p']⟩, []) := rfl

theorem trailing_base_const_retained : declaratorParameter? exampleTypes
    [.identifier "Pair".toList, .identifier "const".toList,
     .punctuation ['*'], .identifier ['p']] =
    some (⟨⟨"Pair".toList, true, [false]⟩, ['p']⟩, []) := rfl

theorem unsupported_pointer_volatile_refused : declaratorParameter? exampleTypes
    [.identifier "Pair".toList, .punctuation ['*'],
     .identifier "volatile".toList, .identifier ['p']] = none := by decide +kernel

theorem keyword_parameter_name_refused : declaratorParameter? exampleTypes
    [.identifier "bool".toList, .identifier "return".toList] = none := by decide +kernel

theorem unadmitted_base_refused : declaratorParameter? exampleTypes
    [.identifier "Other".toList, .punctuation ['*'], .identifier ['p']] = none := rfl

theorem excess_input_not_accepted_as_complete_function : declaratorFunctionText?
    exampleTypes "void f(Pair *const *p) { return; } stray".toList = none :=
  by decide +kernel

#print axioms unqualified_pointer_depth
#print axioms qualifier_depth_extent
#print axioms pointer_level_const_retained
#print axioms base_and_pointer_const_are_distinct
#print axioms multiple_qualifier_levels_retained
#print axioms trailing_base_const_retained
#print axioms unsupported_pointer_volatile_refused
#print axioms keyword_parameter_name_refused
#print axioms unadmitted_base_refused
#print axioms excess_input_not_accepted_as_complete_function

end Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
