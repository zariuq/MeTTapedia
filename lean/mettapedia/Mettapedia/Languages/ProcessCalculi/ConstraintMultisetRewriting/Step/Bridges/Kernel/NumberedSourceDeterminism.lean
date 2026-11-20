import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.NumberedSourceSyntax

/-!
# Unique readback of an actual numbered source node

Earlier-reference certificates determine one source type or term in a fixed
symbol table and fixed input rows. The result applies to different licensed
caches, rather than merely repeating one decoder call. It does not identify
different symbol histories or equate syntax with theorem authority.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NumberedSourceSyntax

open Lean Mettapedia.Languages.OpenTheory Mettapedia.Languages.HOLLight

theorem parsed_unique {A : Type} (decode : Json → Option A) (rows : Nat → Option Json)
    (index : Nat) {firstRaw secondRaw : Json} {first second : A}
    (firstAt : rows index = some firstRaw) (secondAt : rows index = some secondRaw)
    (firstRead : decode firstRaw = some first) (secondRead : decode secondRaw = some second) : first = second := by
  have sameRaw := Option.some.inj (firstAt.symm.trans secondAt)
  subst secondRaw
  exact Option.some.inj (firstRead.symm.trans secondRead)

private theorem children_unique (symbols : ExportCodec.Symbols) (rows : Nat → Option Json) (limit : Nat)
    (unique : ∀ child, child < limit → ∀ first second,
      TypeAt symbols rows child first → TypeAt symbols rows child second → first = second)
    (references : List Nat) (first second : List Ty)
    (firstRead : TypeChildrenAt symbols rows limit references first)
    (secondRead : TypeChildrenAt symbols rows limit references second) : first = second := by
  induction references generalizing first second with
  | nil => cases firstRead; cases secondRead; rfl
  | cons child rest ih =>
      cases firstRead with
      | cons before read later =>
          cases secondRead with
          | cons _ other remaining =>
              have same := unique child before _ _ read other
              cases same
              exact congrArg (List.cons _) (ih _ _ later remaining)

theorem type_unique (symbols : ExportCodec.Symbols) (rows : Nat → Option Json)
    (index : Nat) (first second : Ty)
    (firstRead : TypeAt symbols rows index first) (secondRead : TypeAt symbols rows index second) : first = second := by
  induction index using Nat.strong_induction_on generalizing first second with
  | h index ih =>
      cases firstRead with
      | «variable» atRow parsed =>
          cases secondRead with
          | «variable» otherRow otherParsed =>
              have same := parsed_unique typeRow? rows index atRow otherRow parsed otherParsed
              cases same
              rfl
          | operation otherRow otherParsed _ _ =>
              cases parsed_unique typeRow? rows index atRow otherRow parsed otherParsed
      | operation atRow parsed registered children =>
          cases secondRead with
          | «variable» otherRow otherParsed =>
              cases parsed_unique typeRow? rows index atRow otherRow parsed otherParsed
          | operation otherRow otherParsed otherRegistered otherChildren =>
              have same := parsed_unique typeRow? rows index atRow otherRow parsed otherParsed
              cases same
              have sameOperator := Option.some.inj (registered.symm.trans otherRegistered)
              cases sameOperator
              have sameArguments := children_unique symbols rows index ih _ _ _ children otherChildren
              cases sameArguments
              rfl

theorem term_unique (symbols : ExportCodec.Symbols) (types terms : Nat → Option Json)
    (index : Nat) (first second : SourceTerm)
    (firstRead : TermAt symbols types terms index first)
    (secondRead : TermAt symbols types terms index second) : first = second := by
  induction index using Nat.strong_induction_on generalizing first second with
  | h index ih =>
      cases firstRead with
      | «variable» atRow parsed typed =>
          cases secondRead with
          | «variable» otherRow otherParsed otherTyped =>
              have same := parsed_unique termRow? terms index atRow otherRow parsed otherParsed
              cases same
              cases type_unique symbols types _ _ _ typed otherTyped
              rfl
          | constant otherRow otherParsed _ _ =>
              cases parsed_unique termRow? terms index atRow otherRow parsed otherParsed
          | application otherRow otherParsed _ _ _ _ =>
              cases parsed_unique termRow? terms index atRow otherRow parsed otherParsed
          | abstraction otherRow otherParsed _ _ _ _ =>
              cases parsed_unique termRow? terms index atRow otherRow parsed otherParsed
      | constant atRow parsed registered typed =>
          cases secondRead with
          | «variable» otherRow otherParsed _ =>
              cases parsed_unique termRow? terms index atRow otherRow parsed otherParsed
          | constant otherRow otherParsed otherRegistered otherTyped =>
              have same := parsed_unique termRow? terms index atRow otherRow parsed otherParsed
              cases same
              cases Option.some.inj (registered.symm.trans otherRegistered)
              cases type_unique symbols types _ _ _ typed otherTyped
              rfl
          | application otherRow otherParsed _ _ _ _ =>
              cases parsed_unique termRow? terms index atRow otherRow parsed otherParsed
          | abstraction otherRow otherParsed _ _ _ _ =>
              cases parsed_unique termRow? terms index atRow otherRow parsed otherParsed
      | application atRow parsed functionBefore argumentBefore functionRead argumentRead =>
          cases secondRead with
          | «variable» otherRow otherParsed _ =>
              cases parsed_unique termRow? terms index atRow otherRow parsed otherParsed
          | constant otherRow otherParsed _ _ =>
              cases parsed_unique termRow? terms index atRow otherRow parsed otherParsed
          | application otherRow otherParsed _ _ otherFunction otherArgument =>
              have same := parsed_unique termRow? terms index atRow otherRow parsed otherParsed
              cases same
              cases ih _ functionBefore _ _ functionRead otherFunction
              cases ih _ argumentBefore _ _ argumentRead otherArgument
              rfl
          | abstraction otherRow otherParsed _ _ _ _ =>
              cases parsed_unique termRow? terms index atRow otherRow parsed otherParsed
      | abstraction atRow parsed binderBefore bodyBefore binderRead bodyRead =>
          cases secondRead with
          | «variable» otherRow otherParsed _ =>
              cases parsed_unique termRow? terms index atRow otherRow parsed otherParsed
          | constant otherRow otherParsed _ _ =>
              cases parsed_unique termRow? terms index atRow otherRow parsed otherParsed
          | application otherRow otherParsed _ _ _ _ =>
              cases parsed_unique termRow? terms index atRow otherRow parsed otherParsed
          | abstraction otherRow otherParsed _ _ otherBinder otherBody =>
              have same := parsed_unique termRow? terms index atRow otherRow parsed otherParsed
              cases same
              have sameBinder := ih _ binderBefore _ _ binderRead otherBinder
              cases sameBinder
              cases ih _ bodyBefore _ _ bodyRead otherBody
              rfl

theorem type_caches_agree (symbols : ExportCodec.Symbols) (rows : Nat → Option Json)
    (first second : Nat → Option Ty) (firstCorrect : TypeCacheCorrect symbols rows first)
    (secondCorrect : TypeCacheCorrect symbols rows second) (index : Nat) (left right : Ty)
    (leftFound : first index = some left) (rightFound : second index = some right) : left = right :=
  type_unique symbols rows index left right (firstCorrect index left leftFound) (secondCorrect index right rightFound)

theorem term_caches_agree (symbols : ExportCodec.Symbols) (types terms : Nat → Option Json)
    (first second : Nat → Option SourceTerm)
    (firstCorrect : TermCacheCorrect symbols types terms first)
    (secondCorrect : TermCacheCorrect symbols types terms second) (index : Nat) (left right : SourceTerm)
    (leftFound : first index = some left) (rightFound : second index = some right) : left = right :=
  term_unique symbols types terms index left right (firstCorrect index left leftFound) (secondCorrect index right rightFound)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NumberedSourceSyntax
