import Mettapedia.GSLT.LanguageDef.CettaWireTerm

/-! Exact constructive equality of the shared physical S-expression carrier. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.CettaWire

mutual

def Term.decEq : (first second : Term) → Decidable (first = second)
  | .symbol a, .symbol b => match _root_.decEq a b with
      | .isTrue same => .isTrue (congrArg Term.symbol same)
      | .isFalse different => .isFalse (fun same => different (Term.symbol.inj same))
  | .string a, .string b => match _root_.decEq a b with
      | .isTrue same => .isTrue (congrArg Term.string same)
      | .isFalse different => .isFalse (fun same => different (Term.string.inj same))
  | .natural a, .natural b => match _root_.decEq a b with
      | .isTrue same => .isTrue (congrArg Term.natural same)
      | .isFalse different => .isFalse (fun same => different (Term.natural.inj same))
  | .application a args, .application b args' => match _root_.decEq a b with
      | .isFalse different => .isFalse (fun same => different (Term.application.inj same).1)
      | .isTrue names => match Term.decEqList args args' with
          | .isFalse different => .isFalse (fun same => different (Term.application.inj same).2)
          | .isTrue arguments => .isTrue (by cases names; cases arguments; rfl)
  | .symbol _, .string _ | .symbol _, .natural _ | .symbol _, .application _ _
  | .string _, .symbol _ | .string _, .natural _ | .string _, .application _ _
  | .natural _, .symbol _ | .natural _, .string _ | .natural _, .application _ _
  | .application _ _, .symbol _ | .application _ _, .string _ | .application _ _, .natural _ =>
      .isFalse (by intro same; cases same)
termination_by first second => sizeOf first + sizeOf second

def Term.decEqList : (first second : List Term) → Decidable (first = second)
  | [], [] => .isTrue rfl
  | [], _ :: _ | _ :: _, [] => .isFalse (by intro same; cases same)
  | a :: args, b :: args' => match Term.decEq a b with
      | .isFalse different => .isFalse (fun same => different (List.cons.inj same).1)
      | .isTrue heads => match Term.decEqList args args' with
          | .isFalse different => .isFalse (fun same => different (List.cons.inj same).2)
          | .isTrue tails => .isTrue (by cases heads; cases tails; rfl)
termination_by first second => sizeOf first + sizeOf second

end

instance : DecidableEq Term := Term.decEq

end Mettapedia.GSLT.LanguageDef.CettaWire
