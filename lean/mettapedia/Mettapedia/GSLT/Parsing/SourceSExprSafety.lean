import Mettapedia.GSLT.Parsing.SExprTokenRoundTrip

/-! Constructive checking of the original parser's token round-trip side condition. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.SourceSExprSafety

open Algorithms.MeTTa.Simple.Parser (SExpr)

mutual
  def safeBool : SExpr → Bool
    | .atom token => token != "(" && token != ")"
    | .list children => childrenSafeBool children

  def childrenSafeBool : List SExpr → Bool
    | [] => true
    | child :: rest => safeBool child && childrenSafeBool rest
end

mutual
  theorem safeBool_iff (expression : SExpr) :
      safeBool expression = true ↔ SExprTokenRoundTrip.safe expression := by
    cases expression with
    | atom token => simp [safeBool, SExprTokenRoundTrip.safe]
    | list children => exact childrenSafeBool_iff children
  termination_by sizeOf expression

  theorem childrenSafeBool_iff (children : List SExpr) :
      childrenSafeBool children = true ↔ SExprTokenRoundTrip.childrenSafe children := by
    cases children with
    | nil => simp [childrenSafeBool, SExprTokenRoundTrip.childrenSafe]
    | cons child rest =>
        simp only [childrenSafeBool, SExprTokenRoundTrip.childrenSafe, Bool.and_eq_true,
          safeBool_iff child, childrenSafeBool_iff rest]
  termination_by sizeOf children
end

theorem quoted_token_is_safe : safeBool (.atom "\"native_io.h\"") = true := rfl

theorem delimiter_token_refused : safeBool (.list [.atom "("]) = false := rfl

end Mettapedia.GSLT.Parsing.SourceSExprSafety
