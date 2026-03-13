import Algorithms.MeTTa.Simple.Backend.SessionReferenceFaithful
import Algorithms.MeTTa.Simple.Backend.SessionReferenceTotal

namespace Algorithms.MeTTa.Simple.Backend.SessionReferenceAdequacy

open MeTTailCore.MeTTaIL.Syntax
open Algorithms.MeTTa.Simple

/-- State/space-effect heads currently covered by the total reference kernel. -/
def CoveredStateLikeHead : Pattern → Prop
  | .apply "add-atom" [_space, _fact] => True
  | .apply "add-atom!" [_space, _fact] => True
  | .apply "remove-atom" [_space, _fact] => True
  | .apply "remove-atom!" [_space, _fact] => True
  | .apply "remove-all-atoms" [_space] => True
  | .apply "remove-all-atoms!" [_space] => True
  | .apply "get-atoms" [_space] => True
  | .apply "get-atoms!" [_space] => True
  | .apply "match" [_space, _pat, _tmpl] => True
  | .apply "match" [_pat, _tmpl] => True
  | _ => False

/-- Control-flow heads currently covered by the total reference kernel. -/
def CoveredControlFlowHead : Pattern → Prop
  | .apply "case" [_keyExpr, _branchesExpr] => True
  | .apply "foldall" [_aggExpr, _genExpr, _initExpr] => True
  | .apply "forall" [_genExpr, _checkExpr] => True
  | .apply "if" [_cond, _thenBr, _elseBr] => True
  | .apply "if" [_cond, _thenBr] => True
  | .apply "let" [_pat, _val, _body] => True
  | .apply "let*" [_binds, _body] => True
  | .apply "progn" _exprs => True
  | .apply "prog1" _exprs => True
  | _ => False

/-- PeTTaCore/stream-style heads currently covered by the total reference kernel. -/
def CoveredCoreLikeHead : Pattern → Prop
  | .apply "once" [_arg] => True
  | .apply "catch" [_arg] => True
  | .apply "catch" [_expr, _handler, _fallback] => True
  | .apply "nop" [_arg] => True
  | .apply "msort" [_arg] => True
  | .apply "collapse" [_arg] => True
  | .apply "superpose" [_arg] => True
  | .apply "atom-of" [_x] => True
  | .apply "Expr" _elems => True
  | .apply "repr" [_arg] => True
  | _ => False

/-- Initial explicit coverage predicate for the total reference intrinsic kernel.
    This is intentionally fragment-scoped: it marks the intrinsic heads we currently
    expect to reason about through the total reference backend, without claiming
    global adequacy to the live partial runtime. -/
def CoveredByReferenceN : Pattern → Prop
  | .apply "add-atom" [_space, _fact] => True
  | .apply "add-atom!" [_space, _fact] => True
  | .apply "remove-atom" [_space, _fact] => True
  | .apply "remove-atom!" [_space, _fact] => True
  | .apply "remove-all-atoms" [_space] => True
  | .apply "remove-all-atoms!" [_space] => True
  | .apply "get-atoms" [_space] => True
  | .apply "get-atoms!" [_space] => True
  | .apply "match" [_space, _pat, _tmpl] => True
  | .apply "match" [_pat, _tmpl] => True
  | .apply "case" [_keyExpr, _branchesExpr] => True
  | .apply "foldall" [_aggExpr, _genExpr, _initExpr] => True
  | .apply "forall" [_genExpr, _checkExpr] => True
  | .apply "once" [_arg] => True
  | .apply "catch" [_arg] => True
  | .apply "catch" [_expr, _handler, _fallback] => True
  | .apply "nop" [_arg] => True
  | .apply "msort" [_arg] => True
  | .apply "if" [_cond, _thenBr, _elseBr] => True
  | .apply "if" [_cond, _thenBr] => True
  | .apply "let" [_pat, _val, _body] => True
  | .apply "let*" [_binds, _body] => True
  | .apply "progn" _exprs => True
  | .apply "prog1" _exprs => True
  | .apply "collapse" [_arg] => True
  | .apply "superpose" [_arg] => True
  | .apply "atom-of" [_x] => True
  | .apply "Expr" _elems => True
  | .apply "repr" [_arg] => True
  | _ => False

/-- Public-fuel unary evaluator-agreement contract for `get-atoms`. -/
abbrev PublicGetAtomsUnaryEvalAgreement (s : Session) : Prop :=
  Session.GetAtomsUnaryEvalAgreement (SessionReferenceTotal.referenceFuel s)

/-- Public-fuel unary evaluator-agreement contract for `get-atoms!`. -/
abbrev PublicGetAtomsBangUnaryEvalAgreement (s : Session) : Prop :=
  Session.GetAtomsBangUnaryEvalAgreement (SessionReferenceTotal.referenceFuel s)

/-- Public-fuel constrained unary evaluator-agreement contract for `get-atoms`. -/
abbrev PublicGetAtomsUnaryEvalAgreementOn
    (s : Session) (Q : Session → Pattern → Prop) : Prop :=
  Session.GetAtomsUnaryEvalAgreementOn (SessionReferenceTotal.referenceFuel s) Q

/-- Public-fuel constrained unary evaluator-agreement contract for `get-atoms!`. -/
abbrev PublicGetAtomsBangUnaryEvalAgreementOn
    (s : Session) (Q : Session → Pattern → Prop) : Prop :=
  Session.GetAtomsBangUnaryEvalAgreementOn (SessionReferenceTotal.referenceFuel s) Q

/-- First proved constrained-fragment instance of the public-fuel `get-atoms`
    unary evaluator-agreement contract: sessions with `maxNodes = 0`. -/
theorem public_getAtoms_unary_eval_agreement_on_zeroMaxNodes
    (s : Session) :
    PublicGetAtomsUnaryEvalAgreementOn s (fun sess _spaceArg => sess.maxNodes = 0) := by
  exact
    Session.getAtomsUnaryEvalAgreementOn_zeroMaxNodes
      (fuel := SessionReferenceTotal.referenceFuel s)
      (by
        unfold SessionReferenceTotal.referenceFuel
        exact Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide : (0 : Nat) < 4096) (Nat.le_max_left 4096 s.maxNodes)))

/-- Stronger constrained-fragment instance of the public-fuel `get-atoms` unary
    evaluator-agreement contract: sessions with `maxSteps = 0`. -/
theorem public_getAtoms_unary_eval_agreement_on_zeroMaxSteps
    (s : Session) :
    PublicGetAtomsUnaryEvalAgreementOn s (fun sess _spaceArg => sess.maxSteps = 0) := by
  exact
    Session.getAtomsUnaryEvalAgreementOn_zeroMaxSteps
      (fuel := SessionReferenceTotal.referenceFuel s)
      (by
        unfold SessionReferenceTotal.referenceFuel
        exact Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide : (0 : Nat) < 4096) (Nat.le_max_left 4096 s.maxNodes)))

/-- First non-degenerate constrained-fragment instance of the public-fuel
    `get-atoms` unary evaluator-agreement contract: sessions with `maxNodes = 1`. -/
theorem public_getAtoms_unary_eval_agreement_on_oneMaxNode
    (s : Session) :
    PublicGetAtomsUnaryEvalAgreementOn s (fun sess _spaceArg => sess.maxNodes = 1) := by
  exact
    Session.getAtomsUnaryEvalAgreementOn_oneMaxNode
      (fuel := SessionReferenceTotal.referenceFuel s)
      (by
        unfold SessionReferenceTotal.referenceFuel
        exact Nat.lt_of_lt_of_le (by decide : (1 : Nat) < 4096) (Nat.le_max_left 4096 s.maxNodes))

/-- Public local-reference equality witness for `get-atoms` on the first
    non-degenerate covered fragment, namely `maxNodes = 1`. -/
theorem getAtoms_eval_eq_public_total_of_oneMaxNode
    (s : Session) (spaceArg : Pattern)
    (hNodes : s.maxNodes = 1) :
    Session.referenceEvalWithStateCore s (.apply "get-atoms" [spaceArg]) =
      SessionReferenceTotal.evalWithStateCore s (.apply "get-atoms" [spaceArg]) := by
  simpa [SessionReferenceTotal.evalWithStateCore] using
    (public_getAtoms_unary_eval_agreement_on_oneMaxNode s) s spaceArg hNodes

/-- First proved constrained-fragment instance of the public-fuel `get-atoms!`
    unary evaluator-agreement contract: sessions with `maxNodes = 0`. -/
theorem public_getAtomsBang_unary_eval_agreement_on_zeroMaxNodes
    (s : Session) :
    PublicGetAtomsBangUnaryEvalAgreementOn s (fun sess _spaceArg => sess.maxNodes = 0) := by
  exact
    Session.getAtomsBangUnaryEvalAgreementOn_zeroMaxNodes
      (fuel := SessionReferenceTotal.referenceFuel s)
      (by
        unfold SessionReferenceTotal.referenceFuel
        exact Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide : (0 : Nat) < 4096) (Nat.le_max_left 4096 s.maxNodes)))

/-- Stronger constrained-fragment instance of the public-fuel `get-atoms!`
    unary evaluator-agreement contract: sessions with `maxSteps = 0`. -/
theorem public_getAtomsBang_unary_eval_agreement_on_zeroMaxSteps
    (s : Session) :
    PublicGetAtomsBangUnaryEvalAgreementOn s (fun sess _spaceArg => sess.maxSteps = 0) := by
  exact
    Session.getAtomsBangUnaryEvalAgreementOn_zeroMaxSteps
      (fuel := SessionReferenceTotal.referenceFuel s)
      (by
        unfold SessionReferenceTotal.referenceFuel
        exact Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide : (0 : Nat) < 4096) (Nat.le_max_left 4096 s.maxNodes)))

/-- First non-degenerate constrained-fragment instance of the public-fuel
    `get-atoms!` unary evaluator-agreement contract: sessions with `maxNodes = 1`. -/
theorem public_getAtomsBang_unary_eval_agreement_on_oneMaxNode
    (s : Session) :
    PublicGetAtomsBangUnaryEvalAgreementOn s (fun sess _spaceArg => sess.maxNodes = 1) := by
  exact
    Session.getAtomsBangUnaryEvalAgreementOn_oneMaxNode
      (fuel := SessionReferenceTotal.referenceFuel s)
      (by
        unfold SessionReferenceTotal.referenceFuel
        exact Nat.lt_of_lt_of_le (by decide : (1 : Nat) < 4096) (Nat.le_max_left 4096 s.maxNodes))

/-- Public local-reference equality witness for `get-atoms!` on the first
    non-degenerate covered fragment, namely `maxNodes = 1`. -/
theorem getAtomsBang_eval_eq_public_total_of_oneMaxNode
    (s : Session) (spaceArg : Pattern)
    (hNodes : s.maxNodes = 1) :
    Session.referenceEvalWithStateCore s (.apply "get-atoms!" [spaceArg]) =
      SessionReferenceTotal.evalWithStateCore s (.apply "get-atoms!" [spaceArg]) := by
  simpa [SessionReferenceTotal.evalWithStateCore] using
    (public_getAtomsBang_unary_eval_agreement_on_oneMaxNode s) s spaceArg hNodes

/-- First compositional public-fuel `match` adequacy handle for `get-atoms` templates.
    This is still hypothesis-driven: it isolates the exact two lower facts still needed
    to turn the `match` slice into a fully unconditional adequacy theorem. -/
theorem match_getAtoms_intrinsic_eq_total_of_bindingwise_evalMatchedTemplate_agreement
    (s : Session) (space pat spaceExpr : Pattern)
    (hBindings :
      Session.referenceMatchBindings s space pat =
        Session.totalMatchBindings (SessionReferenceTotal.referenceFuel s) s space pat)
    (hEval :
      ∀ (sess : Session) (bs : MeTTailCore.MeTTaIL.Match.Bindings),
        Session.referenceMatchEvalMatchedTemplate s sess
            (Session.matchTemplateAfterBindings bs (.apply "get-atoms" [spaceExpr])) =
          Session.totalMatchEvalMatchedTemplate
            (SessionReferenceTotal.referenceFuel s) s sess
            (Session.matchTemplateAfterBindings bs (.apply "get-atoms" [spaceExpr]))) :
    Session.referenceMatchIntrinsicResult s space pat (.apply "get-atoms" [spaceExpr]) =
      Session.totalMatchIntrinsicResult
        (SessionReferenceTotal.referenceFuel s) s space pat (.apply "get-atoms" [spaceExpr]) := by
  simpa using
    Session.referenceMatchIntrinsicResult_eq_total_of_getAtomsTemplate_evalMatchedTemplate_agreement
      (fuel := SessionReferenceTotal.referenceFuel s) s space pat spaceExpr hBindings hEval

/-- Public-fuel `get-atoms`-template `match` adequacy with binding enumeration
    equality discharged automatically from the generic `SpaceOps` theorem. -/
theorem match_getAtoms_intrinsic_eq_total_of_eval_agreement
    (s : Session) (space pat spaceExpr : Pattern)
    (hEval :
      ∀ (sess : Session) (bs : MeTTailCore.MeTTaIL.Match.Bindings),
        Session.referenceEvalWithStateCore sess
            (.apply "get-atoms" [Session.matchTemplateAfterBindings bs spaceExpr]) =
          Session.evalWithStateCoreN (SessionReferenceTotal.referenceFuel s) sess
            (.apply "get-atoms" [Session.matchTemplateAfterBindings bs spaceExpr])) :
    Session.referenceMatchIntrinsicResult s space pat (.apply "get-atoms" [spaceExpr]) =
      Session.totalMatchIntrinsicResult
        (SessionReferenceTotal.referenceFuel s) s space pat (.apply "get-atoms" [spaceExpr]) := by
  simpa using
    Session.referenceMatchIntrinsicResult_eq_total_of_getAtomsTemplate_eval_agreement_autoBindings
      (fuel := SessionReferenceTotal.referenceFuel s) s space pat spaceExpr hEval

/-- Public-fuel `get-atoms`-template `match` adequacy from a unary evaluator-agreement
    contract (per substituted space argument), with binding-side plumbing discharged
    by the Session-level auto-bindings theorem. -/
theorem match_getAtoms_intrinsic_eq_total_of_unary_eval_agreement
    (s : Session) (space pat spaceExpr : Pattern)
    (hEvalUnary : PublicGetAtomsUnaryEvalAgreement s) :
    Session.referenceMatchIntrinsicResult s space pat (.apply "get-atoms" [spaceExpr]) =
      Session.totalMatchIntrinsicResult
        (SessionReferenceTotal.referenceFuel s) s space pat (.apply "get-atoms" [spaceExpr]) := by
  simpa using
    Session.referenceMatchIntrinsicResult_eq_total_of_getAtomsTemplate_unary_eval_agreement_autoBindings
      (fuel := SessionReferenceTotal.referenceFuel s) s space pat spaceExpr hEvalUnary

/-- First compositional public-fuel `match` adequacy handle for `get-atoms!` templates.
    This mirrors the `get-atoms` theorem and keeps the `hEval` side local to substituted
    templates while using the generic intrinsic boundary theorem. -/
theorem match_getAtomsBang_intrinsic_eq_total_of_bindingwise_evalMatchedTemplate_agreement
    (s : Session) (space pat spaceExpr : Pattern)
    (hBindings :
      Session.referenceMatchBindings s space pat =
        Session.totalMatchBindings (SessionReferenceTotal.referenceFuel s) s space pat)
    (hEval :
      ∀ (sess : Session) (bs : MeTTailCore.MeTTaIL.Match.Bindings),
        Session.referenceMatchEvalMatchedTemplate s sess
            (Session.matchTemplateAfterBindings bs (.apply "get-atoms!" [spaceExpr])) =
          Session.totalMatchEvalMatchedTemplate
            (SessionReferenceTotal.referenceFuel s) s sess
            (Session.matchTemplateAfterBindings bs (.apply "get-atoms!" [spaceExpr]))) :
    Session.referenceMatchIntrinsicResult s space pat (.apply "get-atoms!" [spaceExpr]) =
      Session.totalMatchIntrinsicResult
        (SessionReferenceTotal.referenceFuel s) s space pat (.apply "get-atoms!" [spaceExpr]) := by
  simpa using
    Session.referenceMatchIntrinsicResult_eq_total_of_getAtomsBangTemplate_evalMatchedTemplate_agreement
      (fuel := SessionReferenceTotal.referenceFuel s) s space pat spaceExpr hBindings hEval

/-- Public-fuel `get-atoms!`-template `match` adequacy with binding enumeration
    equality discharged automatically from the generic `SpaceOps` theorem. -/
theorem match_getAtomsBang_intrinsic_eq_total_of_eval_agreement
    (s : Session) (space pat spaceExpr : Pattern)
    (hEval :
      ∀ (sess : Session) (bs : MeTTailCore.MeTTaIL.Match.Bindings),
        Session.referenceEvalWithStateCore sess
            (.apply "get-atoms!" [Session.matchTemplateAfterBindings bs spaceExpr]) =
          Session.evalWithStateCoreN (SessionReferenceTotal.referenceFuel s) sess
            (.apply "get-atoms!" [Session.matchTemplateAfterBindings bs spaceExpr])) :
    Session.referenceMatchIntrinsicResult s space pat (.apply "get-atoms!" [spaceExpr]) =
      Session.totalMatchIntrinsicResult
        (SessionReferenceTotal.referenceFuel s) s space pat (.apply "get-atoms!" [spaceExpr]) := by
  simpa using
    Session.referenceMatchIntrinsicResult_eq_total_of_getAtomsBangTemplate_eval_agreement_autoBindings
      (fuel := SessionReferenceTotal.referenceFuel s) s space pat spaceExpr hEval

/-- Public-fuel `get-atoms!`-template `match` adequacy from a unary evaluator-agreement
    contract (per substituted space argument), with binding-side plumbing discharged
    by the Session-level auto-bindings theorem. -/
theorem match_getAtomsBang_intrinsic_eq_total_of_unary_eval_agreement
    (s : Session) (space pat spaceExpr : Pattern)
    (hEvalUnary : PublicGetAtomsBangUnaryEvalAgreement s) :
    Session.referenceMatchIntrinsicResult s space pat (.apply "get-atoms!" [spaceExpr]) =
      Session.totalMatchIntrinsicResult
        (SessionReferenceTotal.referenceFuel s) s space pat (.apply "get-atoms!" [spaceExpr]) := by
  simpa using
    Session.referenceMatchIntrinsicResult_eq_total_of_getAtomsBangTemplate_unary_eval_agreement_autoBindings
      (fuel := SessionReferenceTotal.referenceFuel s) s space pat spaceExpr hEvalUnary

/-- First non-degenerate public `match` adequacy theorem for `get-atoms!` templates:
    the bindings fold stays inside the `maxNodes = 1` fragment, so the constrained
    unary theorem is enough to discharge the whole intrinsic boundary. -/
theorem match_getAtomsBang_intrinsic_eq_total_of_oneMaxNode
    (s : Session) (space pat spaceExpr : Pattern)
    (hNodes : s.maxNodes = 1)
    (hStateRoot :
      ∀ (sess : Session) (spaceArg : Pattern),
        sess.maxNodes = 1 →
          (Session.referenceEvalWithStateCore sess (.apply "get-atoms!" [spaceArg])).1 = sess) :
    Session.referenceMatchIntrinsicResult s space pat (.apply "get-atoms!" [spaceExpr]) =
      Session.totalMatchIntrinsicResult
        (SessionReferenceTotal.referenceFuel s) s space pat (.apply "get-atoms!" [spaceExpr]) := by
  simpa using
    Session.referenceMatchIntrinsicResult_eq_total_of_getAtomsBangTemplate_on_oneMaxNode
      (fuel := SessionReferenceTotal.referenceFuel s)
      (by
        unfold SessionReferenceTotal.referenceFuel
        exact Nat.lt_of_lt_of_le (by decide : (1 : Nat) < 4096) (Nat.le_max_left 4096 s.maxNodes))
      s space pat spaceExpr hNodes hStateRoot

/-- Public local-reference equality witness for the first compositional
    `get-atoms!` fragment: a three-argument `match` whose template head is
    `get-atoms!`, on sessions with `maxNodes = 1`. -/
theorem match_getAtomsBang_eval_eq_public_total_of_oneMaxNode
    (s : Session) (space pat spaceExpr : Pattern)
    (hNodes : s.maxNodes = 1)
    (hIntr :
      Session.intrinsicStateful s (.apply "match" [space, pat, .apply "get-atoms!" [spaceExpr]]) =
        Session.intrinsicStatefulN (SessionReferenceTotal.referenceFuel s - 1) s
          (.apply "match" [space, pat, .apply "get-atoms!" [spaceExpr]])) :
    Session.referenceEvalWithStateCore s (.apply "match" [space, pat, .apply "get-atoms!" [spaceExpr]]) =
      SessionReferenceTotal.evalWithStateCore s
        (.apply "match" [space, pat, .apply "get-atoms!" [spaceExpr]]) := by
  simpa [SessionReferenceTotal.evalWithStateCore] using
    Session.referenceEvalWithStateCore_match_getAtomsBang_eq_N_of_maxNodes_one
      (fuel := SessionReferenceTotal.referenceFuel s)
      (by
        unfold SessionReferenceTotal.referenceFuel
        exact Nat.lt_of_lt_of_le (by decide : (3 : Nat) < 4096) (Nat.le_max_left 4096 s.maxNodes))
      s space pat spaceExpr hNodes hIntr

/-- Successful faithful intrinsic evaluation agrees with the public total intrinsic evaluator
    at the same fuel. This is the first adequacy bridge: faithful explicit-status kernel to
    theorem-bearing total kernel, without reopening the live partial runtime path. -/
theorem intrinsic_done_eq_totalIntrinsicStateful
    (fuel : Nat) (s : Session) (term : Pattern)
    (r : Option (Session × List Pattern))
    (hdone : SessionReferenceFaithful.intrinsicStatefulF fuel s term = .done r) :
    SessionReferenceTotal.totalIntrinsicStateful fuel s term = r := by
  exact SessionReferenceFaithful.intrinsicStatefulF_done_eq_total fuel s term hdone

/-- Successful faithful evaluation agrees with the public total evaluator at the same fuel. -/
theorem eval_done_eq_totalEvalWithStateCore
    (fuel : Nat) (s : Session) (term : Pattern)
    (res : Session × List Pattern)
    (hdone : SessionReferenceFaithful.evalWithStateCoreF fuel s term = .done res) :
    SessionReferenceTotal.totalEvalWithStateCore fuel s term = res := by
  exact SessionReferenceFaithful.evalWithStateCoreF_done_eq_total fuel s term hdone

/-- Successful faithful intrinsic evaluation preserves session well-formedness through the
    public total-reference surface. -/
theorem intrinsic_done_preserves
    (fuel : Nat) (s : Session) (term : Pattern)
    (hdone :
      SessionReferenceFaithful.intrinsicStatefulF fuel s term = .done (some (s', out)))
    (hs : SessionReferenceTotal.SessionWF s) :
    SessionReferenceTotal.SessionWF s' := by
  exact SessionReferenceFaithful.intrinsicStatefulF_preserves_done fuel s term hdone hs

/-- Successful faithful evaluation preserves session well-formedness through the
    public total-reference surface. -/
theorem eval_done_preserves
    (fuel : Nat) (s : Session) (term : Pattern)
    (hdone :
      SessionReferenceFaithful.evalWithStateCoreF fuel s term = .done (s', out))
    (hs : SessionReferenceTotal.SessionWF s) :
    SessionReferenceTotal.SessionWF s' := by
  exact SessionReferenceFaithful.evalWithStateCoreF_preserves_done fuel s term hdone hs

/-- At the public total-reference fuel budget, a successful faithful intrinsic run agrees
    with the public theorem-bearing intrinsic evaluator. -/
theorem intrinsic_done_eq_public_totalIntrinsicStateful
    (s : Session) (term : Pattern)
    (r : Option (Session × List Pattern))
    (hdone :
      SessionReferenceFaithful.intrinsicStateful s term = .done r) :
    SessionReferenceTotal.intrinsicStateful s term = r := by
  exact SessionReferenceFaithful.intrinsicStateful_done_eq_total s term hdone

/-- At the public total-reference fuel budget, a successful faithful run agrees
    with the public theorem-bearing evaluator. -/
theorem eval_done_eq_public_totalEvalWithStateCore
    (s : Session) (term : Pattern)
    (res : Session × List Pattern)
    (hdone :
      SessionReferenceFaithful.evalWithStateCore s term = .done res) :
    SessionReferenceTotal.evalWithStateCore s term = res := by
  exact SessionReferenceFaithful.evalWithStateCore_done_eq_total s term hdone

/-- Public-fuel successful faithful intrinsic evaluation preserves `SessionWF`. -/
theorem intrinsic_done_preserves_public
    (s : Session) (term : Pattern)
    (hdone :
      SessionReferenceFaithful.intrinsicStateful s term = .done (some (s', out)))
    (hs : SessionReferenceTotal.SessionWF s) :
    SessionReferenceTotal.SessionWF s' := by
  exact SessionReferenceFaithful.intrinsicStateful_preserves_done s term hdone hs

/-- Public-fuel successful faithful evaluation preserves `SessionWF`. -/
theorem eval_done_preserves_public
    (s : Session) (term : Pattern)
    (hdone :
      SessionReferenceFaithful.evalWithStateCore s term = .done (s', out))
    (hs : SessionReferenceTotal.SessionWF s) :
    SessionReferenceTotal.SessionWF s' := by
  exact SessionReferenceFaithful.evalWithStateCore_preserves_done s term hdone hs

/-- A successful public faithful intrinsic run yields both total-backend agreement and
preservation in one theorem. This is the most convenient adequacy form for downstream
covered-fragment refinement lemmas. -/
theorem intrinsic_done_eq_total_and_preserves_public
    (s : Session) (term : Pattern)
    (hdone :
      SessionReferenceFaithful.intrinsicStateful s term = .done (some (s', out)))
    (hs : SessionReferenceTotal.SessionWF s) :
    SessionReferenceTotal.intrinsicStateful s term = some (s', out) ∧
      SessionReferenceTotal.SessionWF s' := by
  constructor
  · exact intrinsic_done_eq_public_totalIntrinsicStateful s term _ hdone
  · exact intrinsic_done_preserves_public s term hdone hs

/-- A successful public faithful run yields both total-backend agreement and preservation
in one theorem. This packages the adequacy facts in the form most useful to the total
refinement layer. -/
theorem eval_done_eq_total_and_preserves_public
    (s : Session) (term : Pattern)
    (hdone :
      SessionReferenceFaithful.evalWithStateCore s term = .done (s', out))
    (hs : SessionReferenceTotal.SessionWF s) :
    SessionReferenceTotal.evalWithStateCore s term = (s', out) ∧
      SessionReferenceTotal.SessionWF s' := by
  constructor
  · exact eval_done_eq_public_totalEvalWithStateCore s term _ hdone
  · exact eval_done_preserves_public s term hdone hs

end Algorithms.MeTTa.Simple.Backend.SessionReferenceAdequacy
