import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PresentationParser
import Mettapedia.GSLT.Parsing.ClassAwareParserPackReplay

/-! # Ambiguity and malformed forests at the authored transform boundary

Two lexical state rows deliberately recognize the same scalar. Their exact
row identities and CSTs remain distinct in the complete packed forest.
Removing either row's family fails completeness even though another complete
parse still replays. Corrupt spans and forged structural origins fail replay.
-/

set_option autoImplicit false
set_option maxRecDepth 4096

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.Parser.Controls

open Mettapedia.GSLT.Parsing
open ParserProfileSemantics PresentationExprSemantics
open ClassAwareParserPackCorrespondence ClassAwareParserPackCertificate
open ClassAwarePackedForest ClassAwareParserPackReplay ClassAwarePackedForestSaturation

def profile : ParserProfileLayer where
  name := "tcalc.boundary-ambiguity-v1"
  startSort := "Proc"
  classes := [⟨"state-code", .points [83]⟩, ⟨"firing-code", .points [77]⟩]
  states := [⟨"State", "state-code", "EmptyState"⟩,
    ⟨"State", "state-code", "AlreadyTold"⟩, ⟨"Firing", "firing-code", "Move"⟩]

def input : List Nat := [102, 105, 114, 101, 83, 77]

def stateCertificate (second : Bool) : Certificate :=
  .lexical (if second then 1 else 0) (.class "state-code") 4 5

def firingCertificate : Certificate := .lexical 2 (.class "firing-code") 5 6

def certificate (second : Bool) : Certificate :=
  .structural 1 0 6
    (.terminal (.char 102) 0 1 (.terminal (.char 105) 1 2
      (.terminal (.char 114) 2 3 (.terminal (.char 101) 3 4
        (.nonterminal "State" 4 5 (stateCertificate second)
          (.nonterminal "Firing" 5 6 firingCertificate (.nil 6)))))))

def tree (second : Bool) : CST :=
  .node "Request" 0 6 [
    .node (if second then "AlreadyTold" else "EmptyState") 4 5 [.terminal [83] 4 5],
    .node "Move" 5 6 [.terminal [77] 5 6]]

theorem both_certificates_replay (second : Bool) :
    (replay profile (plan profile) input "Proc" 0 6 (certificate second)).isSome = true := by
  cases second <;> decide +kernel

def checkedReplay (second : Bool) :=
  (replay profile (plan profile) input "Proc" 0 6 (certificate second)).get
    (both_certificates_replay second)

theorem replayed_tree (second : Bool) : (checkedReplay second).1 = tree second := by
  cases second <;> decide +kernel

def exactReplay (second : Bool) :
    Replays profile (plan profile) input (certificate second) "Proc" 0 6 (tree second) :=
  replayed_tree second ▸ (checkedReplay second).2

def forest : Forest := pack [("Proc", certificate false), ("Proc", certificate true)]

theorem forest_complete : validateRuleSaturation forest profile (plan profile) input = true := by
  decide +kernel

def packed (second : Bool) : Packed forest profile input (tree second) :=
  ⟨certificate second, ⟨member_pack_rootUnfolds (by cases second <;> simp [profile])⟩,
    exactReplay second⟩

theorem both_source_parses (second : Bool) : Nonempty (Source profile input (tree second)) :=
  packed_reflects forest profile input (tree second) ⟨packed second⟩

theorem distinct_trees : tree false ≠ tree true := by decide +kernel

theorem ambiguity_survives : Nonempty (Packed forest profile input (tree false)) ∧
    Nonempty (Packed forest profile input (tree true)) ∧ tree false ≠ tree true :=
  ⟨⟨packed false⟩, ⟨packed true⟩, distinct_trees⟩

def omitted : Forest :=
  { forest with families := forest.families.filter (fun family =>
      decide (family ≠ certificateFamily "State" (stateCertificate true))) }

theorem missing_alternative_refused :
    validateRuleSaturation omitted profile (plan profile) input = false := by decide +kernel

theorem surviving_parse_still_replays :
    (replay profile (plan profile) input "Proc" 0 6 (certificate false)).isSome = true :=
  both_certificates_replay false

theorem malformed_lexical_span_refused :
    (replay profile (plan profile) input "State" 4 6
      (.lexical 0 (.class "state-code") 4 6)).isNone = true := by decide +kernel

theorem forged_rule_origin_refused :
    (replay profile (plan profile) input "Proc" 0 6
      (.structural 0 0 6 (.nil 6))).isNone = true := by decide +kernel

def selectEmpty : CST → Bool
  | .node "Request" _ _ [.node "EmptyState" _ _ _, _] => true
  | _ => false

def selectTold : CST → Bool
  | .node "Request" _ _ [.node "AlreadyTold" _ _ _, _] => true
  | _ => false

theorem explicit_policy_separates :
    Selected selectEmpty forest profile input (tree false) ∧
      ¬ Selected selectEmpty forest profile input (tree true) ∧
      Selected selectTold forest profile input (tree true) := by
  exact ⟨⟨⟨packed false⟩, rfl⟩, fun h => Bool.noConfusion h.2, ⟨⟨packed true⟩, rfl⟩⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.Parser.Controls
