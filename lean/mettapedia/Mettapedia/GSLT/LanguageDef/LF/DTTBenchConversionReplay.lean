import Mettapedia.GSLT.LanguageDef.LF.PureCorrespondence
import Mettapedia.GSLT.LanguageDef.Pure.DTTBench31

/-!
# DTTBench conversion replay

Calibration fixture: an untrusted producer replays the frozen external
traces and emits candidate LF terms.  Acceptance comes only from the
generic conversion-capable indexed LF checker below.  The candidate and
source artifacts are identified by SHA-256 strings; this module adds no
benchmark-specific typing rule.
-/

namespace Mettapedia.GSLT.LanguageDef.LFDTTBenchConversionReplay

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.LFPureCorrespondence

def claimsSha256 : String := "6994e9b45927db97d6ef83186913575456938dd18be81f7d2211cf5a464bb14d"
def sourceSha256 : String := "51a8070f7b44bbc4ad6776a0db8c2905aeb3eab5cd2b9523b6f0366e62e66809"

structure ReplayCase where
  name : String
  actionCount : Nat
  traceSha256 : String
  referenceTermSha256 : String
  goal : LF.Term
  candidate : LF.Term

def accepts (entry : ReplayCase) : Bool :=
  LFConversionProfileChecker.check 128 LFProfile.indexed [] []
    entry.candidate entry.goal

def candidate_Eq_symm : LF.Term :=
  .lam (.pi (.srt .type) (.pi (.var 0) (.pi (.var 1) (.srt .type)))) (.lam (.pi (.srt .type) (.pi (.var 0) (.app (.app (.app (.var 2) (.var 1)) (.var 0)) (.var 0)))) (.lam (.pi (.srt .type) (.pi (.var 0) (.pi (.pi (.var 1) (.pi (.app (.app (.app (.var 4) (.var 2)) (.var 1)) (.var 0)) (.srt .type))) (.pi (.app (.app (.var 0) (.var 1)) (.app (.app (.var 3) (.var 2)) (.var 1))) (.pi (.var 3) (.pi (.app (.app (.app (.var 6) (.var 4)) (.var 3)) (.var 0)) (.app (.app (.var 3) (.var 1)) (.var 0)))))))) (.lam (.srt .type) (.lam (.var 0) (.lam (.var 1) (.lam (.app (.app (.app (.var 5) (.var 2)) (.var 1)) (.var 0)) (.app (.app (.app (.app (.app (.app (.var 4) (.var 3)) (.var 2)) (.lam (.var 3) (.lam (.app (.app (.app (.var 7) (.var 4)) (.var 3)) (.var 0)) (.app (.app (.app (.var 8) (.var 5)) (.var 1)) (.var 4))))) (.app (.app (.var 5) (.var 3)) (.var 2))) (.var 1)) (.var 0))))))))

def normalizedGoal_Eq_symm : LF.Term :=
  .pi (.pi (.srt .type) (.pi (.var 0) (.pi (.var 1) (.srt .type)))) (.pi (.pi (.srt .type) (.pi (.var 0) (.app (.app (.app (.var 2) (.var 1)) (.var 0)) (.var 0)))) (.pi (.pi (.srt .type) (.pi (.var 0) (.pi (.pi (.var 1) (.pi (.app (.app (.app (.var 4) (.var 2)) (.var 1)) (.var 0)) (.srt .type))) (.pi (.app (.app (.var 0) (.var 1)) (.app (.app (.var 3) (.var 2)) (.var 1))) (.pi (.var 3) (.pi (.app (.app (.app (.var 6) (.var 4)) (.var 3)) (.var 0)) (.app (.app (.var 3) (.var 1)) (.var 0)))))))) (.pi (.srt .type) (.pi (.var 0) (.pi (.var 1) (.pi (.app (.app (.app (.var 5) (.var 2)) (.var 1)) (.var 0)) (.app (.app (.app (.var 6) (.var 3)) (.var 1)) (.var 2))))))))

def normalizedCandidate_Eq_symm : LF.Term :=
  .lam (.pi (.srt .type) (.pi (.var 0) (.pi (.var 1) (.srt .type)))) (.lam (.pi (.srt .type) (.pi (.var 0) (.app (.app (.app (.var 2) (.var 1)) (.var 0)) (.var 0)))) (.lam (.pi (.srt .type) (.pi (.var 0) (.pi (.pi (.var 1) (.pi (.app (.app (.app (.var 4) (.var 2)) (.var 1)) (.var 0)) (.srt .type))) (.pi (.app (.app (.var 0) (.var 1)) (.app (.app (.var 3) (.var 2)) (.var 1))) (.pi (.var 3) (.pi (.app (.app (.app (.var 6) (.var 4)) (.var 3)) (.var 0)) (.app (.app (.var 3) (.var 1)) (.var 0)))))))) (.lam (.srt .type) (.lam (.var 0) (.app (.app (.app (.app (.var 2) (.var 1)) (.var 0)) (.lam (.var 1) (.lam (.app (.app (.app (.var 5) (.var 2)) (.var 1)) (.var 0)) (.app (.app (.app (.var 6) (.var 3)) (.var 1)) (.var 2))))) (.app (.app (.var 3) (.var 1)) (.var 0)))))))

theorem normalizedGoal_Eq_symm_eq :
    normalizedGoal_Eq_symm =
      LFBetaEta.normalForm [] PureBetaEta.normalizationFuel
        (encodeExpr PureDTTBench31.goal_Eq_Eq_symm) := by
  decide

theorem normalizedCandidate_Eq_symm_eq :
    normalizedCandidate_Eq_symm =
      LFBetaEta.normalForm [] PureBetaEta.normalizationFuel
        candidate_Eq_symm := by
  decide

def replay_Eq_symm : ReplayCase :=
  { name := "Eq_symm", actionCount := 12, traceSha256 := "e2eb1cd8f740c4d71b180fc2817ba4600faf7bfb3b51e99e7ac47bbf455ec642", referenceTermSha256 := "ca9628550979b10b48d081dd3579301f30976967274cb01c5da97b85974a8239"
    goal := encodeExpr PureDTTBench31.goal_Eq_Eq_symm
    candidate := candidate_Eq_symm }

theorem replay_Eq_symm_accepted : accepts replay_Eq_symm = true := by
  decide

theorem replay_Eq_symm_sound :
    LFConversionProfileChecker.Deriv LFProfile.indexed [] []
      candidate_Eq_symm (encodeExpr PureDTTBench31.goal_Eq_Eq_symm) :=
  LFConversionProfileChecker.S1 replay_Eq_symm_accepted

def candidate_Eq_trans : LF.Term :=
  .lam (.pi (.srt .type) (.pi (.var 0) (.pi (.var 1) (.srt .type)))) (.lam (.pi (.srt .type) (.pi (.var 0) (.app (.app (.app (.var 2) (.var 1)) (.var 0)) (.var 0)))) (.lam (.pi (.srt .type) (.pi (.var 0) (.pi (.pi (.var 1) (.pi (.app (.app (.app (.var 4) (.var 2)) (.var 1)) (.var 0)) (.srt .type))) (.pi (.app (.app (.var 0) (.var 1)) (.app (.app (.var 3) (.var 2)) (.var 1))) (.pi (.var 3) (.pi (.app (.app (.app (.var 6) (.var 4)) (.var 3)) (.var 0)) (.app (.app (.var 3) (.var 1)) (.var 0)))))))) (.lam (.srt .type) (.lam (.var 0) (.lam (.var 1) (.lam (.var 2) (.lam (.app (.app (.app (.var 6) (.var 3)) (.var 2)) (.var 1)) (.lam (.app (.app (.app (.var 7) (.var 4)) (.var 2)) (.var 1)) (.app (.app (.app (.app (.app (.app (.var 6) (.var 5)) (.var 3)) (.lam (.var 5) (.lam (.app (.app (.app (.var 9) (.var 6)) (.var 4)) (.var 0)) (.app (.app (.app (.var 10) (.var 7)) (.var 6)) (.var 1))))) (.var 1)) (.var 2)) (.var 0))))))))))

def normalizedGoal_Eq_trans : LF.Term :=
  .pi (.pi (.srt .type) (.pi (.var 0) (.pi (.var 1) (.srt .type)))) (.pi (.pi (.srt .type) (.pi (.var 0) (.app (.app (.app (.var 2) (.var 1)) (.var 0)) (.var 0)))) (.pi (.pi (.srt .type) (.pi (.var 0) (.pi (.pi (.var 1) (.pi (.app (.app (.app (.var 4) (.var 2)) (.var 1)) (.var 0)) (.srt .type))) (.pi (.app (.app (.var 0) (.var 1)) (.app (.app (.var 3) (.var 2)) (.var 1))) (.pi (.var 3) (.pi (.app (.app (.app (.var 6) (.var 4)) (.var 3)) (.var 0)) (.app (.app (.var 3) (.var 1)) (.var 0)))))))) (.pi (.srt .type) (.pi (.var 0) (.pi (.var 1) (.pi (.var 2) (.pi (.app (.app (.app (.var 6) (.var 3)) (.var 2)) (.var 1)) (.pi (.app (.app (.app (.var 7) (.var 4)) (.var 2)) (.var 1)) (.app (.app (.app (.var 8) (.var 5)) (.var 4)) (.var 2))))))))))

def normalizedCandidate_Eq_trans : LF.Term :=
  .lam (.pi (.srt .type) (.pi (.var 0) (.pi (.var 1) (.srt .type)))) (.lam (.pi (.srt .type) (.pi (.var 0) (.app (.app (.app (.var 2) (.var 1)) (.var 0)) (.var 0)))) (.lam (.pi (.srt .type) (.pi (.var 0) (.pi (.pi (.var 1) (.pi (.app (.app (.app (.var 4) (.var 2)) (.var 1)) (.var 0)) (.srt .type))) (.pi (.app (.app (.var 0) (.var 1)) (.app (.app (.var 3) (.var 2)) (.var 1))) (.pi (.var 3) (.pi (.app (.app (.app (.var 6) (.var 4)) (.var 3)) (.var 0)) (.app (.app (.var 3) (.var 1)) (.var 0)))))))) (.lam (.srt .type) (.lam (.var 0) (.lam (.var 1) (.lam (.var 2) (.lam (.app (.app (.app (.var 6) (.var 3)) (.var 2)) (.var 1)) (.app (.app (.app (.app (.app (.var 5) (.var 4)) (.var 2)) (.lam (.var 4) (.lam (.app (.app (.app (.var 8) (.var 5)) (.var 3)) (.var 0)) (.app (.app (.app (.var 9) (.var 6)) (.var 5)) (.var 1))))) (.var 0)) (.var 1)))))))))

theorem normalizedGoal_Eq_trans_eq :
    normalizedGoal_Eq_trans =
      LFBetaEta.normalForm [] PureBetaEta.normalizationFuel
        (encodeExpr PureDTTBench31.goal_Eq_Eq_trans) := by
  decide

theorem normalizedCandidate_Eq_trans_eq :
    normalizedCandidate_Eq_trans =
      LFBetaEta.normalForm [] PureBetaEta.normalizationFuel
        candidate_Eq_trans := by
  decide

def replay_Eq_trans : ReplayCase :=
  { name := "Eq_trans", actionCount := 10, traceSha256 := "854fdd8403cb3a8abcd785a5be4550404f08300247e98602bbd4ee9c6bfe05fc", referenceTermSha256 := "6d5edee6594338d96e2dc46dd0a17f71db974024b20b048193954e68f463bfbd"
    goal := encodeExpr PureDTTBench31.goal_Eq_Eq_trans
    candidate := candidate_Eq_trans }

theorem replay_Eq_trans_accepted : accepts replay_Eq_trans = true := by
  decide

theorem replay_Eq_trans_sound :
    LFConversionProfileChecker.Deriv LFProfile.indexed [] []
      candidate_Eq_trans (encodeExpr PureDTTBench31.goal_Eq_Eq_trans) :=
  LFConversionProfileChecker.S1 replay_Eq_trans_accepted

def candidate_Eq_congrArg : LF.Term :=
  .lam (.pi (.srt .type) (.pi (.var 0) (.pi (.var 1) (.srt .type)))) (.lam (.pi (.srt .type) (.pi (.var 0) (.app (.app (.app (.var 2) (.var 1)) (.var 0)) (.var 0)))) (.lam (.pi (.srt .type) (.pi (.var 0) (.pi (.pi (.var 1) (.pi (.app (.app (.app (.var 4) (.var 2)) (.var 1)) (.var 0)) (.srt .type))) (.pi (.app (.app (.var 0) (.var 1)) (.app (.app (.var 3) (.var 2)) (.var 1))) (.pi (.var 3) (.pi (.app (.app (.app (.var 6) (.var 4)) (.var 3)) (.var 0)) (.app (.app (.var 3) (.var 1)) (.var 0)))))))) (.lam (.srt .type) (.lam (.srt .type) (.lam (.pi (.var 1) (.var 1)) (.lam (.var 2) (.lam (.var 3) (.lam (.app (.app (.app (.var 7) (.var 4)) (.var 1)) (.var 0)) (.app (.app (.app (.app (.app (.app (.var 6) (.var 5)) (.var 2)) (.lam (.var 5) (.lam (.app (.app (.app (.var 9) (.var 6)) (.var 3)) (.var 0)) (.app (.app (.app (.var 10) (.var 6)) (.app (.var 5) (.var 4))) (.app (.var 5) (.var 1)))))) (.app (.app (.var 7) (.var 4)) (.app (.var 3) (.var 2)))) (.var 1)) (.var 0))))))))))

def normalizedGoal_Eq_congrArg : LF.Term :=
  .pi (.pi (.srt .type) (.pi (.var 0) (.pi (.var 1) (.srt .type)))) (.pi (.pi (.srt .type) (.pi (.var 0) (.app (.app (.app (.var 2) (.var 1)) (.var 0)) (.var 0)))) (.pi (.pi (.srt .type) (.pi (.var 0) (.pi (.pi (.var 1) (.pi (.app (.app (.app (.var 4) (.var 2)) (.var 1)) (.var 0)) (.srt .type))) (.pi (.app (.app (.var 0) (.var 1)) (.app (.app (.var 3) (.var 2)) (.var 1))) (.pi (.var 3) (.pi (.app (.app (.app (.var 6) (.var 4)) (.var 3)) (.var 0)) (.app (.app (.var 3) (.var 1)) (.var 0)))))))) (.pi (.srt .type) (.pi (.srt .type) (.pi (.pi (.var 1) (.var 1)) (.pi (.var 2) (.pi (.var 3) (.pi (.app (.app (.app (.var 7) (.var 4)) (.var 1)) (.var 0)) (.app (.app (.app (.var 8) (.var 4)) (.app (.var 3) (.var 2))) (.app (.var 3) (.var 1)))))))))))

def normalizedCandidate_Eq_congrArg : LF.Term :=
  .lam (.pi (.srt .type) (.pi (.var 0) (.pi (.var 1) (.srt .type)))) (.lam (.pi (.srt .type) (.pi (.var 0) (.app (.app (.app (.var 2) (.var 1)) (.var 0)) (.var 0)))) (.lam (.pi (.srt .type) (.pi (.var 0) (.pi (.pi (.var 1) (.pi (.app (.app (.app (.var 4) (.var 2)) (.var 1)) (.var 0)) (.srt .type))) (.pi (.app (.app (.var 0) (.var 1)) (.app (.app (.var 3) (.var 2)) (.var 1))) (.pi (.var 3) (.pi (.app (.app (.app (.var 6) (.var 4)) (.var 3)) (.var 0)) (.app (.app (.var 3) (.var 1)) (.var 0)))))))) (.lam (.srt .type) (.lam (.srt .type) (.lam (.pi (.var 1) (.var 1)) (.lam (.var 2) (.app (.app (.app (.app (.var 4) (.var 3)) (.var 0)) (.lam (.var 3) (.lam (.app (.app (.app (.var 7) (.var 4)) (.var 1)) (.var 0)) (.app (.app (.app (.var 8) (.var 4)) (.app (.var 3) (.var 2))) (.app (.var 3) (.var 1)))))) (.app (.app (.var 5) (.var 2)) (.app (.var 1) (.var 0))))))))))

theorem normalizedGoal_Eq_congrArg_eq :
    normalizedGoal_Eq_congrArg =
      LFBetaEta.normalForm [] PureBetaEta.normalizationFuel
        (encodeExpr PureDTTBench31.goal_Eq_Eq_congrArg) := by
  decide

theorem normalizedCandidate_Eq_congrArg_eq :
    normalizedCandidate_Eq_congrArg =
      LFBetaEta.normalForm [] PureBetaEta.normalizationFuel
        candidate_Eq_congrArg := by
  decide

def replay_Eq_congrArg : ReplayCase :=
  { name := "Eq_congrArg", actionCount := 15, traceSha256 := "d3506350cb5efcd47911bf28e4d6020479247bcc3bf33542007ddad98173db8b", referenceTermSha256 := "fa5a6d231b8cf17dbf9095b82571fd6614c4ef82b28c05c391120ad81d3dcb27"
    goal := encodeExpr PureDTTBench31.goal_Eq_Eq_congrArg
    candidate := candidate_Eq_congrArg }

theorem replay_Eq_congrArg_accepted : accepts replay_Eq_congrArg = true := by
  decide

theorem replay_Eq_congrArg_sound :
    LFConversionProfileChecker.Deriv LFProfile.indexed [] []
      candidate_Eq_congrArg (encodeExpr PureDTTBench31.goal_Eq_Eq_congrArg) :=
  LFConversionProfileChecker.S1 replay_Eq_congrArg_accepted

def candidate_Eq_congr : LF.Term :=
  .lam (.pi (.srt .type) (.pi (.var 0) (.pi (.var 1) (.srt .type)))) (.lam (.pi (.srt .type) (.pi (.var 0) (.app (.app (.app (.var 2) (.var 1)) (.var 0)) (.var 0)))) (.lam (.pi (.srt .type) (.pi (.var 0) (.pi (.pi (.var 1) (.pi (.app (.app (.app (.var 4) (.var 2)) (.var 1)) (.var 0)) (.srt .type))) (.pi (.app (.app (.var 0) (.var 1)) (.app (.app (.var 3) (.var 2)) (.var 1))) (.pi (.var 3) (.pi (.app (.app (.app (.var 6) (.var 4)) (.var 3)) (.var 0)) (.app (.app (.var 3) (.var 1)) (.var 0)))))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.srt .type)) (.srt .type))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.srt .type)) (.pi (.app (.app (.var 2) (.var 1)) (.var 0)) (.pi (.var 2) (.app (.var 2) (.var 0)))))) (.lam (.srt .type) (.lam (.srt .type) (.lam (.app (.app (.var 3) (.var 1)) (.lam (.var 1) (.var 1))) (.lam (.app (.app (.var 4) (.var 2)) (.lam (.var 2) (.var 2))) (.lam (.var 3) (.lam (.var 4) (.lam (.app (.app (.app (.var 10) (.app (.app (.var 7) (.var 5)) (.lam (.var 5) (.var 5)))) (.var 3)) (.var 2)) (.lam (.app (.app (.app (.var 11) (.var 6)) (.var 2)) (.var 1)) (.app (.app (.app (.app (.app (.app (.var 10) (.var 7)) (.var 3)) (.lam (.var 7) (.lam (.app (.app (.app (.var 13) (.var 8)) (.var 4)) (.var 0)) (.app (.app (.app (.var 14) (.var 8)) (.app (.app (.app (.app (.var 10) (.var 9)) (.lam (.var 9) (.var 9))) (.var 7)) (.var 5))) (.app (.app (.app (.app (.var 10) (.var 9)) (.lam (.var 9) (.var 9))) (.var 6)) (.var 1)))))) (.app (.app (.app (.app (.app (.app (.var 10) (.app (.app (.var 9) (.var 7)) (.lam (.var 7) (.var 7)))) (.var 5)) (.lam (.app (.app (.var 9) (.var 7)) (.lam (.var 7) (.var 7))) (.lam (.app (.app (.app (.var 13) (.app (.app (.var 10) (.var 8)) (.lam (.var 8) (.var 8)))) (.var 6)) (.var 0)) (.app (.app (.app (.var 14) (.var 8)) (.app (.app (.app (.app (.var 10) (.var 9)) (.lam (.var 9) (.var 9))) (.var 7)) (.var 5))) (.app (.app (.app (.app (.var 10) (.var 9)) (.lam (.var 9) (.var 9))) (.var 1)) (.var 5)))))) (.app (.app (.var 11) (.var 6)) (.app (.app (.app (.app (.var 8) (.var 7)) (.lam (.var 7) (.var 7))) (.var 5)) (.var 3)))) (.var 4)) (.var 1))) (.var 2)) (.var 0))))))))))))))

def normalizedGoal_Eq_congr : LF.Term :=
  .pi (.pi (.srt .type) (.pi (.var 0) (.pi (.var 1) (.srt .type)))) (.pi (.pi (.srt .type) (.pi (.var 0) (.app (.app (.app (.var 2) (.var 1)) (.var 0)) (.var 0)))) (.pi (.pi (.srt .type) (.pi (.var 0) (.pi (.pi (.var 1) (.pi (.app (.app (.app (.var 4) (.var 2)) (.var 1)) (.var 0)) (.srt .type))) (.pi (.app (.app (.var 0) (.var 1)) (.app (.app (.var 3) (.var 2)) (.var 1))) (.pi (.var 3) (.pi (.app (.app (.app (.var 6) (.var 4)) (.var 3)) (.var 0)) (.app (.app (.var 3) (.var 1)) (.var 0)))))))) (.pi (.pi (.srt .type) (.pi (.pi (.var 0) (.srt .type)) (.srt .type))) (.pi (.pi (.srt .type) (.pi (.pi (.var 0) (.srt .type)) (.pi (.app (.app (.var 2) (.var 1)) (.var 0)) (.pi (.var 2) (.app (.var 2) (.var 0)))))) (.pi (.srt .type) (.pi (.srt .type) (.pi (.app (.app (.var 3) (.var 1)) (.lam (.var 1) (.var 1))) (.pi (.app (.app (.var 4) (.var 2)) (.lam (.var 2) (.var 2))) (.pi (.var 3) (.pi (.var 4) (.pi (.app (.app (.app (.var 10) (.app (.app (.var 7) (.var 5)) (.lam (.var 5) (.var 5)))) (.var 3)) (.var 2)) (.pi (.app (.app (.app (.var 11) (.var 6)) (.var 2)) (.var 1)) (.app (.app (.app (.var 12) (.var 6)) (.app (.app (.app (.app (.var 8) (.var 7)) (.lam (.var 7) (.var 7))) (.var 5)) (.var 3))) (.app (.app (.app (.app (.var 8) (.var 7)) (.lam (.var 7) (.var 7))) (.var 4)) (.var 2)))))))))))))))

def normalizedCandidate_Eq_congr : LF.Term :=
  .lam (.pi (.srt .type) (.pi (.var 0) (.pi (.var 1) (.srt .type)))) (.lam (.pi (.srt .type) (.pi (.var 0) (.app (.app (.app (.var 2) (.var 1)) (.var 0)) (.var 0)))) (.lam (.pi (.srt .type) (.pi (.var 0) (.pi (.pi (.var 1) (.pi (.app (.app (.app (.var 4) (.var 2)) (.var 1)) (.var 0)) (.srt .type))) (.pi (.app (.app (.var 0) (.var 1)) (.app (.app (.var 3) (.var 2)) (.var 1))) (.pi (.var 3) (.pi (.app (.app (.app (.var 6) (.var 4)) (.var 3)) (.var 0)) (.app (.app (.var 3) (.var 1)) (.var 0)))))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.srt .type)) (.srt .type))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.srt .type)) (.pi (.app (.app (.var 2) (.var 1)) (.var 0)) (.pi (.var 2) (.app (.var 2) (.var 0)))))) (.lam (.srt .type) (.lam (.srt .type) (.lam (.app (.app (.var 3) (.var 1)) (.lam (.var 1) (.var 1))) (.lam (.app (.app (.var 4) (.var 2)) (.lam (.var 2) (.var 2))) (.lam (.var 3) (.lam (.var 4) (.lam (.app (.app (.app (.var 10) (.app (.app (.var 7) (.var 5)) (.lam (.var 5) (.var 5)))) (.var 3)) (.var 2)) (.app (.app (.app (.app (.app (.var 9) (.var 6)) (.var 2)) (.lam (.var 6) (.lam (.app (.app (.app (.var 12) (.var 7)) (.var 3)) (.var 0)) (.app (.app (.app (.var 13) (.var 7)) (.app (.app (.app (.app (.var 9) (.var 8)) (.lam (.var 8) (.var 8))) (.var 6)) (.var 4))) (.app (.app (.app (.app (.var 9) (.var 8)) (.lam (.var 8) (.var 8))) (.var 5)) (.var 1)))))) (.app (.app (.app (.app (.app (.app (.var 9) (.app (.app (.var 8) (.var 6)) (.lam (.var 6) (.var 6)))) (.var 4)) (.lam (.app (.app (.var 8) (.var 6)) (.lam (.var 6) (.var 6))) (.lam (.app (.app (.app (.var 12) (.app (.app (.var 9) (.var 7)) (.lam (.var 7) (.var 7)))) (.var 5)) (.var 0)) (.app (.app (.app (.var 13) (.var 7)) (.app (.app (.app (.app (.var 9) (.var 8)) (.lam (.var 8) (.var 8))) (.var 6)) (.var 4))) (.app (.app (.app (.app (.var 9) (.var 8)) (.lam (.var 8) (.var 8))) (.var 1)) (.var 4)))))) (.app (.app (.var 10) (.var 5)) (.app (.app (.app (.app (.var 7) (.var 6)) (.lam (.var 6) (.var 6))) (.var 4)) (.var 2)))) (.var 3)) (.var 0))) (.var 1)))))))))))))

theorem normalizedGoal_Eq_congr_eq :
    normalizedGoal_Eq_congr =
      LFBetaEta.normalForm [] PureBetaEta.normalizationFuel
        (encodeExpr PureDTTBench31.goal_Eq_Eq_congr) := by
  decide

theorem normalizedCandidate_Eq_congr_eq :
    normalizedCandidate_Eq_congr =
      LFBetaEta.normalForm [] PureBetaEta.normalizationFuel
        candidate_Eq_congr := by
  decide

def replay_Eq_congr : ReplayCase :=
  { name := "Eq_congr", actionCount := 43, traceSha256 := "7caaa2609b88372b13002c83b7911372e690765f93e284b610ce1893a75785ad", referenceTermSha256 := "5f266af1feb7465bfde6a53e76995406c990175b9b347ed217df038df7c5061a"
    goal := encodeExpr PureDTTBench31.goal_Eq_Eq_congr
    candidate := candidate_Eq_congr }

theorem replay_Eq_congr_accepted : accepts replay_Eq_congr = true := by
  decide

theorem replay_Eq_congr_sound :
    LFConversionProfileChecker.Deriv LFProfile.indexed [] []
      candidate_Eq_congr (encodeExpr PureDTTBench31.goal_Eq_Eq_congr) :=
  LFConversionProfileChecker.S1 replay_Eq_congr_accepted

def candidate_Eq_congrFun : LF.Term :=
  .lam (.pi (.srt .type) (.pi (.var 0) (.pi (.var 1) (.srt .type)))) (.lam (.pi (.srt .type) (.pi (.var 0) (.app (.app (.app (.var 2) (.var 1)) (.var 0)) (.var 0)))) (.lam (.pi (.srt .type) (.pi (.var 0) (.pi (.pi (.var 1) (.pi (.app (.app (.app (.var 4) (.var 2)) (.var 1)) (.var 0)) (.srt .type))) (.pi (.app (.app (.var 0) (.var 1)) (.app (.app (.var 3) (.var 2)) (.var 1))) (.pi (.var 3) (.pi (.app (.app (.app (.var 6) (.var 4)) (.var 3)) (.var 0)) (.app (.app (.var 3) (.var 1)) (.var 0)))))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.srt .type)) (.srt .type))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.srt .type)) (.pi (.app (.app (.var 2) (.var 1)) (.var 0)) (.pi (.var 2) (.app (.var 2) (.var 0)))))) (.lam (.srt .type) (.lam (.pi (.var 0) (.srt .type)) (.lam (.app (.app (.var 3) (.var 1)) (.var 0)) (.lam (.app (.app (.var 4) (.var 2)) (.var 1)) (.lam (.app (.app (.app (.var 8) (.app (.app (.var 5) (.var 3)) (.var 2))) (.var 1)) (.var 0)) (.lam (.var 4) (.app (.app (.app (.app (.app (.app (.var 8) (.app (.app (.var 7) (.var 5)) (.lam (.var 5) (.app (.var 5) (.var 0))))) (.var 3)) (.lam (.app (.app (.var 7) (.var 5)) (.lam (.var 5) (.app (.var 5) (.var 0)))) (.lam (.app (.app (.app (.var 11) (.app (.app (.var 8) (.var 6)) (.lam (.var 6) (.app (.var 6) (.var 0))))) (.var 4)) (.var 0)) (.app (.app (.app (.var 12) (.app (.var 6) (.var 2))) (.app (.app (.app (.app (.var 8) (.var 7)) (.lam (.var 7) (.app (.var 7) (.var 0)))) (.var 5)) (.var 2))) (.app (.app (.app (.app (.var 8) (.var 7)) (.lam (.var 7) (.app (.var 7) (.var 0)))) (.var 1)) (.var 2)))))) (.app (.app (.var 9) (.app (.var 4) (.var 0))) (.app (.app (.app (.app (.var 6) (.var 5)) (.lam (.var 5) (.app (.var 5) (.var 0)))) (.var 3)) (.var 0)))) (.var 2)) (.var 1))))))))))))

def normalizedGoal_Eq_congrFun : LF.Term :=
  .pi (.pi (.srt .type) (.pi (.var 0) (.pi (.var 1) (.srt .type)))) (.pi (.pi (.srt .type) (.pi (.var 0) (.app (.app (.app (.var 2) (.var 1)) (.var 0)) (.var 0)))) (.pi (.pi (.srt .type) (.pi (.var 0) (.pi (.pi (.var 1) (.pi (.app (.app (.app (.var 4) (.var 2)) (.var 1)) (.var 0)) (.srt .type))) (.pi (.app (.app (.var 0) (.var 1)) (.app (.app (.var 3) (.var 2)) (.var 1))) (.pi (.var 3) (.pi (.app (.app (.app (.var 6) (.var 4)) (.var 3)) (.var 0)) (.app (.app (.var 3) (.var 1)) (.var 0)))))))) (.pi (.pi (.srt .type) (.pi (.pi (.var 0) (.srt .type)) (.srt .type))) (.pi (.pi (.srt .type) (.pi (.pi (.var 0) (.srt .type)) (.pi (.app (.app (.var 2) (.var 1)) (.var 0)) (.pi (.var 2) (.app (.var 2) (.var 0)))))) (.pi (.srt .type) (.pi (.pi (.var 0) (.srt .type)) (.pi (.app (.app (.var 3) (.var 1)) (.var 0)) (.pi (.app (.app (.var 4) (.var 2)) (.var 1)) (.pi (.app (.app (.app (.var 8) (.app (.app (.var 5) (.var 3)) (.var 2))) (.var 1)) (.var 0)) (.pi (.var 4) (.app (.app (.app (.var 10) (.app (.var 4) (.var 0))) (.app (.app (.app (.app (.var 6) (.var 5)) (.var 4)) (.var 3)) (.var 0))) (.app (.app (.app (.app (.var 6) (.var 5)) (.var 4)) (.var 2)) (.var 0)))))))))))))

def normalizedCandidate_Eq_congrFun : LF.Term :=
  .lam (.pi (.srt .type) (.pi (.var 0) (.pi (.var 1) (.srt .type)))) (.lam (.pi (.srt .type) (.pi (.var 0) (.app (.app (.app (.var 2) (.var 1)) (.var 0)) (.var 0)))) (.lam (.pi (.srt .type) (.pi (.var 0) (.pi (.pi (.var 1) (.pi (.app (.app (.app (.var 4) (.var 2)) (.var 1)) (.var 0)) (.srt .type))) (.pi (.app (.app (.var 0) (.var 1)) (.app (.app (.var 3) (.var 2)) (.var 1))) (.pi (.var 3) (.pi (.app (.app (.app (.var 6) (.var 4)) (.var 3)) (.var 0)) (.app (.app (.var 3) (.var 1)) (.var 0)))))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.srt .type)) (.srt .type))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.srt .type)) (.pi (.app (.app (.var 2) (.var 1)) (.var 0)) (.pi (.var 2) (.app (.var 2) (.var 0)))))) (.lam (.srt .type) (.lam (.pi (.var 0) (.srt .type)) (.lam (.app (.app (.var 3) (.var 1)) (.var 0)) (.lam (.app (.app (.var 4) (.var 2)) (.var 1)) (.lam (.app (.app (.app (.var 8) (.app (.app (.var 5) (.var 3)) (.var 2))) (.var 1)) (.var 0)) (.lam (.var 4) (.app (.app (.app (.app (.app (.app (.var 8) (.app (.app (.var 7) (.var 5)) (.var 4))) (.var 3)) (.lam (.app (.app (.var 7) (.var 5)) (.var 4)) (.lam (.app (.app (.app (.var 11) (.app (.app (.var 8) (.var 6)) (.var 5))) (.var 4)) (.var 0)) (.app (.app (.app (.var 12) (.app (.var 6) (.var 2))) (.app (.app (.app (.app (.var 8) (.var 7)) (.var 6)) (.var 5)) (.var 2))) (.app (.app (.app (.app (.var 8) (.var 7)) (.var 6)) (.var 1)) (.var 2)))))) (.app (.app (.var 9) (.app (.var 4) (.var 0))) (.app (.app (.app (.app (.var 6) (.var 5)) (.var 4)) (.var 3)) (.var 0)))) (.var 2)) (.var 1))))))))))))

theorem normalizedGoal_Eq_congrFun_eq :
    normalizedGoal_Eq_congrFun =
      LFBetaEta.normalForm [] PureBetaEta.normalizationFuel
        (encodeExpr PureDTTBench31.goal_Eq_Eq_congrFun) := by
  decide

theorem normalizedCandidate_Eq_congrFun_eq :
    normalizedCandidate_Eq_congrFun =
      LFBetaEta.normalForm [] PureBetaEta.normalizationFuel
        candidate_Eq_congrFun := by
  decide

def replay_Eq_congrFun : ReplayCase :=
  { name := "Eq_congrFun", actionCount := 32, traceSha256 := "d712a523f6ca6f02699679495a55d4b1d43bf73aa50e40eeed57409246260dc4", referenceTermSha256 := "a864ff053535bb95cb12159dafb1285319e10ac6c4d41936772034b890ee034d"
    goal := encodeExpr PureDTTBench31.goal_Eq_Eq_congrFun
    candidate := candidate_Eq_congrFun }

theorem replay_Eq_congrFun_accepted : accepts replay_Eq_congrFun = true := by
  decide

theorem replay_Eq_congrFun_sound :
    LFConversionProfileChecker.Deriv LFProfile.indexed [] []
      candidate_Eq_congrFun (encodeExpr PureDTTBench31.goal_Eq_Eq_congrFun) :=
  LFConversionProfileChecker.S1 replay_Eq_congrFun_accepted

def candidate_Eq_mp : LF.Term :=
  .lam (.pi (.srt .type) (.pi (.srt .type) (.srt .type))) (.lam (.pi (.srt .type) (.app (.app (.var 1) (.var 0)) (.var 0))) (.lam (.pi (.srt .type) (.pi (.pi (.srt .type) (.pi (.app (.app (.var 3) (.var 1)) (.var 0)) (.srt .type))) (.pi (.app (.app (.var 0) (.var 1)) (.app (.var 2) (.var 1))) (.pi (.srt .type) (.pi (.app (.app (.var 5) (.var 3)) (.var 0)) (.app (.app (.var 3) (.var 1)) (.var 0))))))) (.lam (.srt .type) (.lam (.srt .type) (.lam (.app (.app (.var 4) (.var 1)) (.var 0)) (.lam (.var 2) (.app (.app (.app (.app (.app (.var 4) (.var 3)) (.lam (.srt .type) (.lam (.app (.app (.var 7) (.var 4)) (.var 0)) (.var 1)))) (.var 0)) (.var 2)) (.var 1))))))))

def normalizedGoal_Eq_mp : LF.Term :=
  .pi (.pi (.srt .type) (.pi (.srt .type) (.srt .type))) (.pi (.pi (.srt .type) (.app (.app (.var 1) (.var 0)) (.var 0))) (.pi (.pi (.srt .type) (.pi (.pi (.srt .type) (.pi (.app (.app (.var 3) (.var 1)) (.var 0)) (.srt .type))) (.pi (.app (.app (.var 0) (.var 1)) (.app (.var 2) (.var 1))) (.pi (.srt .type) (.pi (.app (.app (.var 5) (.var 3)) (.var 0)) (.app (.app (.var 3) (.var 1)) (.var 0))))))) (.pi (.srt .type) (.pi (.srt .type) (.pi (.app (.app (.var 4) (.var 1)) (.var 0)) (.pi (.var 2) (.var 2)))))))

def normalizedCandidate_Eq_mp : LF.Term :=
  .lam (.pi (.srt .type) (.pi (.srt .type) (.srt .type))) (.lam (.pi (.srt .type) (.app (.app (.var 1) (.var 0)) (.var 0))) (.lam (.pi (.srt .type) (.pi (.pi (.srt .type) (.pi (.app (.app (.var 3) (.var 1)) (.var 0)) (.srt .type))) (.pi (.app (.app (.var 0) (.var 1)) (.app (.var 2) (.var 1))) (.pi (.srt .type) (.pi (.app (.app (.var 5) (.var 3)) (.var 0)) (.app (.app (.var 3) (.var 1)) (.var 0))))))) (.lam (.srt .type) (.lam (.srt .type) (.lam (.app (.app (.var 4) (.var 1)) (.var 0)) (.lam (.var 2) (.app (.app (.app (.app (.app (.var 4) (.var 3)) (.lam (.srt .type) (.lam (.app (.app (.var 7) (.var 4)) (.var 0)) (.var 1)))) (.var 0)) (.var 2)) (.var 1))))))))

theorem normalizedGoal_Eq_mp_eq :
    normalizedGoal_Eq_mp =
      LFBetaEta.normalForm [] PureBetaEta.normalizationFuel
        (encodeExpr PureDTTBench31.goal_Eq_Eq_mp) := by
  decide

theorem normalizedCandidate_Eq_mp_eq :
    normalizedCandidate_Eq_mp =
      LFBetaEta.normalForm [] PureBetaEta.normalizationFuel
        candidate_Eq_mp := by
  decide

def replay_Eq_mp : ReplayCase :=
  { name := "Eq_mp", actionCount := 6, traceSha256 := "d8dca2a9d3eddd622d6a3c7f78b34614361cf9b1c09de4b68126909071fae90b", referenceTermSha256 := "18f87872890dc1446b3c6eb11a33b8261d3a69e55f941a4ee5484dd80384445a"
    goal := encodeExpr PureDTTBench31.goal_Eq_Eq_mp
    candidate := candidate_Eq_mp }

theorem replay_Eq_mp_accepted : accepts replay_Eq_mp = true := by
  decide

theorem replay_Eq_mp_sound :
    LFConversionProfileChecker.Deriv LFProfile.indexed [] []
      candidate_Eq_mp (encodeExpr PureDTTBench31.goal_Eq_Eq_mp) :=
  LFConversionProfileChecker.S1 replay_Eq_mp_accepted

def candidate_Nat_zero_le : LF.Term :=
  .lam (.srt .type) (.lam (.var 0) (.lam (.pi (.var 1) (.var 2)) (.lam (.pi (.pi (.var 2) (.srt .type)) (.pi (.app (.var 0) (.var 2)) (.pi (.pi (.var 4) (.pi (.app (.var 2) (.var 0)) (.app (.var 3) (.app (.var 4) (.var 1))))) (.pi (.var 5) (.app (.var 3) (.var 0)))))) (.lam (.pi (.var 3) (.pi (.var 4) (.srt .type))) (.lam (.pi (.var 4) (.app (.app (.var 1) (.var 0)) (.var 0))) (.lam (.pi (.var 5) (.pi (.var 6) (.pi (.app (.app (.var 3) (.var 1)) (.var 0)) (.app (.app (.var 4) (.var 2)) (.app (.var 6) (.var 1)))))) (.lam (.pi (.var 6) (.pi (.pi (.var 7) (.pi (.app (.app (.var 4) (.var 1)) (.var 0)) (.srt .type))) (.pi (.app (.app (.var 0) (.var 1)) (.app (.var 3) (.var 1))) (.pi (.pi (.var 9) (.pi (.app (.app (.var 6) (.var 3)) (.var 0)) (.pi (.app (.app (.var 3) (.var 1)) (.var 0)) (.app (.app (.var 4) (.app (.var 10) (.var 2))) (.app (.app (.app (.var 6) (.var 5)) (.var 2)) (.var 1)))))) (.pi (.var 10) (.pi (.app (.app (.var 7) (.var 4)) (.var 0)) (.app (.app (.var 4) (.var 1)) (.var 0)))))))) (.lam (.var 7) (.app (.app (.app (.app (.var 5) (.lam (.var 8) (.app (.app (.var 5) (.var 8)) (.var 0)))) (.app (.var 3) (.var 7))) (.lam (.var 8) (.lam (.app (.lam (.var 9) (.app (.app (.var 6) (.var 9)) (.var 0))) (.var 0)) (.app (.app (.app (.var 4) (.var 9)) (.var 1)) (.var 0))))) (.var 0))))))))))

def normalizedGoal_Nat_zero_le : LF.Term :=
  .pi (.srt .type) (.pi (.var 0) (.pi (.pi (.var 1) (.var 2)) (.pi (.pi (.pi (.var 2) (.srt .type)) (.pi (.app (.var 0) (.var 2)) (.pi (.pi (.var 4) (.pi (.app (.var 2) (.var 0)) (.app (.var 3) (.app (.var 4) (.var 1))))) (.pi (.var 5) (.app (.var 3) (.var 0)))))) (.pi (.pi (.var 3) (.pi (.var 4) (.srt .type))) (.pi (.pi (.var 4) (.app (.app (.var 1) (.var 0)) (.var 0))) (.pi (.pi (.var 5) (.pi (.var 6) (.pi (.app (.app (.var 3) (.var 1)) (.var 0)) (.app (.app (.var 4) (.var 2)) (.app (.var 6) (.var 1)))))) (.pi (.pi (.var 6) (.pi (.pi (.var 7) (.pi (.app (.app (.var 4) (.var 1)) (.var 0)) (.srt .type))) (.pi (.app (.app (.var 0) (.var 1)) (.app (.var 3) (.var 1))) (.pi (.pi (.var 9) (.pi (.app (.app (.var 6) (.var 3)) (.var 0)) (.pi (.app (.app (.var 3) (.var 1)) (.var 0)) (.app (.app (.var 4) (.app (.var 10) (.var 2))) (.app (.app (.app (.var 6) (.var 5)) (.var 2)) (.var 1)))))) (.pi (.var 10) (.pi (.app (.app (.var 7) (.var 4)) (.var 0)) (.app (.app (.var 4) (.var 1)) (.var 0)))))))) (.pi (.var 7) (.app (.app (.var 4) (.var 7)) (.var 0))))))))))

def normalizedCandidate_Nat_zero_le : LF.Term :=
  .lam (.srt .type) (.lam (.var 0) (.lam (.pi (.var 1) (.var 2)) (.lam (.pi (.pi (.var 2) (.srt .type)) (.pi (.app (.var 0) (.var 2)) (.pi (.pi (.var 4) (.pi (.app (.var 2) (.var 0)) (.app (.var 3) (.app (.var 4) (.var 1))))) (.pi (.var 5) (.app (.var 3) (.var 0)))))) (.lam (.pi (.var 3) (.pi (.var 4) (.srt .type))) (.lam (.pi (.var 4) (.app (.app (.var 1) (.var 0)) (.var 0))) (.lam (.pi (.var 5) (.pi (.var 6) (.pi (.app (.app (.var 3) (.var 1)) (.var 0)) (.app (.app (.var 4) (.var 2)) (.app (.var 6) (.var 1)))))) (.lam (.pi (.var 6) (.pi (.pi (.var 7) (.pi (.app (.app (.var 4) (.var 1)) (.var 0)) (.srt .type))) (.pi (.app (.app (.var 0) (.var 1)) (.app (.var 3) (.var 1))) (.pi (.pi (.var 9) (.pi (.app (.app (.var 6) (.var 3)) (.var 0)) (.pi (.app (.app (.var 3) (.var 1)) (.var 0)) (.app (.app (.var 4) (.app (.var 10) (.var 2))) (.app (.app (.app (.var 6) (.var 5)) (.var 2)) (.var 1)))))) (.pi (.var 10) (.pi (.app (.app (.var 7) (.var 4)) (.var 0)) (.app (.app (.var 4) (.var 1)) (.var 0)))))))) (.app (.app (.app (.var 4) (.app (.var 3) (.var 6))) (.app (.var 2) (.var 6))) (.app (.var 1) (.var 6))))))))))

theorem normalizedGoal_Nat_zero_le_eq :
    normalizedGoal_Nat_zero_le =
      LFBetaEta.normalForm [] PureBetaEta.normalizationFuel
        (encodeExpr PureDTTBench31.goal_Leq_Nat_zero_le) := by
  decide

theorem normalizedCandidate_Nat_zero_le_eq :
    normalizedCandidate_Nat_zero_le =
      LFBetaEta.normalForm [] PureBetaEta.normalizationFuel
        candidate_Nat_zero_le := by
  decide

def replay_Nat_zero_le : ReplayCase :=
  { name := "Nat_zero_le", actionCount := 11, traceSha256 := "dfb13e02b813d8d9b041bb9e84417554c1277fa4c77c8477c9e0261c6d801aa6", referenceTermSha256 := "a596f086d148b406d630fb4d362c92ace4763f913432809cd8feabe3f984b188"
    goal := encodeExpr PureDTTBench31.goal_Leq_Nat_zero_le
    candidate := candidate_Nat_zero_le }

theorem replay_Nat_zero_le_accepted : accepts replay_Nat_zero_le = true := by
  decide

theorem replay_Nat_zero_le_sound :
    LFConversionProfileChecker.Deriv LFProfile.indexed [] []
      candidate_Nat_zero_le (encodeExpr PureDTTBench31.goal_Leq_Nat_zero_le) :=
  LFConversionProfileChecker.S1 replay_Nat_zero_le_accepted

def candidate_Nat_succ_le_succ : LF.Term :=
  .lam (.srt .type) (.lam (.var 0) (.lam (.pi (.var 1) (.var 2)) (.lam (.pi (.pi (.var 2) (.srt .type)) (.pi (.app (.var 0) (.var 2)) (.pi (.pi (.var 4) (.pi (.app (.var 2) (.var 0)) (.app (.var 3) (.app (.var 4) (.var 1))))) (.pi (.var 5) (.app (.var 3) (.var 0)))))) (.lam (.pi (.var 3) (.pi (.var 4) (.srt .type))) (.lam (.pi (.var 4) (.app (.app (.var 1) (.var 0)) (.var 0))) (.lam (.pi (.var 5) (.pi (.var 6) (.pi (.app (.app (.var 3) (.var 1)) (.var 0)) (.app (.app (.var 4) (.var 2)) (.app (.var 6) (.var 1)))))) (.lam (.pi (.var 6) (.pi (.pi (.var 7) (.pi (.app (.app (.var 4) (.var 1)) (.var 0)) (.srt .type))) (.pi (.app (.app (.var 0) (.var 1)) (.app (.var 3) (.var 1))) (.pi (.pi (.var 9) (.pi (.app (.app (.var 6) (.var 3)) (.var 0)) (.pi (.app (.app (.var 3) (.var 1)) (.var 0)) (.app (.app (.var 4) (.app (.var 10) (.var 2))) (.app (.app (.app (.var 6) (.var 5)) (.var 2)) (.var 1)))))) (.pi (.var 10) (.pi (.app (.app (.var 7) (.var 4)) (.var 0)) (.app (.app (.var 4) (.var 1)) (.var 0)))))))) (.lam (.var 7) (.lam (.var 8) (.lam (.app (.app (.var 5) (.var 1)) (.var 0)) (.app (.app (.app (.app (.app (.app (.var 3) (.var 2)) (.lam (.var 10) (.lam (.app (.app (.var 7) (.var 3)) (.var 0)) (.app (.app (.var 8) (.app (.var 10) (.var 4))) (.app (.var 10) (.var 1)))))) (.app (.var 5) (.app (.var 8) (.var 2)))) (.lam (.var 10) (.lam (.app (.app (.var 7) (.var 3)) (.var 0)) (.lam (.app (.app (.lam (.var 12) (.lam (.app (.app (.var 9) (.var 5)) (.var 0)) (.app (.app (.var 10) (.app (.var 12) (.var 6))) (.app (.var 12) (.var 1))))) (.var 1)) (.var 0)) (.app (.app (.app (.var 7) (.app (.var 11) (.var 5))) (.app (.var 11) (.var 2))) (.var 0)))))) (.var 1)) (.var 0))))))))))))

def normalizedGoal_Nat_succ_le_succ : LF.Term :=
  .pi (.srt .type) (.pi (.var 0) (.pi (.pi (.var 1) (.var 2)) (.pi (.pi (.pi (.var 2) (.srt .type)) (.pi (.app (.var 0) (.var 2)) (.pi (.pi (.var 4) (.pi (.app (.var 2) (.var 0)) (.app (.var 3) (.app (.var 4) (.var 1))))) (.pi (.var 5) (.app (.var 3) (.var 0)))))) (.pi (.pi (.var 3) (.pi (.var 4) (.srt .type))) (.pi (.pi (.var 4) (.app (.app (.var 1) (.var 0)) (.var 0))) (.pi (.pi (.var 5) (.pi (.var 6) (.pi (.app (.app (.var 3) (.var 1)) (.var 0)) (.app (.app (.var 4) (.var 2)) (.app (.var 6) (.var 1)))))) (.pi (.pi (.var 6) (.pi (.pi (.var 7) (.pi (.app (.app (.var 4) (.var 1)) (.var 0)) (.srt .type))) (.pi (.app (.app (.var 0) (.var 1)) (.app (.var 3) (.var 1))) (.pi (.pi (.var 9) (.pi (.app (.app (.var 6) (.var 3)) (.var 0)) (.pi (.app (.app (.var 3) (.var 1)) (.var 0)) (.app (.app (.var 4) (.app (.var 10) (.var 2))) (.app (.app (.app (.var 6) (.var 5)) (.var 2)) (.var 1)))))) (.pi (.var 10) (.pi (.app (.app (.var 7) (.var 4)) (.var 0)) (.app (.app (.var 4) (.var 1)) (.var 0)))))))) (.pi (.var 7) (.pi (.var 8) (.pi (.app (.app (.var 5) (.var 1)) (.var 0)) (.app (.app (.var 6) (.app (.var 8) (.var 2))) (.app (.var 8) (.var 1)))))))))))))

def normalizedCandidate_Nat_succ_le_succ : LF.Term :=
  .lam (.srt .type) (.lam (.var 0) (.lam (.pi (.var 1) (.var 2)) (.lam (.pi (.pi (.var 2) (.srt .type)) (.pi (.app (.var 0) (.var 2)) (.pi (.pi (.var 4) (.pi (.app (.var 2) (.var 0)) (.app (.var 3) (.app (.var 4) (.var 1))))) (.pi (.var 5) (.app (.var 3) (.var 0)))))) (.lam (.pi (.var 3) (.pi (.var 4) (.srt .type))) (.lam (.pi (.var 4) (.app (.app (.var 1) (.var 0)) (.var 0))) (.lam (.pi (.var 5) (.pi (.var 6) (.pi (.app (.app (.var 3) (.var 1)) (.var 0)) (.app (.app (.var 4) (.var 2)) (.app (.var 6) (.var 1)))))) (.lam (.pi (.var 6) (.pi (.pi (.var 7) (.pi (.app (.app (.var 4) (.var 1)) (.var 0)) (.srt .type))) (.pi (.app (.app (.var 0) (.var 1)) (.app (.var 3) (.var 1))) (.pi (.pi (.var 9) (.pi (.app (.app (.var 6) (.var 3)) (.var 0)) (.pi (.app (.app (.var 3) (.var 1)) (.var 0)) (.app (.app (.var 4) (.app (.var 10) (.var 2))) (.app (.app (.app (.var 6) (.var 5)) (.var 2)) (.var 1)))))) (.pi (.var 10) (.pi (.app (.app (.var 7) (.var 4)) (.var 0)) (.app (.app (.var 4) (.var 1)) (.var 0)))))))) (.lam (.var 7) (.app (.app (.app (.app (.var 1) (.var 0)) (.lam (.var 8) (.lam (.app (.app (.var 5) (.var 1)) (.var 0)) (.app (.app (.var 6) (.app (.var 8) (.var 2))) (.app (.var 8) (.var 1)))))) (.app (.var 3) (.app (.var 6) (.var 0)))) (.lam (.var 8) (.lam (.app (.app (.var 5) (.var 1)) (.var 0)) (.app (.app (.var 4) (.app (.var 8) (.var 2))) (.app (.var 8) (.var 1))))))))))))))

theorem normalizedGoal_Nat_succ_le_succ_eq :
    normalizedGoal_Nat_succ_le_succ =
      LFBetaEta.normalForm [] PureBetaEta.normalizationFuel
        (encodeExpr PureDTTBench31.goal_Leq_Nat_succ_le_succ) := by
  decide

theorem normalizedCandidate_Nat_succ_le_succ_eq :
    normalizedCandidate_Nat_succ_le_succ =
      LFBetaEta.normalForm [] PureBetaEta.normalizationFuel
        candidate_Nat_succ_le_succ := by
  decide

def replay_Nat_succ_le_succ : ReplayCase :=
  { name := "Nat_succ_le_succ", actionCount := 18, traceSha256 := "873a73bb8b97cb255962a63b1279283cf67f594281e2ce04c426fac67da73736", referenceTermSha256 := "8fe5b1651d7988a88e9525b58a30a7f81e18fda7fe4b41b067c829b04acfae23"
    goal := encodeExpr PureDTTBench31.goal_Leq_Nat_succ_le_succ
    candidate := candidate_Nat_succ_le_succ }

theorem replay_Nat_succ_le_succ_accepted : accepts replay_Nat_succ_le_succ = true := by
  decide

theorem replay_Nat_succ_le_succ_sound :
    LFConversionProfileChecker.Deriv LFProfile.indexed [] []
      candidate_Nat_succ_le_succ (encodeExpr PureDTTBench31.goal_Leq_Nat_succ_le_succ) :=
  LFConversionProfileChecker.S1 replay_Nat_succ_le_succ_accepted

def candidate_Nat_le_trans : LF.Term :=
  .lam (.srt .type) (.lam (.var 0) (.lam (.pi (.var 1) (.var 2)) (.lam (.pi (.pi (.var 2) (.srt .type)) (.pi (.app (.var 0) (.var 2)) (.pi (.pi (.var 4) (.pi (.app (.var 2) (.var 0)) (.app (.var 3) (.app (.var 4) (.var 1))))) (.pi (.var 5) (.app (.var 3) (.var 0)))))) (.lam (.pi (.var 3) (.pi (.var 4) (.srt .type))) (.lam (.pi (.var 4) (.app (.app (.var 1) (.var 0)) (.var 0))) (.lam (.pi (.var 5) (.pi (.var 6) (.pi (.app (.app (.var 3) (.var 1)) (.var 0)) (.app (.app (.var 4) (.var 2)) (.app (.var 6) (.var 1)))))) (.lam (.pi (.var 6) (.pi (.pi (.var 7) (.pi (.app (.app (.var 4) (.var 1)) (.var 0)) (.srt .type))) (.pi (.app (.app (.var 0) (.var 1)) (.app (.var 3) (.var 1))) (.pi (.pi (.var 9) (.pi (.app (.app (.var 6) (.var 3)) (.var 0)) (.pi (.app (.app (.var 3) (.var 1)) (.var 0)) (.app (.app (.var 4) (.app (.var 10) (.var 2))) (.app (.app (.app (.var 6) (.var 5)) (.var 2)) (.var 1)))))) (.pi (.var 10) (.pi (.app (.app (.var 7) (.var 4)) (.var 0)) (.app (.app (.var 4) (.var 1)) (.var 0)))))))) (.lam (.var 7) (.lam (.var 8) (.lam (.var 9) (.lam (.app (.app (.var 6) (.var 2)) (.var 1)) (.lam (.app (.app (.var 7) (.var 2)) (.var 1)) (.app (.app (.app (.app (.app (.app (.var 5) (.var 3)) (.lam (.var 12) (.lam (.app (.app (.var 9) (.var 4)) (.var 0)) (.app (.app (.var 10) (.var 6)) (.var 1))))) (.var 1)) (.lam (.var 12) (.lam (.app (.app (.var 9) (.var 4)) (.var 0)) (.lam (.app (.app (.lam (.var 14) (.lam (.app (.app (.var 11) (.var 6)) (.var 0)) (.app (.app (.var 12) (.var 8)) (.var 1)))) (.var 1)) (.var 0)) (.app (.app (.app (.var 9) (.var 7)) (.var 2)) (.var 0)))))) (.var 2)) (.var 0))))))))))))))

def normalizedGoal_Nat_le_trans : LF.Term :=
  .pi (.srt .type) (.pi (.var 0) (.pi (.pi (.var 1) (.var 2)) (.pi (.pi (.pi (.var 2) (.srt .type)) (.pi (.app (.var 0) (.var 2)) (.pi (.pi (.var 4) (.pi (.app (.var 2) (.var 0)) (.app (.var 3) (.app (.var 4) (.var 1))))) (.pi (.var 5) (.app (.var 3) (.var 0)))))) (.pi (.pi (.var 3) (.pi (.var 4) (.srt .type))) (.pi (.pi (.var 4) (.app (.app (.var 1) (.var 0)) (.var 0))) (.pi (.pi (.var 5) (.pi (.var 6) (.pi (.app (.app (.var 3) (.var 1)) (.var 0)) (.app (.app (.var 4) (.var 2)) (.app (.var 6) (.var 1)))))) (.pi (.pi (.var 6) (.pi (.pi (.var 7) (.pi (.app (.app (.var 4) (.var 1)) (.var 0)) (.srt .type))) (.pi (.app (.app (.var 0) (.var 1)) (.app (.var 3) (.var 1))) (.pi (.pi (.var 9) (.pi (.app (.app (.var 6) (.var 3)) (.var 0)) (.pi (.app (.app (.var 3) (.var 1)) (.var 0)) (.app (.app (.var 4) (.app (.var 10) (.var 2))) (.app (.app (.app (.var 6) (.var 5)) (.var 2)) (.var 1)))))) (.pi (.var 10) (.pi (.app (.app (.var 7) (.var 4)) (.var 0)) (.app (.app (.var 4) (.var 1)) (.var 0)))))))) (.pi (.var 7) (.pi (.var 8) (.pi (.var 9) (.pi (.app (.app (.var 6) (.var 2)) (.var 1)) (.pi (.app (.app (.var 7) (.var 2)) (.var 1)) (.app (.app (.var 8) (.var 4)) (.var 2))))))))))))))

def normalizedCandidate_Nat_le_trans : LF.Term :=
  .lam (.srt .type) (.lam (.var 0) (.lam (.pi (.var 1) (.var 2)) (.lam (.pi (.pi (.var 2) (.srt .type)) (.pi (.app (.var 0) (.var 2)) (.pi (.pi (.var 4) (.pi (.app (.var 2) (.var 0)) (.app (.var 3) (.app (.var 4) (.var 1))))) (.pi (.var 5) (.app (.var 3) (.var 0)))))) (.lam (.pi (.var 3) (.pi (.var 4) (.srt .type))) (.lam (.pi (.var 4) (.app (.app (.var 1) (.var 0)) (.var 0))) (.lam (.pi (.var 5) (.pi (.var 6) (.pi (.app (.app (.var 3) (.var 1)) (.var 0)) (.app (.app (.var 4) (.var 2)) (.app (.var 6) (.var 1)))))) (.lam (.pi (.var 6) (.pi (.pi (.var 7) (.pi (.app (.app (.var 4) (.var 1)) (.var 0)) (.srt .type))) (.pi (.app (.app (.var 0) (.var 1)) (.app (.var 3) (.var 1))) (.pi (.pi (.var 9) (.pi (.app (.app (.var 6) (.var 3)) (.var 0)) (.pi (.app (.app (.var 3) (.var 1)) (.var 0)) (.app (.app (.var 4) (.app (.var 10) (.var 2))) (.app (.app (.app (.var 6) (.var 5)) (.var 2)) (.var 1)))))) (.pi (.var 10) (.pi (.app (.app (.var 7) (.var 4)) (.var 0)) (.app (.app (.var 4) (.var 1)) (.var 0)))))))) (.lam (.var 7) (.lam (.var 8) (.lam (.var 9) (.lam (.app (.app (.var 6) (.var 2)) (.var 1)) (.app (.app (.app (.app (.app (.var 4) (.var 2)) (.lam (.var 11) (.lam (.app (.app (.var 8) (.var 3)) (.var 0)) (.app (.app (.var 9) (.var 5)) (.var 1))))) (.var 0)) (.lam (.var 11) (.lam (.app (.app (.var 8) (.var 3)) (.var 0)) (.app (.app (.var 7) (.var 5)) (.var 1))))) (.var 1)))))))))))))

theorem normalizedGoal_Nat_le_trans_eq :
    normalizedGoal_Nat_le_trans =
      LFBetaEta.normalForm [] PureBetaEta.normalizationFuel
        (encodeExpr PureDTTBench31.goal_Leq_Nat_le_trans) := by
  decide

theorem normalizedCandidate_Nat_le_trans_eq :
    normalizedCandidate_Nat_le_trans =
      LFBetaEta.normalForm [] PureBetaEta.normalizationFuel
        candidate_Nat_le_trans := by
  decide

def replay_Nat_le_trans : ReplayCase :=
  { name := "Nat_le_trans", actionCount := 12, traceSha256 := "d9acd41f597fef25c8a296fea37f03ff8ad01fd987ac697f28674759662201c3", referenceTermSha256 := "24764657f590cea5491a1bd1244941c9dc491a8b510029c7e7dd390f864c1b6f"
    goal := encodeExpr PureDTTBench31.goal_Leq_Nat_le_trans
    candidate := candidate_Nat_le_trans }

theorem replay_Nat_le_trans_accepted : accepts replay_Nat_le_trans = true := by
  decide

theorem replay_Nat_le_trans_sound :
    LFConversionProfileChecker.Deriv LFProfile.indexed [] []
      candidate_Nat_le_trans (encodeExpr PureDTTBench31.goal_Leq_Nat_le_trans) :=
  LFConversionProfileChecker.S1 replay_Nat_le_trans_accepted

def candidate_sSup_inter_le : LF.Term :=
  .lam (.pi (.srt .type) (.pi (.srt .type) (.srt .type))) (.lam (.pi (.srt .type) (.pi (.srt .type) (.pi (.var 1) (.pi (.var 1) (.app (.app (.var 4) (.var 3)) (.var 2)))))) (.lam (.pi (.srt .type) (.pi (.srt .type) (.pi (.app (.app (.var 3) (.var 1)) (.var 0)) (.var 2)))) (.lam (.pi (.srt .type) (.pi (.srt .type) (.pi (.app (.app (.var 4) (.var 1)) (.var 0)) (.var 1)))) (.lam (.srt .type) (.lam (.pi (.pi (.var 0) (.srt .type)) (.var 1)) (.lam (.pi (.var 1) (.pi (.var 2) (.srt .type))) (.lam (.pi (.var 2) (.pi (.var 3) (.var 4))) (.lam (.pi (.pi (.var 3) (.srt .type)) (.pi (.var 4) (.pi (.app (.var 1) (.var 0)) (.app (.app (.var 4) (.var 1)) (.app (.var 5) (.var 2)))))) (.lam (.pi (.pi (.var 4) (.srt .type)) (.pi (.var 5) (.pi (.pi (.var 6) (.pi (.app (.var 2) (.var 0)) (.app (.app (.var 6) (.var 1)) (.var 2)))) (.app (.app (.var 5) (.app (.var 6) (.var 2))) (.var 1))))) (.lam (.pi (.var 5) (.pi (.var 6) (.pi (.var 7) (.pi (.app (.app (.var 6) (.var 2)) (.var 1)) (.pi (.app (.app (.var 7) (.var 3)) (.var 1)) (.app (.app (.var 8) (.var 4)) (.app (.app (.var 7) (.var 3)) (.var 2)))))))) (.lam (.pi (.var 6) (.srt .type)) (.lam (.pi (.var 7) (.srt .type)) (.app (.app (.app (.var 3) (.lam (.var 8) (.app (.app (.var 13) (.app (.var 2) (.var 0))) (.app (.var 1) (.var 0))))) (.app (.app (.var 5) (.app (.var 7) (.lam (.var 8) (.app (.var 2) (.var 0))))) (.app (.var 7) (.lam (.var 8) (.app (.var 1) (.var 0)))))) (.lam (.var 8) (.lam (.app (.lam (.var 9) (.app (.app (.var 14) (.app (.var 3) (.var 0))) (.app (.var 2) (.var 0)))) (.var 0)) (.app (.app (.app (.app (.app (.var 4) (.var 1)) (.app (.var 9) (.lam (.var 10) (.app (.var 4) (.var 0))))) (.app (.var 9) (.lam (.var 10) (.app (.var 3) (.var 0))))) (.app (.app (.app (.var 6) (.lam (.var 10) (.app (.var 4) (.var 0)))) (.var 1)) (.app (.app (.app (.var 12) (.app (.var 3) (.var 1))) (.app (.var 2) (.var 1))) (.var 0)))) (.app (.app (.app (.var 6) (.lam (.var 10) (.app (.var 3) (.var 0)))) (.var 1)) (.app (.app (.app (.var 11) (.app (.var 3) (.var 1))) (.app (.var 2) (.var 1))) (.var 0)))))))))))))))))))

def normalizedGoal_sSup_inter_le : LF.Term :=
  .pi (.pi (.srt .type) (.pi (.srt .type) (.srt .type))) (.pi (.pi (.srt .type) (.pi (.srt .type) (.pi (.var 1) (.pi (.var 1) (.app (.app (.var 4) (.var 3)) (.var 2)))))) (.pi (.pi (.srt .type) (.pi (.srt .type) (.pi (.app (.app (.var 3) (.var 1)) (.var 0)) (.var 2)))) (.pi (.pi (.srt .type) (.pi (.srt .type) (.pi (.app (.app (.var 4) (.var 1)) (.var 0)) (.var 1)))) (.pi (.srt .type) (.pi (.pi (.pi (.var 0) (.srt .type)) (.var 1)) (.pi (.pi (.var 1) (.pi (.var 2) (.srt .type))) (.pi (.pi (.var 2) (.pi (.var 3) (.var 4))) (.pi (.pi (.pi (.var 3) (.srt .type)) (.pi (.var 4) (.pi (.app (.var 1) (.var 0)) (.app (.app (.var 4) (.var 1)) (.app (.var 5) (.var 2)))))) (.pi (.pi (.pi (.var 4) (.srt .type)) (.pi (.var 5) (.pi (.pi (.var 6) (.pi (.app (.var 2) (.var 0)) (.app (.app (.var 6) (.var 1)) (.var 2)))) (.app (.app (.var 5) (.app (.var 6) (.var 2))) (.var 1))))) (.pi (.pi (.var 5) (.pi (.var 6) (.pi (.var 7) (.pi (.app (.app (.var 6) (.var 2)) (.var 1)) (.pi (.app (.app (.var 7) (.var 3)) (.var 1)) (.app (.app (.var 8) (.var 4)) (.app (.app (.var 7) (.var 3)) (.var 2)))))))) (.pi (.pi (.var 6) (.srt .type)) (.pi (.pi (.var 7) (.srt .type)) (.app (.app (.var 6) (.app (.var 7) (.lam (.var 8) (.app (.app (.var 13) (.app (.var 2) (.var 0))) (.app (.var 1) (.var 0)))))) (.app (.app (.var 5) (.app (.var 7) (.var 1))) (.app (.var 7) (.var 0))))))))))))))))

def normalizedCandidate_sSup_inter_le : LF.Term :=
  .lam (.pi (.srt .type) (.pi (.srt .type) (.srt .type))) (.lam (.pi (.srt .type) (.pi (.srt .type) (.pi (.var 1) (.pi (.var 1) (.app (.app (.var 4) (.var 3)) (.var 2)))))) (.lam (.pi (.srt .type) (.pi (.srt .type) (.pi (.app (.app (.var 3) (.var 1)) (.var 0)) (.var 2)))) (.lam (.pi (.srt .type) (.pi (.srt .type) (.pi (.app (.app (.var 4) (.var 1)) (.var 0)) (.var 1)))) (.lam (.srt .type) (.lam (.pi (.pi (.var 0) (.srt .type)) (.var 1)) (.lam (.pi (.var 1) (.pi (.var 2) (.srt .type))) (.lam (.pi (.var 2) (.pi (.var 3) (.var 4))) (.lam (.pi (.pi (.var 3) (.srt .type)) (.pi (.var 4) (.pi (.app (.var 1) (.var 0)) (.app (.app (.var 4) (.var 1)) (.app (.var 5) (.var 2)))))) (.lam (.pi (.pi (.var 4) (.srt .type)) (.pi (.var 5) (.pi (.pi (.var 6) (.pi (.app (.var 2) (.var 0)) (.app (.app (.var 6) (.var 1)) (.var 2)))) (.app (.app (.var 5) (.app (.var 6) (.var 2))) (.var 1))))) (.lam (.pi (.var 5) (.pi (.var 6) (.pi (.var 7) (.pi (.app (.app (.var 6) (.var 2)) (.var 1)) (.pi (.app (.app (.var 7) (.var 3)) (.var 1)) (.app (.app (.var 8) (.var 4)) (.app (.app (.var 7) (.var 3)) (.var 2)))))))) (.lam (.pi (.var 6) (.srt .type)) (.lam (.pi (.var 7) (.srt .type)) (.app (.app (.app (.var 3) (.lam (.var 8) (.app (.app (.var 13) (.app (.var 2) (.var 0))) (.app (.var 1) (.var 0))))) (.app (.app (.var 5) (.app (.var 7) (.var 1))) (.app (.var 7) (.var 0)))) (.lam (.var 8) (.lam (.app (.app (.var 13) (.app (.var 2) (.var 0))) (.app (.var 1) (.var 0))) (.app (.app (.app (.app (.app (.var 4) (.var 1)) (.app (.var 9) (.var 3))) (.app (.var 9) (.var 2))) (.app (.app (.app (.var 6) (.var 3)) (.var 1)) (.app (.app (.app (.var 12) (.app (.var 3) (.var 1))) (.app (.var 2) (.var 1))) (.var 0)))) (.app (.app (.app (.var 6) (.var 2)) (.var 1)) (.app (.app (.app (.var 11) (.app (.var 3) (.var 1))) (.app (.var 2) (.var 1))) (.var 0)))))))))))))))))))

theorem normalizedGoal_sSup_inter_le_eq :
    normalizedGoal_sSup_inter_le =
      LFBetaEta.normalForm [] PureBetaEta.normalizationFuel
        (encodeExpr PureDTTBench31.goal_Leq_sSup_inter_le) := by
  decide

theorem normalizedCandidate_sSup_inter_le_eq :
    normalizedCandidate_sSup_inter_le =
      LFBetaEta.normalForm [] PureBetaEta.normalizationFuel
        candidate_sSup_inter_le := by
  decide

def replay_sSup_inter_le : ReplayCase :=
  { name := "sSup_inter_le", actionCount := 41, traceSha256 := "34089d0605db600f68e5083dd68893f2d1e2dd62aee5140b09fbfd4576df1115", referenceTermSha256 := "bf8fc191abf9572ee70734d00c4380ae2002202ebff5083c151bf5810e269bd8"
    goal := encodeExpr PureDTTBench31.goal_Leq_sSup_inter_le
    candidate := candidate_sSup_inter_le }

theorem replay_sSup_inter_le_accepted : accepts replay_sSup_inter_le = true := by
  decide

theorem replay_sSup_inter_le_sound :
    LFConversionProfileChecker.Deriv LFProfile.indexed [] []
      candidate_sSup_inter_le (encodeExpr PureDTTBench31.goal_Leq_sSup_inter_le) :=
  LFConversionProfileChecker.S1 replay_sSup_inter_le_accepted

def candidate_Iff_refl : LF.Term :=
  .lam (.pi (.srt .type) (.pi (.srt .type) (.srt .type))) (.lam (.pi (.srt .type) (.pi (.srt .type) (.pi (.pi (.var 1) (.var 1)) (.pi (.pi (.var 1) (.var 3)) (.app (.app (.var 4) (.var 3)) (.var 2)))))) (.lam (.srt .type) (.app (.app (.app (.app (.var 1) (.var 0)) (.var 0)) (.lam (.var 0) (.var 0))) (.lam (.var 0) (.var 0)))))

def normalizedGoal_Iff_refl : LF.Term :=
  .pi (.pi (.srt .type) (.pi (.srt .type) (.srt .type))) (.pi (.pi (.srt .type) (.pi (.srt .type) (.pi (.pi (.var 1) (.var 1)) (.pi (.pi (.var 1) (.var 3)) (.app (.app (.var 4) (.var 3)) (.var 2)))))) (.pi (.srt .type) (.app (.app (.var 2) (.var 0)) (.var 0))))

def normalizedCandidate_Iff_refl : LF.Term :=
  .lam (.pi (.srt .type) (.pi (.srt .type) (.srt .type))) (.lam (.pi (.srt .type) (.pi (.srt .type) (.pi (.pi (.var 1) (.var 1)) (.pi (.pi (.var 1) (.var 3)) (.app (.app (.var 4) (.var 3)) (.var 2)))))) (.lam (.srt .type) (.app (.app (.app (.app (.var 1) (.var 0)) (.var 0)) (.lam (.var 0) (.var 0))) (.lam (.var 0) (.var 0)))))

theorem normalizedGoal_Iff_refl_eq :
    normalizedGoal_Iff_refl =
      LFBetaEta.normalForm [] PureBetaEta.normalizationFuel
        (encodeExpr PureDTTBench31.goal_Logic_Iff_refl) := by
  decide

theorem normalizedCandidate_Iff_refl_eq :
    normalizedCandidate_Iff_refl =
      LFBetaEta.normalForm [] PureBetaEta.normalizationFuel
        candidate_Iff_refl := by
  decide

def replay_Iff_refl : ReplayCase :=
  { name := "Iff_refl", actionCount := 5, traceSha256 := "af86bf0e815481063daecb76a76512adabdc56317771dbbdfde85c7dd3b76aba", referenceTermSha256 := "15bd9c48335622bb344275db6b0c215c58c05b565808487dc0ce3cf875c200a7"
    goal := encodeExpr PureDTTBench31.goal_Logic_Iff_refl
    candidate := candidate_Iff_refl }

theorem replay_Iff_refl_accepted : accepts replay_Iff_refl = true := by
  decide

theorem replay_Iff_refl_sound :
    LFConversionProfileChecker.Deriv LFProfile.indexed [] []
      candidate_Iff_refl (encodeExpr PureDTTBench31.goal_Logic_Iff_refl) :=
  LFConversionProfileChecker.S1 replay_Iff_refl_accepted

def candidate_Or_elim : LF.Term :=
  .lam (.pi (.srt .type) (.pi (.srt .type) (.srt .type))) (.lam (.pi (.srt .type) (.pi (.srt .type) (.pi (.var 1) (.app (.app (.var 3) (.var 2)) (.var 1))))) (.lam (.pi (.srt .type) (.pi (.srt .type) (.pi (.var 0) (.app (.app (.var 4) (.var 2)) (.var 1))))) (.lam (.pi (.srt .type) (.pi (.srt .type) (.pi (.pi (.app (.app (.var 4) (.var 1)) (.var 0)) (.srt .type)) (.pi (.pi (.var 2) (.app (.var 1) (.app (.app (.app (.var 5) (.var 3)) (.var 2)) (.var 0)))) (.pi (.pi (.var 2) (.app (.var 2) (.app (.app (.app (.var 5) (.var 4)) (.var 3)) (.var 0)))) (.pi (.app (.app (.var 7) (.var 4)) (.var 3)) (.app (.var 3) (.var 0)))))))) (.lam (.srt .type) (.lam (.srt .type) (.lam (.srt .type) (.lam (.app (.app (.var 6) (.var 2)) (.var 1)) (.lam (.pi (.var 3) (.var 2)) (.lam (.pi (.var 3) (.var 3)) (.app (.app (.app (.app (.app (.app (.var 6) (.var 5)) (.var 4)) (.lam (.app (.app (.var 9) (.var 5)) (.var 4)) (.var 4))) (.lam (.var 5) (.app (.var 2) (.var 0)))) (.lam (.var 4) (.app (.var 1) (.var 0)))) (.var 2)))))))))))

def normalizedGoal_Or_elim : LF.Term :=
  .pi (.pi (.srt .type) (.pi (.srt .type) (.srt .type))) (.pi (.pi (.srt .type) (.pi (.srt .type) (.pi (.var 1) (.app (.app (.var 3) (.var 2)) (.var 1))))) (.pi (.pi (.srt .type) (.pi (.srt .type) (.pi (.var 0) (.app (.app (.var 4) (.var 2)) (.var 1))))) (.pi (.pi (.srt .type) (.pi (.srt .type) (.pi (.pi (.app (.app (.var 4) (.var 1)) (.var 0)) (.srt .type)) (.pi (.pi (.var 2) (.app (.var 1) (.app (.app (.app (.var 5) (.var 3)) (.var 2)) (.var 0)))) (.pi (.pi (.var 2) (.app (.var 2) (.app (.app (.app (.var 5) (.var 4)) (.var 3)) (.var 0)))) (.pi (.app (.app (.var 7) (.var 4)) (.var 3)) (.app (.var 3) (.var 0)))))))) (.pi (.srt .type) (.pi (.srt .type) (.pi (.srt .type) (.pi (.app (.app (.var 6) (.var 2)) (.var 1)) (.pi (.pi (.var 3) (.var 2)) (.pi (.pi (.var 3) (.var 3)) (.var 3))))))))))

def normalizedCandidate_Or_elim : LF.Term :=
  .lam (.pi (.srt .type) (.pi (.srt .type) (.srt .type))) (.lam (.pi (.srt .type) (.pi (.srt .type) (.pi (.var 1) (.app (.app (.var 3) (.var 2)) (.var 1))))) (.lam (.pi (.srt .type) (.pi (.srt .type) (.pi (.var 0) (.app (.app (.var 4) (.var 2)) (.var 1))))) (.lam (.pi (.srt .type) (.pi (.srt .type) (.pi (.pi (.app (.app (.var 4) (.var 1)) (.var 0)) (.srt .type)) (.pi (.pi (.var 2) (.app (.var 1) (.app (.app (.app (.var 5) (.var 3)) (.var 2)) (.var 0)))) (.pi (.pi (.var 2) (.app (.var 2) (.app (.app (.app (.var 5) (.var 4)) (.var 3)) (.var 0)))) (.pi (.app (.app (.var 7) (.var 4)) (.var 3)) (.app (.var 3) (.var 0)))))))) (.lam (.srt .type) (.lam (.srt .type) (.lam (.srt .type) (.lam (.app (.app (.var 6) (.var 2)) (.var 1)) (.lam (.pi (.var 3) (.var 2)) (.lam (.pi (.var 3) (.var 3)) (.app (.app (.app (.app (.app (.app (.var 6) (.var 5)) (.var 4)) (.lam (.app (.app (.var 9) (.var 5)) (.var 4)) (.var 4))) (.var 1)) (.var 0)) (.var 2)))))))))))

theorem normalizedGoal_Or_elim_eq :
    normalizedGoal_Or_elim =
      LFBetaEta.normalForm [] PureBetaEta.normalizationFuel
        (encodeExpr PureDTTBench31.goal_Logic_Or_elim) := by
  decide

theorem normalizedCandidate_Or_elim_eq :
    normalizedCandidate_Or_elim =
      LFBetaEta.normalForm [] PureBetaEta.normalizationFuel
        candidate_Or_elim := by
  decide

def replay_Or_elim : ReplayCase :=
  { name := "Or_elim", actionCount := 9, traceSha256 := "cd15a534399bc9945ebba7af1696d2692300b9777a204bef7608635bbc51acee", referenceTermSha256 := "922074d54a1b0e8ba8308597a9105bdb28683584d095d406a38f6ad5a292bfdc"
    goal := encodeExpr PureDTTBench31.goal_Logic_Or_elim
    candidate := candidate_Or_elim }

theorem replay_Or_elim_accepted : accepts replay_Or_elim = true := by
  decide

theorem replay_Or_elim_sound :
    LFConversionProfileChecker.Deriv LFProfile.indexed [] []
      candidate_Or_elim (encodeExpr PureDTTBench31.goal_Logic_Or_elim) :=
  LFConversionProfileChecker.S1 replay_Or_elim_accepted

def candidate_False_elim : LF.Term :=
  .lam (.srt .type) (.lam (.pi (.pi (.var 0) (.srt .type)) (.pi (.var 1) (.app (.var 1) (.var 0)))) (.lam (.srt .type) (.lam (.var 2) (.app (.app (.var 2) (.lam (.var 3) (.var 2))) (.app (.app (.var 2) (.lam (.var 3) (.var 4))) (.var 0))))))

def normalizedGoal_False_elim : LF.Term :=
  .pi (.srt .type) (.pi (.pi (.pi (.var 0) (.srt .type)) (.pi (.var 1) (.app (.var 1) (.var 0)))) (.pi (.srt .type) (.pi (.var 2) (.var 1))))

def normalizedCandidate_False_elim : LF.Term :=
  .lam (.srt .type) (.lam (.pi (.pi (.var 0) (.srt .type)) (.pi (.var 1) (.app (.var 1) (.var 0)))) (.lam (.srt .type) (.lam (.var 2) (.app (.app (.var 2) (.lam (.var 3) (.var 2))) (.app (.app (.var 2) (.lam (.var 3) (.var 4))) (.var 0))))))

theorem normalizedGoal_False_elim_eq :
    normalizedGoal_False_elim =
      LFBetaEta.normalForm [] PureBetaEta.normalizationFuel
        (encodeExpr PureDTTBench31.goal_Logic_False_elim) := by
  decide

theorem normalizedCandidate_False_elim_eq :
    normalizedCandidate_False_elim =
      LFBetaEta.normalForm [] PureBetaEta.normalizationFuel
        candidate_False_elim := by
  decide

def replay_False_elim : ReplayCase :=
  { name := "False_elim", actionCount := 5, traceSha256 := "876323a4289adf3d8de36e6d21b9bdac11e5e66ca1f1f6d504cd53d4b6dcea30", referenceTermSha256 := "411220d0c6316e3d94caaceb48bbb1b1a8c9111811bbadbef38eebd4130500de"
    goal := encodeExpr PureDTTBench31.goal_Logic_False_elim
    candidate := candidate_False_elim }

theorem replay_False_elim_accepted : accepts replay_False_elim = true := by
  decide

theorem replay_False_elim_sound :
    LFConversionProfileChecker.Deriv LFProfile.indexed [] []
      candidate_False_elim (encodeExpr PureDTTBench31.goal_Logic_False_elim) :=
  LFConversionProfileChecker.S1 replay_False_elim_accepted

def candidate_peirce : LF.Term :=
  .lam (.srt .type) (.lam (.pi (.srt .type) (.pi (.pi (.pi (.var 0) (.var 2)) (.var 2)) (.var 1))) (.lam (.srt .type) (.lam (.srt .type) (.lam (.pi (.pi (.var 1) (.var 1)) (.var 2)) (.app (.app (.var 3) (.var 2)) (.lam (.pi (.var 2) (.var 5)) (.app (.var 0) (.app (.var 1) (.lam (.var 3) (.app (.app (.var 5) (.var 3)) (.lam (.pi (.var 3) (.var 7)) (.app (.var 2) (.var 1)))))))))))))

def normalizedGoal_peirce : LF.Term :=
  .pi (.srt .type) (.pi (.pi (.srt .type) (.pi (.pi (.pi (.var 0) (.var 2)) (.var 2)) (.var 1))) (.pi (.srt .type) (.pi (.srt .type) (.pi (.pi (.pi (.var 1) (.var 1)) (.var 2)) (.var 2)))))

def normalizedCandidate_peirce : LF.Term :=
  .lam (.srt .type) (.lam (.pi (.srt .type) (.pi (.pi (.pi (.var 0) (.var 2)) (.var 2)) (.var 1))) (.lam (.srt .type) (.lam (.srt .type) (.lam (.pi (.pi (.var 1) (.var 1)) (.var 2)) (.app (.app (.var 3) (.var 2)) (.lam (.pi (.var 2) (.var 5)) (.app (.var 0) (.app (.var 1) (.lam (.var 3) (.app (.app (.var 5) (.var 3)) (.lam (.pi (.var 3) (.var 7)) (.app (.var 2) (.var 1)))))))))))))

theorem normalizedGoal_peirce_eq :
    normalizedGoal_peirce =
      LFBetaEta.normalForm [] PureBetaEta.normalizationFuel
        (encodeExpr PureDTTBench31.goal_Logic_peirce) := by
  decide

theorem normalizedCandidate_peirce_eq :
    normalizedCandidate_peirce =
      LFBetaEta.normalForm [] PureBetaEta.normalizationFuel
        candidate_peirce := by
  decide

def replay_peirce : ReplayCase :=
  { name := "peirce", actionCount := 8, traceSha256 := "f8bcb3de4e7bfd4e59edce67c84f5ad56252122cf8f92382ede085056cad0ea4", referenceTermSha256 := "f535d376042c33006040f47f9e3561a1ed9be72825c22ea09d876b2a77f1e445"
    goal := encodeExpr PureDTTBench31.goal_Logic_peirce
    candidate := candidate_peirce }

theorem replay_peirce_accepted : accepts replay_peirce = true := by
  decide

theorem replay_peirce_sound :
    LFConversionProfileChecker.Deriv LFProfile.indexed [] []
      candidate_peirce (encodeExpr PureDTTBench31.goal_Logic_peirce) :=
  LFConversionProfileChecker.S1 replay_peirce_accepted

def candidate_PUnit_ext : LF.Term :=
  .lam (.pi (.srt .type) (.pi (.var 0) (.pi (.var 1) (.srt .type)))) (.lam (.pi (.srt .type) (.pi (.var 0) (.app (.app (.app (.var 2) (.var 1)) (.var 0)) (.var 0)))) (.lam (.pi (.srt .type) (.pi (.var 0) (.pi (.pi (.var 1) (.pi (.app (.app (.app (.var 4) (.var 2)) (.var 1)) (.var 0)) (.srt .type))) (.pi (.app (.app (.var 0) (.var 1)) (.app (.app (.var 3) (.var 2)) (.var 1))) (.pi (.var 3) (.pi (.app (.app (.app (.var 6) (.var 4)) (.var 3)) (.var 0)) (.app (.app (.var 3) (.var 1)) (.var 0)))))))) (.lam (.srt .type) (.lam (.var 0) (.lam (.pi (.pi (.var 1) (.srt .type)) (.pi (.app (.var 0) (.var 1)) (.pi (.var 3) (.app (.var 2) (.var 0))))) (.lam (.var 2) (.lam (.var 3) (.app (.app (.app (.var 2) (.lam (.var 4) (.app (.app (.app (.var 8) (.var 5)) (.var 2)) (.var 0)))) (.app (.app (.app (.var 2) (.lam (.var 4) (.app (.app (.app (.var 8) (.var 5)) (.var 0)) (.var 4)))) (.app (.app (.var 6) (.var 4)) (.var 3))) (.var 1))) (.var 0)))))))))

def normalizedGoal_PUnit_ext : LF.Term :=
  .pi (.pi (.srt .type) (.pi (.var 0) (.pi (.var 1) (.srt .type)))) (.pi (.pi (.srt .type) (.pi (.var 0) (.app (.app (.app (.var 2) (.var 1)) (.var 0)) (.var 0)))) (.pi (.pi (.srt .type) (.pi (.var 0) (.pi (.pi (.var 1) (.pi (.app (.app (.app (.var 4) (.var 2)) (.var 1)) (.var 0)) (.srt .type))) (.pi (.app (.app (.var 0) (.var 1)) (.app (.app (.var 3) (.var 2)) (.var 1))) (.pi (.var 3) (.pi (.app (.app (.app (.var 6) (.var 4)) (.var 3)) (.var 0)) (.app (.app (.var 3) (.var 1)) (.var 0)))))))) (.pi (.srt .type) (.pi (.var 0) (.pi (.pi (.pi (.var 1) (.srt .type)) (.pi (.app (.var 0) (.var 1)) (.pi (.var 3) (.app (.var 2) (.var 0))))) (.pi (.var 2) (.pi (.var 3) (.app (.app (.app (.var 7) (.var 4)) (.var 1)) (.var 0)))))))))

def normalizedCandidate_PUnit_ext : LF.Term :=
  .lam (.pi (.srt .type) (.pi (.var 0) (.pi (.var 1) (.srt .type)))) (.lam (.pi (.srt .type) (.pi (.var 0) (.app (.app (.app (.var 2) (.var 1)) (.var 0)) (.var 0)))) (.lam (.pi (.srt .type) (.pi (.var 0) (.pi (.pi (.var 1) (.pi (.app (.app (.app (.var 4) (.var 2)) (.var 1)) (.var 0)) (.srt .type))) (.pi (.app (.app (.var 0) (.var 1)) (.app (.app (.var 3) (.var 2)) (.var 1))) (.pi (.var 3) (.pi (.app (.app (.app (.var 6) (.var 4)) (.var 3)) (.var 0)) (.app (.app (.var 3) (.var 1)) (.var 0)))))))) (.lam (.srt .type) (.lam (.var 0) (.lam (.pi (.pi (.var 1) (.srt .type)) (.pi (.app (.var 0) (.var 1)) (.pi (.var 3) (.app (.var 2) (.var 0))))) (.lam (.var 2) (.app (.app (.var 1) (.app (.app (.var 6) (.var 3)) (.var 0))) (.app (.app (.app (.var 1) (.lam (.var 3) (.app (.app (.app (.var 7) (.var 4)) (.var 0)) (.var 3)))) (.app (.app (.var 5) (.var 3)) (.var 2))) (.var 0)))))))))

theorem normalizedGoal_PUnit_ext_eq :
    normalizedGoal_PUnit_ext =
      LFBetaEta.normalForm [] PureBetaEta.normalizationFuel
        (encodeExpr PureDTTBench31.goal_Logic_PUnit_ext) := by
  decide

theorem normalizedCandidate_PUnit_ext_eq :
    normalizedCandidate_PUnit_ext =
      LFBetaEta.normalForm [] PureBetaEta.normalizationFuel
        candidate_PUnit_ext := by
  decide

def replay_PUnit_ext : ReplayCase :=
  { name := "PUnit_ext", actionCount := 15, traceSha256 := "1d4e48f1f5a14a1e5104fd6c177f34287d0153adeac3e2b67cd7707bc6e8b1ea", referenceTermSha256 := "3d0d6107488edadc3ee92e312ffe76c0dc33890f12acb86f7109392e5f65b020"
    goal := encodeExpr PureDTTBench31.goal_Logic_PUnit_ext
    candidate := candidate_PUnit_ext }

theorem replay_PUnit_ext_accepted : accepts replay_PUnit_ext = true := by
  decide

theorem replay_PUnit_ext_sound :
    LFConversionProfileChecker.Deriv LFProfile.indexed [] []
      candidate_PUnit_ext (encodeExpr PureDTTBench31.goal_Logic_PUnit_ext) :=
  LFConversionProfileChecker.S1 replay_PUnit_ext_accepted

def candidate_Exists_imp : LF.Term :=
  .lam (.pi (.srt .type) (.pi (.pi (.var 0) (.srt .type)) (.srt .type))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.srt .type)) (.pi (.var 1) (.pi (.app (.var 1) (.var 0)) (.app (.app (.var 4) (.var 3)) (.var 2)))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.srt .type)) (.pi (.pi (.app (.app (.var 3) (.var 1)) (.var 0)) (.srt .type)) (.pi (.pi (.var 2) (.pi (.app (.var 2) (.var 0)) (.app (.var 2) (.app (.app (.app (.app (.var 5) (.var 4)) (.var 3)) (.var 1)) (.var 0))))) (.pi (.app (.app (.var 5) (.var 3)) (.var 2)) (.app (.var 2) (.var 0))))))) (.lam (.srt .type) (.lam (.pi (.var 0) (.srt .type)) (.lam (.pi (.var 1) (.srt .type)) (.lam (.pi (.var 2) (.pi (.app (.var 2) (.var 0)) (.app (.var 2) (.var 1)))) (.lam (.app (.app (.var 6) (.var 3)) (.var 2)) (.app (.app (.app (.app (.app (.var 5) (.var 4)) (.lam (.var 4) (.app (.var 4) (.var 0)))) (.lam (.app (.app (.var 7) (.var 4)) (.lam (.var 4) (.app (.var 4) (.var 0)))) (.app (.app (.var 8) (.var 5)) (.lam (.var 5) (.app (.var 4) (.var 0)))))) (.lam (.var 4) (.lam (.app (.lam (.var 5) (.app (.var 5) (.var 0))) (.var 0)) (.app (.app (.app (.app (.var 8) (.var 6)) (.lam (.var 6) (.app (.var 5) (.var 0)))) (.var 1)) (.app (.app (.var 3) (.var 1)) (.var 0)))))) (.var 0)))))))))

def normalizedGoal_Exists_imp : LF.Term :=
  .pi (.pi (.srt .type) (.pi (.pi (.var 0) (.srt .type)) (.srt .type))) (.pi (.pi (.srt .type) (.pi (.pi (.var 0) (.srt .type)) (.pi (.var 1) (.pi (.app (.var 1) (.var 0)) (.app (.app (.var 4) (.var 3)) (.var 2)))))) (.pi (.pi (.srt .type) (.pi (.pi (.var 0) (.srt .type)) (.pi (.pi (.app (.app (.var 3) (.var 1)) (.var 0)) (.srt .type)) (.pi (.pi (.var 2) (.pi (.app (.var 2) (.var 0)) (.app (.var 2) (.app (.app (.app (.app (.var 5) (.var 4)) (.var 3)) (.var 1)) (.var 0))))) (.pi (.app (.app (.var 5) (.var 3)) (.var 2)) (.app (.var 2) (.var 0))))))) (.pi (.srt .type) (.pi (.pi (.var 0) (.srt .type)) (.pi (.pi (.var 1) (.srt .type)) (.pi (.pi (.var 2) (.pi (.app (.var 2) (.var 0)) (.app (.var 2) (.var 1)))) (.pi (.app (.app (.var 6) (.var 3)) (.var 2)) (.app (.app (.var 7) (.var 4)) (.var 2)))))))))

def normalizedCandidate_Exists_imp : LF.Term :=
  .lam (.pi (.srt .type) (.pi (.pi (.var 0) (.srt .type)) (.srt .type))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.srt .type)) (.pi (.var 1) (.pi (.app (.var 1) (.var 0)) (.app (.app (.var 4) (.var 3)) (.var 2)))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.srt .type)) (.pi (.pi (.app (.app (.var 3) (.var 1)) (.var 0)) (.srt .type)) (.pi (.pi (.var 2) (.pi (.app (.var 2) (.var 0)) (.app (.var 2) (.app (.app (.app (.app (.var 5) (.var 4)) (.var 3)) (.var 1)) (.var 0))))) (.pi (.app (.app (.var 5) (.var 3)) (.var 2)) (.app (.var 2) (.var 0))))))) (.lam (.srt .type) (.lam (.pi (.var 0) (.srt .type)) (.lam (.pi (.var 1) (.srt .type)) (.lam (.pi (.var 2) (.pi (.app (.var 2) (.var 0)) (.app (.var 2) (.var 1)))) (.app (.app (.app (.app (.var 4) (.var 3)) (.var 2)) (.lam (.app (.app (.var 6) (.var 3)) (.var 2)) (.app (.app (.var 7) (.var 4)) (.var 2)))) (.lam (.var 3) (.lam (.app (.var 3) (.var 0)) (.app (.app (.app (.app (.var 7) (.var 5)) (.var 3)) (.var 1)) (.app (.app (.var 2) (.var 1)) (.var 0))))))))))))

theorem normalizedGoal_Exists_imp_eq :
    normalizedGoal_Exists_imp =
      LFBetaEta.normalForm [] PureBetaEta.normalizationFuel
        (encodeExpr PureDTTBench31.goal_Logic_Exists_imp) := by
  decide

theorem normalizedCandidate_Exists_imp_eq :
    normalizedCandidate_Exists_imp =
      LFBetaEta.normalForm [] PureBetaEta.normalizationFuel
        candidate_Exists_imp := by
  decide

def replay_Exists_imp : ReplayCase :=
  { name := "Exists_imp", actionCount := 17, traceSha256 := "98d59acbc63bb45708eb4b3754dc97cecd71c1b82a86200e8b5e1ba0d3555da4", referenceTermSha256 := "6700e7d166e4b84a1f0c90dfe6e36ed6faf7e05006800b2ba5f8c1ba1a180197"
    goal := encodeExpr PureDTTBench31.goal_Logic_Exists_imp
    candidate := candidate_Exists_imp }

theorem replay_Exists_imp_accepted : accepts replay_Exists_imp = true := by
  decide

theorem replay_Exists_imp_sound :
    LFConversionProfileChecker.Deriv LFProfile.indexed [] []
      candidate_Exists_imp (encodeExpr PureDTTBench31.goal_Logic_Exists_imp) :=
  LFConversionProfileChecker.S1 replay_Exists_imp_accepted

def candidate_Relation_TransGen_trans : LF.Term :=
  .lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.srt .type))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.pi (.app (.app (.var 2) (.var 1)) (.var 0)) (.app (.app (.app (.app (.var 5) (.var 4)) (.var 3)) (.var 2)) (.var 1))))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.pi (.var 3) (.pi (.app (.app (.app (.app (.var 6) (.var 4)) (.var 3)) (.var 2)) (.var 1)) (.pi (.app (.app (.var 4) (.var 2)) (.var 1)) (.app (.app (.app (.app (.var 8) (.var 6)) (.var 5)) (.var 4)) (.var 2))))))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.pi (.var 2) (.pi (.app (.app (.app (.app (.var 6) (.var 3)) (.var 2)) (.var 1)) (.var 0)) (.srt .type))) (.pi (.pi (.var 3) (.pi (.app (.app (.var 3) (.var 2)) (.var 0)) (.app (.app (.var 2) (.var 1)) (.app (.app (.app (.app (.app (.var 7) (.var 5)) (.var 4)) (.var 3)) (.var 1)) (.var 0))))) (.pi (.pi (.var 4) (.pi (.var 5) (.pi (.app (.app (.app (.app (.var 9) (.var 6)) (.var 5)) (.var 4)) (.var 1)) (.pi (.app (.app (.var 6) (.var 2)) (.var 1)) (.pi (.app (.app (.var 5) (.var 3)) (.var 1)) (.app (.app (.var 6) (.var 3)) (.app (.app (.app (.app (.app (.app (.app (.var 10) (.var 9)) (.var 8)) (.var 7)) (.var 4)) (.var 3)) (.var 2)) (.var 1)))))))) (.pi (.var 5) (.pi (.app (.app (.app (.app (.var 9) (.var 6)) (.var 5)) (.var 4)) (.var 0)) (.app (.app (.var 4) (.var 1)) (.var 0)))))))))) (.lam (.srt .type) (.lam (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.lam (.var 1) (.lam (.var 2) (.lam (.var 3) (.lam (.app (.app (.app (.app (.var 8) (.var 4)) (.var 3)) (.var 2)) (.var 1)) (.lam (.app (.app (.app (.app (.var 9) (.var 5)) (.var 4)) (.var 2)) (.var 1)) (.app (.app (.app (.app (.app (.app (.app (.app (.var 7) (.var 6)) (.lam (.var 6) (.lam (.var 7) (.app (.app (.var 7) (.var 1)) (.var 0))))) (.var 3)) (.lam (.var 6) (.lam (.app (.app (.app (.app (.var 11) (.var 7)) (.lam (.var 7) (.lam (.var 8) (.app (.app (.var 8) (.var 1)) (.var 0))))) (.var 4)) (.var 0)) (.app (.app (.app (.app (.var 12) (.var 8)) (.lam (.var 8) (.lam (.var 9) (.app (.app (.var 9) (.var 1)) (.var 0))))) (.var 6)) (.var 1))))) (.lam (.var 6) (.lam (.app (.app (.lam (.var 7) (.lam (.var 8) (.app (.app (.var 8) (.var 1)) (.var 0)))) (.var 4)) (.var 0)) (.app (.app (.app (.app (.app (.app (.app (.var 10) (.var 8)) (.lam (.var 8) (.lam (.var 9) (.app (.app (.var 9) (.var 1)) (.var 0))))) (.var 6)) (.var 5)) (.var 1)) (.var 3)) (.var 0))))) (.lam (.var 6) (.lam (.var 7) (.lam (.app (.app (.app (.app (.var 12) (.var 8)) (.lam (.var 8) (.lam (.var 9) (.app (.app (.var 9) (.var 1)) (.var 0))))) (.var 5)) (.var 1)) (.lam (.app (.app (.lam (.var 9) (.lam (.var 10) (.app (.app (.var 10) (.var 1)) (.var 0)))) (.var 2)) (.var 1)) (.lam (.app (.app (.lam (.var 10) (.lam (.app (.app (.app (.app (.var 15) (.var 11)) (.lam (.var 11) (.lam (.var 12) (.app (.app (.var 12) (.var 1)) (.var 0))))) (.var 8)) (.var 0)) (.app (.app (.app (.app (.var 16) (.var 12)) (.lam (.var 12) (.lam (.var 13) (.app (.app (.var 13) (.var 1)) (.var 0))))) (.var 10)) (.var 1)))) (.var 3)) (.var 1)) (.app (.app (.app (.app (.app (.app (.app (.var 13) (.var 11)) (.lam (.var 11) (.lam (.var 12) (.app (.app (.var 12) (.var 1)) (.var 0))))) (.var 9)) (.var 4)) (.var 3)) (.var 0)) (.var 1)))))))) (.var 2)) (.var 0))))))))))))

def normalizedGoal_Relation_TransGen_trans : LF.Term :=
  .pi (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.srt .type))))) (.pi (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.pi (.app (.app (.var 2) (.var 1)) (.var 0)) (.app (.app (.app (.app (.var 5) (.var 4)) (.var 3)) (.var 2)) (.var 1))))))) (.pi (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.pi (.var 3) (.pi (.app (.app (.app (.app (.var 6) (.var 4)) (.var 3)) (.var 2)) (.var 1)) (.pi (.app (.app (.var 4) (.var 2)) (.var 1)) (.app (.app (.app (.app (.var 8) (.var 6)) (.var 5)) (.var 4)) (.var 2))))))))) (.pi (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.pi (.var 2) (.pi (.app (.app (.app (.app (.var 6) (.var 3)) (.var 2)) (.var 1)) (.var 0)) (.srt .type))) (.pi (.pi (.var 3) (.pi (.app (.app (.var 3) (.var 2)) (.var 0)) (.app (.app (.var 2) (.var 1)) (.app (.app (.app (.app (.app (.var 7) (.var 5)) (.var 4)) (.var 3)) (.var 1)) (.var 0))))) (.pi (.pi (.var 4) (.pi (.var 5) (.pi (.app (.app (.app (.app (.var 9) (.var 6)) (.var 5)) (.var 4)) (.var 1)) (.pi (.app (.app (.var 6) (.var 2)) (.var 1)) (.pi (.app (.app (.var 5) (.var 3)) (.var 1)) (.app (.app (.var 6) (.var 3)) (.app (.app (.app (.app (.app (.app (.app (.var 10) (.var 9)) (.var 8)) (.var 7)) (.var 4)) (.var 3)) (.var 2)) (.var 1)))))))) (.pi (.var 5) (.pi (.app (.app (.app (.app (.var 9) (.var 6)) (.var 5)) (.var 4)) (.var 0)) (.app (.app (.var 4) (.var 1)) (.var 0)))))))))) (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.pi (.var 3) (.pi (.app (.app (.app (.app (.var 8) (.var 4)) (.var 3)) (.var 2)) (.var 1)) (.pi (.app (.app (.app (.app (.var 9) (.var 5)) (.var 4)) (.var 2)) (.var 1)) (.app (.app (.app (.app (.var 10) (.var 6)) (.var 5)) (.var 4)) (.var 2))))))))))))

def normalizedCandidate_Relation_TransGen_trans : LF.Term :=
  .lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.srt .type))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.pi (.app (.app (.var 2) (.var 1)) (.var 0)) (.app (.app (.app (.app (.var 5) (.var 4)) (.var 3)) (.var 2)) (.var 1))))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.pi (.var 3) (.pi (.app (.app (.app (.app (.var 6) (.var 4)) (.var 3)) (.var 2)) (.var 1)) (.pi (.app (.app (.var 4) (.var 2)) (.var 1)) (.app (.app (.app (.app (.var 8) (.var 6)) (.var 5)) (.var 4)) (.var 2))))))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.pi (.var 2) (.pi (.app (.app (.app (.app (.var 6) (.var 3)) (.var 2)) (.var 1)) (.var 0)) (.srt .type))) (.pi (.pi (.var 3) (.pi (.app (.app (.var 3) (.var 2)) (.var 0)) (.app (.app (.var 2) (.var 1)) (.app (.app (.app (.app (.app (.var 7) (.var 5)) (.var 4)) (.var 3)) (.var 1)) (.var 0))))) (.pi (.pi (.var 4) (.pi (.var 5) (.pi (.app (.app (.app (.app (.var 9) (.var 6)) (.var 5)) (.var 4)) (.var 1)) (.pi (.app (.app (.var 6) (.var 2)) (.var 1)) (.pi (.app (.app (.var 5) (.var 3)) (.var 1)) (.app (.app (.var 6) (.var 3)) (.app (.app (.app (.app (.app (.app (.app (.var 10) (.var 9)) (.var 8)) (.var 7)) (.var 4)) (.var 3)) (.var 2)) (.var 1)))))))) (.pi (.var 5) (.pi (.app (.app (.app (.app (.var 9) (.var 6)) (.var 5)) (.var 4)) (.var 0)) (.app (.app (.var 4) (.var 1)) (.var 0)))))))))) (.lam (.srt .type) (.lam (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.lam (.var 1) (.lam (.var 2) (.lam (.var 3) (.lam (.app (.app (.app (.app (.var 8) (.var 4)) (.var 3)) (.var 2)) (.var 1)) (.app (.app (.app (.app (.app (.app (.app (.var 6) (.var 5)) (.var 4)) (.var 2)) (.lam (.var 5) (.lam (.app (.app (.app (.app (.var 10) (.var 6)) (.var 5)) (.var 3)) (.var 0)) (.app (.app (.app (.app (.var 11) (.var 7)) (.var 6)) (.var 5)) (.var 1))))) (.lam (.var 5) (.app (.app (.app (.app (.app (.app (.var 8) (.var 6)) (.var 5)) (.var 4)) (.var 3)) (.var 0)) (.var 1)))) (.lam (.var 5) (.lam (.var 6) (.lam (.app (.app (.app (.app (.var 11) (.var 7)) (.var 6)) (.var 4)) (.var 1)) (.lam (.app (.app (.var 7) (.var 2)) (.var 1)) (.lam (.app (.app (.app (.app (.var 13) (.var 9)) (.var 8)) (.var 7)) (.var 3)) (.app (.app (.app (.app (.app (.app (.app (.var 12) (.var 10)) (.var 9)) (.var 8)) (.var 4)) (.var 3)) (.var 0)) (.var 1)))))))) (.var 1)))))))))))

theorem normalizedGoal_Relation_TransGen_trans_eq :
    normalizedGoal_Relation_TransGen_trans =
      LFBetaEta.normalForm [] PureBetaEta.normalizationFuel
        (encodeExpr PureDTTBench31.goal_Relation_Relation_TransGen_trans) := by
  decide

theorem normalizedCandidate_Relation_TransGen_trans_eq :
    normalizedCandidate_Relation_TransGen_trans =
      LFBetaEta.normalForm [] PureBetaEta.normalizationFuel
        candidate_Relation_TransGen_trans := by
  decide

def replay_Relation_TransGen_trans : ReplayCase :=
  { name := "Relation_TransGen_trans", actionCount := 35, traceSha256 := "f4400f1d34422819880a9d9645bfd2c55b6d7b71469684a711ed187397376f18", referenceTermSha256 := "fa4e6d97037861e41224bd7c3c399d8a8bf83c1a2048fd94b155120764109d5a"
    goal := encodeExpr PureDTTBench31.goal_Relation_Relation_TransGen_trans
    candidate := candidate_Relation_TransGen_trans }

theorem replay_Relation_TransGen_trans_accepted : accepts replay_Relation_TransGen_trans = true := by
  decide

theorem replay_Relation_TransGen_trans_sound :
    LFConversionProfileChecker.Deriv LFProfile.indexed [] []
      candidate_Relation_TransGen_trans (encodeExpr PureDTTBench31.goal_Relation_Relation_TransGen_trans) :=
  LFConversionProfileChecker.S1 replay_Relation_TransGen_trans_accepted

def candidate_ReflGen_to_reflTransGen : LF.Term :=
  .lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.srt .type))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.app (.app (.app (.app (.var 3) (.var 2)) (.var 1)) (.var 0)) (.var 0))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.pi (.app (.app (.var 2) (.var 1)) (.var 0)) (.app (.app (.app (.app (.var 6) (.var 4)) (.var 3)) (.var 2)) (.var 1))))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.pi (.var 2) (.pi (.app (.app (.app (.app (.var 6) (.var 3)) (.var 2)) (.var 1)) (.var 0)) (.srt .type))) (.pi (.app (.app (.var 0) (.var 1)) (.app (.app (.app (.var 5) (.var 3)) (.var 2)) (.var 1))) (.pi (.pi (.var 4) (.pi (.app (.app (.var 4) (.var 3)) (.var 0)) (.app (.app (.var 3) (.var 1)) (.app (.app (.app (.app (.app (.var 7) (.var 6)) (.var 5)) (.var 4)) (.var 1)) (.var 0))))) (.pi (.var 5) (.pi (.app (.app (.app (.app (.var 9) (.var 6)) (.var 5)) (.var 4)) (.var 0)) (.app (.app (.var 4) (.var 1)) (.var 0)))))))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.srt .type))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.app (.app (.app (.app (.var 3) (.var 2)) (.var 1)) (.var 0)) (.var 0))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.pi (.var 3) (.pi (.app (.app (.app (.app (.var 6) (.var 4)) (.var 3)) (.var 2)) (.var 1)) (.pi (.app (.app (.var 4) (.var 2)) (.var 1)) (.app (.app (.app (.app (.var 8) (.var 6)) (.var 5)) (.var 4)) (.var 2))))))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.pi (.var 2) (.pi (.app (.app (.app (.app (.var 6) (.var 3)) (.var 2)) (.var 1)) (.var 0)) (.srt .type))) (.pi (.app (.app (.var 0) (.var 1)) (.app (.app (.app (.var 5) (.var 3)) (.var 2)) (.var 1))) (.pi (.pi (.var 4) (.pi (.var 5) (.pi (.app (.app (.app (.app (.var 9) (.var 6)) (.var 5)) (.var 4)) (.var 1)) (.pi (.app (.app (.var 6) (.var 2)) (.var 1)) (.pi (.app (.app (.var 5) (.var 3)) (.var 1)) (.app (.app (.var 6) (.var 3)) (.app (.app (.app (.app (.app (.app (.app (.var 10) (.var 9)) (.var 8)) (.var 7)) (.var 4)) (.var 3)) (.var 2)) (.var 1)))))))) (.pi (.var 5) (.pi (.app (.app (.app (.app (.var 9) (.var 6)) (.var 5)) (.var 4)) (.var 0)) (.app (.app (.var 4) (.var 1)) (.var 0)))))))))) (.lam (.srt .type) (.lam (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.lam (.var 1) (.lam (.var 2) (.lam (.app (.app (.app (.app (.var 11) (.var 3)) (.var 2)) (.var 1)) (.var 0)) (.app (.app (.app (.app (.app (.app (.app (.app (.var 9) (.var 4)) (.lam (.var 4) (.lam (.var 5) (.app (.app (.var 5) (.var 1)) (.var 0))))) (.var 2)) (.lam (.var 4) (.lam (.app (.app (.app (.app (.var 13) (.var 5)) (.lam (.var 5) (.lam (.var 6) (.app (.app (.var 6) (.var 1)) (.var 0))))) (.var 3)) (.var 0)) (.app (.app (.app (.app (.var 10) (.var 6)) (.lam (.var 6) (.lam (.var 7) (.app (.app (.var 7) (.var 1)) (.var 0))))) (.var 4)) (.var 1))))) (.app (.app (.app (.var 7) (.var 4)) (.lam (.var 4) (.lam (.var 5) (.app (.app (.var 5) (.var 1)) (.var 0))))) (.var 2))) (.lam (.var 4) (.lam (.app (.app (.lam (.var 5) (.lam (.var 6) (.app (.app (.var 6) (.var 1)) (.var 0)))) (.var 3)) (.var 0)) (.app (.app (.app (.app (.app (.app (.app (.var 8) (.var 6)) (.lam (.var 6) (.lam (.var 7) (.app (.app (.var 7) (.var 1)) (.var 0))))) (.var 4)) (.var 4)) (.var 1)) (.app (.app (.app (.var 9) (.var 6)) (.lam (.var 6) (.lam (.var 7) (.app (.app (.var 7) (.var 1)) (.var 0))))) (.var 4))) (.var 0))))) (.var 1)) (.var 0))))))))))))))

def normalizedGoal_ReflGen_to_reflTransGen : LF.Term :=
  .pi (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.srt .type))))) (.pi (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.app (.app (.app (.app (.var 3) (.var 2)) (.var 1)) (.var 0)) (.var 0))))) (.pi (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.pi (.app (.app (.var 2) (.var 1)) (.var 0)) (.app (.app (.app (.app (.var 6) (.var 4)) (.var 3)) (.var 2)) (.var 1))))))) (.pi (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.pi (.var 2) (.pi (.app (.app (.app (.app (.var 6) (.var 3)) (.var 2)) (.var 1)) (.var 0)) (.srt .type))) (.pi (.app (.app (.var 0) (.var 1)) (.app (.app (.app (.var 5) (.var 3)) (.var 2)) (.var 1))) (.pi (.pi (.var 4) (.pi (.app (.app (.var 4) (.var 3)) (.var 0)) (.app (.app (.var 3) (.var 1)) (.app (.app (.app (.app (.app (.var 7) (.var 6)) (.var 5)) (.var 4)) (.var 1)) (.var 0))))) (.pi (.var 5) (.pi (.app (.app (.app (.app (.var 9) (.var 6)) (.var 5)) (.var 4)) (.var 0)) (.app (.app (.var 4) (.var 1)) (.var 0)))))))))) (.pi (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.srt .type))))) (.pi (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.app (.app (.app (.app (.var 3) (.var 2)) (.var 1)) (.var 0)) (.var 0))))) (.pi (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.pi (.var 3) (.pi (.app (.app (.app (.app (.var 6) (.var 4)) (.var 3)) (.var 2)) (.var 1)) (.pi (.app (.app (.var 4) (.var 2)) (.var 1)) (.app (.app (.app (.app (.var 8) (.var 6)) (.var 5)) (.var 4)) (.var 2))))))))) (.pi (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.pi (.var 2) (.pi (.app (.app (.app (.app (.var 6) (.var 3)) (.var 2)) (.var 1)) (.var 0)) (.srt .type))) (.pi (.app (.app (.var 0) (.var 1)) (.app (.app (.app (.var 5) (.var 3)) (.var 2)) (.var 1))) (.pi (.pi (.var 4) (.pi (.var 5) (.pi (.app (.app (.app (.app (.var 9) (.var 6)) (.var 5)) (.var 4)) (.var 1)) (.pi (.app (.app (.var 6) (.var 2)) (.var 1)) (.pi (.app (.app (.var 5) (.var 3)) (.var 1)) (.app (.app (.var 6) (.var 3)) (.app (.app (.app (.app (.app (.app (.app (.var 10) (.var 9)) (.var 8)) (.var 7)) (.var 4)) (.var 3)) (.var 2)) (.var 1)))))))) (.pi (.var 5) (.pi (.app (.app (.app (.app (.var 9) (.var 6)) (.var 5)) (.var 4)) (.var 0)) (.app (.app (.var 4) (.var 1)) (.var 0)))))))))) (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.pi (.app (.app (.app (.app (.var 11) (.var 3)) (.var 2)) (.var 1)) (.var 0)) (.app (.app (.app (.app (.var 8) (.var 4)) (.var 3)) (.var 2)) (.var 1))))))))))))))

def normalizedCandidate_ReflGen_to_reflTransGen : LF.Term :=
  .lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.srt .type))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.app (.app (.app (.app (.var 3) (.var 2)) (.var 1)) (.var 0)) (.var 0))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.pi (.app (.app (.var 2) (.var 1)) (.var 0)) (.app (.app (.app (.app (.var 6) (.var 4)) (.var 3)) (.var 2)) (.var 1))))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.pi (.var 2) (.pi (.app (.app (.app (.app (.var 6) (.var 3)) (.var 2)) (.var 1)) (.var 0)) (.srt .type))) (.pi (.app (.app (.var 0) (.var 1)) (.app (.app (.app (.var 5) (.var 3)) (.var 2)) (.var 1))) (.pi (.pi (.var 4) (.pi (.app (.app (.var 4) (.var 3)) (.var 0)) (.app (.app (.var 3) (.var 1)) (.app (.app (.app (.app (.app (.var 7) (.var 6)) (.var 5)) (.var 4)) (.var 1)) (.var 0))))) (.pi (.var 5) (.pi (.app (.app (.app (.app (.var 9) (.var 6)) (.var 5)) (.var 4)) (.var 0)) (.app (.app (.var 4) (.var 1)) (.var 0)))))))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.srt .type))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.app (.app (.app (.app (.var 3) (.var 2)) (.var 1)) (.var 0)) (.var 0))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.pi (.var 3) (.pi (.app (.app (.app (.app (.var 6) (.var 4)) (.var 3)) (.var 2)) (.var 1)) (.pi (.app (.app (.var 4) (.var 2)) (.var 1)) (.app (.app (.app (.app (.var 8) (.var 6)) (.var 5)) (.var 4)) (.var 2))))))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.pi (.var 2) (.pi (.app (.app (.app (.app (.var 6) (.var 3)) (.var 2)) (.var 1)) (.var 0)) (.srt .type))) (.pi (.app (.app (.var 0) (.var 1)) (.app (.app (.app (.var 5) (.var 3)) (.var 2)) (.var 1))) (.pi (.pi (.var 4) (.pi (.var 5) (.pi (.app (.app (.app (.app (.var 9) (.var 6)) (.var 5)) (.var 4)) (.var 1)) (.pi (.app (.app (.var 6) (.var 2)) (.var 1)) (.pi (.app (.app (.var 5) (.var 3)) (.var 1)) (.app (.app (.var 6) (.var 3)) (.app (.app (.app (.app (.app (.app (.app (.var 10) (.var 9)) (.var 8)) (.var 7)) (.var 4)) (.var 3)) (.var 2)) (.var 1)))))))) (.pi (.var 5) (.pi (.app (.app (.app (.app (.var 9) (.var 6)) (.var 5)) (.var 4)) (.var 0)) (.app (.app (.var 4) (.var 1)) (.var 0)))))))))) (.lam (.srt .type) (.lam (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.lam (.var 1) (.app (.app (.app (.app (.app (.app (.var 7) (.var 2)) (.var 1)) (.var 0)) (.lam (.var 2) (.lam (.app (.app (.app (.app (.var 11) (.var 3)) (.var 2)) (.var 1)) (.var 0)) (.app (.app (.app (.app (.var 8) (.var 4)) (.var 3)) (.var 2)) (.var 1))))) (.app (.app (.app (.var 5) (.var 2)) (.var 1)) (.var 0))) (.lam (.var 2) (.app (.app (.app (.app (.app (.app (.var 5) (.var 3)) (.var 2)) (.var 1)) (.var 1)) (.var 0)) (.app (.app (.app (.var 6) (.var 3)) (.var 2)) (.var 1)))))))))))))))

theorem normalizedGoal_ReflGen_to_reflTransGen_eq :
    normalizedGoal_ReflGen_to_reflTransGen =
      LFBetaEta.normalForm [] PureBetaEta.normalizationFuel
        (encodeExpr PureDTTBench31.goal_Relation_ReflGen_to_reflTransGen) := by
  decide

theorem normalizedCandidate_ReflGen_to_reflTransGen_eq :
    normalizedCandidate_ReflGen_to_reflTransGen =
      LFBetaEta.normalForm [] PureBetaEta.normalizationFuel
        candidate_ReflGen_to_reflTransGen := by
  decide

def replay_ReflGen_to_reflTransGen : ReplayCase :=
  { name := "ReflGen_to_reflTransGen", actionCount := 36, traceSha256 := "197a5577233b0dde4f49780d56a95e2f729f676cdf342c21c49d94aed1999c9c", referenceTermSha256 := "0bf86a608d3898feff770884a524ff39cdbd6c3cd23cefbe8e40b3ca63eb4250"
    goal := encodeExpr PureDTTBench31.goal_Relation_ReflGen_to_reflTransGen
    candidate := candidate_ReflGen_to_reflTransGen }

theorem replay_ReflGen_to_reflTransGen_accepted : accepts replay_ReflGen_to_reflTransGen = true := by
  decide

theorem replay_ReflGen_to_reflTransGen_sound :
    LFConversionProfileChecker.Deriv LFProfile.indexed [] []
      candidate_ReflGen_to_reflTransGen (encodeExpr PureDTTBench31.goal_Relation_ReflGen_to_reflTransGen) :=
  LFConversionProfileChecker.S1 replay_ReflGen_to_reflTransGen_accepted

def candidate_ReflGen_mono : LF.Term :=
  .lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.srt .type))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.app (.app (.app (.app (.var 3) (.var 2)) (.var 1)) (.var 0)) (.var 0))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.pi (.app (.app (.var 2) (.var 1)) (.var 0)) (.app (.app (.app (.app (.var 6) (.var 4)) (.var 3)) (.var 2)) (.var 1))))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.pi (.var 2) (.pi (.app (.app (.app (.app (.var 6) (.var 3)) (.var 2)) (.var 1)) (.var 0)) (.srt .type))) (.pi (.app (.app (.var 0) (.var 1)) (.app (.app (.app (.var 5) (.var 3)) (.var 2)) (.var 1))) (.pi (.pi (.var 4) (.pi (.app (.app (.var 4) (.var 3)) (.var 0)) (.app (.app (.var 3) (.var 1)) (.app (.app (.app (.app (.app (.var 7) (.var 6)) (.var 5)) (.var 4)) (.var 1)) (.var 0))))) (.pi (.var 5) (.pi (.app (.app (.app (.app (.var 9) (.var 6)) (.var 5)) (.var 4)) (.var 0)) (.app (.app (.var 4) (.var 1)) (.var 0)))))))))) (.lam (.srt .type) (.lam (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.lam (.pi (.var 1) (.pi (.var 2) (.srt .type))) (.lam (.pi (.var 2) (.pi (.var 3) (.pi (.app (.app (.var 3) (.var 1)) (.var 0)) (.app (.app (.var 3) (.var 2)) (.var 1))))) (.lam (.var 3) (.lam (.var 4) (.lam (.app (.app (.app (.app (.var 9) (.var 5)) (.var 4)) (.var 1)) (.var 0)) (.app (.app (.app (.app (.app (.app (.app (.app (.var 7) (.var 6)) (.lam (.var 6) (.lam (.var 7) (.app (.app (.var 7) (.var 1)) (.var 0))))) (.var 2)) (.lam (.var 6) (.lam (.app (.app (.app (.app (.var 11) (.var 7)) (.lam (.var 7) (.lam (.var 8) (.app (.app (.var 8) (.var 1)) (.var 0))))) (.var 3)) (.var 0)) (.app (.app (.app (.app (.var 12) (.var 8)) (.lam (.var 8) (.lam (.var 9) (.app (.app (.var 8) (.var 1)) (.var 0))))) (.var 4)) (.var 1))))) (.app (.app (.app (.var 9) (.var 6)) (.lam (.var 6) (.lam (.var 7) (.app (.app (.var 6) (.var 1)) (.var 0))))) (.var 2))) (.lam (.var 6) (.lam (.app (.app (.lam (.var 7) (.lam (.var 8) (.app (.app (.var 8) (.var 1)) (.var 0)))) (.var 3)) (.var 0)) (.app (.app (.app (.app (.app (.var 10) (.var 8)) (.lam (.var 8) (.lam (.var 9) (.app (.app (.var 8) (.var 1)) (.var 0))))) (.var 4)) (.var 1)) (.app (.app (.app (.var 5) (.var 4)) (.var 1)) (.var 0)))))) (.var 1)) (.var 0))))))))))))

def normalizedGoal_ReflGen_mono : LF.Term :=
  .pi (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.srt .type))))) (.pi (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.app (.app (.app (.app (.var 3) (.var 2)) (.var 1)) (.var 0)) (.var 0))))) (.pi (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.pi (.app (.app (.var 2) (.var 1)) (.var 0)) (.app (.app (.app (.app (.var 6) (.var 4)) (.var 3)) (.var 2)) (.var 1))))))) (.pi (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.pi (.var 2) (.pi (.app (.app (.app (.app (.var 6) (.var 3)) (.var 2)) (.var 1)) (.var 0)) (.srt .type))) (.pi (.app (.app (.var 0) (.var 1)) (.app (.app (.app (.var 5) (.var 3)) (.var 2)) (.var 1))) (.pi (.pi (.var 4) (.pi (.app (.app (.var 4) (.var 3)) (.var 0)) (.app (.app (.var 3) (.var 1)) (.app (.app (.app (.app (.app (.var 7) (.var 6)) (.var 5)) (.var 4)) (.var 1)) (.var 0))))) (.pi (.var 5) (.pi (.app (.app (.app (.app (.var 9) (.var 6)) (.var 5)) (.var 4)) (.var 0)) (.app (.app (.var 4) (.var 1)) (.var 0)))))))))) (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.pi (.var 1) (.pi (.var 2) (.srt .type))) (.pi (.pi (.var 2) (.pi (.var 3) (.pi (.app (.app (.var 3) (.var 1)) (.var 0)) (.app (.app (.var 3) (.var 2)) (.var 1))))) (.pi (.var 3) (.pi (.var 4) (.pi (.app (.app (.app (.app (.var 9) (.var 5)) (.var 4)) (.var 1)) (.var 0)) (.app (.app (.app (.app (.var 10) (.var 6)) (.var 4)) (.var 2)) (.var 1))))))))))))

def normalizedCandidate_ReflGen_mono : LF.Term :=
  .lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.srt .type))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.app (.app (.app (.app (.var 3) (.var 2)) (.var 1)) (.var 0)) (.var 0))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.pi (.app (.app (.var 2) (.var 1)) (.var 0)) (.app (.app (.app (.app (.var 6) (.var 4)) (.var 3)) (.var 2)) (.var 1))))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.pi (.var 2) (.pi (.app (.app (.app (.app (.var 6) (.var 3)) (.var 2)) (.var 1)) (.var 0)) (.srt .type))) (.pi (.app (.app (.var 0) (.var 1)) (.app (.app (.app (.var 5) (.var 3)) (.var 2)) (.var 1))) (.pi (.pi (.var 4) (.pi (.app (.app (.var 4) (.var 3)) (.var 0)) (.app (.app (.var 3) (.var 1)) (.app (.app (.app (.app (.app (.var 7) (.var 6)) (.var 5)) (.var 4)) (.var 1)) (.var 0))))) (.pi (.var 5) (.pi (.app (.app (.app (.app (.var 9) (.var 6)) (.var 5)) (.var 4)) (.var 0)) (.app (.app (.var 4) (.var 1)) (.var 0)))))))))) (.lam (.srt .type) (.lam (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.lam (.pi (.var 1) (.pi (.var 2) (.srt .type))) (.lam (.pi (.var 2) (.pi (.var 3) (.pi (.app (.app (.var 3) (.var 1)) (.var 0)) (.app (.app (.var 3) (.var 2)) (.var 1))))) (.lam (.var 3) (.app (.app (.app (.app (.app (.app (.var 5) (.var 4)) (.var 3)) (.var 0)) (.lam (.var 4) (.lam (.app (.app (.app (.app (.var 9) (.var 5)) (.var 4)) (.var 1)) (.var 0)) (.app (.app (.app (.app (.var 10) (.var 6)) (.var 4)) (.var 2)) (.var 1))))) (.app (.app (.app (.var 7) (.var 4)) (.var 2)) (.var 0))) (.lam (.var 4) (.lam (.app (.app (.var 4) (.var 1)) (.var 0)) (.app (.app (.app (.app (.app (.var 8) (.var 6)) (.var 4)) (.var 2)) (.var 1)) (.app (.app (.app (.var 3) (.var 2)) (.var 1)) (.var 0))))))))))))))

theorem normalizedGoal_ReflGen_mono_eq :
    normalizedGoal_ReflGen_mono =
      LFBetaEta.normalForm [] PureBetaEta.normalizationFuel
        (encodeExpr PureDTTBench31.goal_Relation_ReflGen_mono) := by
  decide

theorem normalizedCandidate_ReflGen_mono_eq :
    normalizedCandidate_ReflGen_mono =
      LFBetaEta.normalForm [] PureBetaEta.normalizationFuel
        candidate_ReflGen_mono := by
  decide

def replay_ReflGen_mono : ReplayCase :=
  { name := "ReflGen_mono", actionCount := 32, traceSha256 := "c32c6df44fac39fc32f72afc31f1bffcd1cccdf55c80b98f0b6381c5c8102f3f", referenceTermSha256 := "5fe0b101a532df9215c89664d06f2a1b6f22bf119bb15e8d1191a8b2267ae31e"
    goal := encodeExpr PureDTTBench31.goal_Relation_ReflGen_mono
    candidate := candidate_ReflGen_mono }

theorem replay_ReflGen_mono_accepted : accepts replay_ReflGen_mono = true := by
  decide

theorem replay_ReflGen_mono_sound :
    LFConversionProfileChecker.Deriv LFProfile.indexed [] []
      candidate_ReflGen_mono (encodeExpr PureDTTBench31.goal_Relation_ReflGen_mono) :=
  LFConversionProfileChecker.S1 replay_ReflGen_mono_accepted

def candidate_ReflTransGen_trans : LF.Term :=
  .lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.srt .type))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.app (.app (.app (.app (.var 3) (.var 2)) (.var 1)) (.var 0)) (.var 0))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.pi (.var 3) (.pi (.app (.app (.app (.app (.var 6) (.var 4)) (.var 3)) (.var 2)) (.var 1)) (.pi (.app (.app (.var 4) (.var 2)) (.var 1)) (.app (.app (.app (.app (.var 8) (.var 6)) (.var 5)) (.var 4)) (.var 2))))))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.pi (.var 2) (.pi (.app (.app (.app (.app (.var 6) (.var 3)) (.var 2)) (.var 1)) (.var 0)) (.srt .type))) (.pi (.app (.app (.var 0) (.var 1)) (.app (.app (.app (.var 5) (.var 3)) (.var 2)) (.var 1))) (.pi (.pi (.var 4) (.pi (.var 5) (.pi (.app (.app (.app (.app (.var 9) (.var 6)) (.var 5)) (.var 4)) (.var 1)) (.pi (.app (.app (.var 6) (.var 2)) (.var 1)) (.pi (.app (.app (.var 5) (.var 3)) (.var 1)) (.app (.app (.var 6) (.var 3)) (.app (.app (.app (.app (.app (.app (.app (.var 10) (.var 9)) (.var 8)) (.var 7)) (.var 4)) (.var 3)) (.var 2)) (.var 1)))))))) (.pi (.var 5) (.pi (.app (.app (.app (.app (.var 9) (.var 6)) (.var 5)) (.var 4)) (.var 0)) (.app (.app (.var 4) (.var 1)) (.var 0)))))))))) (.lam (.srt .type) (.lam (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.lam (.var 1) (.lam (.var 2) (.lam (.var 3) (.lam (.app (.app (.app (.app (.var 8) (.var 4)) (.var 3)) (.var 2)) (.var 1)) (.lam (.app (.app (.app (.app (.var 9) (.var 5)) (.var 4)) (.var 2)) (.var 1)) (.app (.app (.app (.app (.app (.app (.app (.app (.var 7) (.var 6)) (.lam (.var 6) (.lam (.var 7) (.app (.app (.var 7) (.var 1)) (.var 0))))) (.var 3)) (.lam (.var 6) (.lam (.app (.app (.app (.app (.var 11) (.var 7)) (.lam (.var 7) (.lam (.var 8) (.app (.app (.var 8) (.var 1)) (.var 0))))) (.var 4)) (.var 0)) (.app (.app (.app (.app (.var 12) (.var 8)) (.lam (.var 8) (.lam (.var 9) (.app (.app (.var 9) (.var 1)) (.var 0))))) (.var 6)) (.var 1))))) (.var 1)) (.lam (.var 6) (.lam (.var 7) (.lam (.app (.app (.app (.app (.var 12) (.var 8)) (.lam (.var 8) (.lam (.var 9) (.app (.app (.var 9) (.var 1)) (.var 0))))) (.var 5)) (.var 1)) (.lam (.app (.app (.lam (.var 9) (.lam (.var 10) (.app (.app (.var 10) (.var 1)) (.var 0)))) (.var 2)) (.var 1)) (.lam (.app (.app (.lam (.var 10) (.lam (.app (.app (.app (.app (.var 15) (.var 11)) (.lam (.var 11) (.lam (.var 12) (.app (.app (.var 12) (.var 1)) (.var 0))))) (.var 8)) (.var 0)) (.app (.app (.app (.app (.var 16) (.var 12)) (.lam (.var 12) (.lam (.var 13) (.app (.app (.var 13) (.var 1)) (.var 0))))) (.var 10)) (.var 1)))) (.var 3)) (.var 1)) (.app (.app (.app (.app (.app (.app (.app (.var 13) (.var 11)) (.lam (.var 11) (.lam (.var 12) (.app (.app (.var 12) (.var 1)) (.var 0))))) (.var 9)) (.var 4)) (.var 3)) (.var 0)) (.var 1)))))))) (.var 2)) (.var 0))))))))))))

def normalizedGoal_ReflTransGen_trans : LF.Term :=
  .pi (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.srt .type))))) (.pi (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.app (.app (.app (.app (.var 3) (.var 2)) (.var 1)) (.var 0)) (.var 0))))) (.pi (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.pi (.var 3) (.pi (.app (.app (.app (.app (.var 6) (.var 4)) (.var 3)) (.var 2)) (.var 1)) (.pi (.app (.app (.var 4) (.var 2)) (.var 1)) (.app (.app (.app (.app (.var 8) (.var 6)) (.var 5)) (.var 4)) (.var 2))))))))) (.pi (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.pi (.var 2) (.pi (.app (.app (.app (.app (.var 6) (.var 3)) (.var 2)) (.var 1)) (.var 0)) (.srt .type))) (.pi (.app (.app (.var 0) (.var 1)) (.app (.app (.app (.var 5) (.var 3)) (.var 2)) (.var 1))) (.pi (.pi (.var 4) (.pi (.var 5) (.pi (.app (.app (.app (.app (.var 9) (.var 6)) (.var 5)) (.var 4)) (.var 1)) (.pi (.app (.app (.var 6) (.var 2)) (.var 1)) (.pi (.app (.app (.var 5) (.var 3)) (.var 1)) (.app (.app (.var 6) (.var 3)) (.app (.app (.app (.app (.app (.app (.app (.var 10) (.var 9)) (.var 8)) (.var 7)) (.var 4)) (.var 3)) (.var 2)) (.var 1)))))))) (.pi (.var 5) (.pi (.app (.app (.app (.app (.var 9) (.var 6)) (.var 5)) (.var 4)) (.var 0)) (.app (.app (.var 4) (.var 1)) (.var 0)))))))))) (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.pi (.var 3) (.pi (.app (.app (.app (.app (.var 8) (.var 4)) (.var 3)) (.var 2)) (.var 1)) (.pi (.app (.app (.app (.app (.var 9) (.var 5)) (.var 4)) (.var 2)) (.var 1)) (.app (.app (.app (.app (.var 10) (.var 6)) (.var 5)) (.var 4)) (.var 2))))))))))))

def normalizedCandidate_ReflTransGen_trans : LF.Term :=
  .lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.srt .type))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.app (.app (.app (.app (.var 3) (.var 2)) (.var 1)) (.var 0)) (.var 0))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.pi (.var 3) (.pi (.app (.app (.app (.app (.var 6) (.var 4)) (.var 3)) (.var 2)) (.var 1)) (.pi (.app (.app (.var 4) (.var 2)) (.var 1)) (.app (.app (.app (.app (.var 8) (.var 6)) (.var 5)) (.var 4)) (.var 2))))))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.pi (.var 2) (.pi (.app (.app (.app (.app (.var 6) (.var 3)) (.var 2)) (.var 1)) (.var 0)) (.srt .type))) (.pi (.app (.app (.var 0) (.var 1)) (.app (.app (.app (.var 5) (.var 3)) (.var 2)) (.var 1))) (.pi (.pi (.var 4) (.pi (.var 5) (.pi (.app (.app (.app (.app (.var 9) (.var 6)) (.var 5)) (.var 4)) (.var 1)) (.pi (.app (.app (.var 6) (.var 2)) (.var 1)) (.pi (.app (.app (.var 5) (.var 3)) (.var 1)) (.app (.app (.var 6) (.var 3)) (.app (.app (.app (.app (.app (.app (.app (.var 10) (.var 9)) (.var 8)) (.var 7)) (.var 4)) (.var 3)) (.var 2)) (.var 1)))))))) (.pi (.var 5) (.pi (.app (.app (.app (.app (.var 9) (.var 6)) (.var 5)) (.var 4)) (.var 0)) (.app (.app (.var 4) (.var 1)) (.var 0)))))))))) (.lam (.srt .type) (.lam (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.lam (.var 1) (.lam (.var 2) (.lam (.var 3) (.lam (.app (.app (.app (.app (.var 8) (.var 4)) (.var 3)) (.var 2)) (.var 1)) (.app (.app (.app (.app (.app (.app (.app (.var 6) (.var 5)) (.var 4)) (.var 2)) (.lam (.var 5) (.lam (.app (.app (.app (.app (.var 10) (.var 6)) (.var 5)) (.var 3)) (.var 0)) (.app (.app (.app (.app (.var 11) (.var 7)) (.var 6)) (.var 5)) (.var 1))))) (.var 0)) (.lam (.var 5) (.lam (.var 6) (.lam (.app (.app (.app (.app (.var 11) (.var 7)) (.var 6)) (.var 4)) (.var 1)) (.lam (.app (.app (.var 7) (.var 2)) (.var 1)) (.lam (.app (.app (.app (.app (.var 13) (.var 9)) (.var 8)) (.var 7)) (.var 3)) (.app (.app (.app (.app (.app (.app (.app (.var 12) (.var 10)) (.var 9)) (.var 8)) (.var 4)) (.var 3)) (.var 0)) (.var 1)))))))) (.var 1)))))))))))

theorem normalizedGoal_ReflTransGen_trans_eq :
    normalizedGoal_ReflTransGen_trans =
      LFBetaEta.normalForm [] PureBetaEta.normalizationFuel
        (encodeExpr PureDTTBench31.goal_Relation_ReflTransGen_trans) := by
  decide

theorem normalizedCandidate_ReflTransGen_trans_eq :
    normalizedCandidate_ReflTransGen_trans =
      LFBetaEta.normalForm [] PureBetaEta.normalizationFuel
        candidate_ReflTransGen_trans := by
  decide

def replay_ReflTransGen_trans : ReplayCase :=
  { name := "ReflTransGen_trans", actionCount := 26, traceSha256 := "bc52d0065fce848bafe0695f9c92c9d11d5b575d72137fb4a5d719aac163e87d", referenceTermSha256 := "eddf46927ff01cca2431c4333a312d3915b0d795aca54421c68d3e133e2f0488"
    goal := encodeExpr PureDTTBench31.goal_Relation_ReflTransGen_trans
    candidate := candidate_ReflTransGen_trans }

theorem replay_ReflTransGen_trans_accepted : accepts replay_ReflTransGen_trans = true := by
  decide

theorem replay_ReflTransGen_trans_sound :
    LFConversionProfileChecker.Deriv LFProfile.indexed [] []
      candidate_ReflTransGen_trans (encodeExpr PureDTTBench31.goal_Relation_ReflTransGen_trans) :=
  LFConversionProfileChecker.S1 replay_ReflTransGen_trans_accepted

def candidate_ReflTransGen_head : LF.Term :=
  .lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.srt .type))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.app (.app (.app (.app (.var 3) (.var 2)) (.var 1)) (.var 0)) (.var 0))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.pi (.var 3) (.pi (.app (.app (.app (.app (.var 6) (.var 4)) (.var 3)) (.var 2)) (.var 1)) (.pi (.app (.app (.var 4) (.var 2)) (.var 1)) (.app (.app (.app (.app (.var 8) (.var 6)) (.var 5)) (.var 4)) (.var 2))))))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.pi (.var 2) (.pi (.app (.app (.app (.app (.var 6) (.var 3)) (.var 2)) (.var 1)) (.var 0)) (.srt .type))) (.pi (.app (.app (.var 0) (.var 1)) (.app (.app (.app (.var 5) (.var 3)) (.var 2)) (.var 1))) (.pi (.pi (.var 4) (.pi (.var 5) (.pi (.app (.app (.app (.app (.var 9) (.var 6)) (.var 5)) (.var 4)) (.var 1)) (.pi (.app (.app (.var 6) (.var 2)) (.var 1)) (.pi (.app (.app (.var 5) (.var 3)) (.var 1)) (.app (.app (.var 6) (.var 3)) (.app (.app (.app (.app (.app (.app (.app (.var 10) (.var 9)) (.var 8)) (.var 7)) (.var 4)) (.var 3)) (.var 2)) (.var 1)))))))) (.pi (.var 5) (.pi (.app (.app (.app (.app (.var 9) (.var 6)) (.var 5)) (.var 4)) (.var 0)) (.app (.app (.var 4) (.var 1)) (.var 0)))))))))) (.lam (.srt .type) (.lam (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.lam (.var 1) (.lam (.var 2) (.lam (.var 3) (.lam (.app (.app (.var 3) (.var 2)) (.var 1)) (.lam (.app (.app (.app (.app (.var 9) (.var 5)) (.var 4)) (.var 2)) (.var 1)) (.app (.app (.app (.app (.app (.app (.app (.app (.var 7) (.var 6)) (.lam (.var 6) (.lam (.var 7) (.app (.app (.var 7) (.var 1)) (.var 0))))) (.var 3)) (.lam (.var 6) (.lam (.app (.app (.app (.app (.var 11) (.var 7)) (.lam (.var 7) (.lam (.var 8) (.app (.app (.var 8) (.var 1)) (.var 0))))) (.var 4)) (.var 0)) (.app (.app (.app (.app (.var 12) (.var 8)) (.lam (.var 8) (.lam (.var 9) (.app (.app (.var 9) (.var 1)) (.var 0))))) (.var 6)) (.var 1))))) (.app (.app (.app (.app (.app (.app (.app (.var 8) (.var 6)) (.lam (.var 6) (.lam (.var 7) (.app (.app (.var 7) (.var 1)) (.var 0))))) (.var 4)) (.var 4)) (.var 3)) (.app (.app (.app (.var 9) (.var 6)) (.lam (.var 6) (.lam (.var 7) (.app (.app (.var 7) (.var 1)) (.var 0))))) (.var 4))) (.var 1))) (.lam (.var 6) (.lam (.var 7) (.lam (.app (.app (.app (.app (.var 12) (.var 8)) (.lam (.var 8) (.lam (.var 9) (.app (.app (.var 9) (.var 1)) (.var 0))))) (.var 5)) (.var 1)) (.lam (.app (.app (.lam (.var 9) (.lam (.var 10) (.app (.app (.var 10) (.var 1)) (.var 0)))) (.var 2)) (.var 1)) (.lam (.app (.app (.lam (.var 10) (.lam (.app (.app (.app (.app (.var 15) (.var 11)) (.lam (.var 11) (.lam (.var 12) (.app (.app (.var 12) (.var 1)) (.var 0))))) (.var 8)) (.var 0)) (.app (.app (.app (.app (.var 16) (.var 12)) (.lam (.var 12) (.lam (.var 13) (.app (.app (.var 13) (.var 1)) (.var 0))))) (.var 10)) (.var 1)))) (.var 3)) (.var 1)) (.app (.app (.app (.app (.app (.app (.app (.var 13) (.var 11)) (.lam (.var 11) (.lam (.var 12) (.app (.app (.var 12) (.var 1)) (.var 0))))) (.var 9)) (.var 4)) (.var 3)) (.var 0)) (.var 1)))))))) (.var 2)) (.var 0))))))))))))

def normalizedGoal_ReflTransGen_head : LF.Term :=
  .pi (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.srt .type))))) (.pi (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.app (.app (.app (.app (.var 3) (.var 2)) (.var 1)) (.var 0)) (.var 0))))) (.pi (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.pi (.var 3) (.pi (.app (.app (.app (.app (.var 6) (.var 4)) (.var 3)) (.var 2)) (.var 1)) (.pi (.app (.app (.var 4) (.var 2)) (.var 1)) (.app (.app (.app (.app (.var 8) (.var 6)) (.var 5)) (.var 4)) (.var 2))))))))) (.pi (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.pi (.var 2) (.pi (.app (.app (.app (.app (.var 6) (.var 3)) (.var 2)) (.var 1)) (.var 0)) (.srt .type))) (.pi (.app (.app (.var 0) (.var 1)) (.app (.app (.app (.var 5) (.var 3)) (.var 2)) (.var 1))) (.pi (.pi (.var 4) (.pi (.var 5) (.pi (.app (.app (.app (.app (.var 9) (.var 6)) (.var 5)) (.var 4)) (.var 1)) (.pi (.app (.app (.var 6) (.var 2)) (.var 1)) (.pi (.app (.app (.var 5) (.var 3)) (.var 1)) (.app (.app (.var 6) (.var 3)) (.app (.app (.app (.app (.app (.app (.app (.var 10) (.var 9)) (.var 8)) (.var 7)) (.var 4)) (.var 3)) (.var 2)) (.var 1)))))))) (.pi (.var 5) (.pi (.app (.app (.app (.app (.var 9) (.var 6)) (.var 5)) (.var 4)) (.var 0)) (.app (.app (.var 4) (.var 1)) (.var 0)))))))))) (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.pi (.var 3) (.pi (.app (.app (.var 3) (.var 2)) (.var 1)) (.pi (.app (.app (.app (.app (.var 9) (.var 5)) (.var 4)) (.var 2)) (.var 1)) (.app (.app (.app (.app (.var 10) (.var 6)) (.var 5)) (.var 4)) (.var 2))))))))))))

def normalizedCandidate_ReflTransGen_head : LF.Term :=
  .lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.srt .type))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.app (.app (.app (.app (.var 3) (.var 2)) (.var 1)) (.var 0)) (.var 0))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.pi (.var 3) (.pi (.app (.app (.app (.app (.var 6) (.var 4)) (.var 3)) (.var 2)) (.var 1)) (.pi (.app (.app (.var 4) (.var 2)) (.var 1)) (.app (.app (.app (.app (.var 8) (.var 6)) (.var 5)) (.var 4)) (.var 2))))))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.pi (.var 2) (.pi (.app (.app (.app (.app (.var 6) (.var 3)) (.var 2)) (.var 1)) (.var 0)) (.srt .type))) (.pi (.app (.app (.var 0) (.var 1)) (.app (.app (.app (.var 5) (.var 3)) (.var 2)) (.var 1))) (.pi (.pi (.var 4) (.pi (.var 5) (.pi (.app (.app (.app (.app (.var 9) (.var 6)) (.var 5)) (.var 4)) (.var 1)) (.pi (.app (.app (.var 6) (.var 2)) (.var 1)) (.pi (.app (.app (.var 5) (.var 3)) (.var 1)) (.app (.app (.var 6) (.var 3)) (.app (.app (.app (.app (.app (.app (.app (.var 10) (.var 9)) (.var 8)) (.var 7)) (.var 4)) (.var 3)) (.var 2)) (.var 1)))))))) (.pi (.var 5) (.pi (.app (.app (.app (.app (.var 9) (.var 6)) (.var 5)) (.var 4)) (.var 0)) (.app (.app (.var 4) (.var 1)) (.var 0)))))))))) (.lam (.srt .type) (.lam (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.lam (.var 1) (.lam (.var 2) (.lam (.var 3) (.lam (.app (.app (.var 3) (.var 2)) (.var 1)) (.app (.app (.app (.app (.app (.app (.app (.var 6) (.var 5)) (.var 4)) (.var 2)) (.lam (.var 5) (.lam (.app (.app (.app (.app (.var 10) (.var 6)) (.var 5)) (.var 3)) (.var 0)) (.app (.app (.app (.app (.var 11) (.var 7)) (.var 6)) (.var 5)) (.var 1))))) (.app (.app (.app (.app (.app (.app (.app (.var 7) (.var 5)) (.var 4)) (.var 3)) (.var 3)) (.var 2)) (.app (.app (.app (.var 8) (.var 5)) (.var 4)) (.var 3))) (.var 0))) (.lam (.var 5) (.lam (.var 6) (.lam (.app (.app (.app (.app (.var 11) (.var 7)) (.var 6)) (.var 4)) (.var 1)) (.lam (.app (.app (.var 7) (.var 2)) (.var 1)) (.lam (.app (.app (.app (.app (.var 13) (.var 9)) (.var 8)) (.var 7)) (.var 3)) (.app (.app (.app (.app (.app (.app (.app (.var 12) (.var 10)) (.var 9)) (.var 8)) (.var 4)) (.var 3)) (.var 0)) (.var 1)))))))) (.var 1)))))))))))

theorem normalizedGoal_ReflTransGen_head_eq :
    normalizedGoal_ReflTransGen_head =
      LFBetaEta.normalForm [] PureBetaEta.normalizationFuel
        (encodeExpr PureDTTBench31.goal_Relation_ReflTransGen_head) := by
  decide

theorem normalizedCandidate_ReflTransGen_head_eq :
    normalizedCandidate_ReflTransGen_head =
      LFBetaEta.normalForm [] PureBetaEta.normalizationFuel
        candidate_ReflTransGen_head := by
  decide

def replay_ReflTransGen_head : ReplayCase :=
  { name := "ReflTransGen_head", actionCount := 40, traceSha256 := "65e8c384d7be38036d4fc892221596e146abe6858336b1f2cb53bb950fd5bfc9", referenceTermSha256 := "cea177a135b64afeda35c5be139c0a6cf4481ee3b9723a077e40c94bcceea19b"
    goal := encodeExpr PureDTTBench31.goal_Relation_ReflTransGen_head
    candidate := candidate_ReflTransGen_head }

theorem replay_ReflTransGen_head_accepted : accepts replay_ReflTransGen_head = true := by
  decide

theorem replay_ReflTransGen_head_sound :
    LFConversionProfileChecker.Deriv LFProfile.indexed [] []
      candidate_ReflTransGen_head (encodeExpr PureDTTBench31.goal_Relation_ReflTransGen_head) :=
  LFConversionProfileChecker.S1 replay_ReflTransGen_head_accepted

def candidate_ReflTransGen_symmetric : LF.Term :=
  .lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.srt .type))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.app (.app (.app (.app (.var 3) (.var 2)) (.var 1)) (.var 0)) (.var 0))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.pi (.var 3) (.pi (.app (.app (.app (.app (.var 6) (.var 4)) (.var 3)) (.var 2)) (.var 1)) (.pi (.app (.app (.var 4) (.var 2)) (.var 1)) (.app (.app (.app (.app (.var 8) (.var 6)) (.var 5)) (.var 4)) (.var 2))))))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.pi (.var 2) (.pi (.app (.app (.app (.app (.var 6) (.var 3)) (.var 2)) (.var 1)) (.var 0)) (.srt .type))) (.pi (.app (.app (.var 0) (.var 1)) (.app (.app (.app (.var 5) (.var 3)) (.var 2)) (.var 1))) (.pi (.pi (.var 4) (.pi (.var 5) (.pi (.app (.app (.app (.app (.var 9) (.var 6)) (.var 5)) (.var 4)) (.var 1)) (.pi (.app (.app (.var 6) (.var 2)) (.var 1)) (.pi (.app (.app (.var 5) (.var 3)) (.var 1)) (.app (.app (.var 6) (.var 3)) (.app (.app (.app (.app (.app (.app (.app (.var 10) (.var 9)) (.var 8)) (.var 7)) (.var 4)) (.var 3)) (.var 2)) (.var 1)))))))) (.pi (.var 5) (.pi (.app (.app (.app (.app (.var 9) (.var 6)) (.var 5)) (.var 4)) (.var 0)) (.app (.app (.var 4) (.var 1)) (.var 0)))))))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.pi (.var 3) (.pi (.app (.app (.var 3) (.var 2)) (.var 1)) (.pi (.app (.app (.app (.app (.var 9) (.var 5)) (.var 4)) (.var 2)) (.var 1)) (.app (.app (.app (.app (.var 10) (.var 6)) (.var 5)) (.var 4)) (.var 2))))))))) (.lam (.srt .type) (.lam (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.lam (.pi (.var 1) (.pi (.var 2) (.pi (.app (.app (.var 2) (.var 1)) (.var 0)) (.app (.app (.var 3) (.var 1)) (.var 2))))) (.lam (.var 2) (.lam (.var 3) (.lam (.app (.app (.app (.app (.var 9) (.var 4)) (.var 3)) (.var 1)) (.var 0)) (.app (.app (.app (.app (.app (.app (.app (.app (.var 7) (.var 5)) (.lam (.var 5) (.lam (.var 6) (.app (.app (.var 6) (.var 1)) (.var 0))))) (.var 2)) (.lam (.var 5) (.lam (.app (.app (.app (.app (.var 11) (.var 6)) (.lam (.var 6) (.lam (.var 7) (.app (.app (.var 7) (.var 1)) (.var 0))))) (.var 3)) (.var 0)) (.app (.app (.app (.app (.var 12) (.var 7)) (.lam (.var 7) (.lam (.var 8) (.app (.app (.var 8) (.var 1)) (.var 0))))) (.var 1)) (.var 4))))) (.app (.app (.app (.var 9) (.var 5)) (.lam (.var 5) (.lam (.var 6) (.app (.app (.var 6) (.var 1)) (.var 0))))) (.var 2))) (.lam (.var 5) (.lam (.var 6) (.lam (.app (.app (.app (.app (.var 12) (.var 7)) (.lam (.var 7) (.lam (.var 8) (.app (.app (.var 8) (.var 1)) (.var 0))))) (.var 4)) (.var 1)) (.lam (.app (.app (.lam (.var 8) (.lam (.var 9) (.app (.app (.var 9) (.var 1)) (.var 0)))) (.var 2)) (.var 1)) (.lam (.app (.app (.lam (.var 9) (.lam (.app (.app (.app (.app (.var 15) (.var 10)) (.lam (.var 10) (.lam (.var 11) (.app (.app (.var 11) (.var 1)) (.var 0))))) (.var 7)) (.var 0)) (.app (.app (.app (.app (.var 16) (.var 11)) (.lam (.var 11) (.lam (.var 12) (.app (.app (.var 12) (.var 1)) (.var 0))))) (.var 1)) (.var 8)))) (.var 3)) (.var 1)) (.app (.app (.app (.app (.app (.app (.app (.var 11) (.var 10)) (.lam (.var 10) (.lam (.var 11) (.app (.app (.var 11) (.var 1)) (.var 0))))) (.var 3)) (.var 4)) (.var 7)) (.app (.app (.app (.var 8) (.var 4)) (.var 3)) (.var 1))) (.var 0)))))))) (.var 1)) (.var 0))))))))))))

def normalizedGoal_ReflTransGen_symmetric : LF.Term :=
  .pi (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.srt .type))))) (.pi (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.app (.app (.app (.app (.var 3) (.var 2)) (.var 1)) (.var 0)) (.var 0))))) (.pi (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.pi (.var 3) (.pi (.app (.app (.app (.app (.var 6) (.var 4)) (.var 3)) (.var 2)) (.var 1)) (.pi (.app (.app (.var 4) (.var 2)) (.var 1)) (.app (.app (.app (.app (.var 8) (.var 6)) (.var 5)) (.var 4)) (.var 2))))))))) (.pi (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.pi (.var 2) (.pi (.app (.app (.app (.app (.var 6) (.var 3)) (.var 2)) (.var 1)) (.var 0)) (.srt .type))) (.pi (.app (.app (.var 0) (.var 1)) (.app (.app (.app (.var 5) (.var 3)) (.var 2)) (.var 1))) (.pi (.pi (.var 4) (.pi (.var 5) (.pi (.app (.app (.app (.app (.var 9) (.var 6)) (.var 5)) (.var 4)) (.var 1)) (.pi (.app (.app (.var 6) (.var 2)) (.var 1)) (.pi (.app (.app (.var 5) (.var 3)) (.var 1)) (.app (.app (.var 6) (.var 3)) (.app (.app (.app (.app (.app (.app (.app (.var 10) (.var 9)) (.var 8)) (.var 7)) (.var 4)) (.var 3)) (.var 2)) (.var 1)))))))) (.pi (.var 5) (.pi (.app (.app (.app (.app (.var 9) (.var 6)) (.var 5)) (.var 4)) (.var 0)) (.app (.app (.var 4) (.var 1)) (.var 0)))))))))) (.pi (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.pi (.var 3) (.pi (.app (.app (.var 3) (.var 2)) (.var 1)) (.pi (.app (.app (.app (.app (.var 9) (.var 5)) (.var 4)) (.var 2)) (.var 1)) (.app (.app (.app (.app (.var 10) (.var 6)) (.var 5)) (.var 4)) (.var 2))))))))) (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.pi (.var 1) (.pi (.var 2) (.pi (.app (.app (.var 2) (.var 1)) (.var 0)) (.app (.app (.var 3) (.var 1)) (.var 2))))) (.pi (.var 2) (.pi (.var 3) (.pi (.app (.app (.app (.app (.var 9) (.var 4)) (.var 3)) (.var 1)) (.var 0)) (.app (.app (.app (.app (.var 10) (.var 5)) (.var 4)) (.var 1)) (.var 2))))))))))))

def normalizedCandidate_ReflTransGen_symmetric : LF.Term :=
  .lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.srt .type))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.app (.app (.app (.app (.var 3) (.var 2)) (.var 1)) (.var 0)) (.var 0))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.pi (.var 3) (.pi (.app (.app (.app (.app (.var 6) (.var 4)) (.var 3)) (.var 2)) (.var 1)) (.pi (.app (.app (.var 4) (.var 2)) (.var 1)) (.app (.app (.app (.app (.var 8) (.var 6)) (.var 5)) (.var 4)) (.var 2))))))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.pi (.var 2) (.pi (.app (.app (.app (.app (.var 6) (.var 3)) (.var 2)) (.var 1)) (.var 0)) (.srt .type))) (.pi (.app (.app (.var 0) (.var 1)) (.app (.app (.app (.var 5) (.var 3)) (.var 2)) (.var 1))) (.pi (.pi (.var 4) (.pi (.var 5) (.pi (.app (.app (.app (.app (.var 9) (.var 6)) (.var 5)) (.var 4)) (.var 1)) (.pi (.app (.app (.var 6) (.var 2)) (.var 1)) (.pi (.app (.app (.var 5) (.var 3)) (.var 1)) (.app (.app (.var 6) (.var 3)) (.app (.app (.app (.app (.app (.app (.app (.var 10) (.var 9)) (.var 8)) (.var 7)) (.var 4)) (.var 3)) (.var 2)) (.var 1)))))))) (.pi (.var 5) (.pi (.app (.app (.app (.app (.var 9) (.var 6)) (.var 5)) (.var 4)) (.var 0)) (.app (.app (.var 4) (.var 1)) (.var 0)))))))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.pi (.var 3) (.pi (.app (.app (.var 3) (.var 2)) (.var 1)) (.pi (.app (.app (.app (.app (.var 9) (.var 5)) (.var 4)) (.var 2)) (.var 1)) (.app (.app (.app (.app (.var 10) (.var 6)) (.var 5)) (.var 4)) (.var 2))))))))) (.lam (.srt .type) (.lam (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.lam (.pi (.var 1) (.pi (.var 2) (.pi (.app (.app (.var 2) (.var 1)) (.var 0)) (.app (.app (.var 3) (.var 1)) (.var 2))))) (.lam (.var 2) (.app (.app (.app (.app (.app (.app (.var 5) (.var 3)) (.var 2)) (.var 0)) (.lam (.var 3) (.lam (.app (.app (.app (.app (.var 9) (.var 4)) (.var 3)) (.var 1)) (.var 0)) (.app (.app (.app (.app (.var 10) (.var 5)) (.var 4)) (.var 1)) (.var 2))))) (.app (.app (.app (.var 7) (.var 3)) (.var 2)) (.var 0))) (.lam (.var 3) (.lam (.var 4) (.lam (.app (.app (.app (.app (.var 10) (.var 5)) (.var 4)) (.var 2)) (.var 1)) (.lam (.app (.app (.var 5) (.var 2)) (.var 1)) (.app (.app (.app (.app (.app (.app (.var 8) (.var 7)) (.var 6)) (.var 2)) (.var 3)) (.var 4)) (.app (.app (.app (.var 5) (.var 3)) (.var 2)) (.var 0))))))))))))))))

theorem normalizedGoal_ReflTransGen_symmetric_eq :
    normalizedGoal_ReflTransGen_symmetric =
      LFBetaEta.normalForm [] PureBetaEta.normalizationFuel
        (encodeExpr PureDTTBench31.goal_Relation_ReflTransGen_symmetric) := by
  decide

theorem normalizedCandidate_ReflTransGen_symmetric_eq :
    normalizedCandidate_ReflTransGen_symmetric =
      LFBetaEta.normalForm [] PureBetaEta.normalizationFuel
        candidate_ReflTransGen_symmetric := by
  decide

def replay_ReflTransGen_symmetric : ReplayCase :=
  { name := "ReflTransGen_symmetric", actionCount := 34, traceSha256 := "126d5ea08fc49f0bb4fb28a6d5d6c9017f98befb58358ac8a03b00a2ddf2aafd", referenceTermSha256 := "ff539635cff9c652f72cfa02868a9ae918ece1b143723a0795a2609786fb5024"
    goal := encodeExpr PureDTTBench31.goal_Relation_ReflTransGen_symmetric
    candidate := candidate_ReflTransGen_symmetric }

theorem replay_ReflTransGen_symmetric_accepted : accepts replay_ReflTransGen_symmetric = true := by
  decide

theorem replay_ReflTransGen_symmetric_sound :
    LFConversionProfileChecker.Deriv LFProfile.indexed [] []
      candidate_ReflTransGen_symmetric (encodeExpr PureDTTBench31.goal_Relation_ReflTransGen_symmetric) :=
  LFConversionProfileChecker.S1 replay_ReflTransGen_symmetric_accepted

def candidate_TransGen_to_reflTransGen : LF.Term :=
  .lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.srt .type))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.pi (.app (.app (.var 2) (.var 1)) (.var 0)) (.app (.app (.app (.app (.var 5) (.var 4)) (.var 3)) (.var 2)) (.var 1))))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.pi (.var 3) (.pi (.app (.app (.app (.app (.var 6) (.var 4)) (.var 3)) (.var 2)) (.var 1)) (.pi (.app (.app (.var 4) (.var 2)) (.var 1)) (.app (.app (.app (.app (.var 8) (.var 6)) (.var 5)) (.var 4)) (.var 2))))))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.pi (.var 2) (.pi (.app (.app (.app (.app (.var 6) (.var 3)) (.var 2)) (.var 1)) (.var 0)) (.srt .type))) (.pi (.pi (.var 3) (.pi (.app (.app (.var 3) (.var 2)) (.var 0)) (.app (.app (.var 2) (.var 1)) (.app (.app (.app (.app (.app (.var 7) (.var 5)) (.var 4)) (.var 3)) (.var 1)) (.var 0))))) (.pi (.pi (.var 4) (.pi (.var 5) (.pi (.app (.app (.app (.app (.var 9) (.var 6)) (.var 5)) (.var 4)) (.var 1)) (.pi (.app (.app (.var 6) (.var 2)) (.var 1)) (.pi (.app (.app (.var 5) (.var 3)) (.var 1)) (.app (.app (.var 6) (.var 3)) (.app (.app (.app (.app (.app (.app (.app (.var 10) (.var 9)) (.var 8)) (.var 7)) (.var 4)) (.var 3)) (.var 2)) (.var 1)))))))) (.pi (.var 5) (.pi (.app (.app (.app (.app (.var 9) (.var 6)) (.var 5)) (.var 4)) (.var 0)) (.app (.app (.var 4) (.var 1)) (.var 0)))))))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.srt .type))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.app (.app (.app (.app (.var 3) (.var 2)) (.var 1)) (.var 0)) (.var 0))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.pi (.var 3) (.pi (.app (.app (.app (.app (.var 6) (.var 4)) (.var 3)) (.var 2)) (.var 1)) (.pi (.app (.app (.var 4) (.var 2)) (.var 1)) (.app (.app (.app (.app (.var 8) (.var 6)) (.var 5)) (.var 4)) (.var 2))))))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.pi (.var 2) (.pi (.app (.app (.app (.app (.var 6) (.var 3)) (.var 2)) (.var 1)) (.var 0)) (.srt .type))) (.pi (.app (.app (.var 0) (.var 1)) (.app (.app (.app (.var 5) (.var 3)) (.var 2)) (.var 1))) (.pi (.pi (.var 4) (.pi (.var 5) (.pi (.app (.app (.app (.app (.var 9) (.var 6)) (.var 5)) (.var 4)) (.var 1)) (.pi (.app (.app (.var 6) (.var 2)) (.var 1)) (.pi (.app (.app (.var 5) (.var 3)) (.var 1)) (.app (.app (.var 6) (.var 3)) (.app (.app (.app (.app (.app (.app (.app (.var 10) (.var 9)) (.var 8)) (.var 7)) (.var 4)) (.var 3)) (.var 2)) (.var 1)))))))) (.pi (.var 5) (.pi (.app (.app (.app (.app (.var 9) (.var 6)) (.var 5)) (.var 4)) (.var 0)) (.app (.app (.var 4) (.var 1)) (.var 0)))))))))) (.lam (.srt .type) (.lam (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.lam (.var 1) (.lam (.var 2) (.lam (.app (.app (.app (.app (.var 11) (.var 3)) (.var 2)) (.var 1)) (.var 0)) (.app (.app (.app (.app (.app (.app (.app (.app (.var 9) (.var 4)) (.lam (.var 4) (.lam (.var 5) (.app (.app (.var 5) (.var 1)) (.var 0))))) (.var 2)) (.lam (.var 4) (.lam (.app (.app (.app (.app (.var 13) (.var 5)) (.lam (.var 5) (.lam (.var 6) (.app (.app (.var 6) (.var 1)) (.var 0))))) (.var 3)) (.var 0)) (.app (.app (.app (.app (.var 10) (.var 6)) (.lam (.var 6) (.lam (.var 7) (.app (.app (.var 7) (.var 1)) (.var 0))))) (.var 4)) (.var 1))))) (.lam (.var 4) (.lam (.app (.app (.lam (.var 5) (.lam (.var 6) (.app (.app (.var 6) (.var 1)) (.var 0)))) (.var 3)) (.var 0)) (.app (.app (.app (.app (.app (.app (.app (.var 8) (.var 6)) (.lam (.var 6) (.lam (.var 7) (.app (.app (.var 7) (.var 1)) (.var 0))))) (.var 4)) (.var 4)) (.var 1)) (.app (.app (.app (.var 9) (.var 6)) (.lam (.var 6) (.lam (.var 7) (.app (.app (.var 7) (.var 1)) (.var 0))))) (.var 4))) (.var 0))))) (.lam (.var 4) (.lam (.var 5) (.lam (.app (.app (.app (.app (.var 14) (.var 6)) (.lam (.var 6) (.lam (.var 7) (.app (.app (.var 7) (.var 1)) (.var 0))))) (.var 4)) (.var 1)) (.lam (.app (.app (.lam (.var 7) (.lam (.var 8) (.app (.app (.var 8) (.var 1)) (.var 0)))) (.var 2)) (.var 1)) (.lam (.app (.app (.lam (.var 8) (.lam (.app (.app (.app (.app (.var 17) (.var 9)) (.lam (.var 9) (.lam (.var 10) (.app (.app (.var 10) (.var 1)) (.var 0))))) (.var 7)) (.var 0)) (.app (.app (.app (.app (.var 14) (.var 10)) (.lam (.var 10) (.lam (.var 11) (.app (.app (.var 11) (.var 1)) (.var 0))))) (.var 8)) (.var 1)))) (.var 3)) (.var 1)) (.app (.app (.app (.app (.app (.app (.app (.var 11) (.var 9)) (.lam (.var 9) (.lam (.var 10) (.app (.app (.var 10) (.var 1)) (.var 0))))) (.var 7)) (.var 4)) (.var 3)) (.var 0)) (.var 1)))))))) (.var 1)) (.var 0))))))))))))))

def normalizedGoal_TransGen_to_reflTransGen : LF.Term :=
  .pi (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.srt .type))))) (.pi (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.pi (.app (.app (.var 2) (.var 1)) (.var 0)) (.app (.app (.app (.app (.var 5) (.var 4)) (.var 3)) (.var 2)) (.var 1))))))) (.pi (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.pi (.var 3) (.pi (.app (.app (.app (.app (.var 6) (.var 4)) (.var 3)) (.var 2)) (.var 1)) (.pi (.app (.app (.var 4) (.var 2)) (.var 1)) (.app (.app (.app (.app (.var 8) (.var 6)) (.var 5)) (.var 4)) (.var 2))))))))) (.pi (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.pi (.var 2) (.pi (.app (.app (.app (.app (.var 6) (.var 3)) (.var 2)) (.var 1)) (.var 0)) (.srt .type))) (.pi (.pi (.var 3) (.pi (.app (.app (.var 3) (.var 2)) (.var 0)) (.app (.app (.var 2) (.var 1)) (.app (.app (.app (.app (.app (.var 7) (.var 5)) (.var 4)) (.var 3)) (.var 1)) (.var 0))))) (.pi (.pi (.var 4) (.pi (.var 5) (.pi (.app (.app (.app (.app (.var 9) (.var 6)) (.var 5)) (.var 4)) (.var 1)) (.pi (.app (.app (.var 6) (.var 2)) (.var 1)) (.pi (.app (.app (.var 5) (.var 3)) (.var 1)) (.app (.app (.var 6) (.var 3)) (.app (.app (.app (.app (.app (.app (.app (.var 10) (.var 9)) (.var 8)) (.var 7)) (.var 4)) (.var 3)) (.var 2)) (.var 1)))))))) (.pi (.var 5) (.pi (.app (.app (.app (.app (.var 9) (.var 6)) (.var 5)) (.var 4)) (.var 0)) (.app (.app (.var 4) (.var 1)) (.var 0)))))))))) (.pi (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.srt .type))))) (.pi (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.app (.app (.app (.app (.var 3) (.var 2)) (.var 1)) (.var 0)) (.var 0))))) (.pi (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.pi (.var 3) (.pi (.app (.app (.app (.app (.var 6) (.var 4)) (.var 3)) (.var 2)) (.var 1)) (.pi (.app (.app (.var 4) (.var 2)) (.var 1)) (.app (.app (.app (.app (.var 8) (.var 6)) (.var 5)) (.var 4)) (.var 2))))))))) (.pi (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.pi (.var 2) (.pi (.app (.app (.app (.app (.var 6) (.var 3)) (.var 2)) (.var 1)) (.var 0)) (.srt .type))) (.pi (.app (.app (.var 0) (.var 1)) (.app (.app (.app (.var 5) (.var 3)) (.var 2)) (.var 1))) (.pi (.pi (.var 4) (.pi (.var 5) (.pi (.app (.app (.app (.app (.var 9) (.var 6)) (.var 5)) (.var 4)) (.var 1)) (.pi (.app (.app (.var 6) (.var 2)) (.var 1)) (.pi (.app (.app (.var 5) (.var 3)) (.var 1)) (.app (.app (.var 6) (.var 3)) (.app (.app (.app (.app (.app (.app (.app (.var 10) (.var 9)) (.var 8)) (.var 7)) (.var 4)) (.var 3)) (.var 2)) (.var 1)))))))) (.pi (.var 5) (.pi (.app (.app (.app (.app (.var 9) (.var 6)) (.var 5)) (.var 4)) (.var 0)) (.app (.app (.var 4) (.var 1)) (.var 0)))))))))) (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.pi (.app (.app (.app (.app (.var 11) (.var 3)) (.var 2)) (.var 1)) (.var 0)) (.app (.app (.app (.app (.var 8) (.var 4)) (.var 3)) (.var 2)) (.var 1))))))))))))))

def normalizedCandidate_TransGen_to_reflTransGen : LF.Term :=
  .lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.srt .type))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.pi (.app (.app (.var 2) (.var 1)) (.var 0)) (.app (.app (.app (.app (.var 5) (.var 4)) (.var 3)) (.var 2)) (.var 1))))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.pi (.var 3) (.pi (.app (.app (.app (.app (.var 6) (.var 4)) (.var 3)) (.var 2)) (.var 1)) (.pi (.app (.app (.var 4) (.var 2)) (.var 1)) (.app (.app (.app (.app (.var 8) (.var 6)) (.var 5)) (.var 4)) (.var 2))))))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.pi (.var 2) (.pi (.app (.app (.app (.app (.var 6) (.var 3)) (.var 2)) (.var 1)) (.var 0)) (.srt .type))) (.pi (.pi (.var 3) (.pi (.app (.app (.var 3) (.var 2)) (.var 0)) (.app (.app (.var 2) (.var 1)) (.app (.app (.app (.app (.app (.var 7) (.var 5)) (.var 4)) (.var 3)) (.var 1)) (.var 0))))) (.pi (.pi (.var 4) (.pi (.var 5) (.pi (.app (.app (.app (.app (.var 9) (.var 6)) (.var 5)) (.var 4)) (.var 1)) (.pi (.app (.app (.var 6) (.var 2)) (.var 1)) (.pi (.app (.app (.var 5) (.var 3)) (.var 1)) (.app (.app (.var 6) (.var 3)) (.app (.app (.app (.app (.app (.app (.app (.var 10) (.var 9)) (.var 8)) (.var 7)) (.var 4)) (.var 3)) (.var 2)) (.var 1)))))))) (.pi (.var 5) (.pi (.app (.app (.app (.app (.var 9) (.var 6)) (.var 5)) (.var 4)) (.var 0)) (.app (.app (.var 4) (.var 1)) (.var 0)))))))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.srt .type))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.app (.app (.app (.app (.var 3) (.var 2)) (.var 1)) (.var 0)) (.var 0))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.pi (.var 3) (.pi (.app (.app (.app (.app (.var 6) (.var 4)) (.var 3)) (.var 2)) (.var 1)) (.pi (.app (.app (.var 4) (.var 2)) (.var 1)) (.app (.app (.app (.app (.var 8) (.var 6)) (.var 5)) (.var 4)) (.var 2))))))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.pi (.var 2) (.pi (.app (.app (.app (.app (.var 6) (.var 3)) (.var 2)) (.var 1)) (.var 0)) (.srt .type))) (.pi (.app (.app (.var 0) (.var 1)) (.app (.app (.app (.var 5) (.var 3)) (.var 2)) (.var 1))) (.pi (.pi (.var 4) (.pi (.var 5) (.pi (.app (.app (.app (.app (.var 9) (.var 6)) (.var 5)) (.var 4)) (.var 1)) (.pi (.app (.app (.var 6) (.var 2)) (.var 1)) (.pi (.app (.app (.var 5) (.var 3)) (.var 1)) (.app (.app (.var 6) (.var 3)) (.app (.app (.app (.app (.app (.app (.app (.var 10) (.var 9)) (.var 8)) (.var 7)) (.var 4)) (.var 3)) (.var 2)) (.var 1)))))))) (.pi (.var 5) (.pi (.app (.app (.app (.app (.var 9) (.var 6)) (.var 5)) (.var 4)) (.var 0)) (.app (.app (.var 4) (.var 1)) (.var 0)))))))))) (.lam (.srt .type) (.lam (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.lam (.var 1) (.app (.app (.app (.app (.app (.app (.var 7) (.var 2)) (.var 1)) (.var 0)) (.lam (.var 2) (.lam (.app (.app (.app (.app (.var 11) (.var 3)) (.var 2)) (.var 1)) (.var 0)) (.app (.app (.app (.app (.var 8) (.var 4)) (.var 3)) (.var 2)) (.var 1))))) (.lam (.var 2) (.app (.app (.app (.app (.app (.app (.var 5) (.var 3)) (.var 2)) (.var 1)) (.var 1)) (.var 0)) (.app (.app (.app (.var 6) (.var 3)) (.var 2)) (.var 1))))) (.lam (.var 2) (.lam (.var 3) (.lam (.app (.app (.app (.app (.var 12) (.var 4)) (.var 3)) (.var 2)) (.var 1)) (.lam (.app (.app (.var 4) (.var 2)) (.var 1)) (.lam (.app (.app (.app (.app (.var 10) (.var 6)) (.var 5)) (.var 4)) (.var 3)) (.app (.app (.app (.app (.app (.app (.app (.var 9) (.var 7)) (.var 6)) (.var 5)) (.var 4)) (.var 3)) (.var 0)) (.var 1))))))))))))))))))

theorem normalizedGoal_TransGen_to_reflTransGen_eq :
    normalizedGoal_TransGen_to_reflTransGen =
      LFBetaEta.normalForm [] PureBetaEta.normalizationFuel
        (encodeExpr PureDTTBench31.goal_Relation_TransGen_to_reflTransGen) := by
  decide

theorem normalizedCandidate_TransGen_to_reflTransGen_eq :
    normalizedCandidate_TransGen_to_reflTransGen =
      LFBetaEta.normalForm [] PureBetaEta.normalizationFuel
        candidate_TransGen_to_reflTransGen := by
  decide

def replay_TransGen_to_reflTransGen : ReplayCase :=
  { name := "TransGen_to_reflTransGen", actionCount := 40, traceSha256 := "d544a3393dae8a664a3f8f1741e243cf11289542939a5b954fcc2ba9532cab2f", referenceTermSha256 := "e05a03f0bc2e82690252621076928f84de496a9a9b1f297f151f6b31d388e01e"
    goal := encodeExpr PureDTTBench31.goal_Relation_TransGen_to_reflTransGen
    candidate := candidate_TransGen_to_reflTransGen }

theorem replay_TransGen_to_reflTransGen_accepted : accepts replay_TransGen_to_reflTransGen = true := by
  decide

theorem replay_TransGen_to_reflTransGen_sound :
    LFConversionProfileChecker.Deriv LFProfile.indexed [] []
      candidate_TransGen_to_reflTransGen (encodeExpr PureDTTBench31.goal_Relation_TransGen_to_reflTransGen) :=
  LFConversionProfileChecker.S1 replay_TransGen_to_reflTransGen_accepted

def candidate_TransGen_trans_left : LF.Term :=
  .lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.srt .type))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.pi (.app (.app (.var 2) (.var 1)) (.var 0)) (.app (.app (.app (.app (.var 5) (.var 4)) (.var 3)) (.var 2)) (.var 1))))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.pi (.var 3) (.pi (.app (.app (.app (.app (.var 6) (.var 4)) (.var 3)) (.var 2)) (.var 1)) (.pi (.app (.app (.var 4) (.var 2)) (.var 1)) (.app (.app (.app (.app (.var 8) (.var 6)) (.var 5)) (.var 4)) (.var 2))))))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.pi (.var 2) (.pi (.app (.app (.app (.app (.var 6) (.var 3)) (.var 2)) (.var 1)) (.var 0)) (.srt .type))) (.pi (.pi (.var 3) (.pi (.app (.app (.var 3) (.var 2)) (.var 0)) (.app (.app (.var 2) (.var 1)) (.app (.app (.app (.app (.app (.var 7) (.var 5)) (.var 4)) (.var 3)) (.var 1)) (.var 0))))) (.pi (.pi (.var 4) (.pi (.var 5) (.pi (.app (.app (.app (.app (.var 9) (.var 6)) (.var 5)) (.var 4)) (.var 1)) (.pi (.app (.app (.var 6) (.var 2)) (.var 1)) (.pi (.app (.app (.var 5) (.var 3)) (.var 1)) (.app (.app (.var 6) (.var 3)) (.app (.app (.app (.app (.app (.app (.app (.var 10) (.var 9)) (.var 8)) (.var 7)) (.var 4)) (.var 3)) (.var 2)) (.var 1)))))))) (.pi (.var 5) (.pi (.app (.app (.app (.app (.var 9) (.var 6)) (.var 5)) (.var 4)) (.var 0)) (.app (.app (.var 4) (.var 1)) (.var 0)))))))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.srt .type))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.app (.app (.app (.app (.var 3) (.var 2)) (.var 1)) (.var 0)) (.var 0))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.pi (.var 3) (.pi (.app (.app (.app (.app (.var 6) (.var 4)) (.var 3)) (.var 2)) (.var 1)) (.pi (.app (.app (.var 4) (.var 2)) (.var 1)) (.app (.app (.app (.app (.var 8) (.var 6)) (.var 5)) (.var 4)) (.var 2))))))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.pi (.var 2) (.pi (.app (.app (.app (.app (.var 6) (.var 3)) (.var 2)) (.var 1)) (.var 0)) (.srt .type))) (.pi (.app (.app (.var 0) (.var 1)) (.app (.app (.app (.var 5) (.var 3)) (.var 2)) (.var 1))) (.pi (.pi (.var 4) (.pi (.var 5) (.pi (.app (.app (.app (.app (.var 9) (.var 6)) (.var 5)) (.var 4)) (.var 1)) (.pi (.app (.app (.var 6) (.var 2)) (.var 1)) (.pi (.app (.app (.var 5) (.var 3)) (.var 1)) (.app (.app (.var 6) (.var 3)) (.app (.app (.app (.app (.app (.app (.app (.var 10) (.var 9)) (.var 8)) (.var 7)) (.var 4)) (.var 3)) (.var 2)) (.var 1)))))))) (.pi (.var 5) (.pi (.app (.app (.app (.app (.var 9) (.var 6)) (.var 5)) (.var 4)) (.var 0)) (.app (.app (.var 4) (.var 1)) (.var 0)))))))))) (.lam (.srt .type) (.lam (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.lam (.var 1) (.lam (.var 2) (.lam (.var 3) (.lam (.app (.app (.app (.app (.var 12) (.var 4)) (.var 3)) (.var 2)) (.var 1)) (.lam (.app (.app (.app (.app (.var 9) (.var 5)) (.var 4)) (.var 2)) (.var 1)) (.app (.app (.app (.app (.app (.app (.app (.app (.var 7) (.var 6)) (.lam (.var 6) (.lam (.var 7) (.app (.app (.var 7) (.var 1)) (.var 0))))) (.var 3)) (.lam (.var 6) (.lam (.app (.app (.app (.app (.var 11) (.var 7)) (.lam (.var 7) (.lam (.var 8) (.app (.app (.var 8) (.var 1)) (.var 0))))) (.var 4)) (.var 0)) (.app (.app (.app (.app (.var 16) (.var 8)) (.lam (.var 8) (.lam (.var 9) (.app (.app (.var 9) (.var 1)) (.var 0))))) (.var 6)) (.var 1))))) (.var 1)) (.lam (.var 6) (.lam (.var 7) (.lam (.app (.app (.app (.app (.var 12) (.var 8)) (.lam (.var 8) (.lam (.var 9) (.app (.app (.var 9) (.var 1)) (.var 0))))) (.var 5)) (.var 1)) (.lam (.app (.app (.lam (.var 9) (.lam (.var 10) (.app (.app (.var 10) (.var 1)) (.var 0)))) (.var 2)) (.var 1)) (.lam (.app (.app (.lam (.var 10) (.lam (.app (.app (.app (.app (.var 15) (.var 11)) (.lam (.var 11) (.lam (.var 12) (.app (.app (.var 12) (.var 1)) (.var 0))))) (.var 8)) (.var 0)) (.app (.app (.app (.app (.var 20) (.var 12)) (.lam (.var 12) (.lam (.var 13) (.app (.app (.var 13) (.var 1)) (.var 0))))) (.var 10)) (.var 1)))) (.var 3)) (.var 1)) (.app (.app (.app (.app (.app (.app (.app (.var 17) (.var 11)) (.lam (.var 11) (.lam (.var 12) (.app (.app (.var 12) (.var 1)) (.var 0))))) (.var 9)) (.var 4)) (.var 3)) (.var 0)) (.var 1)))))))) (.var 2)) (.var 0))))))))))))))))

def normalizedGoal_TransGen_trans_left : LF.Term :=
  .pi (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.srt .type))))) (.pi (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.pi (.app (.app (.var 2) (.var 1)) (.var 0)) (.app (.app (.app (.app (.var 5) (.var 4)) (.var 3)) (.var 2)) (.var 1))))))) (.pi (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.pi (.var 3) (.pi (.app (.app (.app (.app (.var 6) (.var 4)) (.var 3)) (.var 2)) (.var 1)) (.pi (.app (.app (.var 4) (.var 2)) (.var 1)) (.app (.app (.app (.app (.var 8) (.var 6)) (.var 5)) (.var 4)) (.var 2))))))))) (.pi (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.pi (.var 2) (.pi (.app (.app (.app (.app (.var 6) (.var 3)) (.var 2)) (.var 1)) (.var 0)) (.srt .type))) (.pi (.pi (.var 3) (.pi (.app (.app (.var 3) (.var 2)) (.var 0)) (.app (.app (.var 2) (.var 1)) (.app (.app (.app (.app (.app (.var 7) (.var 5)) (.var 4)) (.var 3)) (.var 1)) (.var 0))))) (.pi (.pi (.var 4) (.pi (.var 5) (.pi (.app (.app (.app (.app (.var 9) (.var 6)) (.var 5)) (.var 4)) (.var 1)) (.pi (.app (.app (.var 6) (.var 2)) (.var 1)) (.pi (.app (.app (.var 5) (.var 3)) (.var 1)) (.app (.app (.var 6) (.var 3)) (.app (.app (.app (.app (.app (.app (.app (.var 10) (.var 9)) (.var 8)) (.var 7)) (.var 4)) (.var 3)) (.var 2)) (.var 1)))))))) (.pi (.var 5) (.pi (.app (.app (.app (.app (.var 9) (.var 6)) (.var 5)) (.var 4)) (.var 0)) (.app (.app (.var 4) (.var 1)) (.var 0)))))))))) (.pi (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.srt .type))))) (.pi (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.app (.app (.app (.app (.var 3) (.var 2)) (.var 1)) (.var 0)) (.var 0))))) (.pi (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.pi (.var 3) (.pi (.app (.app (.app (.app (.var 6) (.var 4)) (.var 3)) (.var 2)) (.var 1)) (.pi (.app (.app (.var 4) (.var 2)) (.var 1)) (.app (.app (.app (.app (.var 8) (.var 6)) (.var 5)) (.var 4)) (.var 2))))))))) (.pi (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.pi (.var 2) (.pi (.app (.app (.app (.app (.var 6) (.var 3)) (.var 2)) (.var 1)) (.var 0)) (.srt .type))) (.pi (.app (.app (.var 0) (.var 1)) (.app (.app (.app (.var 5) (.var 3)) (.var 2)) (.var 1))) (.pi (.pi (.var 4) (.pi (.var 5) (.pi (.app (.app (.app (.app (.var 9) (.var 6)) (.var 5)) (.var 4)) (.var 1)) (.pi (.app (.app (.var 6) (.var 2)) (.var 1)) (.pi (.app (.app (.var 5) (.var 3)) (.var 1)) (.app (.app (.var 6) (.var 3)) (.app (.app (.app (.app (.app (.app (.app (.var 10) (.var 9)) (.var 8)) (.var 7)) (.var 4)) (.var 3)) (.var 2)) (.var 1)))))))) (.pi (.var 5) (.pi (.app (.app (.app (.app (.var 9) (.var 6)) (.var 5)) (.var 4)) (.var 0)) (.app (.app (.var 4) (.var 1)) (.var 0)))))))))) (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.pi (.var 3) (.pi (.app (.app (.app (.app (.var 12) (.var 4)) (.var 3)) (.var 2)) (.var 1)) (.pi (.app (.app (.app (.app (.var 9) (.var 5)) (.var 4)) (.var 2)) (.var 1)) (.app (.app (.app (.app (.var 14) (.var 6)) (.var 5)) (.var 4)) (.var 2))))))))))))))))

def normalizedCandidate_TransGen_trans_left : LF.Term :=
  .lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.srt .type))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.pi (.app (.app (.var 2) (.var 1)) (.var 0)) (.app (.app (.app (.app (.var 5) (.var 4)) (.var 3)) (.var 2)) (.var 1))))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.pi (.var 3) (.pi (.app (.app (.app (.app (.var 6) (.var 4)) (.var 3)) (.var 2)) (.var 1)) (.pi (.app (.app (.var 4) (.var 2)) (.var 1)) (.app (.app (.app (.app (.var 8) (.var 6)) (.var 5)) (.var 4)) (.var 2))))))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.pi (.var 2) (.pi (.app (.app (.app (.app (.var 6) (.var 3)) (.var 2)) (.var 1)) (.var 0)) (.srt .type))) (.pi (.pi (.var 3) (.pi (.app (.app (.var 3) (.var 2)) (.var 0)) (.app (.app (.var 2) (.var 1)) (.app (.app (.app (.app (.app (.var 7) (.var 5)) (.var 4)) (.var 3)) (.var 1)) (.var 0))))) (.pi (.pi (.var 4) (.pi (.var 5) (.pi (.app (.app (.app (.app (.var 9) (.var 6)) (.var 5)) (.var 4)) (.var 1)) (.pi (.app (.app (.var 6) (.var 2)) (.var 1)) (.pi (.app (.app (.var 5) (.var 3)) (.var 1)) (.app (.app (.var 6) (.var 3)) (.app (.app (.app (.app (.app (.app (.app (.var 10) (.var 9)) (.var 8)) (.var 7)) (.var 4)) (.var 3)) (.var 2)) (.var 1)))))))) (.pi (.var 5) (.pi (.app (.app (.app (.app (.var 9) (.var 6)) (.var 5)) (.var 4)) (.var 0)) (.app (.app (.var 4) (.var 1)) (.var 0)))))))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.srt .type))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.app (.app (.app (.app (.var 3) (.var 2)) (.var 1)) (.var 0)) (.var 0))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.pi (.var 3) (.pi (.app (.app (.app (.app (.var 6) (.var 4)) (.var 3)) (.var 2)) (.var 1)) (.pi (.app (.app (.var 4) (.var 2)) (.var 1)) (.app (.app (.app (.app (.var 8) (.var 6)) (.var 5)) (.var 4)) (.var 2))))))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.pi (.var 2) (.pi (.app (.app (.app (.app (.var 6) (.var 3)) (.var 2)) (.var 1)) (.var 0)) (.srt .type))) (.pi (.app (.app (.var 0) (.var 1)) (.app (.app (.app (.var 5) (.var 3)) (.var 2)) (.var 1))) (.pi (.pi (.var 4) (.pi (.var 5) (.pi (.app (.app (.app (.app (.var 9) (.var 6)) (.var 5)) (.var 4)) (.var 1)) (.pi (.app (.app (.var 6) (.var 2)) (.var 1)) (.pi (.app (.app (.var 5) (.var 3)) (.var 1)) (.app (.app (.var 6) (.var 3)) (.app (.app (.app (.app (.app (.app (.app (.var 10) (.var 9)) (.var 8)) (.var 7)) (.var 4)) (.var 3)) (.var 2)) (.var 1)))))))) (.pi (.var 5) (.pi (.app (.app (.app (.app (.var 9) (.var 6)) (.var 5)) (.var 4)) (.var 0)) (.app (.app (.var 4) (.var 1)) (.var 0)))))))))) (.lam (.srt .type) (.lam (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.lam (.var 1) (.lam (.var 2) (.lam (.var 3) (.lam (.app (.app (.app (.app (.var 12) (.var 4)) (.var 3)) (.var 2)) (.var 1)) (.app (.app (.app (.app (.app (.app (.app (.var 6) (.var 5)) (.var 4)) (.var 2)) (.lam (.var 5) (.lam (.app (.app (.app (.app (.var 10) (.var 6)) (.var 5)) (.var 3)) (.var 0)) (.app (.app (.app (.app (.var 15) (.var 7)) (.var 6)) (.var 5)) (.var 1))))) (.var 0)) (.lam (.var 5) (.lam (.var 6) (.lam (.app (.app (.app (.app (.var 11) (.var 7)) (.var 6)) (.var 4)) (.var 1)) (.lam (.app (.app (.var 7) (.var 2)) (.var 1)) (.lam (.app (.app (.app (.app (.var 17) (.var 9)) (.var 8)) (.var 7)) (.var 3)) (.app (.app (.app (.app (.app (.app (.app (.var 16) (.var 10)) (.var 9)) (.var 8)) (.var 4)) (.var 3)) (.var 0)) (.var 1)))))))) (.var 1)))))))))))))))

theorem normalizedGoal_TransGen_trans_left_eq :
    normalizedGoal_TransGen_trans_left =
      LFBetaEta.normalForm [] PureBetaEta.normalizationFuel
        (encodeExpr PureDTTBench31.goal_Relation_TransGen_trans_left) := by
  decide

theorem normalizedCandidate_TransGen_trans_left_eq :
    normalizedCandidate_TransGen_trans_left =
      LFBetaEta.normalForm [] PureBetaEta.normalizationFuel
        candidate_TransGen_trans_left := by
  decide

def replay_TransGen_trans_left : ReplayCase :=
  { name := "TransGen_trans_left", actionCount := 26, traceSha256 := "02f07604a618da2b260dd5f7a631d6913d4202e0a629a368438415869cd98043", referenceTermSha256 := "27da2cb1dd405bbed0de5b88ae37c317a24bb51044326dc6e40ac7cd025f0006"
    goal := encodeExpr PureDTTBench31.goal_Relation_TransGen_trans_left
    candidate := candidate_TransGen_trans_left }

theorem replay_TransGen_trans_left_accepted : accepts replay_TransGen_trans_left = true := by
  decide

theorem replay_TransGen_trans_left_sound :
    LFConversionProfileChecker.Deriv LFProfile.indexed [] []
      candidate_TransGen_trans_left (encodeExpr PureDTTBench31.goal_Relation_TransGen_trans_left) :=
  LFConversionProfileChecker.S1 replay_TransGen_trans_left_accepted

def candidate_TransGen_to_self : LF.Term :=
  .lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.srt .type))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.pi (.app (.app (.var 2) (.var 1)) (.var 0)) (.app (.app (.app (.app (.var 5) (.var 4)) (.var 3)) (.var 2)) (.var 1))))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.pi (.var 3) (.pi (.app (.app (.app (.app (.var 6) (.var 4)) (.var 3)) (.var 2)) (.var 1)) (.pi (.app (.app (.var 4) (.var 2)) (.var 1)) (.app (.app (.app (.app (.var 8) (.var 6)) (.var 5)) (.var 4)) (.var 2))))))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.pi (.var 2) (.pi (.app (.app (.app (.app (.var 6) (.var 3)) (.var 2)) (.var 1)) (.var 0)) (.srt .type))) (.pi (.pi (.var 3) (.pi (.app (.app (.var 3) (.var 2)) (.var 0)) (.app (.app (.var 2) (.var 1)) (.app (.app (.app (.app (.app (.var 7) (.var 5)) (.var 4)) (.var 3)) (.var 1)) (.var 0))))) (.pi (.pi (.var 4) (.pi (.var 5) (.pi (.app (.app (.app (.app (.var 9) (.var 6)) (.var 5)) (.var 4)) (.var 1)) (.pi (.app (.app (.var 6) (.var 2)) (.var 1)) (.pi (.app (.app (.var 5) (.var 3)) (.var 1)) (.app (.app (.var 6) (.var 3)) (.app (.app (.app (.app (.app (.app (.app (.var 10) (.var 9)) (.var 8)) (.var 7)) (.var 4)) (.var 3)) (.var 2)) (.var 1)))))))) (.pi (.var 5) (.pi (.app (.app (.app (.app (.var 9) (.var 6)) (.var 5)) (.var 4)) (.var 0)) (.app (.app (.var 4) (.var 1)) (.var 0)))))))))) (.lam (.srt .type) (.lam (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.lam (.pi (.var 1) (.pi (.var 2) (.pi (.var 3) (.pi (.app (.app (.var 3) (.var 2)) (.var 1)) (.pi (.app (.app (.var 4) (.var 2)) (.var 1)) (.app (.app (.var 5) (.var 4)) (.var 2))))))) (.lam (.var 2) (.lam (.var 3) (.lam (.app (.app (.app (.app (.var 8) (.var 4)) (.var 3)) (.var 1)) (.var 0)) (.app (.app (.app (.app (.app (.app (.app (.app (.var 6) (.var 5)) (.lam (.var 5) (.lam (.var 6) (.app (.app (.var 6) (.var 1)) (.var 0))))) (.var 2)) (.lam (.var 5) (.lam (.app (.app (.app (.app (.var 10) (.var 6)) (.lam (.var 6) (.lam (.var 7) (.app (.app (.var 7) (.var 1)) (.var 0))))) (.var 3)) (.var 0)) (.app (.app (.var 6) (.var 4)) (.var 1))))) (.lam (.var 5) (.lam (.app (.app (.lam (.var 6) (.lam (.var 7) (.app (.app (.var 7) (.var 1)) (.var 0)))) (.var 3)) (.var 0)) (.var 0)))) (.lam (.var 5) (.lam (.var 6) (.lam (.app (.app (.app (.app (.var 11) (.var 7)) (.lam (.var 7) (.lam (.var 8) (.app (.app (.var 8) (.var 1)) (.var 0))))) (.var 4)) (.var 1)) (.lam (.app (.app (.lam (.var 8) (.lam (.var 9) (.app (.app (.var 9) (.var 1)) (.var 0)))) (.var 2)) (.var 1)) (.lam (.app (.app (.lam (.var 9) (.lam (.app (.app (.app (.app (.var 14) (.var 10)) (.lam (.var 10) (.lam (.var 11) (.app (.app (.var 11) (.var 1)) (.var 0))))) (.var 7)) (.var 0)) (.app (.app (.var 10) (.var 8)) (.var 1)))) (.var 3)) (.var 1)) (.app (.app (.app (.app (.app (.var 8) (.var 7)) (.var 4)) (.var 3)) (.var 0)) (.var 1)))))))) (.var 1)) (.var 0)))))))))))

def normalizedGoal_TransGen_to_self : LF.Term :=
  .pi (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.srt .type))))) (.pi (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.pi (.app (.app (.var 2) (.var 1)) (.var 0)) (.app (.app (.app (.app (.var 5) (.var 4)) (.var 3)) (.var 2)) (.var 1))))))) (.pi (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.pi (.var 3) (.pi (.app (.app (.app (.app (.var 6) (.var 4)) (.var 3)) (.var 2)) (.var 1)) (.pi (.app (.app (.var 4) (.var 2)) (.var 1)) (.app (.app (.app (.app (.var 8) (.var 6)) (.var 5)) (.var 4)) (.var 2))))))))) (.pi (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.pi (.var 2) (.pi (.app (.app (.app (.app (.var 6) (.var 3)) (.var 2)) (.var 1)) (.var 0)) (.srt .type))) (.pi (.pi (.var 3) (.pi (.app (.app (.var 3) (.var 2)) (.var 0)) (.app (.app (.var 2) (.var 1)) (.app (.app (.app (.app (.app (.var 7) (.var 5)) (.var 4)) (.var 3)) (.var 1)) (.var 0))))) (.pi (.pi (.var 4) (.pi (.var 5) (.pi (.app (.app (.app (.app (.var 9) (.var 6)) (.var 5)) (.var 4)) (.var 1)) (.pi (.app (.app (.var 6) (.var 2)) (.var 1)) (.pi (.app (.app (.var 5) (.var 3)) (.var 1)) (.app (.app (.var 6) (.var 3)) (.app (.app (.app (.app (.app (.app (.app (.var 10) (.var 9)) (.var 8)) (.var 7)) (.var 4)) (.var 3)) (.var 2)) (.var 1)))))))) (.pi (.var 5) (.pi (.app (.app (.app (.app (.var 9) (.var 6)) (.var 5)) (.var 4)) (.var 0)) (.app (.app (.var 4) (.var 1)) (.var 0)))))))))) (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.pi (.var 1) (.pi (.var 2) (.pi (.var 3) (.pi (.app (.app (.var 3) (.var 2)) (.var 1)) (.pi (.app (.app (.var 4) (.var 2)) (.var 1)) (.app (.app (.var 5) (.var 4)) (.var 2))))))) (.pi (.var 2) (.pi (.var 3) (.pi (.app (.app (.app (.app (.var 8) (.var 4)) (.var 3)) (.var 1)) (.var 0)) (.app (.app (.var 4) (.var 2)) (.var 1)))))))))))

def normalizedCandidate_TransGen_to_self : LF.Term :=
  .lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.srt .type))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.pi (.app (.app (.var 2) (.var 1)) (.var 0)) (.app (.app (.app (.app (.var 5) (.var 4)) (.var 3)) (.var 2)) (.var 1))))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.pi (.var 3) (.pi (.app (.app (.app (.app (.var 6) (.var 4)) (.var 3)) (.var 2)) (.var 1)) (.pi (.app (.app (.var 4) (.var 2)) (.var 1)) (.app (.app (.app (.app (.var 8) (.var 6)) (.var 5)) (.var 4)) (.var 2))))))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.pi (.var 2) (.pi (.app (.app (.app (.app (.var 6) (.var 3)) (.var 2)) (.var 1)) (.var 0)) (.srt .type))) (.pi (.pi (.var 3) (.pi (.app (.app (.var 3) (.var 2)) (.var 0)) (.app (.app (.var 2) (.var 1)) (.app (.app (.app (.app (.app (.var 7) (.var 5)) (.var 4)) (.var 3)) (.var 1)) (.var 0))))) (.pi (.pi (.var 4) (.pi (.var 5) (.pi (.app (.app (.app (.app (.var 9) (.var 6)) (.var 5)) (.var 4)) (.var 1)) (.pi (.app (.app (.var 6) (.var 2)) (.var 1)) (.pi (.app (.app (.var 5) (.var 3)) (.var 1)) (.app (.app (.var 6) (.var 3)) (.app (.app (.app (.app (.app (.app (.app (.var 10) (.var 9)) (.var 8)) (.var 7)) (.var 4)) (.var 3)) (.var 2)) (.var 1)))))))) (.pi (.var 5) (.pi (.app (.app (.app (.app (.var 9) (.var 6)) (.var 5)) (.var 4)) (.var 0)) (.app (.app (.var 4) (.var 1)) (.var 0)))))))))) (.lam (.srt .type) (.lam (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.lam (.pi (.var 1) (.pi (.var 2) (.pi (.var 3) (.pi (.app (.app (.var 3) (.var 2)) (.var 1)) (.pi (.app (.app (.var 4) (.var 2)) (.var 1)) (.app (.app (.var 5) (.var 4)) (.var 2))))))) (.lam (.var 2) (.app (.app (.app (.app (.app (.app (.var 4) (.var 3)) (.var 2)) (.var 0)) (.lam (.var 3) (.lam (.app (.app (.app (.app (.var 8) (.var 4)) (.var 3)) (.var 1)) (.var 0)) (.app (.app (.var 4) (.var 2)) (.var 1))))) (.lam (.var 3) (.lam (.app (.app (.var 3) (.var 1)) (.var 0)) (.var 0)))) (.lam (.var 3) (.lam (.var 4) (.lam (.app (.app (.app (.app (.var 9) (.var 5)) (.var 4)) (.var 2)) (.var 1)) (.lam (.app (.app (.var 5) (.var 2)) (.var 1)) (.lam (.app (.app (.var 6) (.var 4)) (.var 3)) (.app (.app (.app (.app (.app (.var 6) (.var 5)) (.var 4)) (.var 3)) (.var 0)) (.var 1)))))))))))))))

theorem normalizedGoal_TransGen_to_self_eq :
    normalizedGoal_TransGen_to_self =
      LFBetaEta.normalForm [] PureBetaEta.normalizationFuel
        (encodeExpr PureDTTBench31.goal_Relation_TransGen_to_self) := by
  decide

theorem normalizedCandidate_TransGen_to_self_eq :
    normalizedCandidate_TransGen_to_self =
      LFBetaEta.normalForm [] PureBetaEta.normalizationFuel
        candidate_TransGen_to_self := by
  decide

def replay_TransGen_to_self : ReplayCase :=
  { name := "TransGen_to_self", actionCount := 18, traceSha256 := "64a1af6a004a8cde81d23ebae039de08a105b99d6f9575ff1ba011db66200034", referenceTermSha256 := "2e2f9d77ccfdfe590d71839515f7124762e30e41e1a3f7f2710c6fb573a1740c"
    goal := encodeExpr PureDTTBench31.goal_Relation_TransGen_to_self
    candidate := candidate_TransGen_to_self }

theorem replay_TransGen_to_self_accepted : accepts replay_TransGen_to_self = true := by
  decide

theorem replay_TransGen_to_self_sound :
    LFConversionProfileChecker.Deriv LFProfile.indexed [] []
      candidate_TransGen_to_self (encodeExpr PureDTTBench31.goal_Relation_TransGen_to_self) :=
  LFConversionProfileChecker.S1 replay_TransGen_to_self_accepted

def candidate_TransGen_lift : LF.Term :=
  .lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.srt .type))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.pi (.app (.app (.var 2) (.var 1)) (.var 0)) (.app (.app (.app (.app (.var 5) (.var 4)) (.var 3)) (.var 2)) (.var 1))))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.pi (.var 3) (.pi (.app (.app (.app (.app (.var 6) (.var 4)) (.var 3)) (.var 2)) (.var 1)) (.pi (.app (.app (.var 4) (.var 2)) (.var 1)) (.app (.app (.app (.app (.var 8) (.var 6)) (.var 5)) (.var 4)) (.var 2))))))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.pi (.var 2) (.pi (.app (.app (.app (.app (.var 6) (.var 3)) (.var 2)) (.var 1)) (.var 0)) (.srt .type))) (.pi (.pi (.var 3) (.pi (.app (.app (.var 3) (.var 2)) (.var 0)) (.app (.app (.var 2) (.var 1)) (.app (.app (.app (.app (.app (.var 7) (.var 5)) (.var 4)) (.var 3)) (.var 1)) (.var 0))))) (.pi (.pi (.var 4) (.pi (.var 5) (.pi (.app (.app (.app (.app (.var 9) (.var 6)) (.var 5)) (.var 4)) (.var 1)) (.pi (.app (.app (.var 6) (.var 2)) (.var 1)) (.pi (.app (.app (.var 5) (.var 3)) (.var 1)) (.app (.app (.var 6) (.var 3)) (.app (.app (.app (.app (.app (.app (.app (.var 10) (.var 9)) (.var 8)) (.var 7)) (.var 4)) (.var 3)) (.var 2)) (.var 1)))))))) (.pi (.var 5) (.pi (.app (.app (.app (.app (.var 9) (.var 6)) (.var 5)) (.var 4)) (.var 0)) (.app (.app (.var 4) (.var 1)) (.var 0)))))))))) (.lam (.srt .type) (.lam (.srt .type) (.lam (.pi (.var 1) (.pi (.var 2) (.srt .type))) (.lam (.pi (.var 1) (.pi (.var 2) (.srt .type))) (.lam (.var 3) (.lam (.var 4) (.lam (.pi (.var 5) (.var 5)) (.lam (.pi (.var 6) (.pi (.var 7) (.pi (.app (.app (.var 6) (.var 1)) (.var 0)) (.app (.app (.var 6) (.app (.var 3) (.var 2))) (.app (.var 3) (.var 1)))))) (.lam (.app (.app (.app (.app (.var 11) (.var 7)) (.var 5)) (.var 3)) (.var 2)) (.app (.app (.app (.app (.app (.app (.app (.app (.var 9) (.var 8)) (.lam (.var 8) (.lam (.var 9) (.app (.app (.var 8) (.var 1)) (.var 0))))) (.var 4)) (.lam (.var 8) (.lam (.app (.app (.app (.app (.var 13) (.var 9)) (.lam (.var 9) (.lam (.var 10) (.app (.app (.var 9) (.var 1)) (.var 0))))) (.var 5)) (.var 0)) (.app (.app (.app (.app (.var 14) (.var 9)) (.lam (.var 9) (.lam (.var 10) (.app (.app (.var 9) (.var 1)) (.var 0))))) (.app (.var 4) (.var 6))) (.app (.var 4) (.var 1)))))) (.lam (.var 8) (.lam (.app (.app (.lam (.var 9) (.lam (.var 10) (.app (.app (.var 9) (.var 1)) (.var 0)))) (.var 5)) (.var 0)) (.app (.app (.app (.app (.app (.var 13) (.var 9)) (.lam (.var 9) (.lam (.var 10) (.app (.app (.var 9) (.var 1)) (.var 0))))) (.app (.var 4) (.var 6))) (.app (.var 4) (.var 1))) (.app (.app (.app (.var 3) (.var 6)) (.var 1)) (.var 0)))))) (.lam (.var 8) (.lam (.var 9) (.lam (.app (.app (.app (.app (.var 14) (.var 10)) (.lam (.var 10) (.lam (.var 11) (.app (.app (.var 10) (.var 1)) (.var 0))))) (.var 6)) (.var 1)) (.lam (.app (.app (.lam (.var 11) (.lam (.var 12) (.app (.app (.var 11) (.var 1)) (.var 0)))) (.var 2)) (.var 1)) (.lam (.app (.app (.lam (.var 12) (.lam (.app (.app (.app (.app (.var 17) (.var 13)) (.lam (.var 13) (.lam (.var 14) (.app (.app (.var 13) (.var 1)) (.var 0))))) (.var 9)) (.var 0)) (.app (.app (.app (.app (.var 18) (.var 13)) (.lam (.var 13) (.lam (.var 14) (.app (.app (.var 13) (.var 1)) (.var 0))))) (.app (.var 8) (.var 10))) (.app (.var 8) (.var 1))))) (.var 3)) (.var 1)) (.app (.app (.app (.app (.app (.app (.app (.var 15) (.var 12)) (.lam (.var 12) (.lam (.var 13) (.app (.app (.var 12) (.var 1)) (.var 0))))) (.app (.var 7) (.var 9))) (.app (.var 7) (.var 4))) (.app (.var 7) (.var 3))) (.var 0)) (.app (.app (.app (.var 6) (.var 4)) (.var 3)) (.var 1))))))))) (.var 3)) (.var 0))))))))))))))

def normalizedGoal_TransGen_lift : LF.Term :=
  .pi (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.srt .type))))) (.pi (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.pi (.app (.app (.var 2) (.var 1)) (.var 0)) (.app (.app (.app (.app (.var 5) (.var 4)) (.var 3)) (.var 2)) (.var 1))))))) (.pi (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.pi (.var 3) (.pi (.app (.app (.app (.app (.var 6) (.var 4)) (.var 3)) (.var 2)) (.var 1)) (.pi (.app (.app (.var 4) (.var 2)) (.var 1)) (.app (.app (.app (.app (.var 8) (.var 6)) (.var 5)) (.var 4)) (.var 2))))))))) (.pi (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.pi (.var 2) (.pi (.app (.app (.app (.app (.var 6) (.var 3)) (.var 2)) (.var 1)) (.var 0)) (.srt .type))) (.pi (.pi (.var 3) (.pi (.app (.app (.var 3) (.var 2)) (.var 0)) (.app (.app (.var 2) (.var 1)) (.app (.app (.app (.app (.app (.var 7) (.var 5)) (.var 4)) (.var 3)) (.var 1)) (.var 0))))) (.pi (.pi (.var 4) (.pi (.var 5) (.pi (.app (.app (.app (.app (.var 9) (.var 6)) (.var 5)) (.var 4)) (.var 1)) (.pi (.app (.app (.var 6) (.var 2)) (.var 1)) (.pi (.app (.app (.var 5) (.var 3)) (.var 1)) (.app (.app (.var 6) (.var 3)) (.app (.app (.app (.app (.app (.app (.app (.var 10) (.var 9)) (.var 8)) (.var 7)) (.var 4)) (.var 3)) (.var 2)) (.var 1)))))))) (.pi (.var 5) (.pi (.app (.app (.app (.app (.var 9) (.var 6)) (.var 5)) (.var 4)) (.var 0)) (.app (.app (.var 4) (.var 1)) (.var 0)))))))))) (.pi (.srt .type) (.pi (.srt .type) (.pi (.pi (.var 1) (.pi (.var 2) (.srt .type))) (.pi (.pi (.var 1) (.pi (.var 2) (.srt .type))) (.pi (.var 3) (.pi (.var 4) (.pi (.pi (.var 5) (.var 5)) (.pi (.pi (.var 6) (.pi (.var 7) (.pi (.app (.app (.var 6) (.var 1)) (.var 0)) (.app (.app (.var 6) (.app (.var 3) (.var 2))) (.app (.var 3) (.var 1)))))) (.pi (.app (.app (.app (.app (.var 11) (.var 7)) (.var 5)) (.var 3)) (.var 2)) (.app (.app (.app (.app (.var 12) (.var 7)) (.var 5)) (.app (.var 2) (.var 4))) (.app (.var 2) (.var 3)))))))))))))))

def normalizedCandidate_TransGen_lift : LF.Term :=
  .lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.srt .type))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.pi (.app (.app (.var 2) (.var 1)) (.var 0)) (.app (.app (.app (.app (.var 5) (.var 4)) (.var 3)) (.var 2)) (.var 1))))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.pi (.var 3) (.pi (.app (.app (.app (.app (.var 6) (.var 4)) (.var 3)) (.var 2)) (.var 1)) (.pi (.app (.app (.var 4) (.var 2)) (.var 1)) (.app (.app (.app (.app (.var 8) (.var 6)) (.var 5)) (.var 4)) (.var 2))))))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.pi (.var 2) (.pi (.app (.app (.app (.app (.var 6) (.var 3)) (.var 2)) (.var 1)) (.var 0)) (.srt .type))) (.pi (.pi (.var 3) (.pi (.app (.app (.var 3) (.var 2)) (.var 0)) (.app (.app (.var 2) (.var 1)) (.app (.app (.app (.app (.app (.var 7) (.var 5)) (.var 4)) (.var 3)) (.var 1)) (.var 0))))) (.pi (.pi (.var 4) (.pi (.var 5) (.pi (.app (.app (.app (.app (.var 9) (.var 6)) (.var 5)) (.var 4)) (.var 1)) (.pi (.app (.app (.var 6) (.var 2)) (.var 1)) (.pi (.app (.app (.var 5) (.var 3)) (.var 1)) (.app (.app (.var 6) (.var 3)) (.app (.app (.app (.app (.app (.app (.app (.var 10) (.var 9)) (.var 8)) (.var 7)) (.var 4)) (.var 3)) (.var 2)) (.var 1)))))))) (.pi (.var 5) (.pi (.app (.app (.app (.app (.var 9) (.var 6)) (.var 5)) (.var 4)) (.var 0)) (.app (.app (.var 4) (.var 1)) (.var 0)))))))))) (.lam (.srt .type) (.lam (.srt .type) (.lam (.pi (.var 1) (.pi (.var 2) (.srt .type))) (.lam (.pi (.var 1) (.pi (.var 2) (.srt .type))) (.lam (.var 3) (.lam (.var 4) (.lam (.pi (.var 5) (.var 5)) (.lam (.pi (.var 6) (.pi (.var 7) (.pi (.app (.app (.var 6) (.var 1)) (.var 0)) (.app (.app (.var 6) (.app (.var 3) (.var 2))) (.app (.var 3) (.var 1)))))) (.app (.app (.app (.app (.app (.app (.app (.var 8) (.var 7)) (.var 5)) (.var 3)) (.lam (.var 7) (.lam (.app (.app (.app (.app (.var 12) (.var 8)) (.var 6)) (.var 4)) (.var 0)) (.app (.app (.app (.app (.var 13) (.var 8)) (.var 6)) (.app (.var 3) (.var 5))) (.app (.var 3) (.var 1)))))) (.lam (.var 7) (.lam (.app (.app (.var 6) (.var 4)) (.var 0)) (.app (.app (.app (.app (.app (.var 12) (.var 8)) (.var 6)) (.app (.var 3) (.var 5))) (.app (.var 3) (.var 1))) (.app (.app (.app (.var 2) (.var 5)) (.var 1)) (.var 0)))))) (.lam (.var 7) (.lam (.var 8) (.lam (.app (.app (.app (.app (.var 13) (.var 9)) (.var 7)) (.var 5)) (.var 1)) (.lam (.app (.app (.var 8) (.var 2)) (.var 1)) (.lam (.app (.app (.app (.app (.var 15) (.var 10)) (.var 8)) (.app (.var 5) (.var 7))) (.app (.var 5) (.var 3))) (.app (.app (.app (.app (.app (.app (.app (.var 14) (.var 11)) (.var 9)) (.app (.var 6) (.var 8))) (.app (.var 6) (.var 4))) (.app (.var 6) (.var 3))) (.var 0)) (.app (.app (.app (.var 5) (.var 4)) (.var 3)) (.var 1))))))))) (.var 2)))))))))))))

theorem normalizedGoal_TransGen_lift_eq :
    normalizedGoal_TransGen_lift =
      LFBetaEta.normalForm [] PureBetaEta.normalizationFuel
        (encodeExpr PureDTTBench31.goal_Relation_TransGen_lift) := by
  decide

theorem normalizedCandidate_TransGen_lift_eq :
    normalizedCandidate_TransGen_lift =
      LFBetaEta.normalForm [] PureBetaEta.normalizationFuel
        candidate_TransGen_lift := by
  decide

def replay_TransGen_lift : ReplayCase :=
  { name := "TransGen_lift", actionCount := 46, traceSha256 := "cf4cb3871232ddbc989b0380bf831d6c1ae8a3a15c380e520b4ad3ed5ab41e7a", referenceTermSha256 := "7acc78f916b1770d9ff858d0a3cdb1add60534304ee9f9110bf8451c7e15f20c"
    goal := encodeExpr PureDTTBench31.goal_Relation_TransGen_lift
    candidate := candidate_TransGen_lift }

theorem replay_TransGen_lift_accepted : accepts replay_TransGen_lift = true := by
  decide

theorem replay_TransGen_lift_sound :
    LFConversionProfileChecker.Deriv LFProfile.indexed [] []
      candidate_TransGen_lift (encodeExpr PureDTTBench31.goal_Relation_TransGen_lift) :=
  LFConversionProfileChecker.S1 replay_TransGen_lift_accepted

def candidate_TransGen_swap : LF.Term :=
  .lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.srt .type))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.pi (.app (.app (.var 2) (.var 1)) (.var 0)) (.app (.app (.app (.app (.var 5) (.var 4)) (.var 3)) (.var 2)) (.var 1))))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.pi (.var 3) (.pi (.app (.app (.app (.app (.var 6) (.var 4)) (.var 3)) (.var 2)) (.var 1)) (.pi (.app (.app (.var 4) (.var 2)) (.var 1)) (.app (.app (.app (.app (.var 8) (.var 6)) (.var 5)) (.var 4)) (.var 2))))))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.pi (.var 2) (.pi (.app (.app (.app (.app (.var 6) (.var 3)) (.var 2)) (.var 1)) (.var 0)) (.srt .type))) (.pi (.pi (.var 3) (.pi (.app (.app (.var 3) (.var 2)) (.var 0)) (.app (.app (.var 2) (.var 1)) (.app (.app (.app (.app (.app (.var 7) (.var 5)) (.var 4)) (.var 3)) (.var 1)) (.var 0))))) (.pi (.pi (.var 4) (.pi (.var 5) (.pi (.app (.app (.app (.app (.var 9) (.var 6)) (.var 5)) (.var 4)) (.var 1)) (.pi (.app (.app (.var 6) (.var 2)) (.var 1)) (.pi (.app (.app (.var 5) (.var 3)) (.var 1)) (.app (.app (.var 6) (.var 3)) (.app (.app (.app (.app (.app (.app (.app (.var 10) (.var 9)) (.var 8)) (.var 7)) (.var 4)) (.var 3)) (.var 2)) (.var 1)))))))) (.pi (.var 5) (.pi (.app (.app (.app (.app (.var 9) (.var 6)) (.var 5)) (.var 4)) (.var 0)) (.app (.app (.var 4) (.var 1)) (.var 0)))))))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.pi (.var 3) (.pi (.app (.app (.var 3) (.var 2)) (.var 1)) (.pi (.app (.app (.app (.app (.var 9) (.var 5)) (.var 4)) (.var 2)) (.var 1)) (.app (.app (.app (.app (.var 10) (.var 6)) (.var 5)) (.var 4)) (.var 2))))))))) (.lam (.srt .type) (.lam (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.lam (.var 1) (.lam (.var 2) (.lam (.app (.app (.app (.app (.var 8) (.var 3)) (.var 2)) (.var 0)) (.var 1)) (.app (.app (.app (.app (.app (.app (.app (.app (.var 6) (.var 4)) (.lam (.var 4) (.lam (.var 5) (.app (.app (.var 5) (.var 1)) (.var 0))))) (.var 1)) (.lam (.var 4) (.lam (.app (.app (.app (.app (.var 10) (.var 5)) (.lam (.var 5) (.lam (.var 6) (.app (.app (.var 6) (.var 1)) (.var 0))))) (.var 2)) (.var 0)) (.app (.app (.app (.app (.var 11) (.var 6)) (.lam (.var 6) (.lam (.var 7) (.app (.app (.var 7) (.var 0)) (.var 1))))) (.var 1)) (.var 3))))) (.lam (.var 4) (.lam (.app (.app (.lam (.var 5) (.lam (.var 6) (.app (.app (.var 6) (.var 1)) (.var 0)))) (.var 2)) (.var 0)) (.app (.app (.app (.app (.app (.var 10) (.var 6)) (.lam (.var 6) (.lam (.var 7) (.app (.app (.var 7) (.var 0)) (.var 1))))) (.var 1)) (.var 3)) (.var 0))))) (.lam (.var 4) (.lam (.var 5) (.lam (.app (.app (.app (.app (.var 11) (.var 6)) (.lam (.var 6) (.lam (.var 7) (.app (.app (.var 7) (.var 1)) (.var 0))))) (.var 3)) (.var 1)) (.lam (.app (.app (.lam (.var 7) (.lam (.var 8) (.app (.app (.var 8) (.var 1)) (.var 0)))) (.var 2)) (.var 1)) (.lam (.app (.app (.lam (.var 8) (.lam (.app (.app (.app (.app (.var 14) (.var 9)) (.lam (.var 9) (.lam (.var 10) (.app (.app (.var 10) (.var 1)) (.var 0))))) (.var 6)) (.var 0)) (.app (.app (.app (.app (.var 15) (.var 10)) (.lam (.var 10) (.lam (.var 11) (.app (.app (.var 11) (.var 0)) (.var 1))))) (.var 1)) (.var 7)))) (.var 3)) (.var 1)) (.app (.app (.app (.app (.app (.app (.app (.var 10) (.var 9)) (.lam (.var 9) (.lam (.var 10) (.app (.app (.var 10) (.var 0)) (.var 1))))) (.var 3)) (.var 4)) (.var 6)) (.var 1)) (.var 0)))))))) (.var 2)) (.var 0)))))))))))

def normalizedGoal_TransGen_swap : LF.Term :=
  .pi (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.srt .type))))) (.pi (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.pi (.app (.app (.var 2) (.var 1)) (.var 0)) (.app (.app (.app (.app (.var 5) (.var 4)) (.var 3)) (.var 2)) (.var 1))))))) (.pi (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.pi (.var 3) (.pi (.app (.app (.app (.app (.var 6) (.var 4)) (.var 3)) (.var 2)) (.var 1)) (.pi (.app (.app (.var 4) (.var 2)) (.var 1)) (.app (.app (.app (.app (.var 8) (.var 6)) (.var 5)) (.var 4)) (.var 2))))))))) (.pi (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.pi (.var 2) (.pi (.app (.app (.app (.app (.var 6) (.var 3)) (.var 2)) (.var 1)) (.var 0)) (.srt .type))) (.pi (.pi (.var 3) (.pi (.app (.app (.var 3) (.var 2)) (.var 0)) (.app (.app (.var 2) (.var 1)) (.app (.app (.app (.app (.app (.var 7) (.var 5)) (.var 4)) (.var 3)) (.var 1)) (.var 0))))) (.pi (.pi (.var 4) (.pi (.var 5) (.pi (.app (.app (.app (.app (.var 9) (.var 6)) (.var 5)) (.var 4)) (.var 1)) (.pi (.app (.app (.var 6) (.var 2)) (.var 1)) (.pi (.app (.app (.var 5) (.var 3)) (.var 1)) (.app (.app (.var 6) (.var 3)) (.app (.app (.app (.app (.app (.app (.app (.var 10) (.var 9)) (.var 8)) (.var 7)) (.var 4)) (.var 3)) (.var 2)) (.var 1)))))))) (.pi (.var 5) (.pi (.app (.app (.app (.app (.var 9) (.var 6)) (.var 5)) (.var 4)) (.var 0)) (.app (.app (.var 4) (.var 1)) (.var 0)))))))))) (.pi (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.pi (.var 3) (.pi (.app (.app (.var 3) (.var 2)) (.var 1)) (.pi (.app (.app (.app (.app (.var 9) (.var 5)) (.var 4)) (.var 2)) (.var 1)) (.app (.app (.app (.app (.var 10) (.var 6)) (.var 5)) (.var 4)) (.var 2))))))))) (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.pi (.app (.app (.app (.app (.var 8) (.var 3)) (.var 2)) (.var 0)) (.var 1)) (.app (.app (.app (.app (.var 9) (.var 4)) (.lam (.var 4) (.lam (.var 5) (.app (.app (.var 5) (.var 0)) (.var 1))))) (.var 2)) (.var 1)))))))))))

def normalizedCandidate_TransGen_swap : LF.Term :=
  .lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.srt .type))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.pi (.app (.app (.var 2) (.var 1)) (.var 0)) (.app (.app (.app (.app (.var 5) (.var 4)) (.var 3)) (.var 2)) (.var 1))))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.pi (.var 3) (.pi (.app (.app (.app (.app (.var 6) (.var 4)) (.var 3)) (.var 2)) (.var 1)) (.pi (.app (.app (.var 4) (.var 2)) (.var 1)) (.app (.app (.app (.app (.var 8) (.var 6)) (.var 5)) (.var 4)) (.var 2))))))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.pi (.var 2) (.pi (.app (.app (.app (.app (.var 6) (.var 3)) (.var 2)) (.var 1)) (.var 0)) (.srt .type))) (.pi (.pi (.var 3) (.pi (.app (.app (.var 3) (.var 2)) (.var 0)) (.app (.app (.var 2) (.var 1)) (.app (.app (.app (.app (.app (.var 7) (.var 5)) (.var 4)) (.var 3)) (.var 1)) (.var 0))))) (.pi (.pi (.var 4) (.pi (.var 5) (.pi (.app (.app (.app (.app (.var 9) (.var 6)) (.var 5)) (.var 4)) (.var 1)) (.pi (.app (.app (.var 6) (.var 2)) (.var 1)) (.pi (.app (.app (.var 5) (.var 3)) (.var 1)) (.app (.app (.var 6) (.var 3)) (.app (.app (.app (.app (.app (.app (.app (.var 10) (.var 9)) (.var 8)) (.var 7)) (.var 4)) (.var 3)) (.var 2)) (.var 1)))))))) (.pi (.var 5) (.pi (.app (.app (.app (.app (.var 9) (.var 6)) (.var 5)) (.var 4)) (.var 0)) (.app (.app (.var 4) (.var 1)) (.var 0)))))))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.pi (.var 3) (.pi (.app (.app (.var 3) (.var 2)) (.var 1)) (.pi (.app (.app (.app (.app (.var 9) (.var 5)) (.var 4)) (.var 2)) (.var 1)) (.app (.app (.app (.app (.var 10) (.var 6)) (.var 5)) (.var 4)) (.var 2))))))))) (.lam (.srt .type) (.lam (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.lam (.var 1) (.lam (.var 2) (.app (.app (.app (.app (.app (.app (.app (.var 5) (.var 3)) (.var 2)) (.var 0)) (.lam (.var 3) (.lam (.app (.app (.app (.app (.var 9) (.var 4)) (.var 3)) (.var 1)) (.var 0)) (.app (.app (.app (.app (.var 10) (.var 5)) (.lam (.var 5) (.lam (.var 6) (.app (.app (.var 6) (.var 0)) (.var 1))))) (.var 1)) (.var 2))))) (.lam (.var 3) (.app (.app (.app (.app (.var 8) (.var 4)) (.lam (.var 4) (.lam (.var 5) (.app (.app (.var 5) (.var 0)) (.var 1))))) (.var 0)) (.var 1)))) (.lam (.var 3) (.lam (.var 4) (.lam (.app (.app (.app (.app (.var 10) (.var 5)) (.var 4)) (.var 2)) (.var 1)) (.app (.app (.app (.app (.app (.var 7) (.var 6)) (.lam (.var 6) (.lam (.var 7) (.app (.app (.var 7) (.var 0)) (.var 1))))) (.var 1)) (.var 2)) (.var 3)))))) (.var 1))))))))))

theorem normalizedGoal_TransGen_swap_eq :
    normalizedGoal_TransGen_swap =
      LFBetaEta.normalForm [] PureBetaEta.normalizationFuel
        (encodeExpr PureDTTBench31.goal_Relation_TransGen_swap) := by
  decide

theorem normalizedCandidate_TransGen_swap_eq :
    normalizedCandidate_TransGen_swap =
      LFBetaEta.normalForm [] PureBetaEta.normalizationFuel
        candidate_TransGen_swap := by
  decide

def replay_TransGen_swap : ReplayCase :=
  { name := "TransGen_swap", actionCount := 33, traceSha256 := "ffc20c1f719d6425eeaa3ca4f814f73c8ffd7fd1f7b8598bc3d378d1572acaf5", referenceTermSha256 := "c69f3f4fb20682b9094e7af82063eb7c2c248cc7d30b56de3f50b3a82546af8f"
    goal := encodeExpr PureDTTBench31.goal_Relation_TransGen_swap
    candidate := candidate_TransGen_swap }

theorem replay_TransGen_swap_accepted : accepts replay_TransGen_swap = true := by
  decide

theorem replay_TransGen_swap_sound :
    LFConversionProfileChecker.Deriv LFProfile.indexed [] []
      candidate_TransGen_swap (encodeExpr PureDTTBench31.goal_Relation_TransGen_swap) :=
  LFConversionProfileChecker.S1 replay_TransGen_swap_accepted

def candidate_ReflTransGen_swap : LF.Term :=
  .lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.srt .type))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.app (.app (.app (.app (.var 3) (.var 2)) (.var 1)) (.var 0)) (.var 0))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.pi (.var 3) (.pi (.app (.app (.app (.app (.var 6) (.var 4)) (.var 3)) (.var 2)) (.var 1)) (.pi (.app (.app (.var 4) (.var 2)) (.var 1)) (.app (.app (.app (.app (.var 8) (.var 6)) (.var 5)) (.var 4)) (.var 2))))))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.pi (.var 2) (.pi (.app (.app (.app (.app (.var 6) (.var 3)) (.var 2)) (.var 1)) (.var 0)) (.srt .type))) (.pi (.app (.app (.var 0) (.var 1)) (.app (.app (.app (.var 5) (.var 3)) (.var 2)) (.var 1))) (.pi (.pi (.var 4) (.pi (.var 5) (.pi (.app (.app (.app (.app (.var 9) (.var 6)) (.var 5)) (.var 4)) (.var 1)) (.pi (.app (.app (.var 6) (.var 2)) (.var 1)) (.pi (.app (.app (.var 5) (.var 3)) (.var 1)) (.app (.app (.var 6) (.var 3)) (.app (.app (.app (.app (.app (.app (.app (.var 10) (.var 9)) (.var 8)) (.var 7)) (.var 4)) (.var 3)) (.var 2)) (.var 1)))))))) (.pi (.var 5) (.pi (.app (.app (.app (.app (.var 9) (.var 6)) (.var 5)) (.var 4)) (.var 0)) (.app (.app (.var 4) (.var 1)) (.var 0)))))))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.pi (.var 3) (.pi (.app (.app (.var 3) (.var 2)) (.var 1)) (.pi (.app (.app (.app (.app (.var 9) (.var 5)) (.var 4)) (.var 2)) (.var 1)) (.app (.app (.app (.app (.var 10) (.var 6)) (.var 5)) (.var 4)) (.var 2))))))))) (.lam (.srt .type) (.lam (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.lam (.var 1) (.lam (.var 2) (.lam (.app (.app (.app (.app (.var 8) (.var 3)) (.var 2)) (.var 0)) (.var 1)) (.app (.app (.app (.app (.app (.app (.app (.app (.var 6) (.var 4)) (.lam (.var 4) (.lam (.var 5) (.app (.app (.var 5) (.var 1)) (.var 0))))) (.var 1)) (.lam (.var 4) (.lam (.app (.app (.app (.app (.var 10) (.var 5)) (.lam (.var 5) (.lam (.var 6) (.app (.app (.var 6) (.var 1)) (.var 0))))) (.var 2)) (.var 0)) (.app (.app (.app (.app (.var 11) (.var 6)) (.lam (.var 6) (.lam (.var 7) (.app (.app (.var 7) (.var 0)) (.var 1))))) (.var 1)) (.var 3))))) (.app (.app (.app (.var 8) (.var 4)) (.lam (.var 4) (.lam (.var 5) (.app (.app (.var 5) (.var 0)) (.var 1))))) (.var 1))) (.lam (.var 4) (.lam (.var 5) (.lam (.app (.app (.app (.app (.var 11) (.var 6)) (.lam (.var 6) (.lam (.var 7) (.app (.app (.var 7) (.var 1)) (.var 0))))) (.var 3)) (.var 1)) (.lam (.app (.app (.lam (.var 7) (.lam (.var 8) (.app (.app (.var 8) (.var 1)) (.var 0)))) (.var 2)) (.var 1)) (.lam (.app (.app (.lam (.var 8) (.lam (.app (.app (.app (.app (.var 14) (.var 9)) (.lam (.var 9) (.lam (.var 10) (.app (.app (.var 10) (.var 1)) (.var 0))))) (.var 6)) (.var 0)) (.app (.app (.app (.app (.var 15) (.var 10)) (.lam (.var 10) (.lam (.var 11) (.app (.app (.var 11) (.var 0)) (.var 1))))) (.var 1)) (.var 7)))) (.var 3)) (.var 1)) (.app (.app (.app (.app (.app (.app (.app (.var 10) (.var 9)) (.lam (.var 9) (.lam (.var 10) (.app (.app (.var 10) (.var 0)) (.var 1))))) (.var 3)) (.var 4)) (.var 6)) (.var 1)) (.var 0)))))))) (.var 2)) (.var 0)))))))))))

def normalizedGoal_ReflTransGen_swap : LF.Term :=
  .pi (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.srt .type))))) (.pi (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.app (.app (.app (.app (.var 3) (.var 2)) (.var 1)) (.var 0)) (.var 0))))) (.pi (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.pi (.var 3) (.pi (.app (.app (.app (.app (.var 6) (.var 4)) (.var 3)) (.var 2)) (.var 1)) (.pi (.app (.app (.var 4) (.var 2)) (.var 1)) (.app (.app (.app (.app (.var 8) (.var 6)) (.var 5)) (.var 4)) (.var 2))))))))) (.pi (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.pi (.var 2) (.pi (.app (.app (.app (.app (.var 6) (.var 3)) (.var 2)) (.var 1)) (.var 0)) (.srt .type))) (.pi (.app (.app (.var 0) (.var 1)) (.app (.app (.app (.var 5) (.var 3)) (.var 2)) (.var 1))) (.pi (.pi (.var 4) (.pi (.var 5) (.pi (.app (.app (.app (.app (.var 9) (.var 6)) (.var 5)) (.var 4)) (.var 1)) (.pi (.app (.app (.var 6) (.var 2)) (.var 1)) (.pi (.app (.app (.var 5) (.var 3)) (.var 1)) (.app (.app (.var 6) (.var 3)) (.app (.app (.app (.app (.app (.app (.app (.var 10) (.var 9)) (.var 8)) (.var 7)) (.var 4)) (.var 3)) (.var 2)) (.var 1)))))))) (.pi (.var 5) (.pi (.app (.app (.app (.app (.var 9) (.var 6)) (.var 5)) (.var 4)) (.var 0)) (.app (.app (.var 4) (.var 1)) (.var 0)))))))))) (.pi (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.pi (.var 3) (.pi (.app (.app (.var 3) (.var 2)) (.var 1)) (.pi (.app (.app (.app (.app (.var 9) (.var 5)) (.var 4)) (.var 2)) (.var 1)) (.app (.app (.app (.app (.var 10) (.var 6)) (.var 5)) (.var 4)) (.var 2))))))))) (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.pi (.app (.app (.app (.app (.var 8) (.var 3)) (.var 2)) (.var 0)) (.var 1)) (.app (.app (.app (.app (.var 9) (.var 4)) (.lam (.var 4) (.lam (.var 5) (.app (.app (.var 5) (.var 0)) (.var 1))))) (.var 2)) (.var 1)))))))))))

def normalizedCandidate_ReflTransGen_swap : LF.Term :=
  .lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.srt .type))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.app (.app (.app (.app (.var 3) (.var 2)) (.var 1)) (.var 0)) (.var 0))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.pi (.var 3) (.pi (.app (.app (.app (.app (.var 6) (.var 4)) (.var 3)) (.var 2)) (.var 1)) (.pi (.app (.app (.var 4) (.var 2)) (.var 1)) (.app (.app (.app (.app (.var 8) (.var 6)) (.var 5)) (.var 4)) (.var 2))))))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.pi (.var 2) (.pi (.app (.app (.app (.app (.var 6) (.var 3)) (.var 2)) (.var 1)) (.var 0)) (.srt .type))) (.pi (.app (.app (.var 0) (.var 1)) (.app (.app (.app (.var 5) (.var 3)) (.var 2)) (.var 1))) (.pi (.pi (.var 4) (.pi (.var 5) (.pi (.app (.app (.app (.app (.var 9) (.var 6)) (.var 5)) (.var 4)) (.var 1)) (.pi (.app (.app (.var 6) (.var 2)) (.var 1)) (.pi (.app (.app (.var 5) (.var 3)) (.var 1)) (.app (.app (.var 6) (.var 3)) (.app (.app (.app (.app (.app (.app (.app (.var 10) (.var 9)) (.var 8)) (.var 7)) (.var 4)) (.var 3)) (.var 2)) (.var 1)))))))) (.pi (.var 5) (.pi (.app (.app (.app (.app (.var 9) (.var 6)) (.var 5)) (.var 4)) (.var 0)) (.app (.app (.var 4) (.var 1)) (.var 0)))))))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.pi (.var 3) (.pi (.app (.app (.var 3) (.var 2)) (.var 1)) (.pi (.app (.app (.app (.app (.var 9) (.var 5)) (.var 4)) (.var 2)) (.var 1)) (.app (.app (.app (.app (.var 10) (.var 6)) (.var 5)) (.var 4)) (.var 2))))))))) (.lam (.srt .type) (.lam (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.lam (.var 1) (.lam (.var 2) (.app (.app (.app (.app (.app (.app (.app (.var 5) (.var 3)) (.var 2)) (.var 0)) (.lam (.var 3) (.lam (.app (.app (.app (.app (.var 9) (.var 4)) (.var 3)) (.var 1)) (.var 0)) (.app (.app (.app (.app (.var 10) (.var 5)) (.lam (.var 5) (.lam (.var 6) (.app (.app (.var 6) (.var 0)) (.var 1))))) (.var 1)) (.var 2))))) (.app (.app (.app (.var 7) (.var 3)) (.lam (.var 3) (.lam (.var 4) (.app (.app (.var 4) (.var 0)) (.var 1))))) (.var 0))) (.lam (.var 3) (.lam (.var 4) (.lam (.app (.app (.app (.app (.var 10) (.var 5)) (.var 4)) (.var 2)) (.var 1)) (.app (.app (.app (.app (.app (.var 7) (.var 6)) (.lam (.var 6) (.lam (.var 7) (.app (.app (.var 7) (.var 0)) (.var 1))))) (.var 1)) (.var 2)) (.var 3)))))) (.var 1))))))))))

theorem normalizedGoal_ReflTransGen_swap_eq :
    normalizedGoal_ReflTransGen_swap =
      LFBetaEta.normalForm [] PureBetaEta.normalizationFuel
        (encodeExpr PureDTTBench31.goal_Relation_ReflTransGen_swap) := by
  decide

theorem normalizedCandidate_ReflTransGen_swap_eq :
    normalizedCandidate_ReflTransGen_swap =
      LFBetaEta.normalForm [] PureBetaEta.normalizationFuel
        candidate_ReflTransGen_swap := by
  decide

def replay_ReflTransGen_swap : ReplayCase :=
  { name := "ReflTransGen_swap", actionCount := 31, traceSha256 := "fb81668cf20df153e6a00a11f9a8be7eb07f1e6f4de1fc18801920deb8dd8c4d", referenceTermSha256 := "ff3d58259b097d7bab3ed4b76a508d37a84b17dd4d7334cf25e84f1390fb1635"
    goal := encodeExpr PureDTTBench31.goal_Relation_ReflTransGen_swap
    candidate := candidate_ReflTransGen_swap }

theorem replay_ReflTransGen_swap_accepted : accepts replay_ReflTransGen_swap = true := by
  decide

theorem replay_ReflTransGen_swap_sound :
    LFConversionProfileChecker.Deriv LFProfile.indexed [] []
      candidate_ReflTransGen_swap (encodeExpr PureDTTBench31.goal_Relation_ReflTransGen_swap) :=
  LFConversionProfileChecker.S1 replay_ReflTransGen_swap_accepted

def candidate_EqvGen_mono : LF.Term :=
  .lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.srt .type))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.pi (.app (.app (.var 2) (.var 1)) (.var 0)) (.app (.app (.app (.app (.var 5) (.var 4)) (.var 3)) (.var 2)) (.var 1))))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.app (.app (.app (.app (.var 4) (.var 2)) (.var 1)) (.var 0)) (.var 0))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.pi (.app (.app (.app (.app (.var 6) (.var 3)) (.var 2)) (.var 1)) (.var 0)) (.app (.app (.app (.app (.var 7) (.var 4)) (.var 3)) (.var 1)) (.var 2))))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.pi (.var 3) (.pi (.app (.app (.app (.app (.var 8) (.var 4)) (.var 3)) (.var 2)) (.var 1)) (.pi (.app (.app (.app (.app (.var 9) (.var 5)) (.var 4)) (.var 2)) (.var 1)) (.app (.app (.app (.app (.var 10) (.var 6)) (.var 5)) (.var 4)) (.var 2))))))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.pi (.var 1) (.pi (.var 2) (.pi (.app (.app (.app (.app (.var 8) (.var 3)) (.var 2)) (.var 1)) (.var 0)) (.srt .type)))) (.pi (.pi (.var 2) (.pi (.var 3) (.pi (.app (.app (.var 3) (.var 1)) (.var 0)) (.app (.app (.app (.var 3) (.var 2)) (.var 1)) (.app (.app (.app (.app (.app (.var 9) (.var 5)) (.var 4)) (.var 2)) (.var 1)) (.var 0)))))) (.pi (.pi (.var 3) (.app (.app (.app (.var 2) (.var 0)) (.var 0)) (.app (.app (.app (.var 7) (.var 4)) (.var 3)) (.var 0)))) (.pi (.pi (.var 4) (.pi (.var 5) (.pi (.app (.app (.app (.app (.var 11) (.var 6)) (.var 5)) (.var 1)) (.var 0)) (.pi (.app (.app (.app (.var 5) (.var 2)) (.var 1)) (.var 0)) (.app (.app (.app (.var 6) (.var 2)) (.var 3)) (.app (.app (.app (.app (.app (.var 10) (.var 8)) (.var 7)) (.var 3)) (.var 2)) (.var 1))))))) (.pi (.pi (.var 5) (.pi (.var 6) (.pi (.var 7) (.pi (.app (.app (.app (.app (.var 13) (.var 8)) (.var 7)) (.var 2)) (.var 1)) (.pi (.app (.app (.app (.app (.var 14) (.var 9)) (.var 8)) (.var 2)) (.var 1)) (.pi (.app (.app (.app (.var 8) (.var 4)) (.var 3)) (.var 1)) (.pi (.app (.app (.app (.var 9) (.var 4)) (.var 3)) (.var 1)) (.app (.app (.app (.var 10) (.var 6)) (.var 4)) (.app (.app (.app (.app (.app (.app (.app (.var 13) (.var 12)) (.var 11)) (.var 6)) (.var 5)) (.var 4)) (.var 3)) (.var 2)))))))))) (.pi (.var 6) (.pi (.var 7) (.pi (.app (.app (.app (.app (.var 13) (.var 8)) (.var 7)) (.var 1)) (.var 0)) (.app (.app (.app (.var 7) (.var 2)) (.var 1)) (.var 0)))))))))))) (.lam (.srt .type) (.lam (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.lam (.pi (.var 1) (.pi (.var 2) (.srt .type))) (.lam (.pi (.var 2) (.pi (.var 3) (.pi (.app (.app (.var 3) (.var 1)) (.var 0)) (.app (.app (.var 3) (.var 2)) (.var 1))))) (.lam (.var 3) (.lam (.var 4) (.lam (.app (.app (.app (.app (.var 11) (.var 5)) (.var 4)) (.var 1)) (.var 0)) (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.var 7) (.var 6)) (.lam (.var 6) (.lam (.var 7) (.app (.app (.var 7) (.var 1)) (.var 0))))) (.lam (.var 6) (.lam (.var 7) (.lam (.app (.app (.app (.app (.var 14) (.var 8)) (.lam (.var 8) (.lam (.var 9) (.app (.app (.var 9) (.var 1)) (.var 0))))) (.var 1)) (.var 0)) (.app (.app (.app (.app (.var 15) (.var 9)) (.lam (.var 9) (.lam (.var 10) (.app (.app (.var 9) (.var 1)) (.var 0))))) (.var 2)) (.var 1)))))) (.lam (.var 6) (.lam (.var 7) (.lam (.app (.app (.lam (.var 8) (.lam (.var 9) (.app (.app (.var 9) (.var 1)) (.var 0)))) (.var 1)) (.var 0)) (.app (.app (.app (.app (.app (.var 14) (.var 9)) (.lam (.var 9) (.lam (.var 10) (.app (.app (.var 9) (.var 1)) (.var 0))))) (.var 2)) (.var 1)) (.app (.app (.app (.var 6) (.var 2)) (.var 1)) (.var 0))))))) (.lam (.var 6) (.app (.app (.app (.var 11) (.var 7)) (.lam (.var 7) (.lam (.var 8) (.app (.app (.var 7) (.var 1)) (.var 0))))) (.var 0)))) (.lam (.var 6) (.lam (.var 7) (.lam (.app (.app (.app (.app (.var 14) (.var 8)) (.lam (.var 8) (.lam (.var 9) (.app (.app (.var 9) (.var 1)) (.var 0))))) (.var 1)) (.var 0)) (.lam (.app (.app (.app (.lam (.var 9) (.lam (.var 10) (.lam (.app (.app (.app (.app (.var 17) (.var 11)) (.lam (.var 11) (.lam (.var 12) (.app (.app (.var 12) (.var 1)) (.var 0))))) (.var 1)) (.var 0)) (.app (.app (.app (.app (.var 18) (.var 12)) (.lam (.var 12) (.lam (.var 13) (.app (.app (.var 12) (.var 1)) (.var 0))))) (.var 2)) (.var 1))))) (.var 2)) (.var 1)) (.var 0)) (.app (.app (.app (.app (.app (.var 13) (.var 10)) (.lam (.var 10) (.lam (.var 11) (.app (.app (.var 10) (.var 1)) (.var 0))))) (.var 3)) (.var 2)) (.var 0))))))) (.lam (.var 6) (.lam (.var 7) (.lam (.var 8) (.lam (.app (.app (.app (.app (.var 15) (.var 9)) (.lam (.var 9) (.lam (.var 10) (.app (.app (.var 10) (.var 1)) (.var 0))))) (.var 2)) (.var 1)) (.lam (.app (.app (.app (.app (.var 16) (.var 10)) (.lam (.var 10) (.lam (.var 11) (.app (.app (.var 11) (.var 1)) (.var 0))))) (.var 2)) (.var 1)) (.lam (.app (.app (.app (.lam (.var 11) (.lam (.var 12) (.lam (.app (.app (.app (.app (.var 19) (.var 13)) (.lam (.var 13) (.lam (.var 14) (.app (.app (.var 14) (.var 1)) (.var 0))))) (.var 1)) (.var 0)) (.app (.app (.app (.app (.var 20) (.var 14)) (.lam (.var 14) (.lam (.var 15) (.app (.app (.var 14) (.var 1)) (.var 0))))) (.var 2)) (.var 1))))) (.var 4)) (.var 3)) (.var 1)) (.lam (.app (.app (.app (.lam (.var 12) (.lam (.var 13) (.lam (.app (.app (.app (.app (.var 20) (.var 14)) (.lam (.var 14) (.lam (.var 15) (.app (.app (.var 15) (.var 1)) (.var 0))))) (.var 1)) (.var 0)) (.app (.app (.app (.app (.var 21) (.var 15)) (.lam (.var 15) (.lam (.var 16) (.app (.app (.var 15) (.var 1)) (.var 0))))) (.var 2)) (.var 1))))) (.var 4)) (.var 3)) (.var 1)) (.app (.app (.app (.app (.app (.app (.app (.var 15) (.var 13)) (.lam (.var 13) (.lam (.var 14) (.app (.app (.var 13) (.var 1)) (.var 0))))) (.var 6)) (.var 5)) (.var 4)) (.var 1)) (.var 0)))))))))) (.var 2)) (.var 1)) (.var 0))))))))))))))

def normalizedGoal_EqvGen_mono : LF.Term :=
  .pi (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.srt .type))))) (.pi (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.pi (.app (.app (.var 2) (.var 1)) (.var 0)) (.app (.app (.app (.app (.var 5) (.var 4)) (.var 3)) (.var 2)) (.var 1))))))) (.pi (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.app (.app (.app (.app (.var 4) (.var 2)) (.var 1)) (.var 0)) (.var 0))))) (.pi (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.pi (.app (.app (.app (.app (.var 6) (.var 3)) (.var 2)) (.var 1)) (.var 0)) (.app (.app (.app (.app (.var 7) (.var 4)) (.var 3)) (.var 1)) (.var 2))))))) (.pi (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.pi (.var 3) (.pi (.app (.app (.app (.app (.var 8) (.var 4)) (.var 3)) (.var 2)) (.var 1)) (.pi (.app (.app (.app (.app (.var 9) (.var 5)) (.var 4)) (.var 2)) (.var 1)) (.app (.app (.app (.app (.var 10) (.var 6)) (.var 5)) (.var 4)) (.var 2))))))))) (.pi (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.pi (.var 1) (.pi (.var 2) (.pi (.app (.app (.app (.app (.var 8) (.var 3)) (.var 2)) (.var 1)) (.var 0)) (.srt .type)))) (.pi (.pi (.var 2) (.pi (.var 3) (.pi (.app (.app (.var 3) (.var 1)) (.var 0)) (.app (.app (.app (.var 3) (.var 2)) (.var 1)) (.app (.app (.app (.app (.app (.var 9) (.var 5)) (.var 4)) (.var 2)) (.var 1)) (.var 0)))))) (.pi (.pi (.var 3) (.app (.app (.app (.var 2) (.var 0)) (.var 0)) (.app (.app (.app (.var 7) (.var 4)) (.var 3)) (.var 0)))) (.pi (.pi (.var 4) (.pi (.var 5) (.pi (.app (.app (.app (.app (.var 11) (.var 6)) (.var 5)) (.var 1)) (.var 0)) (.pi (.app (.app (.app (.var 5) (.var 2)) (.var 1)) (.var 0)) (.app (.app (.app (.var 6) (.var 2)) (.var 3)) (.app (.app (.app (.app (.app (.var 10) (.var 8)) (.var 7)) (.var 3)) (.var 2)) (.var 1))))))) (.pi (.pi (.var 5) (.pi (.var 6) (.pi (.var 7) (.pi (.app (.app (.app (.app (.var 13) (.var 8)) (.var 7)) (.var 2)) (.var 1)) (.pi (.app (.app (.app (.app (.var 14) (.var 9)) (.var 8)) (.var 2)) (.var 1)) (.pi (.app (.app (.app (.var 8) (.var 4)) (.var 3)) (.var 1)) (.pi (.app (.app (.app (.var 9) (.var 4)) (.var 3)) (.var 1)) (.app (.app (.app (.var 10) (.var 6)) (.var 4)) (.app (.app (.app (.app (.app (.app (.app (.var 13) (.var 12)) (.var 11)) (.var 6)) (.var 5)) (.var 4)) (.var 3)) (.var 2)))))))))) (.pi (.var 6) (.pi (.var 7) (.pi (.app (.app (.app (.app (.var 13) (.var 8)) (.var 7)) (.var 1)) (.var 0)) (.app (.app (.app (.var 7) (.var 2)) (.var 1)) (.var 0)))))))))))) (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.pi (.var 1) (.pi (.var 2) (.srt .type))) (.pi (.pi (.var 2) (.pi (.var 3) (.pi (.app (.app (.var 3) (.var 1)) (.var 0)) (.app (.app (.var 3) (.var 2)) (.var 1))))) (.pi (.var 3) (.pi (.var 4) (.pi (.app (.app (.app (.app (.var 11) (.var 5)) (.var 4)) (.var 1)) (.var 0)) (.app (.app (.app (.app (.var 12) (.var 6)) (.var 4)) (.var 2)) (.var 1))))))))))))))

def normalizedCandidate_EqvGen_mono : LF.Term :=
  .lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.srt .type))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.pi (.app (.app (.var 2) (.var 1)) (.var 0)) (.app (.app (.app (.app (.var 5) (.var 4)) (.var 3)) (.var 2)) (.var 1))))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.app (.app (.app (.app (.var 4) (.var 2)) (.var 1)) (.var 0)) (.var 0))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.pi (.app (.app (.app (.app (.var 6) (.var 3)) (.var 2)) (.var 1)) (.var 0)) (.app (.app (.app (.app (.var 7) (.var 4)) (.var 3)) (.var 1)) (.var 2))))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.var 1) (.pi (.var 2) (.pi (.var 3) (.pi (.app (.app (.app (.app (.var 8) (.var 4)) (.var 3)) (.var 2)) (.var 1)) (.pi (.app (.app (.app (.app (.var 9) (.var 5)) (.var 4)) (.var 2)) (.var 1)) (.app (.app (.app (.app (.var 10) (.var 6)) (.var 5)) (.var 4)) (.var 2))))))))) (.lam (.pi (.srt .type) (.pi (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.pi (.pi (.var 1) (.pi (.var 2) (.pi (.app (.app (.app (.app (.var 8) (.var 3)) (.var 2)) (.var 1)) (.var 0)) (.srt .type)))) (.pi (.pi (.var 2) (.pi (.var 3) (.pi (.app (.app (.var 3) (.var 1)) (.var 0)) (.app (.app (.app (.var 3) (.var 2)) (.var 1)) (.app (.app (.app (.app (.app (.var 9) (.var 5)) (.var 4)) (.var 2)) (.var 1)) (.var 0)))))) (.pi (.pi (.var 3) (.app (.app (.app (.var 2) (.var 0)) (.var 0)) (.app (.app (.app (.var 7) (.var 4)) (.var 3)) (.var 0)))) (.pi (.pi (.var 4) (.pi (.var 5) (.pi (.app (.app (.app (.app (.var 11) (.var 6)) (.var 5)) (.var 1)) (.var 0)) (.pi (.app (.app (.app (.var 5) (.var 2)) (.var 1)) (.var 0)) (.app (.app (.app (.var 6) (.var 2)) (.var 3)) (.app (.app (.app (.app (.app (.var 10) (.var 8)) (.var 7)) (.var 3)) (.var 2)) (.var 1))))))) (.pi (.pi (.var 5) (.pi (.var 6) (.pi (.var 7) (.pi (.app (.app (.app (.app (.var 13) (.var 8)) (.var 7)) (.var 2)) (.var 1)) (.pi (.app (.app (.app (.app (.var 14) (.var 9)) (.var 8)) (.var 2)) (.var 1)) (.pi (.app (.app (.app (.var 8) (.var 4)) (.var 3)) (.var 1)) (.pi (.app (.app (.app (.var 9) (.var 4)) (.var 3)) (.var 1)) (.app (.app (.app (.var 10) (.var 6)) (.var 4)) (.app (.app (.app (.app (.app (.app (.app (.var 13) (.var 12)) (.var 11)) (.var 6)) (.var 5)) (.var 4)) (.var 3)) (.var 2)))))))))) (.pi (.var 6) (.pi (.var 7) (.pi (.app (.app (.app (.app (.var 13) (.var 8)) (.var 7)) (.var 1)) (.var 0)) (.app (.app (.app (.var 7) (.var 2)) (.var 1)) (.var 0)))))))))))) (.lam (.srt .type) (.lam (.pi (.var 0) (.pi (.var 1) (.srt .type))) (.lam (.pi (.var 1) (.pi (.var 2) (.srt .type))) (.lam (.pi (.var 2) (.pi (.var 3) (.pi (.app (.app (.var 3) (.var 1)) (.var 0)) (.app (.app (.var 3) (.var 2)) (.var 1))))) (.app (.app (.app (.app (.app (.app (.app (.var 4) (.var 3)) (.var 2)) (.lam (.var 3) (.lam (.var 4) (.lam (.app (.app (.app (.app (.var 11) (.var 5)) (.var 4)) (.var 1)) (.var 0)) (.app (.app (.app (.app (.var 12) (.var 6)) (.var 4)) (.var 2)) (.var 1)))))) (.lam (.var 3) (.lam (.var 4) (.lam (.app (.app (.var 4) (.var 1)) (.var 0)) (.app (.app (.app (.app (.app (.var 11) (.var 6)) (.var 4)) (.var 2)) (.var 1)) (.app (.app (.app (.var 3) (.var 2)) (.var 1)) (.var 0))))))) (.app (.app (.var 7) (.var 3)) (.var 1))) (.lam (.var 3) (.lam (.var 4) (.lam (.app (.app (.app (.app (.var 11) (.var 5)) (.var 4)) (.var 1)) (.var 0)) (.app (.app (.app (.app (.var 9) (.var 6)) (.var 4)) (.var 2)) (.var 1)))))) (.lam (.var 3) (.lam (.var 4) (.lam (.var 5) (.lam (.app (.app (.app (.app (.var 12) (.var 6)) (.var 5)) (.var 2)) (.var 1)) (.lam (.app (.app (.app (.app (.var 13) (.var 7)) (.var 6)) (.var 2)) (.var 1)) (.app (.app (.app (.app (.app (.var 10) (.var 8)) (.var 6)) (.var 4)) (.var 3)) (.var 2)))))))))))))))))

theorem normalizedGoal_EqvGen_mono_eq :
    normalizedGoal_EqvGen_mono =
      LFBetaEta.normalForm [] PureBetaEta.normalizationFuel
        (encodeExpr PureDTTBench31.goal_Relation_EqvGen_mono) := by
  decide

theorem normalizedCandidate_EqvGen_mono_eq :
    normalizedCandidate_EqvGen_mono =
      LFBetaEta.normalForm [] PureBetaEta.normalizationFuel
        candidate_EqvGen_mono := by
  decide

def replay_EqvGen_mono : ReplayCase :=
  { name := "EqvGen_mono", actionCount := 50, traceSha256 := "579bf194999f0ee71f5d41c7c5bce343f6575edf9a6c30ecd5f5abda266469be", referenceTermSha256 := "bf1b9c14b2c18800b5b4a95dcdf370387dccf7b3662eff5a8388960cbd1502b3"
    goal := encodeExpr PureDTTBench31.goal_Relation_EqvGen_mono
    candidate := candidate_EqvGen_mono }

theorem replay_EqvGen_mono_accepted : accepts replay_EqvGen_mono = true := by
  decide

theorem replay_EqvGen_mono_sound :
    LFConversionProfileChecker.Deriv LFProfile.indexed [] []
      candidate_EqvGen_mono (encodeExpr PureDTTBench31.goal_Relation_EqvGen_mono) :=
  LFConversionProfileChecker.S1 replay_EqvGen_mono_accepted

def candidate_powerset_mono : LF.Term :=
  .lam (.srt .type) (.lam (.srt .type) (.lam (.pi (.var 1) (.srt .type)) (.lam (.pi (.var 2) (.srt .type)) (.lam (.pi (.pi (.pi (.pi (.var 3) (.srt .type)) (.pi (.pi (.var 4) (.pi (.app (.var 1) (.var 0)) (.app (.var 4) (.var 1)))) (.pi (.var 5) (.pi (.app (.var 2) (.var 0)) (.app (.var 4) (.var 1)))))) (.pi (.var 4) (.pi (.app (.var 3) (.var 0)) (.app (.var 3) (.var 1))))) (.pi (.pi (.pi (.var 4) (.pi (.app (.var 3) (.var 0)) (.app (.var 3) (.var 1)))) (.pi (.pi (.var 5) (.srt .type)) (.pi (.pi (.var 6) (.pi (.app (.var 1) (.var 0)) (.app (.var 6) (.var 1)))) (.pi (.var 7) (.pi (.app (.var 2) (.var 0)) (.app (.var 6) (.var 1))))))) (.var 4))) (.app (.app (.var 0) (.lam (.pi (.pi (.var 4) (.srt .type)) (.pi (.pi (.var 5) (.pi (.app (.var 1) (.var 0)) (.app (.var 5) (.var 1)))) (.pi (.var 6) (.pi (.app (.var 2) (.var 0)) (.app (.var 5) (.var 1)))))) (.lam (.var 5) (.lam (.app (.var 4) (.var 0)) (.app (.app (.app (.app (.var 2) (.lam (.var 7) (.app (.var 6) (.var 0)))) (.lam (.var 7) (.lam (.app (.lam (.var 8) (.app (.var 7) (.var 0))) (.var 0)) (.var 0)))) (.var 1)) (.var 0)))))) (.lam (.pi (.var 4) (.pi (.app (.var 3) (.var 0)) (.app (.var 3) (.var 1)))) (.lam (.pi (.var 5) (.srt .type)) (.lam (.pi (.var 6) (.pi (.app (.var 1) (.var 0)) (.app (.var 6) (.var 1)))) (.lam (.var 7) (.lam (.app (.var 2) (.var 0)) (.app (.app (.var 4) (.var 1)) (.app (.app (.var 2) (.var 1)) (.var 0)))))))))))))

def normalizedGoal_powerset_mono : LF.Term :=
  .pi (.srt .type) (.pi (.srt .type) (.pi (.pi (.var 1) (.srt .type)) (.pi (.pi (.var 2) (.srt .type)) (.pi (.pi (.pi (.pi (.pi (.var 3) (.srt .type)) (.pi (.pi (.var 4) (.pi (.app (.var 1) (.var 0)) (.app (.var 4) (.var 1)))) (.pi (.var 5) (.pi (.app (.var 2) (.var 0)) (.app (.var 4) (.var 1)))))) (.pi (.var 4) (.pi (.app (.var 3) (.var 0)) (.app (.var 3) (.var 1))))) (.pi (.pi (.pi (.var 4) (.pi (.app (.var 3) (.var 0)) (.app (.var 3) (.var 1)))) (.pi (.pi (.var 5) (.srt .type)) (.pi (.pi (.var 6) (.pi (.app (.var 1) (.var 0)) (.app (.var 6) (.var 1)))) (.pi (.var 7) (.pi (.app (.var 2) (.var 0)) (.app (.var 6) (.var 1))))))) (.var 4))) (.var 3)))))

def normalizedCandidate_powerset_mono : LF.Term :=
  .lam (.srt .type) (.lam (.srt .type) (.lam (.pi (.var 1) (.srt .type)) (.lam (.pi (.var 2) (.srt .type)) (.lam (.pi (.pi (.pi (.pi (.var 3) (.srt .type)) (.pi (.pi (.var 4) (.pi (.app (.var 1) (.var 0)) (.app (.var 4) (.var 1)))) (.pi (.var 5) (.pi (.app (.var 2) (.var 0)) (.app (.var 4) (.var 1)))))) (.pi (.var 4) (.pi (.app (.var 3) (.var 0)) (.app (.var 3) (.var 1))))) (.pi (.pi (.pi (.var 4) (.pi (.app (.var 3) (.var 0)) (.app (.var 3) (.var 1)))) (.pi (.pi (.var 5) (.srt .type)) (.pi (.pi (.var 6) (.pi (.app (.var 1) (.var 0)) (.app (.var 6) (.var 1)))) (.pi (.var 7) (.pi (.app (.var 2) (.var 0)) (.app (.var 6) (.var 1))))))) (.var 4))) (.app (.app (.var 0) (.lam (.pi (.pi (.var 4) (.srt .type)) (.pi (.pi (.var 5) (.pi (.app (.var 1) (.var 0)) (.app (.var 5) (.var 1)))) (.pi (.var 6) (.pi (.app (.var 2) (.var 0)) (.app (.var 5) (.var 1)))))) (.app (.app (.var 0) (.var 3)) (.lam (.var 5) (.lam (.app (.var 4) (.var 0)) (.var 0)))))) (.lam (.pi (.var 4) (.pi (.app (.var 3) (.var 0)) (.app (.var 3) (.var 1)))) (.lam (.pi (.var 5) (.srt .type)) (.lam (.pi (.var 6) (.pi (.app (.var 1) (.var 0)) (.app (.var 6) (.var 1)))) (.lam (.var 7) (.lam (.app (.var 2) (.var 0)) (.app (.app (.var 4) (.var 1)) (.app (.app (.var 2) (.var 1)) (.var 0)))))))))))))

theorem normalizedGoal_powerset_mono_eq :
    normalizedGoal_powerset_mono =
      LFBetaEta.normalForm [] PureBetaEta.normalizationFuel
        (encodeExpr PureDTTBench31.goal_Set_powerset_mono) := by
  decide

theorem normalizedCandidate_powerset_mono_eq :
    normalizedCandidate_powerset_mono =
      LFBetaEta.normalForm [] PureBetaEta.normalizationFuel
        candidate_powerset_mono := by
  decide

def replay_powerset_mono : ReplayCase :=
  { name := "powerset_mono", actionCount := 12, traceSha256 := "195dfe5c72f44c8ec6acbec6786c82cda14325d9dbeface506a68cb45f92a3d9", referenceTermSha256 := "3c16e0f05260f6b5367fe348b57fbc29efe26265295c0d6f0efcd9c49f644bef"
    goal := encodeExpr PureDTTBench31.goal_Set_powerset_mono
    candidate := candidate_powerset_mono }

theorem replay_powerset_mono_accepted : accepts replay_powerset_mono = true := by
  decide

theorem replay_powerset_mono_sound :
    LFConversionProfileChecker.Deriv LFProfile.indexed [] []
      candidate_powerset_mono (encodeExpr PureDTTBench31.goal_Set_powerset_mono) :=
  LFConversionProfileChecker.S1 replay_powerset_mono_accepted

def candidate_Cantor : LF.Term :=
  .lam (.srt .type) (.lam (.pi (.srt .type) (.pi (.srt .type) (.srt .type))) (.lam (.pi (.var 1) (.pi (.var 2) (.srt .type))) (.lam (.pi (.pi (.var 2) (.srt .type)) (.var 3)) (.lam (.pi (.pi (.var 3) (.srt .type)) (.pi (.var 4) (.app (.app (.var 4) (.app (.app (.var 3) (.app (.var 2) (.var 1))) (.var 0))) (.app (.var 1) (.var 0))))) (.lam (.pi (.srt .type) (.srt .type)) (.lam (.srt .type) (.lam (.pi (.srt .type) (.pi (.app (.app (.var 6) (.var 0)) (.app (.var 2) (.var 0))) (.var 2))) (.app (.app (.var 0) (.app (.app (.var 5) (.app (.var 4) (.lam (.var 7) (.app (.var 3) (.app (.app (.var 6) (.var 0)) (.var 0)))))) (.app (.var 4) (.lam (.var 7) (.app (.var 3) (.app (.app (.var 6) (.var 0)) (.var 0))))))) (.app (.app (.var 3) (.lam (.var 7) (.app (.var 3) (.app (.app (.var 6) (.var 0)) (.var 0))))) (.app (.var 4) (.lam (.var 7) (.app (.var 3) (.app (.app (.var 6) (.var 0)) (.var 0))))))))))))))

def normalizedGoal_Cantor : LF.Term :=
  .pi (.srt .type) (.pi (.pi (.srt .type) (.pi (.srt .type) (.srt .type))) (.pi (.pi (.var 1) (.pi (.var 2) (.srt .type))) (.pi (.pi (.pi (.var 2) (.srt .type)) (.var 3)) (.pi (.pi (.pi (.var 3) (.srt .type)) (.pi (.var 4) (.app (.app (.var 4) (.app (.app (.var 3) (.app (.var 2) (.var 1))) (.var 0))) (.app (.var 1) (.var 0))))) (.pi (.pi (.srt .type) (.srt .type)) (.pi (.srt .type) (.pi (.pi (.srt .type) (.pi (.app (.app (.var 6) (.var 0)) (.app (.var 2) (.var 0))) (.var 2))) (.var 1))))))))

def normalizedCandidate_Cantor : LF.Term :=
  .lam (.srt .type) (.lam (.pi (.srt .type) (.pi (.srt .type) (.srt .type))) (.lam (.pi (.var 1) (.pi (.var 2) (.srt .type))) (.lam (.pi (.pi (.var 2) (.srt .type)) (.var 3)) (.lam (.pi (.pi (.var 3) (.srt .type)) (.pi (.var 4) (.app (.app (.var 4) (.app (.app (.var 3) (.app (.var 2) (.var 1))) (.var 0))) (.app (.var 1) (.var 0))))) (.lam (.pi (.srt .type) (.srt .type)) (.lam (.srt .type) (.lam (.pi (.srt .type) (.pi (.app (.app (.var 6) (.var 0)) (.app (.var 2) (.var 0))) (.var 2))) (.app (.app (.var 0) (.app (.app (.var 5) (.app (.var 4) (.lam (.var 7) (.app (.var 3) (.app (.app (.var 6) (.var 0)) (.var 0)))))) (.app (.var 4) (.lam (.var 7) (.app (.var 3) (.app (.app (.var 6) (.var 0)) (.var 0))))))) (.app (.app (.var 3) (.lam (.var 7) (.app (.var 3) (.app (.app (.var 6) (.var 0)) (.var 0))))) (.app (.var 4) (.lam (.var 7) (.app (.var 3) (.app (.app (.var 6) (.var 0)) (.var 0))))))))))))))

theorem normalizedGoal_Cantor_eq :
    normalizedGoal_Cantor =
      LFBetaEta.normalForm [] PureBetaEta.normalizationFuel
        (encodeExpr PureDTTBench31.goal_Set_Cantor) := by
  decide

theorem normalizedCandidate_Cantor_eq :
    normalizedCandidate_Cantor =
      LFBetaEta.normalForm [] PureBetaEta.normalizationFuel
        candidate_Cantor := by
  decide

def replay_Cantor : ReplayCase :=
  { name := "Cantor", actionCount := 22, traceSha256 := "42024e90926d756e254dae5e2fe08083f75c227adfe516602453991f0d244ea2", referenceTermSha256 := "48dfa3fa0ed463f9c9f78361229108c9a5594679e29c2061aefd47470122bb28"
    goal := encodeExpr PureDTTBench31.goal_Set_Cantor
    candidate := candidate_Cantor }

theorem replay_Cantor_accepted : accepts replay_Cantor = true := by
  decide

theorem replay_Cantor_sound :
    LFConversionProfileChecker.Deriv LFProfile.indexed [] []
      candidate_Cantor (encodeExpr PureDTTBench31.goal_Set_Cantor) :=
  LFConversionProfileChecker.S1 replay_Cantor_accepted

def cases : List ReplayCase :=
  [replay_Eq_symm,
   replay_Eq_trans,
   replay_Eq_congrArg,
   replay_Eq_congr,
   replay_Eq_congrFun,
   replay_Eq_mp,
   replay_Nat_zero_le,
   replay_Nat_succ_le_succ,
   replay_Nat_le_trans,
   replay_sSup_inter_le,
   replay_Iff_refl,
   replay_Or_elim,
   replay_False_elim,
   replay_peirce,
   replay_PUnit_ext,
   replay_Exists_imp,
   replay_Relation_TransGen_trans,
   replay_ReflGen_to_reflTransGen,
   replay_ReflGen_mono,
   replay_ReflTransGen_trans,
   replay_ReflTransGen_head,
   replay_ReflTransGen_symmetric,
   replay_TransGen_to_reflTransGen,
   replay_TransGen_trans_left,
   replay_TransGen_to_self,
   replay_TransGen_lift,
   replay_TransGen_swap,
   replay_ReflTransGen_swap,
   replay_EqvGen_mono,
   replay_powerset_mono,
   replay_Cantor]

theorem cases_length : cases.length = 31 := by rfl

theorem all_cases_accept : cases.all accepts = true := by
  simp [cases, replay_Eq_symm_accepted, replay_Eq_trans_accepted, replay_Eq_congrArg_accepted, replay_Eq_congr_accepted, replay_Eq_congrFun_accepted, replay_Eq_mp_accepted, replay_Nat_zero_le_accepted, replay_Nat_succ_le_succ_accepted, replay_Nat_le_trans_accepted, replay_sSup_inter_le_accepted, replay_Iff_refl_accepted, replay_Or_elim_accepted, replay_False_elim_accepted, replay_peirce_accepted, replay_PUnit_ext_accepted, replay_Exists_imp_accepted, replay_Relation_TransGen_trans_accepted, replay_ReflGen_to_reflTransGen_accepted, replay_ReflGen_mono_accepted, replay_ReflTransGen_trans_accepted, replay_ReflTransGen_head_accepted, replay_ReflTransGen_symmetric_accepted, replay_TransGen_to_reflTransGen_accepted, replay_TransGen_trans_left_accepted, replay_TransGen_to_self_accepted, replay_TransGen_lift_accepted, replay_TransGen_swap_accepted, replay_ReflTransGen_swap_accepted, replay_EqvGen_mono_accepted, replay_powerset_mono_accepted, replay_Cantor_accepted]

/-- A malformed candidate cannot exploit the source metadata. -/
def malformed : ReplayCase :=
  { replay_Eq_symm with candidate := .srt .kind }

theorem malformed_rejected : accepts malformed = false := by
  decide

/-- Decrementing one outer de-Bruijn reference captures it. -/
def binderCaptureCandidate : LF.Term :=
  .lam (.pi (.srt .type) (.pi (.var 0) (.pi (.var 0) (.srt .type)))) (.lam (.pi (.srt .type) (.pi (.var 0) (.app (.app (.app (.var 2) (.var 1)) (.var 0)) (.var 0)))) (.lam (.pi (.srt .type) (.pi (.var 0) (.pi (.pi (.var 1) (.pi (.app (.app (.app (.var 4) (.var 2)) (.var 1)) (.var 0)) (.srt .type))) (.pi (.app (.app (.var 0) (.var 1)) (.app (.app (.var 3) (.var 2)) (.var 1))) (.pi (.var 3) (.pi (.app (.app (.app (.var 6) (.var 4)) (.var 3)) (.var 0)) (.app (.app (.var 3) (.var 1)) (.var 0)))))))) (.lam (.srt .type) (.lam (.var 0) (.app (.app (.app (.app (.var 2) (.var 1)) (.var 0)) (.lam (.var 1) (.lam (.app (.app (.app (.var 5) (.var 2)) (.var 1)) (.var 0)) (.app (.app (.app (.var 6) (.var 3)) (.var 1)) (.var 2))))) (.app (.app (.var 3) (.var 1)) (.var 0)))))))

def binderCaptureMutation : ReplayCase :=
  { replay_Eq_symm with candidate := binderCaptureCandidate }

theorem binderCaptureMutation_rejected :
    accepts binderCaptureMutation = false := by
  decide

/-- This accepted case is genuinely eta-sensitive: beta normal forms
alone do not coincide. -/
theorem Eq_congrFun_requires_eta :
    LFTyping.nf [] 128 candidate_Eq_congrFun ≠
      LFTyping.nf [] 128
        (encodeExpr PureDTTBench31.goal_Eq_Eq_congrFun) := by
  decide

#print axioms all_cases_accept
#print axioms replay_Eq_congrFun_sound
#print axioms replay_sSup_inter_le_sound
#print axioms malformed_rejected
#print axioms binderCaptureMutation_rejected
#print axioms Eq_congrFun_requires_eta

end Mettapedia.GSLT.LanguageDef.LFDTTBenchConversionReplay
