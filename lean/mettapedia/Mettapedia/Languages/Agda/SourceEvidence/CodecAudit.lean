import Mettapedia.Languages.Agda.SourceEvidence.CodecExecution

open Lean Lean.Elab.Command

run_cmd do
  let modules := [`Mettapedia.Languages.Agda.SourceEvidence.RawCode, `Mettapedia.Languages.Agda.SourceEvidence.NumeralCode, `Mettapedia.Languages.Agda.SourceEvidence.JudgmentCode, `Mettapedia.Languages.Agda.SourceEvidence.ProofCode, `Mettapedia.Languages.Agda.SourceEvidence.DecodeProof,
    `Mettapedia.Languages.Agda.SourceEvidence.ProofRoundtrip, `Mettapedia.Languages.Agda.SourceEvidence.ProofRecovery, `Mettapedia.Languages.Agda.SourceEvidence.ProofControls, `Mettapedia.Languages.Agda.SourceEvidence.CodecExecution]
  let allowed := [``propext, ``Quot.sound]
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if let some origin := env.getModuleIdxFor? name |>.bind (env.header.modules[·]?) then
      if modules.contains origin.module then
        let axioms ← collectAxioms name
        let excess := axioms.filter fun dependency => !allowed.contains dependency
        unless excess.isEmpty do
          throwError "{name}: excess axioms {excess}"
        count := count + 1
        logInfo m!"AUDIT {name}: {axioms}"
  logInfo m!"Source proof codec: {count} module-origin declarations within [propext, Quot.sound]."

#print axioms Mettapedia.Languages.Agda.SourceEvidence.Codec.decode
#print axioms Mettapedia.Languages.Agda.SourceEvidence.Codec.decode_encodePacked
#print axioms Mettapedia.Languages.Agda.SourceEvidence.Codec.encodeEvidence_injective
#print axioms Mettapedia.Languages.Agda.SourceEvidence.Codec.evidenceEncodable
#print axioms Mettapedia.Languages.Agda.SourceEvidence.Codec.decodeNat_encodeNat
#print axioms Mettapedia.Languages.Agda.SourceEvidence.Codec.recover
#print axioms Mettapedia.Languages.Agda.SourceEvidence.Codec.Controls.ordered_receipts_distinct
#print axioms Mettapedia.Languages.Agda.SourceEvidence.Codec.Controls.wrong_universe_has_no_proof_code
