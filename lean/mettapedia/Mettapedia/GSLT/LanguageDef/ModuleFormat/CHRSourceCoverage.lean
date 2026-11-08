import Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRRuntimeCompiler
import Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceCatalogueCertifiedCoverage

/-! The meaning of a verified CHR source. The lang library verifies a source
text, its native forest and its selected catalogue before it reads the
catalogue. When the certified verifier accepts and the reader returns a
program, every whole-input interpretation of the text that the CHR grammar,
lexical profile and selection admit is a catalogue packet that the CHR
frontend reads as exactly that program: the native parser omitted none, and
the retained ambiguity policy leaves none with another meaning. Every packet
the reader reads is such an interpretation. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRRuntimeCompiler

open Lean (Json)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.Parsing.LanguageDefScalarPrinter (stringScalars)
open ScalarSyntaxCore RetainedSourceLowering
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

/-- The verifier's reply when both checks finished and accepted. -/
def verifiedReply : Json := Json.mkObj [("status", .str "verified")]

theorem pending_ne_verified : Json.mkObj [("status", .str "pending")] ≠ verifiedReply := by
  intro same
  have := congrArg (fun json : Json => (json.getObjValAs? String "status").toOption) same
  revert this
  decide

/-- A description has one parser: its rules and plan are compiled. -/
theorem parser_unique {description : Description} (first second : Parser description) : first = second := by
  obtain ⟨rules, plan, rulesCompiled, planCompiled⟩ := first
  obtain ⟨rules', plan', rulesCompiled', planCompiled'⟩ := second
  have sameRules : rules = rules' := Option.some.inj (rulesCompiled.symm.trans rulesCompiled')
  subst sameRules
  have samePlan : plan = plan' := Option.some.inj (planCompiled.symm.trans planCompiled')
  subst samePlan
  rfl

theorem except_bind_ok {ε α β : Type} {first : Except ε α} {next : α → Except ε β} {result : β}
    (bound : first >>= next = .ok result) : ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first with
  | error message => cases bound
  | ok value => exact ⟨value, rfl, bound⟩

theorem mapM_ok_of_mem {α β ε : Type} (f : α → Except ε β) :
    ∀ (inputs : List α) (outputs : List β), inputs.mapM f = .ok outputs →
      ∀ input ∈ inputs, ∃ output ∈ outputs, f input = .ok output
  | [], _, _, input, member => absurd member List.not_mem_nil
  | first :: rest, outputs, mapped, input, member => by
    rw [List.mapM_cons] at mapped
    cases one : f first with
    | error message => simp [one, bind, Except.bind] at mapped
    | ok value =>
      cases others : rest.mapM f with
      | error message => simp [one, others, bind, Except.bind] at mapped
      | ok values =>
        simp only [one, others, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at mapped
        subst mapped
        rcases List.mem_cons.mp member with rfl | later
        · exact ⟨value, List.mem_cons_self, one⟩
        · obtain ⟨output, inside, same⟩ := mapM_ok_of_mem f rest values others input later
          exact ⟨output, List.mem_cons_of_mem _ inside, same⟩

/-- An accepted verification reply came from an accepted certified check of
the catalogue's packets. -/
theorem verifySource_verified {spec : Portable.SyntaxDescription} {filters : List SourceSyntax.FamilyFilter}
    {source catalogue forest identity allowance : String}
    (verified : SourceCompilerProtocol.verifySource spec filters source catalogue forest identity allowance =
      .ok verifiedReply) :
    ∃ evidence, SourceCompilerProtocol.readSourceEvidence catalogue forest identity allowance = .ok evidence ∧
      SourceCatalogueCertifiedVerification.verify? spec filters source evidence.forest evidence.identity
        evidence.packets evidence.rounds = some true := by
  unfold SourceCompilerProtocol.verifySource at verified
  obtain ⟨evidence, read, checked⟩ := except_bind_ok verified
  refine ⟨evidence, read, ?_⟩
  cases accepted : SourceCatalogueCertifiedVerification.verify? spec filters source evidence.forest
      evidence.identity evidence.packets evidence.rounds with
  | none =>
    simp only [accepted, SourceCompilerProtocol.verificationReply, Except.ok.injEq] at checked
    exact absurd checked pending_ne_verified
  | some result =>
    cases result
    · simp [accepted] at checked
    · rfl

theorem readSourceEvidence_packets {catalogue forest identity allowance : String}
    {evidence : SourceCompilerProtocol.SourceEvidence}
    (read : SourceCompilerProtocol.readSourceEvidence catalogue forest identity allowance = .ok evidence) :
    SpaceSemantics.readSource catalogue = .ok [.expression (.symbol "SourceValuesV1" :: evidence.packets)] := by
  unfold SourceCompilerProtocol.readSourceEvidence at read
  split at read
  · rename_i packets listed
    obtain ⟨forestBytes, _, read⟩ := except_bind_ok read
    obtain ⟨identityBytes, _, read⟩ := except_bind_ok read
    cases rounds : allowance.toNat? with
    | none => simp [rounds] at read
    | some count =>
      simp only [rounds, pure, Except.pure, Except.ok.injEq] at read
      subst read
      exact listed
  · cases read

/-- What reading a catalogue establishes: its packets, each packet's reading,
and the one program they all lower to. -/
theorem readProgram_packets {source catalogue : String} {program : CHRPrologLowering.Program}
    (read : readProgram source catalogue = .ok program) :
    ∃ packets, SpaceSemantics.readSource catalogue = .ok [.expression (.symbol "SourceValuesV1" :: packets)] ∧
      packets ≠ [] ∧
      ∀ packet ∈ packets, ∃ tree retained, packet = .expression [.symbol "result", tree, .symbol "nil"] ∧
        CHRPrologFrontend.read source tree = .ok retained ∧ retained.lowered = program := by
  unfold readProgram at read
  split at read
  · rename_i packets listed
    obtain ⟨outputs, mapped, finished⟩ := except_bind_ok read
    cases outputs with
    | nil => cases finished
    | cons first rest =>
      dsimp only at finished
      split at finished
      · rename_i agree
        simp only [pure, Except.pure, Except.ok.injEq] at finished
        subst finished
        refine ⟨packets, listed, ?_, ?_⟩
        · rintro rfl
          simp [pure, Except.pure] at mapped
        · intro packet member
          obtain ⟨output, inside, stepped⟩ := mapM_ok_of_mem _ packets _ mapped packet member
          have same : output = first := by
            rcases List.mem_cons.mp inside with rfl | later
            · rfl
            · exact of_decide_eq_true (List.all_eq_true.mp agree output later)
          subst same
          split at stepped
          · rename_i tree
            cases frontend : CHRPrologFrontend.read source tree with
            | error message => simp [frontend, Functor.map, Except.map] at stepped
            | ok retained =>
              simp only [frontend, Functor.map, Except.map, Except.ok.injEq] at stepped
              exact ⟨tree, retained, rfl, frontend, stepped⟩
          · cases stepped
      · cases finished
  · cases read

/-- A frontend reading's source core is the packet's replayed core, and the
packet is a selected interpretation. -/
theorem frontend_read_core {source : String} {tree : SourcePacket.Packet}
    {retained : Retained CHRPrologLowering.Program}
    (read : CHRPrologFrontend.read source tree = .ok retained) :
    ∃ admitted, admit? CHRPrologFrontend.description = some admitted ∧
      SourcePacketSelection.core? CHRPrologFrontend.description admitted.parser admitted.shape
        CHRPrologSyntax.selection (stringScalars source) CHRPrologFrontend.description.profile.startSort tree =
          some retained.sourceCore := by
  unfold CHRPrologFrontend.read at read
  cases admitted : admit? CHRPrologFrontend.description with
  | none => simp [admitted] at read
  | some witness =>
    simp only [admitted] at read
    refine ⟨witness, rfl, ?_⟩
    obtain ⟨replayedCore, elaborated⟩ := lower_readback read
    have sort : CHRPrologFrontend.description.profile.startSort = "ChrSourceProgram" := rfl
    cases certificate : SourcePacketCertificate.readPacket? CHRPrologFrontend.description witness.parser
        witness.shape (stringScalars source) "ChrSourceProgram" tree with
    | none => simp [certificate] at elaborated
    | some reading =>
      simp only [certificate] at elaborated
      cases chosen : SourcePacketSelection.selected
          (SourcePacketSelection.allows CHRPrologSyntax.selection (stringScalars source)) "ChrSourceProgram"
          reading.certificate
      · simp [chosen, bind, Except.bind] at elaborated
      · have sameCore : reading.core = retained.sourceCore := by
          unfold SourcePacketCertificate.core? at replayedCore
          rw [sort, certificate] at replayedCore
          exact Option.some.inj replayedCore
        unfold SourcePacketSelection.core? SourcePacketSelection.read?
        rw [sort, certificate]
        simp only [Bind.bind, Option.bind, chosen, ↓reduceIte, Option.map_some, sameCore]

/-- **Every selected interpretation of a verified CHR source has the read
program.** When the certified verifier accepts a source text with its native
forest and selected catalogue, and the reader returns a program from that
catalogue, every whole-input interpretation of the text that the CHR grammar,
lexical profile and selection admit is a catalogue packet that the CHR
frontend reads, with that interpretation as its source core, as exactly the
program. -/
theorem selected_interpretations_read (parser : Parser CHRPrologFrontend.description)
    {source catalogue forest identity allowance : String} {program : CHRPrologLowering.Program}
    (verified : SourceCompilerProtocol.verifySource CHRPrologSyntax.description CHRPrologSyntax.selection
      source catalogue forest identity allowance = .ok verifiedReply)
    (read : readProgram source catalogue = .ok program) {core : Pattern}
    (selected : SourcePacketSelection.Source CHRPrologFrontend.description parser CHRPrologSyntax.selection
      (stringScalars source) CHRPrologFrontend.description.profile.startSort core) :
    ∃ packets, SpaceSemantics.readSource catalogue = .ok [.expression (.symbol "SourceValuesV1" :: packets)] ∧
      ∃ tree, .expression [.symbol "result", tree, .symbol "nil"] ∈ packets ∧
        ∃ retained, CHRPrologFrontend.read source tree = .ok retained ∧
          retained.sourceCore = core ∧ retained.lowered = program := by
  obtain ⟨evidence, evidenceRead, accepted⟩ := verifySource_verified verified
  have listed := readSourceEvidence_packets evidenceRead
  obtain ⟨packets, listedRead, nonempty, readings⟩ := readProgram_packets read
  have samePackets : evidence.packets = packets := by
    have both := listed.symm.trans listedRead
    simp only [Except.ok.injEq, List.cons.injEq, Atom.expression.injEq, true_and, and_true] at both
    exact both
  rw [samePackets] at accepted
  -- The reader read a packet, so the description is admitted.
  obtain ⟨firstPacket, firstMember⟩ := List.exists_mem_of_ne_nil packets nonempty
  obtain ⟨_, _, _, firstRead, _⟩ := readings firstPacket firstMember
  obtain ⟨admitted, admittedSome, _⟩ := frontend_read_core firstRead
  obtain rfl : parser = admitted.parser := parser_unique _ _
  have sort := admitted.parser.agreement.startSort_eq
  rw [← sort] at selected
  obtain ⟨packet, member, treePacket, packetRead, coreRead⟩ :=
    SourceCatalogue.verified_source_returned admitted.parser admitted.shape accepted selected
  obtain ⟨tree, retained, rfl, frontend, lowered⟩ := readings packet member
  have sameTree : tree = treePacket := by
    simp only [SourceCatalogue.packetTree?, Option.some.injEq] at packetRead
    exact packetRead
  subst sameTree
  obtain ⟨admitted', admittedSome', replayed⟩ := frontend_read_core frontend
  have sameAdmitted : admitted' = admitted := Option.some.inj (admittedSome'.symm.trans admittedSome)
  subst sameAdmitted
  rw [sort] at coreRead
  refine ⟨packets, listedRead, _, member, retained, frontend, ?_, lowered⟩
  exact Option.some.inj (replayed.symm.trans coreRead)

/-- **Every packet the reader reads is a selected interpretation.** A program
the reader returns from a catalogue is the reading of at least one packet,
and the source core of every packet it reads is a whole-input interpretation
of the text that the CHR grammar, lexical profile and selection admit. -/
theorem read_interpretations_selected {source catalogue : String} {program : CHRPrologLowering.Program}
    (read : readProgram source catalogue = .ok program) :
    ∃ packets, SpaceSemantics.readSource catalogue = .ok [.expression (.symbol "SourceValuesV1" :: packets)] ∧
      packets ≠ [] ∧
      ∀ packet ∈ packets, ∃ tree admitted retained, packet = .expression [.symbol "result", tree, .symbol "nil"] ∧
        admit? CHRPrologFrontend.description = some admitted ∧
        CHRPrologFrontend.read source tree = .ok retained ∧ retained.lowered = program ∧
        SourcePacketSelection.Source CHRPrologFrontend.description admitted.parser CHRPrologSyntax.selection
          (stringScalars source) CHRPrologFrontend.description.profile.startSort retained.sourceCore := by
  obtain ⟨packets, listed, nonempty, readings⟩ := readProgram_packets read
  refine ⟨packets, listed, nonempty, fun packet member => ?_⟩
  obtain ⟨tree, retained, shaped, frontend, lowered⟩ := readings packet member
  obtain ⟨admitted, admittedSome, replayed⟩ := frontend_read_core frontend
  exact ⟨tree, admitted, retained, shaped, admittedSome, frontend, lowered,
    SourcePacketSelection.core?_sound replayed⟩

#print axioms selected_interpretations_read
#print axioms read_interpretations_selected

end Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRRuntimeCompiler
