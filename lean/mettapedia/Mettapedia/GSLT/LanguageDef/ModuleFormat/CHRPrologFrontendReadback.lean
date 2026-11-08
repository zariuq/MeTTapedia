import Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRPrologFrontend
import Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRPrologSentences

/-! **Canonical CHR source reads back through the frontend.** Every packet the
frontend accepts for the canonical text of a printable, admitted program with
declared inputs lowers to that program in tuple normal form, with its inputs
(`read_printed`). The packet's sentence texts cover the text up to layout, so
they are the printed sentences up to the newline between them, and each reads
as its form. Whether the native parser proposes a packet at all is the
separate forest-coverage obligation. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRPrologFrontend

open Mettapedia.Logic.Prolog
open Mettapedia.Languages
open ScalarSyntaxCore
open CHRPrologTermReadback
open CHRPrologReadback (programForms ProgramPrintable assemble_forms)
open Mettapedia.Languages.CHR.TupleNormal (normalProgram)
open RetainedSourceLowering
open Mettapedia.GSLT.Parsing.LanguageDefScalarPrinter (stringScalars)

/-- Each sentence the frontend reads is accepted by the reference reader, and
its form is the lowering of that reading. -/
theorem readSentences_reads : ∀ (ordinal : Nat) (sentences : List SourcePacket.Packet)
    (read : List (String × CHRPrologLowering.Form)), readSentences ordinal sentences = .ok read →
    ∀ pair ∈ read, ∃ result number, ReaderTerm.readOneWith chr chr.operators pair.1 = .ok result ∧
      CHRPrologLowering.form number result.term = .ok pair.2
  | _, [], read, done => by
    simp only [readSentences, Except.ok.injEq] at done
    subst done
    intro pair inside
    cases inside
  | ordinal, sentence :: rest, read, done => by
    unfold readSentences at done
    cases texted : PrologSourceLowering.text CHRPrologSyntax.profile "PlSentence" sentence with
    | error reason =>
      simp only [texted, bind, Except.bind] at done
      cases done
    | ok text =>
      simp only [texted, bind, Except.bind] at done
      cases checked : PrologSourceFrontend.checkedLower CHRPrologSyntax.profile text sentence with
      | error reason =>
        simp only [checked] at done
        cases done
      | ok parsed =>
        simp only [checked] at done
        cases formed : CHRPrologLowering.form ordinal parsed.term with
        | error reason =>
          simp only [formed] at done
          cases done
        | ok form =>
          simp only [formed] at done
          cases later : readSentences (nextOrdinal ordinal form) rest with
          | error reason =>
            simp only [later] at done
            cases done
          | ok others =>
            simp only [later, pure, Except.pure, Except.ok.injEq] at done
            subst done
            intro pair inside
            rcases List.mem_cons.mp inside with rfl | inside
            · obtain ⟨reference, reads, sameTerm, _⟩ := PrologSourceFrontend.checkedLower_agrees checked
              exact ⟨reference, ordinal, reads, by rw [← sameTerm]; exact formed⟩
            · exact readSentences_reads _ rest others later pair inside

theorem covers_split {input : String} {texts : List String} (covered : covers input texts = true) :
    ∃ tail, (texts.map String.toList).flatten ++ tail = input.toList ∧ Quiet tail := by
  unfold covers at covered
  simp only [Bool.and_eq_true, List.isPrefixOf_iff_prefix] at covered
  obtain ⟨front, quiet⟩ := covered
  refine ⟨input.toList.drop (texts.map String.toList).flatten.length, List.prefix_iff_eq_append.mp front, ?_⟩
  unfold Quiet
  split at quiet
  · assumption
  · cases quiet

theorem forms_agree : ∀ (read : List (String × CHRPrologLowering.Form)) (forms : List CHRPrologLowering.Form),
    (∀ pair ∈ read, ∃ result number, ReaderTerm.readOneWith chr chr.operators pair.1 = .ok result ∧
      CHRPrologLowering.form number result.term = .ok pair.2) →
    List.Forall₂ (fun text form => SentenceReads (String.ofList text) form) (read.map (·.1.toList)) forms →
    read.map Prod.snd = forms
  | [], forms, _, related => by
    cases related
    rfl
  | pair :: read, forms, reads, related => by
    cases related with
    | cons first rest =>
      obtain ⟨result, number, readsPair, formed⟩ := reads pair (List.mem_cons_self ..)
      obtain ⟨result', readsText, lowers⟩ := first
      rw [String.ofList_toList, readsPair, Except.ok.injEq] at readsText
      subst readsText
      rw [lowers number, Except.ok.injEq] at formed
      simp only [List.map_cons, List.cons.injEq]
      exact ⟨formed.symm, forms_agree read _ (fun other inside => reads other (List.mem_cons_of_mem _ inside)) rest⟩

/-- **Canonical source reads back through the frontend.** -/
theorem read_printed (program : CHR.Program) (inputs : List CHR.Constraint)
    (printable : ProgramPrintable program inputs)
    (declared : ∀ constraint ∈ inputs,
      CHR.Admission.declared program ⟨constraint.name, constraint.arguments.map CHR.Term.value⟩ = true)
    (admitted : CHR.Admission.diagnose program = none) {packet : SourcePacket.Packet}
    {result : Retained CHRPrologLowering.Program}
    (accepted : read (CHRPrologPrinter.program program inputs) packet = .ok result) :
    result.lowered = ⟨normalProgram program, inputs⟩ := by
  have elaborated : elaborate (CHRPrologPrinter.program program inputs) packet = .ok result.lowered := by
    unfold read at accepted
    cases admittedDescription : admit? description with
    | none => simp [admittedDescription] at accepted
    | some witness =>
      simp only [admittedDescription] at accepted
      have inner := (lower_readback accepted).2
      cases reading : SourcePacketCertificate.readPacket? description witness.parser witness.shape
          (stringScalars (CHRPrologPrinter.program program inputs)) "ChrSourceProgram" packet with
      | none =>
        simp only [reading] at inner
        cases inner
      | some found =>
        simp only [reading] at inner
        cases selected : SourcePacketSelection.selected
            (SourcePacketSelection.allows CHRPrologSyntax.selection
              (stringScalars (CHRPrologPrinter.program program inputs))) "ChrSourceProgram" found.certificate with
        | false => simp [selected, bind, Except.bind] at inner
        | true => simpa [selected] using inner
  unfold elaborate at elaborated
  simp only [bind, Except.bind] at elaborated
  split at elaborated
  · cases elaborated
  · split at elaborated
    · split at elaborated
      · cases elaborated
      · split at elaborated
        · cases elaborated
        · rename_i readings readSome
          unfold finish at elaborated
          split at elaborated
          · rename_i covered
            obtain ⟨tail, whole, quiet⟩ := covers_split covered
            have reads := readSentences_reads 0 _ readings readSome
            have accepted' : ∀ text ∈ (readings.map Prod.fst).map String.toList, Accepted text := by
              intro text inside
              obtain ⟨piece, member, rfl⟩ := List.mem_map.mp inside
              obtain ⟨pair, pairMember, rfl⟩ := List.mem_map.mp member
              obtain ⟨reading, _, readsPair, _⟩ := reads pair pairMember
              obtain ⟨clean, span, scanned, free⟩ := ReaderTerm.readOneWith_sentence readsPair
              exact ⟨clean, span, by rw [String.ofList_toList]; exact scanned, free⟩
            have segmented := program_segments program inputs printable _ tail whole accepted' quiet
            rw [List.map_map] at segmented
            have formsEq := forms_agree readings (programForms program inputs) reads segmented
            rw [formsEq, assemble_forms program inputs declared admitted, Except.ok.injEq] at elaborated
            exact elaborated.symm
          · cases elaborated
    · cases elaborated

#print axioms read_printed

end Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRPrologFrontend
