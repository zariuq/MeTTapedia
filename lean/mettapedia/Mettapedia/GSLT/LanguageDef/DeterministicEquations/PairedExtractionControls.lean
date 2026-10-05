import Mettapedia.GSLT.LanguageDef.DeterministicEquations.PairedExtraction
import Mathlib.Tactic.NormNum

/-! # Source extraction, reflection and refusal controls -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DeterministicEquations.Extraction.Controls

open Lean Meta Elab Command
open Mettapedia.Languages
open Paired

private def bytesHead : String :=
  "nik:extracted:Mettapedia.GSLT.LanguageDef.DeterministicEquations.Extraction.Paired.bytesProgram"

private def substitutionHead : String :=
  "nik:extracted:Mettapedia.GSLT.LanguageDef.DeterministicEquations.Extraction.Paired.substitutionProgram"

theorem bytes_empty (value : Nat) :
    Applies bytesProgram productDivisionHost bytesHead [natural 0, natural value] (.list []) :=
  bytes_computes 0 value

theorem bytes_all_widths_and_values (width value : Nat) (observed : DeterministicEquations.Term) :
    Applies bytesProgram productDivisionHost bytesHead [natural width, natural value] observed ↔
      observed = encodeList encodeByte (VibeITP.Spec.leBytes width value) :=
  bytes_computes_result_exact width value observed

theorem byte_order_is_preserved :
    Applies bytesProgram productDivisionHost bytesHead [natural 2, natural 258]
      (.list [natural 2, natural 1]) := by
  simpa [bytesHead, encodeList, encodeByte, VibeITP.Spec.leBytes, UInt8.toNat_ofNat'] using bytes_computes 2 258

theorem swapped_byte_order_refuses :
    ¬ Applies bytesProgram productDivisionHost bytesHead [natural 2, natural 258]
      (.list [natural 1, natural 2]) := by
  intro accepted
  have same := accepted.deterministic byte_order_is_preserved
  cases same

theorem extra_byte_refuses (value : Nat) :
    ¬ Applies bytesProgram productDivisionHost bytesHead [natural 0, natural value]
      (.list [natural 7]) := by
  intro accepted
  have same := accepted.deterministic (bytes_empty value)
  cases same

theorem above_word_range_keeps_ninth_byte :
    Applies bytesProgram productDivisionHost bytesHead [natural 9, natural (2 ^ 64)]
      (.list [natural 0, natural 0, natural 0, natural 0, natural 0, natural 0, natural 0,
        natural 0, natural 1]) := by
  have computed := bytes_computes 9 (2 ^ 64)
  norm_num [bytesHead, encodeList, encodeByte, VibeITP.Spec.leBytes, UInt8.toNat_ofNat'] at computed ⊢
  exact computed

theorem missing_substitution_image_is_none :
    Applies substitutionProgram productDivisionHost substitutionHead
      [encodeList MM0.Presentation.encode [], MM0.Presentation.encode (.var 0)] (.sym "None") :=
  substitution_computes [] (.var 0)

theorem substitution_is_simultaneous :
    Applies substitutionProgram productDivisionHost substitutionHead
      [encodeList MM0.Presentation.encode [.var 1, .term 17], MM0.Presentation.encode (.var 0)]
      (encodeOption MM0.Presentation.encode (some (.var 1))) :=
  substitution_computes [.var 1, .term 17] (.var 0)

theorem recursively_substituted_image_refuses :
    ¬ Applies substitutionProgram productDivisionHost substitutionHead
      [encodeList MM0.Presentation.encode [.var 1, .term 17], MM0.Presentation.encode (.var 0)]
      (encodeOption MM0.Presentation.encode (some (.term 17))) := by
  intro accepted
  have same := accepted.deterministic substitution_is_simultaneous
  have payloads := (List.cons.inj (List.cons.inj (DeterministicEquations.Term.expr.inj same)).2).1
  have sourceSame := MM0.Presentation.encode_injective payloads
  cases sourceSame

theorem application_visits_both_children :
    Applies substitutionProgram productDivisionHost substitutionHead
      [encodeList MM0.Presentation.encode [.term 3, .term 7],
        MM0.Presentation.encode (.app (.var 0) (.var 1))]
      (encodeOption MM0.Presentation.encode (some (.app (.term 3) (.term 7)))) :=
  substitution_computes [.term 3, .term 7] (.app (.var 0) (.var 1))

theorem missing_second_child_refuses_as_data :
    Applies substitutionProgram productDivisionHost substitutionHead
      [encodeList MM0.Presentation.encode [.term 3],
        MM0.Presentation.encode (.app (.var 0) (.var 1))] (.sym "None") :=
  substitution_computes [.term 3] (.app (.var 0) (.var 1))

theorem huge_missing_index_is_none :
    Applies substitutionProgram productDivisionHost substitutionHead
      [encodeList MM0.Presentation.encode [.term 3],
        MM0.Presentation.encode (.var (2 ^ 128))] (.sym "None") :=
  substitution_computes [.term 3] (.var (2 ^ 128))

theorem wrong_arity_is_failure :
    apply bytesProgram productDivisionHost 32 bytesHead [natural 0] = .failure := rfl

theorem malformed_natural_is_failure :
    apply bytesProgram productDivisionHost 32 bytesHead [.sym "bad-width", natural 0] = .failure := rfl

private def refused : Outcome → Bool
  | .failure => true
  | _ => false

private theorem refused_iff (outcome : Outcome) : refused outcome = true ↔ outcome = .failure := by
  cases outcome <;> simp [refused]

theorem foreign_preterm_is_failure :
    apply substitutionProgram productDivisionHost 32 substitutionHead
      [.list [], .expr [.sym "Foreign:Var", natural 0]] = .failure := by
  apply (refused_iff _).mp
  decide +kernel

theorem exhaustion_is_separate :
    apply bytesProgram productDivisionHost 0 bytesHead [natural 1, natural 0] = .exhausted := rfl

theorem completed_runs_cannot_refuse (width value fuel : Nat)
    (completed : apply bytesProgram productDivisionHost fuel bytesHead
      [natural width, natural value] ≠ .exhausted) :
    apply bytesProgram productDivisionHost fuel bytesHead [natural width, natural value] =
      .value (encodeList encodeByte (VibeITP.Spec.leBytes width value)) :=
  bytes_computes_completed_exact width value fuel completed

namespace Alias

certify_extraction bytesProgram from VibeITP.Spec.leBytes as qualified_alias_computes

end Alias

namespace Distinct

extract_candidate bytesProgram from VibeITP.Spec.leBytes

end Distinct

theorem namespaced_programs_have_distinct_dispatch :
    (Paired.bytesProgram.map Equation.head).headD "" ≠
      (Distinct.bytesProgram.map Equation.head).headD "" := by decide

/- The following elaboration controls test refusals before any certificate is
installed. They are not theorem counts or assumptions of correspondence. -/

private def unsupportedPower (value : Nat) : Nat := 2 ^ value
private def zeroDivision (value : Nat) : Nat := value / 0

@[instance_reducible] private def foreignPure : Pure Option := ⟨fun _ => none⟩
@[instance_reducible] private def foreignBind : Bind Option := ⟨fun _ _ => none⟩

private def foreignPureSource (value : Nat) : Option Nat :=
  @Pure.pure Option foreignPure Nat value

private def foreignBindSource (value : Option Nat) : Option Nat :=
  @Bind.bind Option foreignBind Nat Nat value Option.some

private inductive Pair where
  | node (first second : Nat)

private def permutedCodec : Pair → DeterministicEquations.Term
  | .node first second => named "Pair" [natural second, natural first]

private theorem permutedCodec_injective : Function.Injective permutedCodec := by
  intro first second same
  cases first with
  | node a b =>
      cases second with
      | node c d =>
          have items := DeterministicEquations.Term.expr.inj same
          have tails := (List.cons.inj items).2
          have hb := natural_injective (List.cons.inj tails).1
          have ha := natural_injective (List.cons.inj (List.cons.inj tails).2).1
          subst c
          subst d
          rfl

private def pairSource : Pair → Pair
  | .node first second => .node first second

private def runAttempt (operation : Elab.Term.TermElabM Unit) : Elab.Term.TermElabM Bool := do
  let saved ← saveState
  try
    operation
    return false
  catch _ =>
    saved.restore
    return true

private def requireRefusal (operation : Elab.Term.TermElabM Unit) : Elab.Term.TermElabM Unit := do
  unless ← runAttempt operation do throwError "unsupported source was silently accepted"

private def emptyMutant : Program :=
  [⟨"mutated", "mutation:bytes", [.var "width", .var "value"], .list []⟩]

run_cmd liftTermElabM do
  for source in #[``unsupportedPower, ``zeroDivision, ``foreignPureSource, ``foreignBindSource] do
    requireRefusal do
      let root ← inspectRoot source ("test:" ++ source.toString)
      let _ ← compileRoot root
  let originalEnvironment ← getEnv
  registerCodec ⟨``Pair, ``permutedCodec, ``permutedCodec_injective⟩
  requireRefusal do
    let root ← inspectRoot ``pairSource "test:permuted-fields"
    let _ ← compileRoot root
  modifyEnv fun _ => originalEnvironment
  requireRefusal do
    let _ ← certify ``emptyMutant ``VibeITP.Spec.leBytes "mutation:bytes"

end Mettapedia.GSLT.LanguageDef.DeterministicEquations.Extraction.Controls
