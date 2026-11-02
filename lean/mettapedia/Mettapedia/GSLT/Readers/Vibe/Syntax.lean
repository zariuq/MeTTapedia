import Mettapedia.GSLT.LanguageDef.ModuleSource.Commands
import Mettapedia.GSLT.Readers.BinaryTokens

/-!
# Vibe-ITP's checker input, read from its `.module` presentation

Vibe-ITP's standalone checker (`check.c`) replays a stream of instructions, each one opcode byte
followed by its operands, and turns each instruction into exactly one call of the kernel
(`logic.c`). `metta/gslt/module/readers/vibe/CheckStreamSyntax.module` presents that stream as
eight pieces (`SymbolOps`, `TermOps`, `TheoremOps`, `ChallengeOps`, `DefinitionOps`, `SetupOps`,
`ProofOps`, `Files`) joined over one shared `Sorts` value, plus the lexical layer (`Tokens`) as a
binary token profile returned by a message. Each row is one case of `process_file` in `check.c`,
its operands in the order the step reads them, typed as `binary_spec.md` names them; a file before
`--proofs` is read from `setup_file`, a file after it from `proof_file`.

The `.module` file is read when this file is elaborated; Lake does not track it, so a change to it
needs a change here before a build sees it (version: first).

Results:
* `grammar`: the composed grammar; `grammar_rows`, `grammar_types`: its size and sorts;
  `grammar_labels`: its rows by label and sort.
* `profile`: the decoded lexical layer; `profile_facts`: words in the code with 247 as the largest
  one-byte value, 27 one-byte opcode sorts, the operand sorts by kind.
* `token_controls`: which byte strings are tokens of which sorts.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace Mettapedia.GSLT.Readers.Vibe

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.ModuleSource.Commands
open scoped Mettapedia.GSLT.LanguageDef.ModuleSource.Commands
open Mettapedia.GSLT.Readers.TokenProfile (ByteSet)
open Mettapedia.GSLT.Readers.BinaryTokens

#module_file "../../../../../../metta/gslt/module/readers/vibe/CheckStreamSyntax.module"

/-- The grammar the `.module` elaborates to. -/
def grammar? : Option LanguageDef := CheckStreamSyntax.language.toOption

def grammar : LanguageDef := grammar?.get (by decide +kernel)

theorem grammar_elaborated : grammar? = some grammar := (Option.some_get _).symm

theorem grammar_rows : grammar.terms.length = 33 := by decide +kernel

theorem grammar_types : grammar.types.length = 46 := by decide +kernel

/-- The rows, by label and sort, in the order of the `.module`. -/
theorem grammar_labels :
    grammar.terms.map (fun r => (r.label, r.category)) =
      [("fvar_new", "instr"), ("const_new", "instr"), ("symbol_swap", "instr"),
        ("symbol_free", "instr"), ("term_new_bvar", "instr"), ("term_new_literal", "instr"),
        ("term_new_app", "instr"), ("term_swap", "instr"), ("term_free", "instr"),
        ("thm_exchange", "instr"), ("thm_free", "instr"), ("thm_swap", "instr"),
        ("challenge_add", "instr"), ("define_const", "instr"), ("add_axiom", "setup_instr"),
        ("challenge_satisfy", "proof_instr"), ("modus_ponens", "proof_instr"),
        ("thm_instantiate", "proof_instr"), ("thm_lit_is_nat", "proof_instr"),
        ("thm_lit_lt", "proof_instr"), ("thm_lit_add", "proof_instr"),
        ("thm_lit_mul", "proof_instr"), ("thm_lit_div", "proof_instr"),
        ("thm_lit_length", "proof_instr"), ("thm_lit_get", "proof_instr"),
        ("thm_jit", "proof_instr"), ("thm_instantiate_n", "proof_instr"),
        ("setup_end", "setup_file"), ("setup_common", "setup_file"), ("setup_only", "setup_file"),
        ("proof_end", "proof_file"), ("proof_common", "proof_file"),
        ("proof_only", "proof_file")] := by
  decide +kernel

/-! ## The lexical layer -/

def tokensFragment : Except ModuleSource.Error (String × ModuleSource.Value) :=
  ModuleSource.applyTheory CheckStreamSyntax.library CheckStreamSyntax.module ["Tokens"] []

/-- The reply of the `ReturnTokenProfile` message, decoded as a binary profile. -/
def profile? : Option Profile := do
  let (_, fragment) ← tokensFragment.toOption
  match fragment.entries.filterMap (fun entry => match entry.body with
      | ModuleSource.Decl.rewrite rule =>
          if rule.left == .apply "GetTokenProfile" [] then some rule.right else none
      | _ => none) with
  | [reply] => BinaryTokens.profile? reply
  | _ => none

def profile : Profile := profile?.get (by decide +kernel)

/-- The opcode sorts `op0` … `op26`, one byte each. -/
def opcodeSorts : List String := (List.range 27).map fun k => "op" ++ toString k

theorem profile_facts :
    profile.start = "proof_file" ∧ profile.inline = 247 ∧ profile.classes.length = 41 ∧
      (opcodeSorts.zip (List.range 27)).all (fun (c, k) =>
        profile.kindOf? c == some (.byte (.points [k]))) = true ∧
      ["u_nat", "u_sym", "u_term", "u_thm", "u_chal", "u_dst_sym", "u_dst_term", "u_dst_thm",
        "u_dst_chal"].all (fun c => profile.kindOf? c == some .word) = true ∧
      profile.kindOf? "u_count" = some .count ∧
      ["u_nats", "u_syms", "u_terms"].all (fun c => profile.kindOf? c == some .words) = true ∧
      profile.kindOf? "u_bytes" = some .bytes := by
  decide +kernel

/-- Tokens, the counts aside: an opcode is its one byte; `249 44 1` (300) is a word and `248 5`
(five, written with a header) is not; `5 249 44 1` is two words; any bytes are bytes. -/
theorem token_controls :
    (profile.kindOf? "op5").map (·.member 247 [5]) = some true ∧
      (profile.kindOf? "op5").map (·.member 247 [6]) = some false ∧
      (profile.kindOf? "op5").map (·.member 247 [5, 5]) = some false ∧
      (profile.kindOf? "u_term").map (·.member 247 [249, 44, 1]) = some true ∧
      (profile.kindOf? "u_term").map (·.member 247 [248, 5]) = some false ∧
      (profile.kindOf? "u_term").map (·.member 247 []) = some false ∧
      (profile.kindOf? "u_terms").map (·.member 247 [5, 249, 44, 1]) = some true ∧
      (profile.kindOf? "u_terms").map (·.member 247 [249, 44]) = some false ∧
      (profile.kindOf? "u_bytes").map (·.member 247 [0, 255, 248]) = some true ∧
      profile.kindOf? "instr" = none := by
  decide +kernel

end Mettapedia.GSLT.Readers.Vibe
