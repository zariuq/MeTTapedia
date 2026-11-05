import Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRPrologLowering
import Mettapedia.Languages.CHR.Examples

/-! Constructor interpretation and CHR admission controls. Textual source,
forest coverage and selected parses have separate executable controls; these
kernel proofs test the interpretation of source terms into independent IR. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRPrologLoweringControls

open Mettapedia.Logic.Prolog
open Mettapedia.Languages.CHR
open CHRPrologLowering

private def atom := SourceSignature.atom
private def app := SourceSignature.compound
private def int := SourceSignature.integer
private def var := SourceSignature.var
private def binary (name : String) (left right : SourceTerm) := app name [left,right]
private def named (name : String) (body : SourceTerm) := binary "@" (atom name) body
private def declaration (name : String) (arity : Nat) := binary "/" (atom name) (int arity)
private def declarations (body : SourceTerm) := app ":-" [app "chr_constraint" [body]]
private def query (body : SourceTerm) := app "?-" [body]

private def read (sources : List SourceTerm) : Except String CHRPrologLowering.Program := do
  let forms ← sources.zipIdx.mapM fun (source, index) => form index source
  assemble forms

theorem minimum_lowering : read [
    declarations (declaration "minimum" 1),
    named "minimum_remove" (binary "<=>"
      (binary "\\" (app "minimum" [var "X" 0]) (app "minimum" [var "Y" 1]))
      (binary "|" (binary "=<" (var "X" 0) (var "Y" 1)) (atom "true"))),
    query (binary "," (app "minimum" [int 4])
      (binary "," (app "minimum" [int 2])
        (binary "," (app "minimum" [int 2]) (app "minimum" [int 9]))))] =
    .ok ⟨Examples.minimum, [4,2,2,9].map (fun n => Examples.fact "minimum" [.integer n])⟩ := by
  decide_cbv

theorem gcd_lowering : read [
    app ":-" [app "use_module" [app "library" [atom "chr"]]],
    declarations (declaration "gcd" 1),
    named "gcd_zero" (binary "<=>" (app "gcd" [int 0]) (atom "true")),
    named "gcd_reduce" (binary "<=>"
      (binary "\\" (app "gcd" [var "N" 0]) (app "gcd" [var "M" 1]))
      (binary "|" (binary "=<" (var "N" 0) (var "M" 1))
        (binary "," (binary "is" (var "L" 2) (binary "mod" (var "M" 1) (var "N" 0)))
          (app "gcd" [var "L" 2]))))] = .ok ⟨Examples.gcd, []⟩ := by decide_cbv

theorem canonical_indices : form 0 (named "r" (binary "<=>"
    (app "p" [var "V8" 0,var "V0" 1]) (app "q" [var "V0" 1,var "V8" 0]))) = .ok (.rule
    ⟨"r", [], [⟨"p", [.var 8,.var 0]⟩], [], [.tell ⟨"q", [.var 0,.var 8]⟩]⟩) := by decide_cbv

theorem mixed_names_do_not_alias : form 0 (named "r" (binary "<=>"
    (app "p" [var "V8" 0,var "X" 1,var "V0" 2])
    (app "q" [var "X" 1,var "V0" 2,var "V8" 0]))) = .ok (.rule
    ⟨"r", [], [⟨"p", [.var 0,.var 1,.var 2]⟩], [], [.tell ⟨"q", [.var 1,.var 2,.var 0]⟩]⟩) := by decide_cbv

theorem anonymous_occurrences_distinct : form 0 (named "r" (binary "==>"
    (app "p" [var "_" 0,var "_" 1]) (atom "true"))) = .ok (.rule
    ⟨"r", [⟨"p", [.var 0,.var 1]⟩], [], [], []⟩) := by decide_cbv

theorem tuple_sharing : form 0 (named "r" (binary "<=>"
    (binary "," (app "p" [app "tuple" [var "X" 0,atom "a"]])
      (app "p" [app "tuple" [var "X" 0,atom "a"]])) (atom "true"))) = .ok (.rule
    ⟨"r", [], [⟨"p", [.tuple [.var 0,.value (.atom "a")]]⟩,
      ⟨"p", [.tuple [.var 0,.value (.atom "a")]]⟩], [], []⟩) := by decide_cbv

theorem repeated_inputs_remain_distinct : read [declarations (declaration "p" 1),
    query (binary "," (app "p" [int 1]) (app "p" [int 1]))] =
    .ok ⟨⟨[⟨"p",1⟩],[]⟩, [Examples.fact "p" [.integer 1],Examples.fact "p" [.integer 1]]⟩ := by decide_cbv

theorem unsafe_body_refused : (read [declarations (binary "," (declaration "p" 1) (declaration "q" 1)),
    named "r" (binary "<=>" (app "p" [var "X" 0]) (app "q" [var "Y" 1]))]).isOk = false := by decide_cbv

theorem non_ground_query_refused : (read [declarations (declaration "p" 1), query (app "p" [var "X" 0])]).isOk = false := by
  decide_cbv

theorem bad_query_arity_refused : (read [declarations (declaration "p" 1), query (app "p" [int 1,int 2])]).isOk = false := by
  decide_cbv

theorem host_effect_not_executed : (form 0 (app ":-" [app "write" [atom "hello"]])).isOk = false := by decide_cbv

#print axioms minimum_lowering
#print axioms gcd_lowering
#print axioms mixed_names_do_not_alias
#print axioms unsafe_body_refused

end Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRPrologLoweringControls
