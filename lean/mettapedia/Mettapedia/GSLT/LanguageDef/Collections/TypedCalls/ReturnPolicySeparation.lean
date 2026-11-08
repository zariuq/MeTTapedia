import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.ChainRegionAdmission
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEReturns

/-!
# Return protocols are not a common intersection of object types

PeTTa checks the enclosing row after its body has returned. HE evaluates the
body at the enclosing range, but a nested typed head can establish its own
return evaluation policy. In particular, a nested `%Undefined%` range can
prevent a final enclosing `Number` cast. A shared boundary algebra therefore
cannot identify the two dialects' return-obligation composition rules.

The controls below use actual equation-body evaluation and the existing HE
interpreter. They are not a proposed change to either language.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.ReturnPolicySeparation

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open TypedCalls.Controls (env num str)

def rows : String → Option (List (Ty Empty) × Ty Empty)
  | "k" => some ([.sym "Number"], .sym "Number")
  | "g" => some ([.sym "Number"], .sym "%Undefined%")
  | _ => none

def declarations : Decls := fun name =>
  match rows name with
  | some (params, range) => [arrow (params.map Ty.lift) range.lift]
  | none => []

theorem declarations_functional : Functional declarations := by
  intro name
  unfold declarations
  cases rows name <;> simp

theorem rejects_string (grounded : String → Bool) :
    owedCheck declarations grounded (some (.sym "Number")) {str "s"} = 0 := by
  simp only [owedCheck, rangeCheck, Multiset.singleton_bind]
  rw [guardCount_of_not_meta (by decide : ¬ MetaName (Ty.sym "Number")),
    count_class declarations (show valueClass (.string "s") = some "String" from rfl)]
  simp

def equations : String → List Equation
  | "k" => [⟨[.var "x"], .enter "u" [.var "x"]⟩]
  | "u" => [⟨[.var "x"], .enter "g" [.var "x"]⟩]
  | "g" => [⟨[.var "x"], .const (str "s")⟩]
  | _ => []

theorem g_step (oracle : String → List Atom → Multiset Atom) :
    stepsOf env equations "g" oracle [num 1] = {Sum.inl (str "s")} := by
  simp [stepsOf, equations, Pat.matchAll, Pat.match, Expr.evalOut, Expr.eval]

theorem u_step (oracle : String → List Atom → Multiset Atom) :
    stepsOf env equations "u" oracle [num 1] = {Sum.inr ("g", [num 1])} := by
  simp [stepsOf, equations, Pat.matchAll, Pat.match, Expr.evalOut, Expr.evalAll, Expr.eval]

theorem k_step (oracle : String → List Atom → Multiset Atom) :
    stepsOf env equations "k" oracle [num 1] = {Sum.inr ("u", [num 1])} := by
  simp [stepsOf, equations, Pat.matchAll, Pat.match, Expr.evalOut, Expr.evalAll, Expr.eval]

theorem petta_g (grounded : String → Bool) (fuel : Nat) :
    ChainRegion.run declarations grounded rows (stepsOf env equations)
      (fuel + 1) (some (.sym "Number")) "g" [num 1] = 0 := by
  rw [ChainRegion.run_accepted declarations grounded rows _ fuel (some (.sym "Number"))
    "g" [num 1] (q := none) (by decide) (by decide), g_step]
  simpa using rejects_string grounded

theorem petta_u (grounded : String → Bool) (fuel : Nat) :
    ChainRegion.run declarations grounded rows (stepsOf env equations)
      (fuel + 2) (some (.sym "Number")) "u" [num 1] = 0 := by
  rw [ChainRegion.run_accepted declarations grounded rows _ (fuel + 1) (some (.sym "Number"))
    "u" [num 1] (q := none) (by decide) (by decide), u_step]
  simpa using petta_g grounded fuel

theorem petta_k (grounded : String → Bool) (fuel : Nat) :
    protocolRunS declarations grounded (sigOf rows) (stepsOf env equations)
      (fuel + 3) "k" [num 1] = 0 := by
  rw [← ChainRegion.program_run_eq_protocol declarations grounded declarations_functional
    rows env equations (fuel + 3) "k" [num 1]]
  rw [ChainRegion.run_accepted declarations grounded rows _ (fuel + 2) none
    "k" [num 1] (q := some (.sym "Number")) (by decide) (by decide), k_step]
  simpa using petta_u grounded fuel

/-- The analogous HE source preserves the string through the enclosing
Number-declared head. This refutes importing PeTTa's debt-intersection law
as an unconditional HE law. -/
theorem dialects_differ (grounded : String → Bool) (fuel : Nat) :
    protocolRunS declarations grounded (sigOf rows) (stepsOf env equations)
        (fuel + 3) "k" [num 1] = 0 ∧
      HEReturns.Controls.answersAt HEReturns.Controls.castSpace
        (.expression [.symbol "k", num 1]) Atom.undefinedType (fuel + 15) = [str "s"] := by
  exact ⟨petta_k grounded fuel,
    HEReturns.Controls.reply_through_undefined_range (fuel + 15) (by omega)⟩

/-- A declared HE range alone is not a successful-result classification
certificate. A concrete returned string still has its actual String type. -/
theorem declaration_does_not_classify_every_result (fuel : Nat) :
    HEReturns.Controls.answersAt HEReturns.Controls.castSpace
        (.expression [.symbol "k", num 1]) Atom.undefinedType (fuel + 15) = [str "s"] ∧
      Mettapedia.Languages.MeTTa.HE.getAtomTypes HEReturns.Controls.castSpace (str "s") =
        [.symbol "String"] := by
  exact ⟨HEReturns.Controls.reply_through_undefined_range (fuel + 15) (by omega), rfl⟩

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.ReturnPolicySeparation
