import Mettapedia.Languages.MeTTa.PeTTa.Legacy.ContractTyping.Determinism

/-!
# Contract typing for PeTTa: soundness

The type theory of PeTTa's contract checker (`src/types.pl`) and of its determinism analysis
(`lib/lib_det.pl`), as one development. Behaviour tests, not text, relate the two; the rules
carry the names of the predicates they model.

| Lean | Prolog |
|---|---|
| `Fits` | `typecheck_ok/2`, with `literal_tag/1` and newtypes |
| `primTest` | `fast_test/3` for `Number`, `String`, `Bool` |
| `Est`, `Establishes` | `est/2`, `established/2` |
| `Conflict`, `MayShare`, `Constructed` | `consistent/2` and `conflict/2`, `may_share_values/2`, `constructed/2` |
| `classify`, `boundary` | `type_boundary/4` (`boundary/6`, `value_established/2`, `nominal/1`) |
| `rigidVars`, `bodyView` | `body_contract/4` |
| `representation_declaration_conflict` | `representation_declaration/2` |
| `Checker.test`, `Checker.est` | `typecheck_ok/2`, `established/2` |
| `Checker.passes` | `type_boundary_args/4`: instance `T` for establishment, declared `K` for the check |
| `Step.check` with retention | `typecheck_or_error/2` with `retain_open/2` |
| `Checker.callContract` | `contract_call/5`, `dynamic_call/4` |
| `Checker.compiledCall`, `Route` | `type_call/6`, `type_closure_call/6`, `type_overload/8` |
| `Checker.singleEntry` | `contract_call(params(_), ...)` with the clauses' result checks |
| `Checker.brand` | `(brand N E)`, `newtype_representation/2` |
| `Grade`: `seq`, `choice`, `join`, `once` | `seq/3`, `choice/3`, `join/3`, `once_grade/2` |
| `infer`, `Fn.grade`, `valueType` | `grade/3`, `function_grade/5`, `value_type/2` |
| `coverN`, `constructors`, `specialize`, `defaultRows` | `covers/2`, `constructors/2`, `specialize/4`, `default_rows/2` |

The theorems whose axioms are printed below are the headline; `compiled_call_erasure` and
`det_validation_covers` compose them.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Legacy.ContractTyping

open Mettapedia.Machines.AnswerCardinality
open Mettapedia.Languages.MeTTa.PeTTa.CheckedCardinality (Declaration)

universe u

/-- A compiled call that raises no type error computes what its body computes, followed by its
continuation with checks erased: compilation on any route, then erasure of every check. -/
theorem compiled_call_erasure {sig : Sig} {W : Type u} (chk : Checker sig) (r : Route)
    (σ : Nat → Ty) (decls : List Decl) (body : Bindings → W → List Bindings × W) {args : List Arg}
    (hargs : ∀ a ∈ args, a.Sound sig) (out : Term) {ps' ps : List (Step W)} (hps : Erases ps' ps)
    (retain : Bool) (l : Local) (w : W) {res : List Bindings × W}
    (h : exec retain (chk.compiledCall r σ decls body args out ++ ps) l w = .ok res) :
    exec retain (.run body :: ps') l w = .ok res := by
  rw [chk.contract_route_independent r σ decls body hargs out ps retain l w] at h
  exact erasure_preserves_observations (.drop _ (.keep _ (.drop _ hps))) retain l w h

/-- Determinism validated with `covers/2`: its coverage test is sound, so the heads of a
committing function, and the patterns of `let` and `case`, are exhaustive where it says so. -/
theorem det_validation_covers {sig : Sig} (chk : Checker sig) (k : Nat) (P : String → Fn)
    (D : String → Declaration) (hv : Validated (coverN sig k) P D)
    (hcl : ClosuresRespect P D chk) (n : Nat) (f : String) (vs as : List Term)
    (h : call P chk n f vs = some as) : Allows (D f).grade as.length :=
  det_validation_sound (coverN sig k) P D chk hv (coverN_sound k) hcl n f vs as h

#print axioms establishes_sound
#print axioms inst_evidence_stable
#print axioms compat_evidence_unstable
#print axioms classify_exact_sound
#print axioms classify_conflict_sound
#print axioms representation_declaration_conflict
#print axioms Conflict.atomic_apart
#print axioms union_branch_fails
#print axioms list_conflict_nil
#print axioms arrow_conflict_component
#print axioms rigid_conflict
#print axioms newtype_conflict
#print axioms Fits.of_subst
#print axioms Checker.contract_route_independent
#print axioms Checker.declared_check_accepts
#print axioms Checker.arrow_conflict_raises
#print axioms Checker.brand_sound
#print axioms erasure_preserves_observations
#print axioms effectful_check_breaks_erasure
#print axioms retained_check_redundant
#print axioms Checker.inst_check_erasable
#print axioms Checker.single_declaration_entry
#print axioms OpenAlias.open_alias_needs_retention
#print axioms coverN_sound
#print axioms det_validation_sound
#print axioms compiled_call_erasure
#print axioms det_validation_covers

end Mettapedia.Languages.MeTTa.PeTTa.Legacy.ContractTyping
