import Mettapedia.Languages.MeTTa.OSLFCore.Atom
import Mettapedia.Languages.MeTTa.TypeSchemeActivation
import Mettapedia.Machines.OrderedGuardPipeline
import Mettapedia.Machines.RevisionedQueryFacts
import Mettapedia.GSLT.LanguageDef.CommittedFallbackFusion

/-!
# PeTTa call plans and qualified guard optimization

The demand rules transcribe the base interface `petta_type_policy`: literal
`Atom` retains source, literal Undefined and `_` translate without checking,
and every other formal translates and guards. They are chosen before binding.
Body holding belongs to the whole declaration family, independently of the
selected arrow's result guard. Partial calls keep that result guard.

The control laws use the existing scoped call continuations. Pure guards are
ordered refinements, not Booleans. Admission of a full relational query is the
separate cursor law from `CommittedFallbackFusion`; arbitrary classifiers are
not claimed pure or memoizable here. These proofs do not implement the native
compiler or verify C allocation, family deduplication, or complete inference.

Mercury's checked mode and determinism declarations motivate specialization
claims, not a semantic license to reorder alternatives or prune duplicates.
PeTTa retains its own ordered, effect-sensitive operational semantics.
See https://www.mercurylang.org/information/doc-latest/mercury_reference_manual/Determinism.html.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.CallGuardOptimization

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Machines ScopedCommit OrderedGuardPipeline

inductive Demand where
  | raw | translate | checked
  deriving DecidableEq, Repr

/-- Operational source judgment on the literal declaration, not its future
substitution instance. -/
inductive LiteralDemand : Atom → Demand → Prop where
  | raw : LiteralDemand (.symbol "Atom") .raw
  | undefined : LiteralDemand (.symbol "%Undefined%") .translate
  | underscore : LiteralDemand (.symbol "_") .translate
  | checked {formal : Atom} :
      formal ≠ .symbol "Atom" → formal ≠ .symbol "%Undefined%" →
      formal ≠ .symbol "_" → LiteralDemand formal .checked

def demand (formal : Atom) : Demand :=
  if formal = .symbol "Atom" then .raw
  else if formal = .symbol "%Undefined%" ∨ formal = .symbol "_" then .translate
  else .checked

theorem demand_sound (formal : Atom) : LiteralDemand formal (demand formal) := by
  unfold demand
  split
  · rename_i same; subst formal; exact .raw
  · rename_i notAtom
    split
    · rename_i translated
      rcases translated with same | same <;> subst formal
      · exact .undefined
      · exact .underscore
    · rename_i checked
      exact .checked notAtom (fun h => checked (.inl h)) (fun h => checked (.inr h))

theorem demand_complete {formal : Atom} {mode : Demand}
    (source : LiteralDemand formal mode) : demand formal = mode := by
  cases source <;> simp_all [demand]

structure Signature where
  domains : List Atom
  codomain : Atom
  deriving DecidableEq, Repr

/-- A signature is one scheme: domains and codomain share variable names. -/
def Signature.scheme (signature : Signature) : Atom :=
  .expression (.symbol "->" :: (signature.domains ++ [signature.codomain]))

def renameSignature (names : String → String) (signature : Signature) : Signature :=
  ⟨signature.domains.map (TypeSchemeActivation.rename names),
    TypeSchemeActivation.rename names signature.codomain⟩

theorem rename_signature_scheme (names : String → String) (signature : Signature) :
    (renameSignature names signature).scheme = TypeSchemeActivation.rename names signature.scheme := by
  simp [Signature.scheme, renameSignature, TypeSchemeActivation.rename]

/-- Fresh renaming keeps the literal shape of a demand. This law does not
apply to substitution, which may bind a formal variable to literal Atom. -/
theorem demand_rename (names : String → String) (formal : Atom) :
    demand (TypeSchemeActivation.rename names formal) = demand formal := by
  cases formal <;> simp [demand, TypeSchemeActivation.rename]

structure Plan where
  signature : Signature
  demands : List Demand
  guardResult : Bool
  holdResult : Bool
  deriving DecidableEq, Repr

def compile (signature : Signature) : Plan :=
  ⟨signature, signature.domains.map demand,
    demand signature.codomain == .checked, demand signature.codomain == .raw⟩

def holdBody (family : List Signature) : Bool :=
  family.any (fun signature => demand signature.codomain == .raw)

def supported (signature : Signature) (supplied : Nat) : Bool :=
  decide (supplied ≤ signature.domains.length)

theorem compile_rename (names : String → String) (signature : Signature) :
    (compile (renameSignature names signature)).demands = (compile signature).demands ∧
      (compile (renameSignature names signature)).guardResult = (compile signature).guardResult ∧
      (compile (renameSignature names signature)).holdResult = (compile signature).holdResult := by
  simp [compile, renameSignature, List.map_map, Function.comp_def, demand_rename]

theorem family_holding_rename (names : String → String) (family : List Signature) :
    holdBody (family.map (renameSignature names)) = holdBody family := by
  simp [holdBody, renameSignature, demand_rename, Function.comp_def]

theorem partial_support_rename (names : String → String) (signature : Signature)
    (supplied : Nat) :
    supported (renameSignature names signature) supplied = supported signature supplied := by
  simp [supported, renameSignature]

/-- The separately proved finite-support activation contract supplies hygiene,
while the interface retains pre-binding demand and result classifications. -/
theorem hygienic_signature_activation (signature : Signature) (occupied : List String)
    (activation : TypeSchemeActivation.Activation signature.scheme occupied) :
    (renameSignature activation.names signature).scheme = activation.value ∧
      (∀ name ∈ TypeSchemeActivation.freeVars (renameSignature activation.names signature).scheme,
        name ∉ occupied) ∧
      (compile (renameSignature activation.names signature)).demands = (compile signature).demands ∧
      (compile (renameSignature activation.names signature)).guardResult = (compile signature).guardResult := by
  have schemeEq := rename_signature_scheme activation.names signature
  refine ⟨schemeEq, ?_, (compile_rename activation.names signature).1,
    (compile_rename activation.names signature).2.1⟩
  rw [schemeEq]
  exact activation.no_capture

theorem compiled_demands_have_the_source_judgment (signature : Signature) :
    List.Forall₂ LiteralDemand signature.domains (compile signature).demands := by
  change List.Forall₂ LiteralDemand signature.domains (signature.domains.map demand)
  induction signature.domains with
  | nil => exact .nil
  | cons formal formals ih =>
      exact .cons (demand_sound formal) ih

theorem compiled_arity (signature : Signature) :
    (compile signature).demands.length = signature.domains.length := by
  simp [compile]

/-- Activating the whole signature keeps its source-classified demands.
The instantiator must separately preserve sharing and freshness; its binding
action is not allowed to reclassify the demands. -/
def activate (instantiate : Signature → Signature) (plan : Plan) : Plan :=
  { plan with signature := instantiate plan.signature }

theorem activation_retains_literal_demands (instantiate : Signature → Signature)
    (signature : Signature) :
    (activate instantiate (compile signature)).demands = signature.domains.map demand := rfl

theorem activation_retains_result_guard (instantiate : Signature → Signature)
    (signature : Signature) :
    (activate instantiate (compile signature)).guardResult = (compile signature).guardResult := rfl

theorem partial_support (signature : Signature) (supplied : Nat) :
    supported signature supplied = true ↔ supplied ≤ signature.domains.length := by
  simp [supported]

theorem atom_in_family_holds_body (family : List Signature) (signature : Signature)
    (member : signature ∈ family) (atomResult : signature.codomain = .symbol "Atom") :
    holdBody family = true := by
  apply List.any_eq_true.mpr
  exact ⟨signature, member, by simp [demand, atomResult]⟩

variable {State World Result : Type}

/-- The caller supplies translation as its existing control body. Raw demand
must not execute that body. Guarding follows translation, never precedes it. -/
def argument (mode : Demand) (translate : Body State World)
    (check : Guard State) (next : Body State World) : Body State World :=
  match mode with
  | .raw => next
  | .translate => andThen translate next
  | .checked => andThen translate (guard check next)

def result (plan : Plan) (check : Guard State) (next : Body State World) :
    Body State World := if plan.guardResult then guard check next else next

theorem raw_argument_skips_translation (translate : Body State World)
    (check : Guard State) (next : Body State World) (state : State)
    (success : Success State World Result) (failure saved : Failure World Result)
    (world : World) :
    eval (argument .raw translate check next) state success failure saved world =
      eval next state success failure saved world := rfl

theorem unchecked_argument_still_translates (translate next : Body State World)
    (check : Guard State) (state : State)
    (success : Success State World Result) (failure saved : Failure World Result)
    (world : World) :
    eval (argument .translate translate check next) state success failure saved world =
      eval translate state (fun prepared pending world =>
        eval next prepared success pending saved world) failure saved world :=
  eval_andThen translate next state success failure saved world

theorem checked_argument_orders_translation_before_refinement
    (translate next : Body State World) (check : Guard State) (state : State)
    (success : Success State World Result) (failure saved : Failure World Result)
    (world : World) :
    eval (argument .checked translate check next) state success failure saved world =
      eval translate state (fun prepared pending world =>
        eval (guard check next) prepared success pending saved world)
        failure saved world :=
  eval_andThen translate (guard check next) state success failure saved world

/-- Keeping typing on a compiled call does not require entering a general
equation dispatcher: any replacement body with the same continuation meaning
can be enclosed by the existing ordered guards. This is a component law, not
an admission certificate for a particular native body. -/
theorem typed_body_refinement (stages : List (Guard State))
    (source target : Body State World)
    (bodyExact : ∀ state (success : Success State World Result) failure saved world,
      eval source state success failure saved world =
        eval target state success failure saved world)
    (state : State) (success : Success State World Result)
    (failure saved : Failure World Result) (world : World) :
    eval (pipeline stages source) state success failure saved world =
      eval (pipeline stages target) state success failure saved world := by
  rw [pipeline_fusion, pipeline_fusion]
  simp only [OrderedGuardPipeline.guard, eval]
  have folded : ∀ states : List State,
      states.foldr (fun state pending => fun world =>
        eval source state success pending saved world) failure =
      states.foldr (fun state pending => fun world =>
        eval target state success pending saved world) failure := by
    intro states
    induction states with
    | nil => rfl
    | cons state states ih =>
        simp only [List.foldr_cons, ih]
        funext world
        exact bodyExact state success _ saved world
  exact congrFun (folded (refinements stages state)) world

namespace Controls

def unchecked : Signature := ⟨[.symbol "%Undefined%"], .symbol "%Undefined%"⟩
def held : Signature := ⟨[.symbol "Number"], .symbol "Atom"⟩
def binaryNumber : Signature := ⟨[.symbol "Number", .symbol "Number"], .symbol "Number"⟩
def variableDomain : Signature := ⟨[.var "a"], .var "a"⟩

theorem undefined_is_not_raw : demand (.symbol "%Undefined%") = .translate := by decide

theorem variable_bound_to_atom_cannot_be_reclassified :
    (activate (fun _ => held) (compile variableDomain)).demands = [.checked] ∧
      demand (.symbol "Atom") = .raw := by decide

theorem family_holding_is_not_selected_guarding :
    holdBody [held, unchecked] = true ∧
      (compile unchecked).holdResult = false ∧
      (compile unchecked).guardResult = false := by decide

theorem authored_partial_keeps_its_result_check :
    supported binaryNumber 1 = true ∧ (compile binaryNumber).guardResult = true := by decide

def translation : Body Nat Nat := .effect (fun _ world => (6, world + 1)) .done
def reject : Guard Nat := fun _ => []

theorem no_guard_does_not_mean_no_evaluation :
    run (argument .translate translation reject .done) 0 0 = ([6], 1) ∧
      run (argument .raw translation reject .done) 0 0 = ([0], 0) := ⟨rfl, rfl⟩

theorem argument_failure_keeps_translation_effect :
    run (argument .checked translation reject .done) 0 0 = ([], 1) := rfl

end Controls

end Mettapedia.Languages.MeTTa.PeTTa.CallGuardOptimization
