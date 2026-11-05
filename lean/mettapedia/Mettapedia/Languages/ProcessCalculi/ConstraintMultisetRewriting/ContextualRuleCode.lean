import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleBodySyntax
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualStoredRows
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualGuardMatching
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPublicationPlan
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.StandingRuleRows

/-!
# Whole rule bodies as ordinary contextual syntax values

A quoted-rule constructor records the finite layout of its ports; its
children are precisely the existing term-bearing positions. Decoding only
reconstructs syntax. It neither evaluates the body nor fires a rule.
The representation retains arbitrary base operators and their binders.

Substitution commutes with quotation, and the structural decoder is a left
inverse. Thus one ordinary schema-row read can open an entire rule body
with shared private variables across all its ports.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualRuleCode

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open RuleBodySyntax

inductive CodeOp (S : Signature) (atom : S.Srt) : S.Srt → Type where
  | original {sort : S.Srt} : S.Op sort → CodeOp S atom sort
  | quoted (shape : Layout) : CodeOp S atom atom
  | declaration (mode : StandingRuleRows.Mode) (reusable : List Bool) : CodeOp S atom atom

instance {S : Signature} {atom : S.Srt} [∀ sort, DecidableEq (S.Op sort)] (sort : S.Srt) :
    DecidableEq (CodeOp S atom sort) := by
  intro first second
  cases first with
  | original first =>
      cases second with
      | original second =>
          cases decEq first second with
          | isTrue same => exact isTrue (congrArg CodeOp.original same)
          | isFalse different => exact isFalse (fun same => different (CodeOp.original.inj same))
      | quoted shape => exact isFalse (by intro same; cases same)
      | declaration mode reusable => exact isFalse (by intro same; cases same)
  | quoted first =>
      cases second with
      | original second => exact isFalse (by intro same; cases same)
      | quoted second =>
          cases decEq first second with
          | isTrue same => exact isTrue (congrArg CodeOp.quoted same)
          | isFalse different => exact isFalse (fun same => different (CodeOp.quoted.inj same))
      | declaration mode reusable => exact isFalse (by intro same; cases same)
  | declaration mode reusable =>
      cases second with
      | original second => exact isFalse (by intro same; cases same)
      | quoted shape => exact isFalse (by intro same; cases same)
      | declaration other kinds =>
          exact decidable_of_iff (mode = other ∧ reusable = kinds)
            ⟨fun same => by cases same.1; cases same.2; rfl,
              fun same => CodeOp.declaration.inj same⟩

abbrev codeSignature (S : Signature) (atom : S.Srt) : Signature where
  Srt := S.Srt
  Op := CodeOp S atom
  arity
    | .original head => S.arity head
    | .quoted shape => List.replicate (ContextualWorldScopeLedger.ruleTerms shape).length ([], atom)
    | .declaration _ _ => [([], atom)]

structure Declaration (T : Type) where
  mode : StandingRuleRows.Mode
  plan : ContextualPublication.Plan T

def Declaration.map {T U : Type} (change : T → U) (declaration : Declaration T) : Declaration U where
  mode := declaration.mode
  plan := ⟨declaration.plan.rule.map change, declaration.plan.reusable,
    by simpa only [RuleInstance.map, List.length_map] using declaration.plan.shape⟩

variable {S : Signature} {atom : S.Srt} {V W : Type}
    {source : V → MetaArity (codeSignature S atom)} {next : W → MetaArity (codeSignature S atom)}
    {Γ : Ctx S}

def pack : (values : List (Term (signature (codeSignature S atom) source) Γ atom)) →
    Args (signature (codeSignature S atom) source) (List.replicate values.length ([], atom)) Γ
  | [] => .nil
  | first :: rest => .cons first (pack rest)

def unpack : {count : Nat} → Args (signature (codeSignature S atom) source) (List.replicate count ([], atom)) Γ →
    List (Term (signature (codeSignature S atom) source) Γ atom)
  | 0, .nil => []
  | _ + 1, .cons first rest => first :: unpack rest

theorem unpack_pack (values : List (Term (signature (codeSignature S atom) source) Γ atom)) : unpack (pack values) = values := by
  induction values with
  | nil => rfl
  | cons first rest ih => exact congrArg (List.cons first) ih

theorem unpack_injective {count : Nat} :
    Function.Injective (unpack (source := source) (Γ := Γ) (count := count)) := by
  induction count with
  | zero => intro first second _; cases first; cases second; rfl
  | succ count ih =>
      intro first second same
      cases first with
      | cons first rest =>
          cases second with
          | cons other tail =>
              have parts := List.cons.inj same
              exact congrArg₂ Args.cons parts.1 (ih parts.2)

theorem unpack_cast {first second : Nat}
    (same : List.replicate first ([], atom) = List.replicate second ([], atom))
    (values : Args (signature (codeSignature S atom) source) (List.replicate first ([], atom)) Γ) :
    unpack (castArgsArity (T := signature (codeSignature S atom) source) same values) = unpack values := by
  have lengths : first = second := by simpa only [List.length_replicate] using congrArg List.length same
  subst second
  rfl

theorem unpack_instantiate (assignment : Assignment source next) {count : Nat}
    (values : Args (signature (codeSignature S atom) source) (List.replicate count ([], atom)) Γ) :
    unpack (instantiateArgs assignment values) = (unpack values).map (instantiate assignment) := by
  induction count with
  | zero => cases values; rfl
  | succ count ih =>
      cases values with
      | cons first rest => exact congrArg (List.cons (instantiate assignment first)) (ih rest)

def quote (shape : Layout) (values : List (Term (signature (codeSignature S atom) source) Γ atom))
    (size : values.length = (ContextualWorldScopeLedger.ruleTerms shape).length) :
    Term (signature (codeSignature S atom) source) Γ atom :=
  .op (.inl (.quoted shape))
    (castArgsArity (T := signature (codeSignature S atom) source)
      (congrArg (fun count => List.replicate count ([], atom)) size) (pack values))

def encode (body : RuleInstance (Term (signature (codeSignature S atom) source) Γ atom)) :
    Term (signature (codeSignature S atom) source) Γ atom :=
  quote (layout body) (ContextualWorldScopeLedger.ruleTerms body) (payload_length body).symm

theorem quote_congr {firstShape secondShape : Layout}
    {first second : List (Term (signature (codeSignature S atom) source) Γ atom)}
    (firstSize : first.length = (ContextualWorldScopeLedger.ruleTerms firstShape).length)
    (secondSize : second.length = (ContextualWorldScopeLedger.ruleTerms secondShape).length)
    (shapes : firstShape = secondShape) (values : first = second) :
    quote firstShape first firstSize = quote secondShape second secondSize := by
  cases shapes
  cases values
  rfl

def decode : Term (signature (codeSignature S atom) source) Γ atom →
    Option (RuleInstance (Term (signature (codeSignature S atom) source) Γ atom))
  | .op (.inl (.quoted shape)) arguments =>
      match parse shape (unpack arguments) with
      | some (body, []) => some body
      | _ => none
  | _ => none

theorem decode_encode (body : RuleInstance (Term (signature (codeSignature S atom) source) Γ atom)) :
    decode (encode body) = some body := by
  unfold encode quote decode
  change (match parse (layout body)
    (unpack (castArgsArity (T := signature (codeSignature S atom) source) _
      (pack (ContextualWorldScopeLedger.ruleTerms body)))) with
    | some (result, []) => some result
    | _ => none) = some body
  erw [unpack_cast, unpack_pack]
  have decoded := parse_roundtrip body []
  simp only [List.append_nil] at decoded
  rw [decoded]

theorem encode_injective : Function.Injective (encode (source := source) (Γ := Γ)) := by
  intro first second same
  have decoded := congrArg decode same
  rw [decode_encode, decode_encode] at decoded
  exact Option.some.inj decoded

theorem instantiate_quote (assignment : Assignment source next) (shape : Layout)
    (values : List (Term (signature (codeSignature S atom) source) Γ atom))
    (size : values.length = (ContextualWorldScopeLedger.ruleTerms shape).length) :
    instantiate assignment (quote shape values size) =
      quote shape (values.map (instantiate assignment)) (by simpa only [List.length_map] using size) := by
  change Term.op (S := signature (codeSignature S atom) next) (.inl (.quoted shape)) (instantiateArgs assignment _) =
    Term.op (S := signature (codeSignature S atom) next) (.inl (.quoted shape)) _
  apply congrArg (Term.op (S := signature (codeSignature S atom) next) (.inl (.quoted shape)))
  apply unpack_injective
  erw [unpack_instantiate, unpack_cast, unpack_pack, unpack_cast, unpack_pack]

theorem instantiate_encode (assignment : Assignment source next)
    (body : RuleInstance (Term (signature (codeSignature S atom) source) Γ atom)) :
    instantiate assignment (encode body) = encode (body.map (instantiate assignment)) := by
  exact (instantiate_quote assignment (layout body) (ContextualWorldScopeLedger.ruleTerms body) _).trans
    (quote_congr _ _ (layout_map (instantiate assignment) body).symm
      (ContextualWorldScopeLedger.ruleTerms_map (instantiate assignment) body).symm)

/-- The equality observed by a whole-code read is exactly equality of all
instantiated ports, including guard constructors and multiplicities. -/
theorem instantiated_codes_iff (assignment : Assignment source next)
    (first second : RuleInstance (Term (signature (codeSignature S atom) source) Γ atom)) :
    instantiate assignment (encode first) = instantiate assignment (encode second) ↔
      first.map (instantiate assignment) = second.map (instantiate assignment) := by
  rw [instantiate_encode, instantiate_encode]
  exact ⟨fun same => encode_injective (S := S) (atom := atom) (source := next) (Γ := Γ) same,
    congrArg (encode (S := S) (atom := atom) (source := next) (Γ := Γ))⟩

def encodeDeclaration (declaration : Declaration (Term (signature (codeSignature S atom) source) Γ atom)) :
    Term (signature (codeSignature S atom) source) Γ atom :=
  .op (.inl (.declaration declaration.mode declaration.plan.reusable)) (.cons (encode declaration.plan.rule) .nil)

def decodeDeclaration : Term (signature (codeSignature S atom) source) Γ atom →
    Option (Declaration (Term (signature (codeSignature S atom) source) Γ atom))
  | .op (.inl (.declaration mode reusable)) (.cons body .nil) =>
      match decode body with
      | none => none
      | some rule => if size : reusable.length = rule.produce.length then some ⟨mode, ⟨rule, reusable, size⟩⟩ else none
  | _ => none

theorem decode_encodeDeclaration (declaration : Declaration (Term (signature (codeSignature S atom) source) Γ atom)) :
    decodeDeclaration (encodeDeclaration declaration) = some declaration := by
  unfold encodeDeclaration decodeDeclaration
  change (match decode (encode declaration.plan.rule) with
    | none => none
    | some rule => if size : declaration.plan.reusable.length = rule.produce.length then
        some ⟨declaration.mode, ⟨rule, declaration.plan.reusable, size⟩⟩ else none) = some declaration
  rw [decode_encode]
  dsimp only
  rw [dif_pos declaration.plan.shape]

theorem instantiate_encodeDeclaration (assignment : Assignment source next)
    (declaration : Declaration (Term (signature (codeSignature S atom) source) Γ atom)) :
    instantiate assignment (encodeDeclaration declaration) = encodeDeclaration (declaration.map (instantiate assignment)) := by
  change Term.op (S := signature (codeSignature S atom) next) (.inl (.declaration declaration.mode declaration.plan.reusable))
      (.cons (instantiate assignment (encode declaration.plan.rule)) .nil) = _
  rw [instantiate_encode]
  rfl

theorem code_instances_iff {X : Type} {other : X → MetaArity (codeSignature S atom)}
    (left : Assignment source next) (right : Assignment other next)
    (first : RuleInstance (Term (signature (codeSignature S atom) source) Γ atom))
    (second : RuleInstance (Term (signature (codeSignature S atom) other) Γ atom)) :
    instantiate left (encode first) = instantiate right (encode second) ↔
      first.map (instantiate left) = second.map (instantiate right) := by
  rw [instantiate_encode, instantiate_encode]
  exact ⟨fun same => encode_injective (S := S) (atom := atom) (source := next) (Γ := Γ) same,
    congrArg (encode (S := S) (atom := atom) (source := next) (Γ := Γ))⟩

section Storage

variable {Local Shared : Type} (locals : Local → MetaArity (codeSignature S atom))
    (captures : Shared → MetaArity (codeSignature S atom))
    (body : RuleInstance (Term (signature (codeSignature S atom) (ContextualSelectionViews.source locals captures)) Γ atom))

theorem view_schema (scope : Nat) :
    ContextualStoredRows.viewAt locals captures scope (.schema (encode body)) =
      encode (ContextualFreshening.ruleAt locals captures scope body) :=
  instantiate_encode (ContextualFreshening.assignment locals captures scope) body

theorem decode_schema_view (scope : Nat) :
    decode (ContextualStoredRows.viewAt locals captures scope (.schema (encode body))) =
      some (ContextualFreshening.ruleAt locals captures scope body) := by
  rw [view_schema, decode_encode]

theorem schema_match_iff {Q Next : Type}
    {query : Q → MetaArity (codeSignature S atom)} {next : Next → MetaArity (codeSignature S atom)}
    (caller : Assignment captures next) (arguments : Assignment query next)
    (pattern : RuleInstance (Term (signature (codeSignature S atom) query) Γ atom)) :
    ContextualGuardMatching.Matches locals caller (instantiate arguments (encode pattern)) (.schema (encode body)) ↔
    ∃ extension : ContextualGuardMatching.Extension next,
      ∃ privateBodies : Assignment locals extension.declarations,
        body.map (instantiate (ContextualGuardMatching.instanceAssignment locals privateBodies extension.assignment caller)) =
          pattern.map (instantiate (Assignment.compose extension.assignment arguments)) := by
  constructor
  · rintro ⟨extension, privateBodies, same⟩
    refine ⟨extension, privateBodies, ?_⟩
    erw [← Assignment.instantiate_compose] at same
    exact (code_instances_iff _ _ body pattern).mp same
  · rintro ⟨extension, privateBodies, same⟩
    refine ⟨extension, privateBodies, ?_⟩
    erw [← Assignment.instantiate_compose]
    exact (code_instances_iff _ _ body pattern).mpr same

/-- A private name used in stored code cannot acquire one global view for
two activations. The separation concerns syntax identities, not a failure
to find a unifier between the independently opened bodies. -/
theorem schema_views_ne {first second : Nat} (different : first ≠ second) (name : Local)
    (used : Sum.inl name ∈ support (encode body)) :
    ContextualStoredRows.viewAt locals captures first (.schema (encode body)) ≠
      ContextualStoredRows.viewAt locals captures second (.schema (encode body)) := by
  intro same
  have firstUse : Sum.inl (Mettapedia.Logic.LP.ScopedVar.at first name) ∈
      support (ContextualFreshening.termAt locals captures first (encode body)) := by
    erw [ContextualFreshening.support_termAt]
    exact List.mem_map.mpr ⟨.inl name, used, rfl⟩
  change ContextualFreshening.termAt locals captures first (encode body) =
    ContextualFreshening.termAt locals captures second (encode body) at same
  rw [same] at firstUse
  exact different (ContextualFreshening.local_scope locals captures second (encode body) _ firstUse)

end Storage

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualRuleCode
