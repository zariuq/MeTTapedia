import Mettapedia.GSLT.LanguageDef.CettaWireEquality
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.NativeSubstitution
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.UniverseProfiles
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.ExecutableWrittenChecking

/-!
# Exact wire decoding of annotated dependent sources

This adapter reads the native constructor grammar into `NativeSyntax.Raw`,
then recovers scope through the independently defined `ATm` decoder. Written
lambda domains survive both maps. Declaration names are simple names, as
native symbol addresses are strings; hierarchical Lean names are refused
rather than flattened. Universe expressions retain parameters, successor and
maximum. The opaque legacy head has its separate spelling.

The carrier is the existing physical S-expression carrier. These theorems do
not assert a parser/rendering round trip, integer-representation bounds, or
the correctness of the C implementation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativeDependentSourceWire

open Mettapedia.GSLT.LanguageDef.CettaWire
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation
open Mettapedia.TypeTheory.UniverseLevel

abbrev Wire := Term
abbrev Raw := NativeSyntax.Raw Tower.Head

def nameText : DeclName → Option String
  | .str .anonymous text => some text
  | _ => none

theorem nameText_exact {name : DeclName} {text : String}
    (encoded : nameText name = some text) : Lean.Name.mkSimple text = name := by
  unfold nameText at encoded
  split at encoded
  · cases encoded; rfl
  · cases encoded

def encodeLevel : LevelExpr Nat → Wire
  | .const level => .application "LevelConst" [.natural level]
  | .param parameter => .application "LevelParam" [.natural parameter]
  | .succ level => .application "LevelSucc" [encodeLevel level]
  | .max first second => .application "LevelMax" [encodeLevel first, encodeLevel second]

def decodeLevel : Wire → Option (LevelExpr Nat)
  | .application "LevelConst" [.natural level] => some (.const level)
  | .application "LevelParam" [.natural parameter] => some (.param parameter)
  | .application "LevelSucc" [level] => LevelExpr.succ <$> decodeLevel level
  | .application "LevelMax" [first, second] => do
      return .max (← decodeLevel first) (← decodeLevel second)
  | _ => none
termination_by term => sizeOf term

@[simp] theorem decodeLevel_encodeLevel (level : LevelExpr Nat) :
    decodeLevel (encodeLevel level) = some level := by
  induction level <;> simp_all [encodeLevel, decodeLevel]

def encode : Raw → Option Wire
  | .var index => some (.application "idx" [.natural index])
  | .const name => do return .application "DeclConst" [.symbol (← nameText name)]
  | .head .legacyGround => some (.symbol "U0")
  | .head (.sort level) => some (.application "Sort" [encodeLevel level])
  | .pi domain body => do return .application "Pi" [← encode domain, ← encode body]
  | .sigma domain body => do return .application "Sigma" [← encode domain, ← encode body]
  | .id carrier left right => do return .application "Id" [← encode carrier, ← encode left, ← encode right]
  | .lamBare body => do return .application "Lam" [← encode body]
  | .lamTyped domain body => do return .application "Lam" [← encode domain, ← encode body]
  | .app function argument => do return .application "App" [← encode function, ← encode argument]
  | .pair first second => do return .application "Pair" [← encode first, ← encode second]
  | .fst pair => do return .application "Fst" [← encode pair]
  | .snd pair => do return .application "Snd" [← encode pair]
  | .refl subject => do return .application "Refl" [← encode subject]

def decode : Wire → Option Raw
  | .symbol "U0" => some (.head .legacyGround)
  | .application "Sort" [level] => do return .head (.sort (← decodeLevel level))
  | .application "idx" [.natural index] => some (.var index)
  | .application "DeclConst" [.symbol name] => some (.const (.mkSimple name))
  | .application "Pi" [domain, body] => do return .pi (← decode domain) (← decode body)
  | .application "Sigma" [domain, body] => do return .sigma (← decode domain) (← decode body)
  | .application "Id" [carrier, left, right] => do return .id (← decode carrier) (← decode left) (← decode right)
  | .application "Lam" [body] => do return .lamBare (← decode body)
  | .application "Lam" [domain, body] => do return .lamTyped (← decode domain) (← decode body)
  | .application "App" [function, argument] => do return .app (← decode function) (← decode argument)
  | .application "Pair" [first, second] => do return .pair (← decode first) (← decode second)
  | .application "Fst" [pair] => do return .fst (← decode pair)
  | .application "Snd" [pair] => do return .snd (← decode pair)
  | .application "Refl" [subject] => do return .refl (← decode subject)
  | _ => none
termination_by term => sizeOf term

/-- All successfully lowered sources read back exactly, with annotations. -/
theorem decode_encode {raw : Raw} {wire : Wire} (encoded : encode raw = some wire) :
    decode wire = some raw := by
  induction raw generalizing wire with
  | var index => cases encoded; simp [decode]
  | const name =>
      cases named : nameText name with
      | none => simp [encode, named] at encoded
      | some text =>
          simp [encode, named] at encoded
          subst wire
          simp [decode, nameText_exact named]
  | head value => cases value <;> cases encoded <;> simp [decode]
  | pi domain body ihDomain ihBody =>
      cases hd : encode domain <;> cases hb : encode body <;> simp [encode, hd, hb] at encoded
      subst wire
      simp [decode, ihDomain hd, ihBody hb]
  | sigma domain body ihDomain ihBody =>
      cases hd : encode domain <;> cases hb : encode body <;> simp [encode, hd, hb] at encoded
      subst wire
      simp [decode, ihDomain hd, ihBody hb]
  | id carrier left right ihCarrier ihLeft ihRight =>
      cases hc : encode carrier <;> cases hl : encode left <;> cases hr : encode right <;>
        simp [encode, hc, hl, hr] at encoded
      subst wire
      simp [decode, ihCarrier hc, ihLeft hl, ihRight hr]
  | lamBare body ih =>
      cases hb : encode body <;> simp [encode, hb] at encoded
      subst wire
      simp [decode, ih hb]
  | lamTyped domain body ihDomain ihBody =>
      cases hd : encode domain <;> cases hb : encode body <;> simp [encode, hd, hb] at encoded
      subst wire
      simp [decode, ihDomain hd, ihBody hb]
  | app function argument ihFunction ihArgument =>
      cases hf : encode function <;> cases ha : encode argument <;> simp [encode, hf, ha] at encoded
      subst wire
      simp [decode, ihFunction hf, ihArgument ha]
  | pair first second ihFirst ihSecond =>
      cases hf : encode first <;> cases hs : encode second <;> simp [encode, hf, hs] at encoded
      subst wire
      simp [decode, ihFirst hf, ihSecond hs]
  | fst pair ih =>
      cases hp : encode pair <;> simp [encode, hp] at encoded
      subst wire
      simp [decode, ih hp]
  | snd pair ih =>
      cases hp : encode pair <;> simp [encode, hp] at encoded
      subst wire
      simp [decode, ih hp]
  | refl subject ih =>
      cases hs : encode subject <;> simp [encode, hs] at encoded
      subst wire
      simp [decode, ih hs]

theorem encoded_injective {first second : Raw} {wire : Wire}
    (firstEncoded : encode first = some wire) (secondEncoded : encode second = some wire) :
    first = second := by
  have firstDecoded := decode_encode firstEncoded
  have secondDecoded := decode_encode secondEncoded
  exact Option.some.inj (firstDecoded.symm.trans secondDecoded)

def decodeScoped (n : Nat) (wire : Wire) : Option (ATm Tower.Head n) := do
  NativeSyntax.decode n (← decode wire)

def lower {n : Nat} (source : ATm Tower.Head n) : Option Wire :=
  encode (NativeSyntax.encode source)

theorem lower_decode {n : Nat} {source : ATm Tower.Head n} {wire : Wire}
    (lowered : lower source = some wire) : decodeScoped n wire = some source := by
  simp [decodeScoped, decode_encode lowered, NativeSyntax.decode_encode]

theorem lower_injective {n : Nat} {first second : ATm Tower.Head n} {wire : Wire}
    (firstLowered : lower first = some wire) (secondLowered : lower second = some wire) :
    first = second :=
  Option.some.inj ((lower_decode firstLowered).symm.trans (lower_decode secondLowered))

/-- The decoded wire's numeric scope is exactly scope recovery. -/
theorem scope_exact {n : Nat} {wire : Wire} {raw : Raw} (decoded : decode wire = some raw) :
    (decodeScoped n wire).isSome = NativeSyntax.checkScope n raw := by
  simp [decodeScoped, decoded, NativeSyntax.decode_isSome]

/-- Beta substitution on decoded native indices agrees with the independent
annotated substitution, including written lambda domains. -/
theorem substitution_exact {n : Nat} (argument : ATm Tower.Head n)
    (body : ATm Tower.Head (n+1)) :
    NativeSyntax.decode n (NativeSyntax.substituteZero (NativeSyntax.encode argument) 0
      (NativeSyntax.encode body)) = some (ATm.inst0 argument body) :=
  NativeSyntax.substituteZero_decodes argument body

open TypedEquality.Normalization.ExecutableWrittenChecking (SourceContext)

/-- Native contexts put the newest domain first. That domain is read at the
length of its predecessor, outside the new binder. -/
def lowerContext : {n : Nat} → SourceContext Tower.Head n → Option Wire
  | _, .nil => some (.symbol "PrimeCtxNil")
  | _, .snoc prior domain => do
      return .application "PrimeCtxCons" [← lower domain, ← lowerContext prior]

def decodeContext : (n : Nat) → Wire → Option (SourceContext Tower.Head n)
  | 0, .symbol "PrimeCtxNil" => some .nil
  | n+1, .application "PrimeCtxCons" [domain, prior] => do
      return .snoc (← decodeContext n prior) (← decodeScoped n domain)
  | _, _ => none

theorem decodeContext_lowerContext {n : Nat} {context : SourceContext Tower.Head n}
    {wire : Wire} (lowered : lowerContext context = some wire) :
    decodeContext n wire = some context := by
  induction context generalizing wire with
  | nil => cases lowered; rfl
  | snoc prior domain ih =>
      cases hd : lower domain <;> cases hc : lowerContext prior <;>
        simp [lowerContext, hd, hc] at lowered
      subst wire
      simp [decodeContext, ih hc, lower_decode hd]

/-- The source term and context are both carried by the scoped native input. -/
def lowerScoped {n : Nat} (context : SourceContext Tower.Head n) (term : ATm Tower.Head n) :
    Option Wire := do
  return .application "PrimeScoped" [← lowerContext context, ← lower term]

def decodeInput (n : Nat) : Wire →
    Option (SourceContext Tower.Head n × ATm Tower.Head n)
  | .application "PrimeScoped" [context, term] => do
      return (← decodeContext n context, ← decodeScoped n term)
  | _ => none

theorem decodeInput_lowerScoped {n : Nat} {context : SourceContext Tower.Head n}
    {term : ATm Tower.Head n} {wire : Wire} (lowered : lowerScoped context term = some wire) :
    decodeInput n wire = some (context, term) := by
  cases hc : lowerContext context <;> cases ht : lower term <;>
    simp [lowerScoped, hc, ht] at lowered
  subst wire
  simp [decodeInput, decodeContext_lowerContext hc, lower_decode ht]

/-- The scope of a lowered domain is its predecessor's length. A variable in
the new slot itself cannot serve as that slot's domain. -/
theorem self_scoped_domain_refused :
    decodeContext 1 (.application "PrimeCtxCons"
      [.application "idx" [.natural 0], .symbol "PrimeCtxNil"]) = none := by
  decide +kernel

theorem quoted_declaration_is_not_a_symbol :
    decode (.application "DeclConst" [.string "num"]) = none := by decide +kernel

theorem unsupported_constructor_refused :
    decode (.application "PVar" [.natural 0]) = none := by decide +kernel

theorem hierarchical_name_refused : encode (.const `a.b) = none := rfl

theorem dotted_symbol_is_retained :
    decode (.application "DeclConst" [.symbol "a.b"]) =
      some (.const (.mkSimple "a.b")) := by decide +kernel

/-- A declaration view and local variable context are distinct inputs. The
native `PrimeCtxDecl` header contributes no local de Bruijn slot. -/
def lowerContextOver (base : Wire) : {n : Nat} → SourceContext Tower.Head n → Option Wire
  | _, .nil => some base
  | _, .snoc prior domain => do
      return .application "PrimeCtxCons" [← lower domain, ← lowerContextOver base prior]

def decodeContextOver (base : Wire) : (n : Nat) → Wire → Option (SourceContext Tower.Head n)
  | 0, wire => if wire = base then some .nil else none
  | n+1, .application "PrimeCtxCons" [domain, prior] => do
      return .snoc (← decodeContextOver base n prior) (← decodeScoped n domain)
  | _, _ => none

theorem decodeContextOver_lowerContextOver {n : Nat} (base : Wire)
    {context : SourceContext Tower.Head n} {wire : Wire}
    (lowered : lowerContextOver base context = some wire) :
    decodeContextOver base n wire = some context := by
  induction context generalizing wire with
  | nil => cases lowered; simp [decodeContextOver]
  | snoc prior domain ih =>
      cases hd : lower domain <;> cases hc : lowerContextOver base prior <;>
        simp [lowerContextOver, hd, hc] at lowered
      subst wire
      simp [decodeContextOver, ih hc, lower_decode hd]

def lowerScopedOver {n : Nat} (base : Wire)
    (context : SourceContext Tower.Head n) (term : ATm Tower.Head n) : Option Wire := do
  return .application "PrimeScoped" [← lowerContextOver base context, ← lower term]

def decodeInputOver (base : Wire) (n : Nat) : Wire →
    Option (SourceContext Tower.Head n × ATm Tower.Head n)
  | .application "PrimeScoped" [context, term] => do
      return (← decodeContextOver base n context, ← decodeScoped n term)
  | _ => none

theorem decodeInputOver_lowerScopedOver {n : Nat} (base : Wire)
    {context : SourceContext Tower.Head n} {term : ATm Tower.Head n} {wire : Wire}
    (lowered : lowerScopedOver base context term = some wire) :
    decodeInputOver base n wire = some (context, term) := by
  cases hc : lowerContextOver base context <;> cases ht : lower term <;>
    simp [lowerScopedOver, hc, ht] at lowered
  subst wire
  simp [decodeInputOver, decodeContextOver_lowerContextOver base hc, lower_decode ht]

/-- A closed declaration signature, in authored order. Its formation and
computation rules are checked separately by the selected semantic package. -/
def lowerDeclarations : List (DeclName × ATm Tower.Head 0) → Option Wire
  | [] => some (.symbol "PrimeCtxNil")
  | declaration :: declarations => do
      return .application "PrimeCtxDecl"
        [.application "DeclConst" [.symbol (← nameText declaration.1)],
          ← lower declaration.2, ← lowerDeclarations declarations]

/-- Headers are outermost-first: the first entry is the newest declaration. -/
def declarationsLookup : List (DeclName × ATm Tower.Head 0) → DeclName → Option (Tm Tower.Head 0)
  | [], _ => none
  | declaration :: declarations, name =>
      if name = declaration.1 then some declaration.2.erase else declarationsLookup declarations name

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativeDependentSourceWire
