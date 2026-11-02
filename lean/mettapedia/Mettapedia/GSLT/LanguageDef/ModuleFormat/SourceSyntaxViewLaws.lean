import Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceSyntax

/-! A source description is recovered from its actual grammar elaboration
and its declared lexical payload. The payload codec's round-trip theorem
connects decoding to that reply without treating quotation as authority. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceSyntax

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.Parsing.ParserProfileSemantics

def lexicalPayload? (library : List (String × ModuleSource.Module)) (module : ModuleSource.Module) : Option Pattern :=
  (replyAt? library module "LexicalProfile" "ReturnLexicalProfile" profileRequest).map (·.2)

theorem lexicalReply_payload (library : List (String × ModuleSource.Module)) (module : ModuleSource.Module) :
    (lexicalReplyAt? library module "ReturnLexicalProfile" profileRequest).map (·.2) =
      (lexicalPayload? library module).bind Portable.readLexicalData? := by
  unfold lexicalReplyAt? lexicalPayload?
  cases replyAt? library module "LexicalProfile" "ReturnLexicalProfile" profileRequest with
  | none => rfl
  | some pair =>
    rcases pair with ⟨entry, data⟩
    cases decoded : Portable.readLexicalData? data <;> simp [bind, Option.bind, pure, decoded]

theorem lexicalReply_of_payload (library : List (String × ModuleSource.Module)) (module : ModuleSource.Module)
    (profile : ParserProfileLayer) (payload : lexicalPayload? library module = some (Portable.lexicalData profile)) :
    (lexicalReplyAt? library module "ReturnLexicalProfile" profileRequest).map (·.2) = some profile := by
  rw [lexicalReply_payload, payload]
  exact Portable.lexicalData_roundtrip profile

theorem description_of_views (library : List (String × ModuleSource.Module)) (module : ModuleSource.Module)
    (grammar : LanguageDef) (profile : ParserProfileLayer)
    (grammarRead : (ModuleSource.elaborate library module).toOption = some grammar)
    (profileRead : (lexicalReplyAt? library module "ReturnLexicalProfile" profileRequest).map (·.2) = some profile) :
    description? library module = some ⟨grammar, profile⟩ := by
  unfold description?
  rw [grammarRead]
  cases read : lexicalReplyAt? library module "ReturnLexicalProfile" profileRequest with
  | none => simp [read] at profileRead
  | some pair =>
    have same : pair.2 = profile := by simpa only [read, Option.map_some, Option.some.injEq] using profileRead
    simp [bind, Option.bind, pure, same]

#print axioms lexicalReply_payload
#print axioms lexicalReply_of_payload
#print axioms description_of_views

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceSyntax
