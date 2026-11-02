import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlSourceLowering
import Mettapedia.Languages.OCaml.NamedPatternCompleteness
import Mettapedia.Languages.OCaml.NamedPatternCounts
import Mettapedia.Data.List.NamedEnvironment

/-! The actual source pattern elaborator retains one named pattern before
erasure. Every anonymous matcher answer reconstructs its source name/value
bindings; pushing them agrees with the compiler's name-index lookup. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlSourceLowering

open Mettapedia.Languages
open Mettapedia.Languages.OCaml

theorem patternFuel_readback {fuel : Nat} {context : Context} {source : SourcePacket.Packet}
    {pattern : MatchPattern} {names : List String}
    (built : patternFuel fuel context source = .ok (pattern, names)) :
    ∃ named, namedPatternFuel fuel context source = .ok named ∧ named.erase = pattern ∧ named.names = names := by
  unfold patternFuel at built
  cases produced : namedPatternFuel fuel context source with
  | error reason => simp [produced, Except.map] at built
  | ok named =>
    have same : (named.erase, named.names) = (pattern, names) := by simpa only [produced, Except.map, Except.ok.injEq] using built
    exact ⟨named, rfl, (Prod.mk.inj same).1, (Prod.mk.inj same).2⟩

theorem patternFuel_binding_count {fuel : Nat} {context : Context} {source : SourcePacket.Packet}
    {pattern : MatchPattern} {names : List String}
    (built : patternFuel fuel context source = .ok (pattern, names)) : names.length = pattern.binders := by
  obtain ⟨named, _, rfl, rfl⟩ := patternFuel_readback built
  exact (NamedPattern.erase_binders named).symm

theorem patternFuel_matching {fuel : Nat} {context : Context} {source : SourcePacket.Packet}
    {pattern : MatchPattern} {names : List String}
    (built : patternFuel fuel context source = .ok (pattern, names)) :
    ∃ named, namedPatternFuel fuel context source = .ok named ∧
      ∀ value values, matchPattern pattern value = some values ↔
        ∃ bindings, NamedPattern.Matches named value bindings ∧
          bindings.map Prod.fst = names ∧ bindings.map Prod.snd = values := by
  obtain ⟨named, produced, rfl, rfl⟩ := patternFuel_readback built
  refine ⟨named, produced, fun value values => ?_⟩
  constructor
  · intro matched
    obtain ⟨bindings, namedMatch, same⟩ := NamedPattern.erased_match_complete named value values matched
    exact ⟨bindings, namedMatch, NamedPattern.matches_names namedMatch, same⟩
  · rintro ⟨_bindings, namedMatch, _, same⟩
    exact same ▸ NamedPattern.matches_erased namedMatch

theorem resolveName_lookup (context : Context) (entries : List (String × OCaml.Value)) (name : String)
    (aligned : entries.map Prod.fst = context.names) :
    List.NamedEnvironment.lookup? entries name =
      (resolveName? context name).bind (fun index => (entries.map Prod.snd)[index]?) :=
  List.NamedEnvironment.lookup_index_of_names entries context.names name aligned

theorem pattern_push_lookup (context : Context) (entries : List (String × OCaml.Value)) (named : NamedPattern)
    (value : OCaml.Value) (bindings : NamedPattern.Bindings) (name : String)
    (aligned : entries.map Prod.fst = context.names) (matched : NamedPattern.Matches named value bindings) :
    List.NamedEnvironment.lookup? (bindings.reverse ++ entries) name =
      (resolveName? (extendNames context named.names) name).bind
        (fun index => (extend (entries.map Prod.snd) (bindings.map Prod.snd))[index]?) := by
  have names := NamedPattern.matches_names matched
  simpa only [names, aligned, resolveName?, extendNames, extend] using
    List.NamedEnvironment.lookup_push entries bindings name

#print axioms patternFuel_readback
#print axioms patternFuel_binding_count
#print axioms patternFuel_matching
#print axioms resolveName_lookup
#print axioms pattern_push_lookup

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlSourceLowering
