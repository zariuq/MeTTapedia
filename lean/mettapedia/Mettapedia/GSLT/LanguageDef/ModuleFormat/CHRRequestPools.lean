import Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRHeadMatchReadout

/-! The literal pools and active identity are read from the actual request
match, before any candidate guard or commit. Later assignment extensions
retain those meanings. In particular, numeric literal slots denote the
closed integer encoding, not an opaque scalar-name reference. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRCompilation.RequestPools

open Mettapedia.Languages.CHR
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding GeneralScopedMatch Match
open GeneralFirstOrderProjection

def scalarDatum (value : Value) (index : Nat) : Pattern :=
  match value with | .integer number => integer number | _ => scalarRef index

structure Read (vocabulary : Vocabulary) (bindings : Bindings) : Prop where
  predicates : ∀ index name, vocabulary.predicates[index]? = some name →
    bindings.lookup (predicateSlot index) = some (predicateRef index)
  scalars : ∀ index value, vocabulary.scalars[index]? = some value →
    bindings.lookup (scalarSlot index) = some (scalarDatum value index)

theorem request_prefix (vocabulary : Vocabulary) (query activeSlot activeId : Nat)
    (source : Rule) (rule : RewriteRule) (known : List Pattern)
    (compiled : compileRule? vocabulary query activeSlot source = some rule)
    {spec : RuleBindingSpec} {ambient : Nat} {captured chosen : ScopedRuleMatching.Assignment}
    (matched : Matches rule spec ambient .left [] 0 [] rule.left
      (request vocabulary query activeId known) captured)
    (later : Extends captured chosen) (roots : GeneralPremise.RootValues ambient chosen) :
    Read vocabulary (ordinary chosen) ∧
      (ordinary chosen).lookup "chr:active" = some (occurrenceRef activeId) := by
  obtain ⟨selected, left, _⟩ := HeadShape.compiled_rule_heads vocabulary query activeSlot source rule compiled
  rw [left] at matched
  simp only [poolPatterns, request, List.cons_append, List.nil_append] at matched
  cases matched with
  | constructor arguments =>
    cases arguments with
    | cons predicates afterPredicates =>
      cases afterPredicates with
      | cons scalars afterScalars =>
        cases afterScalars with
        | cons active afterActive =>
          have predicateRead := named_arguments_readout
            ((List.range vocabulary.predicates.length).map predicateSlot)
            ((List.range vocabulary.predicates.length).map predicateRef)
            (fixed_vector_arguments (by
              simpa only [vector, List.map_map, Function.comp_def] using predicates))
            (scalars.extends.trans (active.extends.trans (afterActive.extends.trans later))) roots
          have scalarRead := named_arguments_readout
            ((List.range vocabulary.scalars.length).map scalarSlot)
            (vocabulary.scalars.zipIdx.map fun entry => scalarDatum entry.1 entry.2)
            (fixed_vector_arguments (by
              convert scalars using 1 <;> simp only [vector, List.map_map, Function.comp_def]
              all_goals
                congr 2
              ))
            (active.extends.trans (afterActive.extends.trans later)) roots
          have activeRead : (ordinary chosen).lookup "chr:active" = some (occurrenceRef activeId) := by
            cases active with
            | capture stored =>
              exact capture_ordinary_compatible stored (afterActive.extends.trans later) roots
                ("chr:active", occurrenceRef activeId) List.mem_cons_self
          refine ⟨⟨?_, ?_⟩, activeRead⟩
          · intro index name selected
            have within := (List.getElem?_eq_some_iff.mp selected).1
            have row := predicateRead.get (by simpa using within) (by simpa using within)
            simpa using row
          · intro index value selected
            obtain ⟨within, atIndex⟩ := List.getElem?_eq_some_iff.mp selected
            have row := scalarRead.get (by simpa using within) (by simpa using within)
            simpa [atIndex] using row

#print axioms request_prefix

end Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRCompilation.RequestPools
