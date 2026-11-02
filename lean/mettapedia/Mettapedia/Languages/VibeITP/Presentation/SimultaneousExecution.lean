import Mettapedia.Languages.VibeITP.Presentation.SimultaneousProgram
import Mettapedia.GSLT.LanguageDef.DeterministicEquations.ProgramSuffix

/-!
# Execution of the authored simultaneous environment

Each computation is an application of the actual equation program. Existing
lookup, scalar and binding operations are transported into the disjoint program
extension; no source operation is installed as a new host primitive.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
namespace Mettapedia.Languages.VibeITP.Presentation.ComputationalSimultaneous

open ComputationalData ComputationalShift ComputationalSubstitution
open ComputationalInstantiation ComputationalInference
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

local notation "P" => simultaneousProgram
local notation "A" => simultaneousEquations
local notation "H" => computationalHost

theorem simultaneous_equation {head : String} {arguments : List Term} {equation : Equation}
    {environment : Env} {result : Term} (used : head ∈ simultaneousEquations.map Equation.head)
    (defined : simultaneousEquations.definesAt head arguments.length = true)
    (selected : simultaneousEquations.select head arguments = some (equation, environment))
    (body : Evaluates P H environment equation.body result) :
    Applies P H head arguments result :=
  Applies.suffix_equation simultaneousEquations_disjoint used defined selected body

private theorem called_append_left {head : String} (source addition : Program)
    (used : head ∈ source.calledHeads) : head ∈ (source ++ addition).calledHeads := by
  simp only [Program.calledHeads, List.flatMap_append, List.mem_append]
  exact Or.inl used

theorem instantiation_applies {head : String} {arguments : List Term} {result : Term}
    (used : head ∈ instantiationProgram.calledHeads)
    (computed : Applies instantiationProgram H head arguments result) : Applies P H head arguments result :=
  reuse_inference_call (called_append_left _ inferenceEquations used) (reuse_instantiation_call used computed)

theorem substitution_applies {head : String} {arguments : List Term} {result : Term}
    (used : head ∈ substitutionProgram.calledHeads)
    (computed : Applies substitutionProgram H head arguments result) : Applies P H head arguments result :=
  instantiation_applies (called_append_left _ instantiationEquations used) (reuse_substitution_call used computed)

private theorem symbol_applies (first second : Spec.SymId) :
    Applies P H "vibe:symbol-eq" [encodeSymbol first, encodeSymbol second]
      (boolean (decide (first = second))) := by
  apply substitution_applies (by decide +kernel)
  apply (Applies.append_iff shiftProgram substitutionEquations H substitutionEquations_disjoint
    "vibe:symbol-eq" (by decide +kernel) _ _).mpr
  exact symbol_computes first second

private theorem declaration_applies (table : SignatureTable) (symbol : Spec.SymId) :
    Applies P H "vibe:lookup-symbol" [encodeTable table, encodeSymbol symbol]
      (encodeInfoResult (signatureOf table symbol)) := by
  apply substitution_applies (by decide +kernel)
  apply (Applies.append_iff shiftProgram substitutionEquations H substitutionEquations_disjoint
    "vibe:lookup-symbol" (by decide +kernel) _ _).mpr
  exact ComputationalShift.lookup_computes table symbol

private theorem depth_applies (table : SignatureTable) (term : Spec.Term) :
    Applies P H "vibe:depth" [encodeTable table, encode term] (natural (Spec.depth (signatureOf table) term)) :=
  substitution_applies (by decide +kernel) (depth_computes_in_substitution table term)

private theorem length_applies (items : List Term) :
    Applies P H "vibe:list-length" [.list items] (natural items.length) :=
  substitution_applies (by decide +kernel) (listLength_computes items)

theorem view_applies (items : List Term) :
    Applies P H "nik:list-view" [.list items] (listView items) :=
  .primitive (by rfl) (computationalHost_list_view items)

private theorem le_applies (left right : Nat) :
    Applies P H "nik:nat-le" [natural left, natural right] (boolean (decide (left ≤ right))) :=
  .primitive (by rfl) (naturalArithmeticHost_le left right)

private theorem lookup_start (entries : List Spec.SimultaneousInstantiation.Entry) (symbol : Spec.SymId)
    (next : Applies P H "vibe:many-lookup-view" [listView (entries.map encodeEntry), encodeSymbol symbol]
      (encodeEntryResult (Spec.SimultaneousInstantiation.lookup entries symbol))) :
    Applies P H "vibe:many-lookup" [encodeEntries entries, encodeSymbol symbol]
      (encodeEntryResult (Spec.SimultaneousInstantiation.lookup entries symbol)) := by
  refine simultaneous_equation (equation := A[0])
    (environment := [("entries", encodeEntries entries), ("symbol", encodeSymbol symbol)])
    (by decide +kernel) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special]) (.cons ?_ (.cons (.variable (by rfl)) .nil)) next
  exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil)
    (view_applies (entries.map encodeEntry))

theorem lookup_computes (entries : List Spec.SimultaneousInstantiation.Entry) (symbol : Spec.SymId) :
    Applies P H "vibe:many-lookup" [encodeEntries entries, encodeSymbol symbol]
      (encodeEntryResult (Spec.SimultaneousInstantiation.lookup entries symbol)) := by
  induction entries with
  | nil => apply lookup_start; exact ⟨1, rfl⟩
  | cons entry rest ih =>
      apply lookup_start
      refine simultaneous_equation (equation := A[2])
        (environment := [("first", encodeSymbol entry.symbol), ("arity", natural entry.arity),
          ("value", encode entry.value), ("rest", encodeEntries rest), ("symbol", encodeSymbol symbol)])
        (by decide +kernel) (by rfl) (by rfl) ?_
      refine Evaluates.call (values := [boolean (decide (symbol = entry.symbol)), encodeSymbol entry.symbol,
        natural entry.arity, encode entry.value, encodeEntries rest, encodeSymbol symbol]) (by simp [Special])
        (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
          (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))))) ?_
      · exact Evaluates.call (by simp [Special])
          (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) (symbol_applies symbol entry.symbol)
      · by_cases same : symbol = entry.symbol
        · simp only [same, decide_true, boolean, Spec.SimultaneousInstantiation.lookup, ↓reduceIte]
          exact ⟨3, rfl⟩
        · simp only [same, decide_false, boolean, Spec.SimultaneousInstantiation.lookup, if_false]
          refine simultaneous_equation (equation := A[4])
            (environment := [("first", encodeSymbol entry.symbol), ("arity", natural entry.arity),
              ("value", encode entry.value), ("rest", encodeEntries rest), ("symbol", encodeSymbol symbol)])
            (by decide +kernel) (by rfl) (by rfl) ?_
          exact Evaluates.call (by simp [Special])
            (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) ih

private theorem prepare_start (table : SignatureTable) (replacements : List (Spec.SymId × Spec.Term))
    (result : Option (List Spec.SimultaneousInstantiation.Entry))
    (next : Applies P H "vibe:many-prepare-view"
      [encodeTable table, listView (replacements.map encodeReplacement)] (encodePreparation result)) :
    Applies P H "vibe:many-prepare" [encodeTable table, encodeReplacements replacements]
      (encodePreparation result) := by
  refine simultaneous_equation (equation := A[5])
    (environment := [("table", encodeTable table), ("replacements", encodeReplacements replacements)])
    (by decide +kernel) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) (.cons ?_ .nil)) next
  exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil)
    (view_applies (replacements.map encodeReplacement))

private theorem prepare_prepend (entry : Spec.SimultaneousInstantiation.Entry)
    (prepared : Option (List Spec.SimultaneousInstantiation.Entry)) :
    Applies P H "vibe:many-prepare-rest"
      [encodePreparation prepared, encodeSymbol entry.symbol, natural entry.arity, encode entry.value]
      (encodePreparation (prepared.map (entry :: ·))) := by
  cases prepared with
  | none => exact ⟨1, rfl⟩
  | some rest => exact ⟨4, rfl⟩

private theorem prepare_valid (table : SignatureTable) (symbol : Spec.SymId) (value : Spec.Term)
    (arity : Nat) (rest : List (Spec.SymId × Spec.Term))
    (computed : Applies P H "vibe:many-prepare" [encodeTable table, encodeReplacements rest]
      (encodePreparation (Spec.SimultaneousInstantiation.prepare (signatureOf table) rest))) :
    Applies P H "vibe:many-prepare-depth"
      [.sym "True", natural arity, encodeTable table, encodeSymbol symbol, encode value, encodeReplacements rest]
      (encodePreparation ((Spec.SimultaneousInstantiation.prepare (signatureOf table) rest).map
        (⟨symbol, arity, value⟩ :: ·))) := by
  refine simultaneous_equation (equation := A[13])
    (environment := [("arity", natural arity), ("table", encodeTable table), ("symbol", encodeSymbol symbol),
      ("value", encode value), ("rest", encodeReplacements rest)])
    (by decide +kernel) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special])
    (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))))
    (prepare_prepend ⟨symbol, arity, value⟩ _)
  exact Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) computed

private theorem prepare_arity (table : SignatureTable) (symbol : Spec.SymId) (value : Spec.Term)
    (arity : Nat) (rest : List (Spec.SymId × Spec.Term))
    (computed : Applies P H "vibe:many-prepare" [encodeTable table, encodeReplacements rest]
      (encodePreparation (Spec.SimultaneousInstantiation.prepare (signatureOf table) rest))) :
    Applies P H "vibe:many-prepare-arity"
      [natural arity, encodeTable table, encodeSymbol symbol, encode value, encodeReplacements rest]
      (encodePreparation (if Spec.depth (signatureOf table) value ≤ arity then
        (Spec.SimultaneousInstantiation.prepare (signatureOf table) rest).map (⟨symbol, arity, value⟩ :: ·)
        else none)) := by
  refine simultaneous_equation (equation := A[11])
    (environment := [("arity", natural arity), ("table", encodeTable table), ("symbol", encodeSymbol symbol),
      ("value", encode value), ("rest", encodeReplacements rest)])
    (by decide +kernel) (by rfl) (by rfl) ?_
  refine Evaluates.call (values := [boolean (decide (Spec.depth (signatureOf table) value ≤ arity)),
    natural arity, encodeTable table, encodeSymbol symbol, encode value, encodeReplacements rest]) (by simp [Special])
    (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))))) ?_
  · refine Evaluates.call (by simp [Special]) (.cons ?_ (.cons (.variable (by rfl)) .nil))
      (le_applies (Spec.depth (signatureOf table) value) arity)
    exact Evaluates.call (by simp [Special])
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) (depth_applies table value)
  · by_cases fits : Spec.depth (signatureOf table) value ≤ arity
    · simp only [fits, decide_true, boolean, if_true]
      exact prepare_valid table symbol value arity rest computed
    · simp only [fits, decide_false, boolean, if_false]
      exact ⟨1, rfl⟩

theorem prepare_computes (table : SignatureTable) (replacements : List (Spec.SymId × Spec.Term)) :
    Applies P H "vibe:many-prepare" [encodeTable table, encodeReplacements replacements]
      (encodePreparation (Spec.SimultaneousInstantiation.prepare (signatureOf table) replacements)) := by
  induction replacements with
  | nil => apply prepare_start; exact ⟨2, rfl⟩
  | cons replacement rest ih =>
      rcases replacement with ⟨symbol, value⟩
      apply prepare_start
      refine simultaneous_equation (equation := A[7])
        (environment := [("table", encodeTable table), ("symbol", encodeSymbol symbol),
          ("value", encode value), ("rest", encodeReplacements rest)])
        (by decide +kernel) (by rfl) (by rfl) ?_
      refine Evaluates.call (values := [encodeInfoResult (signatureOf table symbol), encodeTable table,
        encodeSymbol symbol, encode value, encodeReplacements rest]) (by simp [Special])
        (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
          (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))))) ?_
      · exact Evaluates.call (by simp [Special])
          (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) (declaration_applies table symbol)
      · cases found : signatureOf table symbol with
        | none => simp only [Spec.SimultaneousInstantiation.prepare, found]; exact ⟨1, rfl⟩
        | some info =>
            cases kind : info.kind with
            | constant =>
                simp only [Spec.SimultaneousInstantiation.prepare, found, kind,
                  reduceCtorEq, false_and, if_false, encodeInfoResult, encodeInfo, encodeKind]
                exact ⟨1, rfl⟩
            | fvar =>
                simp only [Spec.SimultaneousInstantiation.prepare, found, kind, true_and,
                  encodeInfoResult, encodeInfo, encodeKind]
                refine simultaneous_equation (equation := A[10])
                  (environment := [("binders", encodeBinders info.binders), ("table", encodeTable table),
                    ("symbol", encodeSymbol symbol), ("value", encode value), ("rest", encodeReplacements rest)])
                  (by decide +kernel) (by rfl) (by rfl) ?_
                refine Evaluates.call (by simp [Special])
                  (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
                    (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))))
                  (prepare_arity table symbol value info.arity rest ih)
                exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil)
                  (by simpa only [encodeBinders, Spec.SymInfo.arity, List.length_map]
                    using length_applies (info.binders.map natural))

#print axioms lookup_computes
#print axioms prepare_computes

end Mettapedia.Languages.VibeITP.Presentation.ComputationalSimultaneous
