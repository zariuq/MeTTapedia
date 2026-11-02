import Mettapedia.Languages.MeTTa.PeTTa.Bridges.FlatQueryIndexedSource
import Mettapedia.Languages.MeTTa.PeTTa.MatchValueExtension

/-!
# Queries through captured space operands

An ordinary wrapper may pass its space as a captured argument. Successful
source matching extends that caller without rebinding the handle. This module
connects such queries to indexed counting while retaining the actual variable
or quoted operand in the source expression. Operand stability is proved from
source evaluation and lookup extension, not inferred from its spelling.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.CapturedQuerySource

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open Mettapedia.GSLT.LanguageDef.FiniteEnvironmentCompilation
open Eval SpaceSemantics FlatQueryRowCodec FlatQueryRelationCompilation FlatQueryConjunctionCompilation
open FlatQuerySourceExecution

structure Operand (caller : Subst) (source : Atom) where
  value : Atom
  returns : ∀ program state bindings, bindings.lookupExtends caller →
    PureReturns program bindings state source state value

def Operand.symbol (caller : Subst) (name : String) : Operand caller (.symbol name) :=
  ⟨.symbol name, fun program state bindings _ => symbol_returns program bindings state name⟩

def Operand.variable (caller : Subst) (name : String) (value : Atom)
    (found : Subst.lookup caller name = some value) : Operand caller (.var name) where
  value := value
  returns program state bindings extended := by
    simpa only [applySubst, extended name value found, Option.getD_some] using
      variable_returns program bindings state name

def Operand.quoted (caller : Subst) (value : Atom)
    (ground : Mettapedia.Languages.ProcessCalculi.MORK.isGroundAtom (applySubst caller value) = true) :
    Operand caller (.expression [.symbol "quote", value]) where
  value := applySubst caller value
  returns program state bindings extended := by
    have same := Mettapedia.Languages.ProcessCalculi.MORK.applySubst_ground_ext extended ground
    simpa only [same] using quote_returns program bindings state value

def prepareOperand (caller : Subst) : (source : Atom) → Option (Operand caller source)
  | .symbol name => some (Operand.symbol caller name)
  | .var name => match found : Subst.lookup caller name with
      | none => none
      | some value => some (Operand.variable caller name value found)
  | .expression [.symbol "quote", value] =>
      if ground : Mettapedia.Languages.ProcessCalculi.MORK.isGroundAtom (applySubst caller value) then
        some (Operand.quoted caller value ground) else none
  | _ => none

private theorem path_trans {system : Mettapedia.GSLT.GSLT} {a b c : system.Term}
    (first : system.MultiStep a b) (second : system.MultiStep b c) : system.MultiStep a c := by
  induction first with
  | refl _ => exact second
  | step step _ ih => exact .step step (ih second)

theorem match_returns (program : Program) (state : Effects.State) (bindings : Subst)
    (space value : Atom) (rows : List Atom) (spaceReturn : PureReturns program bindings state space state value)
    (snapshot : (Effects.readHandle value >>= state.read) = some rows)
    (pattern body : Atom) (answers : Subst → List Atom)
    (returned : ∀ row ∈ rows, ∀ bound, matchValue bindings pattern row = some bound →
      Returns program bound state body state (answers bound)) :
    Returns program bindings state (.expression [.symbol "match", space, pattern, body]) state
      ((sourceScan bindings pattern 0 rows).flatMap (fun result => answers result.2)) := by
  refine .step (step_transition rfl) (path_trans
    (path_with_caller_frames program [.query bindings pattern body] spaceReturn) ?_)
  refine .step (step_transition rfl) ?_
  simp only [withFrames, finished, List.nil_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  simp only [queryAlternatives, snapshot]
  simpa [finished] using rows_return_matched program state bindings pattern body answers rows returned 0 []

theorem nested_returns {caller : Subst} {space : Atom} (operand : Operand caller space)
    (program : Program) (state : Effects.State) (bindings : Subst) (extended : bindings.lookupExtends caller)
    (rows : List Atom) (snapshot : (Effects.readHandle operand.value >>= state.read) = some rows)
    (patterns : List Atom) (body : Atom) (answers : Subst → List Atom)
    (returned : ∀ bound, bound.lookupExtends caller → Returns program bound state body state (answers bound)) :
    Returns program bindings state (sourceTerm space patterns body) state
      ((sourceRun rows bindings patterns).flatMap (fun result => answers result.1)) := by
  induction patterns generalizing bindings with
  | nil => simpa [sourceTerm, sourceRun] using returned bindings extended
  | cons pattern patterns ih =>
      have result := match_returns program state bindings space operand.value rows
        (operand.returns program state bindings extended) snapshot pattern (sourceTerm space patterns body)
        (fun bound => (sourceRun rows bound patterns).flatMap (fun result => answers result.1))
        (fun _ _ bound matched => ih bound (Subst.lookupExtends_trans extended (matchValue_lookup_extends matched)))
      simpa only [sourceTerm, sourceRun, List.flatMap_assoc, List.flatMap_map, Function.comp_def] using result

def countTerm (space : Atom) (patterns : List Atom) : Atom :=
  .expression [.symbol "size-atom", .expression [.symbol "collapse", sourceTerm space patterns (Effects.boolean true)]]

theorem count_returns {caller : Subst} {space : Atom} (operand : Operand caller space)
    (program : Program) (state : Effects.State) (rows : List Atom)
    (snapshot : (Effects.readHandle operand.value >>= state.read) = some rows) (patterns : List Atom) :
    PureReturns program caller state (countTerm space patterns) state
      (.grounded (.int (sourceRun rows caller patterns).length)) := by
  have stream : Returns program caller state (sourceTerm space patterns (Effects.boolean true)) state
      ((sourceRun rows caller patterns).map (fun _ => Effects.boolean true)) := by
    rw [List.map_eq_flatMap]
    exact nested_returns operand program state caller (Subst.lookupExtends_refl caller) rows snapshot
      patterns (Effects.boolean true) (fun _ => [Effects.boolean true])
      (fun bound _ => grounded_returns program bound state (.bool true))
  have collected := collapse_returns program caller state state _ _ stream
  have counted := native_unary_call_returns program caller state state state "size-atom"
    (.expression [.symbol "collapse", sourceTerm space patterns (Effects.boolean true)])
    (.expression ((sourceRun rows caller patterns).map (fun _ => Effects.boolean true)))
    (.grounded (.int ((sourceRun rows caller patterns).map (fun _ => Effects.boolean true)).length))
    (by decide) (by decide) (by simp [argumentIsRaw, StdLib.known, StdLib.rawArgument])
    collected rfl (by decide)
  simpa only [List.length_map, countTerm] using counted

def certificate {Value : Type} [LinearOrder Value] {codec : Codec Value} {names : Inventory String}
    {rows patterns : List Atom} {environment : DenseEnvironment names Value}
    (prepared : FlatQueryIndexedSource.Prepared codec names rows patterns environment)
    (outside : Value) (caller : Subst) (represented : Represents codec names environment caller)
    {space : Atom} (operand : Operand caller space) (program : Program) :
    ReadOnlyQuerySource.Certified program caller (countTerm space patterns) where
  reads := [(operand.value, rows)]
  values := [.grounded (.int (prepared.count outside))]
  returns state valid := by
    rw [prepared.count_exact, compiled_count_exact codec names rows patterns prepared.legs prepared.accepted
      environment caller represented]
    exact count_returns operand program state rows ((ReadOnlyQuerySource.valid_singleton _ _ _).mp valid) patterns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.CapturedQuerySource
