import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeRecursiveDriver
import Mettapedia.Machines.ReadOnlySpecialization

/-!
# Specializing the existing recursive type-read plan

An available annotation can be discharged for the selected source and
runtime profile. A later closure request still belongs to the current
call. A pending closure and a completed empty type list keep their distinct
outcomes. This specializes the existing semantic reader, with
both the answer and the primitive trace retained.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeSpecialization

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Machines.ReadOnlyQuery
open Mettapedia.Machines.ReadOnlySpecialization
open NativeTypeCallGraph NativeTypeRecursiveDriver NativeTypeViews

def staticAnnotation (before : PrimitiveStore) : Primitive → Bool
  | key@(.annotations _) => (before key).isSome
  | _ => false

def prepare (ops : Ops Atom TypeScopeMatcher.State Atom) (before : PrimitiveStore)
    (reads depth : Nat) (call : Call) : Residual (expand ops depth call) :=
  drive (staticAnnotation before) before reads (expand ops depth call)

theorem prepared_trace (ops : Ops Atom TypeScopeMatcher.State Atom)
    (before live : PrimitiveStore) (reads depth : Nat) (call : Call)
    {result : Observation Primitive (Option Reply) (Option Reply)}
    (accepted : (prepare ops before reads depth call).tryRun live = some result) :
    result = run live (expand ops depth call) :=
  Residual.tryRun_sound _ _ accepted

theorem prepared_answer (ops : Ops Atom TypeScopeMatcher.State Atom)
    (before live : PrimitiveStore) (reads depth : Nat) (call : Call)
    {result : Observation Primitive (Option Reply) (Option Reply)}
    (accepted : (prepare ops before reads depth call).tryRun live = some result) :
    result.answer = evaluate ops live depth call :=
  (congrArg Observation.answer (prepared_trace ops before live reads depth call accepted)).trans
    (expanded_answer ops live depth call)

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeSpecialization
