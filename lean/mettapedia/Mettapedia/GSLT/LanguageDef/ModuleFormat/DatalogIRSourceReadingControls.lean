import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRReceiptSoundness

/-! The source-reading profile accepts a real join with a numeric guard,
and separates unsafe source, failed guards and inconsistent shared variables. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.SourceReadingControls

open Mettapedia.Languages.Datalog
open Mettapedia.OSLF.MeTTaIL Syntax Match

def clause : Clause := ⟨⟨["Low"],[.var "X"]⟩,
  [.atom ⟨["Pair"],[.var "X",.var "X"]⟩,.comparison ⟨.less,.var "X",.literal (.number 2)⟩]⟩
def source : Program := ⟨[
  .declaration ⟨["Pair"],[⟨"left",.number⟩,⟨"right",.number⟩]⟩,
  .declaration ⟨["Low"],[⟨"value",.number⟩]⟩,.rule clause,.output ["Low"]]⟩
def inputs : List GroundFact := [⟨["Pair"],[.number 1,.number 1]⟩,⟨["Pair"],[.number 1,.number 2]⟩,
  ⟨["Pair"],[.number 2,.number 2]⟩]
def prepared : Executable.Prepared := (Executable.prepare source inputs).toOption.get (by decide +kernel)

theorem preparation_succeeds : (Executable.prepare source inputs).toOption.isSome = true := by decide +kernel

#guard GeneralPremise.Static.checkLanguage
    (GeneralPlanEnvironment.environment (Executable.plan prepared prepared.seedFacts))

theorem good_pair : (⟨["Pair"],[.var "X",.var "X"]⟩ : Mettapedia.Languages.Datalog.Atom).Matches
    (fun _ => some (.number 1)) ⟨["Pair"],[.number 1,.number 1]⟩ := by simp [Atom.Matches,Argument.Matches]

theorem different_pair_refused : ¬ (⟨["Pair"],[.var "X",.var "X"]⟩ : Mettapedia.Languages.Datalog.Atom).Matches
    (fun _ => some (.number 1)) ⟨["Pair"],[.number 1,.number 2]⟩ := by simp [Atom.Matches,Argument.Matches]

theorem guard_passes : Executable.policy.Holds .less (.number 1) (.number 2) := by simp [Executable.policy]
theorem guard_refuses : ¬ Executable.policy.Holds .less (.number 2) (.number 2) := by simp [Executable.policy]

def unsafeSource : Program := ⟨[
  .declaration ⟨["Pair"],[⟨"left",.number⟩,⟨"right",.number⟩]⟩,
  .declaration ⟨["Low"],[⟨"value",.number⟩]⟩,
  .rule ⟨⟨["Low"],[.var "Y"]⟩,[.atom ⟨["Pair"],[.var "X",.var "X"]⟩]⟩]⟩

#guard (Executable.prepare unsafeSource inputs).toOption.isNone

#print axioms preparation_succeeds
#print axioms good_pair
#print axioms different_pair_refused
#print axioms guard_passes
#print axioms guard_refuses

end Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.SourceReadingControls
