import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingRho

/-!
# Controls for the composed core-rho compiler

The positive source case contains a persistent definition and a binary
application, so coverage is not confined to unary communication. An unused
private scope supplies the static boundary: pi's structural equations erase
it, while the emitted rho allocation client is not structurally inaction.
An operational or observational comparison must therefore account for
allocation; it cannot be a literal map of these structural equations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingRhoControls

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.LambdaCalculus
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open RhoUnaryCode

abbrev publicScope : Ctx sig := [Srt.nm, Srt.nm]

/-- A retained identity definition is invoked in its own binding scope. -/
def retainedIdentity : NamePassingLambda.Expr publicScope :=
  .defn (.lam (.var .zero)) (.app (.var .zero) (.succ .zero))

def publicWorld : RhoUnaryCompiler.World publicScope 0
  | .zero => .atom "argument"
  | .succ .zero => .atom "result"

theorem retained_identity_emits_core :
    ∃ code : Code 0,
      NamePassingRho.compile retainedIdentity (fun _ x => x) (.succ .zero) publicWorld = some code :=
  NamePassingRho.compile_total _ _ _ _

theorem retained_identity_uses_guarded_protocol :
    RhoUnaryCompiler.GuardedUnary
      (MonadicProtocol.lower (NamePassingLambda.translate retainedIdentity (.succ .zero))) :=
  NamePassingRho.guarded_compiler_image _ _ _

def emptyWorld : RhoUnaryCompiler.World [] 0 := fun name => nomatch name

theorem inaction_compiles :
    RhoUnaryCompiler.compile emptyWorld (nil : Proc []) = some (Code.zero 0) := by
  rw [nil, RhoUnaryCompiler.compile]

theorem unused_scope_compiles :
    RhoUnaryCompiler.compile emptyWorld (nu (nil : Proc [Srt.nm])) =
      some (Code.reserve (Code.zero 1)) := by
  rw [nu, RhoUnaryCompiler.compile, nil, RhoUnaryCompiler.compile]
  rfl

theorem source_unused_scope_is_inaction :
    StructuralEq (nu (nil : Proc [Srt.nm])) (nil : Proc []) := by
  have unused : weaken (nil : Proc []) = (nil : Proc [Srt.nm]) := rfl
  simpa only [unused] using StructuralEq.nuUnused (nil : Proc [])

theorem allocation_client_is_not_structural_inaction :
    ¬ Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence
      (Code.reserve (Code.zero 1)).term (Code.zero 0).term := by
  intro equal
  have impossible := Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction.ioCount_SC equal
  simp only [Code.reserve, Code.par, Code.sendName, Code.emit, Code.datum, Code.listen,
    Code.zero, NameValue.payload, NameValue.term, Reserved.label,
    Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoScopedServers.parallel,
    Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoScopedServers.send,
    Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoScopedServers.receive,
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction.ioCount,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at impossible
  omega

/-- Both sides of this control are the literal successful outputs of the
actual guarded-unary compiler. -/
theorem unused_scope_static_boundary :
    StructuralEq (nu (nil : Proc [Srt.nm])) (nil : Proc []) ∧
      RhoUnaryCompiler.compile emptyWorld (nu (nil : Proc [Srt.nm])) =
        some (Code.reserve (Code.zero 1)) ∧
      RhoUnaryCompiler.compile emptyWorld (nil : Proc []) = some (Code.zero 0) ∧
      ¬ Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence
        (Code.reserve (Code.zero 1)).term (Code.zero 0).term :=
  ⟨source_unused_scope_is_inaction, unused_scope_compiles, inaction_compiles,
    allocation_client_is_not_structural_inaction⟩

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingRhoControls
