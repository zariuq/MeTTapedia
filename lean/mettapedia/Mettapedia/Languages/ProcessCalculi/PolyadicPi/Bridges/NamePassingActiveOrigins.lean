import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveMarking
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingEnvironmentEquations

/-!
# Source constructors recovered from actual compiled communications

Compiler markings are computed from the source constructor addresses. Only
function paths and environment bodies are active; lambda bodies and stored
values remain guarded. The origin inversion theorem recovers an actual source
constructor from a selected compiler marking. Combined with static tracing,
an arbitrary target communication therefore identifies a real source lookup,
call or declaration owner, rather than a label assigned afterward.

This does not yet prove that the recovered sender and receiver have the same
source reference or that the supplied target endpoint recompiles a source
successor. Those require the separate name-key and continuation comparison.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingActiveOrigins

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.LambdaCalculus.NamePassing
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingLambda
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveHeaderInvariant
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveMarking
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ScopedCommunicationInversion

inductive Edge where
  | lambdaBody
  | function
  | definitionValue
  | definitionBody
  | carrierValue
  | carrierBody
  deriving DecidableEq, Repr

inductive Kind where
  | lookup
  | lambda
  | application
  | definition
  | carrier
  | privateCall
  | privateReference
  deriving DecidableEq, Repr

structure Origin where
  kind : Kind
  address : List Edge
  deriving DecidableEq, Repr

/-- A prefix or private binder's identity is computed before execution. -/
def mark : {Γ : Ctx sig} → Expr Srt.nm Γ → List Edge → ActiveMarking.Tree Origin
  | _, .var _, address => .out1 ⟨.lookup, address⟩
  | _, .lam body, address => .inp2 ⟨.lambda, address⟩ (mark body (.lambdaBody :: address))
  | _, .app function _, address => .nu ⟨.privateCall, address⟩
      (.par (mark function (.function :: address)) (.out2 ⟨.application, address⟩))
  | _, .defn value body, address => .nu ⟨.privateReference, address⟩
      (.par (mark body (.definitionBody :: address))
        (.rep (.inp1 ⟨.definition, address⟩ (mark value (.definitionValue :: address)))))
  | _, .carrier _ value body, address =>
      .par (mark body (.carrierBody :: address))
        (.inp1 ⟨.carrier, address⟩ (mark value (.carrierValue :: address)))

/-- The computed marking follows every real compiler constructor and binder. -/
theorem mark_fits {Γ Δ : Ctx sig} (source : Expr Srt.nm Γ) (address : List Edge)
    (environment : Ren sig Γ Δ) (result : Var Δ .nm) :
    Fits (mark source address) (compile source environment result) := by
  induction source generalizing Δ address with
  | var name => exact .out1 _ _ _
  | lam body ih => exact .inp2 _ _ (ih _ _ _)
  | app function argument ih => exact .nu _ (.par (ih _ _ _) (.out2 _ _ _ _))
  | defn value body valueIH bodyIH =>
      exact .nu _ (.par (bodyIH _ _ _) (.rep (.inp1 _ _ (valueIH _ _ _))))
  | carrier name value body valueIH bodyIH =>
      exact .par (bodyIH _ _ _) (.inp1 _ _ (valueIH _ _ _))

/-- An independently defined active source-constructor address. The lambda
body and stored value are retained by the constructor data, and no rule
allows traversal through them while they are suspended. -/
inductive SourcePrefix : Header → Origin → {Γ : Ctx sig} → Expr Srt.nm Γ → List Edge → Type where
  | lookup {Γ} (name : Var Γ Srt.nm) (address : List Edge) :
      SourcePrefix .output1 ⟨.lookup, address⟩ (.var name) address
  | lambda {Γ} (body : Expr Srt.nm (Srt.nm :: Γ)) (address : List Edge) :
      SourcePrefix .input2 ⟨.lambda, address⟩ (.lam body) address
  | application {Γ} (function : Expr Srt.nm Γ) (argument : Var Γ Srt.nm) (address : List Edge) :
      SourcePrefix .output2 ⟨.application, address⟩ (.app function argument) address
  | definition {Γ} (value : Expr Srt.nm Γ) (body : Expr Srt.nm (Srt.nm :: Γ)) (address : List Edge) :
      SourcePrefix .input1 ⟨.definition, address⟩ (.defn value body) address
  | carrier {Γ} (name : Var Γ Srt.nm) (value body : Expr Srt.nm Γ) (address : List Edge) :
      SourcePrefix .input1 ⟨.carrier, address⟩ (.carrier name value body) address
  | function {Γ header origin} {function : Expr Srt.nm Γ} (argument : Var Γ Srt.nm) {address : List Edge} :
      SourcePrefix header origin function (.function :: address) →
      SourcePrefix header origin (.app function argument) address
  | definitionBody {Γ header origin} (value : Expr Srt.nm Γ) {body : Expr Srt.nm (Srt.nm :: Γ)} {address : List Edge} :
      SourcePrefix header origin body (.definitionBody :: address) →
      SourcePrefix header origin (.defn value body) address
  | carrierBody {Γ header origin} (name : Var Γ Srt.nm) (value : Expr Srt.nm Γ)
      {body : Expr Srt.nm Γ} {address : List Edge} :
      SourcePrefix header origin body (.carrierBody :: address) →
      SourcePrefix header origin (.carrier name value body) address

/-- Constructor marking inversion reaches the supplied source term, not a
new term decoded from the eventual result. -/
noncomputable def sourcePrefix_of_selection {Γ : Ctx sig} (source : Expr Srt.nm Γ) (address : List Edge)
    {header : Header} {origin : Origin} (selected : Selection header origin (mark source address)) :
    SourcePrefix header origin source address := by
  induction source generalizing address header origin with
  | var name => cases selected; exact .lookup name address
  | lam body ih => cases selected; exact .lambda body address
  | app function argument ih =>
      cases selected with
      | nu _ selected => cases selected with
          | left _ selected => exact .function argument (ih _ selected)
          | right _ selected => cases selected; exact .application function argument address
  | defn value body valueIH bodyIH =>
      cases selected with
      | nu _ selected => cases selected with
          | left _ selected => exact .definitionBody value (bodyIH _ selected)
          | right _ selected => cases selected with
              | rep selected => cases selected; exact .definition value body address
  | carrier name value body valueIH bodyIH =>
      cases selected with
      | left _ selected => exact .carrierBody name value (bodyIH _ selected)
      | right _ selected => cases selected; exact .carrier name value body address

/-- Both actors of an arbitrary actual target firing have independent source
constructor witnesses, with all chosen target syntax retained by the trace. -/
theorem actual_step_has_source_origins {Γ Δ : Ctx sig} (source : Expr Srt.nm Γ)
    (environment : Ren sig Γ Δ) (result : Var Δ .nm) {target : Proc Δ}
    (firing : StepModulo (compile source environment result) target) :
    ∃ (exposure : Exposure (compile source environment result) target)
      (traced : TracedExposure (mark source []) exposure),
      Nonempty (SourcePrefix (inputHeader exposure.selected) traced.continuation.inputOrigin source []) ∧
      Nonempty (SourcePrefix (outputHeader exposure.selected) traced.continuation.outputOrigin source []) := by
  rcases modulo_step_has_traced_origins (Origin.mk .privateCall []) (mark_fits source [] environment result) firing with
    ⟨exposure, traced⟩
  rcases traced with ⟨traced⟩
  exact ⟨exposure, traced, ⟨sourcePrefix_of_selection source [] traced.originalInput⟩,
    ⟨sourcePrefix_of_selection source [] traced.originalOutput⟩⟩

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingActiveOrigins
