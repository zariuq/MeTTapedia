import Mettapedia.Languages.ProcessCalculi.PiCalculus.ProcessContext
import Mettapedia.Languages.ProcessCalculi.PiCalculus.EncodingMorphism

/-!
# The pi-to-rho encoding as a pair: a map on terms and a map on contexts

The encoding of a process depends on two names.  Along a context, the
namespace name is extended at every parallel composition, restriction and
replication crossed on the way to the hole; the value name is passed
unchanged.  The image of a context is the operation on rho terms that wraps
the encoding of the plugged process, and the encoding is equivariant on the
nose: the encoding of a plugged context is the image of the context applied
to the encoding of the process, at the name the context passes to its hole.
The image of a composite context is the composite of the images.

The parameterisation is therefore part of the interface: the image of a
context is a map from terms at one name to terms at another.

The image of a context is an operation on rho terms and not, in general, the
plugging of a rho one-hole context.  Two things stand in the way.  Parallel
composition in the image is flattened, so the image of a hole beside a
process splices the components of what is plugged instead of placing it.  And
a hole beneath an input binds: the image closes the bound name in what is
plugged before placing it.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PiCalculus

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution (closeFVar)
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Context (parComponents)

open private rhoPar_eq_parComponents_append from
  Mettapedia.Languages.ProcessCalculi.PiCalculus.EncodingMorphism

namespace ProcessContext

/-- The namespace name a context passes to its hole. -/
def parameter : ProcessContext → String → String
  | .hole, n => n
  | .parLeft inner _, n => inner.parameter (n ++ "_L")
  | .parRight _ inner, n => inner.parameter (n ++ "_R")
  | .input _ _ inner, n => inner.parameter n
  | .nu _ inner, n => inner.parameter (n ++ "_" ++ n)
  | .replicate _ _ inner, n => inner.parameter (n ++ "_rep")

/-- **The image of a context**: the operation on rho terms that wraps the
encoding of what is plugged. -/
def encode : ProcessContext → String → String → Pattern → Pattern
  | .hole, _, _, plugged => plugged
  | .parLeft inner right, n, v, plugged =>
      rhoPar (inner.encode (n ++ "_L") v plugged)
        (PiCalculus.encode right (n ++ "_R") v)
  | .parRight left inner, n, v, plugged =>
      rhoPar (PiCalculus.encode left (n ++ "_L") v) (inner.encode (n ++ "_R") v plugged)
  | .input channel bound inner, n, v, plugged =>
      rhoInput (piNameToRhoName channel) bound (inner.encode n v plugged)
  | .nu bound inner, n, v, plugged =>
      rhoPar (rhoOutput (.fvar v) (.fvar n))
        (rhoInput (.fvar n) bound (inner.encode (n ++ "_" ++ n) v plugged))
  | .replicate channel bound inner, n, v, plugged =>
      rhoReplicate
        (rhoInput (piNameToRhoName channel) bound (inner.encode (n ++ "_rep") v plugged))

/-- **Equivariance.**  The encoding of a plugged context is the image of the
context applied to the encoding of the process, at the name the context
passes to its hole. -/
theorem encode_fill :
    ∀ (context : ProcessContext) (process : Process) (n v : String),
      PiCalculus.encode (context.fill process) n v =
        context.encode n v (PiCalculus.encode process (context.parameter n) v)
  | .hole, _, _, _ => rfl
  | .parLeft inner right, process, n, v => by
      simp only [fill, PiCalculus.encode, encode, parameter,
        encode_fill inner process (n ++ "_L") v]
  | .parRight left inner, process, n, v => by
      simp only [fill, PiCalculus.encode, encode, parameter,
        encode_fill inner process (n ++ "_R") v]
  | .input _ _ inner, process, n, v => by
      simp only [fill, PiCalculus.encode, encode, parameter, encode_fill inner process n v]
  | .nu _ inner, process, n, v => by
      simp only [fill, PiCalculus.encode, encode, parameter,
        encode_fill inner process (n ++ "_" ++ n) v]
  | .replicate _ _ inner, process, n, v => by
      simp only [fill, PiCalculus.encode, encode, parameter,
        encode_fill inner process (n ++ "_rep") v]

/-- The name passed to the hole of a composite is passed twice. -/
theorem parameter_comp :
    ∀ (first second : ProcessContext) (n : String),
      (first.comp second).parameter n = second.parameter (first.parameter n)
  | .hole, _, _ => rfl
  | .parLeft inner _, second, n => by
      simp only [comp, parameter, parameter_comp inner second]
  | .parRight _ inner, second, n => by
      simp only [comp, parameter, parameter_comp inner second]
  | .input _ _ inner, second, n => by
      simp only [comp, parameter, parameter_comp inner second]
  | .nu _ inner, second, n => by
      simp only [comp, parameter, parameter_comp inner second]
  | .replicate _ _ inner, second, n => by
      simp only [comp, parameter, parameter_comp inner second]

/-- **The image of a composite context is the composite of the images**, the
inner image being taken at the name the outer context passes to its hole. -/
theorem encode_comp :
    ∀ (first second : ProcessContext) (n v : String) (plugged : Pattern),
      (first.comp second).encode n v plugged =
        first.encode n v (second.encode (first.parameter n) v plugged)
  | .hole, _, _, _, _ => rfl
  | .parLeft inner _, second, n, v, plugged => by
      simp only [comp, encode, parameter, encode_comp inner second]
  | .parRight _ inner, second, n, v, plugged => by
      simp only [comp, encode, parameter, encode_comp inner second]
  | .input _ _ inner, second, n, v, plugged => by
      simp only [comp, encode, parameter, encode_comp inner second]
  | .nu _ inner, second, n, v, plugged => by
      simp only [comp, encode, parameter, encode_comp inner second]
  | .replicate _ _ inner, second, n, v, plugged => by
      simp only [comp, encode, parameter, encode_comp inner second]

/-- The image of the hole is the identity. -/
@[simp] theorem encode_hole (n v : String) (plugged : Pattern) :
    hole.encode n v plugged = plugged := rfl

/-- A context that crosses a parallel composition changes the name it passes
on: the parameterisation is not constant along contexts. -/
theorem parameter_parLeft_ne (right : Process) (n : String) :
    (parLeft hole right).parameter n ≠ n := by
  simp [parameter]

end ProcessContext

/-! ## The image of a context is not a one-hole context -/

/-- **Flattening.**  No rho one-hole context plugs as parallel composition
with a fixed process does: the composition splices the components of a
parallel argument and places any other, so the number of components of the
result depends on what is plugged. -/
theorem rhoPar_left_not_oneHole (right : Pattern) :
    ¬ ∃ context : OneHoleContext, ∀ plugged : Pattern,
      context.fill plugged = rhoPar plugged right := by
  rintro ⟨context, plugs⟩
  have placed := plugs (.apply "PZero" [])
  have spliced := plugs rhoNil
  rw [rhoPar_eq_parComponents_append] at placed spliced
  cases context with
  | collection kind before inner after rest =>
      simp only [OneHoleContext.fill, Pattern.collection.injEq] at placed spliced
      have placedLength := congrArg List.length placed.2.1
      have splicedLength := congrArg List.length spliced.2.1
      simp [parComponents, rhoNil] at placedLength splicedLength
      omega
  | hole => simp [OneHoleContext.fill] at placed
  | apply _ _ _ _ => simp [OneHoleContext.fill] at placed
  | lambda _ _ => simp [OneHoleContext.fill] at placed
  | multiLambda _ _ _ => simp [OneHoleContext.fill] at placed
  | substBody _ _ => simp [OneHoleContext.fill] at placed
  | substReplacement _ _ => simp [OneHoleContext.fill] at placed

/-- The image of a hole beside a process is not the plugging of any rho
one-hole context. -/
theorem encode_parLeft_not_oneHole (right : Process) (n v : String) :
    ¬ ∃ context : OneHoleContext, ∀ plugged : Pattern,
      context.fill plugged = (ProcessContext.parLeft .hole right).encode n v plugged :=
  rhoPar_left_not_oneHole (encode right (n ++ "_R") v)

/-- **Capture.**  No rho one-hole context plugs as an input with a fixed
channel and bound name does: the input closes the bound name in what is
plugged, and plugging leaves what is plugged as it is. -/
theorem rhoInput_not_oneHole (channel : Pattern) (bound : String) :
    ¬ ∃ context : OneHoleContext, ∀ plugged : Pattern,
      context.fill plugged = rhoInput channel bound plugged := by
  rintro ⟨context, plugs⟩
  have captured := plugs (.fvar bound)
  have placed := plugs (.apply "PZero" [])
  have capturedBody : closeFVar 0 bound (.fvar bound) = .bvar 0 := by simp [closeFVar]
  have placedBody : closeFVar 0 bound (.apply "PZero" []) = .apply "PZero" [] := by
    simp [closeFVar]
  rw [rhoInput, capturedBody] at captured
  rw [rhoInput, placedBody] at placed
  cases context with
  | apply label before inner after =>
      simp only [OneHoleContext.fill, Pattern.apply.injEq] at captured placed
      obtain ⟨-, capturedArguments⟩ := captured
      obtain ⟨-, placedArguments⟩ := placed
      match before, capturedArguments, placedArguments with
      | [], capturedArguments, placedArguments =>
          simp only [List.nil_append, List.cons.injEq] at capturedArguments placedArguments
          have clash := capturedArguments.2.symm.trans placedArguments.2
          simp at clash
      | [_], capturedArguments, _ =>
          simp only [List.cons_append, List.nil_append, List.cons.injEq] at capturedArguments
          obtain ⟨-, body, -⟩ := capturedArguments
          cases inner with
          | lambda name deeper =>
              simp only [OneHoleContext.fill, Pattern.lambda.injEq] at body
              obtain ⟨-, deeperFill⟩ := body
              cases deeper <;> simp [OneHoleContext.fill] at deeperFill
          | hole => simp [OneHoleContext.fill] at body
          | apply _ _ _ _ => simp [OneHoleContext.fill] at body
          | multiLambda _ _ _ => simp [OneHoleContext.fill] at body
          | substBody _ _ => simp [OneHoleContext.fill] at body
          | substReplacement _ _ => simp [OneHoleContext.fill] at body
          | collection _ _ _ _ _ => simp [OneHoleContext.fill] at body
      | _ :: _ :: rest, capturedArguments, _ =>
          have lengths := congrArg List.length capturedArguments
          simp at lengths
  | hole => simp [OneHoleContext.fill] at captured
  | lambda _ _ => simp [OneHoleContext.fill] at captured
  | multiLambda _ _ _ => simp [OneHoleContext.fill] at captured
  | substBody _ _ => simp [OneHoleContext.fill] at captured
  | substReplacement _ _ => simp [OneHoleContext.fill] at captured
  | collection _ _ _ _ _ => simp [OneHoleContext.fill] at captured

/-- The image of a hole beneath an input is not the plugging of any rho
one-hole context. -/
theorem encode_input_not_oneHole (channel bound : Name) (n v : String) :
    ¬ ∃ context : OneHoleContext, ∀ plugged : Pattern,
      context.fill plugged = (ProcessContext.input channel bound .hole).encode n v plugged :=
  rhoInput_not_oneHole (piNameToRhoName channel) bound

end Mettapedia.Languages.ProcessCalculi.PiCalculus
