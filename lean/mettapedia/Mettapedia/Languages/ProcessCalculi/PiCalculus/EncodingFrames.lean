import Mettapedia.Languages.ProcessCalculi.PiCalculus.EncodingEquivariance
import Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CongruenceInContext

/-!
# The image of a pi context as a rho one-hole context, up to congruence

On the nose the image of a pi context is an operation on rho terms.  Up to the
structural congruence of the rho calculus it is the plugging of a rho
one-hole context, once two things are made explicit.

* A parallel composition in the image is flattened; the one-hole context
  keeps it as a two-component composition, which is congruent to the
  flattened one.
* A hole beneath an input, a restriction or a replication is in the scope of
  a bound name.  What is plugged is first closed over the names captured on
  the way to the hole, the outermost at the greatest depth: the hole has a
  binding stage, and its argument is a term at that stage.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PiCalculus

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution (closeFVar)
open Mettapedia.OSLF.MeTTaIL.DerivedContexts

open private rhoPar_to_two from
  Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation

namespace ProcessContext

/-- The number of names bound above the hole: the binding stage of the
hole. -/
def stage (context : ProcessContext) : Nat := context.captured.length

/-- The rho one-hole context of a pi context at a pair of names.  A parallel
composition is kept as a two-component composition; a binder is an
abstraction around the context of its body, closed over the bound name. -/
def frame : ProcessContext → String → String → OneHoleContext
  | .hole, _, _ => .hole
  | .parLeft inner right, n, v =>
      .collection .hashBag [] (inner.frame (n ++ "_L") v)
        [PiCalculus.encode right (n ++ "_R") v] none
  | .parRight left inner, n, v =>
      .collection .hashBag [PiCalculus.encode left (n ++ "_L") v]
        (inner.frame (n ++ "_R") v) [] none
  | .input channel bound inner, n, v =>
      .apply "PInput" [piNameToRhoName channel]
        (.lambda none ((inner.frame n v).closeName bound 0)) []
  | .nu bound inner, n, v =>
      .collection .hashBag [rhoOutput (.fvar v) (.fvar n)]
        (.apply "PInput" [.fvar n]
          (.lambda none ((inner.frame (n ++ "_" ++ n) v).closeName bound 0)) []) [] none
  | .replicate channel bound inner, n, v =>
      .apply "PReplicate" []
        (.apply "PInput" [piNameToRhoName channel]
          (.lambda none ((inner.frame (n ++ "_rep") v).closeName bound 0)) []) []

/-- Close what is plugged over the names captured on the way to the hole. -/
def capture : ProcessContext → Pattern → Pattern
  | .hole, plugged => plugged
  | .parLeft inner _, plugged => inner.capture plugged
  | .parRight _ inner, plugged => inner.capture plugged
  | .input _ bound inner, plugged => closeFVar inner.stage bound (inner.capture plugged)
  | .nu bound inner, plugged => closeFVar inner.stage bound (inner.capture plugged)
  | .replicate _ bound inner, plugged => closeFVar inner.stage bound (inner.capture plugged)

/-- The hole of the rho context sits beneath as many binders as the pi
context captures names. -/
theorem binders_frame :
    ∀ (context : ProcessContext) (n v : String), (context.frame n v).binders = context.stage
  | .hole, _, _ => rfl
  | .parLeft inner _, n, v => by
      simp only [frame, OneHoleContext.binders, binders_frame inner, stage, captured]
  | .parRight _ inner, n, v => by
      simp only [frame, OneHoleContext.binders, binders_frame inner, stage, captured]
  | .input _ bound inner, n, v => by
      simp only [frame, OneHoleContext.binders,
        OneHoleContext.binders_closeName bound (inner.frame n v) 0, binders_frame inner n v,
        stage, captured, List.length_cons]
  | .nu bound inner, n, v => by
      simp only [frame, OneHoleContext.binders,
        OneHoleContext.binders_closeName bound (inner.frame (n ++ "_" ++ n) v) 0,
        binders_frame inner (n ++ "_" ++ n) v, stage, captured, List.length_cons]
  | .replicate _ bound inner, n, v => by
      simp only [frame, OneHoleContext.binders,
        OneHoleContext.binders_closeName bound (inner.frame (n ++ "_rep") v) 0,
        binders_frame inner (n ++ "_rep") v, stage, captured, List.length_cons]

/-- Closing a congruence over a bound name and placing it beneath the
abstraction of the closed context. -/
theorem closed_congruent {inner : ProcessContext} {n v : String} {image plugged : Pattern}
    (bound : String)
    (related : RhoCalculus.StructuralCongruence image ((inner.frame n v).fill (inner.capture plugged))) :
    RhoCalculus.StructuralCongruence (closeFVar 0 bound image)
      (((inner.frame n v).closeName bound 0).fill
        (closeFVar inner.stage bound (inner.capture plugged))) := by
  have closed := RhoCalculus.StructuralCongruence.closeName bound related 0
  rw [OneHoleContext.closeFVar_fill, binders_frame, Nat.zero_add] at closed
  exact closed

/-- **The image of a context is, up to structural congruence, the plugging of
its rho one-hole context** into what is plugged closed over the captured
names. -/
theorem encode_congruent_frame :
    ∀ (context : ProcessContext) (n v : String) (plugged : Pattern),
      RhoCalculus.StructuralCongruence (context.encode n v plugged)
        ((context.frame n v).fill (context.capture plugged))
  | .hole, _, _, plugged => .refl plugged
  | .parLeft inner right, n, v, plugged => by
      refine .trans _ _ _ (rhoPar_to_two _ _) ?_
      exact RhoCalculus.StructuralCongruence.fill
        (.collection .hashBag [] .hole [PiCalculus.encode right (n ++ "_R") v] none)
        (encode_congruent_frame inner (n ++ "_L") v plugged)
  | .parRight left inner, n, v, plugged => by
      refine .trans _ _ _ (rhoPar_to_two _ _) ?_
      exact RhoCalculus.StructuralCongruence.fill
        (.collection .hashBag [PiCalculus.encode left (n ++ "_L") v] .hole [] none)
        (encode_congruent_frame inner (n ++ "_R") v plugged)
  | .input channel bound inner, n, v, plugged =>
      RhoCalculus.StructuralCongruence.fill
        (.apply "PInput" [piNameToRhoName channel] (.lambda none .hole) [])
        (closed_congruent bound (encode_congruent_frame inner n v plugged))
  | .nu bound inner, n, v, plugged =>
      RhoCalculus.StructuralCongruence.fill
        (.collection .hashBag [rhoOutput (.fvar v) (.fvar n)]
          (.apply "PInput" [.fvar n] (.lambda none .hole) []) [] none)
        (closed_congruent bound (encode_congruent_frame inner (n ++ "_" ++ n) v plugged))
  | .replicate channel bound inner, n, v, plugged =>
      RhoCalculus.StructuralCongruence.fill
        (.apply "PReplicate" []
          (.apply "PInput" [piNameToRhoName channel] (.lambda none .hole) []) [])
        (closed_congruent bound (encode_congruent_frame inner (n ++ "_rep") v plugged))

/-- **Equivariance up to structural congruence.**  The encoding of a plugged
context is congruent to the rho one-hole context of the context plugged with
the encoding of the process, taken at the name the context passes to its hole
and closed over the names the context captures. -/
theorem encode_fill_congruent_frame (context : ProcessContext) (process : Process)
    (n v : String) :
    RhoCalculus.StructuralCongruence (PiCalculus.encode (context.fill process) n v)
      ((context.frame n v).fill
        (context.capture (PiCalculus.encode process (context.parameter n) v))) := by
  rw [encode_fill]
  exact encode_congruent_frame context n v _

end ProcessContext

end Mettapedia.Languages.ProcessCalculi.PiCalculus
