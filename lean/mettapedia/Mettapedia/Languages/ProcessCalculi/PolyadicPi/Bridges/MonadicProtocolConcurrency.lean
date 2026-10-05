import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol

/-!
# Multiple calls to a unary tuple receiver

These paths use the actual private-session protocol and one persistent public
receiver. Each selected session completes with its own two fields. Equal calls
retain their multiplicity; choosing a different sender order changes only the
order of the selected blocks. The statements preserve these supplied paths,
without asserting that all untyped surrounding processes obey the protocol.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.NativeTypes

/-- A fixed parallel component accompanies every actual firing and the exact
endpoint of a retained protocol path. -/
def parallelPath {Γ : Ctx sig} {source target : Proc Γ}
    (path : (operationalTheory Γ).RewritePath source target) (frame : Proc Γ) :
    (operationalTheory Γ).RewritePath (par source frame) (par target frame) :=
  match path with
  | .nil _ => .nil _
  | .cons first rest => .cons (modulo_add_parallel first frame) (parallelPath rest frame)

theorem parallelPath_length : ∀ {Γ : Ctx sig} {source target : Proc Γ}
    (path : (operationalTheory Γ).RewritePath source target) (frame : Proc Γ),
    (parallelPath path frame).length = path.length
  | _, _, _, .nil _, _ => rfl
  | _, _, _, .cons _ rest, frame => by
      simp only [parallelPath, Mettapedia.GSLT.GSLT.RewritePath.length]
      rw [parallelPath_length rest frame]
termination_by _ _ _ path _ => path.length
decreasing_by simp only [Mettapedia.GSLT.GSLT.RewritePath.length]; omega

private theorem swapEndpoints {Γ : Ctx sig} (p q r : Proc Γ) :
    StructuralEq (par (par p q) r) (par (par r q) p) :=
  .trans (.parAssoc _ _ _) (.trans (.par (.refl _) (.parComm _ _)) (.parComm _ _))

/-- Two real senders share one public replicated receiver. They are selected
in the stated order and return their own ordered pairs; private names are
allocated separately by the two syntactic sender occurrences. -/
def twoSendersPath {Γ : Ctx sig} (channel first₁ second₁ first₂ second₂ : Name Γ)
    (body : Proc (.nm :: .nm :: Γ)) :
    (operationalTheory Γ).RewritePath
      (par (par (sendPair channel first₁ second₁) (rep (receivePair channel body)))
        (sendPair channel first₂ second₂))
      (par (openPair body first₁ second₁)
        (par (openPair body first₂ second₂) (rep (receivePair channel body)))) :=
  .cons (modulo_add_parallel (server_session_fires channel first₁ second₁ body) _)
    (.cons (modulo_add_parallel (modulo_add_parallel (callback_fires first₁ second₁ body) _) _)
      (.cons (modulo_add_parallel (modulo_add_parallel (first_field_fires first₁ second₁ body) _) _)
        (.cons (modulo_add_parallel (modulo_add_parallel (second_field_fires first₁ second₁ body) _) _)
          (.cons (modulo_source_equation (swapEndpoints _ _ _)
              (modulo_add_parallel (server_session_fires channel first₂ second₂ body) _))
            (.cons (modulo_add_parallel (modulo_add_parallel (callback_fires first₂ second₂ body) _) _)
              (.cons (modulo_add_parallel (modulo_add_parallel (first_field_fires first₂ second₂ body) _) _)
                (.cons (modulo_target_equation
                    (modulo_add_parallel (modulo_add_parallel (second_field_fires first₂ second₂ body) _) _)
                    (.parComm _ _)) (.nil _))))))))

/-- Two selected requests take eight unary communications, including six
administrative communications. Parallel structure is not an extra firing. -/
theorem twoSendersPath_length {Γ : Ctx sig} (channel first₁ second₁ first₂ second₂ : Name Γ)
    (body : Proc (.nm :: .nm :: Γ)) :
    (twoSendersPath channel first₁ second₁ first₂ second₂ body).length = 2 * 4 := rfl

/-- Duplicated requests remain two requests, with two returned occurrences
and the same retained server. -/
def duplicateSendersPath {Γ : Ctx sig} (channel first second : Name Γ)
    (body : Proc (.nm :: .nm :: Γ)) :
    (operationalTheory Γ).RewritePath
      (par (par (sendPair channel first second) (rep (receivePair channel body)))
        (sendPair channel first second))
      (par (openPair body first second)
        (par (openPair body first second) (rep (receivePair channel body)))) :=
  twoSendersPath channel first second first second body

theorem duplicateSendersPath_length {Γ : Ctx sig} (channel first second : Name Γ)
    (body : Proc (.nm :: .nm :: Γ)) :
    (duplicateSendersPath channel first second body).length = 8 := rfl

/-- Both public requests are accepted before either payload is delivered.
Their callback and payload steps then interleave. Each private session still
returns the tuple supplied by its own sender, and the receiver is retained. -/
def interleavedSendersPath {Γ : Ctx sig} (channel first₁ second₁ first₂ second₂ : Name Γ)
    (body : Proc (.nm :: .nm :: Γ)) :
    (operationalTheory Γ).RewritePath
      (par (par (sendPair channel first₁ second₁) (rep (receivePair channel body)))
        (sendPair channel first₂ second₂))
      (par (openPair body first₁ second₁)
        (par (openPair body first₂ second₂) (rep (receivePair channel body)))) :=
  .cons (modulo_add_parallel (server_session_fires channel first₁ second₁ body) _)
    (.cons (modulo_source_equation (swapEndpoints _ _ _)
        (modulo_add_parallel (server_session_fires channel first₂ second₂ body) _))
      (.cons (modulo_source_equation (swapEndpoints _ _ _)
          (modulo_add_parallel (modulo_add_parallel (callback_fires first₁ second₁ body) _) _))
        (.cons (modulo_source_equation (swapEndpoints _ _ _)
            (modulo_add_parallel (modulo_add_parallel (callback_fires first₂ second₂ body) _) _))
          (.cons (modulo_source_equation (swapEndpoints _ _ _)
              (modulo_add_parallel (modulo_add_parallel (first_field_fires first₁ second₁ body) _) _))
            (.cons (modulo_source_equation (swapEndpoints _ _ _)
                (modulo_add_parallel (modulo_add_parallel (first_field_fires first₂ second₂ body) _) _))
              (.cons (modulo_add_parallel (modulo_add_parallel (second_field_fires first₂ second₂ body) _) _)
                (.cons (modulo_target_equation
                    (modulo_source_equation (swapEndpoints _ _ _)
                      (modulo_add_parallel (modulo_add_parallel (second_field_fires first₁ second₁ body) _) _))
                    (.trans (.parAssoc _ _ _) (.par (.refl _) (.parComm _ _))))
                  (.nil _))))))))

theorem interleavedSendersPath_length {Γ : Ctx sig} (channel first₁ second₁ first₂ second₂ : Name Γ)
    (body : Proc (.nm :: .nm :: Γ)) :
    (interleavedSendersPath channel first₁ second₁ first₂ second₂ body).length = 8 := rfl

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol
