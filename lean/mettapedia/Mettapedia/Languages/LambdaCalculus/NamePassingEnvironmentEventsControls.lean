import Mettapedia.Languages.LambdaCalculus.NamePassingEnvironmentEvents

/-!
# Equal-endpoint environment occurrences retain their owners

Two equal declarations can service the same active reference. Consuming the
outer one or the inner one leaves the same expression, but their retained
constructor derivations point to different declaration owners. This is real
source multiplicity rather than two labels assigned to one erased derivation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.LambdaCalculus.NamePassing.Environment.EventControls

open Mettapedia.OSLF.Binding

abbrev Term (Γ : List Unit) := Expr () Γ

def value : Term [()] := .lam (.var .zero)
def twoDeclarations : Term [()] :=
  .carrier .zero value (.carrier .zero value (.var .zero))
def remainingDeclaration : Term [()] := .carrier .zero value value

def outerSelected : EventCertificate .carrierFetch twoDeclarations remainingDeclaration :=
  .carrierFetch .zero value (.carrier .zero value (.here .zero value))

def innerSelected : EventCertificate .carrierFetch twoDeclarations remainingDeclaration :=
  .carrier .zero value (.carrierFetch .zero value (.here .zero value))

/-- Both retained origins describe actual steps at the same supplied endpoints. -/
theorem both_are_source_events :
    Step .carrierFetch twoDeclarations remainingDeclaration ∧
      Step .carrierFetch twoDeclarations remainingDeclaration :=
  ⟨outerSelected.sound, innerSelected.sound⟩

theorem outer_owner : outerSelected.owner = [] := rfl
theorem inner_owner : innerSelected.owner = [.carrierBody] := rfl

/-- The service consumer is the same reference; it is the chosen declaration
owner that distinguishes these two events. -/
theorem same_reference :
    outerSelected.reference = innerSelected.reference ∧
      outerSelected.reference = some [.carrierBody, .carrierBody] := ⟨rfl, rfl⟩

theorem selected_derivations_distinct : outerSelected ≠ innerSelected := by
  intro equal
  have owners := congrArg EventCertificate.owner equal
  change [] = [Position.carrierBody] at owners
  cases owners

theorem selected_origins_distinct : outerSelected.origin ≠ innerSelected.origin := by
  intro equal
  have owners := congrArg EventOrigin.owner equal
  change [] = [Position.carrierBody] at owners
  cases owners

/-- No endpoint-only readout can recover which equal declaration was consumed. -/
theorem no_endpoint_owner :
    ¬ ∃ readout : Term [()] → Term [()] → List Position,
      ∀ certificate : EventCertificate .carrierFetch twoDeclarations remainingDeclaration,
        readout twoDeclarations remainingDeclaration = certificate.owner := by
  rintro ⟨readout, recovers⟩
  have owners := (recovers outerSelected).symm.trans (recovers innerSelected)
  change [] = [Position.carrierBody] at owners
  cases owners

def nestedOuterReference (stored : Term [()]) :
    FetchCertificate (.zero : Var [()] ()) value
      (.defn stored (.var (.succ .zero)))
      (.defn stored (NamePassing.weaken value)) :=
  .defn stored (.here (.succ .zero) (NamePassing.weaken value))

theorem nested_reference_address (stored : Term [()]) :
    (nestedOuterReference stored).address = [.definitionBody] := rfl

/-- Retaining an origin cannot fabricate capture of a freshly shadowing name. -/
theorem fresh_reference_not_a_certificate {target : Term [(), ()]} :
    ¬ Nonempty (FetchCertificate (.succ .zero) (NamePassing.weaken value)
      (.var .zero) target) := by
  rw [FetchCertificate.nonempty_iff]
  apply fetch_distinct_variable
  intro equal
  cases equal

end Mettapedia.Languages.LambdaCalculus.NamePassing.Environment.EventControls
