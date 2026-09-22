import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Conversion.NativeConversionReceiptIngress

/-!
# Computed Pi and Sigma component conversion

An accepted native conversion between two dependent function or pair types
computes accepted conversion codes for both components. The construction first
joins the actual checked path, then decomposes each directed continuation. The
codomain remains in the extended context; no binder is dropped or substituted
by an arbitrary closed term.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeParallelReceipt

open Presentation NativeCompletedRootCertificate

def piPathView {n : Nat} {domain : Tower.Tm n} {codomain : Tower.Tm (n + 1)}
    {target : Tower.Tm n} (path : DirectedPath (.pi domain codomain) target) :
    Σ domain' codomain', PLift (target = .pi domain' codomain') ×
      DirectedPath domain domain' × DirectedPath codomain codomain' := by
  induction path with
  | nil => exact ⟨_, _, ⟨rfl⟩, .nil, .nil⟩
  | cons earlier last ih =>
      obtain ⟨middleDomain, middleCodomain, ⟨rfl⟩, first, second⟩ := ih
      change Receipt (.pi middleDomain middleCodomain) _ at last
      cases last with
      | pi domainStep codomainStep =>
          exact ⟨_, _, ⟨rfl⟩, .cons first domainStep, .cons second codomainStep⟩

def piPathToFixed {n : Nat} {domain domain' : Tower.Tm n}
    {codomain codomain' : Tower.Tm (n + 1)}
    (path : DirectedPath (.pi domain codomain) (.pi domain' codomain')) :
    DirectedPath domain domain' × DirectedPath codomain codomain' := by
  obtain ⟨actualDomain, actualCodomain, ⟨shape⟩, first, second⟩ := piPathView path
  obtain ⟨rfl, rfl⟩ := Tm.pi.inj shape
  exact ⟨first, second⟩

/-- Both outputs replay through the original checker, with the codomain still
scoped under its binder. The input need not have a congruence-shaped code. -/
def piComponents {n : Nat} {domain domain' : Tower.Tm n}
    {codomain codomain' : Tower.Tm (n + 1)}
    (certificate : Certificate (.pi domain codomain) (.pi domain' codomain')) :
    Certificate domain domain' × Certificate codomain codomain' := by
  obtain ⟨common, left, right⟩ := joinCertificate certificate
  obtain ⟨commonDomain, commonCodomain, ⟨rfl⟩, leftDomain, leftCodomain⟩ := piPathView left
  obtain ⟨rightDomain, rightCodomain⟩ := piPathToFixed right
  exact ⟨(replayPath leftDomain).trans (replayPath rightDomain).symm,
    (replayPath leftCodomain).trans (replayPath rightCodomain).symm⟩

def checkedPiComponents {n : Nat} (code : NativeRelatorConversionChecking.Code n)
    (domain domain' : Tower.Tm n) (codomain codomain' : Tower.Tm (n + 1)) :
    Option (Certificate domain domain' × Certificate codomain codomain') :=
  if accepted : NativeRelatorConversionChecking.check code
      (.pi domain codomain) (.pi domain' codomain') = true then
    some (piComponents ⟨code, accepted⟩)
  else none

theorem checkedPiComponents_domain {n : Nat}
    (code : NativeRelatorConversionChecking.Code n)
    (domain domain' : Tower.Tm n) (codomain codomain' : Tower.Tm (n + 1)) :
    (checkedPiComponents code domain domain' codomain codomain').isSome =
      NativeRelatorConversionChecking.check code (.pi domain codomain) (.pi domain' codomain') := by
  unfold checkedPiComponents
  split <;> simp_all

theorem piComponents_recheck {n : Nat} {domain domain' : Tower.Tm n}
    {codomain codomain' : Tower.Tm (n + 1)}
    (certificate : Certificate (.pi domain codomain) (.pi domain' codomain')) :
    NativeRelatorConversionChecking.check (piComponents certificate).1.code domain domain' = true ∧
      NativeRelatorConversionChecking.check (piComponents certificate).2.code codomain codomain' = true :=
  ⟨(piComponents certificate).1.checked, (piComponents certificate).2.checked⟩

#print axioms piPathView
#print axioms piComponents
#print axioms checkedPiComponents_domain
#print axioms piComponents_recheck

def sigmaPathView {n : Nat} {domain : Tower.Tm n} {codomain : Tower.Tm (n + 1)}
    {target : Tower.Tm n} (path : DirectedPath (.sigma domain codomain) target) :
    Σ domain' codomain', PLift (target = .sigma domain' codomain') ×
      DirectedPath domain domain' × DirectedPath codomain codomain' := by
  induction path with
  | nil => exact ⟨_, _, ⟨rfl⟩, .nil, .nil⟩
  | cons earlier last ih =>
      obtain ⟨middleDomain, middleCodomain, ⟨rfl⟩, first, second⟩ := ih
      change Receipt (.sigma middleDomain middleCodomain) _ at last
      cases last with
      | sigma domainStep codomainStep =>
          exact ⟨_, _, ⟨rfl⟩, .cons first domainStep, .cons second codomainStep⟩

def sigmaPathToFixed {n : Nat} {domain domain' : Tower.Tm n}
    {codomain codomain' : Tower.Tm (n + 1)}
    (path : DirectedPath (.sigma domain codomain) (.sigma domain' codomain')) :
    DirectedPath domain domain' × DirectedPath codomain codomain' := by
  obtain ⟨actualDomain, actualCodomain, ⟨shape⟩, first, second⟩ := sigmaPathView path
  obtain ⟨rfl, rfl⟩ := Tm.sigma.inj shape
  exact ⟨first, second⟩

/-- Both outputs replay through the original checker, with the codomain still
scoped under its binder. The input need not have a congruence-shaped code. -/
def sigmaComponents {n : Nat} {domain domain' : Tower.Tm n}
    {codomain codomain' : Tower.Tm (n + 1)}
    (certificate : Certificate (.sigma domain codomain) (.sigma domain' codomain')) :
    Certificate domain domain' × Certificate codomain codomain' := by
  obtain ⟨common, left, right⟩ := joinCertificate certificate
  obtain ⟨commonDomain, commonCodomain, ⟨rfl⟩, leftDomain, leftCodomain⟩ := sigmaPathView left
  obtain ⟨rightDomain, rightCodomain⟩ := sigmaPathToFixed right
  exact ⟨(replayPath leftDomain).trans (replayPath rightDomain).symm,
    (replayPath leftCodomain).trans (replayPath rightCodomain).symm⟩

def checkedSigmaComponents {n : Nat} (code : NativeRelatorConversionChecking.Code n)
    (domain domain' : Tower.Tm n) (codomain codomain' : Tower.Tm (n + 1)) :
    Option (Certificate domain domain' × Certificate codomain codomain') :=
  if accepted : NativeRelatorConversionChecking.check code
      (.sigma domain codomain) (.sigma domain' codomain') = true then
    some (sigmaComponents ⟨code, accepted⟩)
  else none

theorem checkedSigmaComponents_domain {n : Nat}
    (code : NativeRelatorConversionChecking.Code n)
    (domain domain' : Tower.Tm n) (codomain codomain' : Tower.Tm (n + 1)) :
    (checkedSigmaComponents code domain domain' codomain codomain').isSome =
      NativeRelatorConversionChecking.check code (.sigma domain codomain) (.sigma domain' codomain') := by
  unfold checkedSigmaComponents
  split <;> simp_all

theorem sigmaComponents_recheck {n : Nat} {domain domain' : Tower.Tm n}
    {codomain codomain' : Tower.Tm (n + 1)}
    (certificate : Certificate (.sigma domain codomain) (.sigma domain' codomain')) :
    NativeRelatorConversionChecking.check (sigmaComponents certificate).1.code domain domain' = true ∧
      NativeRelatorConversionChecking.check (sigmaComponents certificate).2.code codomain codomain' = true :=
  ⟨(sigmaComponents certificate).1.checked, (sigmaComponents certificate).2.checked⟩

#print axioms sigmaPathView
#print axioms sigmaComponents
#print axioms checkedSigmaComponents_domain
#print axioms sigmaComponents_recheck

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeParallelReceipt
