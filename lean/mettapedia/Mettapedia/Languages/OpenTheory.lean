import Mettapedia.Languages.OpenTheory.Substitution
import Mettapedia.Languages.OpenTheory.CoreRules
import Mettapedia.Languages.OpenTheory.Binding
import Mettapedia.Languages.OpenTheory.BindingRules
import Mettapedia.Languages.OpenTheory.TheoremSubstitutionRule
import Mettapedia.Languages.OpenTheory.PrimitiveRules
import Mettapedia.Languages.OpenTheory.AxiomPolicy
import Mettapedia.Languages.OpenTheory.AxiomPolicyCanary
import Mettapedia.Languages.OpenTheory.TheoryClosure
import Mettapedia.Languages.OpenTheory.TheoryClosureCanary
import Mettapedia.Languages.OpenTheory.TheoryReplay
import Mettapedia.Languages.OpenTheory.TheoryReplayCanary
import Mettapedia.Languages.OpenTheory.Definitions
import Mettapedia.Languages.OpenTheory.DefinitionsCanary
import Mettapedia.Languages.OpenTheory.PackageDefinitionOwnership
import Mettapedia.Languages.OpenTheory.PackageDefinitionOwnershipCanary
import Mettapedia.Languages.OpenTheory.NominalProvenanceBoundary
import Mettapedia.Languages.OpenTheory.NominalProvenanceBoundaryCanary
import Mettapedia.Languages.OpenTheory.CheckedSourceTheorem
import Mettapedia.Languages.OpenTheory.CheckedSourceTheoremCanary
import Mettapedia.Languages.OpenTheory.NIKAuthority
import Mettapedia.Languages.OpenTheory.NIKAuthorityCanary

/-!
# OpenTheory bridge interface

This module exposes provenance-sensitive typed syntax, the pinned
source-compatible substitution model, typed alpha-canonical sequents, and an
executable checker for all nine primitive theorem rules.  The rules have
Type-valued one-step certificates, independent declarative semantics, exact
success and failure correspondence, and deterministic combined dispatch.
Substitution uses the stricter `TermSubst.TypeCorrect` admission condition and
its type-preservation theorem.  Axiom policies and least premise closure keep
the primitive kernel distinct from each selected object theory.

Constant and type-operator definitions have exact executable admission gates
and provenance theorems.  Package-level printed-name ownership is separate
from provenance identity, and a proved alpha-collision shows why exact
definition provenance requires retained nominal source evidence.  A
source-retaining theorem carrier and constant-definition checker now project
exactly to the canonical pinned checker.  Every explicit decidable axiom
policy also induces a concrete NIK least-closure authority whose semantic
projection is precisely axiom-provenance authorization, not truth.  Closure
of the source-retaining carrier under every article command, recursive proof
trails, reader execution, semantic
conservativity of definitions, and adequacy for OpenTheory, HOL Light, or HOL4
artifacts remain separate obligations.  The standard theorem axioms
(extensionality, choice, and infinity) remain separate from the primitive
inference layer.
-/
