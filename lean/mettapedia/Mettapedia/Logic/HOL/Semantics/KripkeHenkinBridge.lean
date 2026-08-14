import Mettapedia.Logic.HOL.Semantics.HeytingGeneral
import Mettapedia.Logic.HOL.Semantics.KripkeHenkinCanonical

/-!
# Kripke-Henkin Bridge Package

Public citation handle for the bridge between the substitutional
Kripke-Henkin presentation and the supported canonical membership interface.

This module re-exports:

- `HeytingSem.ofKripkeHenkin`, the embedding of every substitutional
  `KripkeHenkin` model into the Heyting-valued semantics;
- `KripkeHenkin.SupportedCanonicalFrame.SupportedMembershipConsequence` and
  the `Provable ↔ SupportedMembershipConsequence` interfaces;
- the provider-dispatched successor clauses
  `forces_imp_level_provider`, `forces_not_level_provider`, and
  `forces_all_level_provider`.

What this buys: a classical-style presentation bridge, conditional on
`SchedulerProvider`, the honest intuitionistic analogue of the classical
enumeration/Henkin-enumeration assumptions.  It connects the supported
canonical membership theorem-map to the older substitutional Kripke-Henkin
interface and to the Heyting package.

What this does not buy: it is not the main completeness route.  The
`FullPresentedUpgrade`, `LocalMembershipClauses`, and
`FullPresentedIntuitionisticWorld` interfaces remain quarantined hypothesis
packages.  This module does not discharge, revive, or delete them.
-/

