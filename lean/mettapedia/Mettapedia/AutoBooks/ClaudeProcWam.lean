/-
# Operational Semantics in Logical Form — Prolog/WAM Lane

Formalization of operational semantics and machine models for logic programming.

## Lanes

1. **WAM** — Warren Abstract Machine
   - Heap-based term representation
   - Register allocation and unification
   - Backtracking with choice points
   - Environment frames for procedures

2. **ProcessCalculi** — Session-typed process calculi
   - Pi-calculus with linear types
   - Propositions as sessions (Wadler 2012)
   - Polymorphic session types

3. **Governance** — Deontic/input-output logic
   - Input-output logics (Makinson & van der Torre)
   - LogiKey workbench foundations
   - Conflict-tolerant deontic reasoning

## References

### WAM
- Warren (1983): Abstract Prolog Instruction Set
- Aït-Kaci (1991): WAM Tutorial Reconstruction
- Bohrer & Crary (2018): TWAM Certifying Abstract Machine

### Process Calculi
- Caires & Pfenning (2010): Session types as propositions
- Wadler (2012): Propositions as sessions
- Toninho & Yoshida (2018): Polymorphic sessions

### Governance
- Makinson & van der Torre (2000): Input-output logics
- Benzmüller (2020): LogiKey workbench
- Robaldo (2024): Conflict-tolerant deontic RDF
-/

import Mettapedia.AutoBooks.ClaudeProcWam.WAM
import Mettapedia.AutoBooks.ClaudeProcWam.ProcessCalculi
import Mettapedia.AutoBooks.ClaudeProcWam.Governance
