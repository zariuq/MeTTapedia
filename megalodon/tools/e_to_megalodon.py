#!/usr/bin/env python3
"""
E Prover to Megalodon Proof Translator

This tool parses E prover's CNFRefutation output and generates
Megalodon proof tactics for set-theoretic proofs.

Usage:
    python e_to_megalodon.py <e_proof_output> [megalodon_output]
    eprover --auto --proof-object problem.p | python e_to_megalodon.py -

The translator handles:
- Disjunction elimination via case analysis
- Unit resolution / subsumption resolution
- Simple propositional reasoning
"""

import re
import sys
from dataclasses import dataclass, field
from typing import List, Dict, Optional, Tuple, Set
from collections import defaultdict

@dataclass
class ProofStep:
    """Represents a single step in E's proof."""
    name: str
    formula_type: str  # fof or cnf
    role: str  # axiom, plain, negated_conjecture
    formula: str
    inference: Optional[str] = None
    parents: List[str] = field(default_factory=list)
    raw_line: str = ""

    def is_axiom(self) -> bool:
        return self.inference == 'file' or self.role == 'axiom'

    def is_unit_clause(self) -> bool:
        """Check if this is a unit clause (single literal)."""
        f = self.formula.strip()
        # No disjunctions and single literal
        return '|' not in f

    def is_negation(self) -> bool:
        """Check if this is a negation."""
        f = self.formula.strip()
        return f.startswith('~') or f.startswith('(~')

    def get_literals(self) -> List[str]:
        """Extract literals from a clause."""
        f = self.formula.strip()
        if f.startswith('(') and f.endswith(')'):
            f = f[1:-1]
        # Split on | but be careful with nested parens
        literals = []
        depth = 0
        current = ""
        for c in f:
            if c == '(':
                depth += 1
                current += c
            elif c == ')':
                depth -= 1
                current += c
            elif c == '|' and depth == 0:
                lit = current.strip()
                if lit:
                    literals.append(lit)
                current = ""
            else:
                current += c
        lit = current.strip()
        if lit:
            literals.append(lit)
        return literals


def parse_e_proof(proof_text: str) -> List[ProofStep]:
    """Parse E prover's CNFRefutation output into structured steps."""
    steps = []

    # Extract just the CNFRefutation part
    start = proof_text.find('# SZS output start CNFRefutation')
    end = proof_text.find('# SZS output end CNFRefutation')

    if start != -1 and end != -1:
        proof_text = proof_text[start:end]

    # Pattern for fof/cnf lines - handles multi-line
    lines = proof_text.split('\n')
    current_line = ""

    for line in lines:
        line = line.strip()
        if not line or line.startswith('#') or line.startswith('%'):
            continue

        current_line += " " + line

        # Check if line is complete (ends with . not inside parens)
        if current_line.strip().endswith('.'):
            parse_formula_line(current_line.strip(), steps)
            current_line = ""

    return steps


def parse_formula_line(line: str, steps: List[ProofStep]):
    """Parse a single fof/cnf formula line."""
    # Pattern: (fof|cnf)(name, role, formula, source).
    match = re.match(r'(fof|cnf)\(([^,]+),\s*([^,]+),\s*(.+)\)\.$', line, re.DOTALL)
    if not match:
        return

    formula_type = match.group(1)
    name = match.group(2).strip()
    role = match.group(3).strip()
    rest = match.group(4)

    # Find the source part (either file(...) or inference(...))
    # Need to handle nested parens

    # Try to find inference first
    inference_rule = None
    parents = []
    formula = ""

    # Look for inference( or file(
    inf_match = find_inference_section(rest)
    if inf_match:
        formula = inf_match[0]
        inference_rule = inf_match[1]
        parents = inf_match[2]
    else:
        # Just the formula
        formula = rest.strip()
        if formula.endswith(')'):
            # Might be file(...) at end
            idx = formula.rfind(', file(')
            if idx > 0:
                formula = formula[:idx].strip()
                inference_rule = 'file'

    step = ProofStep(
        name=name,
        formula_type=formula_type,
        role=role,
        formula=formula,
        inference=inference_rule,
        parents=parents,
        raw_line=line
    )
    steps.append(step)


def find_inference_section(rest: str) -> Optional[Tuple[str, str, List[str]]]:
    """Find and parse inference(...) or file(...) at end of formula string."""
    # Look for ', inference(' or ', file('

    # Find last ', inference(' or ', file('
    inf_idx = rest.rfind(', inference(')
    file_idx = rest.rfind(', file(')

    if inf_idx == -1 and file_idx == -1:
        return None

    if inf_idx > file_idx:
        # It's an inference
        formula = rest[:inf_idx].strip()
        inf_str = rest[inf_idx + 2:].strip()  # Skip ', '

        # Parse inference(rule, status, [parents])
        # inf_str starts with 'inference('
        if not inf_str.startswith('inference('):
            return None

        # Find matching close paren
        inner = extract_balanced_parens(inf_str[len('inference('):])
        if inner is None:
            return None

        # Parse: rule, [status(...)], [...parents...]
        parts = split_top_level(inner, ',')
        rule = parts[0].strip() if parts else 'unknown'

        # Find parent references
        parents = []
        for part in parts:
            # Look for step names like c_0_19, n1_not_adj_n2, etc.
            parent_matches = re.findall(r'\b(c_\d+_\d+|[a-z][a-z0-9_]*)\b', part)
            for p in parent_matches:
                if p not in ['status', 'thm', 'inference', 'fof', 'cnf', 'split', 'conjunct']:
                    parents.append(p)

        return (formula, rule, parents)
    else:
        # It's a file reference (axiom)
        formula = rest[:file_idx].strip()
        return (formula, 'file', [])


def extract_balanced_parens(s: str) -> Optional[str]:
    """Extract content until matching close paren."""
    depth = 1
    result = ""
    for c in s:
        if c == '(':
            depth += 1
        elif c == ')':
            depth -= 1
            if depth == 0:
                return result
        result += c
    return None


def split_top_level(s: str, sep: str) -> List[str]:
    """Split string by separator, respecting parentheses."""
    parts = []
    depth = 0
    current = ""
    i = 0
    while i < len(s):
        c = s[i]
        if c == '(' or c == '[':
            depth += 1
            current += c
        elif c == ')' or c == ']':
            depth -= 1
            current += c
        elif c == sep and depth == 0:
            parts.append(current)
            current = ""
        else:
            current += c
        i += 1
    if current:
        parts.append(current)
    return parts


def analyze_proof_structure(steps: List[ProofStep]) -> Dict:
    """Analyze the proof to understand its structure."""
    analysis = {
        'axioms': [],
        'goals': [],
        'derived': [],
        'final_step': None,
        'proof_type': 'unknown'
    }

    step_by_name = {s.name: s for s in steps}

    for step in steps:
        if step.is_axiom():
            analysis['axioms'].append(step)
        elif step.role == 'negated_conjecture':
            analysis['goals'].append(step)
        else:
            analysis['derived'].append(step)

        # Check if this is the final step (proves $false)
        if '$false' in step.formula:
            analysis['final_step'] = step

    # Determine proof type
    if analysis['final_step']:
        analysis['proof_type'] = 'refutation'

    return analysis


def generate_megalodon_disjunction_elim(steps: List[ProofStep], analysis: Dict) -> str:
    """
    Generate Megalodon proof for disjunction elimination proofs.

    These proofs have a big disjunction as axiom, and systematically
    eliminate each disjunct by showing it contradicts other axioms.
    """
    output = []
    output.append("(* Proof translated from E prover CNFRefutation *)")
    output.append("")

    # Find the main disjunction (largest clause)
    disjunctions = []
    negations = []

    for step in analysis['axioms']:
        lits = step.get_literals()
        if len(lits) > 1:
            disjunctions.append((step, lits))
        elif step.is_negation():
            negations.append(step)

    if not disjunctions:
        output.append("(* No disjunction found - simple proof *)")
        return '\n'.join(output)

    # Sort by number of literals
    disjunctions.sort(key=lambda x: len(x[1]), reverse=True)
    main_disj, main_lits = disjunctions[0]

    output.append(f"(* Main disjunction: {main_disj.name} with {len(main_lits)} literals *)")
    output.append(f"(* Literals: {main_lits} *)")
    output.append("")

    # Build negation map
    neg_map = {}
    for step in negations:
        f = step.formula.strip()
        if f.startswith('~'):
            lit = f[1:].strip()
            if lit.startswith('(') and lit.endswith(')'):
                lit = lit[1:-1]
            neg_map[lit] = step.name

    output.append(f"(* Negation axioms available: {list(neg_map.keys())[:5]}... *)")
    output.append("")

    # Generate the proof structure
    output.append("(* Megalodon proof strategy: *)")
    output.append("(* Use cases_* for case analysis on the disjunction *)")
    output.append("(* For each case, derive False from the corresponding negation axiom *)")
    output.append("")

    # Generate actual Megalodon tactics
    output.append("prove False.")
    output.append(f"(* Apply case analysis from {main_disj.name} *)")

    # For each literal in the disjunction
    for i, lit in enumerate(main_lits):
        output.append(f"(* Case {i+1}: assume {lit} *)")

        # Find if we have a negation for this literal
        clean_lit = lit.strip()
        if clean_lit in neg_map:
            output.append(f"  (* Contradicts {neg_map[clean_lit]} *)")

    return '\n'.join(output)


def generate_megalodon_proof(steps: List[ProofStep]) -> str:
    """Generate Megalodon proof tactics from parsed proof steps."""
    analysis = analyze_proof_structure(steps)

    output = []
    output.append("(* Proof translated from E prover CNFRefutation *)")
    output.append(f"(* Proof type: {analysis['proof_type']} *)")
    output.append(f"(* {len(analysis['axioms'])} axioms, {len(analysis['derived'])} derived steps *)")
    output.append("")

    # For refutation proofs, use disjunction elimination strategy
    if analysis['proof_type'] == 'refutation':
        output.append(generate_megalodon_disjunction_elim(steps, analysis))
        output.append("")
        output.append(generate_megalodon_orE_proof(steps))
        output.append("")
        resolution = generate_resolution_analysis(steps)
        if resolution:
            output.append(resolution)

    # Also output step-by-step analysis
    output.append("")
    output.append("(* === Detailed proof step analysis === *)")
    output.append("")

    for step in steps:
        output.append(f"(* {step.formula_type} {step.name}: {step.role} *)")
        output.append(f"(*   Formula: {step.formula[:80]}{'...' if len(step.formula) > 80 else ''} *)")
        if step.inference:
            output.append(f"(*   Inference: {step.inference} *)")
        if step.parents:
            output.append(f"(*   Parents: {step.parents[:5]}{'...' if len(step.parents) > 5 else ''} *)")
        output.append("")

    return '\n'.join(output)


def translate_simple_propositional(steps: List[ProofStep], axiom_map: Dict[str, str]) -> str:
    """
    Translate a simple propositional proof to Megalodon.

    axiom_map: maps axiom names in E to Megalodon hypothesis names
    """
    output = []

    analysis = analyze_proof_structure(steps)

    # Find the pattern: big disjunction + unit negations
    disjunctions = []
    negations = {}

    for step in analysis['axioms']:
        lits = step.get_literals()
        if len(lits) > 1:
            disjunctions.append((step.name, lits))
        elif step.is_negation():
            # Extract the positive literal from ~lit
            f = step.formula.strip()
            if f.startswith('~'):
                pos = f[1:].strip()
                if pos.startswith('(') and pos.endswith(')'):
                    pos = pos[1:-1]
                negations[pos] = step.name

    if not disjunctions:
        return "(* No disjunction pattern found *)"

    main_disj_name, main_lits = disjunctions[0]

    output.append(f"(* Disjunction: {main_disj_name} *)")
    output.append(f"(* Literals: {len(main_lits)} *)")

    # Check each literal has a negation
    all_covered = True
    for lit in main_lits:
        if lit not in negations:
            output.append(f"(* WARNING: No negation for {lit} *)")
            all_covered = False

    if all_covered:
        output.append("(* All cases covered by negation axioms *)")
        output.append("")
        output.append("(* Megalodon proof: *)")
        output.append("prove False.")
        output.append(f"apply cases_{len(main_lits)} {axiom_map.get(main_disj_name, main_disj_name)}.")
        for i, lit in enumerate(main_lits):
            neg_name = negations[lit]
            output.append(f"- (* Case: {lit} *)")
            output.append(f"  assume H: {lit}.")
            output.append(f"  exact {axiom_map.get(neg_name, neg_name)} H.")

    return '\n'.join(output)


def generate_orE_chain(literals: List[str], negation_hyps: Dict[str, str], indent: int = 0) -> List[str]:
    """
    Generate a chain of orE applications for disjunction elimination.

    For A | B | C | ... | N, generates:
    apply orE (A) (B | C | ... | N) Hdisj.
    - assume Ha: A. exact Hnot_a Ha.
    - assume Hrest: B | C | ... | N.
      [recursive case]
    """
    prefix = "  " * indent
    output = []

    if len(literals) == 0:
        return output
    elif len(literals) == 1:
        # Base case: single literal
        lit = literals[0]
        if lit in negation_hyps:
            output.append(f"{prefix}assume H: {lit}.")
            output.append(f"{prefix}exact {negation_hyps[lit]} H.")
        else:
            output.append(f"{prefix}(* No negation available for {lit} *)")
            output.append(f"{prefix}admit.")
        return output
    elif len(literals) == 2:
        # Two literals: simple orE
        left, right = literals
        output.append(f"{prefix}apply orE.")
        output.append(f"{prefix}- assume H: {left}.")
        if left in negation_hyps:
            output.append(f"{prefix}  exact {negation_hyps[left]} H.")
        else:
            output.append(f"{prefix}  admit.")
        output.append(f"{prefix}- assume H: {right}.")
        if right in negation_hyps:
            output.append(f"{prefix}  exact {negation_hyps[right]} H.")
        else:
            output.append(f"{prefix}  admit.")
        return output
    else:
        # Multiple literals: nested orE
        first = literals[0]
        rest = literals[1:]

        output.append(f"{prefix}apply orE.")
        output.append(f"{prefix}- (* Case: {first} *)")
        output.append(f"{prefix}  assume H: {first}.")
        if first in negation_hyps:
            output.append(f"{prefix}  exact {negation_hyps[first]} H.")
        else:
            output.append(f"{prefix}  admit.")
        output.append(f"{prefix}- (* Remaining {len(rest)} cases *)")

        # Recursive case
        sub_output = generate_orE_chain(rest, negation_hyps, indent + 1)
        output.extend(sub_output)

        return output


def generate_megalodon_direct_contradiction(steps: List[ProofStep]) -> str:
    """
    Generate Megalodon proof for direct contradiction (positive vs negative literal).
    """
    output = []

    # Find positive literals and negations from ALL steps (including derived)
    positives = {}
    negations = {}

    for step in steps:
        f = step.formula.strip()
        # Remove outer parens
        if f.startswith('(') and f.endswith(')'):
            f = f[1:-1]

        if f.startswith('~'):
            pos = f[1:].strip()
            if pos.startswith('(') and pos.endswith(')'):
                pos = pos[1:-1]
            negations[pos] = step.name
        elif '|' not in f and '&' not in f and '->' not in f and f != '$false':
            # Simple positive literal
            positives[f] = step.name

    # Find contradictions
    contradictions = []
    for lit, pos_name in positives.items():
        if lit in negations:
            contradictions.append((lit, pos_name, negations[lit]))

    if not contradictions:
        return None

    output.append("(* === Megalodon direct contradiction proof === *)")
    output.append("")

    for lit, pos_name, neg_name in contradictions:
        output.append(f"(* {pos_name} asserts: {lit} *)")
        output.append(f"(* {neg_name} asserts: ~{lit} *)")
        output.append("")
        output.append("prove False.")
        output.append(f"exact {neg_name} {pos_name}.")
        output.append("")

    return '\n'.join(output)


def extract_predicate_args(formula: str) -> Tuple[str, List[str]]:
    """Extract predicate name and arguments from a formula like 'pred(a,b,c)'."""
    formula = formula.strip()
    if formula.startswith('~'):
        formula = formula[1:].strip()

    match = re.match(r'(\w+)\(([^)]*)\)', formula)
    if match:
        pred = match.group(1)
        args_str = match.group(2)
        args = [a.strip() for a in args_str.split(',')] if args_str else []
        return pred, args
    return formula, []


def find_unification(clause1_lit: str, clause2_lit: str) -> Optional[Dict[str, str]]:
    """
    Find unification between two literals.
    Returns substitution mapping variables to terms.
    """
    pred1, args1 = extract_predicate_args(clause1_lit)
    pred2, args2 = extract_predicate_args(clause2_lit)

    if pred1 != pred2 or len(args1) != len(args2):
        return None

    subst = {}
    for a1, a2 in zip(args1, args2):
        # Variable starts with uppercase in TPTP
        if a1[0].isupper() and a1 not in subst:
            subst[a1] = a2
        elif a2[0].isupper() and a2 not in subst:
            subst[a2] = a1
        elif a1 != a2 and a1 not in subst and a2 not in subst:
            return None  # Can't unify

    return subst


def generate_superposition_proof(steps: List[ProofStep]) -> Optional[str]:
    """
    Generate Megalodon proof for superposition-based refutation.

    Strategy: Track the resolution chain and generate explicit
    instantiations of the universal formulas.
    """
    output = []
    step_map = {s.name: s for s in steps}

    # Find the original universal formula (usually from triangle_free or similar)
    universal_axioms = []
    unit_facts = []

    for step in steps:
        if step.is_axiom():
            f = step.formula.strip()
            if f.startswith('!['):
                universal_axioms.append(step)
            elif '|' not in f and not f.startswith('~'):
                unit_facts.append(step)

    # Find resolution chain
    resolution_steps = [s for s in steps if s.inference in ['spm', 'rw', 'sr', 'cn']]

    if not resolution_steps:
        return None

    output.append("(* === Megalodon superposition proof === *)")
    output.append("")

    # Build dependency graph to trace the proof
    output.append("(* Proof trace: *)")
    for step in resolution_steps:
        output.append(f"(*   {step.name}: {step.inference} from {step.parents} *)")
        output.append(f"(*     Result: {step.formula[:60]}... *)")

    output.append("")

    # Try to reconstruct the instantiation
    # For triangle_free style proofs: ~adj(X,Y) | ~adj(Y,Z) | ~adj(X,Z)
    # with unit facts adj(a,b), adj(b,c), adj(a,c)
    # The proof instantiates X=a, Y=b, Z=c

    if unit_facts:
        output.append("(* Unit facts (positive literals): *)")
        for uf in unit_facts:
            pred, args = extract_predicate_args(uf.formula)
            output.append(f"(*   {uf.name}: {pred}({', '.join(args)}) *)")
        output.append("")

    # Generate Megalodon proof skeleton
    output.append("(* Megalodon proof: *)")
    output.append("")

    # Collect all terms from unit facts
    all_terms = set()
    for uf in unit_facts:
        _, args = extract_predicate_args(uf.formula)
        all_terms.update(args)

    if universal_axioms and unit_facts:
        output.append("(* Given the universal formula and unit facts, *)")
        output.append("(* instantiate the universal formula with the concrete terms: *)")
        output.append(f"(*   Terms: {sorted(all_terms)} *)")
        output.append("")

        # Generate the actual proof
        if len(unit_facts) >= 3:
            # This looks like a triangle-free proof
            facts = [extract_predicate_args(uf.formula) for uf in unit_facts]
            pred_name = facts[0][0] if facts else "R"

            output.append("prove False.")
            output.append("")

            # Try to find a triangle pattern
            # adj(a,b), adj(b,c), adj(a,c) forms a triangle
            terms_by_pair = {}
            for uf in unit_facts:
                pred, args = extract_predicate_args(uf.formula)
                if len(args) == 2:
                    pair = tuple(sorted(args))
                    terms_by_pair[pair] = (uf.name, args)

            # Find three facts that form a triangle
            all_terms_list = sorted(all_terms)
            for i, t1 in enumerate(all_terms_list):
                for j, t2 in enumerate(all_terms_list[i+1:], i+1):
                    for t3 in all_terms_list[j+1:]:
                        p12 = tuple(sorted([t1, t2]))
                        p23 = tuple(sorted([t2, t3]))
                        p13 = tuple(sorted([t1, t3]))
                        if p12 in terms_by_pair and p23 in terms_by_pair and p13 in terms_by_pair:
                            h12, args12 = terms_by_pair[p12]
                            h23, args23 = terms_by_pair[p23]
                            h13, args13 = terms_by_pair[p13]
                            output.append(f"(* Triangle found: {t1}, {t2}, {t3} *)")
                            output.append(f"(* Using: {h12}, {h23}, {h13} *)")
                            output.append("")
                            output.append(f"(* Apply triangle_free with x={t1}, y={t2}, z={t3}: *)")
                            output.append(f"exact Htf {t1} {t2} {t3} {h12} {h23} {h13}.")
                            return '\n'.join(output)

        # Fallback: just show the structure
        output.append("(* Instantiate Htf with appropriate terms and facts *)")
        output.append("exact Htf _ _ _ H1 H2 H3.  (* fill in terms *)")

    return '\n'.join(output)


def generate_resolution_analysis(steps: List[ProofStep]) -> str:
    """
    Analyze resolution steps (spm, rw) to help with Megalodon translation.
    """
    output = []

    # First try to generate a proper superposition proof
    spm_proof = generate_superposition_proof(steps)
    if spm_proof:
        output.append(spm_proof)
        output.append("")

    output.append("(* === Resolution proof analysis === *)")
    output.append("")

    # Build dependency graph
    step_map = {s.name: s for s in steps}

    # Find resolution steps
    resolution_steps = [s for s in steps if s.inference in ['spm', 'rw', 'sr']]

    if not resolution_steps:
        return '\n'.join(output) if output else None

    output.append(f"(* Found {len(resolution_steps)} resolution steps *)")
    output.append("")

    for step in resolution_steps:
        output.append(f"(* {step.name}: {step.formula[:60]}{'...' if len(step.formula) > 60 else ''} *)")
        output.append(f"(*   Rule: {step.inference} *)")
        output.append(f"(*   From: {step.parents} *)")

        # Try to explain the step
        if step.inference == 'spm':
            output.append("(*   Superposition: resolves two clauses by unification *)")
        elif step.inference == 'rw':
            output.append("(*   Rewrite: applies an equality to rewrite term *)")
        elif step.inference == 'sr':
            output.append("(*   Subsumption resolution: removes subsumed literals *)")

        # Megalodon hint
        f = step.formula.strip()
        if '|' in f:
            output.append("(*   Megalodon: may need orE or case analysis *)")
        elif f.startswith('~'):
            output.append("(*   Megalodon: negation - may use apply or exact *)")
        else:
            output.append("(*   Megalodon: positive fact - may use exact *)")

        output.append("")

    return '\n'.join(output)


def generate_megalodon_orE_proof(steps: List[ProofStep]) -> str:
    """
    Generate Megalodon proof using orE chains for disjunction elimination.
    """
    analysis = analyze_proof_structure(steps)
    output = []

    # First, try direct contradiction
    direct = generate_megalodon_direct_contradiction(steps)
    if direct:
        return direct

    # Find disjunctions and negations
    disjunctions = []
    negations = {}

    for step in analysis['axioms']:
        lits = step.get_literals()
        if len(lits) > 1:
            disjunctions.append((step, lits))
        elif step.is_negation():
            f = step.formula.strip()
            if f.startswith('~'):
                pos = f[1:].strip()
                if pos.startswith('(') and pos.endswith(')'):
                    pos = pos[1:-1]
                negations[pos] = f"Hneg_{step.name}"

    if not disjunctions:
        return "(* No disjunction found *)"

    # Sort by number of literals
    disjunctions.sort(key=lambda x: len(x[1]), reverse=True)
    main_step, main_lits = disjunctions[0]

    output.append("(* === Megalodon orE-chain proof === *)")
    output.append("")
    output.append("(* Hypotheses needed: *)")
    disj_str = ' \\/ '.join(main_lits)
    output.append(f"assume Hdisj: {disj_str}.")
    for lit in main_lits:
        if lit in negations:
            output.append(f"assume {negations[lit]}: ~{lit}.")
    output.append("")
    output.append("prove False.")
    output.append("")

    # Generate orE chain
    chain = generate_orE_chain(main_lits, negations)
    output.extend(chain)

    return '\n'.join(output)


def main():
    import argparse
    parser = argparse.ArgumentParser(
        description="E Prover to Megalodon Proof Translator",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  eprover --auto --proof-object problem.p | python e_to_megalodon.py -
  python e_to_megalodon.py e_proof.out megalodon_proof.mg
  python e_to_megalodon.py -m orE e_proof.out

The translator analyzes E's CNFRefutation proofs and generates
Megalodon tactics, particularly for disjunction elimination proofs.
""")
    parser.add_argument('input', help='Input file (- for stdin)')
    parser.add_argument('output', nargs='?', help='Output file (stdout if omitted)')
    parser.add_argument('-m', '--mode', choices=['full', 'orE', 'summary'],
                       default='full', help='Output mode: full, orE (just proof), or summary')
    parser.add_argument('-q', '--quiet', action='store_true',
                       help='Suppress stderr messages')

    args = parser.parse_args()

    input_file = args.input
    output_file = args.output

    # Read input
    if input_file == '-':
        proof_text = sys.stdin.read()
    else:
        with open(input_file, 'r') as f:
            proof_text = f.read()

    # Parse and analyze
    steps = parse_e_proof(proof_text)

    if not args.quiet:
        print(f"Parsed {len(steps)} proof steps", file=sys.stderr)
        # Count by type
        axioms = sum(1 for s in steps if s.is_axiom())
        derived = len(steps) - axioms
        print(f"  {axioms} axioms, {derived} derived", file=sys.stderr)

    # Generate Megalodon proof based on mode
    if args.mode == 'orE':
        megalodon_proof = generate_megalodon_orE_proof(steps)
    elif args.mode == 'summary':
        analysis = analyze_proof_structure(steps)
        megalodon_proof = generate_megalodon_disjunction_elim(steps, analysis)
    else:
        megalodon_proof = generate_megalodon_proof(steps)

    # Output
    if output_file:
        with open(output_file, 'w') as f:
            f.write(megalodon_proof)
        if not args.quiet:
            print(f"Wrote Megalodon proof to {output_file}", file=sys.stderr)
    else:
        print(megalodon_proof)


if __name__ == '__main__':
    main()
