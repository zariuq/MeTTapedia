#!/usr/bin/env python3
"""Extract WordNet hypernymy from GF WordNet's taxonomy.txt.

Output: hypernymy.json — maps synsetId → [direct hypernym synsetIds]
Only includes synsets that appear in our concept_grounding.json.

Usage: cd lean-projects/algorithms && python3 gf_fragments/export_hypernymy.py
"""
import json, sys

def main():
    taxonomy_path = "/home/zar/claude/gf-wordnet/taxonomy.txt"
    grounding_path = "gf_fragments/concept_grounding.json"
    output_path = "gf_fragments/hypernymy.json"

    # 1. Build pos → synset_id map from taxonomy
    print(f"Reading {taxonomy_path}...")
    pos_to_synset = {}
    synset_to_pos = {}
    lines = []
    with open(taxonomy_path) as f:
        for line in f:
            lines.append(line)
            parts = line.strip().split(' ', 2)
            if len(parts) < 2:
                continue
            synset_id = parts[0]
            try:
                pos = int(parts[1])
            except ValueError:
                continue
            pos_to_synset[pos] = synset_id
            synset_to_pos[synset_id] = pos

    print(f"  Taxonomy synsets: {len(pos_to_synset)}")

    # 2. Extract direct hypernym edges (@ relation)
    direct = {}  # synset → [hypernym synsets]
    for line in lines:
        gloss_split = line.strip().split('|')
        tokens = gloss_split[0].split()
        if len(tokens) < 2:
            continue
        synset_id = tokens[0]

        # Parse past the synset_id, internal_pos, and [...] ranges
        i = 2
        in_brackets = False
        hypers = []
        while i < len(tokens):
            t = tokens[i]
            if t.startswith('[') or t.startswith('('):
                in_brackets = True
            if in_brackets:
                if ']' in t or ')' in t:
                    in_brackets = False
                i += 1
                continue
            if t == '@':
                if i + 1 < len(tokens):
                    try:
                        hyper_pos = int(tokens[i + 1])
                        hyper_synset = pos_to_synset.get(hyper_pos)
                        if hyper_synset:
                            hypers.append(hyper_synset)
                    except ValueError:
                        pass
                i += 2
            else:
                i += 1

        if hypers:
            direct[synset_id] = hypers

    print(f"  Synsets with hypernyms: {len(direct)}")
    print(f"  Total hypernym edges: {sum(len(v) for v in direct.values())}")

    # 3. Load grounding to filter to relevant synsets
    print(f"Reading {grounding_path}...")
    with open(grounding_path) as f:
        grounding = json.load(f)

    our_synsets = set()
    for entry in grounding.values():
        sid = entry.get("synset", "")
        if sid:
            our_synsets.add(sid)

    print(f"  Our synsets: {len(our_synsets)}")

    # 4. Build transitive closure up to depth 5 for our synsets
    # (to find useful background knowledge chains)
    relevant = {}
    for sid in sorted(our_synsets):
        if sid in direct:
            # Walk up the chain
            chain = []
            current = sid
            for _ in range(5):
                hypers = direct.get(current, [])
                if not hypers:
                    break
                # Take first (primary) hypernym
                parent = hypers[0]
                chain.append(parent)
                current = parent
            if chain:
                relevant[sid] = chain

    print(f"  Our synsets with hypernym chains: {len(relevant)}")

    # 5. Build the output: direct edges for all taxonomy + chains for ours
    # Only export direct edges where at least one endpoint is in our synsets
    # (to keep the file manageable)
    filtered_direct = {}
    for sid, hypers in direct.items():
        if sid in our_synsets or any(h in our_synsets for h in hypers):
            filtered_direct[sid] = hypers

    result = {
        "direct": filtered_direct,
        "chains": relevant,
    }

    print(f"  Filtered direct edges: {len(filtered_direct)}")

    with open(output_path, 'w') as f:
        json.dump(result, f, separators=(',', ':'))

    size_mb = len(json.dumps(result, separators=(',', ':'))) / 1024 / 1024
    print(f"Written {output_path} ({size_mb:.1f} MB)")

    # 6. Verification: check Example 74 chain
    print("\nVerification:")
    # sun_4_N → 09473603-n, star_1_N → 09467004-n
    sun_sid = "09473603-n"
    star_sid = "09467004-n"
    sun_chain = relevant.get(sun_sid, [])
    print(f"  sun ({sun_sid}) chain: {sun_chain[:5]}")
    print(f"  star in sun's chain: {star_sid in sun_chain}")

    # hydrogen_N → 14664612-n
    h_sid = "14664612-n"
    h_chain = relevant.get(h_sid, [])
    print(f"  hydrogen ({h_sid}) chain: {h_chain[:5]}")

    # element_3_N → 14647071-n (chemistry element)
    e_sid = "14647071-n"
    e_chain = relevant.get(e_sid, [])
    print(f"  element ({e_sid}) chain: {e_chain[:5]}")

if __name__ == "__main__":
    main()
