#!/usr/bin/env python3
"""Fetch DBpedia triples for science concepts and output as GFCore-compatible atoms.

Queries DBpedia's SPARQL endpoint for IsA (rdf:type, dbo:) and property triples,
mapping to GFCore atom format (JSON) for ingestion into the LP knowledge base.

Usage: cd lean-projects/algorithms && python3 gf_fragments/fetch_dbpedia.py
"""
import json, urllib.request, urllib.parse, sys, time

SPARQL_URL = "https://dbpedia.org/sparql"

def sparql_query(query: str) -> list:
    """Execute a SPARQL query against DBpedia and return bindings."""
    url = SPARQL_URL + "?query=" + urllib.parse.quote(query) + "&format=application%2Fsparql-results%2Bjson"
    req = urllib.request.Request(url)
    try:
        with urllib.request.urlopen(req, timeout=30) as resp:
            data = json.loads(resp.read())
            return data["results"]["bindings"]
    except Exception as e:
        print(f"  SPARQL error: {e}", file=sys.stderr)
        return []

def uri_to_name(uri: str) -> str:
    """Extract local name from a URI."""
    if "/" in uri:
        return uri.rsplit("/", 1)[-1]
    return uri

def fetch_science_triples(concepts: list[str]) -> list[dict]:
    """Fetch IsA and property triples for a list of DBpedia concepts."""
    atoms = []

    for concept in concepts:
        resource = f"http://dbpedia.org/resource/{concept}"
        print(f"Fetching {concept}...")

        # 1. Get rdf:type (IsA) triples
        query = f"""
        SELECT ?type WHERE {{
            <{resource}> a ?type .
            FILTER(STRSTARTS(STR(?type), "http://dbpedia.org/ontology/"))
        }} LIMIT 20
        """
        bindings = sparql_query(query)
        for b in bindings:
            type_name = uri_to_name(b["type"]["value"])
            atoms.append({
                "kind": "isa",
                "sub": concept,
                "sup": type_name,
                "source": f"DBpedia:rdf:type:{concept}"
            })
            print(f"  IsA({concept}, {type_name})")

        # 2. Get dbo: property triples (object properties)
        query = f"""
        SELECT ?p ?o WHERE {{
            <{resource}> ?p ?o .
            FILTER(STRSTARTS(STR(?p), "http://dbpedia.org/ontology/"))
            FILTER(isURI(?o))
            FILTER(STRSTARTS(STR(?o), "http://dbpedia.org/resource/"))
        }} LIMIT 30
        """
        bindings = sparql_query(query)
        for b in bindings:
            pred = uri_to_name(b["p"]["value"])
            obj = uri_to_name(b["o"]["value"])
            atoms.append({
                "kind": "rel",
                "pred": pred,
                "args": [concept, obj],
                "source": f"DBpedia:dbo:{concept}"
            })
            print(f"  Rel({pred}, [{concept}, {obj}])")

        # 3. Get dbo: literal properties (string/number)
        query = f"""
        SELECT ?p ?o WHERE {{
            <{resource}> ?p ?o .
            FILTER(STRSTARTS(STR(?p), "http://dbpedia.org/ontology/"))
            FILTER(isLiteral(?o))
            FILTER(LANG(?o) = 'en' || LANG(?o) = '')
        }} LIMIT 20
        """
        bindings = sparql_query(query)
        for b in bindings:
            pred = uri_to_name(b["p"]["value"])
            val = b["o"]["value"][:100]
            atoms.append({
                "kind": "attr",
                "entity": concept,
                "prop": pred,
                "value": val,
                "source": f"DBpedia:literal:{concept}"
            })

        time.sleep(0.5)  # be polite to the endpoint

    return atoms

def main():
    # Science concepts relevant to EntailmentBank
    concepts = [
        "Sun", "Star", "Moon", "Earth", "Planet",
        "Hydrogen", "Oxygen", "Water", "Carbon_dioxide",
        "Light", "Heat", "Energy", "Sound",
        "Rock_(geology)", "Mineral", "Erosion", "Weathering",
        "Gravity", "Magnetism", "Electricity",
        "Cell_(biology)", "Photosynthesis", "Ecosystem",
        "Mammal", "Reptile", "Amphibian", "Fish",
        "Atmosphere", "Weather", "Climate",
        "Solar_System", "Galaxy", "Milky_Way",
    ]

    print(f"Fetching {len(concepts)} concepts from DBpedia...")
    atoms = fetch_science_triples(concepts)

    output_path = "gf_fragments/dbpedia_atoms.json"
    with open(output_path, "w") as f:
        json.dump(atoms, f, indent=1)

    print(f"\nWritten {len(atoms)} atoms to {output_path}")

    # Summary
    isa_count = sum(1 for a in atoms if a["kind"] == "isa")
    rel_count = sum(1 for a in atoms if a["kind"] == "rel")
    attr_count = sum(1 for a in atoms if a["kind"] == "attr")
    print(f"  IsA: {isa_count}, Rel: {rel_count}, Attr: {attr_count}")

if __name__ == "__main__":
    main()
