import itertools

def verify_graph_a():
    # Graph A (McKay / GPT-5.1)
    # 0 : 9, 14, 15, 16
    # 1 : 7, 11, 13, 16
    # 2 : 8, 10, 12, 15
    # 3 : 6, 8, 13, 15, 16
    # 4 : 5, 7, 12, 14, 16
    # 5 : 4, 9, 10, 11, 13
    # 6 : 3, 10, 11, 12, 14
    # 7 : 1, 4, 9, 10, 15
    # 8 : 2, 3, 9, 11, 14
    # 9 : 0, 5, 7, 8, 12
    # 10 : 2, 5, 6, 7, 16
    # 11 : 1, 5, 6, 8, 15
    # 12 : 2, 4, 6, 9, 13
    # 13 : 1, 3, 5, 12, 14
    # 14 : 0, 4, 6, 8, 13
    # 15 : 0, 2, 3, 7, 11
    # 16 : 0, 1, 3, 4, 10

    adj = {
        0 : {9, 14, 15, 16},
        1 : {7, 11, 13, 16},
        2 : {8, 10, 12, 15},
        3 : {6, 8, 13, 15, 16},
        4 : {5, 7, 12, 14, 16},
        5 : {4, 9, 10, 11, 13},
        6 : {3, 10, 11, 12, 14},
        7 : {1, 4, 9, 10, 15},
        8 : {2, 3, 9, 11, 14},
        9 : {0, 5, 7, 8, 12},
        10 : {2, 5, 6, 7, 16},
        11 : {1, 5, 6, 8, 15},
        12 : {2, 4, 6, 9, 13},
        13 : {1, 3, 5, 12, 14},
        14 : {0, 4, 6, 8, 13},
        15 : {0, 2, 3, 7, 11},
        16 : {0, 1, 3, 4, 10}
    }
    
    return check_graph("Graph A (GPT-5.1)", adj)

def verify_graph_b():
    # Graph B (Gork)
    # 0:  1, 2, 4, 7, 11
    # 1:  0, 2, 5, 9, 14
    # 2:  0, 1, 6,10, 15
    # 3:  4, 5, 6, 8, 12
    # 4:  0, 3, 7,13, 16
    # 5:  1, 3, 8,10, 13
    # 6:  2, 3, 9,11, 16
    # 7:  0, 4, 10,12, 14
    # 8:  3, 5, 11,15, 16
    # 9:  1, 6, 12,13, 15
    # 10: 2, 5, 7, 13, 16
    # 11: 0, 6, 8, 14, 15
    # 12: 3, 7, 9, 14, 16
    # 13: 4, 5, 9, 10, 15
    # 14: 1, 7, 11, 12, 16
    # 15: 2, 8, 9, 11, 13
    # 16: 4, 6, 8, 10, 12

    adj = {
        0:  {1, 2, 4, 7, 11},
        1:  {0, 2, 5, 9, 14},
        2:  {0, 1, 6,10, 15},
        3:  {4, 5, 6, 8, 12},
        4:  {0, 3, 7,13, 16},
        5:  {1, 3, 8,10, 13},
        6:  {2, 3, 9,11, 16},
        7:  {0, 4, 10,12, 14},
        8:  {3, 5, 11,15, 16},
        9:  {1, 6, 12,13, 15},
        10: {2, 5, 7, 13, 16},
        11: {0, 6, 8, 14, 15},
        12: {3, 7, 9, 14, 16},
        13: {4, 5, 9, 10, 15},
        14: {1, 7, 11, 12, 16},
        15: {2, 8, 9, 11, 13},
        16: {4, 6, 8, 10, 12}
    }
    return check_graph("Graph B (Gork)", adj)

def check_graph(name, adj):
    print(f"Checking {name}...")
    n = 17
    
    # Check symmetry
    for u in range(n):
        for v in adj[u]:
            if u not in adj[v]:
                print(f"  Asymmetry found: {u}->{v} but not {v}->{u}")
                return False
            
    # Check degrees
    degrees = [len(adj[u]) for u in range(n)]
    print(f"  Degrees: {sorted(degrees)}")
    
    # Check Triangle-free
    triangles = 0
    for u in range(n):
        for v in adj[u]:
            if v > u:
                for w in adj[v]:
                    if w > v:
                        if w in adj[u]:
                            triangles += 1
                            print(f"  Triangle found: {u}, {v}, {w}")
    
    if triangles > 0:
        print(f"  FAILED: Found {triangles} triangles.")
        return False
    else:
        print("  PASSED: Triangle-free.")

    # Check Independence Number (No indep set of size 6)
    # Check if there is an independent set of size 6
    # Iterate over all combinations of 6 vertices
    print("  Checking for independent sets of size 6...")
    found_is_6 = False
    
    # Optimization: Backtracking search for max independent set is faster than checking all C(17,6) = 12376
    # But 12376 is small enough for brute force.
    
    count = 0
    for subset in itertools.combinations(range(n), 6):
        count += 1
        is_independent = True
        for i in range(len(subset)):
            for j in range(i + 1, len(subset)):
                u, v = subset[i], subset[j]
                if v in adj[u]:
                    is_independent = False
                    break
            if not is_independent:
                break
        
        if is_independent:
            print(f"  FAILED: Found independent set of size 6: {subset}")
            found_is_6 = True
            break
            
    if not found_is_6:
        print("  PASSED: No independent set of size 6 found.")
        # Double check size 5
        print("  Checking for independent set of size 5 (should exist)...")
        found_is_5 = False
        for subset in itertools.combinations(range(n), 5):
            is_independent = True
            for i in range(len(subset)):
                for j in range(i + 1, len(subset)):
                    u, v = subset[i], subset[j]
                    if v in adj[u]:
                        is_independent = False
                        break
                if not is_independent:
                    break
            if is_independent:
                print(f"  Found IS of size 5: {subset}")
                found_is_5 = True
                break
        if found_is_5:
             print("  Confirmed alpha(G) >= 5.")
        else:
             print("  WARNING: No independent set of size 5 found? (Unexpected)")

        return True
    return False

if __name__ == "__main__":
    res_a = verify_graph_a()
    print("-" * 20)
    res_b = verify_graph_b()
    
    if res_a and res_b:
        print("\nBoth graphs are valid critical graphs!")
    elif res_a:
        print("\nOnly Graph A (GPT-5.1) is valid.")
    elif res_b:
        print("\nOnly Graph B (Gork) is valid.")
    else:
        print("\nNeither graph is valid.")
