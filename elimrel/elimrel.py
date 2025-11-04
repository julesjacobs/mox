# Eliminable relations

domains = {
    'uniqueness': ['unique', 'aliased'],
    'contention': ['uncontended', 'shared', 'contended'],
    'linearity': ['many', 'once'],
    'portability': ['portable', 'nonportable'],
    'areality': ['global','stack','borrowed']
}

def leqrel(dom):
    res = frozenset()
    for i in range(0, len(dom)):
        for j in range(i, len(dom)):
            res |= frozenset([(dom[i], dom[j])])
    return res

def eqrel(dom):
    return frozenset([(a,a) for a in dom])

# Subtype relations
relations = {}
for d in domains:
    relations[(d,d)] = frozenset([leqrel(domains[d])])

# In-relation for areality
relations[('areality','areality')] |= frozenset([leqrel(['borrowed']) |  leqrel(['global','stack'])])

# In-relation for uniqueness
relations[('uniqueness','uniqueness')] |= frozenset([leqrel(['aliased','unique'])])
# In-relation for contention
relations[('contention','contention')] |= frozenset([leqrel(['contended','shared','uncontended'])])


# Dagger relations

relations[('linearity', 'uniqueness')] = frozenset([
    frozenset([
        ('once', 'unique'),
        ('once', 'aliased'),
        ('many', 'aliased')
    ])
])

relations[('portability', 'contention')] = frozenset([
    frozenset([
        ('nonportable', 'contended'),
        ('nonportable', 'shared'),
        ('nonportable', 'uncontended'),
        ('portable', 'uncontended'),
    ])
])

def pprel(rel):
    s = []
    for (a,b) in rel:
        s.append(f"({a},{b})")
    return "{" + ",".join(s) + "}"

for pair in relations:
    print(f"Relations for ({pair[0]},{pair[1]}):")
    for relation in relations[pair]:
        print(f"- {pprel(relation)}")

# Completion

def rev(rel):
    return frozenset([
        (b,a) for (a,b) in rel
    ])

for dom1 in domains:
    for dom2 in domains:
        if (dom1, dom2) in relations:
            relations[(dom1,dom2)] |= frozenset(rev(rel) for rel in relations[(dom1,dom2)])

def compose(rel1, rel2):
    return frozenset([
        (a,b) for (a,c1) in rel1 for (c2,b) in rel2 if c1 == c2
    ])

def inter(rel1,rel2):
    return frozenset([
        (a,b) for (a,b) in rel1 if (a,b) in rel2
    ])

# Add complete relations
# for dom1 in domains:
#     for dom2 in domains:
#         if (dom1,dom2) not in relations:
#             relations[(dom1,dom2)] = frozenset()
#         relations[(dom1,dom2)] |= frozenset([
#             frozenset([(a,b)]) for a in domains[dom1] for b in domains[dom2]
#         ])

for dom in domains:
    # Add singletons
    relations[(dom,dom)] |= frozenset([
        frozenset([(a,a)]) for a in domains[dom]
    ])


changed = True
while changed:
    changed = False
    # Add intersections
    for dom in domains:
        if (dom,dom) in relations:
            for rel1 in relations[(dom,dom)]:
                for rel2 in relations[(dom,dom)]:
                    rel3 = inter(rel1,rel2)
                    if rel3 not in relations[(dom,dom)]:
                        changed = True
                        relations[(dom,dom)] |= frozenset([rel3])
    # Add compositions
    for dom1 in domains:
        for dom2 in domains:
            for dom3 in domains:
                dom12rels = relations.get((dom1, dom2), frozenset())
                dom23rels = relations.get((dom2, dom3), frozenset())
                for rel1 in dom12rels:
                    for rel2 in dom23rels:
                        rel12 = compose(rel1, rel2)
                        if rel12 not in relations.get((dom1, dom3), frozenset()):
                            changed = True
                            if (dom1, dom3) not in relations:
                                relations[(dom1, dom3)] = frozenset()
                            relations[(dom1, dom3)] |= frozenset([rel12])

print("\nAfter completion:")
for pair in relations:
    print(f"Relations for ({pair[0]},{pair[1]}) -- {len(relations[pair])}:")
    for relation in relations[pair]:
        print(f"- {pprel(relation)}")

# Unaries

unaries = {
    dom: frozenset([
        frozenset([a for (a,b) in rel if a==b])
        for rel in relations[(dom,dom)]   
    ]) for dom in domains
}

def ppunary(unary):
    return "{" + ",".join(unary) + "}"

print("\nUnaries:")
for dom in unaries:
    print(f"Unaries for {dom}:")
    for unary in unaries[dom]:
        print(f"- {ppunary(unary)}")

# Remove boxes

def is_box(rel):
    left = frozenset(p[0] for p in rel)
    right = frozenset(p[1] for p in rel)
    cart = frozenset((a,b) for a in left for b in right)
    return rel == cart

for dom in relations:
    relations[dom] = frozenset(rel for rel in relations[dom] if not is_box(rel))

print("\nAfter removing boxes:")
for pair in relations:
    print(f"Relations for ({pair[0]},{pair[1]}) -- {len(relations[pair])}:")
    for relation in relations[pair]:
        print(f"- {pprel(relation)}")
