import path

-- from math 688 notes

universe u
variables (V : Type u)

namespace simple_graph

variables {V} (G : simple_graph V) [inhabited V] [fintype V]

def connected : Prop := ∀ (a b : V), ∃ (p : G.path), a = p.head ∧ b = p.last

def acyclic : Prop := ∀ (p : G.path), p.head ≠ p.last


def tree : Prop := connected G ∧ acyclic G

--def leaf (v : V) : Prop := G.degree v = 1

-- every tree on n ≥ 2 vertices contains at least two vertices of degree 1

lemma two_deg_one (t : tree G) : 



end simple_graph