import path

-- from math 688 notes, lec-19

universe u
variables (V : Type u)

namespace simple_graph

variables {V} (G : simple_graph V) [inhabited V] [fintype V] [∀ (v : V), fintype (G.neighbor_set v)]

def connected : Prop := ∀ (a b : V), ∃ (p : G.path), a = p.head ∧ b = p.last

def acyclic : Prop := ∀ (p : G.path), p.head ≠ p.last ∧ p.is_trail


def tree : Prop := connected G ∧ acyclic G

def leaf (v : V) : Prop := G.degree v = 1

-- every tree on n ≥ 2 vertices contains at least two vertices of degree 1

lemma two_deg_one (t : tree G) (h : 2 ≤ fintype.card V) : ∃ (v₁ v₂ : V), G.degree v₁ = 1 ∧ G.degree v₂ = 1 :=
begin
    sorry,
end

-- if T is a tree on n ≥ vertices and x is a leaf, then the graph obtained by removing x from T is a tree on n - 1 vertices

-- lol define induced subgraphs i guess


-- T is a tree → there exists a unique path between any two distinct vertices


-- there exists a unique path between any two distinct vertices → T is connected on n vertices with n - 1 edges


-- T is connected on n vertices with n - 1 edges → T is acyclic on n vertices with n - 1 edges


-- T is acyclic on n vertices with n - 1 edges → T is a tree

-- i guess make a bunch of iff lemmas out of that

-- make Prüfer codes


end simple_graph