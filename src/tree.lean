import path

-- from math 688 notes, lec-19

universe u
variables (V : Type u)


namespace simple_graph

variables {V} (T : simple_graph V) [inhabited V] [fintype V] [∀ (v : V), fintype (T.neighbor_set v)]

def connected : Prop := ∀ (a b : V), ∃ (p : T.path), a = p.head ∧ b = p.last

def acyclic : Prop := ∀ (p : T.path), p.head ≠ p.last ∧ p.is_tour


def tree : Prop := connected T ∧ acyclic T

def leaf (v : V) : Prop := T.degree v = 1

-- every tree on n ≥ 2 vertices contains at least two vertices of degree 1

lemma two_deg_one (t : tree T) (h : 2 ≤ fintype.card V) : ∃ (v₁ v₂ : V), v₁ ≠ v₂ ∧ T.degree v₁ = 1 ∧ T.degree v₂ = 1 :=
begin
    -- let p = x0 x1 ... xk in T. maximal path in T? how do i define maximal 
    sorry,
end

-- if T is a tree on n ≥ 2 vertices and x is a leaf, then the graph obtained by removing x from T is a tree on n - 1 vertices

/-variables (x : V) (s : set.univ V) (S : induced_subgraph T (s\{x}))

lemma tree_rem_vertex_is_tree (t : tree T) (h : 2 ≤ fintype.card V) (x : V) (s : induced_subgraph T (set.univ\{x})) : tree (induced_subgraph T (set.univ\{x})) :=
begin

end-/


-- T is a tree → there exists a unique path between any two distinct vertices


-- there exists a unique path between any two distinct vertices → T is connected on n vertices with n - 1 edges


-- T is connected on n vertices with n - 1 edges → T is acyclic on n vertices with n - 1 edges


-- T is acyclic on n vertices with n - 1 edges → T is a tree

-- i guess make a bunch of iff lemmas out of that

-- make Prüfer codes


end simple_graph