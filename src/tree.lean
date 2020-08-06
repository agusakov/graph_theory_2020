import path

-- from math 688 notes, lec-19

universe u
variables (V : Type u)


namespace simple_graph

def induced_subgraph (G : simple_graph V) (S : set V) : simple_graph S :=
{adj := λ a b, G.adj a b,
sym := λ a b h, G.sym h, 
loopless := λ x h, G.loopless x h}

variables {V} (T : simple_graph V)

def connected : Prop := ∀ (a b : V), ∃ (p : T.path), a = p.head ∧ b = p.last

def acyclic : Prop := ∀ (p : T.path), p.head ≠ p.last ∧ p.is_tour


def tree : Prop := connected T ∧ acyclic T

def leaf (v : V) [fintype (T.neighbor_set v)] : Prop := T.degree v = 1

variables [∀ v, fintype (T.neighbor_set v)]

-- every tree on n ≥ 2 vertices contains at least two vertices of degree 1

lemma two_deg_one (t : tree T) : ∃ (v₁ v₂ : V), v₁ ≠ v₂ ∧ T.leaf v₁ ∧ T.leaf v₂ :=
begin
    -- let p = x0 x1 ... xk in T. maximal path in T? how do i define maximal 
    sorry,
end

-- if T is a tree on n ≥ 2 vertices and x is a leaf, then the graph obtained by removing x from T is a tree on n - 1 vertices

variable (x : V)


/-lemma tree_rem_leaf_is_tree (t : tree T) (x : V) (h : T.leaf x) : tree (induced_subgraph T (λ v, v ≠ x)) :=
begin
    sorry,
end-/


-- T is a tree → there exists a unique path between any two distinct vertices


-- there exists a unique path between any two distinct vertices → T is connected on n vertices with n - 1 edges


-- T is connected on n vertices with n - 1 edges → T is acyclic on n vertices with n - 1 edges


-- T is acyclic on n vertices with n - 1 edges → T is a tree

-- i guess make a bunch of iff lemmas out of that

-- make Prüfer codes


end simple_graph