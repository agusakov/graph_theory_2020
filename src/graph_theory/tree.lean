import .path
import .graph_induction
import .subgraph

-- from math 688 notes, lec-19

universe u
variables {V : Type u}

-- TO DO:
    -- define components (they are used twice here), give them some lemmas
    -- prove that removing a vertex from a tree results in a graph whose components are trees with smaller size
    -- concrete development of the category of graphs so we can prove useful properties (see Hedetniemi branch)

-- might be useful:
    -- `finset.eq_singleton_iff_unique_mem` says `s = {a} ↔ a ∈ s ∧ ∀ x ∈ s, x = a`

section classical
open_locale classical

namespace simple_graph

-- create some sort of type coercion for edges in subgraph and supergraph

variables {V} (T : simple_graph V) (a b : V) --(S : simple_graph (λ v, v ≠ a))

#check T.adj a b

def acyclic : Prop := ∀ (p : T.path), ¬ p.is_cycle
-- CR : changing the definition from 
    -- ∀ (p : T.path), ¬ p.simple_cycle
-- to
    -- ∀ (p : T.path), ¬ p.is_cycle
-- the simple_cycle definition is annoying because it has the extra condition that p is a tour
-- we don't need that condition here (i don't think)

class tree : Prop := 
(connected : connected T)
(acyclic : acyclic T)
#check T.connected

--def tree : Prop := connected T ∧ acyclic T

def leaf (v : V) [fintype (T.neighbor_set v)] : Prop := T.degree v = 1

#check fintype.card

namespace path

variables [∀ v, fintype (T.neighbor_set v)] [tree T] (p : path T)

-- move this to simple_graph later (need to prove that `p.is_tour` and therefore `p.is_maximal` exists in any finite simple graph)
lemma fin_max_tour [fintype V] [decidable_eq V] [nonempty V]: ∃ (p : path T), p.is_maximum_length :=
begin
    
    -- show that if the number of vertices is finite then the path lengths are all finite
    -- use the fact that you have an upper bound for sets of integers
    /-have h2 := fintype.exists_pair_of_one_lt_card h,
    cases h2 with a hb,
    cases hb with b h3,-/ -- don't think we want to pick arbitrary a and b
    --have h4 := T.connected,
    -- we're gonna need the bijection (λ (p : path), p.length) in order to find a maximum because then we can find a finite set on ℕ

    sorry,
end

/- Theorem 1: every tree on n ≥ 2 vertices contains at least two vertices of degree 1 -/
lemma two_deg_one [fintype V] [decidable_eq V] [nonempty V] : ∃ (v₁ v₂ : V), v₁ ≠ v₂ ∧ T.leaf v₁ ∧ T.leaf v₂ :=
begin
    /-have h2 := fintype.exists_pair_of_one_lt_card h,
    cases h2 with a hb,
    cases hb with b h3,
    use a,
    use b,
    split,
    exact h3, -/
    -- Proof outline:
    -- let p = x0 x1 ... xk in T be a maximal path in tree T
    have h3 := fin_max_tour T,
        -- Sub-lemma : prove that maximal paths exist
        -- use `p.tail.length` (number of edges in `p`)
    cases h3 with p hp,
    cases hp with ht hl,
    use p.head,
    use p.last,
    split,
    change ¬ p.is_cycle,
    have : T.acyclic := tree.acyclic,
    specialize this p,
    exact this,
    split,
    by_contra,
    have ha : ∃ v : V, T.adj p.head v ∧ v ∉ p.vertices,
    -- so with assumption a, we have that the cardinality of the edgeset of p.head is greater than 1
    -- shit not exactly, v.leaf means its cardinality is exactly one
    -- so we also need T.connected
    -- i think we need a lemma for T.connected that says all vertices have degree ≥ 1
    --push_neg at a,
    
    -- assume for contradiction that we have some neighbor y of x0, where y ≠ x1. this gives us two cases:
        -- either y is contained in a path that links back up with the original path, so acyclicity is violated
        -- or y is contained in a path that does not link back up, which then makes that new path an extension of the original, so maximality of p is violated
            -- `p.cons e hp hs` is the path extending `p` by edge `e`.
            -- (these two things should probably be their own lemmas so we can just apply them to x0 and xk)
    -- so then x0 does not have any neighbors besides x1, and therefore has degree 1
    -- similar argument goes for xk, which gives us at least two vertices in T that are leaves
    sorry,
    sorry,
    sorry,
end


/- Theorem 2: if T is a tree on n ≥ 2 vertices and x is a leaf, then the graph obtained by removing x from T is a tree on n - 1 vertices -/
-- this should probably be made with more general lemmas
section other
/-lemma acyclic_subgraph_acyclic (t : acyclic T) (s : set V) : acyclic (induced_subgraph V T s) :=
begin
    -- Proof outline:
    -- T has no cycles so T \ {x} has no cycles
    sorry,
end -- generalize to any subgraph once that's defined-/

variable (x : V)

--vertex_mem (v : V) (p : G.path) : Prop := v ∈ p.vertices

-- is this actually useful? who knows
/-lemma leaf_path_endpoint (p : T.path) (h1 : T.leaf x) (h2 : x ∈ p.vertices) : p.head = x ∨ p.last = x :=
begin
    -- `rw mem_neighbor_finset` says `w ∈ G.neighbor_finset v ↔ G.adj v w`
    unfold leaf at h1,
    unfold degree at h1,
    rw finset.card_eq_one at h1,
    cases h1 with w hw,
    rw finset.eq_singleton_iff_unique_mem at hw,
    cases hw with hm hu,
    -- reverse (head :: tail) to, well, reverse it
    -- list.head (list.reverse (head :: tail) is the new list head
    sorry,
end-/

/-lemma connected_rmleaf_connected (t : connected T) {x : V} (h : T.leaf x) : connected (induced_subgraph V T (λ v, v ≠ x)) :=
begin
    -- Proof outline:
    -- there are uv paths for all u v in T
    
    -- if T.leaf x and x ∈ p, x must either be p.head or p.last ?
        -- should this be its own sub-lemma?
    -- T.connected means there are paths from every vertex to every vertex
    unfold connected,
    unfold connected at t,
    intros h1 h2,
    sorry,
end-/

end other

/-instance tree_rmleaf_is_tree {x : V} (h : T.leaf x) : tree (induced_subgraph V T (λ v, v ≠ x)) :=
{ connected := T.connected_rmleaf_connected tree.connected h, 
  acyclic := T.acyclic_subgraph_acyclic tree.acyclic _
}-/


/- Theorem 3: TFAE
    (a) T is a tree
    (b) There exists a unique path between any two distinct vertices of T
    (c) T is a connected graph on n vertices with n-1 edges
    (d) T is an acyclic graph on n vertices with n-1 edges -/

-- Proof outline:
/- Lemma 1: (a) → (b) : T is a tree → there exists a unique path between any two distinct vertices -/
lemma tree_unique_path [inhabited V] (t : tree T) (u v : V) (p : T.path) (q : T.path) : (p.head = q.head) ∧ (p.last = q.last) → p = q :=
begin
-- Subproof outline:
    -- let u,v be distinct vertices in T
    -- T is a tree, so a uv path p exists
        -- we already have uv path guaranteed by definition of tree
    intro h,
    cases h with hh hl,
    rw path.eq_of_vertices_eq,
    -- suppose for contradiction that another path uv path q exists, p ≠ q (negation of eq_of_vertices_eq?)
    by_contra,
    -- there exists w s.t. w ∈ p and w ∈ q, where w is the last vertex before p and q diverge (maybe make a lemma for this)
        -- shit this is gonna be tricky
        -- (this doesn't cover the edge case that u is adjacent to v, which is false by the condition that we have a simple graph. this is a problem. fix the definition somehow)
    -- p.last = q.last, so we must have a vertex w' in p,q (could be v) such that (figure out how to say this correctly) w'.tail ∈ p ∧ w'.tail ∈ q (also this should probably be a path lemma)
    -- now, this means that we can build a path from w back to itself using the segments w to w' in p and q (do we have reversible paths in path.lean?)
    sorry,
end


/- Lemma 2: (b) → (c) : there exists a unique path between any two distinct vertices → T is connected on n vertices with n - 1 edges -/
-- note: no mention of T being a tree here, so that's not one of our assumptions (and can be used on any simple graph i think)
-- Subproof outline: (strong induction on V.card)
    -- Base Case: trivially true for V.card = 1, but that's because we have no edges
        -- this might be a problem - if we don't have loops, how can we say the individual vertex has a path to itself?
        -- maybe need to show it's true for V.card = 2?
    -- IH: assume the statement holds for V.card < n vertices
    -- let V.card = n
    -- let u,v be distinct vertices in T
    -- by assumption, a uv path p exists
    -- since p is unique, removing an edge x from p (and in fact the edge set of T. maybe new induced subgraph definition?) disconnects u from v
    -- the resultant graph contains two components H and K on vertex sets U and W, where U.card < n and W.card < n, so by IH we have U.card - 1 edges in H and W.card - 1 edges in K, and U.card + W.card = n - 1, which gives us n - 2 edges in H ∪ K. then adding back x, we have n - 1 edges in T.


/- Lemma 3: (c) → (d) : T is connected on n vertices with n - 1 edges → T is acyclic on n vertices with n - 1 edges -/
-- note: no mention of T being a tree here, so that's not one of our assumptions (and can be used on any simple graph)
-- Subproof outline:
    -- suppose for contradiction that T has a cycle C of length k ≥ 3.
    -- C contains k vertices and k edges (i think there are lemmas for this in path.lean)
    -- since k ≤ n (by (c)), there are n - k vertices in T that are not in C
    -- ∀ v : V, v ∉ C
        -- consider a path connecting v to a vertex in C
        -- each path will have at least 1 edge
        -- the number of edges connecting the rest of the vertices in V to those in C is at least n - k
        -- this means we have n - k + k = n ≤ edges in T, which is a contradiction

/- Lemma 4: (d) → (a) : T is acyclic on n vertices with n - 1 edges → T is a tree -/ 
-- note: this time we want to prove that T is a tree, so that's not one of our assumptions (and can be used on any simple graph)
-- Subproof outline:
    -- T is acyclic, V.card = n
    -- suppose T has k ≥ 1 components T1, T2, ... , Tk (oh boy finset time)
    -- since T is acyclic and components are connected, each Ti is a tree (say they're on Vi, and Vi.card = ni)
    -- since each Ti is a tree, we can use (a) → (b) → (c) to get that each Ti has ni - 1 edges
    -- therefore, T has ∑ (ni - 1) = (∑ ni) - k = n - k edges
    -- since n - k = n - 1, we have k = 1, so we have 1 component (which is connected by definition of component)
    -- the one component is all of T (make this a lemma about components)
    -- therefore T is acyclic and connected, and must be a tree

-- i guess make a bunch of iff lemmas out of that so i can rw stuff

-- make Prüfer codes
end path

end simple_graph

end classical

#lint
-- CR : missing docstrings, unused arguments, and "inhabited"