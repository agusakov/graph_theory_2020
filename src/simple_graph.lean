--universe u


--instance complete_graph_adj_decidable (V : Type u) [decidable_eq V] :
--#exit
/-
Copyright (c) 2020 Aaron Anderson, Jalex Stark, Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Aaron Anderson, Jalex Stark, Kyle Miller.
-/
import data.fintype.basic
import sym2
import tactic

open finset
-- noncomputable theory

/-!
# Simple graphs
This module defines simple graphs on a vertex type `V` as an
irreflexive symmetric relation.
There is a basic API for locally finite graphs and for graphs with
finitely many vertices.
## Main definitions
* `simple_graph` is a structure for symmetric, irreflexive relations
* `neighbor_set` is the `set` of vertices adjacent to a given vertex
* `neighbor_finset` is the `finset` of vertices adjacent to a given vertex,
   if `neighbor_set` is finite
## Implementation notes
* A locally finite graph is one with instances `∀ v, fintype (G.neighbor_set v)`.
* Given instances `decidable_rel G.adj` and `fintype V`, then the graph
is locally finite, too.
TODO: This is the simplest notion of an unoriented graph.  This should
eventually fit into a more complete combinatorics hierarchy which
includes multigraphs and directed graphs.  We begin with simple graphs
in order to start learning what the combinatorics hierarchy should
look like.
TODO: Part of this would include defining, for example, subgraphs of a
simple graph.
-/

universe u
variables (V : Type u)
/--
A simple graph is an irreflexive symmetric relation `adj` on a vertex type `V`.
The relation describes which pairs of vertices are adjacent.
There is exactly one edge for every pair of adjacent edges;
see `simple_graph.E` for the corresponding type of edges.
Note: The type of the relation is given as `V → set V` rather than
`V → V → Prop` so that, given vertices `v` and `w`, then `w ∈ G.adj v`
works as another way to write `G.adj v w`.  Otherwise Lean cannot find
a `has_mem` instance.
-/
@[ext] structure simple_graph :=
(adj : V → V → Prop)
(sym : symmetric adj . obviously)
(loopless : irreflexive adj . obviously)
--(unique_edges : edge set not multiset?)
namespace simple_graph

-- notation for adj
-- class has_splodge (α : Sort*) := { bigcirc : α → α → Prop }
-- instance (α : Type u) [simple_graph α] : has_splodge α := 
-- { bigcirc := @simple_graph.adj α _inst_1 }

-- why can't I use exotic unicode in infix notation?
-- binding power and associativity sent to default values
--infix `◯`:37 := has_splodge.bigcirc
notation v ` ◯⦃`:37 G `⦄ `:37 w := G.adj v w

def adj_ne {X : Type u} (G : simple_graph X) (v w : X)
  (h : v ◯⦃G⦄ w) : v ≠ w :=
begin
  rintro rfl,
  apply G.loopless v h,
end


/--
The complete graph on a type `V` is the simple graph with all pairs of distinct vertices adjacent.
-/
variables {V} (G : simple_graph V)

def complete_graph : simple_graph V :=
{ adj := ne }

def empty : simple_graph V := 
{ adj := λ _ _, false}


-- @[simp] lemma empty_adj (v u : V) : (@empty V).adj v u ↔ false := by tidy

instance : inhabited (simple_graph V) := ⟨@complete_graph V⟩

instance complete_graph_adj_decidable (V : Type u) [decidable_eq V] :
  decidable_rel (@complete_graph V).adj :=
by { dsimp [complete_graph], apply_instance }

-- variables {V} (G : simple_graph V)

/-- `G.neighbor_set v` is the set of vertices adjacent to `v` in `G`. -/
def neighbor_set (v : V) : set V := set_of (G.adj v)

lemma ne_of_edge {a b : V} (hab : G.adj a b) : a ≠ b :=
by { rintro rfl, exact G.loopless a hab }

/--
The edges of G consist of the unordered pairs of vertices related by
`G.adj`.  It is given as a subtype of the symmetric square.
-/
def E : Type u := {x : sym2 V // x ∈ sym2.from_rel G.sym}

@[ext] theorem E.ext {a b : E G} : a.1 = b.1 → a = b :=
by { cases a, cases b, simp }

@[ext] theorem E.ext_iff (a b : E G) : a = b ↔ a.1 = b.1 :=
⟨λ h, by cases h; refl, E.ext G⟩

/-- Allows us to refer to a vertex being a member of an edge. -/
instance has_mem : has_mem V G.E := { mem := λ v e, v ∈ e.val }

/-- Construct an edge from its endpoints. -/
def edge_of_adj {v w : V} (h : G.adj v w) : G.E := ⟨⟦(v,w)⟧, h⟩

lemma edge_eq_edge_of_adj (e : G.E): 
  ∃ v w, ∃ (h : v ◯⦃G⦄ w), e = G.edge_of_adj h := 
begin
    cases e,
    rcases e_val,
    cases e_val with v w,
    use [v, w, e_property],
    refl
end

lemma edge_eq_edge_of_adj_iff (e : G.E) {v w} (h : G.adj v w) : 
  e = G.edge_of_adj h ↔ v ∈ e ∧ w ∈ e := 
begin
  cases e with e he,
  rcases e with ⟨v', w'⟩,
  change v' ◯⦃G⦄ w' at he,
  split,
  { intro H,
    cases G with adj symm loopless,
    dsimp at symm loopless h he,
    unfold edge_of_adj at H,
    rw H,
    unfold has_mem.mem sym2.mem,
    simp,
    split,
    use w, use v,
    apply quotient.exact, 
    -- how the fuck 
    exact sym2.eq_swap },
  { rintro ⟨hv,hw⟩,
    cases hv with v hv,
    cases hw with w hw,
    ext,
    apply sym2.eq_iff.2,
    cases sym2.eq_iff.1 hv;
    cases sym2.eq_iff.1 hw; try {cc},
    replace h := adj_ne _ _ _ h,
    cc,
    clear hv hw,
    replace he := adj_ne _ _ _ he,
    rcases h_1 with ⟨rfl, rfl⟩,
    rcases h_2 with ⟨rfl, rfl⟩,
    replace h := adj_ne _ _ _ h,
    cases h rfl }
end

#check sym2

@[simp]
lemma mem_of_adj {v w : V} (h : G.adj v w) :
  v ∈ G.edge_of_adj h := sym2.mk_has_mem v w

@[simp] 
lemma mem_of_adj_right {v w : V} (h : G.adj v w) :
  w ∈ G.edge_of_adj h := sym2.mk_has_mem_right v w

lemma adj_iff_exists_edge {v w : V} (hne : v ≠ w) :
G.adj v w ↔ ∃ (e : G.E), v ∈ e ∧ w ∈ e :=
begin
  split, { intro, use ⟦(v,w)⟧, assumption, refine ⟨(G.mem_of_adj _), (G.mem_of_adj_right _)⟩ },
  rintro ⟨e, ⟨w', hve⟩, ⟨v', hew⟩⟩,
  have : e.val = ⟦(v,w)⟧, { rw [hve, sym2.eq_iff] at hew ⊢, cc },
  have key := e.property, rwa this at key,
end

lemma empty_edge (e : (@empty V).E) : false := by tidy

lemma edge_eq_iff (e d : G.E) : e = d ↔ ∃ u, ∃ v ≠ u, u ∈ e ∧ u ∈ d ∧ v ∈ e ∧ v ∈ d :=
begin
 split, 
 { rintro rfl, rcases G.edge_eq_edge_of_adj e with ⟨u, v, h, rfl⟩, 
  use [u, v], have := G.ne_of_edge h, simp; cc,
 },
 rintro ⟨u, v, h, _⟩,
 have : G.adj v u, rw G.adj_iff_exists_edge h, use e, tauto,
 transitivity G.edge_of_adj this,
 { rw edge_eq_edge_of_adj_iff, tauto },
 { symmetry, rw edge_eq_edge_of_adj_iff, tauto },
end

@[ext]
lemma edge_eq_iff' (e d : G.E) : e = d ↔ ∀ u, u ∈ e ↔ u ∈ d :=
begin
  split, { rintro rfl, simp },
  intro h, rw edge_eq_iff,
  rcases G.edge_eq_edge_of_adj e with ⟨u, v, h_adj, rfl⟩,
  use [u, v],
  have := G.ne_of_edge h_adj, simp only [← h], simp; tauto,
end

variables {G}

/-- Given an edge and one vertex incident on it, construct the other one. -/
noncomputable def E.other (e : G.E) {v : V} (h : v ∈ e) : V :=
by { have : v ∈ e.val, apply h, exact this.other }

lemma E.other_mem (e : G.E) {v : V} (h : v ∈ e) : e.other h ∈ e :=
begin
  change sym2.mem.other h ∈ e.val, have := sym2.mem_other_spec h,
  convert sym2.mk_has_mem_right _ _; tauto,
end

lemma E.other_ne (e : G.E) {v : V} (h : v ∈ e) : e.other h ≠ v :=
begin
  have key := e.property,
  erw [← sym2.mem_other_spec h, sym2.eq_swap] at key,
  exact G.ne_of_edge key,
end

lemma E.mem_iff (e : G.E) {v : V} (h : v ∈ e) (u : V) :
  u ∈ e ↔ u = v ∨ u = e.other h :=
begin
  convert sym2.mem_iff using 1, 
  erw sym2.mem_other_spec h, refl,
end

lemma E.eq_other_iff (e : G.E) {v : V} (h : v ∈ e) (u : V) : 
 u = e.other h ↔ u ≠ v ∧ u ∈ e :=
begin
  split, { rintro rfl, refine ⟨ E.other_ne _ _, E.other_mem _ _⟩ },
  rintro ⟨huv, hu⟩,
  rw e.mem_iff h at hu, tauto,
end
attribute [irreducible] E.other

instance E.inhabited [inhabited {p : V × V | G.adj p.1 p.2}] : inhabited G.E :=
⟨begin
  rcases inhabited.default {p : V × V | G.adj p.1 p.2} with ⟨⟨x, y⟩, h⟩,
  use ⟦(x, y)⟧, rwa sym2.from_rel_prop,
end⟩
#check sym2

instance edges_fintype [decidable_eq V] [fintype V] [decidable_rel G.adj] :
  fintype G.E := subtype.fintype _

section classical
open_locale classical
noncomputable theory 

def E.some (e : G.E) : V := 
begin
  suffices : ∃ v, v ∈ e,
  exact classical.some this,
  sorry
end

lemma E.some_spec (e : G.E) : e.some ∈ e := 
begin
  dsimp [E.some], 
  -- refine classical.some_spec _,
  sorry,
end

variables [fintype V]

def E_finset  (G : simple_graph V) : finset $ V × V :=
finset.filter (λ x, G.adj x.1 x.2) univ

lemma E_finset_spec [decidable_eq V] [fintype V] [decidable_rel G.adj] : 
2 * fintype.card G.E = finset.card G.E_finset := 
begin
  -- transitivity 2 * finset.card _, ring,
  have : fintype.card (fin 2) = 2, { tidy },
  rw [← this, ← fintype.card_prod], 
  rw ← fintype.card_of_finset, swap, { intro, refl },
  convert fintype.of_equiv_card _, 
  symmetry, refine equiv.of_bijective _ _,
  rintro ⟨b, e⟩, 
  refine if b = 0 
    then ⟨(e.some, e.other e.some_spec), _⟩ 
    else ⟨(e.other e.some_spec, e.some), _⟩,
  { suffices : G.adj e.some (e.other e.some_spec), simpa [E_finset],
    rw adj_iff_exists_edge, refine ⟨ e, e.some_spec, _⟩, apply e.other_mem, 
    symmetry, apply e.other_ne },
  { suffices : G.adj (e.other e.some_spec) _, simpa [E_finset],
    rw adj_iff_exists_edge, { refine ⟨ e, _, e.some_spec⟩, apply e.other_mem },
    simp [e.other_ne] },
  sorry,
  -- refine ⟨_, _⟩, 
  -- intros x y h,
  -- by_cases hxy : x.1 = y.1,
  -- ext, any_goals { simp [hxy] }, 
  -- dsimp at h, by_cases hy : y.1 = 0, 
end
variables (G)
#check prod.eq_iff_fst_eq_snd_eq
def card_edges : ℕ := fintype.card G.E

@[simp] lemma empty_card_edges : (@empty V).card_edges = 0 :=
by { dsimp [card_edges], rw fintype.card_eq_zero_iff, tidy }

@[simp] lemma card_edges_eq_zero_iff : 
  G.card_edges = 0 ↔ G = empty :=
begin
  split, swap, { rintro rfl, simp },
  intro h, dsimp [card_edges] at h, 
  ext, simp only [empty, iff_false], contrapose! h,
  rw [← nat.pos_iff_ne_zero, fintype.card_pos_iff],
  apply nonempty.intro, exact G.edge_of_adj h,
end

lemma empty_iff_not_edge : G = empty ↔ G.E → false :=
begin
  split, { rintro rfl, apply empty_edge },
  intro h, ext u v, suffices : ¬ G.adj u v, { tidy },
  intro he, have e := G.edge_of_adj he, exact h e,
end

def inhabited_of_ne_empty (h : G ≠ empty) : inhabited G.E :=
begin
  suffices : nonempty G.E, { letI := this, inhabit G.E, assumption },
  refine fintype.card_pos_iff.mp _, contrapose! h, 
  erw [le_zero_iff_eq, card_edges_eq_zero_iff] at h, exact h,
end
end classical

attribute [irreducible] E

@[simp] lemma irrefl {v : V} : ¬G.adj v v := G.loopless v

@[symm] lemma edge_symm (u v : V) : G.adj u v ↔ G.adj v u :=
by split; apply G.sym

@[simp] lemma mem_neighbor_set (v w : V) : w ∈ G.neighbor_set v ↔ G.adj v w :=
by tauto

section finite_at

/-!
## Finiteness at a vertex
This section contains definitions and lemmas concerning vertices that
have finitely many adjacent vertices.  We denote this condition by
`fintype (G.neighbor_set v)`.
We define `G.neighbor_finset v` to be the `finset` version of `G.neighbor_set v`.
Use `neighbor_finset_eq_filter` to rewrite this definition as a `filter`.
-/

variables (v : V) [fintype (G.neighbor_set v)]
variables (G)
/--
`G.neighbors v` is the `finset` version of `G.adj v` in case `G` is
locally finite at `v`.
-/
def neighbor_finset : finset V := (G.neighbor_set v).to_finset

@[simp] lemma mem_neighbor_finset (w : V) :
  w ∈ G.neighbor_finset v ↔ G.adj v w :=
by simp [neighbor_finset]

/--
`G.degree v` is the number of vertices adjacent to `v`.
-/
def degree : ℕ := (G.neighbor_finset v).card

@[simp]
lemma card_neighbor_set_eq_degree : fintype.card (G.neighbor_set v) = G.degree v :=
by simp [degree, neighbor_finset]

end finite_at

section locally_finite

variables (G) [∀ (v : V), fintype (G.neighbor_set v)]
/--
A regular graph is a locally finite graph such that every vertex has the same degree.
-/
def regular_graph (d : ℕ) : Prop := ∀ (v : V), G.degree v = d

end locally_finite

section finite

variables [fintype V]

instance neighbor_set_fintype [decidable_rel G.adj] (v : V) : fintype (G.neighbor_set v) :=
  @subtype.fintype _ _ (by {simp_rw mem_neighbor_set, apply_instance}) _

lemma neighbor_finset_eq_filter {v : V} [decidable_rel G.adj] :
  G.neighbor_finset v = finset.univ.filter (G.adj v) :=
by { ext, simp }

@[simp]
lemma complete_graph_degree [decidable_eq V] (v : V) :
  (@complete_graph V).degree v = fintype.card V - 1 :=
begin
  convert univ.card.pred_eq_sub_one,
  erw [degree, neighbor_finset_eq_filter, filter_ne, card_erase_of_mem (mem_univ v)],
end

lemma complete_graph_is_regular [decidable_eq V] :
  (@complete_graph V).regular_graph (fintype.card V - 1) :=
by { intro v, simp }

end finite

end simple_graph
