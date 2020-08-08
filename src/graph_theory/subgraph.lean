/-
Copyright (c) 2020 Alena Gusakov, Jalex Stark. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Alena Gusakov, Jalex Stark.
-/

import .basic

noncomputable theory
open_locale classical

universes u
variables {V : Type u}  
namespace simple_graph

-- define map from graph to subgraph, use `is_subgraph` property from graph_induction.lean

def is_subgraph (H : simple_graph V) (G : simple_graph V) : Prop := 
∀ u v, H.adj u v → G.adj u v


variables (G : simple_graph V) 
include G

@[refl] lemma is_subgraph_self : G.is_subgraph G := by tidy

lemma empty_is_subgraph : empty.is_subgraph G := by tidy

def subgraph := {H : simple_graph V // H.is_subgraph G}

namespace subgraph

-- CR-soon jstark: bundle these together
variables {G} (H : simple_graph V) (hG : H.is_subgraph G)
include hG

def edge_inclusion : H.E → G.E := 
begin
  intro e, 
  set u := e.some, 
  have hu := e.some_spec,
  set v := e.other hu,
  have hv := e.other_mem hu,
  suffices : G.adj u v, { apply G.edge_of_adj this },
  apply hG, apply e.other_adj,
end

-- properties of `inclusion`: it's an injective homomorphism

end subgraph

def induced_subgraph (G : simple_graph V) (S : set V) : simple_graph S :=
{
  adj := λ a b, G.adj a b,
  sym := λ a b h, G.sym h, 
  loopless := λ x h, G.loopless x h
}

variables (s : set V) (S : simple_graph s)

-- two ideas: 
    -- `induced_subgraph.to_supergraph`
    -- `simple_graph.to_induced_subgraph`

/-def induced_subgraph.to_supergraph {S : simple_graph s} {G : simple_graph V} : S.E → G.E
    | -/

def path_inclusion.to_supergraph {V : Type u} : T.path → S.path
    | []     := ∅
    | (h::t) := {h} ∪ list.to_set t


end simple_graph

