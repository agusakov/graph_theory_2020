import simple_graph

noncomputable theory
open_locale classical

universes u
variables {V : Type u}  
namespace simple_graph

def is_subgraph (H : simple_graph V) (G : simple_graph V)  : Prop := 
∀ u v, H.adj u v → G.adj u v


variables (G : simple_graph V) 
include G

@[refl] lemma is_subgraph_self : G.is_subgraph G := by tidy

lemma empty_is_subgraph : empty.is_subgraph G := by tidy

variables [fintype V]

  -- want a lemma that 2 * card_edges equals the card of a specific finset.
-- lemma 2 * G.card_edges = finset.card G.E_finset

@[elab_as_eliminator]
lemma induction_on 
  (P : simple_graph V → Prop)
  (P_empty : P empty)
  (P_inductive : ∀ G ≠ empty, ∃ (H : simple_graph V), 
    H.is_subgraph G ∧ 
    H.card_edges < G.card_edges ∧
    (P H → P G) ) : P G := 
begin
  by_cases h : G = empty, { rwa h },
  suffices : ∀ H : simple_graph V, H.card_edges < G.card_edges → P H, 
  { have := P_inductive G h, tauto },
  induction G.card_edges using nat.strong_induction_on with k hk,
  intros H hHk, 
  by_cases H_card : H = empty, { cc }, 
  rcases P_inductive H H_card with ⟨K, K_sub, K_card, hKH⟩,
  apply hKH, exact hk _ hHk _ K_card,
end
-- for every graph, there exists an edge so that P (G.erase e) → P G

def erase (e : G.E) : simple_graph V := 
{ adj := λ u v, if u ∈ e ∧ v ∈ e then false else G.adj u v,
  sym := by { unfold symmetric, intros, simp_rw [edge_symm, and_comm], cc } }

@[simp] lemma erase_adj_iff (e : G.E) (u v : V) : 
  (G.erase e).adj u v ↔ G.adj u v ∧ (u ∉ e ∨ v ∉ e) :=
by { simp [erase]; tauto, }

lemma erase_is_subgraph (e : G.E) : (G.erase e).is_subgraph G := by tidy
-- writing this down in a way that avoids nat subtraction
lemma card_edges_erase (e : G.E) : (G.erase e).card_edges + 1 = G.card_edges :=
begin
  sorry
end
@[elab_as_eliminator]
lemma induction_on_erase
  (P : simple_graph V → Prop)
  (P_empty : P empty)
  (P_inductive : ∀ G : simple_graph V, G ≠ empty → 
    ∃ e : G.E, P (G.erase e) → P G)
  : P G := 
begin
  apply G.induction_on, assumption,
  intros G₁ hG₁, cases P_inductive G₁ hG₁ with e he,
  use G₁.erase e, 
  split, { apply erase_is_subgraph },
  split, linarith [G₁.card_edges_erase e],
  assumption,
end

end simple_graph