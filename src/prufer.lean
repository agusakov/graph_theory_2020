import tree

-- from math 688 notes, lec-19

universe u
variables (V : Type u) (T : simple_graph V)

-- need some sort of bijection between natural numbers 1, ... , n and v : V
/-def labelled_graph (G : simple_graph V) [fintype V] (n : ℕ) (h : fintype.card V = n) (f : V → ℕ) : finset ℕ := 
{ val := λ v : V, ∃ k : ℕ, (v → k),
  nodup := _ }-/

/-def prufer_code (t : tree T) [fintype V] : set ℕ :=
{

}-/