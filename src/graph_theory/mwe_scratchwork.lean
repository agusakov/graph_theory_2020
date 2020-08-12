import .basic
import .path

universes u
variables {V : Type u}

namespace simple_graph
variables (G : simple_graph V) 


namespace path
variables {G} 
variables (p : G.path)

/- length of path.is_tour is less than the cardinality of V -/
lemma tour_lt_card [fintype V] : ∀ (p : path G) (hp : p.is_tour), p.length < fintype.card V :=
begin
  intros,
  unfold is_tour at hp,
  have h := p.vertices,
  -- p contains vertices of V
  -- vertices in p don't repeat
  -- there are `V.card` vertices
  sorry,
end

instance : has_Sup {n : ℕ | ∃ (p : G.path), p.is_tour ∧ p.length = n} :=
begin
  
  sorry,
end

/- there exists a path, path.is_tour, s.t. path.is_maximal -/
-- CR : can be generalized to infinite graphs
lemma fin_max_tour [fintype V] [nonempty V]: ∃ (p : path G), p.is_maximum :=
begin
  have s := {n : ℕ | ∃ (p : G.path), p.is_tour ∧ p.length = n},
  --have h2 : ∀ n ∈ s, n ≤ fintype.card V := 
  sorry,
end

end path

end simple_graph
#lint
-- CR : there are unused arguments, they are there because I will need to use them once I figure out the proofs lol