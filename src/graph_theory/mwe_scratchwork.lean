import .basic
import .path

universes u
variables {V : Type u}

namespace simple_graph
variables (G : simple_graph V)

namespace path
variables {G}
variables (p : G.path)

section classical
open_locale classical

#check nat.find
/- there exists a path, path.is_tour, s.t. path.is_maximum_length -/
-- CR : can be generalized to infinite graphs (i think??)
lemma fin_max_tour [fintype V] [decidable_eq V] [nonempty V]: ∃ (p : path G), p.is_maximum_length :=
begin
  let s := {n : ℕ | ∃ (p : G.path), p.is_tour ∧ p.length = n},
  have h2 : ∀ n ∈ s, n ≤ fintype.card V,
  { intros n hn,
    apply le_of_lt,
    rw set.mem_set_of_eq at hn,
    rcases hn with ⟨p, ht, rfl⟩, -- i keep forgetting rcases
    exact tour_lt_card p ht },
  have h : ∃ m (q : path G), q.is_tour ∧ q.length = m ∧ ∀ (p : path G), p.is_tour → p.length ≤ m,
  {
    let su := upper_bounds s,
    have : bdd_above s,
    {
      unfold bdd_above,
      rw set.nonempty_def,
      use fintype.card V,
      rw mem_upper_bounds,
      exact h2,
    },
    have h3 : ∃ (b : ℕ), b ∈ s ∧ ∀ x ∈ s, x ≤ b,
    {
      sorry,
    },
    cases h3 with m hm,
    cases hm with hmem hmax,
    rw set.mem_set_of_eq at hmem,
    cases hmem with q hq,
    cases hq with hi hl,
    use m,
    use q,
    split,
    exact hi,
    split,
    exact hl,
    
    sorry,
  },
  --let m := nat.find h,
  rcases h with ⟨m, q, hq, hm, hi⟩,
  use q,
  unfold is_maximum_length,
  rw hm,
  split,
  exact hq,
  exact hi,
end

end classical

end path

end simple_graph
#lint
-- CR : there are unused arguments, they are there because I will need to use them once I figure out the proofs lol. replace `decidable` with `classical`