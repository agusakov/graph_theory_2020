import tactic
import sym2

universe u
variables (V : Type u)

structure simple_graph :=
(adj : V → V → Prop)
(sym : symmetric adj . obviously)
(loopless : irreflexive adj . obviously)

namespace simple_graph

def induced_subgraph (G : simple_graph V) (S : set V) : simple_graph S :=
{adj := λ a b, G.adj a b,
sym := λ a b h, G.sym h, 
loopless := λ x h, G.loopless x h}

variables {V} (T : simple_graph V)

def E : Type u := {x : sym2 V // x ∈ sym2.from_rel T.sym}

instance has_mem : has_mem V T.E := { mem := λ v e, v ∈ e.val }

structure path :=
(head : V)
(tail : list V)
(edges : list T.E)
(length_eq : edges.length = tail.length)
(adj : ∀ (n : ℕ) (hn : n < edges.length), 
  let u := (list.cons head tail).nth_le n (by { simp; omega }) in
  let v := (list.cons head tail).nth_le (n + 1) (by { simp, cc }) in
  u ≠ v ∧ u ∈ edges.nth_le n hn ∧ v ∈ edges.nth_le n hn)

namespace path
variables {T} 
variables (p : T.path)

def vertices : list V := p.head :: p.tail 

def is_tour : Prop := list.nodup p.vertices

section classical
open_locale classical
noncomputable def last : V := if h : p.tail = list.nil then p.head else p.tail.last h

end classical
end path

def acyclic : Prop := ∀ (p : T.path), p.head ≠ p.last ∧ p.is_tour

lemma acyclic_subgraph_acyclic (t : acyclic T) (s : set V) : acyclic (induced_subgraph V T s) :=
begin
    -- Proof outline:
    -- T has no cycles so T \ {x} has no cycles
    sorry,
end

end simple_graph