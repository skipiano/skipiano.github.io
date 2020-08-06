---
# Feel free to add content and custom Front Matter to this file.
# To modify the layout, see https://jekyllrb.com/docs/themes/#overriding-theme-defaults

layout: home


---
Definition of simple graph
```lean
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
```

Definition of path
```lean
/-- Morally, a path is an alternating list of vertices and edges, 
  with incidences between adjacent objects -/
@[ext] structure path :=
(head : V)
(tail : list V)
(edges : list G.E)
(length_eq : edges.length = tail.length)
(adj : ∀ (n : ℕ) (hn : n < edges.length), 
  let u := (list.cons head tail).nth_le n (by { simp; omega }) in
  let v := (list.cons head tail).nth_le (n + 1) (by { simp, cc }) in
  u ≠ v ∧ u ∈ edges.nth_le n hn ∧ v ∈ edges.nth_le n hn)
```

Definition of other path stuff
```lean
/-- p.is_cycle if p starts and ends in the same place. -/
def is_cycle : Prop := p.head = p.last

/-- p.is_trail if p has no repeated edges. -/
def is_trail : Prop := list.nodup p.edges

/-- p.is_Eulerian if p hits each edge exactly once. -/
def is_Eulerian : Prop := p.is_trail ∧ ∀ e : G.E, p.edge_mem e
```

Eulerian path proof

{{ "{% highlight lean"}}%}
<div>
lemma has_eulerian_path_iff : 
  G.has_eulerian_path ↔ card (filter {v : V | ¬ nat.even (G.degree v)} univ) ∈ ({0, 2} : finset ℕ) :=
begin
  split,
  { intro hep, cases hep with p hp,
    simp only [mem_insert, card_eq_zero, mem_singleton],
    by_cases p.is_cycle,
    { left, convert finset.filter_false _,
      { ext, rw [degree_eq_crossed hp, path_crossed], tauto },
      { apply_instance } },
    { right,
      have : finset.card {p.head, p.last} = 2, { rw [card_insert_of_not_mem, card_singleton], rwa mem_singleton },
      convert this, ext,
      suffices : ¬(G.degree a).even ↔ a = p.head ∨ a = p.last, convert this; { simp; refl },
      have deg_cross := degree_eq_crossed hp, rw [deg_cross, path_crossed], simp [h]; tauto,
    }},
    refine G.induction_on _ _ _,
    { intro, apply empty_has_eulerian_path },
    clear G, intros G hG0,
    by_cases (filter {v : V | ¬(G.degree v).even} univ).card = 0,
    { rw h, 
      haveI := G.inhabited_of_ne_empty hG0,  
      have e := arbitrary G.E,
      use G.erase e,
      split, { exact G.erase_is_subgraph e },
      split, { rw ← G.card_edges_erase e, linarith },
      intro x, have eep : (G.erase e).has_eulerian_path, apply x,
      { right, sorry },
      cases eep with p ed, simp, sorry,
    },
    by_cases (filter {v : V | ¬(G.degree v).even} univ).card = 2,
    { sorry },
    use empty, split, exact empty_is_subgraph G,

    -- convert G.induction_on _ _ _, refl,
  
  
  
  -- { rintro ⟨x, y, p, hep⟩,
  --   have deg_cross := G.degree_eq_crossed p hep,
  --   simp at *, 
  --   by_cases x = y,
  --   { left, convert finset.filter_false _,
  --     { ext, simp [deg_cross, path_crossed, h] },
  --     { apply_instance } },
  --   { right,
  --     have : finset.card {x, y} = 2, { rw [card_insert_of_not_mem, card_singleton], rwa mem_singleton },
  --     convert this, ext, 
  --     suffices : ¬(G.degree a).even ↔ a = x ∨ a = y, convert this; { simp; refl },
  --     rw [deg_cross, path_crossed'], simp [h]; tauto,
  --   }},
  -- intro h, simp only [mem_insert, card_eq_zero, mem_singleton] at h, 
  -- I think we need induction on the number of edges?
  split, rw empty_card_edges, have zero_neq : G.card_edges ≠ 0, contrapose! hG0,
  rw ← card_edges_eq_zero_iff, exact hG0, omega,
  intro x, intro y, exfalso, finish,
end
-- iff the number of vertices of odd degree is 0 or 2
</div>
{{ "{% endhighlight "}}%}