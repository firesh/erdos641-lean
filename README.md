# Erdős Problem 641 in Lean 4

A complete, `sorry`-free Lean 4 / Mathlib formalization of the **negative answer** to
[Erdős Problem #641](https://www.erdosproblems.com/641), a question of Erdős and Hajnal
(P. Erdős, *Some of my favourite problems in various branches of combinatorics*, 1992; [Er97d, p. 84]):

> Is there some function `f` such that for all `k ≥ 1`, if a finite graph `G` has chromatic
> number `≥ f(k)`, then `G` has `k` edge-disjoint cycles on the same set of vertices?

**Answer: no.** It already fails for `k = 2`.

## Main theorem

```lean
-- Erdos641/Statement.lean
/-- `G` contains `k` pairwise edge-disjoint cycles which all have the same vertex set. -/
def HasDisjointCyclesSameVertexSet {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ (u : Fin k → V) (c : ∀ i, G.Walk (u i) (u i)),
    (∀ i, (c i).IsCycle) ∧
    (∀ i j, i ≠ j → ∀ e ∈ (c i).edges, e ∉ (c j).edges) ∧
    (∀ i j v, v ∈ (c i).support ↔ v ∈ (c j).support)

def Erdos641Negation : Prop :=
  ¬ ∃ f : ℕ → ℕ, ∀ k, 1 ≤ k → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      (f k : ℕ∞) ≤ G.chromaticNumber → HasDisjointCyclesSameVertexSet G k

-- Erdos641/Main.lean
theorem Erdos641.erdos_641 : Erdos641Negation
```

Cycles are Mathlib walks with `Walk.IsCycle`. The cycles are pairwise edge-disjoint and have the
same support.

The proof also gives the finite statement behind it:

```lean
theorem Erdos641.exists_good_graph (m : ℕ) (hm : 2 ≤ m) :
    ∃ (C : ℕ) (s : Fin C → ℕ) (ω : Omega s),
      ¬ (graph ω).Colorable (m - 1) ∧ ¬ Dense4 (graph ω)
```

For every `m ≥ 2` there is a finite graph that is not `(m - 1)`-colourable and has no nonempty
set `S` carrying `2|S|` edges of maximum degree 4. In particular it has no two edge-disjoint cycles
on the same vertex set.

```
$ lake env lean AxiomCheck.lean
'Erdos641.erdos_641' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The repository contains no `sorry`, `admit`, `native_decide` or added axioms.

## Attribution

* **Mathematics.** The negative answer and the construction are due to **Barnabás Janzer,
  Richard Steiner and Benny Sudakov**: *Chromatic number and regular subgraphs*,
  [arXiv:2410.02437](https://arxiv.org/abs/2410.02437) (2024). They build a random layered graph
  with large chromatic number and no 4-regular subgraph.
* **Formalization.** Written by the owner of this repository (GitHub account `firesh`). The
  probabilistic part of the argument is replaced by exact counting over the finite set of all
  configurations: each bad event is shown to contain at most a quarter of them. Layer sizes and
  constants are explicit. AI assistance was used in developing the formalization.
* **Other formalizations.** An independent formalization of the same result, by Codex /
  GPT-5.6 Sol, is in [plby/lean-proofs](https://github.com/plby/lean-proofs)
  (`src/latest/ErdosProblems/Erdos641.lean`). This repository is a separate development and
  shares no code with it.

## Build

Requires the toolchain in `lean-toolchain` (Lean `v4.34.0-rc1`) and the Mathlib revision
pinned in `lake-manifest.json`.

```sh
lake exe cache get      # optional: download Mathlib build cache
lake build
lake env lean AxiomCheck.lean
```

## Files

| File | Content |
| --- | --- |
| `Erdos641/Statement.lean` | The statement, `Dense4`, and two edge-disjoint cycles on one vertex set → `Dense4` |
| `Erdos641/Layered.lean` | Layers, configurations `ω`, the graph `graph ω` |
| `Erdos641/Sparse.lean` | `Dense4` → a locally dense set below some layer (deterministic part of JSS Lemma 2.1) |
| `Erdos641/Counting.lean` | Exact count of configurations satisfying constraints on some keys |
| `Erdos641/EventA.lean` | Count for the locally dense event; edges inside `X` are keys landing in `X` |
| `Erdos641/EventB.lean` | Count for the event "no edge between `T` and `J`" (JSS Lemma 2.3) |
| `Erdos641/Indep.lean` | A colouring has a heavy colour class, which yields `T` and `J` |
| `Erdos641/Numeric.lean` | `C(N, x) ≤ (3N/x)^x` and a geometric sum |
| `Erdos641/Union.lean` | The two bad events and their union bounds |
| `Erdos641/Bounds.lean` | Each union bound is at most `1/4` of all configurations |
| `Erdos641/Params.lean` | Concrete layer sizes and the inequalities they satisfy |
| `Erdos641/Main.lean` | A configuration avoiding both events; `exists_good_graph`; `erdos_641` |

## Proof outline

Fix `m ≥ 2`. Take `C = 64 m²` layers `L_0, …, L_{C-1}` of sizes
`s_i = 2^(D (12^C − 12^i))` with `D = 9 + 2C`, so each layer is far smaller than the previous one.

1. **Graph.** A configuration `ω` chooses, for every vertex `x ∈ L_i` and every later layer
   `j > i`, one vertex `ω(i, j, x) ∈ L_j`. The graph `graph ω` joins `x` to these choices. Every
   vertex has exactly one neighbour in each later layer.
2. **From cycles to density.** Two edge-disjoint cycles on the same vertex set `S` give `2|S|`
   edges on `S` with every vertex in at most 4 of them (`Dense4`).
3. **Locally dense set.** Cut `S` at the first layer `r` where `1000 s_r < |S|`. Few vertices
   of `S` lie in layers `≥ r`. Each vertex below layer `a = r − 1` has one edge to layer `a`. So
   the part `X` of `S` below layer `a` has `|X| ≤ 1000 s_a` and at least `1.1 |X|` edges inside
   (`Sparse.lean`).
4. **Event A.** Every edge inside `X` is a key `(x, j)` with `x ∈ X`, `j < a` and
   `ω(x, j) ∈ X`. For a fixed set `Q` of keys, the fraction of configurations sending all of
   `Q` into `X` is at most `(|X| / s_{a-1})^|Q|`. Summing over `a`, `X` and `Q` gives at most a
   quarter of all configurations, because `s_{a-1}^11` exceeds `(144 C² s_0)^10 · 3000 C s_a`.
5. **Colourings.** An `(m − 1)`-colouring has a colour class `I` of weight
   `Σ_j |I ∩ L_j| / s_j ≥ C / (m − 1) ≥ 64 m`. Take the first layer `i` where `I` has density at
   least `1/(4m)`. This gives `T = I ∩ L_i` with `|T| ≥ s_i / (4m)`, and `J = I` above `i` with
   later weight at least `24 m`, with no edge between `T` and `J`.
6. **Event B.** For fixed `T`, `J`, the fraction of configurations with no `T`–`J` edge is at most
   `exp(−|T| · 24 m)`. Summing over `i`, `T` and `J` gives at most a quarter of all
   configurations, since everything above layer `i` has at most `s_i / (4m)` vertices.
7. **Conclusion.** Some configuration avoids both events. Its graph is not
   `(m − 1)`-colourable and has no `Dense4`. Given `f`, take `m = max(f 2, 2)`.
