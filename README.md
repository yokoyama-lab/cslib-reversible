# cslib-reversible

An axiom layer for **reversible computation** on top of
[CSLib](https://github.com/leanprover/cslib)'s labelled transition systems,
in Lean 4.

CSLib is the Lean 4 computer science library.  Its
`Cslib.Foundations.Semantics.LTS` provides transition systems together with
bisimulation, simulation, executions, divergence and trace equivalence — but
nothing about reversibility.  This development adds that layer:

* transitions as *data* carrying a direction (`Transition`), so that they can
  be permuted and cancelled;
* paths (`Chained`) and **causal equivalence indexed by its endpoints**
  (`CEq`);
* the axioms of Lanese–Phillips–Ulidowski — the Square Property, Backward
  Transitions are Independent, Well-Foundedness — and the theorems derivable
  from them: the Parabolic Lemma, causal consistency, causal safety and
  causal liveness.

The intended use is that a reversible language or calculus discharges the
axioms **once** and inherits the theory, instead of reproving it.

The layer is not only for people who want reversibility.  `Independence.lean`
derives the *forward* theory — the exchange law, Mazurkiewicz trace
equivalence, and the soundness of partial-order reduction — from the Square
Property, using nothing but the fact that every `LTS` can be read backwards
for free.  Partial-order reduction turns out to be a corollary of
reversibility, not a neighbour of it.

## The theory

| Module | Contents |
|---|---|
| `Defs` | transitions, validity, reversal, the Loop Lemma |
| `Path` | paths, composition, decomposition |
| `CausalEquiv` | endpoint-indexed causal equivalence, endpoint preservation, congruence |
| `Axioms` | IC / SP / BTI / IndepSymm / CLG / WF as classes, `exists_origin` |
| `Diamond` | the backward diamond, uniqueness of origins |
| `Independence` | exchange law, Mazurkiewicz traces, POR soundness, and the bridge from the Square Property |
| `Parabolic` | Danos–Krivine elimination, forward pushing, the **Parabolic Lemma** |
| `RevPath` | path reversal, `CEq.rev` |
| `CausalConsistency` | `normalize_path`, `bwd_cc`, `fwd_cc_from_origin`, **causal consistency** |
| `Events` | `Diamond`, `CPI`, `SameEvent`, `IRE`, Lemma 4.4, **BLD as a theorem** |
| `EventCount` | the signed event count, **Lemma 4.9** |
| `Ladder` | coinitially independent events, Lemma 4.15, the **Ladder Lemma** |
| `CausalSafety` | **causal safety** (Theorem 5.5) |
| `NRE` | forward normal form, Lemma 4.20, **no repeated events** (Prop. 4.21) |
| `CausalLiveness` | `BFCIRE`, the commuting argument, **causal liveness** (Thm. 5.29) |

## The resources

Reversibility has a cost that irreversible computation does not pay, and it
can be pinned down exactly.  To compute a non-injective `f : X → Y` reversibly
you must emit, alongside the answer, something that tells apart the inputs `f`
conflates — the **garbage**.

| Module | Contents |
|---|---|
| `Complexity.Garbage` | `Realization`, `fiberWidth`, `garbageBits`; the lower bound, the matching construction, and `isLeast_garbageCard` — the fiber width **is** the minimum, not an estimate |
| `Complexity.Machine` | `Computes`: what a reversible machine ends up holding is bounded below by the same number, for every machine, using nothing but reversibility |
| `Complexity.Examples` | the definition checked against the standard gates |
| `Complexity.ToffoliMachine` | a machine that meets the bound, so that the bound is about something |

The minimum number of garbage values for `f` is `max_y |f⁻¹(y)|`.  The
construction achieving it ranks each input inside its own fiber, so the garbage
values it uses form an initial segment — this is the *g-minimality* of Glück
and Yokoyama, mechanized.

The check against known gates is in `Complexity.Examples`, and it turns up
something the usual statements do not say.  Conjunction needs 3 garbage values,
so 2 bits; the Toffoli gate keeps both inputs, so 2 bits.  Toffoli is therefore
optimal **in bits** — but it spends 4 values where 3 suffice, so it is not
optimal **in values**, and no bit-addressed register can close that gap.

## The instances

Each instance discharges the axioms and inherits everything above.

| Module | What it is |
|---|---|
| `Instances.History` | the history extension of an arbitrary LTS |
| `Instances.Product` | two components with per-component histories — a family discharging every axiom |
| `Instances.CCSK` | CCS with communication keys (Phillips–Ulidowski) |
| `Instances.RCore` | R-CORE, a minimal reversible imperative language |
| `Instances.Circuit` | reversible circuits: a sequence of gates, each a bijection of the register |
| `Instances.Deterministic` | reversible deterministic systems |
| `Instances.Grounded` | systems whose computations start from an origin |
| `Instances.Restrict` | restricting an instance along a predicate |

## Trust

Nothing here is admitted: the library builds with **no `sorry`**, and
`Audit.lean` pins every headline result's axiom set with `#guard_msgs`, so
the build fails if one changes.

The transition-system layer uses only `propext`.  In particular
`Classical.choice` is not used: the case split in `bstep_diamond` goes through
`DecidableEq`, and `reflTransGen_cases_head` is reproved rather than taken
from Mathlib, which proves it classically.

The complexity layer is **not** choice-free, and cannot be made so while it
counts with `Finset`: every Mathlib cardinality lemma it rests on already
depends on `Classical.choice`.  The audit records exactly where the line
falls — `Computes.final_injective`, which is reversibility doing the work, is
still `propext` alone; choice enters only once configurations start being
counted.

Every axiom in the development is one of LPU's own (`SquareProperty`, `BTI`,
`WellFoundedBwd`, `CPI`, `CLG`, `IRE`, `BFCIRE`, plus irreflexivity and
symmetry of independence, which are part of the definition of an LTSI).
There are no hypotheses of our own invention: backward label determinism,
Proposition 4.17 and reversal-compatibility of events are the *theorems*
`bld_of_sp_bti_cpi`, `lbl_ne_of_cIndep` and `sameEvent_rev`.

## Why the endpoints are in the type

Causal equivalence is usually presented as a relation on *raw lists* of
transitions, with the endpoints supplied separately.  That presentation
cannot prove

```
CEq l₁ l₂ → Chained p l₁ q → Chained p l₂ q
```

because symmetry applied to the cancellation rule gives `CEq [] [t, t.rev]`,
and the empty path is chained from every state to itself.  Indexing on the
endpoints fixes it at the source and, as a side effect, removes seven of the
eleven premises of the swap rule: they are what the two chainedness premises
already say.

## Building

```
lake exe cache get
lake build
```

The Lean toolchain and the Mathlib revision follow CSLib's pin
(`v4.33.0-rc2`).

## References

* I. Lanese, I. Phillips, I. Ulidowski.
  *An Axiomatic Theory for Reversible Computation.*
  ACM Transactions on Computational Logic 25(2), 1–40, 2024.
  [doi:10.1145/3648474](https://doi.org/10.1145/3648474),
  [arXiv:2307.13360](https://arxiv.org/abs/2307.13360)
* I. Lanese, I. Phillips, I. Ulidowski.
  *An Axiomatic Approach to Reversible Computation.*  FoSSaCS 2020,
  LNCS 12077, 442–461.
  [doi:10.1007/978-3-030-45231-5_23](https://doi.org/10.1007/978-3-030-45231-5_23)
* I. Phillips, I. Ulidowski.  *Reversing algebraic process calculi.*
  Journal of Logic and Algebraic Programming 73(1–2), 70–96, 2007.
* F. Montesi et al.  *CSLib: The Lean Computer Science Library.*

## License

Apache 2.0, matching CSLib and Mathlib.  See `LICENSE`.
