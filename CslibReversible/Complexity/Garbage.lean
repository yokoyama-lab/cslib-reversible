/-
Copyright (c) 2026 Tetsuo Yokoyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuo Yokoyama
-/
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Nat.Log
import Mathlib.Data.Countable.Basic

/-!
# Garbage as a resource

A reversible machine cannot compute a non-injective function without keeping
something extra.  To turn `f : X → Y` into an injection one emits, alongside
the answer, a second value — the **garbage** — whose only job is to tell apart
inputs that `f` conflates.

This file makes "how much garbage does `f` need?" a definite question with a
definite answer.

## Main definitions

- `Realization f G`: a garbage map `X → G` making `x ↦ (f x, garbage x)`
  injective.  This is what it means to compute `f` reversibly with garbage
  drawn from `G`.
- `fiber f y`: the inputs `f` sends to `y`.
- `fiberWidth f`: the size of the largest fiber.
- `garbageBits f`: `⌈log₂⌉` of the fiber width — the answer in bits.

## Main statements

- `fiberWidth_le_card`: **every** realization needs `|G| ≥ fiberWidth f`.
  This is the direction that bounds physical cost from below.  Nothing is
  assumed about how the realization was obtained: the garbage map it carries
  is itself the injection that does the counting.
- `realization_fin_fiberWidth`: a realization on exactly `fiberWidth f`
  garbage values exists.  The construction ranks each input inside its own
  fiber, so the garbage values it uses are `0, 1, …, k-1` — an initial
  segment.  This is the mechanized form of the *g-minimality* construction of
  Glück and Yokoyama.
- `isLeast_garbageCard`: putting the two together, `fiberWidth f` **is** the
  minimum number of garbage values, not merely a bound.
- `garbageBits_eq_zero_iff`: `f` can be computed garbage-free exactly when it
  is injective.

## The asymmetry, and why it is deliberate

`fiberWidth_le_card` is a *lower* bound on garbage, and lower bounds are what
survive being restricted to a subset of the inputs: if a machine is only ever
run on inputs from `S`, whatever `S`-fibers force is still forced.  The
matching *upper* bound is not stable in that way — a realization that is
minimal for `S` may be far from minimal for all of `X`, because its garbage
may be distinguishing inputs that lie outside `S`.

Downstream users of this file (energy and qubit counts) should therefore quote
`fiberWidth_le_card` when they want to say "at least this much is needed", and
must not turn a measured surplus into a claim of provable waste.

## Axioms

Unlike the transition-system layer, this file is *not* choice-free, and it
cannot be made so while it counts with `Finset`: measured on 2026-08-08, every
cardinality lemma it rests on — `Finset.card_le_card_of_injOn`,
`Finset.sup_le`, `Finset.le_sup`, `Finset.card_le_univ`, `Finset.card_le_one`,
`Finset.card_lt_card` — already depends on `Classical.choice` and `Quot.sound`
in Mathlib itself.  `Quot.sound` is unavoidable in any case, `Finset` being a
quotient of `List`.  The audit in `CslibReversible.Audit` pins the resulting
axiom set so that it cannot grow unnoticed.

## References

* R. Glück, T. Yokoyama.  *Making Programs Reversible with Minimal Extra
  Data.*  Reversible Computation, 2019.
* C. H. Bennett.  *Logical reversibility of computation.*  IBM Journal of
  Research and Development 17(6), 525–532, 1973.
-/

universe u v w

namespace Cslib.Reversible

variable {X : Type u} {Y : Type v} {G : Type w}

/--
A **reversible realization** of `f` with garbage in `G`.

`garbage` is the extra output; the condition says that the answer together
with the garbage determines the input, which is exactly what a reversible
machine must guarantee.
-/
structure Realization (f : X → Y) (G : Type w) where
  /-- The extra output. -/
  garbage : X → G
  /-- Answer and garbage together determine the input. -/
  injective : Function.Injective fun x => (f x, garbage x)

namespace Realization

variable {f : X → Y}

/--
Within one fiber the garbage separates inputs.  This is the whole content of
a realization, stated in the form the counting arguments use.
-/
theorem eq_of_fiber (R : Realization f G) {x x' : X}
    (hf : f x = f x') (hg : R.garbage x = R.garbage x') : x = x' :=
  R.injective (by simp only [Prod.mk.injEq]; exact ⟨hf, hg⟩)

/-- The garbage map is injective on each fiber. -/
theorem injOn_fiber (R : Realization f G) (y : Y) :
    Set.InjOn R.garbage {x | f x = y} := by
  intro x hx x' hx' h
  exact R.eq_of_fiber (by simp only [Set.mem_ofPred_eq] at hx hx'; rw [hx, hx']) h

/-- Transport a realization along an injection of the garbage type. -/
def map {G' : Type*} (R : Realization f G) (e : G → G') (he : Function.Injective e) :
    Realization f G' where
  garbage x := e (R.garbage x)
  injective := by
    intro x x' h
    simp only [Prod.mk.injEq] at h
    exact R.eq_of_fiber h.1 (he h.2)

/-- An injective function needs no garbage. -/
def ofInjective (hf : Function.Injective f) : Realization f PUnit where
  garbage _ := ⟨⟩
  injective := by
    intro x x' h
    simp only [Prod.mk.injEq] at h
    exact hf h.1

end Realization

section Finite

variable [Fintype X] [DecidableEq Y]

/-- The fiber of `f` over `y`: the inputs that `f` maps to `y`. -/
def fiber (f : X → Y) (y : Y) : Finset X := Finset.univ.filter fun x => f x = y

@[simp] theorem mem_fiber {f : X → Y} {y : Y} {x : X} : x ∈ fiber f y ↔ f x = y := by
  simp [fiber]

theorem self_mem_fiber (f : X → Y) (x : X) : x ∈ fiber f (f x) := by simp

/--
The **fiber width** of `f`: how many inputs the worst-case output conflates.

This is the quantity the rest of the file identifies with the garbage
requirement.
-/
def fiberWidth (f : X → Y) : ℕ := (Finset.univ.image f).sup fun y => (fiber f y).card

theorem card_fiber_le_fiberWidth (f : X → Y) (y : Y) : (fiber f y).card ≤ fiberWidth f := by
  by_cases h : (fiber f y).Nonempty
  · obtain ⟨x, hx⟩ := h
    have : y ∈ Finset.univ.image f := by
      rw [Finset.mem_image]
      exact ⟨x, Finset.mem_univ x, by simpa using hx⟩
    exact Finset.le_sup (f := fun y => (fiber f y).card) this
  · rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h, Finset.card_empty]
    exact Nat.zero_le _

/-- The fiber width is at most the number of inputs. -/
theorem fiberWidth_le_card_univ (f : X → Y) : fiberWidth f ≤ Fintype.card X := by
  refine Finset.sup_le fun y _ => ?_
  exact Finset.card_le_univ _

/-!
### The lower bound

Nothing about how a realization was produced is used here, and no choice is
made: the garbage map that comes with the realization is itself the injection
that does the counting.
-/

/--
**The garbage register really does take at least `fiberWidth f` distinct
values.**

This is sharper than a bound on the size of `G`, and it is the form the
physical reading needs: what a machine must later erase is the values its
garbage register actually visits, not the values its type could in principle
hold.
-/
theorem fiberWidth_le_card_image {f : X → Y} [DecidableEq G] (R : Realization f G) :
    fiberWidth f ≤ (Finset.univ.image R.garbage).card := by
  refine Finset.sup_le fun y _ => ?_
  refine Finset.card_le_card_of_injOn R.garbage
    (fun a _ => Finset.mem_image_of_mem _ (Finset.mem_univ a)) ?_
  intro x hx x' hx' h
  rw [Finset.mem_coe, mem_fiber] at hx hx'
  exact R.eq_of_fiber (by rw [hx, hx']) h

/--
**Every realization needs at least `fiberWidth f` garbage values.**

The bound is on the *type* `G`, so it holds however the realization was built
and however wastefully it uses `G`.
-/
theorem fiberWidth_le_card {f : X → Y} [Fintype G] (R : Realization f G) :
    fiberWidth f ≤ Fintype.card G := by
  classical
  exact le_trans (fiberWidth_le_card_image R) (Finset.card_le_univ _)

/-!
### The construction

The garbage attached to `x` is the number of elements of `x`'s own fiber that
precede it in a fixed enumeration of the inputs.  Two consequences fall out at
once: the value is below the size of that fiber, so the garbage used is an
initial segment `{0, …, k-1}` rather than an arbitrary set of that size; and
distinct elements of a fiber get distinct values, which is what makes the map
a realization.

The first of these is *g-minimality* in the sense of Glück and Yokoyama: the
garbage set is downward closed in the enumeration order.
-/

variable (ι : X ↪ ℕ)

/-- The position of `x` among the elements of its own fiber, in `ι`-order. -/
def rank (f : X → Y) (x : X) : ℕ :=
  ((fiber f (f x)).filter fun x' => ι x' < ι x).card

variable {ι}

theorem rank_lt_card_fiber (f : X → Y) (x : X) :
    rank ι f x < (fiber f (f x)).card := by
  refine Finset.card_lt_card ⟨Finset.filter_subset _ _, fun hsub => ?_⟩
  have hx : x ∈ (fiber f (f x)).filter fun x' => ι x' < ι x := hsub (self_mem_fiber f x)
  simp at hx

theorem rank_lt_fiberWidth (f : X → Y) (x : X) : rank ι f x < fiberWidth f :=
  lt_of_lt_of_le (rank_lt_card_fiber f x) (card_fiber_le_fiberWidth f (f x))

/-- Inside a fiber, `rank` is strictly monotone in the enumeration order. -/
theorem rank_lt_rank {f : X → Y} {x x' : X} (hfib : f x = f x') (hlt : ι x < ι x') :
    rank ι f x < rank ι f x' := by
  refine Finset.card_lt_card ⟨fun a ha => ?_, fun hsub => ?_⟩
  · simp only [Finset.mem_filter, mem_fiber] at ha ⊢
    exact ⟨by rw [ha.1, hfib], lt_trans ha.2 hlt⟩
  · have hx : x ∈ (fiber f (f x)).filter fun a => ι a < ι x :=
      hsub (by simp only [Finset.mem_filter, mem_fiber]; exact ⟨hfib, hlt⟩)
    simp at hx

/-- `rank` separates the elements of a fiber. -/
theorem rank_injOn {f : X → Y} {x x' : X} (hfib : f x = f x')
    (h : rank ι f x = rank ι f x') : x = x' := by
  rcases lt_trichotomy (ι x) (ι x') with hlt | heq | hgt
  · exact absurd h (Nat.ne_of_lt (rank_lt_rank hfib hlt))
  · exact ι.injective heq
  · exact absurd h.symm (Nat.ne_of_lt (rank_lt_rank hfib.symm hgt))

/--
The realization built from an enumeration: garbage is the rank inside the
fiber, and it lands in `Fin (fiberWidth f)`.
-/
def realizationOfEmbedding (ι : X ↪ ℕ) (f : X → Y) : Realization f (Fin (fiberWidth f)) where
  garbage x := ⟨rank ι f x, rank_lt_fiberWidth f x⟩
  injective := by
    intro x x' h
    simp only [Prod.mk.injEq, Fin.mk.injEq] at h
    exact rank_injOn h.1 h.2

/--
**A realization on exactly `fiberWidth f` garbage values exists.**

Together with `fiberWidth_le_card` this pins the garbage requirement exactly.
-/
theorem realization_fin_fiberWidth (f : X → Y) :
    Nonempty (Realization f (Fin (fiberWidth f))) := by
  obtain ⟨ι⟩ := nonempty_embedding_nat X
  exact ⟨realizationOfEmbedding ι f⟩

/-- Any garbage type at least as large as the fiber width supports a realization. -/
theorem exists_realization_of_card_le {f : X → Y} [Fintype G]
    (h : fiberWidth f ≤ Fintype.card G) : Nonempty (Realization f G) := by
  obtain ⟨R⟩ := realization_fin_fiberWidth f
  obtain ⟨e⟩ : Nonempty (Fin (fiberWidth f) ↪ G) := by
    rw [Function.Embedding.nonempty_iff_card_le]
    simpa using h
  exact ⟨R.map e e.injective⟩

/-!
### Garbage complexity
-/

/--
**The fiber width is the least number of garbage values that suffices.**

Both halves are needed for this to be a definition of a resource rather than
an estimate: the lower bound says no realization can do better, the upper
bound says one achieves it.
-/
theorem isLeast_garbageCard (f : X → Y) :
    IsLeast {n : ℕ | ∃ G : Type, ∃ _ : Fintype G, Fintype.card G = n ∧
      Nonempty (Realization f G)} (fiberWidth f) := by
  constructor
  · exact ⟨Fin (fiberWidth f), inferInstance, Fintype.card_fin _, realization_fin_fiberWidth f⟩
  · rintro n ⟨G, hG, rfl, ⟨R⟩⟩
    exact fiberWidth_le_card R

/-- The **garbage complexity** of `f`, in bits. -/
def garbageBits (f : X → Y) : ℕ := Nat.clog 2 (fiberWidth f)

/-- A realization needs at least `garbageBits f` bits of garbage. -/
theorem garbageBits_le_log_card {f : X → Y} [Fintype G] (R : Realization f G) :
    garbageBits f ≤ Nat.clog 2 (Fintype.card G) :=
  Nat.clog_mono_right 2 (fiberWidth_le_card R)

theorem fiberWidth_le_one_iff_injective {f : X → Y} :
    fiberWidth f ≤ 1 ↔ Function.Injective f := by
  constructor
  · intro h x x' hxx
    have hcard : (fiber f (f x)).card ≤ 1 := le_trans (card_fiber_le_fiberWidth f (f x)) h
    exact Finset.card_le_one.mp hcard x (self_mem_fiber f x) x' (mem_fiber.mpr hxx.symm)
  · intro hf
    refine Finset.sup_le fun y _ => ?_
    refine Finset.card_le_one.mpr fun a ha b hb => ?_
    simp only [mem_fiber] at ha hb
    exact hf (by rw [ha, hb])

/--
**Garbage-free exactly when injective.**  The definition passes the sanity
check it has to pass.
-/
theorem garbageBits_eq_zero_iff {f : X → Y} : garbageBits f = 0 ↔ Function.Injective f := by
  rw [garbageBits, ← fiberWidth_le_one_iff_injective]
  refine ⟨fun h => ?_, fun h => Nat.clog_of_right_le_one h 2⟩
  rcases Nat.lt_or_ge 1 (fiberWidth f) with hgt | hle
  · have hpos : 0 < Nat.clog 2 (fiberWidth f) := Nat.clog_pos (b := 2) Nat.one_lt_two hgt
    omega
  · exact hle

end Finite

end Cslib.Reversible
