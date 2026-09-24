/-
Copyright (c) 2026 Tetsuo Yokoyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuo Yokoyama
-/
import CslibReversible.Complexity.GarbageComposition

/-!
# Composing minimal garbage by prefix sums

`Complexity.Garbage` shows that a single function `f` can be computed
reversibly with exactly `fiberWidth f` garbage values, by ranking every input
inside its own fiber.  This file shows that the same bound is reached for a
*composition* `f₂ ∘ f₁` by an encoding that is built **stage by stage**: the
garbage of the second stage is not recomputed from scratch on `f₂ ∘ f₁`, it is
assembled from the fiber ranks of `f₁` and the *fiber cardinalities* of `f₁`
over each fiber of `f₂`.

It repairs the composition rule of Yokoyama, Axelsen and Glück (ICNC 2012),
which carries only the fiber width from stage to stage (see
`Complexity.GarbageComposition`).
Fix enumerations `ι : X ↪ ℕ` and `κ : Y ↪ ℕ`.  For `y : Y` let

* `prefixOff κ f₁ f₂ y := ∑ y' ∈ fiber f₂ (f₂ y), κ y' < κ y, (fiber f₁ y').card`

be the total size of the `f₁`-fibers over the elements of `y`'s own
`f₂`-fiber that precede `y`, and set

* `prefixGarbage ι κ f₁ f₂ x := prefixOff κ f₁ f₂ (f₁ x) + rank ι f₁ x`.

This is the position of `x` in its `f₂ ∘ f₁`-fiber when that fiber is listed
lexicographically: first by `κ (f₁ x)`, then by `ι x`.

## Main statements

- `prefixGarbage_lt_card_fiber`: the garbage value stays below the size of the
  input's own `f₂ ∘ f₁`-fiber.
- `prefixGarbage_eq_of_fiber`: within one `f₂ ∘ f₁`-fiber the garbage separates
  inputs.
- `prefixGarbage_bijOn_fiber`: together, `prefixGarbage` maps every fiber of
  `f₂ ∘ f₁` **bijectively** onto `{0, …, card - 1}`.  This is the statement of
  Proposition 3.
- `prefixRealization`: the resulting
  `Realization (f₂ ∘ f₁) (Fin (fiberWidth (f₂ ∘ f₁)))`.  By `isLeast_garbageCard`
  no realization can use fewer garbage values, so the composed encoding is
  minimal.
- `card_image_prefixGarbage`: the garbage register visits *exactly*
  `fiberWidth (f₂ ∘ f₁)` values — g-minimality, in the sense of
  `Complexity.Garbage`, for the composed map.

## Why this matters for accounting

The ICNC-2012 composition rule carries one scalar per stage, the fiber width,
and combines stages by the product `fiberWidth f₂ * fiberWidth f₁`.  The
present construction carries the *function* `y ↦ (fiber f₁ y).card` instead
and combines stages by the fiber-wise sum of `card_fiber_comp`.  The
product is an upper bound for the sum, and the gap is real: the example at the
end of the file shows `7 < 9` garbage values (three bits against four) for the
three-input conjunction computed as two two-input conjunctions.

## Relation to `GarbageComposition`

The identity that makes the offsets add up is `card_fiber_comp` of
`Complexity.GarbageComposition`: fiber cardinalities push forward along
composition *exactly*,
`(fiber (f₂ ∘ f₁) z).card = ∑ y ∈ fiber f₂ z, (fiber f₁ y).card`.
That file bounds the composite by the product of the widths
(`fiberWidth_comp_le`); this one shows the bound by the sum is attained by a
stage-wise encoding.

## Axioms

As for `Complexity.Garbage`: `Finset` counting rests on `Classical.choice` and
`Quot.sound` inside Mathlib, and nothing here adds to that.  The `decide`
examples at the end use kernel reduction only, not `native_decide`.

## Attribution

Ranking a lexicographically ordered finite set by prefix sums is a standard
combinatorial encoding; nothing about the *theorem* is new.  What this file
contributes is the mechanization and its fit with the resource notions of
`Complexity.Garbage`: the composed garbage is a `Realization` in the library's
sense, and its size is the library's `fiberWidth`.
-/

universe u v w

namespace Cslib.Reversible

variable {X : Type u} {Y : Type v} {Z : Type w}

section Finite

variable [Fintype X] [Fintype Y] [DecidableEq Y] [DecidableEq Z]

/-!
### The prefix-sum offset

`prefixOff κ f₁ f₂ y` counts the inputs of `f₁` that land in `y`'s own
`f₂`-fiber *before* `y` in the enumeration `κ`.  Two facts are needed: moving
to a later element of the same `f₂`-fiber advances the offset by at least the
size of the fiber left behind, and the offset plus the size of `y`'s own
`f₁`-fiber never exceeds the size of the `f₂ ∘ f₁`-fiber.
-/

variable (ι : X ↪ ℕ) (κ : Y ↪ ℕ)

/-- The offset of `y`: total size of the `f₁`-fibers over the elements of
`y`'s own `f₂`-fiber that precede `y` in `κ`-order. -/
def prefixOff (f₁ : X → Y) (f₂ : Y → Z) (y : Y) : ℕ :=
  ∑ y' ∈ (fiber f₂ (f₂ y)).filter (fun y' => κ y' < κ y), (fiber f₁ y').card

/--
The composed garbage: the offset of the intermediate value, plus the rank of
the input inside its own `f₁`-fiber.

This is the position of `x` in the fiber of `f₂ ∘ f₁` over `f₂ (f₁ x)` when
that fiber is ordered lexicographically by `(κ (f₁ x), ι x)`.
-/
def prefixGarbage (f₁ : X → Y) (f₂ : Y → Z) (x : X) : ℕ :=
  prefixOff κ f₁ f₂ (f₁ x) + rank ι f₁ x

variable {ι κ}

/-- Inside one `f₂`-fiber, a later element's offset lies past the whole
block of an earlier one. -/
theorem prefixOff_add_card_le {f₁ : X → Y} {f₂ : Y → Z} {y y' : Y}
    (hfib : f₂ y = f₂ y') (hlt : κ y < κ y') :
    prefixOff κ f₁ f₂ y + (fiber f₁ y).card ≤ prefixOff κ f₁ f₂ y' := by
  have hnot : y ∉ (fiber f₂ (f₂ y)).filter fun a => κ a < κ y := by simp
  have hsub : insert y ((fiber f₂ (f₂ y)).filter fun a => κ a < κ y) ⊆
      (fiber f₂ (f₂ y')).filter fun a => κ a < κ y' := by
    intro a ha
    rw [Finset.mem_insert, Finset.mem_filter, mem_fiber] at ha
    rw [Finset.mem_filter, mem_fiber]
    rcases ha with rfl | ⟨hy, hay⟩
    · exact ⟨hfib, hlt⟩
    · exact ⟨hy.trans hfib, lt_trans hay hlt⟩
  have h := Finset.sum_le_sum_of_subset (f := fun a => (fiber f₁ a).card) hsub
  rw [Finset.sum_insert hnot, add_comm] at h
  exact h

/-- The offset of `y` together with `y`'s own block fits inside the
`f₂`-fiber's total. -/
theorem prefixOff_add_card_le_sum (f₁ : X → Y) (f₂ : Y → Z) (y : Y) :
    prefixOff κ f₁ f₂ y + (fiber f₁ y).card ≤
      ∑ y' ∈ fiber f₂ (f₂ y), (fiber f₁ y').card := by
  have hnot : y ∉ (fiber f₂ (f₂ y)).filter fun a => κ a < κ y := by simp
  have hsub : insert y ((fiber f₂ (f₂ y)).filter fun a => κ a < κ y) ⊆
      fiber f₂ (f₂ y) := by
    intro a ha
    rw [Finset.mem_insert] at ha
    rcases ha with rfl | ha
    · exact self_mem_fiber f₂ _
    · exact (Finset.mem_filter.mp ha).1
  have h := Finset.sum_le_sum_of_subset (f := fun a => (fiber f₁ a).card) hsub
  rw [Finset.sum_insert hnot, add_comm] at h
  exact h

/-!
### The composed garbage is a rank

Below the fiber size, strictly monotone in the lexicographic order, hence
injective on each fiber of `f₂ ∘ f₁`.
-/

/-- The composed garbage stays below the size of the input's `f₂ ∘ f₁`-fiber. -/
theorem prefixGarbage_lt_card_fiber (f₁ : X → Y) (f₂ : Y → Z) (x : X) :
    prefixGarbage ι κ f₁ f₂ x < (fiber (f₂ ∘ f₁) (f₂ (f₁ x))).card := by
  rw [card_fiber_comp]
  have h₁ := prefixOff_add_card_le_sum (κ := κ) f₁ f₂ (f₁ x)
  have h₂ := rank_lt_card_fiber (ι := ι) f₁ x
  unfold prefixGarbage
  omega

/-- Hence it stays below the fiber width of the composite. -/
theorem prefixGarbage_lt_fiberWidth (f₁ : X → Y) (f₂ : Y → Z) (x : X) :
    prefixGarbage ι κ f₁ f₂ x < fiberWidth (f₂ ∘ f₁) :=
  lt_of_lt_of_le (prefixGarbage_lt_card_fiber f₁ f₂ x)
    (card_fiber_le_fiberWidth (f₂ ∘ f₁) (f₂ (f₁ x)))

/-- Within one `f₂ ∘ f₁`-fiber, the composed garbage is strictly monotone in
the first lexicographic coordinate `κ (f₁ x)`. -/
theorem prefixGarbage_lt_of_lt {f₁ : X → Y} {f₂ : Y → Z} {x x' : X}
    (hfib : f₂ (f₁ x) = f₂ (f₁ x')) (hlt : κ (f₁ x) < κ (f₁ x')) :
    prefixGarbage ι κ f₁ f₂ x < prefixGarbage ι κ f₁ f₂ x' := by
  have h₁ := prefixOff_add_card_le (f₁ := f₁) hfib hlt
  have h₂ := rank_lt_card_fiber (ι := ι) f₁ x
  unfold prefixGarbage
  omega

/--
**The composed garbage separates the elements of a fiber.**

If the intermediate values differ, the offsets already differ by at least a
whole block; if they agree, the ranks inside the shared `f₁`-fiber differ.
-/
theorem prefixGarbage_eq_of_fiber {f₁ : X → Y} {f₂ : Y → Z} {x x' : X}
    (hfib : f₂ (f₁ x) = f₂ (f₁ x'))
    (h : prefixGarbage ι κ f₁ f₂ x = prefixGarbage ι κ f₁ f₂ x') : x = x' := by
  rcases lt_trichotomy (κ (f₁ x)) (κ (f₁ x')) with hlt | heq | hgt
  · exact absurd h (Nat.ne_of_lt (prefixGarbage_lt_of_lt hfib hlt))
  · have hy : f₁ x = f₁ x' := κ.injective heq
    unfold prefixGarbage at h
    rw [hy] at h
    exact rank_injOn hy (Nat.add_left_cancel h)
  · exact absurd h.symm (Nat.ne_of_lt (prefixGarbage_lt_of_lt hfib.symm hgt))

/-- The composed garbage is injective on every fiber of `f₂ ∘ f₁`. -/
theorem prefixGarbage_injOn_fiber (f₁ : X → Y) (f₂ : Y → Z) (z : Z) :
    Set.InjOn (prefixGarbage ι κ f₁ f₂) (fiber (f₂ ∘ f₁) z) := by
  intro x hx x' hx' h
  rw [Finset.mem_coe, mem_fiber, Function.comp_apply] at hx hx'
  exact prefixGarbage_eq_of_fiber (hx.trans hx'.symm) h

/-- On a fiber of `f₂ ∘ f₁` the composed garbage takes exactly the values
`0, …, card - 1`. -/
theorem image_prefixGarbage_fiber (f₁ : X → Y) (f₂ : Y → Z) (z : Z) :
    (fiber (f₂ ∘ f₁) z).image (prefixGarbage ι κ f₁ f₂) =
      Finset.range (fiber (f₂ ∘ f₁) z).card := by
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro n hn
    rw [Finset.mem_image] at hn
    obtain ⟨x, hx, rfl⟩ := hn
    rw [mem_fiber, Function.comp_apply] at hx
    rw [Finset.mem_range]
    have h := prefixGarbage_lt_card_fiber (ι := ι) (κ := κ) f₁ f₂ x
    rw [hx] at h
    exact h
  · exact le_of_eq (by
      rw [Finset.card_range, Finset.card_image_of_injOn (prefixGarbage_injOn_fiber f₁ f₂ z)])

/--
**Proposition 3 (minimal composition).**  The composed garbage maps each
fiber of `f₂ ∘ f₁` bijectively onto the initial segment `{0, …, card - 1}`.
-/
theorem prefixGarbage_bijOn_fiber (f₁ : X → Y) (f₂ : Y → Z) (z : Z) :
    Set.BijOn (prefixGarbage ι κ f₁ f₂) (fiber (f₂ ∘ f₁) z)
      (Finset.range (fiber (f₂ ∘ f₁) z).card) := by
  have h := (prefixGarbage_injOn_fiber (ι := ι) (κ := κ) f₁ f₂ z).bijOn_image
  rwa [← Finset.coe_image, image_prefixGarbage_fiber] at h

/-!
### The realization, and its minimality
-/

/--
The composed encoding as a realization of `f₂ ∘ f₁`: the garbage lands in
`Fin (fiberWidth (f₂ ∘ f₁))`, which `isLeast_garbageCard` identifies as the
least possible number of garbage values.
-/
def prefixRealization (ι : X ↪ ℕ) (κ : Y ↪ ℕ) (f₁ : X → Y) (f₂ : Y → Z) :
    Realization (f₂ ∘ f₁) (Fin (fiberWidth (f₂ ∘ f₁))) where
  garbage x := ⟨prefixGarbage ι κ f₁ f₂ x, prefixGarbage_lt_fiberWidth f₁ f₂ x⟩
  injective := by
    intro x x' h
    simp only [Prod.mk.injEq, Fin.mk.injEq, Function.comp_apply] at h
    exact prefixGarbage_eq_of_fiber (f₁ := f₁) (f₂ := f₂) h.1 h.2

/--
**The composed garbage register visits exactly `fiberWidth (f₂ ∘ f₁)` values.**

This is g-minimality for the composite: the values used form the initial
segment `{0, …, fiberWidth - 1}`, and by `fiberWidth_le_card_image` no
realization visits fewer.
-/
theorem card_image_prefixGarbage (f₁ : X → Y) (f₂ : Y → Z) :
    (Finset.univ.image (prefixGarbage ι κ f₁ f₂)).card = fiberWidth (f₂ ∘ f₁) := by
  refine le_antisymm ?_ ?_
  · have hsub : Finset.univ.image (prefixGarbage ι κ f₁ f₂) ⊆
        Finset.range (fiberWidth (f₂ ∘ f₁)) := by
      intro n hn
      rw [Finset.mem_image] at hn
      obtain ⟨x, -, rfl⟩ := hn
      exact Finset.mem_range.mpr (prefixGarbage_lt_fiberWidth f₁ f₂ x)
    have h := Finset.card_le_card hsub
    rwa [Finset.card_range] at h
  · refine Finset.sup_le fun z _ => ?_
    have h := Finset.card_le_card (Finset.image_subset_image (f := prefixGarbage ι κ f₁ f₂)
      (Finset.subset_univ (fiber (f₂ ∘ f₁) z)))
    rwa [image_prefixGarbage_fiber, Finset.card_range] at h

end Finite

/-!
### The minimum is attained stage-wise

Stated outside the `Fintype Y` block: the statement mentions only
`fiberWidth (f₂ ∘ f₁)`, so `Y` needs to be `Finite` for the *proof* alone,
where it supplies the enumeration `κ` and the `Fintype Y` instance behind
`prefixRealization`.
-/

/--
The minimum of `isLeast_garbageCard` for a composite is attained by the
stage-wise encoding, not only by re-ranking `f₂ ∘ f₁` from scratch.
-/
theorem fiberWidth_comp_mem_garbageCard [Fintype X] [Finite Y] [DecidableEq Y] [DecidableEq Z]
    (f₁ : X → Y) (f₂ : Y → Z) :
    fiberWidth (f₂ ∘ f₁) ∈
      {n : ℕ | ∃ G : Type, ∃ _ : Fintype G, Fintype.card G = n ∧
        Nonempty (Realization (f₂ ∘ f₁) G)} := by
  have := Fintype.ofFinite Y
  obtain ⟨ι⟩ := nonempty_embedding_nat X
  obtain ⟨κ⟩ := nonempty_embedding_nat Y
  exact ⟨Fin (fiberWidth (f₂ ∘ f₁)), inferInstance, Fintype.card_fin _,
    ⟨prefixRealization ι κ f₁ f₂⟩⟩

/-!
## Example: three-input conjunction in two stages

`and₃ (a, b, c) = a && b && c` computed as `andStep₂ ∘ andStep₁`, where the
first stage conjoins `a` and `b` and passes `c` through.  The fiber width of
each stage is `3`, so the ICNC-2012 product rule budgets `3 * 3 = 9` garbage
values (four bits).  The composite has fiber width `7` (three bits), and the
prefix-sum encoding uses exactly those seven values.
-/

/-- First stage: conjoin the first two inputs, pass the third through. -/
def andStep₁ (p : Bool × Bool × Bool) : Bool × Bool := (p.1 && p.2.1, p.2.2)

/-- Second stage: conjoin what is left. -/
def andStep₂ (q : Bool × Bool) : Bool := q.1 && q.2

/-- A binary enumeration of the three-bit inputs. -/
def enc₃ : Bool × Bool × Bool ↪ ℕ :=
  ⟨fun p => 4 * p.1.toNat + 2 * p.2.1.toNat + p.2.2.toNat, by decide⟩

/-- A binary enumeration of the two-bit intermediate values. -/
def enc₂ : Bool × Bool ↪ ℕ := ⟨fun q => 2 * q.1.toNat + q.2.toNat, by decide⟩

/-- The two stages compose to the three-input conjunction. -/
example : andStep₂ ∘ andStep₁ = fun p : Bool × Bool × Bool => p.1 && p.2.1 && p.2.2 := by
  funext p
  rfl

/-- Each stage alone has fiber width `3`. -/
example : fiberWidth andStep₁ = 3 ∧ fiberWidth andStep₂ = 3 := by decide

/-- The product rule budgets nine garbage values for the composite … -/
example : fiberWidth andStep₂ * fiberWidth andStep₁ = 9 := by decide

/-- … but the composite needs only seven, so the product rule is not tight. -/
example :
    fiberWidth (andStep₂ ∘ andStep₁) < fiberWidth andStep₂ * fiberWidth andStep₁ := by
  decide

/-- In bits: three against four. -/
example :
    garbageBits (andStep₂ ∘ andStep₁) = 3 ∧
      garbageBits andStep₂ + garbageBits andStep₁ = 4 := by
  decide

/-- The prefix-sum encoding uses exactly the seven values `0, …, 6`. -/
example :
    Finset.univ.image (prefixGarbage enc₃ enc₂ andStep₁ andStep₂) = Finset.range 7 := by
  decide

/-- On the big fiber (output `false`) it is a bijection onto `{0, …, 6}`. -/
example :
    (fiber (andStep₂ ∘ andStep₁) false).image
        (prefixGarbage enc₃ enc₂ andStep₁ andStep₂) =
      Finset.range 7 := by
  decide

end Cslib.Reversible
