/-
Copyright (c) 2026 Tetsuo Yokoyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuo Yokoyama
-/
import CslibReversible.Complexity.Garbage
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# How garbage composes

`Complexity.Garbage` pins the garbage requirement of a single function: it is the fiber
width, and `⌈log₂⌉` of that in bits.  Programs are not single functions, though.  They are
built by sequencing and by branching, and an analysis that wants to report a garbage count
for a program has to say what those two constructs do to the count.

This file answers that, and the answer is not the one a reader would guess from
`Complexity.Garbage` alone.

## The two readings of "how much garbage"

Write `c f y := (fiber f y).card` for the **garbage measure** of `f` — the whole function
`y ↦ |f⁻¹ y|`, not a number.  `fiberWidth f` is its supremum.  The distinction is the
content of this file:

* the *measure* composes, exactly: `card_fiber_comp` says the measure of `g ∘ f` is the
  pushforward of the measure of `f` along `g`, and `card_fiber_filter_add` says a case
  split adds the measures of its branches;
* the *supremum* only composes up to an inequality: `fiberWidth_comp_le` gives
  `fiberWidth (g ∘ f) ≤ fiberWidth g * fiberWidth f`, and `lt_fiberWidth_mul_example`
  shows the inequality can be strict.

So an analysis that carries only the width — one number per stage — pays the slack in that
inequality, in real garbage lines.  An analysis that carries the measure does not.

## Why this matters outside Lean

Yokoyama, Axelsen and Glück (ICNC 2012) minimize the garbage of a reversible simulation by
propagating exactly one number per stage, `𝒩` (their Eq. 9), which is `fiberWidth` here,
and packing the garbage of consecutive `let`s by the operator `⋄` of their Eq. 11, whose
bound component is the product `max₁ × max₂`.  (The printed `else` branch reads
`max₂ × max₂`; the product is what Eq. 14 and the case studies use.)  The paper calls the
method heuristic and says it "is not guaranteed to always reach solution with the optimal
garbage size" (§VI); `fiberWidth_comp_le` locates where the guarantee is lost.  Carrying one
number per stage can only reproduce the right-hand side of that inequality, so the method is
exact precisely when the inequality is tight.  Their two case studies — insertion sort and
mergesort — reach the true minimum `n!`, and `fiberWidth_comp_of_card_fiber_const` explains
why: with distinct keys every fiber has the same size, and that is a hypothesis under which
the inequality is tight.  Without it the method can lose, and the paper's own running
example shows it: the three-input conjunction of §IV-A is given the bound `3 × 3 = 9`
(Eq. 14), where the true width is `7` (`lt_fiberWidth_mul_example`), one bit more.  The
passages referred to are Eq. 9 (p. 382), Eq. 11 and 14 (p. 384) and §VI (p. 387).

## Main statements

- `card_fiber_comp`: the measure of a composite is the pushforward of the measure.
- `card_fiber_filter_add`: a case split adds branch measures.
- `fiberWidth_comp_le`, `garbageBits_comp_le`: the width, and the bit count, are only
  submultiplicative resp. subadditive.
- `fiberWidth_comp_of_card_fiber_const`: constant fiber size makes the bound tight.
- `lt_fiberWidth_mul_example`, `lt_garbageBits_add_example`: the bounds are not tight in
  general, on the concrete function ICNC 2012 uses.

## References

* T. Yokoyama, H. B. Axelsen, R. Glück.  *Minimizing Garbage Size by Generating Reversible
  Simulations.*  ICNC 2012, 379–387.
  [doi:10.1109/icnc.2012.73](https://doi.org/10.1109/icnc.2012.73)
* M. Soeken, R. Wille, O. Keszőcze, D. M. Miller, R. Drechsler.  *Embedding of Large
  Boolean Functions for Reversible Logic.*  ACM JETC 12(4), 2016.
  [doi:10.1145/2786982](https://doi.org/10.1145/2786982)
-/

universe u v w

namespace Cslib.Reversible

section Branch

variable {X : Type u} {Y : Type v}
variable [Fintype X] [DecidableEq Y]

/--
**A case split adds the measures of its branches.**

`fiber f y` is partitioned by any decidable guard, so the counts add.  Nothing here is
about reversibility; it is recorded because it is the second of the two composition rules
an analysis needs, and because the *branch* rule is the one ICNC 2012 already gets right —
its reversibilizer offsets each branch by the total count of the later ones.
-/
theorem card_fiber_filter_add (f : X → Y) (p : X → Prop) [DecidablePred p] (y : Y) :
    ((fiber f y).filter p).card + ((fiber f y).filter (fun x => ¬ p x)).card
      = (fiber f y).card :=
  Finset.card_filter_add_card_filter_not p

end Branch

section Compose

variable {X : Type u} {Y : Type v} {Z : Type w}
variable [Fintype X] [Fintype Y] [DecidableEq Y] [DecidableEq Z]

/--
**The garbage measure of a composite is the pushforward of the measure of the first stage.**

Every input that `g ∘ f` sends to `z` passes through exactly one intermediate value, and
that value lies in `g`'s fiber over `z`; grouping the inputs by which one they pass through
is the whole proof.

This is an equation, not a bound, and it is the reason to carry the measure rather than its
supremum: pushforward composes, `sup` does not.
-/
theorem card_fiber_comp (f : X → Y) (g : Y → Z) (z : Z) :
    (fiber (g ∘ f) z).card = ∑ y ∈ fiber g z, (fiber f y).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := f) (t := fiber g z)
      (fun x hx => by simpa using (mem_fiber.mp hx))]
  refine Finset.sum_congr rfl fun y hy => ?_
  congr 1
  ext x
  simp only [Finset.mem_filter, mem_fiber, Function.comp_apply]
  exact ⟨fun h => h.2, fun h => ⟨by rw [h]; simpa using hy, h⟩⟩

/--
**Widths are submultiplicative under composition.**

Immediate from `card_fiber_comp`: the sum has at most `fiberWidth g` terms and each is at
most `fiberWidth f`.  Both losses are real — see `lt_fiberWidth_mul_example`.
-/
theorem fiberWidth_comp_le (f : X → Y) (g : Y → Z) :
    fiberWidth (g ∘ f) ≤ fiberWidth g * fiberWidth f := by
  refine Finset.sup_le fun z _ => ?_
  rw [card_fiber_comp]
  calc ∑ y ∈ fiber g z, (fiber f y).card
      ≤ ∑ _y ∈ fiber g z, fiberWidth f :=
        Finset.sum_le_sum fun y _ => card_fiber_le_fiberWidth f y
    _ = (fiber g z).card * fiberWidth f := Finset.sum_const_nat fun _ _ => rfl
    _ ≤ fiberWidth g * fiberWidth f :=
        Nat.mul_le_mul_right _ (card_fiber_le_fiberWidth g z)

/--
**Garbage bits are subadditive under composition.**

The bit count is `⌈log₂⌉` of the width, so submultiplicativity of the width becomes
subadditivity of the bits.  This is the form a compiler would use: *at most* the sum of the
per-stage bit counts, never more.
-/
theorem garbageBits_comp_le (f : X → Y) (g : Y → Z) :
    garbageBits (g ∘ f) ≤ garbageBits g + garbageBits f := by
  refine le_trans (Nat.clog_mono_right 2 (fiberWidth_comp_le f g)) ?_
  refine Nat.clog_le_of_le_pow ?_
  rw [pow_add]
  exact Nat.mul_le_mul (Nat.le_pow_clog Nat.one_lt_two _) (Nat.le_pow_clog Nat.one_lt_two _)

/--
**When every fiber of the first stage has the same size, the product bound is exact.**

This is the hypothesis that makes carrying one number per stage lossless, and it is worth
stating separately because it is the case the literature's successful examples fall into:
sorting `n` distinct keys conflates exactly `n!` inputs at *every* output, and the stages of
insertion sort likewise, so the multiplicative rule loses nothing there.  It is a statement
about the function, not about the method.
-/
theorem fiberWidth_comp_of_card_fiber_const (f : X → Y) (g : Y → Z) (k : ℕ)
    (hf : ∀ y, (fiber f y).card = k) :
    fiberWidth (g ∘ f) = fiberWidth g * k := by
  have hsum : ∀ z, (fiber (g ∘ f) z).card = (fiber g z).card * k := by
    intro z
    rw [card_fiber_comp, Finset.sum_const_nat fun y _ => hf y]
  refine le_antisymm ?_ ?_
  · refine Finset.sup_le fun z _ => ?_
    rw [hsum]
    exact Nat.mul_le_mul_right _ (card_fiber_le_fiberWidth g z)
  · rcases Nat.eq_zero_or_pos k with hk | hk
    · simp [hk]
    -- `k > 0` makes every fiber of `f` inhabited, so `f` is onto and the two images agree.
    rcases Finset.eq_empty_or_nonempty (Finset.univ.image g) with hg | hg
    · simp [fiberWidth, hg]
    obtain ⟨z, hz, hzsup⟩ := Finset.exists_mem_eq_sup _ hg fun z => (fiber g z).card
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨x, hx⟩ : (fiber f y).Nonempty := by
      rw [← Finset.card_pos, hf]; exact hk
    have hmem : g y ∈ Finset.univ.image (g ∘ f) :=
      Finset.mem_image.mpr ⟨x, Finset.mem_univ x, by
        simpa [Function.comp_apply] using congrArg g (mem_fiber.mp hx)⟩
    calc fiberWidth g * k
        = (fiber g (g y)).card * k := by rw [fiberWidth, hzsup]
      _ = (fiber (g ∘ f) (g y)).card := (hsum _).symm
      _ ≤ fiberWidth (g ∘ f) :=
          Finset.le_sup (f := fun z => (fiber (g ∘ f) z).card) hmem

end Compose

/-!
### The bounds are not tight

The witness is the three-input conjunction of ICNC 2012 §IV-A, staged the way that paper
stages it: first `and` on the leading two inputs (carrying the third along untouched), then
`and` again.  Each stage conflates three inputs at worst; the composite conflates seven,
not nine.

Seven values need three bits and nine need four, so the loss is a whole garbage line — on
the paper's own running example.
-/

/-- First stage of the staged three-input conjunction: `and` the first two, carry the third. -/
private def andStage1 : Bool × Bool × Bool → Bool × Bool := fun p => (p.1 && p.2.1, p.2.2)

/-- Second stage of the staged three-input conjunction. -/
private def andStage2 : Bool × Bool → Bool := fun q => q.1 && q.2

example : fiberWidth andStage1 = 3 := by decide

example : fiberWidth andStage2 = 3 := by decide

example : fiberWidth (andStage2 ∘ andStage1) = 7 := by decide

/-- **Submultiplicativity is strict here: seven, not nine.** -/
theorem lt_fiberWidth_mul_example :
    fiberWidth (andStage2 ∘ andStage1) < fiberWidth andStage2 * fiberWidth andStage1 := by
  decide

/-- **And strict in bits: three garbage lines suffice where the product rule asks for four.** -/
theorem lt_garbageBits_add_example :
    garbageBits (andStage2 ∘ andStage1) < garbageBits andStage2 + garbageBits andStage1 := by
  decide

end Cslib.Reversible
