/-
Copyright (c) 2026 Tetsuo Yokoyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuo Yokoyama
-/
import CslibReversible.Complexity.Garbage
import CslibReversible.Diamond

/-!
# What reversibility costs a machine

`CslibReversible.Complexity.Garbage` measures the garbage a *function* needs.
This file connects that number to a *machine*: it shows that a reversible
transition system computing `f` cannot avoid carrying the garbage in its own
configurations.

The argument is short, and every step of it is already in the library.  A
reversible machine has unique origins (`unique_origin`), so a final
configuration determines the input it came from.  If distinct inputs also have
distinct start configurations, the map from inputs to final configurations is
injective — and an injective map into "answer paired with the rest" is exactly
a `Realization`.  The lower bound on realizations then applies verbatim.

## Main definitions

- `Computes lts f Garb`: a reversible machine computing `f`, whose final
  configurations are read as an answer in `Y` together with a residue in
  `Garb`.

## Main statements

- `Computes.final_injective`: distinct inputs end in distinct configurations.
  This is reversibility doing the work; it is false for irreversible machines,
  which is the whole point.
- `Computes.toRealization`: such a machine realizes `f` with `Garb` as garbage.
- `Computes.fiberWidth_le_card`: **the residue must have at least
  `fiberWidth f` values**, and so at least `garbageBits f` bits.  No cleverness
  in the machine's design can lower this, because nothing about the machine
  beyond reversibility was used.

## Scope

The bound is on what the machine *ends up holding*, not on what it holds while
running: a machine may use far more intermediate state and clean it up.  It is
also a bound for the whole of `X`.  Restricting the inputs can only lower the
fiber width, never raise it, so a bound obtained on a subset remains a valid
bound for that subset — but a machine that is optimal on a subset need not be
optimal on `X`, and a surplus measured on a subset is not evidence of waste.
-/

universe u v w x

namespace Cslib.Reversible

open Cslib.LTS

variable {State : Type u} {Label : Type v} {X : Type x} {Y : Type*} {Garb : Type w}

/--
A reversible machine computing `f`.

`readout` presents a configuration as an answer together with everything else
the configuration still holds; it is required to be injective because it is a
*change of view* on the configuration, not a summary that may forget part of
it.  A machine whose readout genuinely forgot something would not be
reversible.
-/
structure Computes (lts : LTS State Label) (f : X → Y) (Garb : Type w) where
  /-- The start configuration for an input. -/
  input : X → State
  /-- Distinct inputs start apart. -/
  input_injective : Function.Injective input
  /-- Start configurations have nothing to undo. -/
  input_origin : ∀ x, Origin lts (input x)
  /-- The configuration the machine halts in. -/
  final : X → State
  /-- Halting configurations rewind to their own start configuration. -/
  rewinds : ∀ x, Relation.ReflTransGen (BStep lts) (final x) (input x)
  /-- A configuration, viewed as an answer together with the rest of it. -/
  readout : State → Y × Garb
  /-- The view loses nothing. -/
  readout_injective : Function.Injective readout
  /-- What the machine halts holding answers the question. -/
  readout_fst : ∀ x, (readout (final x)).1 = f x

namespace Computes

variable {lts : LTS State Label} {f : X → Y}

/--
**Distinct inputs halt in distinct configurations.**

Two inputs halting in the same configuration would rewind to the same origin,
and the origins are the start configurations, which were assumed apart.

The hypotheses are spelled out on each result rather than left to section
variables: the conclusions do not mention `Indep`, so Lean would not include
them automatically.
-/
theorem final_injective
    {Indep : Transition State Label → Transition State Label → Prop}
    [DecidableEq State] [DecidableEq Label]
    [SquareProperty lts Indep] [BTI lts Indep] [WellFoundedBwd lts] [BStepDec lts]
    (C : Computes lts f Garb) : Function.Injective C.final := by
  intro x x' h
  refine C.input_injective (unique_origin (Indep := Indep) (C.rewinds x) (C.input_origin x) ?_
    (C.input_origin x'))
  rw [h]
  exact C.rewinds x'

/-- The residue left in the halting configuration. -/
def garbage (C : Computes lts f Garb) (x : X) : Garb := (C.readout (C.final x)).2

/--
**A reversible machine computing `f` realizes `f`, with its own residue as the
garbage.**
-/
def toRealization
    {Indep : Transition State Label → Transition State Label → Prop}
    [DecidableEq State] [DecidableEq Label]
    [SquareProperty lts Indep] [BTI lts Indep] [WellFoundedBwd lts] [BStepDec lts]
    (C : Computes lts f Garb) : Realization f Garb where
  garbage := C.garbage
  injective := by
    intro x x' h
    simp only [Prod.mk.injEq] at h
    obtain ⟨hf, hg⟩ := h
    refine final_injective (Indep := Indep) C (C.readout_injective (Prod.ext ?_ hg))
    rw [C.readout_fst, C.readout_fst, hf]

/--
**The residue must have at least `fiberWidth f` values.**

Nothing about the machine was used beyond reversibility and the fact that it
starts distinct inputs apart, so this is a bound on every reversible machine
for `f`, not on a particular design.
-/
theorem fiberWidth_le_card
    {Indep : Transition State Label → Transition State Label → Prop}
    [DecidableEq State] [DecidableEq Label]
    [SquareProperty lts Indep] [BTI lts Indep] [WellFoundedBwd lts] [BStepDec lts]
    [Fintype X] [DecidableEq Y] [Fintype Garb]
    (C : Computes lts f Garb) : fiberWidth f ≤ Fintype.card Garb :=
  Cslib.Reversible.fiberWidth_le_card (toRealization (Indep := Indep) C)

/-- The same bound in bits. -/
theorem garbageBits_le
    {Indep : Transition State Label → Transition State Label → Prop}
    [DecidableEq State] [DecidableEq Label]
    [SquareProperty lts Indep] [BTI lts Indep] [WellFoundedBwd lts] [BStepDec lts]
    [Fintype X] [DecidableEq Y] [Fintype Garb]
    (C : Computes lts f Garb) : garbageBits f ≤ Nat.clog 2 (Fintype.card Garb) :=
  Cslib.Reversible.garbageBits_le_log_card (toRealization (Indep := Indep) C)

-- `Fintype X` is absent from the statement but the proof counts fibers with it,
-- and `fiberWidth` is stated for `Fintype` rather than `Finite`.  Swapping the
-- binder for `Finite` would only move the instance into the proof and leave the
-- two `Fintype X` instances to be reconciled.
set_option linter.unusedFintypeInType false in
/--
A machine can halt holding nothing beyond the answer exactly when the function
it computes is injective.
-/
theorem injective_of_unique_garbage
    {Indep : Transition State Label → Transition State Label → Prop}
    [DecidableEq State] [DecidableEq Label]
    [SquareProperty lts Indep] [BTI lts Indep] [WellFoundedBwd lts] [BStepDec lts]
    [Fintype X] [DecidableEq Y] [Fintype Garb]
    (C : Computes lts f Garb) (h : Fintype.card Garb ≤ 1) : Function.Injective f := by
  rw [← garbageBits_eq_zero_iff, garbageBits]
  have hwidth : fiberWidth f ≤ Fintype.card Garb := fiberWidth_le_card (Indep := Indep) C
  have hmono : Nat.clog 2 (fiberWidth f) ≤ Nat.clog 2 (Fintype.card Garb) :=
    Nat.clog_mono_right 2 hwidth
  have hzero : Nat.clog 2 (Fintype.card Garb) = 0 := Nat.clog_of_right_le_one h 2
  omega

end Computes

end Cslib.Reversible
