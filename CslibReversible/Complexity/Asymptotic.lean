/-
Copyright (c) 2026 Tetsuo Yokoyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuo Yokoyama
-/
import CslibReversible.Complexity.Machine
import CslibReversible.Instances.Deterministic
import Mathlib.Data.Fintype.Pi

/-!
# Asymptotic garbage complexity

`Complexity.Garbage` and `Complexity.Machine` measure the garbage a *finite*
function needs, and show that every reversible machine pays it.  This file
packages the same number as a resource on `{0,1}* → {0,1}*`, in the style of
`RevTIME` and `RevSPACE` (Axelsen 2011), and then shows that the resulting
class **collapses**: membership is decided by a combinatorial quantity of the
function, not by anything a machine does.

The length-`n` slice of `f : List Bool → List Bool` is `restrict f n`, and

```
garb f n = garbageBits (restrict f n) = ⌈log₂ μ(f_n)⌉
```

where `μ(f_n)` is the fiber width, the largest number of inputs of length `n`
sharing an output.  `RevGARB g` is the set of `f` for which, at every length,
*some* reversible machine computes the slice holding at most `g n` bits of
residue.

## Main definitions

- `restrict f n`: the slice `f_n : {0,1}^n → {0,1}*`.
- `garb f n`: the garbage measure `⌈log₂ μ(f_n)⌉`.
- `RevMachine f Garb`: some reversible machine — a labelled transition system
  satisfying the axioms of `CslibReversible.Axioms` — computing `f` with
  residue in `Garb`.  Nothing about the machine is assumed beyond
  reversibility.
- `RevGARB g`: the garbage class.
- `RevMachine.ofRealization`: the canonical one-step machine that turns a
  `Realization` into a `RevMachine`.  This is the upper half of the collapse
  at the machine level, which `Complexity.Garbage` only had at the function
  level.

## Main statements

- `mem_revGARB_iff`: **the class collapses**: `f ∈ RevGARB g ↔ ∀ n, garb f n ≤ g n`.
- `isLeast_revMachineGarbageBits`: **the least garbage any reversible machine
  for a finite `f` can end up holding is `garbageBits f`** — the machine-level
  analogue of `isLeast_garbageCard`; `isLeast_revMachineGarbageCard` is the
  same statement counted in values.
- `mem_revGARB_zero_iff`: garbage-free at every length exactly when every
  slice is injective.
- `revGARB_mono`, `mem_revGARB_garb`: the class is monotone and `garb f` is
  the least bound `f` satisfies.

## Why the collapse is bad news

A resource class is interesting when its lower bounds do not reduce to a
combinatorial quantity of the function.  Time and space are like that; garbage
is not.  `RevGARB g` is independent of the machine model and is completely
determined by `μ(f_n)`, so a class that measures garbage alone has no content
as a complexity class.  The theorem behind this — minimal garbage equals fiber
width — is too strong for anything else to happen.

The content returns as soon as a second resource is fixed: the construction
that achieves `garb f n` enumerates fibers, which in general takes exponential
time, and the question of how little garbage a machine can leave *within a
time bound* `t n` is open, with the same shape as Bennett's time–space
trade-off (Bennett 1989; Levine–Sherman 1990; Buhrman–Tromp–Vitányi 2001).

## What is *not* claimed

- **The theorem is not new.**  Minimal garbage equals fiber width is Theorem 1
  of Maslov and Dueck (2004) and goes back to Toffoli (1980).  What is new
  here is the asymptotic packaging (`garb`, `RevGARB`) and the machine-level
  statement (`RevMachine.ofRealization`, `isLeast_revMachineGarbageBits`),
  together with their mechanization.
- **Time is not modelled.**  `RevMachine` carries no step count, and `RevGARB`
  imposes no time bound.  The garbage–time trade-off is left open.
- **Garbage is counted in classical bits** of the residue type, as
  `Nat.clog 2 (Fintype.card Garb)`.  Resources of another kind — qubits,
  energy — are related by other maps, not by this number.
- **Taking the maximum over outputs is a convention**, not a theorem.  Garbage
  is relative to the output; `μ` collapses that to a function of `n` alone.
  Finer per-output information is available from `fiber` directly.
- **Nothing is said about measured programs.**  A bound obtained here is a
  bound for the whole of `{0,1}^n`.  A residue measured on some subset of the
  inputs can exceed it without that surplus being avoidable in general; see
  the scope note in `Complexity.Machine`.

## References

* H. B. Axelsen.  *Time complexity of tape reduction for reversible Turing
  machines.*  Reversible Computation 2011, LNCS 7165, 1–13.
* K.-J. Lange, P. McKenzie, A. Tapp.  *Reversible space equals deterministic
  space.*  Journal of Computer and System Sciences 60(2), 354–367, 2000.
* M. Li, P. Vitányi.  *Reversibility and adiabatic computation: trading time
  and space for energy.*  Proceedings of the Royal Society A 452, 769–789,
  1996.  [arXiv:quant-ph/9703022](https://arxiv.org/abs/quant-ph/9703022)
* C. H. Bennett.  *Time/space trade-offs for reversible computation.*  SIAM
  Journal on Computing 18(4), 766–776, 1989.
* R. Y. Levine, A. T. Sherman.  *A note on Bennett's time-space tradeoff for
  reversible computation.*  SIAM Journal on Computing 19(4), 673–677, 1990.
* H. Buhrman, J. Tromp, P. Vitányi.  *Time and space bounds for reversible
  simulation.*  Journal of Physics A 34(35), 6821–6830, 2001.
* D. Maslov, G. W. Dueck.  *Reversible Cascades With Minimal Garbage.*  IEEE
  TCAD 23(11), 1497–1509, 2004.
* T. Toffoli.  *Reversible computing.*  ICALP 1980, LNCS 85, 632–644.
-/

namespace Cslib.Reversible

open Cslib.LTS

/-! ## Slices and the garbage measure -/

/--
The **length-`n` slice** `f_n : {0,1}^n → {0,1}*` of `f : {0,1}* → {0,1}*`.

Inputs of length `n` are represented as `Fin n → Bool`, which is a `Fintype`,
so the finite theory of `Complexity.Garbage` applies to each slice.
-/
def restrict (f : List Bool → List Bool) (n : ℕ) : (Fin n → Bool) → List Bool :=
  fun x => f (List.ofFn x)

/--
The **garbage measure** of `f` at length `n`: `⌈log₂ μ(f_n)⌉`, the garbage
complexity in bits of the length-`n` slice.
-/
def garb (f : List Bool → List Bool) (n : ℕ) : ℕ := garbageBits (restrict f n)

/-- The garbage measure is the ceiling logarithm of the fiber width of the slice. -/
theorem garb_eq_clog (f : List Bool → List Bool) (n : ℕ) :
    garb f n = Nat.clog 2 (fiberWidth (restrict f n)) := rfl

/-! ## Some reversible machine computes `f` -/

variable {X Y : Type}

/--
**Some reversible machine computes `f` with residue in `Garb`.**

The machine is a labelled transition system with an independence relation
satisfying the axioms of `CslibReversible.Axioms` — the Square Property, BTI,
well-founded and decidable undoing — together with a `Computes` witness.
Nothing about its design is assumed beyond these axioms of reversibility;
in particular no step count is recorded, so no time bound can be expressed.

The state and label types live in `Type`, which is all the slices of a
function on bit strings need.
-/
structure RevMachine (f : X → Y) (Garb : Type) where
  /-- The configurations of the machine. -/
  State : Type
  /-- The labels of its steps. -/
  Label : Type
  /-- The transition system. -/
  lts : LTS State Label
  /-- The independence relation the axioms are stated over. -/
  Indep : Transition State Label → Transition State Label → Prop
  /-- Configurations can be compared. -/
  [decState : DecidableEq State]
  /-- Labels can be compared. -/
  [decLabel : DecidableEq Label]
  /-- The Square Property. -/
  [square : SquareProperty lts Indep]
  /-- Backward transitions are independent. -/
  [bti : BTI lts Indep]
  /-- Undoing terminates. -/
  [wf : WellFoundedBwd lts]
  /-- Undoing is decidable. -/
  [dec : BStepDec lts]
  /-- The machine computes `f`. -/
  computes : Computes lts f Garb

namespace RevMachine

variable {f : X → Y} {Garb : Type}

/--
**The residue of any reversible machine for `f` has at least `fiberWidth f`
values.**  This is `Computes.fiberWidth_le_card` with the machine bundled.
-/
theorem fiberWidth_le_card [Fintype X] [DecidableEq Y] [Fintype Garb]
    (M : RevMachine f Garb) : fiberWidth f ≤ Fintype.card Garb := by
  have := M.decState
  have := M.decLabel
  have := M.square
  have := M.bti
  have := M.wf
  have := M.dec
  exact Computes.fiberWidth_le_card (Indep := M.Indep) M.computes

/-- The same bound in bits. -/
theorem garbageBits_le [Fintype X] [DecidableEq Y] [Fintype Garb]
    (M : RevMachine f Garb) : garbageBits f ≤ Nat.clog 2 (Fintype.card Garb) :=
  Nat.clog_mono_right 2 M.fiberWidth_le_card

end RevMachine

/-! ## The garbage class -/

/--
**The garbage class `RevGARB g`**: the functions `f : {0,1}* → {0,1}*` such
that, for every input length `n`, some reversible machine computes the slice
`f_n` and halts holding a residue of at most `g n` bits.

Three conventions are built into this definition and should be read off it
rather than inferred:

* **Garbage is measured in classical bits** of the residue type,
  `Nat.clog 2 (Fintype.card Garb)`.  A count in qubits or in energy is a
  different map, not a different reading of this number.
* **The bound is uniform over outputs.**  Garbage is relative to the output
  `y`; the class bounds the worst case over all `y`, which is what makes it a
  function of `n` alone.  This is a convention, not a theorem.
* **No time bound is imposed.**  The machine may take as long as it likes, and
  `RevMachine` has no way to say otherwise.  This is what makes the class
  collapse (`mem_revGARB_iff`).
-/
def RevGARB (g : ℕ → ℕ) : Set (List Bool → List Bool) :=
  {f | ∀ n, ∃ Garb : Type, ∃ _ : Fintype Garb,
    Nonempty (RevMachine (restrict f n) Garb) ∧ Nat.clog 2 (Fintype.card Garb) ≤ g n}

/--
**Lower half of the collapse.**  Whatever reversible machine computes the
slice, its residue has at least `garb f n` bits.  Only reversibility is used.
-/
theorem garb_le_of_revMachine {f : List Bool → List Bool} {n : ℕ} {Garb : Type} [Fintype Garb]
    (M : RevMachine (restrict f n) Garb) : garb f n ≤ Nat.clog 2 (Fintype.card Garb) :=
  M.garbageBits_le

/-! ## The one-step machine

The upper half of the collapse needs a *machine*, not just a `Realization`.
The simplest one does the whole computation in a single step: from the
configuration `inl x` it moves to `inr (f x, garbage x)` and stops.  Backward
determinism is exactly the injectivity of the realization, undoing takes at
most one step, and deciding whether a halting configuration can be undone is a
finite search over the inputs.
-/

namespace OneStep

variable {G : Type} {f : X → Y}

/-- The one-step semantics: from an input, to the answer paired with its garbage. -/
inductive Step (R : Realization f G) : X ⊕ (Y × G) → Unit → X ⊕ (Y × G) → Prop where
  /-- Run the realization. -/
  | run (x : X) : Step R (.inl x) () (.inr (f x, R.garbage x))

/-- The one-step machine as an `LTS`. -/
def lts (R : Realization f G) : LTS (X ⊕ (Y × G)) Unit := ⟨Step R⟩

/-- Everything a step tells us. -/
theorem step_inv {R : Realization f G} {p q : X ⊕ (Y × G)} {l : Unit} (h : Step R p l q) :
    ∃ x, p = .inl x ∧ q = .inr (f x, R.garbage x) := by
  cases h with | run x => exact ⟨x, rfl, rfl⟩

/--
**Backward determinism.**  A halting configuration determines the input it
came from, because the realization is injective.
-/
instance bwdDeterministic (R : Realization f G) : BwdDeterministic (lts R) where
  bwd_unique {t u} htv htb huv hub hco := by
    rw [Transition.Valid, htb] at htv
    rw [Transition.Valid, hub] at huv
    obtain ⟨x, htgt, hsrc⟩ := step_inv htv
    obtain ⟨x', hutgt, husrc⟩ := step_inv huv
    have hs : t.src = u.src := hco
    have hx : x = x' := R.injective (Sum.inr.inj (hsrc.symm.trans (hs.trans husrc)))
    refine Transition.ext hs (Subsingleton.elim _ _) (htb.trans hub.symm) ?_
    rw [htgt, hutgt, hx]

/-- An input configuration has nothing to undo. -/
theorem origin_inl (R : Realization f G) (x : X) : Origin (lts R) (.inl x) := by
  rintro _ ⟨t, hv, hb, hs, -⟩
  rw [Transition.Valid, hb] at hv
  obtain ⟨x', -, hsrc⟩ := step_inv hv
  rw [hs] at hsrc
  cases hsrc

/-- Everything an undo step tells us. -/
theorem bstep_inv {R : Realization f G} {p q : X ⊕ (Y × G)} (h : BStep (lts R) p q) :
    ∃ x, q = .inl x ∧ p = .inr (f x, R.garbage x) := by
  obtain ⟨t, hv, hb, hs, ht⟩ := h
  rw [Transition.Valid, hb] at hv
  obtain ⟨x, htgt, hsrc⟩ := step_inv hv
  refine ⟨x, ?_, ?_⟩
  · rw [← ht]
    exact htgt
  · rw [← hs]
    exact hsrc

/-- The halting configuration of `x` undoes to `x`. -/
theorem bstep_inr (R : Realization f G) (x : X) :
    BStep (lts R) (.inr (f x, R.garbage x)) (.inl x) :=
  ⟨Transition.mk (.inr (f x, R.garbage x)) () .bwd (.inl x), Step.run x, rfl, rfl, rfl⟩

/-- The same, for a halting configuration given by its components. -/
theorem bstep_inr_of_eq (R : Realization f G) {x : X} {y : Y} {g : G}
    (h : f x = y ∧ R.garbage x = g) : BStep (lts R) (.inr (y, g)) (.inl x) := by
  obtain ⟨rfl, rfl⟩ := h
  exact bstep_inr R x

/-- A halting configuration that can be undone came from some input. -/
theorem exists_of_bstep_inr {R : Realization f G} {y : Y} {g : G} {q : X ⊕ (Y × G)}
    (h : BStep (lts R) (.inr (y, g)) q) : ∃ x, f x = y ∧ R.garbage x = g := by
  obtain ⟨x, -, hp⟩ := bstep_inv h
  obtain ⟨hy, hg⟩ := Prod.mk.inj (Sum.inr.inj hp)
  exact ⟨x, hy.symm, hg.symm⟩

/-- **Well-foundedness.**  A second undo would have to start from an input. -/
instance wellFoundedBwd (R : Realization f G) : WellFoundedBwd (lts R) where
  wf := ⟨fun p => Acc.intro p fun q hq => Acc.intro q fun r hr => by
    obtain ⟨x, hqx, -⟩ := bstep_inv hq
    rw [hqx] at hr
    exact (origin_inl R x r hr).elim⟩

-- The `Fintype X` is what makes the question "can this configuration be
-- undone?" decidable: it is a search over the inputs.  It does not appear in
-- the type because the type only says that a stepper exists.  The witness
-- itself is extracted with choice, which the complexity layer already uses.
set_option linter.unusedFintypeInType false in
/--
**Undoing is decidable.**  An input configuration cannot be undone; a halting
configuration `(y, g)` can be undone exactly when some input `x` has
`f x = y` and garbage `g`, which is decidable because the inputs are finite.
-/
noncomputable instance bStepDec [Fintype X] [DecidableEq Y] [DecidableEq G]
    (R : Realization f G) : BStepDec (lts R) where
  step p :=
    match p with
    | .inl x => .inr (origin_inl R x)
    | .inr (y, g) =>
      if h : ∃ x, f x = y ∧ R.garbage x = g then
        .inl ⟨.inl (Classical.choose h), bstep_inr_of_eq R (Classical.choose_spec h)⟩
      else
        .inr fun _ hq => h (exists_of_bstep_inr hq)

/-- The one-step machine computes `f`, with the realization's garbage as residue. -/
def computes (R : Realization f G) : Computes (lts R) f G where
  input := Sum.inl
  input_injective := by
    intro _ _ h
    exact Sum.inl.inj h
  input_origin := origin_inl R
  final x := .inr (f x, R.garbage x)
  rewinds x := .single (bstep_inr R x)
  readout := Sum.elim (fun x => (f x, R.garbage x)) id
  readout_injOn := by
    rintro _ ⟨x, rfl⟩ _ ⟨x', rfl⟩ h
    have h' : (f x, R.garbage x) = (f x', R.garbage x') := h
    rw [R.injective h']
  readout_fst _ := rfl

end OneStep

-- `Fintype X` builds the backward stepper of the machine (see `OneStep.bStepDec`);
-- the type of the result only records that a machine exists.
set_option linter.unusedFintypeInType false in
/--
**Every realization is realized by a machine.**  The canonical one-step
machine of `OneStep`, bundled with its axioms.  This is the upper half of the
collapse at the machine level.
-/
noncomputable def RevMachine.ofRealization {G : Type} {f : X → Y} [Fintype X] [DecidableEq X]
    [DecidableEq Y] [DecidableEq G] (R : Realization f G) : RevMachine f G where
  State := X ⊕ (Y × G)
  Label := Unit
  lts := OneStep.lts R
  Indep := NoIndep
  decState := inferInstance
  decLabel := inferInstance
  square := inferInstance
  bti := inferInstance
  wf := inferInstance
  dec := inferInstance
  computes := OneStep.computes R

/-- **A machine on exactly `fiberWidth f` residue values exists.** -/
theorem exists_revMachine_fin_fiberWidth [Fintype X] [DecidableEq X] [DecidableEq Y]
    (f : X → Y) : Nonempty (RevMachine f (Fin (fiberWidth f))) := by
  obtain ⟨R⟩ := realization_fin_fiberWidth f
  exact ⟨RevMachine.ofRealization R⟩

/-- Any residue type at least as large as the fiber width supports a machine. -/
theorem exists_revMachine_of_card_le [Fintype X] [DecidableEq X] [DecidableEq Y] {f : X → Y}
    {G : Type} [Fintype G] (h : fiberWidth f ≤ Fintype.card G) : Nonempty (RevMachine f G) := by
  classical
  obtain ⟨R⟩ := exists_realization_of_card_le h
  exact ⟨RevMachine.ofRealization R⟩

/-! ## The collapse -/

/--
**The garbage class collapses.**  `f ∈ RevGARB g` exactly when
`garb f n ≤ g n` for every `n`: membership is decided by the fiber widths of
the slices, and no machine can do better or needs to do worse.

The forward direction uses nothing about the machine beyond reversibility
(`garb_le_of_revMachine`); the backward direction is the one-step machine on
the rank-within-fiber realization (`exists_revMachine_fin_fiberWidth`).
-/
theorem mem_revGARB_iff (f : List Bool → List Bool) (g : ℕ → ℕ) :
    f ∈ RevGARB g ↔ ∀ n, garb f n ≤ g n := by
  change (∀ n, ∃ Garb : Type, ∃ _ : Fintype Garb,
    Nonempty (RevMachine (restrict f n) Garb) ∧ Nat.clog 2 (Fintype.card Garb) ≤ g n) ↔ _
  constructor
  · intro h n
    obtain ⟨Garb, hG, ⟨M⟩, hle⟩ := h n
    exact le_trans (garb_le_of_revMachine M) hle
  · intro h n
    refine ⟨Fin (fiberWidth (restrict f n)), inferInstance,
      exists_revMachine_fin_fiberWidth (restrict f n), ?_⟩
    exact (congrArg (Nat.clog 2) (Fintype.card_fin _)).trans_le (h n)

/--
**The least residue any reversible machine for `f` can hold is `fiberWidth f`
values.**  The machine analogue of `isLeast_garbageCard`.
-/
theorem isLeast_revMachineGarbageCard [Fintype X] [DecidableEq X] [DecidableEq Y] (f : X → Y) :
    IsLeast {b : ℕ | ∃ G : Type, ∃ _ : Fintype G, Fintype.card G = b ∧
      Nonempty (RevMachine f G)} (fiberWidth f) := by
  constructor
  · exact ⟨Fin (fiberWidth f), inferInstance, Fintype.card_fin _,
      exists_revMachine_fin_fiberWidth f⟩
  · rintro b ⟨G, hG, rfl, ⟨M⟩⟩
    exact M.fiberWidth_le_card

/--
**The least residue any reversible machine for `f` can hold is `garbageBits f`
bits.**  Together with `mem_revGARB_iff` this is the machine-level content of
the collapse: the bound is attained, and by a machine.
-/
theorem isLeast_revMachineGarbageBits [Fintype X] [DecidableEq X] [DecidableEq Y] (f : X → Y) :
    IsLeast {b : ℕ | ∃ G : Type, ∃ _ : Fintype G, Nat.clog 2 (Fintype.card G) = b ∧
      Nonempty (RevMachine f G)} (garbageBits f) := by
  constructor
  · exact ⟨Fin (fiberWidth f), inferInstance, congrArg (Nat.clog 2) (Fintype.card_fin _),
      exists_revMachine_fin_fiberWidth f⟩
  · rintro b ⟨G, hG, rfl, ⟨M⟩⟩
    exact M.garbageBits_le

/-! ## Corollaries -/

/--
**Garbage-free at every length exactly when every slice is injective.**  The
class with the zero bound is the class of functions injective on every input
length, as it must be.
-/
theorem mem_revGARB_zero_iff (f : List Bool → List Bool) :
    f ∈ RevGARB (fun _ => 0) ↔ ∀ n, Function.Injective (restrict f n) := by
  rw [mem_revGARB_iff]
  refine forall_congr' fun n => ?_
  rw [Nat.le_zero, garb, garbageBits_eq_zero_iff]

/-- A looser bound gives a larger class. -/
theorem revGARB_mono {g g' : ℕ → ℕ} (h : ∀ n, g n ≤ g' n) : RevGARB g ⊆ RevGARB g' := by
  intro f hf
  rw [mem_revGARB_iff] at hf ⊢
  exact fun n => le_trans (hf n) (h n)

/-- Every function is in the class of its own garbage measure. -/
theorem mem_revGARB_garb (f : List Bool → List Bool) : f ∈ RevGARB (garb f) :=
  (mem_revGARB_iff f (garb f)).2 fun _ => le_rfl

end Cslib.Reversible
