/-
Copyright (c) 2026 Tetsuo Yokoyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuo Yokoyama
-/
import CslibReversible.Axioms

/-!
# Independence and the exchange law

This file is the *forward* half of the theory, and it is written so that a
reader who does not care about reversibility can use it: nothing in
`Exchange`, `FRun`, `SwapStep` or `MEq` mentions `Transition`, `Dir`, or a
backward step.

An independence relation on labels, together with the exchange law, is the
hypothesis under which

* consecutive independent steps may be transposed (`FRun.swap_head`),
* Mazurkiewicz-equivalent traces relate the same states
  (`FRun.of_mequiv`, `FRun.mequiv_iff`),

which is the soundness argument that partial-order reduction rests on: a
model checker may explore one representative of each equivalence class of
traces without losing reachable states.

## The bridge

The second section discharges `Exchange` from the reversible layer.  Every
`LTS` has a reversible reading for free — a backward transition simply *is*
the converse of a forward one (`Transition.rev_valid`) — so the Square Property of
Lanese–Phillips–Ulidowski, which speaks of *coinitial* transitions, can be
applied to the pair consisting of the *reversal* of the first step and the
second step.  Those two are coinitial at the intermediate state, and the
square they close is exactly the exchange law.

So the two theories are not neighbours; the forward one is a corollary of the
backward one:

```
SquareProperty (coinitial)  +  CLG   ⟹   Exchange (sequential)   ⟹   POR soundness
                            ⟹   bstep_diamond ⟹ unique_origin    (Diamond.lean)
```

## References

* [I. Lanese, I. Phillips, I. Ulidowski, *An Axiomatic Theory for Reversible
  Computation*, ACM TOCL 25(2), 2024][LPU2024]
-/

universe u v

namespace Cslib.LTS

variable {State : Type u} {Label : Type v}

/-! ## Runs and the exchange law -/

/-- A run: `FRun lts p w q` says the label sequence `w` takes `p` to `q`. -/
def FRun (lts : LTS State Label) : State → List Label → State → Prop
  | p, [], q => p = q
  | p, a :: as, q => ∃ m, lts.Tr p a m ∧ FRun lts m as q

variable {lts : LTS State Label} {I : Label → Label → Prop}

@[simp] theorem frun_nil {p q : State} : FRun lts p [] q ↔ p = q := Iff.rfl

@[simp] theorem frun_cons {a : Label} {w : List Label} {p q : State} :
    FRun lts p (a :: w) q ↔ ∃ m, lts.Tr p a m ∧ FRun lts m w q := Iff.rfl

/-- Runs compose. -/
theorem FRun.append {w₁ w₂ : List Label} {p m q : State}
    (h₁ : FRun lts p w₁ m) (h₂ : FRun lts m w₂ q) : FRun lts p (w₁ ++ w₂) q := by
  induction w₁ generalizing p with
  | nil => cases h₁; exact h₂
  | cons a w ih => obtain ⟨s, hs, hr⟩ := h₁; exact ⟨s, hs, ih hr⟩

/-- Runs decompose. -/
theorem FRun.split {w₁ w₂ : List Label} {p q : State}
    (h : FRun lts p (w₁ ++ w₂) q) : ∃ m, FRun lts p w₁ m ∧ FRun lts m w₂ q := by
  induction w₁ generalizing p with
  | nil => exact ⟨p, rfl, h⟩
  | cons a w ih =>
    obtain ⟨s, hs, hr⟩ := h
    obtain ⟨m, h₁, h₂⟩ := ih hr
    exact ⟨m, ⟨s, hs, h₁⟩, h₂⟩

/--
**Exchange law.**  Independent labels commute: a step `a` followed by an
independent step `b` can be performed in the other order, arriving at the
same state.

This is the classical hypothesis of partial-order reduction, stated with no
reference to reversibility.  It is discharged from the Square Property in
`exchange_of_square` below.
-/
class Exchange (lts : LTS State Label) (I : Label → Label → Prop) : Prop where
  /-- Consecutive independent steps commute. -/
  exchange : ∀ {a b : Label} {p q r : State}, I a b →
    lts.Tr p a q → lts.Tr q b r → ∃ q', lts.Tr p b q' ∧ lts.Tr q' a r

/-- Transposing the first two labels of a run. -/
theorem FRun.swap_head [Exchange lts I] {a b : Label} {w : List Label} {p q : State}
    (hI : I a b) (h : FRun lts p (a :: b :: w) q) : FRun lts p (b :: a :: w) q := by
  obtain ⟨m, hpm, n, hmn, hrest⟩ := h
  obtain ⟨m', h₁, h₂⟩ := Exchange.exchange hI hpm hmn
  exact ⟨m', h₁, n, h₂, hrest⟩

/-! ## Mazurkiewicz trace equivalence -/

/-- One transposition of adjacent independent labels, anywhere in a word. -/
inductive SwapStep (I : Label → Label → Prop) : List Label → List Label → Prop
  /-- Swap `a` and `b` between the prefix `pre` and the suffix `post`. -/
  | mk (pre : List Label) {a b : Label} (post : List Label) (h : I a b) :
      SwapStep I (pre ++ a :: b :: post) (pre ++ b :: a :: post)

/-- **Mazurkiewicz trace equivalence**: the reflexive transitive closure of swaps. -/
abbrev MEq (I : Label → Label → Prop) : List Label → List Label → Prop :=
  Relation.ReflTransGen (SwapStep I)

/-- A swap of a symmetric independence relation can be undone by a swap. -/
theorem SwapStep.symm (hs : ∀ a b : Label, I a b → I b a)
    {w w' : List Label} (h : SwapStep I w w') : SwapStep I w' w := by
  obtain ⟨pre, post, hI⟩ := h
  exact .mk pre post (hs _ _ hI)

/-- Trace equivalence is symmetric when independence is. -/
theorem MEq.symm (hs : ∀ a b : Label, I a b → I b a) {w w' : List Label}
    (h : MEq I w w') : MEq I w' w := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih => exact Relation.ReflTransGen.head (SwapStep.symm hs hstep) ih

/-! ## Soundness of partial-order reduction -/

/-- A single transposition anywhere in the word preserves the endpoints of a run. -/
theorem FRun.of_swapStep [Exchange lts I] {w w' : List Label} {p q : State}
    (hs : SwapStep I w w') (h : FRun lts p w q) : FRun lts p w' q := by
  obtain ⟨pre, post, hI⟩ := hs
  obtain ⟨m, h₁, h₂⟩ := FRun.split h
  exact h₁.append (FRun.swap_head hI h₂)

/--
**Trace equivalence preserves endpoints.**  Mazurkiewicz-equivalent words
relate exactly the same pairs of states.

This is the property partial-order reduction needs: exploring one
representative of each equivalence class loses no reachable state.
-/
theorem FRun.of_mequiv [Exchange lts I] {w w' : List Label} {p q : State}
    (h : MEq I w w') (hr : FRun lts p w q) : FRun lts p w' q := by
  induction h with
  | refl => exact hr
  | tail _ hstep ih => exact FRun.of_swapStep hstep ih

/-- The two-sided form, when independence is symmetric. -/
theorem FRun.mequiv_iff [Exchange lts I] (hs : ∀ a b : Label, I a b → I b a)
    {w w' : List Label} {p q : State} (h : MEq I w w') :
    FRun lts p w q ↔ FRun lts p w' q :=
  ⟨FRun.of_mequiv h, FRun.of_mequiv (MEq.symm hs h)⟩

/-- **Reachability is invariant under trace equivalence.** -/
theorem reachable_of_mequiv [Exchange lts I] {w w' : List Label} {p : State}
    (h : MEq I w w') (hr : ∃ q, FRun lts p w q) : ∃ q, FRun lts p w' q :=
  hr.imp fun _ hq => FRun.of_mequiv h hq

/-! ## The bridge: exchange from the Square Property -/

variable {Indep : Transition State Label → Transition State Label → Prop}

/--
The independence relation a label pair inherits from `Indep`.

`CLG` says independence is settled by the labels and coinitiality, so this
loses nothing.
-/
def LIndep (Indep : Transition State Label → Transition State Label → Prop) (a b : Label) : Prop :=
  ∃ t u, Indep t u ∧ t.lbl = a ∧ u.lbl = b

theorem LIndep.symm [IndepSymm Indep] {a b : Label} (h : LIndep Indep a b) :
    LIndep Indep b a := by
  obtain ⟨t, u, h, ht, hu⟩ := h
  exact ⟨u, t, IndepSymm.symm h, hu, ht⟩

/-- Under `CLG`, label-level independence transports to any coinitial pair. -/
theorem indep_of_lindep [CLG Indep] {a b : Label} (h : LIndep Indep a b)
    {t u : Transition State Label} (ht : t.lbl = a) (hu : u.lbl = b) (hc : t.Coinitial u) :
    Indep t u := by
  obtain ⟨t₀, u₀, h₀, ht₀, hu₀⟩ := h
  exact CLG.clg h₀ (ht.trans ht₀.symm) (hu.trans hu₀.symm) hc

/--
**The exchange law follows from the Square Property.**

Given `p -a→ q -b→ r`, the reversal of the first step and the second step are
both transitions out of `q`, so the Square Property applies to them.  The
square it closes has `p -b→ w` on one side and `w -a→ r` on the other, which
is the exchange law.

The reversal is available for nothing: `Transition.Valid` reads a backward
transition as the converse of a forward one, so no assumption beyond the
`LTS` itself is used here.
-/
instance exchange_of_square [SquareProperty lts Indep] [CLG Indep] :
    Exchange lts (LIndep Indep) where
  exchange := by
    intro a b p q r hI h₁ h₂
    have htv : (Transition.mk q a .bwd p).Valid lts := h₁
    have huv : (Transition.mk q b .fwd r).Valid lts := h₂
    have hind : Indep (Transition.mk q a .bwd p) (Transition.mk q b .fwd r) :=
      indep_of_lindep hI rfl rfl rfl
    obtain ⟨w, hw₁, hw₂⟩ := SquareProperty.square (Indep := Indep) htv huv hind
    exact ⟨w, hw₁, hw₂⟩

end Cslib.LTS
