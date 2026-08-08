/-
Copyright (c) 2026 Tetsuo Yokoyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuo Yokoyama
-/
import CslibReversible.CausalEquiv
import CslibReversible.Diamond

/-!
# The Parabolic Lemma

Every path is causally equivalent to a *parabola*: undo for a while, then do.

The proof is the one of Danos and Krivine, in the axiomatic form of
Lanese–Phillips–Ulidowski.  It has three steps:

* `fb_swap_or_cancel` — a forward step immediately followed by a backward one
  either cancels outright or commutes into backward-then-forward;
* `push_fwd` — hence a single forward step can be pushed rightwards through a
  block of backward steps;
* `parabolic` — hence, by induction on the path, every path sorts.

## The indexing pays here

Each of these statements carries its endpoints in the type of `CEq`, so none
of them has to repeat the side conditions relating sources and targets.  The
corresponding Rocq statement of `fb_swap_or_cancel` lists seven such
conditions; below there are none, because `Chained lts p [t, u] q` already
says all of it and `CEq.chained_right` gives it back on the other side.

## References

* [I. Lanese, I. Phillips, I. Ulidowski, *An Axiomatic Theory for Reversible
  Computation*, ACM TOCL 25(2), 2024][LPU2024]
-/

universe u v

namespace Cslib.LTS

variable {State : Type u} {Label : Type v} {lts : LTS State Label}
variable {Indep : Transition State Label → Transition State Label → Prop}

/--
**The Danos–Krivine elimination step.**  A forward transition immediately
followed by a backward one either is the undoing of that very step, or the two
commute into a backward step followed by a forward one.
-/
theorem fb_swap_or_cancel [DecidableEq State] [DecidableEq Label]
    [SquareProperty lts Indep] [BTI lts Indep]
    {t u : Transition State Label} {p q : State}
    (hc : Chained lts p [t, u] q) (hft : t.IsFwd) (hbu : u.IsBwd) :
    CEq lts Indep p q [t, u] [] ∨
      ∃ u' t', u'.IsBwd ∧ t'.IsFwd ∧ CEq lts Indep p q [t, u] [u', t'] := by
  obtain ⟨hts, htv, hus, huv, hut⟩ := hc
  have hft' : t.dir = Dir.fwd := hft
  have hbu' : u.dir = Dir.bwd := hbu
  refine Decidable.byCases (p := u = t.rev) (fun hu => ?_) (fun hu => ?_)
  · -- The second step undoes the first.
    subst hu
    have hpq : p = q := hts.symm.trans (by simpa using hut)
    subst hpq
    exact Or.inl (CEq.cancel htv hts)
  · refine Or.inr ?_
    -- `t.rev` and `u` are two backward transitions out of `t.tgt`.
    have hrv : t.rev.Valid lts := Transition.rev_valid htv
    have hrb : t.rev.IsBwd := by simp [Transition.IsBwd, Transition.rev, Dir.rev, hft']
    have hco : t.rev.Coinitial u := by simp [Transition.Coinitial, hus]
    have hind : Indep t.rev u :=
      BTI.bti hrv huv hco hrb hbu (fun h => hu (by rw [h]))
    obtain ⟨w, hw₁, hw₂⟩ := SquareProperty.square (Indep := Indep) hrv huv hind
    -- `u'` replays `u` from `p`; `tr'` is the residual of `t.rev` from `q`.
    set u' : Transition State Label := Transition.mk t.src u.lbl u.dir w
    set tr' : Transition State Label := Transition.mk u.tgt t.lbl t.dir.rev w
    have hu'v : u'.Valid lts := hw₁
    have htr'v : tr'.Valid lts := hw₂
    have ht'v : tr'.rev.Valid lts := Transition.rev_valid htr'v
    -- The one- and two-step paths the argument needs.
    have cP : Chained lts p [t] t.tgt := ⟨hts, htv, rfl⟩
    have cU' : Chained lts p [u'] w := ⟨hts, hu'v, rfl⟩
    have cT' : Chained lts w [tr'.rev] q := ⟨rfl, ht'v, by simpa using hut⟩
    have cL : Chained lts t.tgt [t.rev, u'] w := ⟨rfl, hrv, ⟨rfl, hu'v, rfl⟩⟩
    have cR : Chained lts t.tgt [u, tr'] w := ⟨hus, huv, ⟨rfl, htr'v, rfl⟩⟩
    have cTU : Chained lts p [t, u] q := ⟨hts, htv, hus, huv, hut⟩
    -- C1: the square, as a swap.
    have c1 : CEq lts Indep t.tgt w [t.rev, u'] [u, tr'] :=
      CEq.swap hind rfl rfl rfl rfl cL cR
    -- C2 / C3 / C4: cancel `t` against `t.rev` in front of `u'`.
    have c2 : CEq lts Indep p w [t, t.rev, u'] [u'] := by
      simpa using (CEq.cancel (Indep := Indep) htv hts).appendRight cU'
    have c3 : CEq lts Indep p w [t, t.rev, u'] [t, u, tr'] := by
      simpa using CEq.appendLeft cP c1
    have c4 : CEq lts Indep p w [u'] [t, u, tr'] := c2.symm.trans c3
    -- C5 / C6: append `tr'.rev` and cancel it against `tr'`.
    have c5 : CEq lts Indep p q [u', tr'.rev] [t, u, tr', tr'.rev] := by
      simpa using c4.appendRight cT'
    have c6 : CEq lts Indep p q [t, u, tr', tr'.rev] [t, u] := by
      simpa using CEq.appendLeft cTU (CEq.cancel (Indep := Indep) htr'v (by simpa using hut))
    have htr'dir : tr'.dir = t.dir.rev := rfl
    have ht'f : tr'.rev.IsFwd := by simp [Transition.IsFwd, htr'dir, hft']
    exact ⟨u', tr'.rev, hbu', ht'f, (c5.trans c6).symm⟩

/--
**Pushing a forward step through a block of backward steps.**  The result is
again a backward block followed by a forward block.
-/
theorem push_fwd [DecidableEq State] [DecidableEq Label]
    [SquareProperty lts Indep] [BTI lts Indep]
    {lb : List (Transition State Label)} {t : Transition State Label} {p q : State}
    (hb : ∀ x ∈ lb, x.IsBwd) (hft : t.IsFwd) (hc : Chained lts p (t :: lb) q) :
    ∃ lb₂ lf₂, (∀ x ∈ lb₂, x.IsBwd) ∧ (∀ x ∈ lf₂, x.IsFwd) ∧
      CEq lts Indep p q (t :: lb) (lb₂ ++ lf₂) := by
  induction lb generalizing t p with
  | nil =>
    exact ⟨[], [t], by simp, by simpa using hft, by simpa using CEq.refl hc⟩
  | cons u lb'' ih =>
    obtain ⟨hts, htv, hrest⟩ := hc
    have hbu : u.IsBwd := hb u (by simp)
    have hb'' : ∀ x ∈ lb'', x.IsBwd := fun x hx => hb x (by simp [hx])
    obtain ⟨hus, huv, hc''⟩ := hrest
    have hcTU : Chained lts p [t, u] u.tgt := ⟨hts, htv, hus, huv, rfl⟩
    rcases fb_swap_or_cancel (Indep := Indep) hcTU hft hbu with hcan | ⟨u', t', hbu', hft', hsw⟩
    · -- Cancellation: the two steps vanish and `lb''` is already sorted.
      refine ⟨lb'', [], hb'', by simp, ?_⟩
      have : CEq lts Indep p u.tgt [t, u] [] := hcan
      have := this.appendRight (post := lb'') hc''
      simpa using this
    · -- Swap: recurse on `t'` through `lb''`.
      have hch : Chained lts p [u', t'] u.tgt := hsw.chained_right
      obtain ⟨hu's, hu'v, ht's, ht'v, ht't⟩ := hch
      have hrec : Chained lts u'.tgt (t' :: lb'') q := ⟨ht's, ht'v, by rw [ht't]; exact hc''⟩
      obtain ⟨lb₂, lf₂, hb₂, hf₂, hcq₂⟩ := ih hb'' hft' hrec
      refine ⟨u' :: lb₂, lf₂, ?_, hf₂, ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hbu'
        · exact hb₂ x hx
      · have s1 : CEq lts Indep p q (t :: u :: lb'') (u' :: t' :: lb'') := by
          simpa using hsw.appendRight (post := lb'') hc''
        have s2 : CEq lts Indep p q (u' :: t' :: lb'') (u' :: (lb₂ ++ lf₂)) := by
          simpa using CEq.appendLeft (pre := [u']) ⟨hu's, hu'v, rfl⟩ hcq₂
        simpa using s1.trans s2

/--
**The Parabolic Lemma.**  Every path is causally equivalent to a backward
block followed by a forward block.
-/
theorem parabolic [DecidableEq State] [DecidableEq Label]
    [SquareProperty lts Indep] [BTI lts Indep]
    {l : List (Transition State Label)} {p q : State} (hc : Chained lts p l q) :
    ∃ lb lf, (∀ x ∈ lb, x.IsBwd) ∧ (∀ x ∈ lf, x.IsFwd) ∧
      CEq lts Indep p q l (lb ++ lf) := by
  induction l generalizing p with
  | nil => exact ⟨[], [], by simp, by simp, by simpa using CEq.refl hc⟩
  | cons t l ih =>
    obtain ⟨hts, htv, hc'⟩ := hc
    obtain ⟨lb, lf, hb, hf, hcq⟩ := ih hc'
    have hcons : CEq lts Indep p q (t :: l) (t :: (lb ++ lf)) := by
      simpa using CEq.appendLeft (pre := [t]) ⟨hts, htv, rfl⟩ hcq
    cases hd : t.dir with
    | bwd =>
      -- A backward head joins the backward block.
      refine ⟨t :: lb, lf, ?_, hf, ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hd
        · exact hb x hx
      · simpa using hcons
    | fwd =>
      -- A forward head has to be pushed through the backward block first.
      obtain ⟨-, -, hrest⟩ := hcons.chained_right
      obtain ⟨m, hlb, hlf⟩ := Chained.split hrest
      obtain ⟨lb₂, lf₂, hb₂, hf₂, hcq₂⟩ :=
        push_fwd (Indep := Indep) hb hd (⟨hts, htv, hlb⟩ : Chained lts p (t :: lb) m)
      refine ⟨lb₂, lf₂ ++ lf, hb₂, ?_, ?_⟩
      · intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact hf₂ x hx
        · exact hf x hx
      · refine hcons.trans ?_
        simpa [List.append_assoc] using hcq₂.appendRight (post := lf) hlf

end Cslib.LTS
