/-
Copyright (c) 2026 Tetsuo Yokoyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuo Yokoyama
-/
import CslibReversible.CausalConsistency
import CslibReversible.Instances.History

/-!
# A non-vacuous instance: two components, each with its own history

This file discharges the axioms for `revProd`, the parallel composition of the
history extensions of two arbitrary LTSs.  Independence is "the two
transitions act on different components".

The instance is chosen because it is the smallest one in which **BTI has
content**.  Put a single global history on the product and BTI fails: the
history serialises the two components, so undoing has to follow the global
order and two coinitial backward transitions need not be independent.  Give
each component its own history and BTI holds.  The Rocq development
`crcore-semantics` records the same fact as the counterexample
`plain_bti_fails`.

Everything here is about *arbitrary* `l₁` and `l₂`, so this is not one
instance but a family — and `unique_origin` follows for every member of it
without any further work.
-/

universe u₁ u₂ v₁ v₂

namespace Cslib.LTS

variable {S₁ : Type u₁} {S₂ : Type u₂} {L₁ : Type v₁} {L₂ : Type v₂}

/-- Parallel composition: each step is a step of one component. -/
def prodLTS (l₁ : LTS S₁ L₁) (l₂ : LTS S₂ L₂) : LTS (S₁ × S₂) (L₁ ⊕ L₂) where
  Tr p μ q :=
    match μ with
    | .inl α => l₁.Tr p.1 α q.1 ∧ p.2 = q.2
    | .inr β => l₂.Tr p.2 β q.2 ∧ p.1 = q.1

section

variable {l₁ : LTS S₁ L₁} {l₂ : LTS S₂ L₂}

/-- A left-labelled transition is a transition of the left component that fixes the right. -/
theorem valid_inl_iff {t : Transition (S₁ × S₂) (L₁ ⊕ L₂)} {α : L₁} (hα : t.lbl = .inl α) :
    t.Valid (prodLTS l₁ l₂) ↔
      (Transition.mk t.src.1 α t.dir t.tgt.1).Valid l₁ ∧ t.src.2 = t.tgt.2 := by
  cases hd : t.dir <;>
    simp [Transition.Valid, prodLTS, hα, hd, eq_comm, and_comm]

/-- A right-labelled transition is a transition of the right component that fixes the left. -/
theorem valid_inr_iff {t : Transition (S₁ × S₂) (L₁ ⊕ L₂)} {β : L₂} (hβ : t.lbl = .inr β) :
    t.Valid (prodLTS l₁ l₂) ↔
      (Transition.mk t.src.2 β t.dir t.tgt.2).Valid l₂ ∧ t.src.1 = t.tgt.1 := by
  cases hd : t.dir <;>
    simp [Transition.Valid, prodLTS, hβ, hd, eq_comm, and_comm]

/-- Transitions of a product are independent when they act on different components. -/
def SideIndep (t u : Transition (S₁ × S₂) (L₁ ⊕ L₂)) : Prop :=
  t.Coinitial u ∧ t.lbl.isLeft ≠ u.lbl.isLeft

instance : IsIndep (prodLTS l₁ l₂) (SideIndep (S₁ := S₁) (S₂ := S₂) (L₁ := L₁) (L₂ := L₂)) where
  coinitial h := h.1

instance : IndepSymm (SideIndep (S₁ := S₁) (S₂ := S₂) (L₁ := L₁) (L₂ := L₂)) where
  symm h := ⟨h.1.symm, h.2.symm⟩

instance : CLG (SideIndep (S₁ := S₁) (S₂ := S₂) (L₁ := L₁) (L₂ := L₂)) where
  clg h ht hu hco := ⟨hco, by rw [ht, hu]; exact h.2⟩

/--
**The Square Property.**  Steps of different components commute, in whichever
direction each is taken.
-/
instance : SquareProperty (prodLTS l₁ l₂)
    (SideIndep (S₁ := S₁) (S₂ := S₂) (L₁ := L₁) (L₂ := L₂)) where
  square {t u} htv huv hind := by
    obtain ⟨hco, hside⟩ := hind
    have hco' : t.src = u.src := hco
    -- The two transitions carry labels on opposite sides.
    cases hlt : t.lbl with
    | inl α =>
      cases hlu : u.lbl with
      | inl α' => rw [hlt, hlu] at hside; exact absurd rfl hside
      | inr β =>
        obtain ⟨hL, hsnd⟩ := (valid_inl_iff hlt).mp htv
        obtain ⟨hR, hfst⟩ := (valid_inr_iff hlu).mp huv
        exact ⟨(t.tgt.1, u.tgt.2),
          (valid_inr_iff (β := β) rfl).mpr ⟨by simpa [← hsnd, hco'] using hR, rfl⟩,
          (valid_inl_iff (α := α) rfl).mpr ⟨by simpa [hco', hfst] using hL, rfl⟩⟩
    | inr β =>
      cases hlu : u.lbl with
      | inr β' => rw [hlt, hlu] at hside; exact absurd rfl hside
      | inl α =>
        obtain ⟨hR, hfst⟩ := (valid_inr_iff hlt).mp htv
        obtain ⟨hL, hsnd⟩ := (valid_inl_iff hlu).mp huv
        exact ⟨(u.tgt.1, t.tgt.2),
          (valid_inl_iff (α := α) rfl).mpr ⟨by simpa [← hfst, hco'] using hL, rfl⟩,
          (valid_inr_iff (β := β) rfl).mpr ⟨by simpa [← hsnd, ← hco'] using hR, rfl⟩⟩

end

/-- Two components, each carrying its own history. -/
abbrev revProd (l₁ : LTS S₁ L₁) (l₂ : LTS S₂ L₂) :
    LTS (Hist S₁ L₁ × Hist S₂ L₂) (L₁ ⊕ L₂) :=
  prodLTS (histLTS l₁) (histLTS l₂)

section RevProd

variable {l₁ : LTS S₁ L₁} {l₂ : LTS S₂ L₂}

local notation "I" => SideIndep (S₁ := Hist S₁ L₁) (S₂ := Hist S₂ L₂) (L₁ := L₁) (L₂ := L₂)

/--
**BTI.**  This is the axiom that has content here.

Within one component a backward transition is unique (`histLTS_bwd_unique`),
so two *distinct* coinitial backward transitions must live in different
components — and transitions of different components are independent.

Replace the two per-component histories by a single global one and the
argument collapses: the global history serialises the components, so the two
backward transitions are no longer forced apart.  That is the content of
`plain_bti_fails` in `crcore-semantics`.
-/
instance : BTI (revProd l₁ l₂) I where
  bti {t u} htv huv hco htb hub hne := by
    refine ⟨hco, ?_⟩
    have hco' : t.src = u.src := hco
    intro hsame
    apply hne
    cases hlt : t.lbl with
    | inl α =>
      cases hlu : u.lbl with
      | inr β => rw [hlt, hlu] at hsame; exact absurd hsame (by simp)
      | inl α' =>
        obtain ⟨hL, hsnd⟩ := (valid_inl_iff hlt).mp htv
        obtain ⟨hL', hsnd'⟩ := (valid_inl_iff hlu).mp huv
        have heq := histLTS_bwd_unique hL htb hL' hub (by simp [hco'])
        have hα : α = α' := congrArg Transition.lbl heq
        have hfst : t.tgt.1 = u.tgt.1 := congrArg Transition.tgt heq
        exact Transition.ext hco' (by rw [hlt, hlu, hα]) (htb.trans hub.symm)
          (Prod.ext hfst (by rw [← hsnd, ← hsnd', hco']))
    | inr β =>
      cases hlu : u.lbl with
      | inl α => rw [hlt, hlu] at hsame; exact absurd hsame (by simp)
      | inr β' =>
        obtain ⟨hR, hfst⟩ := (valid_inr_iff hlt).mp htv
        obtain ⟨hR', hfst'⟩ := (valid_inr_iff hlu).mp huv
        have heq := histLTS_bwd_unique hR htb hR' hub (by simp [hco'])
        have hβ : β = β' := congrArg Transition.lbl heq
        have hsnd : t.tgt.2 = u.tgt.2 := congrArg Transition.tgt heq
        exact Transition.ext hco' (by rw [hlt, hlu, hβ]) (htb.trans hub.symm)
          (Prod.ext (by rw [← hfst, ← hfst', hco']) hsnd)

/-- Total length of the two histories: what undoing decreases. -/
def histLen (p : Hist S₁ L₁ × Hist S₂ L₂) : Nat := p.1.2.length + p.2.2.length

theorem histLen_lt_of_bstep {p q : Hist S₁ L₁ × Hist S₂ L₂}
    (h : BStep (revProd l₁ l₂) p q) : histLen q < histLen p := by
  obtain ⟨t, hv, hb, hs, ht⟩ := h
  subst hs; subst ht
  cases hlt : t.lbl with
  | inl α =>
    obtain ⟨hL, hsnd⟩ := (valid_inl_iff hlt).mp hv
    have hh := histLTS_bwd_src hL hb
    simp only [histLen, ← hsnd]
    rw [hh]
    simp
  | inr β =>
    obtain ⟨hR, hfst⟩ := (valid_inr_iff hlt).mp hv
    have hh := histLTS_bwd_src hR hb
    simp only [histLen, ← hfst]
    rw [hh]
    simp

/-- **Well-foundedness.**  Undoing terminates: each step shortens a history. -/
instance : WellFoundedBwd (revProd l₁ l₂) where
  wf := Subrelation.wf histLen_lt_of_bstep (measure histLen).wf

/-- A state whose two histories offer no undoable step is an origin. -/
theorem origin_of_no_head {p : Hist S₁ L₁ × Hist S₂ L₂}
    (h₁ : ∀ x α h', p.1.2 = (x, α) :: h' → ¬ l₁.Tr x α p.1.1)
    (h₂ : ∀ y β h', p.2.2 = (y, β) :: h' → ¬ l₂.Tr y β p.2.1) :
    Origin (revProd l₁ l₂) p := by
  rintro q ⟨t, hv, hb, rfl, rfl⟩
  cases hlt : t.lbl with
  | inl α =>
    obtain ⟨hL, _⟩ := (valid_inl_iff hlt).mp hv
    exact h₁ _ _ _ (histLTS_bwd_src hL hb) (histLTS_bwd_tr hL hb)
  | inr β =>
    obtain ⟨hR, _⟩ := (valid_inr_iff hlt).mp hv
    exact h₂ _ _ _ (histLTS_bwd_src hR hb) (histLTS_bwd_tr hR hb)

variable [∀ s μ s', Decidable (l₁.Tr s μ s')] [∀ s μ s', Decidable (l₂.Tr s μ s')]

/-- The right component's half of the search, once the left offers nothing. -/
private def stepRight (p : Hist S₁ L₁ × Hist S₂ L₂)
    (hL0 : ∀ x α h', p.1.2 = (x, α) :: h' → ¬ l₁.Tr x α p.1.1) :
    PSum {q // BStep (revProd l₁ l₂) p q} (∀ q, ¬ BStep (revProd l₁ l₂) p q) := by
  rcases e₂ : p.2.2 with _ | ⟨⟨y, β⟩, h₂'⟩
  · exact .inr (origin_of_no_head hL0 (by simp [e₂]))
  · exact
      if hTr : l₂.Tr y β p.2.1 then
        .inl ⟨(p.1, (y, h₂')), ⟨Transition.mk p (.inr β) .bwd (p.1, (y, h₂')),
          ⟨⟨hTr, e₂⟩, rfl⟩, rfl, rfl, rfl⟩⟩
      else
        .inr (origin_of_no_head hL0 (by
          intro y' β' h' he hT
          rw [e₂] at he
          simp only [List.cons.injEq, Prod.mk.injEq] at he
          obtain ⟨⟨rfl, rfl⟩, rfl⟩ := he
          exact hTr hT))

/--
**Undoing is decidable.**  Look at the head of each history: the recorded step
either really is a step of that component, or the state is unreachable and
there is nothing there to undo.
-/
instance : BStepDec (revProd l₁ l₂) where
  step p := by
    rcases e₁ : p.1.2 with _ | ⟨⟨x, α⟩, h₁'⟩
    · exact stepRight p (by simp [e₁])
    · exact
        if hTr : l₁.Tr x α p.1.1 then
          .inl ⟨((x, h₁'), p.2), ⟨Transition.mk p (.inl α) .bwd ((x, h₁'), p.2),
            ⟨⟨hTr, e₁⟩, rfl⟩, rfl, rfl, rfl⟩⟩
        else
          stepRight p (by
            intro x' α' h' he hT
            rw [e₁] at he
            simp only [List.cons.injEq, Prod.mk.injEq] at he
            obtain ⟨⟨rfl, rfl⟩, rfl⟩ := he
            exact hTr hT)

/--
**The payoff.**  Nothing below was proved about `revProd`: every reversible
product inherits it from the axioms discharged above.
-/
theorem revProd_unique_origin [DecidableEq S₁] [DecidableEq S₂]
    [DecidableEq L₁] [DecidableEq L₂]
    {p o₁ o₂ : Hist S₁ L₁ × Hist S₂ L₂}
    (h₁ : Relation.ReflTransGen (BStep (revProd l₁ l₂)) p o₁)
    (ho₁ : Origin (revProd l₁ l₂) o₁)
    (h₂ : Relation.ReflTransGen (BStep (revProd l₁ l₂)) p o₂)
    (ho₂ : Origin (revProd l₁ l₂) o₂) :
    o₁ = o₂ :=
  unique_origin (Indep := I) h₁ ho₁ h₂ ho₂

/--
**Causal consistency, for free.**

Nothing about `revProd` is proved here.  Every axiom it needs was discharged
above, and the theorem follows for the whole family — for arbitrary `l₁` and
`l₂`, in whatever state space and with whatever labels.
-/
theorem revProd_causal_consistency [DecidableEq S₁] [DecidableEq S₂]
    [DecidableEq L₁] [DecidableEq L₂]
    {p q : Hist S₁ L₁ × Hist S₂ L₂} {π₁ π₂ : List (Transition (Hist S₁ L₁ × Hist S₂ L₂) (L₁ ⊕ L₂))}
    (h₁ : Chained (revProd l₁ l₂) p π₁ q) (h₂ : Chained (revProd l₁ l₂) p π₂ q) :
    CEq (revProd l₁ l₂) I p q π₁ π₂ :=
  causal_consistency (Indep := I) h₁ h₂

end RevProd

end Cslib.LTS
