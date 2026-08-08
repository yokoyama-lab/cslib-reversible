/-
Copyright (c) 2026 Tetsuo Yokoyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuo Yokoyama
-/
import CslibReversible.Diamond
import CslibReversible.Parabolic
import CslibReversible.CausalConsistency
import CslibReversible.Independence
import Cslib.Languages.CCS.Basic

/-!
# CCSK: a calculus we did not design

`Instances.History` and `Instances.Product` are constructions of our own, so
they cannot tell us whether the axiom layer is the right shape for someone
else's calculus.  CCSK is the standard test: Phillips and Ulidowski obtain it
by applying their reversal method to Milner's CCS, and Lanese, Phillips and
Ulidowski use it as one of the running examples of the axiomatic theory.

The actions are CSLib's own `Cslib.CCS.Act`, so the syntax below really is
CCS with keys and not a private imitation of it.

## Labels carry locations

Transition labels are triples `(location, action, key)`.  The location records
the path taken through the term to reach the redex, in the style of the
*proved* transition systems that Aubert uses to define concurrency for CCSK.
Carrying it is what makes independence a condition **on labels**, and hence
what makes `CLG` hold by construction — which is exactly the route
Lanese–Phillips–Ulidowski take (§7.2: "Since coinitial independence is defined
on labels, we can deduce that the LTSI is CLG").

## Backward transitions are free

Nothing below defines a reverse SOS.  The axiom layer reads a backward
transition as the converse of a forward one, so the reverse rules of CCSK are
already present the moment the forward ones are: `Tr.pre` reversed *is* the
rule `μ[k].P ⤳ μ.P`.  This is the first place where that design choice pays
for itself on a calculus we did not write.

## Main definitions

- `Proc`: CCSK processes over CSLib's `Act` — prefix, executed prefix, parallel
  composition, choice and restriction, with communication between the
  components of a parallel composition.
- `Tr`: the forward SOS, with located labels.
- `lts`: the resulting `LTS`.
- `Sep`, `Concurrent`, `Indep`: independence as divergence of footprints **at a
  parallel composition**.  Divergence alone will not do once there is a choice
  operator: its two branches conflict rather than commute.

## Main statements

- `IsIndep`, `IndepSymm`, `CLG` instances: discharged outright.
- `keyCount_lt`: a forward step adds keys, hence `WellFoundedBwd`: undoing
  terminates.
- `last_step_concurrent`, hence `BTI`: two different ways of arriving at the
  same state are concurrent.  See the note on `Tr` for why the standardness
  side condition is what makes this come out true.

- `square_ff`, `square_bb`, `square_ex`, hence `SquareProperty`: transitions at
  concurrent locations commute, in each combination of directions.

- `preds`, a verified step-back function, hence `BStepDec`.  Its enumeration of
  communications is where `Classical.choice` enters; everything that does not
  go through the step-back function — `parabolic_ccsk`, `por_ccsk` — stays
  constructive.

With every class discharged, CCSK inherits the theory: `parabolic_ccsk`,
`causal_consistency_ccsk`, `unique_origin_ccsk`, `exists_origin_ccsk`,
`bstep_diamond_ccsk`, and — through the forward half, which never mentions
reversibility — `por_ccsk`.  None of their proofs says anything about CCSK.

## References

* [I.C.C. Phillips, I. Ulidowski, *Reversing algebraic process calculi*,
  JLAP 73(1–2):70–96, 2007][PhillipsUlidowski2007]
* [C. Aubert, *Concurrencies in reversible concurrent calculi*, RC 2022][Aubert2022]
* [I. Lanese, I. Phillips, I. Ulidowski, *An Axiomatic Theory for Reversible
  Computation*, ACM TOCL 25(2), 2024][LPU2024]
-/

universe u

namespace Cslib.LTS.CCSK

open Cslib.CCS

/-- Communication keys. -/
abbrev Key := Nat

/-- One step of the path from a term to a redex. -/
inductive Step where
  /-- Into the left component of a parallel composition. -/
  | l : Step
  /-- Into the right component of a parallel composition. -/
  | r : Step
  /-- Under a prefix that has already been executed. -/
  | past : Step
  /-- Into the left branch of a choice. -/
  | cl : Step
  /-- Into the right branch of a choice. -/
  | cr : Step
  /-- Under a restriction. -/
  | res : Step
  deriving DecidableEq, Repr

/-- The path taken through a term to reach one redex. -/
abbrev Path := List Step

/--
The *footprint* of a transition: every path it touches.

An ordinary action touches one path.  A communication touches two — one in
each component of a parallel composition — which is why this is a list and not
a single path.
-/
abbrev Loc := List Path

variable {Name : Type u}

/-- CCSK processes: CCS, plus prefixes that have been executed and keep their key. -/
inductive Proc (Name : Type u) : Type u where
  /-- The inactive process. -/
  | nil : Proc Name
  /-- A prefix that has not been executed. -/
  | pre (μ : Act Name) (p : Proc Name) : Proc Name
  /-- A prefix that has been executed, remembering its key. -/
  | preK (μ : Act Name) (k : Key) (p : Proc Name) : Proc Name
  /-- Parallel composition. -/
  | par (p q : Proc Name) : Proc Name
  /-- Choice.  CCSK keeps the branch not taken, so that the step can be undone. -/
  | choice (p q : Proc Name) : Proc Name
  /-- Restriction. -/
  | res (a : Name) (p : Proc Name) : Proc Name
  deriving DecidableEq

/-- The keys occurring in a process. -/
def keys : Proc Name → List Key
  | .nil => []
  | .pre _ p => keys p
  | .preK _ k p => k :: keys p
  | .par p q => keys p ++ keys q
  | .choice p q => keys p ++ keys q
  | .res _ p => keys p

/-- How many prefixes of a process have been executed. -/
def keyCount : Proc Name → Nat
  | .nil => 0
  | .pre _ p => keyCount p
  | .preK _ _ p => keyCount p + 1
  | .par p q => keyCount p + keyCount q
  | .choice p q => keyCount p + keyCount q
  | .res _ p => keyCount p

/-- A transition label: where the redex is, what it does, and under which key. -/
structure Lab (Name : Type u) where
  /-- Paths to the redexes. -/
  loc : Loc
  /-- The action performed. -/
  act : Act Name
  /-- The key attached to it. -/
  key : Key
  deriving DecidableEq

/--
The forward SOS of CCSK.

Freshness is enforced along the path: a key may not already occur in the
sibling of a parallel composition, nor on the prefix it passes under.

The prefix rule carries CCSK's standardness side condition — a prefix may be
executed only when nothing beneath it has run.  It is not decoration.  Without
it, `preK a k (preK b k' nil)` would admit **two** backward transitions, one
undoing `k` at location `[]` and one undoing `k'` at location `[past]`; those
locations are nested rather than concurrent, so BTI would be false.  The side
condition removes the first of the two, because `preK b k' nil` is not
standard.  Reversing the rule recovers the usual reverse prefix rule of CCSK,
`μ[k].P ⤳ μ.P` for standard `P`.
-/
inductive Tr : Proc Name → Lab Name → Proc Name → Prop where
  /-- Executing a prefix marks it with a fresh key; nothing beneath it has run. -/
  | pre {μ : Act Name} {k : Key} {p : Proc Name} (h : keys p = []) :
      Tr (.pre μ p) ⟨[[]], μ, k⟩ (.preK μ k p)
  /-- A process under an executed prefix keeps moving. -/
  | past {μ μ' : Act Name} {k k' : Key} {loc : Loc} {p p' : Proc Name}
      (hk : k' ≠ k) (h : Tr p ⟨loc, μ', k'⟩ p') :
      Tr (.preK μ k p) ⟨loc.map (Step.past :: ·), μ', k'⟩ (.preK μ k p')
  /-- The left component moves. -/
  | parL {loc : Loc} {μ : Act Name} {k : Key} {p p' q : Proc Name}
      (hq : k ∉ keys q) (h : Tr p ⟨loc, μ, k⟩ p') :
      Tr (.par p q) ⟨loc.map (Step.l :: ·), μ, k⟩ (.par p' q)
  /-- The right component moves. -/
  | parR {loc : Loc} {μ : Act Name} {k : Key} {p q q' : Proc Name}
      (hp : k ∉ keys p) (h : Tr q ⟨loc, μ, k⟩ q') :
      Tr (.par p q) ⟨loc.map (Step.r :: ·), μ, k⟩ (.par p q')
  /--
  The two components synchronise on complementary actions.

  Both sides record the *same* key: that is how CCSK remembers which two
  prefixes communicated.  The footprint is the union of the two sides, so a
  communication is independent only of transitions that avoid both.
  -/
  | com {locp locq : Loc} {μ μ' : Act Name} {k : Key} {p p' q q' : Proc Name}
      (hco : μ.Co μ') (hpq : k ∉ keys p) (hqp : k ∉ keys q)
      (hp : Tr p ⟨locp, μ, k⟩ p') (hq : Tr q ⟨locq, μ', k⟩ q') :
      Tr (.par p q) ⟨locp.map (Step.l :: ·) ++ locq.map (Step.r :: ·), Act.τ, k⟩ (.par p' q')
  /-- The left branch of a choice moves.  The branch not taken must be untouched. -/
  | choiceL {loc : Loc} {μ : Act Name} {k : Key} {p p' q : Proc Name}
      (hq : keys q = []) (h : Tr p ⟨loc, μ, k⟩ p') :
      Tr (.choice p q) ⟨loc.map (Step.cl :: ·), μ, k⟩ (.choice p' q)
  /-- The right branch of a choice moves. -/
  | choiceR {loc : Loc} {μ : Act Name} {k : Key} {p q q' : Proc Name}
      (hp : keys p = []) (h : Tr q ⟨loc, μ, k⟩ q') :
      Tr (.choice p q) ⟨loc.map (Step.cr :: ·), μ, k⟩ (.choice p q')
  /-- A restricted process moves on an action the restriction does not block. -/
  | res {loc : Loc} {μ : Act Name} {k : Key} {a : Name} {p p' : Proc Name}
      (hn : μ ≠ Act.name a) (hcn : μ ≠ Act.coname a) (h : Tr p ⟨loc, μ, k⟩ p') :
      Tr (.res a p) ⟨loc.map (Step.res :: ·), μ, k⟩ (.res a p')

/-- CCSK as an `LTS`. -/
def lts (Name : Type u) : LTS (Proc Name) (Lab Name) := ⟨Tr⟩

@[simp] theorem lts_Tr {p q : Proc Name} {α : Lab Name} :
    (lts Name).Tr p α q ↔ Tr p α q := Iff.rfl

/-! ## Independence -/

/--
Two paths are separate when they diverge **at a parallel composition**.

Divergence alone is not enough once the calculus has a choice operator: the
two branches of a choice are in *conflict*, not concurrent — taking one
discards the other — and a definition that merely asked for neither path to be
a prefix of the other would wrongly call them independent.  So the recursion
below accepts only the `l` / `r` pair.
-/
def Sep : Path → Path → Prop
  | [], _ => False
  | _ :: _, [] => False
  | a :: u, b :: v =>
      (a = .l ∧ b = .r) ∨ (a = .r ∧ b = .l) ∨ (a = b ∧ Sep u v)

theorem Sep.symm : ∀ {u v : Path}, Sep u v → Sep v u
  | [], _, h => h.elim
  | _ :: _, [], h => h.elim
  | _ :: u, _ :: v, h => by
    rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact Or.inr (Or.inl ⟨h₂, h₁⟩)
    · exact Or.inl ⟨h₂, h₁⟩
    · exact Or.inr (Or.inr ⟨h₁.symm, Sep.symm h₂⟩)

/-- Descending through the same constructor keeps paths separate. -/
theorem Sep.cons {s : Step} {u v : Path} (h : Sep u v) : Sep (s :: u) (s :: v) :=
  Or.inr (Or.inr ⟨rfl, h⟩)

/-- Descending through the same constructor reflects separateness. -/
theorem Sep.of_cons {s : Step} {u v : Path} (h : Sep (s :: u) (s :: v)) : Sep u v := by
  rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨_, h₂⟩
  · exact absurd (h₁ ▸ h₂) (by simp)
  · exact absurd (h₁ ▸ h₂) (by simp)
  · exact h₂

/-- The two components of a parallel composition are separate. -/
theorem Sep.of_par {s t : Step} (h : (s = .l ∧ t = .r) ∨ (s = .r ∧ t = .l)) (u v : Path) :
    Sep (s :: u) (t :: v) := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr (Or.inl ⟨rfl, rfl⟩)

/-- The two branches of a choice are in conflict, so never separate. -/
theorem not_sep_choice {u v : Path} : ¬ Sep (Step.cl :: u) (Step.cr :: v) := by
  rintro (⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩) <;> exact absurd h (by simp)

/-- The empty path is separate from none. -/
theorem not_sep_nil {v : Path} : ¬ Sep [] v := id

/--
Footprints are concurrent when every path of one is separate from every path
of the other.  A communication is therefore concurrent with a transition only
when that transition avoids *both* of the components it synchronises.
-/
def Concurrent (U V : Loc) : Prop := ∀ u ∈ U, ∀ v ∈ V, Sep u v

theorem Concurrent.symm {U V : Loc} (h : Concurrent U V) : Concurrent V U :=
  fun v hv u hu => (h u hu v hv).symm

/-- Descending through the same constructor keeps footprints concurrent. -/
theorem Concurrent.cons {s : Step} {U V : Loc} (h : Concurrent U V) :
    Concurrent (U.map (s :: ·)) (V.map (s :: ·)) := by
  intro u' hu' v' hv'
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hu'
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hv'
  exact (h u hu v hv).cons

/-- Descending through the same constructor reflects concurrency. -/
theorem Concurrent.of_cons {s : Step} {U V : Loc}
    (h : Concurrent (U.map (s :: ·)) (V.map (s :: ·))) : Concurrent U V := by
  intro u hu v hv
  exact Sep.of_cons (h _ (List.mem_map_of_mem hu) _ (List.mem_map_of_mem hv))

/-- Concurrency with a union is concurrency with both parts. -/
theorem Concurrent.append {A B C : Loc} (h₁ : Concurrent A C) (h₂ : Concurrent B C) :
    Concurrent (A ++ B) C := by
  intro u hu v hv
  rcases List.mem_append.mp hu with h | h
  · exact h₁ u h v hv
  · exact h₂ u h v hv

theorem Concurrent.of_append_left {A B C : Loc} (h : Concurrent (A ++ B) C) :
    Concurrent A C := fun u hu v hv => h u (List.mem_append_left _ hu) v hv

theorem Concurrent.of_append_right {A B C : Loc} (h : Concurrent (A ++ B) C) :
    Concurrent B C := fun u hu v hv => h u (List.mem_append_right _ hu) v hv

/-- Footprints in different components of a parallel composition are concurrent. -/
theorem Concurrent.of_par {s t : Step} (h : (s = .l ∧ t = .r) ∨ (s = .r ∧ t = .l)) (U V : Loc) :
    Concurrent (U.map (s :: ·)) (V.map (t :: ·)) := by
  intro u' hu' v' hv'
  obtain ⟨u, _, rfl⟩ := List.mem_map.mp hu'
  obtain ⟨v, _, rfl⟩ := List.mem_map.mp hv'
  exact Sep.of_par h u v

/-- The branches of a choice are never concurrent, so nothing can be independent of them. -/
theorem not_concurrent_choice {U V : Loc} (hU : U ≠ []) (hV : V ≠ [])
    (h : Concurrent (U.map (Step.cl :: ·)) (V.map (Step.cr :: ·))) : False := by
  obtain ⟨u, hu⟩ := List.exists_mem_of_ne_nil U hU
  obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil V hV
  exact not_sep_choice (h _ (List.mem_map_of_mem hu) _ (List.mem_map_of_mem hv))

/-- A prefix step is concurrent with nothing that can also happen. -/
theorem not_concurrent_root {V : Loc} (hV : V ≠ []) : ¬ Concurrent [[]] V := by
  intro h
  obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil V hV
  exact not_sep_nil (h [] (List.mem_singleton_self _) v hv)

/--
Independence of transitions: coinitial, at concurrent locations, and not
competing for the same key.

The key condition is not redundant.  Two transitions in different components
of a parallel composition may each choose a key that is fresh for the whole
process, and they may choose the *same* one; after either has fired, the other
is no longer available under that key, so the square cannot close.

This depends on the transitions only through their source and their labels,
which is what `CLG` asks for — the route Lanese–Phillips–Ulidowski take for
CCSK in §7.2.
-/
def Indep (t u : Transition (Proc Name) (Lab Name)) : Prop :=
  t.src = u.src ∧ Concurrent t.lbl.loc u.lbl.loc ∧ t.lbl.key ≠ u.lbl.key

instance : IsIndep (lts Name) (Indep (Name := Name)) where
  coinitial h := h.1

instance : IndepSymm (Indep (Name := Name)) where
  symm h := ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩

instance : CLG (Indep (Name := Name)) where
  clg h ht hu hc := ⟨hc, ht ▸ hu ▸ h.2.1, ht ▸ hu ▸ h.2.2⟩

/-- Every transition touches something. -/
theorem loc_ne_nil {p q : Proc Name} {α : Lab Name} (h : Tr p α q) : α.loc ≠ [] := by
  induction h with
  | pre => simp
  | past _ _ ih => simpa using fun hnil => ih (by simpa using hnil)
  | parL _ _ ih => simpa using fun hnil => ih (by simpa using hnil)
  | parR _ _ ih => simpa using fun hnil => ih (by simpa using hnil)
  | com _ _ _ _ _ ihp _ => simpa using fun hnil _ => ihp (by simpa using hnil)
  | choiceL _ _ ih => simpa using fun hnil => ih (by simpa using hnil)
  | choiceR _ _ ih => simpa using fun hnil => ih (by simpa using hnil)
  | res _ _ _ ih => simpa using fun hnil => ih (by simpa using hnil)

/-! ## What a step does to the keys -/

/-- The key of a step occurs in the state it leads to. -/
theorem key_mem_keys {p q : Proc Name} {α : Lab Name} (h : Tr p α q) : α.key ∈ keys q := by
  induction h with
  | pre => exact List.mem_cons_self ..
  | past _ _ ih => exact List.mem_cons_of_mem _ ih
  | parL _ _ ih => exact List.mem_append_left _ ih
  | parR _ _ ih => exact List.mem_append_right _ ih
  | com _ _ _ _ _ ihp _ => exact List.mem_append_left _ ihp
  | choiceL _ _ ih => exact List.mem_append_left _ ih
  | choiceR _ _ ih => exact List.mem_append_right _ ih
  | res _ _ _ ih => exact ih

/-- A step introduces its own key and nothing else. -/
theorem mem_keys_of_step {p q : Proc Name} {α : Lab Name} (h : Tr p α q) {x : Key}
    (hx : x ∈ keys q) : x = α.key ∨ x ∈ keys p := by
  induction h with
  | pre =>
    rcases List.mem_cons.mp hx with h | h
    · exact Or.inl h
    · exact Or.inr h
  | past _ _ ih =>
    rcases List.mem_cons.mp hx with h | h
    · exact Or.inr (h ▸ List.mem_cons_self ..)
    · exact (ih h).imp id (List.mem_cons_of_mem _)
  | parL _ _ ih =>
    rcases List.mem_append.mp hx with h | h
    · exact (ih h).imp id (List.mem_append_left _)
    · exact Or.inr (List.mem_append_right _ h)
  | parR _ _ ih =>
    rcases List.mem_append.mp hx with h | h
    · exact Or.inr (List.mem_append_left _ h)
    · exact (ih h).imp id (List.mem_append_right _)
  | com _ _ _ _ _ ihp ihq =>
    rcases List.mem_append.mp hx with h | h
    · exact (ihp h).imp id (List.mem_append_left _)
    · exact (ihq h).imp id (List.mem_append_right _)
  | choiceL _ _ ih =>
    rcases List.mem_append.mp hx with h | h
    · exact (ih h).imp id (List.mem_append_left _)
    · exact Or.inr (List.mem_append_right _ h)
  | choiceR _ _ ih =>
    rcases List.mem_append.mp hx with h | h
    · exact Or.inr (List.mem_append_left _ h)
    · exact (ih h).imp id (List.mem_append_right _)
  | res _ _ _ ih => exact ih hx

/-- A key that is fresh for the target of a step was fresh for its source. -/
theorem not_mem_keys_of_step {p q : Proc Name} {α : Lab Name} (h : Tr p α q) {x : Key}
    (hne : x ≠ α.key) (hp : x ∉ keys p) : x ∉ keys q :=
  fun hx => (mem_keys_of_step h hx).elim hne hp

/-! ## Undoing terminates -/

/-- A forward step executes at least one prefix — two, if it is a communication. -/
theorem keyCount_lt {p q : Proc Name} {α : Lab Name} (h : Tr p α q) :
    keyCount p < keyCount q := by
  induction h with
  | pre => simp [keyCount]
  | past _ _ ih => simpa [keyCount] using ih
  | parL _ _ ih => simp only [keyCount]; omega
  | parR _ _ ih => simp only [keyCount]; omega
  | com _ _ _ _ _ ihp ihq => simp only [keyCount]; omega
  | choiceL _ _ ih => simp only [keyCount]; omega
  | choiceR _ _ ih => simp only [keyCount]; omega
  | res _ _ _ ih => simpa [keyCount] using ih

/-- Undoing a step decreases the number of executed prefixes. -/
theorem keyCount_lt_of_bstep {p q : Proc Name} (h : BStep (lts Name) p q) :
    keyCount q < keyCount p := by
  obtain ⟨t, hv, hb, hs, ht⟩ := h
  subst hs; subst ht
  rw [Transition.Valid, hb] at hv
  have := keyCount_lt (Name := Name) hv
  omega

instance : WellFoundedBwd (lts Name) where
  wf := Subrelation.wf keyCount_lt_of_bstep (InvImage.wf keyCount Nat.lt_wfRel.wf)

/-! ## Backward transitions are independent -/

/--
Two different ways of arriving at the same state are at concurrent locations
and carry different keys.

The interesting cases are the two that cannot happen and the one that forces
the keys apart:

* a prefix step and a step underneath it cannot both be the last step, because
  the prefix rule leaves its continuation standard while a step underneath it
  leaves a key there;
* steps in the two components of a parallel composition have different keys,
  because each side condition says the key is fresh for the *other* component,
  and a step leaves its key in the component it acted on.
-/
theorem last_step_concurrent [DecidableEq Name] {p q₁ q₂ : Proc Name} {α β : Lab Name}
    (h₁ : Tr q₁ α p) (h₂ : Tr q₂ β p) (hne : ¬(α = β ∧ q₁ = q₂)) :
    Concurrent α.loc β.loc ∧ α.key ≠ β.key := by
  induction h₁ generalizing q₂ β with
  | @pre μ k p₀ hstd =>
    cases h₂ with
    | pre => exact absurd ⟨rfl, rfl⟩ hne
    | past _ h => exact absurd (hstd ▸ key_mem_keys h) (by simp)
  | @past μ μ' k k' loc p' p'' hk h ih =>
    cases h₂ with
    | pre hstd => exact absurd (hstd ▸ key_mem_keys h) (by simp)
    | past hk₂ h₂ =>
      obtain ⟨hc, hkey⟩ := ih h₂ (by
        rintro ⟨hl, hq⟩
        exact hne ⟨by simp_all [Lab.mk.injEq], by simp_all⟩)
      exact ⟨hc.cons, hkey⟩
  | @parL loc μ k p p' q hq h ih =>
    cases h₂ with
    | parL hq₂ h₂ =>
      obtain ⟨hc, hkey⟩ := ih h₂ (by
        rintro ⟨hl, hq⟩
        exact hne ⟨by simp_all [Lab.mk.injEq], by simp_all⟩)
      exact ⟨hc.cons, hkey⟩
    | @parR loc₂ μ₂ k₂ _ _ _ hp₂ h₂ =>
      exact ⟨Concurrent.of_par (by simp) _ _,
        fun he => hp₂ ((show k = k₂ from he) ▸ key_mem_keys h)⟩
    | @com locp₂ locq₂ μ₂ μ₂' k₂ _ _ _ _ _ _ _ hp₂ hq₂ =>
      have hkey : k ≠ k₂ := fun he => hq (he ▸ key_mem_keys hq₂)
      refine ⟨Concurrent.symm (Concurrent.append ?_ ?_), hkey⟩
      · exact Concurrent.symm
          ((ih hp₂ (by rintro ⟨hl, _⟩; exact hkey (by simp_all [Lab.mk.injEq]))).1).cons
      · exact Concurrent.of_par (by simp) _ _
  | @parR loc μ k p q q' hp h ih =>
    cases h₂ with
    | @parL loc₂ μ₂ k₂ _ _ _ hq₂ h₂ =>
      exact ⟨Concurrent.of_par (by simp) _ _,
        fun he => hq₂ ((show k = k₂ from he) ▸ key_mem_keys h)⟩
    | parR hp₂ h₂ =>
      obtain ⟨hc, hkey⟩ := ih h₂ (by
        rintro ⟨hl, hq⟩
        exact hne ⟨by simp_all [Lab.mk.injEq], by simp_all⟩)
      exact ⟨hc.cons, hkey⟩
    | @com locp₂ locq₂ μ₂ μ₂' k₂ _ _ _ _ _ _ _ hp₂ hq₂ =>
      have hkey : k ≠ k₂ := fun he => hp (he ▸ key_mem_keys hp₂)
      refine ⟨Concurrent.symm (Concurrent.append ?_ ?_), hkey⟩
      · exact Concurrent.of_par (by simp) _ _
      · exact Concurrent.symm
          ((ih hq₂ (by rintro ⟨hl, _⟩; exact hkey (by simp_all [Lab.mk.injEq]))).1).cons
  | @com locp locq μ μ' k p p' q q' hco hpq hqp hp hq ihp ihq =>
    cases h₂ with
    | @parL loc₂ μ₂ k₂ _ _ _ hq₂ h₂ =>
      have hkey : k ≠ k₂ := fun he => hq₂ (he ▸ key_mem_keys hq)
      refine ⟨Concurrent.append ?_ ?_, hkey⟩
      · exact ((ihp h₂ (by rintro ⟨hl, _⟩; exact hkey (by simp_all [Lab.mk.injEq]))).1).cons
      · exact Concurrent.of_par (by simp) _ _
    | @parR loc₂ μ₂ k₂ _ _ _ hp₂ h₂ =>
      have hkey : k ≠ k₂ := fun he => hp₂ (he ▸ key_mem_keys hp)
      refine ⟨Concurrent.append ?_ ?_, hkey⟩
      · exact Concurrent.of_par (by simp) _ _
      · exact ((ihq h₂ (by rintro ⟨hl, _⟩; exact hkey (by simp_all [Lab.mk.injEq]))).1).cons
    | @com locp₂ locq₂ μ₂ μ₂' k₂ b₂ _ c₂ _ _ _ _ hp₂ hq₂ =>
      have hkey : k ≠ k₂ := by
        intro hkk
        have e1 : (⟨locp, μ, k⟩ : Lab Name) = ⟨locp₂, μ₂, k₂⟩ ∧ p = b₂ :=
          Decidable.byContradiction fun hcon => absurd hkk (ihp hp₂ hcon).2
        have e2 : (⟨locq, μ', k⟩ : Lab Name) = ⟨locq₂, μ₂', k₂⟩ ∧ q = c₂ :=
          Decidable.byContradiction fun hcon => absurd hkk (ihq hq₂ hcon).2
        obtain ⟨el, rfl⟩ := e1
        obtain ⟨er, rfl⟩ := e2
        exact hne ⟨by simp_all [Lab.mk.injEq], rfl⟩
      refine ⟨Concurrent.append (Concurrent.symm (Concurrent.append ?_ ?_))
        (Concurrent.symm (Concurrent.append ?_ ?_)), hkey⟩
      · exact Concurrent.symm
          ((ihp hp₂ (by rintro ⟨hl, _⟩; exact hkey (by simp_all [Lab.mk.injEq]))).1).cons
      · exact Concurrent.of_par (by simp) _ _
      · exact Concurrent.of_par (by simp) _ _
      · exact Concurrent.symm
          ((ihq hq₂ (by rintro ⟨hl, _⟩; exact hkey (by simp_all [Lab.mk.injEq]))).1).cons
  | @choiceL loc μ k a P' Q hq h ih =>
    cases h₂ with
    | choiceL hq₂ h₂ =>
      obtain ⟨hc, hkey⟩ := ih h₂ (by
        rintro ⟨hl, hq⟩
        exact hne ⟨by simp_all [Lab.mk.injEq], by simp_all⟩)
      exact ⟨hc.cons, hkey⟩
    | choiceR hp₂ h₂ => exact absurd (hp₂ ▸ key_mem_keys h) (by simp)
  | @choiceR loc μ k P a Q' hp h ih =>
    cases h₂ with
    | choiceL hq₂ h₂ => exact absurd (hq₂ ▸ key_mem_keys h) (by simp)
    | choiceR hp₂ h₂ =>
      obtain ⟨hc, hkey⟩ := ih h₂ (by
        rintro ⟨hl, hq⟩
        exact hne ⟨by simp_all [Lab.mk.injEq], by simp_all⟩)
      exact ⟨hc.cons, hkey⟩
  | @res loc μ k a p p' hn hcn h ih =>
    cases h₂ with
    | res hn₂ hcn₂ h₂ =>
      obtain ⟨hc, hkey⟩ := ih h₂ (by
        rintro ⟨hl, hq⟩
        exact hne ⟨by simp_all [Lab.mk.injEq], by simp_all⟩)
      exact ⟨hc.cons, hkey⟩

instance [DecidableEq Name] : BTI (lts Name) (Indep (Name := Name)) where
  bti {t u} htv huv hco htb hub hne := by
    rw [Transition.Valid, htb] at htv
    rw [Transition.Valid, hub] at huv
    rw [Transition.Coinitial] at hco
    rw [← hco] at huv
    refine ⟨hco, last_step_concurrent htv huv ?_⟩
    rintro ⟨hl, ht⟩
    exact hne (Transition.ext hco hl (htb.trans hub.symm) ht)

/-! ## The Square Property -/

/-- A step never removes a key. -/
theorem mem_keys_of_source {p q : Proc Name} {α : Lab Name} (h : Tr p α q) {x : Key}
    (hx : x ∈ keys p) : x ∈ keys q := by
  induction h with
  | pre => exact List.mem_cons_of_mem _ hx
  | past _ _ ih =>
    rcases List.mem_cons.mp hx with h | h
    · exact h ▸ List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (ih h)
  | parL _ _ ih =>
    rcases List.mem_append.mp hx with h | h
    · exact List.mem_append_left _ (ih h)
    · exact List.mem_append_right _ h
  | parR _ _ ih =>
    rcases List.mem_append.mp hx with h | h
    · exact List.mem_append_left _ h
    · exact List.mem_append_right _ (ih h)
  | com _ _ _ _ _ ihp ihq =>
    rcases List.mem_append.mp hx with h | h
    · exact List.mem_append_left _ (ihp h)
    · exact List.mem_append_right _ (ihq h)
  | choiceL _ _ ih =>
    rcases List.mem_append.mp hx with h | h
    · exact List.mem_append_left _ (ih h)
    · exact List.mem_append_right _ h
  | choiceR _ _ ih =>
    rcases List.mem_append.mp hx with h | h
    · exact List.mem_append_left _ h
    · exact List.mem_append_right _ (ih h)
  | res _ _ _ ih => exact ih hx

/-- A key that is fresh for the target of a step is fresh for its source. -/
theorem not_mem_keys_of_target {p q : Proc Name} {α : Lab Name} (h : Tr p α q) {x : Key}
    (hq : x ∉ keys q) : x ∉ keys p := fun hx => hq (mem_keys_of_source h hx)

/--
**Forward diamond.**  Two forward steps out of the same state at concurrent
locations converge.
-/
theorem square_ff {p a b : Proc Name} {α β : Lab Name}
    (h₁ : Tr p α a) (h₂ : Tr p β b)
    (hc : Concurrent α.loc β.loc) (hk : α.key ≠ β.key) :
    ∃ w, Tr a β w ∧ Tr b α w := by
  induction h₁ generalizing b β with
  | pre => exact absurd hc (not_concurrent_root (loc_ne_nil h₂))
  | @past μ μ' k k' loc p₀ p₀' hk₁ h ih =>
    cases h₂ with
    | @past _ μ₂ _ k₂ loc₂ _ b₀ hk₂ h₂ =>
      obtain ⟨w₀, hw₁, hw₂⟩ := ih h₂ hc.of_cons hk
      exact ⟨.preK μ k w₀, .past hk₂ hw₁, .past hk₁ hw₂⟩
  | @parL loc μ k p₁ p₁' q hq h ih =>
    cases h₂ with
    | @parL loc₂ μ₂ k₂ _ b₁ _ hq₂ h₂ =>
      obtain ⟨w₁, hw₁, hw₂⟩ := ih h₂ hc.of_cons hk
      exact ⟨.par w₁ q, .parL hq₂ hw₁, .parL hq hw₂⟩
    | @parR loc₂ μ₂ k₂ _ _ q' hp₂ h₂ =>
      exact ⟨.par p₁' q', .parR (not_mem_keys_of_step h (Ne.symm hk) hp₂) h₂,
        .parL (not_mem_keys_of_step h₂ hk hq) h⟩
    | @com locp₂ locq₂ μ₂ μ₂' k₂ _ P₂ _ Q₂ hco₂ hpq₂ hqp₂ hp₂ hq₂ =>
      obtain ⟨w₁, hw₁, hw₂⟩ :=
        ih hp₂ (hc.symm.of_append_left.symm.of_cons) hk
      exact ⟨.par w₁ Q₂,
        .com hco₂ (not_mem_keys_of_step h (Ne.symm hk) hpq₂) hqp₂ hw₁ hq₂,
        .parL (not_mem_keys_of_step hq₂ hk hq) hw₂⟩
  | @parR loc μ k p₁ q q' hp h ih =>
    cases h₂ with
    | @parL loc₂ μ₂ k₂ _ b₁ _ hq₂ h₂ =>
      exact ⟨.par b₁ q', .parL (not_mem_keys_of_step h (Ne.symm hk) hq₂) h₂,
        .parR (not_mem_keys_of_step h₂ hk hp) h⟩
    | @parR loc₂ μ₂ k₂ _ _ b₁ hp₂ h₂ =>
      obtain ⟨w₁, hw₁, hw₂⟩ := ih h₂ hc.of_cons hk
      exact ⟨.par p₁ w₁, .parR hp₂ hw₁, .parR hp hw₂⟩
    | @com locp₂ locq₂ μ₂ μ₂' k₂ _ P₂ _ Q₂ hco₂ hpq₂ hqp₂ hp₂ hq₂ =>
      obtain ⟨w₁, hw₁, hw₂⟩ :=
        ih hq₂ (hc.symm.of_append_right.symm.of_cons) hk
      exact ⟨.par P₂ w₁,
        .com hco₂ hpq₂ (not_mem_keys_of_step h (Ne.symm hk) hqp₂) hp₂ hw₁,
        .parR (not_mem_keys_of_step hp₂ hk hp) hw₂⟩
  | @com locp locq μ μ' k P P' Q Q' hco hpq hqp hp hq ihp ihq =>
    cases h₂ with
    | @parL loc₂ μ₂ k₂ _ P₂ _ hq₂ h₂ =>
      obtain ⟨w₁, hw₁, hw₂⟩ :=
        ihp h₂ (hc.of_append_left.of_cons) hk
      exact ⟨.par w₁ Q',
        .parL (not_mem_keys_of_step hq (Ne.symm hk) hq₂) hw₁,
        .com hco (not_mem_keys_of_step h₂ hk hpq) hqp hw₂ hq⟩
    | @parR loc₂ μ₂ k₂ _ _ Q₂ hp₂ h₂ =>
      obtain ⟨w₁, hw₁, hw₂⟩ :=
        ihq h₂ (hc.of_append_right.of_cons) hk
      exact ⟨.par P' w₁,
        .parR (not_mem_keys_of_step hp (Ne.symm hk) hp₂) hw₁,
        .com hco hpq (not_mem_keys_of_step h₂ hk hqp) hp hw₂⟩
    | @com locp₂ locq₂ μ₂ μ₂' k₂ _ P₂ _ Q₂ hco₂ hpq₂ hqp₂ hp₂ hq₂ =>
      obtain ⟨w₁, hw₁, hw₂⟩ :=
        ihp hp₂ (hc.of_append_left.symm.of_append_left.symm.of_cons) hk
      obtain ⟨w₂, hv₁, hv₂⟩ :=
        ihq hq₂ (hc.of_append_right.symm.of_append_right.symm.of_cons) hk
      exact ⟨.par w₁ w₂,
        .com hco₂ (not_mem_keys_of_step hp (Ne.symm hk) hpq₂)
          (not_mem_keys_of_step hq (Ne.symm hk) hqp₂) hw₁ hv₁,
        .com hco (not_mem_keys_of_step hp₂ hk hpq)
          (not_mem_keys_of_step hq₂ hk hqp) hw₂ hv₂⟩
  | @choiceL loc μ k P P' Q hq h ih =>
    cases h₂ with
    | @choiceL loc₂ μ₂ k₂ _ b₁ _ hq₂ h₂ =>
      obtain ⟨w₁, hw₁, hw₂⟩ := ih h₂ hc.of_cons hk
      exact ⟨.choice w₁ Q, .choiceL hq₂ hw₁, .choiceL hq hw₂⟩
    | @choiceR loc₂ μ₂ k₂ _ _ _ hp₂ h₂ =>
      exact (not_concurrent_choice (loc_ne_nil h) (loc_ne_nil h₂) hc).elim
  | @choiceR loc μ k P Q Q' hp h ih =>
    cases h₂ with
    | @choiceL loc₂ μ₂ k₂ _ _ _ hq₂ h₂ =>
      exact (not_concurrent_choice (loc_ne_nil h₂) (loc_ne_nil h) hc.symm).elim
    | @choiceR loc₂ μ₂ k₂ _ _ b₁ hp₂ h₂ =>
      obtain ⟨w₁, hw₁, hw₂⟩ := ih h₂ hc.of_cons hk
      exact ⟨.choice P w₁, .choiceR hp₂ hw₁, .choiceR hp hw₂⟩
  | @res loc μ k a P P' hn hcn h ih =>
    cases h₂ with
    | @res loc₂ μ₂ k₂ _ _ b₁ hn₂ hcn₂ h₂ =>
      obtain ⟨w₁, hw₁, hw₂⟩ := ih h₂ hc.of_cons hk
      exact ⟨.res a w₁, .res hn₂ hcn₂ hw₁, .res hn hcn hw₂⟩

/--
**Backward diamond.**  Two forward steps into the same state at concurrent
locations come from a common state.
-/
theorem square_bb {p a b : Proc Name} {α β : Lab Name}
    (h₁ : Tr a α p) (h₂ : Tr b β p)
    (hc : Concurrent α.loc β.loc) (hk : α.key ≠ β.key) :
    ∃ w, Tr w β a ∧ Tr w α b := by
  induction h₁ generalizing b β with
  | pre => exact absurd hc (not_concurrent_root (loc_ne_nil h₂))
  | @past μ μ' k k' loc a₀ p₀ hk₁ h ih =>
    cases h₂ with
    | pre hstd => exact absurd (hstd ▸ key_mem_keys h) (by simp)
    | @past _ μ₂ _ k₂ loc₂ b₀ _ hk₂ h₂ =>
      obtain ⟨w₀, hw₁, hw₂⟩ := ih h₂ hc.of_cons hk
      exact ⟨.preK μ k w₀, .past hk₂ hw₁, .past hk₁ hw₂⟩
  | @parL loc μ k a₁ p₁ q hq h ih =>
    cases h₂ with
    | @parL loc₂ μ₂ k₂ b₁ _ _ hq₂ h₂ =>
      obtain ⟨w₁, hw₁, hw₂⟩ := ih h₂ hc.of_cons hk
      exact ⟨.par w₁ q, .parL hq₂ hw₁, .parL hq hw₂⟩
    | @parR loc₂ μ₂ k₂ _ q₂ _ hp₂ h₂ =>
      exact ⟨.par a₁ q₂, .parR (not_mem_keys_of_target h hp₂) h₂,
        .parL (not_mem_keys_of_target h₂ hq) h⟩
    | @com locp₂ locq₂ μ₂ μ₂' k₂ b₂ _ c₂ _ hco₂ hpq₂ hqp₂ hp₂ hq₂ =>
      obtain ⟨w₁, hw₁, hw₂⟩ :=
        ih hp₂ (hc.symm.of_append_left.symm.of_cons) hk
      exact ⟨.par w₁ c₂,
        .com hco₂ (not_mem_keys_of_target hw₂ hpq₂) hqp₂ hw₁ hq₂,
        .parL (not_mem_keys_of_target hq₂ hq) hw₂⟩
  | @parR loc μ k p₁ q₂ q hp h ih =>
    cases h₂ with
    | @parL loc₂ μ₂ k₂ b₁ _ _ hq₂ h₂ =>
      exact ⟨.par b₁ q₂, .parL (not_mem_keys_of_target h hq₂) h₂,
        .parR (not_mem_keys_of_target h₂ hp) h⟩
    | @parR loc₂ μ₂ k₂ _ b₁ _ hp₂ h₂ =>
      obtain ⟨w₁, hw₁, hw₂⟩ := ih h₂ hc.of_cons hk
      exact ⟨.par p₁ w₁, .parR hp₂ hw₁, .parR hp hw₂⟩
    | @com locp₂ locq₂ μ₂ μ₂' k₂ b₂ _ c₂ _ hco₂ hpq₂ hqp₂ hp₂ hq₂ =>
      obtain ⟨w₁, hw₁, hw₂⟩ :=
        ih hq₂ (hc.symm.of_append_right.symm.of_cons) hk
      exact ⟨.par b₂ w₁,
        .com hco₂ hpq₂ (not_mem_keys_of_target hw₂ hqp₂) hp₂ hw₁,
        .parR (not_mem_keys_of_target hp₂ hp) hw₂⟩
  | @com locp locq μ μ' k P P' Q Q' hco hpq hqp hp hq ihp ihq =>
    cases h₂ with
    | @parL loc₂ μ₂ k₂ b₁ _ _ hq₂ h₂ =>
      obtain ⟨w₁, hw₁, hw₂⟩ := ihp h₂ (hc.of_append_left.of_cons) hk
      exact ⟨.par w₁ Q,
        .parL (not_mem_keys_of_target hq hq₂) hw₁,
        .com hco (not_mem_keys_of_target hw₁ hpq) hqp hw₂ hq⟩
    | @parR loc₂ μ₂ k₂ _ b₁ _ hp₂ h₂ =>
      obtain ⟨w₁, hw₁, hw₂⟩ := ihq h₂ (hc.of_append_right.of_cons) hk
      exact ⟨.par P w₁,
        .parR (not_mem_keys_of_target hp hp₂) hw₁,
        .com hco hpq (not_mem_keys_of_target hw₁ hqp) hp hw₂⟩
    | @com locp₂ locq₂ μ₂ μ₂' k₂ b₂ _ c₂ _ hco₂ hpq₂ hqp₂ hp₂ hq₂ =>
      obtain ⟨w₁, hw₁, hw₂⟩ :=
        ihp hp₂ (hc.of_append_left.symm.of_append_left.symm.of_cons) hk
      obtain ⟨w₂, hv₁, hv₂⟩ :=
        ihq hq₂ (hc.of_append_right.symm.of_append_right.symm.of_cons) hk
      exact ⟨.par w₁ w₂,
        .com hco₂ (not_mem_keys_of_target hw₂ hpq₂) (not_mem_keys_of_target hv₂ hqp₂) hw₁ hv₁,
        .com hco (not_mem_keys_of_target hw₁ hpq) (not_mem_keys_of_target hv₁ hqp) hw₂ hv₂⟩
  | @choiceL loc μ k a P' Q hq h ih =>
    cases h₂ with
    | @choiceL loc₂ μ₂ k₂ b₁ _ _ hq₂ h₂ =>
      obtain ⟨w₁, hw₁, hw₂⟩ := ih h₂ hc.of_cons hk
      exact ⟨.choice w₁ Q, .choiceL hq₂ hw₁, .choiceL hq hw₂⟩
    | @choiceR loc₂ μ₂ k₂ _ _ _ hp₂ h₂ =>
      exact (not_concurrent_choice (loc_ne_nil h) (loc_ne_nil h₂) hc).elim
  | @choiceR loc μ k P a Q' hp h ih =>
    cases h₂ with
    | @choiceL loc₂ μ₂ k₂ _ _ _ hq₂ h₂ =>
      exact (not_concurrent_choice (loc_ne_nil h₂) (loc_ne_nil h) hc.symm).elim
    | @choiceR loc₂ μ₂ k₂ _ b₁ _ hp₂ h₂ =>
      obtain ⟨w₁, hw₁, hw₂⟩ := ih h₂ hc.of_cons hk
      exact ⟨.choice P w₁, .choiceR hp₂ hw₁, .choiceR hp hw₂⟩
  | @res loc μ k a a₀ P' hn hcn h ih =>
    cases h₂ with
    | @res loc₂ μ₂ k₂ _ b₁ _ hn₂ hcn₂ h₂ =>
      obtain ⟨w₁, hw₁, hw₂⟩ := ih h₂ hc.of_cons hk
      exact ⟨.res a w₁, .res hn₂ hcn₂ hw₁, .res hn hcn hw₂⟩

/--
**Exchange.**  A step followed by a concurrent step can be taken in the other
order.
-/
theorem square_ex {p a b : Proc Name} {α β : Lab Name}
    (h₁ : Tr p α a) (h₂ : Tr b β p)
    (hc : Concurrent α.loc β.loc) (hk : α.key ≠ β.key) :
    ∃ w, Tr b α w ∧ Tr w β a := by
  induction h₁ generalizing b β with
  | pre => exact absurd hc (not_concurrent_root (loc_ne_nil h₂))
  | @past μ μ' k k' loc p₀ a₀ hk₁ h ih =>
    cases h₂ with
    | pre => exact absurd hc.symm (not_concurrent_root (by simpa using loc_ne_nil h))
    | @past _ μ₂ _ k₂ loc₂ b₀ _ hk₂ h₂ =>
      obtain ⟨w₀, hw₁, hw₂⟩ := ih h₂ hc.of_cons hk
      exact ⟨.preK μ k w₀, .past hk₁ hw₁, .past hk₂ hw₂⟩
  | @parL loc μ k p₁ p₁' q hq h ih =>
    cases h₂ with
    | @parL loc₂ μ₂ k₂ b₁ _ _ hq₂ h₂ =>
      obtain ⟨w₁, hw₁, hw₂⟩ := ih h₂ hc.of_cons hk
      exact ⟨.par w₁ q, .parL hq hw₁, .parL hq₂ hw₂⟩
    | @parR loc₂ μ₂ k₂ _ q₂ _ hp₂ h₂ =>
      exact ⟨.par p₁' q₂, .parL (not_mem_keys_of_target h₂ hq) h,
        .parR (not_mem_keys_of_step h (Ne.symm hk) hp₂) h₂⟩
    | @com locp₂ locq₂ μ₂ μ₂' k₂ b₂ _ c₂ _ hco₂ hpq₂ hqp₂ hp₂ hq₂ =>
      obtain ⟨w₁, hw₁, hw₂⟩ :=
        ih hp₂ (hc.symm.of_append_left.symm.of_cons) hk
      exact ⟨.par w₁ c₂,
        .parL (not_mem_keys_of_target hq₂ hq) hw₁,
        .com hco₂ (not_mem_keys_of_step hw₁ (Ne.symm hk) hpq₂) hqp₂ hw₂ hq₂⟩
  | @parR loc μ k p₁ q q' hp h ih =>
    cases h₂ with
    | @parL loc₂ μ₂ k₂ b₁ _ _ hq₂ h₂ =>
      exact ⟨.par b₁ q', .parR (not_mem_keys_of_target h₂ hp) h,
        .parL (not_mem_keys_of_step h (Ne.symm hk) hq₂) h₂⟩
    | @parR loc₂ μ₂ k₂ _ q₂ _ hp₂ h₂ =>
      obtain ⟨w₁, hw₁, hw₂⟩ := ih h₂ hc.of_cons hk
      exact ⟨.par p₁ w₁, .parR hp hw₁, .parR hp₂ hw₂⟩
    | @com locp₂ locq₂ μ₂ μ₂' k₂ b₂ _ c₂ _ hco₂ hpq₂ hqp₂ hp₂ hq₂ =>
      obtain ⟨w₁, hw₁, hw₂⟩ :=
        ih hq₂ (hc.symm.of_append_right.symm.of_cons) hk
      exact ⟨.par b₂ w₁,
        .parR (not_mem_keys_of_target hp₂ hp) hw₁,
        .com hco₂ hpq₂ (not_mem_keys_of_step hw₁ (Ne.symm hk) hqp₂) hp₂ hw₂⟩
  | @com locp locq μ μ' k P P' Q Q' hco hpq hqp hp hq ihp ihq =>
    cases h₂ with
    | @parL loc₂ μ₂ k₂ b₁ _ _ hq₂ h₂ =>
      obtain ⟨w₁, hw₁, hw₂⟩ := ihp h₂ (hc.of_append_left.of_cons) hk
      exact ⟨.par w₁ Q',
        .com hco (not_mem_keys_of_target h₂ hpq) hqp hw₁ hq,
        .parL (not_mem_keys_of_step hq (Ne.symm hk) hq₂) hw₂⟩
    | @parR loc₂ μ₂ k₂ _ b₁ _ hp₂ h₂ =>
      obtain ⟨w₁, hw₁, hw₂⟩ := ihq h₂ (hc.of_append_right.of_cons) hk
      exact ⟨.par P' w₁,
        .com hco hpq (not_mem_keys_of_target h₂ hqp) hp hw₁,
        .parR (not_mem_keys_of_step hp (Ne.symm hk) hp₂) hw₂⟩
    | @com locp₂ locq₂ μ₂ μ₂' k₂ b₂ _ c₂ _ hco₂ hpq₂ hqp₂ hp₂ hq₂ =>
      obtain ⟨w₁, hw₁, hw₂⟩ :=
        ihp hp₂ (hc.of_append_left.symm.of_append_left.symm.of_cons) hk
      obtain ⟨w₂, hv₁, hv₂⟩ :=
        ihq hq₂ (hc.of_append_right.symm.of_append_right.symm.of_cons) hk
      exact ⟨.par w₁ w₂,
        .com hco (not_mem_keys_of_target hp₂ hpq) (not_mem_keys_of_target hq₂ hqp) hw₁ hv₁,
        .com hco₂ (not_mem_keys_of_step hw₁ (Ne.symm hk) hpq₂)
          (not_mem_keys_of_step hv₁ (Ne.symm hk) hqp₂) hw₂ hv₂⟩
  | @choiceL loc μ k P P' Q hq h ih =>
    cases h₂ with
    | @choiceL loc₂ μ₂ k₂ b₁ _ _ hq₂ h₂ =>
      obtain ⟨w₁, hw₁, hw₂⟩ := ih h₂ hc.of_cons hk
      exact ⟨.choice w₁ Q, .choiceL hq hw₁, .choiceL hq₂ hw₂⟩
    | @choiceR loc₂ μ₂ k₂ _ _ _ hp₂ h₂ =>
      exact (not_concurrent_choice (loc_ne_nil h) (loc_ne_nil h₂) hc).elim
  | @choiceR loc μ k P Q Q' hp h ih =>
    cases h₂ with
    | @choiceL loc₂ μ₂ k₂ _ _ _ hq₂ h₂ =>
      exact (not_concurrent_choice (loc_ne_nil h₂) (loc_ne_nil h) hc.symm).elim
    | @choiceR loc₂ μ₂ k₂ _ b₁ _ hp₂ h₂ =>
      obtain ⟨w₁, hw₁, hw₂⟩ := ih h₂ hc.of_cons hk
      exact ⟨.choice P w₁, .choiceR hp hw₁, .choiceR hp₂ hw₂⟩
  | @res loc μ k a P P' hn hcn h ih =>
    cases h₂ with
    | @res loc₂ μ₂ k₂ _ b₁ _ hn₂ hcn₂ h₂ =>
      obtain ⟨w₁, hw₁, hw₂⟩ := ih h₂ hc.of_cons hk
      exact ⟨.res a w₁, .res hn hcn hw₁, .res hn₂ hcn₂ hw₂⟩

instance : SquareProperty (lts Name) (Indep (Name := Name)) where
  square {t u} htv huv hind := by
    obtain ⟨hco, hc, hk⟩ := hind
    cases hdt : t.dir <;> cases hdu : u.dir <;>
      rw [Transition.Valid, hdt] at htv <;> rw [Transition.Valid, hdu] at huv <;>
      rw [← hco] at huv
    · obtain ⟨w, hw₁, hw₂⟩ := square_ff htv huv hc hk
      exact ⟨w, hw₁, hw₂⟩
    · obtain ⟨w, hw₁, hw₂⟩ := square_ex htv huv hc hk
      exact ⟨w, hw₂, hw₁⟩
    · obtain ⟨w, hw₁, hw₂⟩ := square_ex huv htv hc.symm (Ne.symm hk)
      exact ⟨w, hw₁, hw₂⟩
    · obtain ⟨w, hw₁, hw₂⟩ := square_bb htv huv hc hk
      exact ⟨w, hw₁, hw₂⟩

/-! ## Stepping back -/

/--
All immediate predecessors of a process.

This is the step-back function of a reversible debugger, and it is total: the
rules that could have produced a given term are determined by the term.  The
side conditions reappear here as the filters — a prefix can only have been
executed if nothing beneath it has run, and a component can only have moved
under a key that is fresh for its sibling.
-/
def preds [DecidableEq Name] : Proc Name → List (Lab Name × Proc Name)
  | .nil => []
  | .pre _ _ => []
  | .preK μ k p =>
      (if keys p = [] then [(⟨[[]], μ, k⟩, Proc.pre μ p)] else []) ++
      (preds p).filterMap fun x =>
        if x.1.key = k then none
        else some (⟨x.1.loc.map (Step.past :: ·), x.1.act, x.1.key⟩, Proc.preK μ k x.2)
  | .par p q =>
      ((preds p).filterMap fun x =>
        if x.1.key ∈ keys q then none
        else some (⟨x.1.loc.map (Step.l :: ·), x.1.act, x.1.key⟩, Proc.par x.2 q)) ++
      ((preds q).filterMap fun x =>
        if x.1.key ∈ keys p then none
        else some (⟨x.1.loc.map (Step.r :: ·), x.1.act, x.1.key⟩, Proc.par p x.2)) ++
      ((preds p).flatMap fun x => (preds q).filterMap fun y =>
        if x.1.key = y.1.key ∧ Act.isCo x.1.act y.1.act = true ∧
            x.1.key ∉ keys x.2 ∧ x.1.key ∉ keys y.2 then
          some (⟨x.1.loc.map (Step.l :: ·) ++ y.1.loc.map (Step.r :: ·), Act.τ, x.1.key⟩,
            Proc.par x.2 y.2)
        else none)
  | .choice p q =>
      (if keys q = [] then (preds p).map fun x =>
        (⟨x.1.loc.map (Step.cl :: ·), x.1.act, x.1.key⟩, Proc.choice x.2 q) else []) ++
      (if keys p = [] then (preds q).map fun x =>
        (⟨x.1.loc.map (Step.cr :: ·), x.1.act, x.1.key⟩, Proc.choice p x.2) else [])
  | .res a p =>
      (preds p).filterMap fun x =>
        if x.1.act = Act.name a ∨ x.1.act = Act.coname a then none
        else some (⟨x.1.loc.map (Step.res :: ·), x.1.act, x.1.key⟩, Proc.res a x.2)

/-- Everything `preds` produces really is a step into the given process. -/
theorem tr_of_mem_preds [DecidableEq Name] : ∀ {p : Proc Name} {α : Lab Name} {q : Proc Name},
    (α, q) ∈ preds p → Tr q α p
  | .preK μ k p, α, q, h => by
    rcases List.mem_append.mp h with h | h
    · split at h
      · rcases List.mem_singleton.mp h with ⟨⟩
        exact Tr.pre ‹keys p = []›
      · exact absurd h (List.not_mem_nil)
    · obtain ⟨y, hy, hf⟩ := List.mem_filterMap.mp h
      split at hf
      · exact absurd hf (by simp)
      · obtain ⟨⟩ := Option.some.inj hf
        exact Tr.past ‹¬ y.1.key = k› (tr_of_mem_preds hy)
  | .par p q, α, r, h => by
    rcases List.mem_append.mp h with h | h
    · rcases List.mem_append.mp h with h | h <;>
        obtain ⟨y, hy, hf⟩ := List.mem_filterMap.mp h <;> split at hf
      · exact absurd hf (by simp)
      · obtain ⟨⟩ := Option.some.inj hf
        exact Tr.parL ‹¬ y.1.key ∈ keys q› (tr_of_mem_preds hy)
      · exact absurd hf (by simp)
      · obtain ⟨⟩ := Option.some.inj hf
        exact Tr.parR ‹¬ y.1.key ∈ keys p› (tr_of_mem_preds hy)
    · obtain ⟨x, hx, h⟩ := List.mem_flatMap.mp h
      obtain ⟨y, hy, hf⟩ := List.mem_filterMap.mp h
      split at hf
      · rename_i hcond
        obtain ⟨hkeq, hco, hfp, hfq⟩ := hcond
        have he := Option.some.inj hf
        have hlab := congrArg Prod.fst he
        have hpr := congrArg Prod.snd he
        simp only at hlab hpr
        subst hlab; subst hpr
        refine Tr.com (Act.isCo_iff.mp hco) hfp hfq (tr_of_mem_preds hx) ?_
        rw [hkeq]
        exact tr_of_mem_preds hy
      · exact absurd hf (by simp)
  | .choice p q, α, r, h => by
    rcases List.mem_append.mp h with h | h <;> split at h
    · obtain ⟨y, hy, hf⟩ := List.mem_map.mp h
      have hlab := congrArg Prod.fst hf
      have hpr := congrArg Prod.snd hf
      simp only at hlab hpr
      subst hlab; subst hpr
      exact Tr.choiceL ‹keys q = []› (tr_of_mem_preds hy)
    · exact absurd h List.not_mem_nil
    · obtain ⟨y, hy, hf⟩ := List.mem_map.mp h
      have hlab := congrArg Prod.fst hf
      have hpr := congrArg Prod.snd hf
      simp only at hlab hpr
      subst hlab; subst hpr
      exact Tr.choiceR ‹keys p = []› (tr_of_mem_preds hy)
    · exact absurd h List.not_mem_nil
  | .res a p, α, r, h => by
    obtain ⟨y, hy, hf⟩ := List.mem_filterMap.mp h
    split at hf
    · exact absurd hf (by simp)
    · rename_i hcond
      have he := Option.some.inj hf
      have hlab := congrArg Prod.fst he
      have hpr := congrArg Prod.snd he
      simp only at hlab hpr
      subst hlab; subst hpr
      exact Tr.res (fun h' => hcond (Or.inl h')) (fun h' => hcond (Or.inr h'))
        (tr_of_mem_preds hy)

/-- Every step into a process is found by `preds`. -/
theorem mem_preds_of_tr [DecidableEq Name] {p q : Proc Name} {α : Lab Name} (h : Tr q α p) :
    (α, q) ∈ preds p := by
  induction h with
  | @pre μ k p hstd =>
    exact List.mem_append_left _ (by simp [hstd])
  | @past μ μ' k k' loc p p' hk h ih =>
    refine List.mem_append_right _ (List.mem_filterMap.mpr ⟨(⟨loc, μ', k'⟩, p), ih, ?_⟩)
    simp [hk]
  | @parL loc μ k p p' q hq h ih =>
    refine List.mem_append_left _ (List.mem_append_left _
      (List.mem_filterMap.mpr ⟨(⟨loc, μ, k⟩, p), ih, ?_⟩))
    simp [hq]
  | @parR loc μ k p q q' hp h ih =>
    refine List.mem_append_left _ (List.mem_append_right _
      (List.mem_filterMap.mpr ⟨(⟨loc, μ, k⟩, q), ih, ?_⟩))
    simp [hp]
  | @com locp locq μ μ' k p p' q q' hco hpq hqp hp hq ihp ihq =>
    refine List.mem_append_right _ (List.mem_flatMap.mpr
      ⟨(⟨locp, μ, k⟩, p), ihp, List.mem_filterMap.mpr ⟨(⟨locq, μ', k⟩, q), ihq, ?_⟩⟩)
    simp [Act.isCo_iff.mpr hco, hpq, hqp]
  | @choiceL loc μ k p p' q hq h ih =>
    refine List.mem_append_left _ ?_
    rw [if_pos hq]
    exact List.mem_map.mpr ⟨(⟨loc, μ, k⟩, p), ih, rfl⟩
  | @choiceR loc μ k p q q' hp h ih =>
    refine List.mem_append_right _ ?_
    rw [if_pos hp]
    exact List.mem_map.mpr ⟨(⟨loc, μ, k⟩, q), ih, rfl⟩
  | @res loc μ k a p p' hn hcn h ih =>
    refine List.mem_filterMap.mpr ⟨(⟨loc, μ, k⟩, p), ih, ?_⟩
    rw [if_neg (by rintro (he | he) <;> simp_all)]

instance [DecidableEq Name] : BStepDec (lts Name) where
  step p :=
    match hp : preds p with
    | [] => .inr fun q hq => by
        obtain ⟨t, hv, hb, hs, ht⟩ := hq
        subst hs; subst ht
        rw [Transition.Valid, hb] at hv
        exact absurd (hp ▸ mem_preds_of_tr hv) (List.not_mem_nil)
    | x :: _ => .inl ⟨x.2, ⟨Transition.mk p x.1 .bwd x.2,
        tr_of_mem_preds (hp ▸ List.mem_cons_self ..), rfl, rfl, rfl⟩⟩

/-! ## What CCSK inherits -/

section Inherited

/--
**The Parabolic Lemma for CCSK.**  Every computation is causally equivalent to
one that undoes and then redoes.

Nothing about CCSK is used in the proof; it is the general theorem applied to
the instance above.
-/
theorem parabolic_ccsk [DecidableEq Name] {l : List (Transition (Proc Name) (Lab Name))}
    {p q : Proc Name}
    (hc : Chained (lts Name) p l q) :
    ∃ lb lf, (∀ x ∈ lb, x.IsBwd) ∧ (∀ x ∈ lf, x.IsFwd) ∧
      CEq (lts Name) Indep p q l (lb ++ lf) :=
  parabolic (Indep := Indep) hc

/-- **Undoing is confluent for CCSK.** -/
theorem bstep_diamond_ccsk [DecidableEq Name] {p q₁ q₂ : Proc Name}
    (h₁ : BStep (lts Name) p q₁) (h₂ : BStep (lts Name) p q₂) :
    q₁ = q₂ ∨ ∃ w, BStep (lts Name) q₁ w ∧ BStep (lts Name) q₂ w :=
  bstep_diamond (Indep := Indep) h₁ h₂

/--
**Causal consistency for CCSK.**  Two computations with the same endpoints are
causally equivalent.

This is the theorem the axiomatic theory exists to prove, and here it is
obtained for a calculus we did not design without a single argument about
CCSK.
-/
theorem causal_consistency_ccsk [DecidableEq Name] {p q : Proc Name}
    {l₁ l₂ : List (Transition (Proc Name) (Lab Name))}
    (h₁ : Chained (lts Name) p l₁ q) (h₂ : Chained (lts Name) p l₂ q) :
    CEq (lts Name) Indep p q l₁ l₂ :=
  causal_consistency (Indep := Indep) h₁ h₂

/-- **However a CCSK process is rewound, the origin reached is the same.** -/
theorem unique_origin_ccsk [DecidableEq Name] {p o₁ o₂ : Proc Name}
    (h₁ : Relation.ReflTransGen (BStep (lts Name)) p o₁) (ho₁ : Origin (lts Name) o₁)
    (h₂ : Relation.ReflTransGen (BStep (lts Name)) p o₂) (ho₂ : Origin (lts Name) o₂) :
    o₁ = o₂ :=
  unique_origin (Indep := Indep) h₁ ho₁ h₂ ho₂

/-- Every CCSK process can be rewound to a process with nothing left to undo. -/
theorem exists_origin_ccsk [DecidableEq Name] (p : Proc Name) :
    ∃ o, Relation.ReflTransGen (BStep (lts Name)) p o ∧ Origin (lts Name) o :=
  exists_origin p

/--
**Partial-order reduction is sound for CCSK.**  Mazurkiewicz-equivalent label
sequences relate the same processes.

This one arrives through the forward half of the theory, which never mentions
reversibility: the `Exchange` instance is derived from the Square Property
proved above.
-/
theorem por_ccsk {w w' : List (Lab Name)} {p q : Proc Name}
    (h : MEq (LIndep (Indep (Name := Name))) w w') (hr : FRun (lts Name) p w q) :
    FRun (lts Name) p w' q :=
  FRun.of_mequiv h hr

end Inherited

/-! ## The instance is not vacuous -/

section Examples

variable {a b : Act Name}

/-- `a.b.0` executes `a`, marking it with key `0`. -/
example : Tr (.pre a (.pre b .nil)) ⟨[[]], a, 0⟩ (.preK a 0 (.pre b .nil)) := .pre rfl

/-- and then executes `b` underneath the executed prefix. -/
example : Tr (.preK a 0 (.pre b .nil)) ⟨[[Step.past]], b, 1⟩ (.preK a 0 (.preK b 1 .nil)) :=
  .past (by decide) (.pre rfl)

/-- Undoing is the converse, so it needs no rule of its own. -/
example : (Transition.mk (.preK a 0 (.pre b .nil)) ⟨[[]], a, 0⟩ .bwd (.pre a (.pre b .nil))).Valid
    (lts Name) := Tr.pre rfl

/-- The two sides of `a.0 | b.0` act at concurrent locations, so they are independent. -/
example :
    Indep (Name := Name)
      ⟨.par (.pre a .nil) (.pre b .nil), ⟨[[Step.l]], a, 0⟩, .fwd,
        .par (.preK a 0 .nil) (.pre b .nil)⟩
      ⟨.par (.pre a .nil) (.pre b .nil), ⟨[[Step.r]], b, 1⟩, .fwd,
        .par (.pre a .nil) (.preK b 1 .nil)⟩ :=
  ⟨rfl, by simpa [Concurrent] using Sep.of_par (by simp) [] [], by simp⟩

/-- Both of those transitions really are transitions. -/
example : Tr (.par (.pre a .nil) (.pre b .nil)) ⟨[[Step.l]], a, 0⟩
    (.par (.preK a 0 .nil) (.pre b .nil)) :=
  .parL (by simp [keys]) (.pre rfl)

/-- Nested locations are *not* concurrent: this is what BTI would fail on. -/
example : ¬ Concurrent [[]] [[Step.past]] := not_concurrent_root (by simp)

/--
The two branches of a choice are in *conflict*, not concurrent.

This is the case a prefix-based definition of separateness would get wrong,
and getting it wrong would make the Square Property false: after the left
branch has acted, the right branch can no longer act at all.
-/
example : ¬ Sep [Step.cl] [Step.cr] := not_sep_choice

/-- Restriction does not branch, so paths under it stay comparable. -/
example : ¬ Sep [Step.res] [Step.res] := by
  rintro (⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩) <;> simp_all [not_sep_nil]

end Examples

end Cslib.LTS.CCSK







