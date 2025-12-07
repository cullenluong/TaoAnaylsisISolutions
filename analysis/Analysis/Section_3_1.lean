import Mathlib.Tactic

/-!
# Analysis I, Section 3.1: Fundamentals (of set theory)

In this section we set up a version of Zermelo-Frankel set theory (with atoms) that tries to be
as faithful as possible to the original text of Analysis I, Section 3.1. All numbering refers to
the original text.

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- A type `Chapter3.SetTheory.Set` of sets
- A type `Chapter3.SetTheory.Object` of objects
- An axiom that every set is (or can be coerced into) an object
- The empty set `∅`, singletons `{y}`, and pairs `{y,z}` (and more general finite tuples), with
  their attendant axioms
- Pairwise union `X ∪ Y`, and their attendant axioms
- Coercion of a set `A` to its associated type `A.toSubtype`, which is a subtype of `Object`, and
  basic API.  (This is a technical construction needed to make the Zermelo-Frankel set theory
  compatible with the dependent type theory of Lean.)
- The specification `A.specify P` of a set `A` and a predicate `P: A.toSubtype → Prop` to the
  subset of elements of `A` obeying `P`, and the axiom of specification.
  TODO: somehow implement set builder elaboration for this.
- The replacement `A.replace hP` of a set `A` via a predicate
  `P: A.toSubtype → Object → Prop` obeying a uniqueness condition
  `∀ x y y', P x y ∧ P x y' → y = y'`, and the axiom of replacement.
- A bijective correspondence between the Mathlib natural numbers `ℕ` and a set
  `Chapter3.Nat : Chapter3.Set` (the axiom of infinity).
- Axioms of regularity, power set, and union (used in later sections of this chapter, but not
  required here)
- Connections with Mathlib's notion of a set

The other axioms of Zermelo-Frankel set theory are discussed in later sections.

Some technical notes:
- Mathlib of course has its own notion of a `Set` (or more precisely, a type `Set X` associated to
  each type `X`), which is not compatible with the notion `Chapter3.Set` defined here,
  though we will try to make the notations match as much as possible.  This causes some notational
  conflict: for instance, one may need to explicitly specify `(∅:Chapter3.Set)` instead of just `∅`
  to indicate that one is using the `Chapter3.Set` version of the empty set, rather than the
  Mathlib version of the empty set, and similarly for other notation defined here.
- In Analysis I, we chose to work with an "impure" set theory, in which there could be more
  `Object`s than just `Set`s.  In the type theory of Lean, this requires treating `Chapter3.Set`
  and `Chapter3.Object` as distinct types. Occasionally this means we have to use a coercion
  `(X: Chapter3.Object)` of a `Chapter3.Set` `X` to make into a `Chapter3.Object`: this is
  mostly needed when manipulating sets of sets.
- Strictly speaking, a set `X:Set` is not a type; however, we will coerce sets to types, and
  specifically to a subtype of `Object`.  A similar coercion is in place for Mathlib's
  formalization of sets.
- After this chapter is concluded, the notion of a `Chapter3.SetTheory.Set` will be deprecated in
  favor of the standard Mathlib notion of a `Set` (or more precisely of the type `Set X` of a set
  in a given type `X`).  However, due to various technical incompatibilities between set theory
  and type theory, we will not attempt to create a full equivalence between these two
  notions of sets. (As such, this makes this entire chapter optional from the point of view of
  the rest of the book, though we retain it for pedagogical purposes.)

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)
-/

namespace Chapter3

/- The ability to work in multiple universe is not relevant immediately, but
becomes relevant when constructing models of set theory in the Chapter 3 epilogue. -/
universe u v

/-- The axioms of Zermelo-Frankel theory with atoms.  -/
class SetTheory where
  Set : Type u -- Axiom 3.1
  Object : Type v -- Axiom 3.1
  set_to_object : Set ↪ Object -- Axiom 3.1
  mem : Object → Set → Prop -- Axiom 3.1
  extensionality X Y : (∀ x, mem x X ↔ mem x Y) → X = Y -- Axiom 3.2
  emptyset: Set -- Axiom 3.3
  emptyset_mem x : ¬ mem x emptyset -- Axiom 3.3
  singleton : Object → Set -- Axiom 3.4
  singleton_axiom x y : mem x (singleton y) ↔ x = y -- Axiom 3.4
  union_pair : Set → Set → Set -- Axiom 3.5
  union_pair_axiom X Y x : mem x (union_pair X Y) ↔ (mem x X ∨ mem x Y) -- Axiom 3.5
  specify A (P: Subtype (mem . A) → Prop) : Set -- Axiom 3.6
  specification_axiom A (P: Subtype (mem . A) → Prop) :
    (∀ x, mem x (specify A P) → mem x A) ∧ ∀ x, mem x.val (specify A P) ↔ P x -- Axiom 3.6
  replace A (P: Subtype (mem . A) → Object → Prop)
    (hP: ∀ x y y', P x y ∧ P x y' → y = y') : Set -- Axiom 3.7
  replacement_axiom A (P: Subtype (mem . A) → Object → Prop)
    (hP: ∀ x y y', P x y ∧ P x y' → y = y') : ∀ y, mem y (replace A P hP) ↔ ∃ x, P x y -- Axiom 3.7
  nat : Set -- Axiom 3.8
  nat_equiv : ℕ ≃ Subtype (mem . nat) -- Axiom 3.8
  regularity_axiom A (hA : ∃ x, mem x A) :
    ∃ x, mem x A ∧ ∀ S, x = set_to_object S → ¬ ∃ y, mem y A ∧ mem y S -- Axiom 3.9
  pow : Set → Set → Set -- Axiom 3.11
  function_to_object (X: Set) (Y: Set) :
    (Subtype (mem . X) → Subtype (mem . Y)) ↪ Object -- Axiom 3.11
  powerset_axiom (X: Set) (Y: Set) (F:Object) :
    mem F (pow X Y) ↔ ∃ f: Subtype (mem . Y) → Subtype (mem . X),
    function_to_object Y X f = F -- Axiom 3.11
  union : Set → Set -- Axiom 3.12
  union_axiom A x : mem x (union A) ↔ ∃ S, mem x S ∧ mem (set_to_object S) A -- Axiom 3.12

-- This enables one to use `Set` and `Object` instead of `SetTheory.Set` and `SetTheory.Object`.
export SetTheory (Set Object)

-- This instance implicitly imposes the axioms of Zermelo-Frankel set theory with atoms.
variable [SetTheory]

/-- Definition 3.1.1 (objects can be elements of sets) -/
instance SetTheory.objects_mem_sets : Membership Object Set where
  mem X x := mem x X

-- Now we can use the `∈` notation between our `Object` and `Set`.
example (X: Set) (x: Object) : x ∈ X ↔ SetTheory.mem x X := by rfl

/-- Axiom 3.1 (Sets are objects)-/
instance SetTheory.sets_are_objects : Coe Set Object where
  coe X := set_to_object X

-- Now we can treat a `Set` as an `Object` when needed.
example (X: Set) : (X: Object) = SetTheory.set_to_object X := rfl

/-- Axiom 3.1 (Sets are objects)-/
theorem SetTheory.Set.coe_eq {X Y:Set} (h: (X: Object) = (Y: Object)) : X = Y :=
  set_to_object.inj' h

/-- Axiom 3.1 (Sets are objects)-/
@[simp]
theorem SetTheory.Set.coe_eq_iff (X Y:Set) : (X: Object) = (Y: Object) ↔  X = Y :=
  ⟨ coe_eq, by rintro rfl; rfl ⟩

/-- Axiom 3.2 (Equality of sets).  The `[ext]` tag allows the `ext` tactic to work for sets. -/
@[ext]
theorem SetTheory.Set.ext {X Y:Set} (h: ∀ x, x ∈ X ↔ x ∈ Y) : X = Y := extensionality _ _ h

/- Axiom 3.2 (Equality of sets)-/
#check SetTheory.Set.ext_iff

instance SetTheory.Set.instEmpty : EmptyCollection Set where
  emptyCollection := emptyset

-- Now we can use the `∅` notation to refer to `SetTheory.emptyset`.
example : ∅ = SetTheory.emptyset := rfl

-- Make everything we define in `SetTheory.Set.*` accessible directly.
open SetTheory.Set

/--
  Axiom 3.3 (empty set).
  Note: in some applications one may have to explicitly cast ∅ to Set due to
  Mathlib's existing set theory notation.
-/
@[simp]
theorem SetTheory.Set.not_mem_empty : ∀ x, x ∉ (∅:Set) := emptyset_mem

/-- Empty set has no elements -/
theorem SetTheory.Set.eq_empty_iff_forall_notMem {X:Set} : X = ∅ ↔ (∀ x, x ∉ X) := by
  constructor
  · intro h x
    simp[SetTheory.Set.ext_iff] at *
    -- tauto works but I want to how it works
    simp[h]
  · intro h
    simpa[SetTheory.Set.ext_iff]





/-- Empty set is unique -/
theorem SetTheory.Set.empty_unique : ∃! (X:Set), ∀ x, x ∉ X := by
  refine ⟨(∅ : Set), ?hEmpty, ?uniq⟩
  -- ⊢ (fun X ↦ ∀ (x : Object), x ∉ X) ∅
  -- ⊢ ∀ (y : Set), (fun X ↦ ∀ (x : Object), x ∉ X) y → y = ∅
  -- We show that the empty set exists (which is trivial by the axiom)
  -- We show that it is unique
  · -- ⊢ (fun X ↦ ∀ (x : Object), x ∉ X) ∅
    -- there  exists a function that sends the set X and the output is that for any object x, x is not the
    intro x
    apply not_mem_empty
  · -- If `Y` has no elements, then `Y = ∅` by extensionality
    -- ⊢ ∀ (y : Set), (fun X ↦ ∀ (x : Object), x ∉ X) y → y = ∅
    -- for any
    intro Y hY
    apply SetTheory.Set.ext
    intro x
    constructor
    · intro hx
      exact False.elim (hY x hx)
    · intro hxEmpty
      exact False.elim ((SetTheory.Set.not_mem_empty x) hxEmpty)


private theorem SetTheory.Set.empty_unique_com : ∃! (X:Set), ∀ x, x ∉ X := by
  apply existsUnique_of_exists_of_unique

-- inst✝ : SetTheory
-- ⊢ ∃ x, ∀ (x_1 : Object), x_1 ∉ x
-- case hunique
-- inst✝ : SetTheory
-- ⊢ ∀ (y₁ y₂ : Set), (∀ (x : Object), x ∉ y₁) → (∀ (x : Object), x ∉ y₂) → y₁ = y₂


  . use SetTheory.emptyset
    exact SetTheory.emptyset_mem
  . intro x y hx hy
    have hxz := eq_empty_iff_forall_notMem.mpr hx
    have hyz := eq_empty_iff_forall_notMem.mpr hy
    simp [hxz, hyz]


/-- Lemma 3.1.5 (Single choice) -/
lemma SetTheory.Set.nonempty_def {X:Set} (h: X ≠ ∅) : ∃ x, x ∈ X := by
  -- This proof is written to follow the structure of the original text.
  by_contra! this
  have claim (x:Object) : x ∈ X ↔ x ∈ (∅:Set) := by simp [this, not_mem_empty]
  apply ext at claim
  contradiction

theorem SetTheory.Set.nonempty_of_inhabited {X:Set} {x:Object} (h:x ∈ X) : X ≠ ∅ := by
  contrapose! h
  rw [eq_empty_iff_forall_notMem] at h
  exact h x

instance SetTheory.Set.instSingleton : Singleton Object Set where
  singleton := singleton

-- Now we can use the `{x}` notation for a single element `Set`.
example (x: Object) : {x} = SetTheory.singleton x := rfl

/--
  Axiom 3.3(a) (singleton).
  Note: in some applications one may have to explicitly cast {a} to Set due to Mathlib's
  existing set theory notation.
-/
@[simp]
theorem SetTheory.Set.mem_singleton (x a:Object) : x ∈ ({a}:Set) ↔ x = a := singleton_axiom x a


instance SetTheory.Set.instUnion : Union Set where
  union := union_pair

-- Now we can use the `X ∪ Y` notation for a union of two `Set`s.
example (X Y: Set) : X ∪ Y = SetTheory.union_pair X Y := rfl

/-- Axiom 3.4 (Pairwise union)-/
@[simp]
theorem SetTheory.Set.mem_union (x:Object) (X Y:Set) : x ∈ (X ∪ Y) ↔ (x ∈ X ∨ x ∈ Y) :=
  union_pair_axiom X Y x

instance SetTheory.Set.instInsert : Insert Object Set where
  insert x X := {x} ∪ X

@[simp]
theorem SetTheory.Set.mem_insert (a b: Object) (X: Set) : a ∈ insert b X ↔ a = b ∨ a ∈ X := by
  simp [instInsert]

/-- Axiom 3.3(b) (pair).  Note: in some applications one may have to cast {a,b}
    to Set. -/
theorem SetTheory.Set.pair_eq (a b:Object) : ({a,b}:Set) = {a} ∪ {b} := by rfl

/-- Axiom 3.3(b) (pair).  Note: in some applications one may have to cast {a,b}
    to Set. -/
@[simp]
theorem SetTheory.Set.mem_pair (x a b:Object) : x ∈ ({a,b}:Set) ↔ (x = a ∨ x = b) := by
  simp [pair_eq, mem_union, mem_singleton]

@[simp]
theorem SetTheory.Set.mem_triple (x a b c:Object) : x ∈ ({a,b,c}:Set) ↔ (x = a ∨ x = b ∨ x = c) := by
  simp [Insert.insert, mem_union, mem_singleton]

/-- Remark 3.1.9 -/
theorem SetTheory.Set.singleton_uniq (a:Object) : ∃! (X:Set), ∀ x, x ∈ X ↔ x = a := by
  --For some object a, There exists a unique set X such that for any object x that is a member of X iff x = a
  -- Existence: take `X = {a}`.
  refine ⟨({a} : Set), ?hX, ?uniq⟩
  · -- Show `{a}` has exactly the elements equal to `a`.
    intro x
    simp[(SetTheory.Set.mem_singleton x a)]
  · -- Uniqueness: any `Y` with the same membership characterization equals `{a}` by extensionality.
    intro Y hY
    apply SetTheory.Set.ext
    intro x
    have hy : x ∈ Y ↔ x = a := hY x
    have hx : x ∈ ({a} : Set) ↔ x = a := SetTheory.Set.mem_singleton x a
    -- Both sides characterize membership by `x = a`, so the sets are extensionally equal.
    exact hy.trans hx.symm


--https://github.com/gaearon/analysis-solutions/blob/solutions/analysis/Analysis/Section_3_1.lean

private theorem SetTheory.Set.singleton_uniq_gaeron (a:Object) : ∃! (X:Set), ∀ x, x ∈ X ↔ x = a := by
  apply existsUnique_of_exists_of_unique
  · use {a}
    intro x
    apply mem_singleton
  intro e1 e2 h1 h2
  ext x
  simp[h1 x, h2 x]


/-- Remark 3.1.9 -/
theorem SetTheory.Set.pair_uniq (a b:Object) : ∃! (X:Set), ∀ x, x ∈ X ↔ x = a ∨ x = b := by
  apply existsUnique_of_exists_of_unique
  · use {a, b}
    intro x
    apply mem_pair
  intro e1 e2 h1 h2
  ext x
  simp [h1 x, h2 x]





/-- Remark 3.1.9 -/
theorem SetTheory.Set.pair_comm (a b:Object) : ({a,b}:Set) = {b,a} := by
  ext x
  simp_all only [mem_insert, mem_singleton]
  apply Iff.intro
  · intro hxab
    cases hxab with
    | inl hxa =>
      subst hxa
      simp_all only [or_true]
    | inr hxb =>
      subst hxb
      simp_all only [true_or]
  · intro hxba
    cases hxba with
    | inl hxb =>
      subst hxb
      simp_all only [or_true]
    | inr hxa =>
      subst hxa
      simp_all only [true_or]

/-- Remark 3.1.9 -/
@[simp]
theorem SetTheory.Set.pair_self (a:Object) : ({a,a}:Set) = {a} := by
  aesop?

/-- Exercise 3.1.1 -/
theorem SetTheory.Set.pair_eq_pair {a b c d:Object} (h: ({a,b}:Set) = {c,d}) :
    a = c ∧ b = d ∨ a = d ∧ b = c := by
  --simp_all[pair_comm]
  simp only [Set.ext_iff] at h
  simp_all only [mem_insert, mem_singleton]
  have hacd : a = c ∨ a = d := by
    specialize h a
    simp only [true_or, true_iff] at h
    exact h
  have hbcd : b = c ∨ b = d := by
    specialize h b
    simp only [ or_true, true_iff] at h
    exact h
  have hcab : c = a ∨ c = b := by
    specialize h c
    simp only [true_or, iff_true] at h
    exact h
  have hdab : d = a ∨ d = b := by
    specialize h d
    simp only [ or_true, iff_true] at h
    exact h
  aesop?
abbrev SetTheory.Set.empty : Set := ∅
abbrev SetTheory.Set.singleton_empty : Set := {(empty: Object)}
abbrev SetTheory.Set.pair_empty : Set := {(empty: Object), (singleton_empty: Object)}

/-- Exercise 3.1.2 -/
theorem SetTheory.Set.emptyset_neq_singleton : empty ≠ singleton_empty := by
  simp only [empty,singleton_empty]
  symm
  simp[Set.ext_iff]




/-- Exercise 3.1.2 -/
theorem SetTheory.Set.emptyset_neq_pair : empty ≠ pair_empty := by
  simp[empty,pair_empty]
  push_neg
  symm
  simp[Set.ext_iff,not_mem_empty]
  apply Exists.intro
  · intro a
    rfl




/-- Exercise 3.1.2 -/
theorem SetTheory.Set.singleton_empty_neq_pair : singleton_empty ≠ pair_empty := by
  simp[empty,singleton_empty,pair_empty]
  simp[Set.ext_iff]


/--
  Remark 3.1.11.
  (These results can be proven either by a direct rewrite, or by using extensionality.)
-/
theorem SetTheory.Set.union_congr_left (A A' B:Set) (h: A = A') : A ∪ B = A' ∪ B := by
  ext x
  simp[mem_union]
  subst h
  simp_all only

/--
  Remark 3.1.11.
  (These results can be proven either by a direct rewrite, or by using extensionality.)
-/
theorem SetTheory.Set.union_congr_right (A B B':Set) (h: B = B') : A ∪ B = A ∪ B' := by
  ext x
  simp only [mem_union]
  subst h
  simp_all only

/-- Lemma 3.1.12 (Basic properties of unions) / Exercise 3.1.3 -/
theorem SetTheory.Set.singleton_union_singleton (a b:Object) :
    ({a}:Set) ∪ ({b}:Set) = {a,b} := by
  ext x
  simp only [mem_union, mem_singleton, mem_insert]

/-- Lemma 3.1.12 (Basic properties of unions) / Exercise 3.1.3 -/
theorem SetTheory.Set.union_comm (A B:Set) : A ∪ B = B ∪ A := by
  ext x
  simp[mem_union]
  apply Iff.intro
  · intro a
    cases a with
    | inl h => simp_all only [or_true]
    | inr h_1 => simp_all only [true_or]
  · intro a
    cases a with
    | inl h => simp_all only [or_true]
    | inr h_1 => simp_all only [true_or]

/-- Lemma 3.1.12 (Basic properties of unions) / Exercise 3.1.3 -/
theorem SetTheory.Set.union_assoc (A B C:Set) : (A ∪ B) ∪ C = A ∪ (B ∪ C) := by
  -- this proof is written to follow the structure of the original text.
  ext x
  constructor
  . intro hx; rw [mem_union] at hx
    obtain case1 | case2 := hx
    . rw [mem_union] at case1
      obtain case1a | case1b := case1
      . rw [mem_union]; tauto
      have : x ∈ B ∪ C := by rw [mem_union]; tauto
      rw [mem_union]; tauto
    have : x ∈ B ∪ C := by rw [mem_union]; tauto
    rw [mem_union]; tauto
  intro h
  simp_all[mem_union]
  cases h with
  | inl h_1 => simp_all only [true_or]
  | inr h_2 =>
    cases h_2 with
    | inl h => simp_all only [or_true, true_or]
    | inr h_1 => simp_all only [or_true]


/-- Proposition 3.1.27(c) -/
@[simp]
theorem SetTheory.Set.union_self (A:Set) : A ∪ A = A := by
  ext x
  simp only [mem_union, or_self]

/-- Proposition 3.1.27(a) -/
@[simp]
theorem SetTheory.Set.union_empty (A:Set) : A ∪ ∅ = A := by
  ext x
  simp only [mem_union, not_mem_empty, or_false]

/-- Proposition 3.1.27(a) -/
@[simp]
theorem SetTheory.Set.empty_union (A:Set) : ∅ ∪ A = A := by
  ext x
  simp only [mem_union, not_mem_empty, false_or]

theorem SetTheory.Set.triple_eq (a b c:Object) : {a,b,c} = ({a}:Set) ∪ {b,c} := by
  rfl

/-- Example 3.1.10 -/
theorem SetTheory.Set.pair_union_pair (a b c:Object) :
    ({a,b}:Set) ∪ {b,c} = {a,b,c} := by
  ext; simp only [mem_union, mem_pair, mem_triple]; tauto

/-- Definition 3.1.14.   -/
instance SetTheory.Set.instSubset : HasSubset Set where
  Subset X Y := ∀ x, x ∈ X → x ∈ Y

-- Now we can use `⊆` for a subset relationship between two `Set`s.
example (X Y: Set) : X ⊆ Y ↔ ∀ x, x ∈ X → x ∈ Y := by rfl

/--
  Definition 3.1.14.
  Note that the strict subset operation in Mathlib is denoted `⊂` rather than `⊊`.
-/
instance SetTheory.Set.instSSubset : HasSSubset Set where
  SSubset X Y := X ⊆ Y ∧ X ≠ Y

-- Now we can use `⊂` for a strict subset relationship between two `Set`s.
example (X Y: Set) : X ⊂ Y ↔ X ⊆ Y ∧ X ≠ Y := by rfl

/-- Definition 3.1.14. -/
theorem SetTheory.Set.subset_def (X Y:Set) : X ⊆ Y ↔ ∀ x, x ∈ X → x ∈ Y := by rfl

/--
  Definition 3.1.14.
  Note that the strict subset operation in Mathlib is denoted `⊂` rather than `⊊`.
-/
theorem SetTheory.Set.ssubset_def (X Y:Set) : X ⊂ Y ↔ (X ⊆ Y ∧ X ≠ Y) := by rfl

/-- Remark 3.1.15 -/
theorem SetTheory.Set.subset_congr_left {A A' B:Set} (hAA':A = A') (hAB: A ⊆ B) : A' ⊆ B := by
  simp_all

/-- Examples 3.1.16 -/
@[simp, refl]
theorem SetTheory.Set.subset_self (A:Set) : A ⊆ A := by
  simp[subset_def]

/-- Examples 3.1.16 -/
@[simp]
theorem SetTheory.Set.empty_subset (A:Set) : ∅ ⊆ A := by
  simp only [subset_def, not_mem_empty, IsEmpty.forall_iff, implies_true]


/-- Proposition 3.1.17 (Partial ordering by set inclusion) -/
theorem SetTheory.Set.subset_trans {A B C:Set} (hAB:A ⊆ B) (hBC:B ⊆ C) : A ⊆ C := by
  -- This proof is written to follow the structure of the original text.
  rw [subset_def]
  intro x hx
  rw [subset_def] at hAB
  apply hAB x at hx
  apply hBC x at hx
  assumption

/-- Proposition 3.1.17 (Partial ordering by set inclusion) -/
theorem SetTheory.Set.subset_antisymm (A B:Set) (hAB:A ⊆ B) (hBA:B ⊆ A) : A = B := by
  simp_all[subset_def]
  aesop?

/-- Proposition 3.1.17 (Partial ordering by set inclusion) -/
theorem SetTheory.Set.ssubset_trans (A B C:Set) (hAB:A ⊂ B) (hBC:B ⊂ C) : A ⊂ C := by
  have this: A⊆ C:=by
     simp_all[ssubset_def]
     obtain⟨haAB,hbAB⟩:=hAB
     obtain⟨haBC,hbBC⟩:=hBC
     exact Set.subset_trans haAB haBC
  simp_all  [ssubset_def]
  by_contra hAC
  simp[hAC] at hAB
  have h:= subset_antisymm B C
  subst hAC
  simp_all only [subset_self, imp_false, not_true_eq_false]
/--
  This defines the subtype `A.toSubtype` for any `A:Set`.
  Note that `A.toSubtype` gives you a type, similar to how `Object` or `Set` are types.
  A value `x'` of type `A.toSubtype` combines some `x: Object` with a proof that `hx: x ∈ A`.

  To produce an element `x'` of this subtype, use `⟨ x, hx ⟩`, where `x: Object` and `hx: x ∈ A`.
  The object `x` associated to a subtype element `x'` is recovered as `x'.val`, and
  the property `hx` that `x` belongs to `A` is recovered as `x'.property`.
-/
abbrev SetTheory.Set.toSubtype (A:Set) := Subtype (fun x ↦ x ∈ A)

example (A: Set) (x: Object) (hx: x ∈ A) : A.toSubtype := ⟨x, hx⟩
example (A: Set) (x': A.toSubtype) : Object := x'.val
example (A: Set) (x': A.toSubtype) : x'.val ∈ A := x'.property

-- In practice, a subtype lets us carry an object with a membership proof as a single value.
-- Compare these two proofs. They are equivalent, but the latter packs `x` and `hx` into `x'`.
example (A B: Set) (x: Object) (hx: x ∈ A) : x ∈ A ∪ B := by simp; left; exact hx
example (A B: Set) (x': A.toSubtype) : x'.val ∈ A ∪ B := by simp; left; exact x'.property

instance : CoeSort (Set) (Type v) where
  coe A := A.toSubtype

-- Now instead of writing `x': A.toSubtype`, we can just write `x': A`.
-- Compare these three proofs. They are equivalent, but the last one reads most concisely.
example (A B: Set) (x: Object) (hx: x ∈ A) : x ∈ A ∪ B := by simp; left; exact hx
example (A B: Set) (x': A.toSubtype) : x'.val ∈ A ∪ B := by simp; left; exact x'.property
example (A B: Set) (x': A) : x'.val ∈ A ∪ B := by simp; left; exact x'.property

/--
  Elements of a set (implicitly coerced to a subtype) are also elements of the set
  (with respect to the membership operation of the set theory).
-/
lemma SetTheory.Set.subtype_property (A:Set) (x:A) : x.val ∈ A := x.property

lemma SetTheory.Set.subtype_coe (A:Set) (x:A) : x.val = x := rfl

lemma SetTheory.Set.coe_inj (A:Set) (x y:A) : x.val = y.val ↔ x = y := Subtype.coe_inj

/--
  If one has a proof `hx` of `x ∈ A`, then `A.subtype_mk hx` will then make the element of `A`
  (viewed as a subtype) corresponding to `x`.
-/
def SetTheory.Set.subtype_mk (A:Set) {x:Object} (hx:x ∈ A) : A := ⟨ x, hx ⟩

@[simp]
lemma SetTheory.Set.subtype_mk_coe {A:Set} {x:Object} (hx:x ∈ A) : A.subtype_mk hx = x := by rfl


abbrev SetTheory.Set.specify (A:Set) (P: A → Prop) : Set := SetTheory.specify A P

/-- Axiom 3.6 (axiom of specification) -/
theorem SetTheory.Set.specification_axiom {A:Set} {P: A → Prop} {x:Object} (h: x ∈ A.specify P) :
    x ∈ A :=
  (SetTheory.specification_axiom A P).1 x h

/-- Axiom 3.6 (axiom of specification) -/
theorem SetTheory.Set.specification_axiom' {A:Set} (P: A → Prop) (x:A) :
    x.val ∈ A.specify P ↔ P x :=
  (SetTheory.specification_axiom A P).2 x

/-- Axiom 3.6 (axiom of specification) -/
@[simp]
theorem SetTheory.Set.specification_axiom'' {A:Set} (P: A → Prop) (x:Object) :
    x ∈ A.specify P ↔ ∃ h:x ∈ A, P ⟨ x, h ⟩ := by
  constructor
  . intro h; use specification_axiom h
    simp [←specification_axiom' P, h]
  intro ⟨ h, hP ⟩
  simpa [←specification_axiom' P] using hP

theorem SetTheory.Set.specify_subset {A:Set} (P: A → Prop) : A.specify P ⊆ A := by
  simp[subset_def]
  intro x h Q
  exact h

/-- This exercise may require some understanding of how  subtypes are implemented in Lean. -/
theorem SetTheory.Set.specify_congr {A A':Set} (hAA':A = A') {P: A → Prop} {P': A' → Prop}
  (hPP': (x:Object) → (h:x ∈ A) → (h':x ∈ A') → P ⟨ x, h⟩ ↔ P' ⟨ x, h'⟩ ) :
    A.specify P = A'.specify P' := by
  --let Q x y := P x ∧ x=y
  ext x
  simp_all only [forall_true_left, specification_axiom'']

instance SetTheory.Set.instIntersection : Inter Set where
  inter X Y := X.specify (fun x ↦ x.val ∈ Y)

-- Now we can use the `X ∩ Y` notation for an intersection of two `Set`s.
example (X Y: Set) : X ∩ Y = X.specify (fun x ↦ x.val ∈ Y) := rfl

/-- Definition 3.1.22 (Intersections) -/
@[simp]
theorem SetTheory.Set.mem_inter (x:Object) (X Y:Set) : x ∈ (X ∩ Y) ↔ (x ∈ X ∧ x ∈ Y) := by
  constructor
  . intro h; have h' := specification_axiom h; simp [h']
    exact (specification_axiom' _ ⟨ x, h' ⟩).mp h
  intro ⟨ hX, hY ⟩; exact (specification_axiom' (fun x ↦ x.val ∈ Y) ⟨ x,hX⟩).mpr hY

instance SetTheory.Set.instSDiff : SDiff Set where
  sdiff X Y := X.specify (fun x ↦ x.val ∉ Y)

-- Now we can use the `X \ Y` notation for a difference of two `Set`s.
example (X Y: Set) : X \ Y = X.specify (fun x ↦ x.val ∉ Y) := rfl

/-- Definition 3.1.26 (Difference sets) -/
@[simp]
theorem SetTheory.Set.mem_sdiff (x:Object) (X Y:Set) : x ∈ (X \ Y) ↔ (x ∈ X ∧ x ∉ Y) := by
  constructor
  . intro h; have h' := specification_axiom h; simp [h']
    exact (specification_axiom' _ ⟨ x, h' ⟩ ).mp h
  intro ⟨ hX, hY ⟩; exact (specification_axiom' (fun x ↦ x.val ∉ Y) ⟨ x, hX⟩ ).mpr hY

/-- Proposition 3.1.27(d) / Exercise 3.1.6 -/
theorem SetTheory.Set.inter_comm (A B:Set) : A ∩ B = B ∩ A := by
  ext x
  simp[mem_inter]
  aesop?

/-- Proposition 3.1.27(b) -/
theorem SetTheory.Set.subset_union {A X: Set} (hAX: A ⊆ X) : A ∪ X = X := by
  ext x
  simp[mem_union]
  intro h
  simp[subset_def] at hAX
  specialize hAX x
  apply hAX at h
  exact h

/-- Proposition 3.1.27(b) -/
theorem SetTheory.Set.union_subset {A X: Set} (hAX: A ⊆ X) : X ∪ A = X := by
  ext x
  simp_all only [mem_union, or_iff_left_iff_imp]
  intro y
  aesop?



/-- Proposition 3.1.27(c) -/
@[simp]
theorem SetTheory.Set.inter_self (A:Set) : A ∩ A = A := by
  ext x
  simp_all only [mem_inter, and_self]

/-- Proposition 3.1.27(e) -/
theorem SetTheory.Set.inter_assoc (A B C:Set) : (A ∩ B) ∩ C = A ∩ (B ∩ C) := by
  ext x
  simp_all only [mem_inter]
  constructor
  · intro a
    simp_all only [and_self]
  · intro a
    simp_all only [and_self]

/-- Proposition 3.1.27(f) -/
theorem  SetTheory.Set.inter_union_distrib_left (A B C:Set) :
    A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by
  ext x
  simp_all
  constructor
  · intro a
    simp_all only [true_and]
  · intro a
    cases a with
    | inl h => simp_all only [true_or, and_self]
    | inr h_1 => simp_all only [or_true, and_self]

/-- Proposition 3.1.27(f) -/
theorem  SetTheory.Set.union_inter_distrib_left (A B C:Set) :
    A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) := by
  ext x
  simp_all
  aesop?

/-- Proposition 3.1.27(f) -/

theorem SetTheory.Set.union_compl {A X:Set} (hAX: A ⊆ X) : A ∪ (X \ A) = X := by
  -- ext x
  -- simp_all[subset_def,mem_union]

  -- constructor
  -- · intro h
  --   cases h with
  --   | inl h_1 => simp_all only
  --   | inr h_2 => simp_all only
  -- · intro h
  ext x
  simp only [ mem_union, mem_sdiff]

  by_cases h: x ∈ A
  · constructor
    · intro h2
      --simp_all only [not_true_eq_false, and_false, or_false]
      apply hAX
      simp_all only
    · intro h2
      simp_all only [not_true_eq_false, and_false, or_false]
  · simp_all only [not_false_eq_true, and_true, false_or]
/-- Proposition 3.1.27(f) -/
theorem SetTheory.Set.inter_compl {A X:Set} : A ∩ (X \ A) = ∅ := by
  ext x
  simp_all only [mem_inter, mem_sdiff, not_mem_empty, iff_false, not_and, not_true_eq_false,
    and_false, not_false_eq_true, implies_true]

/-- Proposition 3.1.27(g) -/
theorem SetTheory.Set.compl_union {A B X:Set} : X \ (A ∪ B) = (X \ A) ∩ (X \ B) := by
  ext x
  simp_all[mem_inter,mem_sdiff]
  apply Iff.intro
  · intro a
    simp_all only [not_false_eq_true, and_self]
  · intro a
    simp_all only [not_false_eq_true, and_self]


/-- Proposition 3.1.27(g) -/
theorem SetTheory.Set.compl_inter {A B X:Set} : X \ (A ∩ B) = (X \ A) ∪ (X \ B) := by
  ext x
  simp_all[mem_sdiff,mem_inter,mem_union]
  apply Iff.intro
  · intro a
    simp_all only [true_and]
    obtain ⟨left, right⟩ := a
    sorry
  · intro a
    cases a with
    | inl h => simp_all only [IsEmpty.forall_iff, and_self]
    | inr h_1 => simp_all only [not_false_eq_true, implies_true, and_self]


/-- Not from textbook: sets form a distributive lattice. -/
instance SetTheory.Set.instDistribLattice : DistribLattice Set where
  le := (· ⊆ ·)
  le_refl := subset_self
  le_trans := fun _ _ _ ↦ subset_trans
  le_antisymm := subset_antisymm
  inf := (· ∩ ·)
  sup := (· ∪ ·)
  le_sup_left := by
    intro A B
    simp[subset_def,mem_union]
    intro x h
    tauto
  le_sup_right := by
    intro A B
    simp[subset_def,mem_union]
    intro x h
    tauto
  sup_le := by
    intro A B C hac hbc
    simp[mem_union,subset_def]
    intro x h
    cases h with
    | inl h_1 =>
      apply hac
      simp_all only
    | inr h_2 =>
      apply hbc
      simp_all only
  inf_le_left := by
    intro A B x h
    simp_all only [mem_inter]
  inf_le_right := by
    intro A B x h
    simp_all only [mem_inter]
  le_inf := by
    intro A B C hab hac
    simp_all [subset_def,mem_inter]
  le_sup_inf := by
    intro X Y Z; change (X ∪ Y) ∩ (X ∪ Z) ⊆ X ∪ (Y ∩ Z)
    rw [←union_inter_distrib_left]

/-- Sets have a minimal element.  -/
instance SetTheory.Set.instOrderBot : OrderBot Set where
  bot := ∅
  bot_le := empty_subset

-- Now we've defined `A ≤ B` to mean `A ⊆ B`, and set `⊥` to `∅`.
-- This makes the `Disjoint` definition from Mathlib work with our `Set`.
example (A B: Set) : (A ≤ B) ↔ (A ⊆ B) := by rfl
example : ⊥ = (∅: Set) := by rfl
example (A B: Set) : Prop := Disjoint A B

/-- Definition of disjointness (using the previous instances) -/
theorem SetTheory.Set.disjoint_iff (A B:Set) : Disjoint A B ↔ A ∩ B = ∅ := by
  convert _root_.disjoint_iff

abbrev SetTheory.Set.replace (A:Set) {P: A → Object → Prop}
  (hP : ∀ x y y', P x y ∧ P x y' → y = y') : Set := SetTheory.replace A P hP

/-- Axiom 3.7 (Axiom of replacement) -/
@[simp]
theorem SetTheory.Set.replacement_axiom {A:Set} {P: A → Object → Prop}
  (hP: ∀ x y y', P x y ∧ P x y' → y = y') (y:Object) :
    y ∈ A.replace hP ↔ ∃ x, P x y := SetTheory.replacement_axiom A P hP y

abbrev Nat := SetTheory.nat

-- Going forward, we'll use `Nat` as a type.
-- However, notice we've set `Nat` to `SetTheory.nat` which is a `Set` and not a type.
-- The only reason we can write `x: Nat` is because we've previously defined a `CoeSort`
-- coercion that lets us write `x: A` (when `A` is a `Set`) as a shortcut for `x: A.toSubtype`.
-- This is why, whenever you see `x: Nat`, you're really looking at `x: Nat.toSubtype`.
example (x: Nat) : Nat.toSubtype := x
example (x: Nat) : Object := x.val
example (x: Nat) : (x.val ∈ Nat) := x.property
example (o: Object) (ho: o ∈ Nat) : Nat := ⟨o, ho⟩

/-- Axiom 3.8 (Axiom of infinity) -/
def SetTheory.Set.nat_equiv : ℕ ≃ Nat := SetTheory.nat_equiv

-- Below are some API for handling coercions. This may not be the optimal way to set things up.
instance SetTheory.Set.instOfNat {n:ℕ} : OfNat Nat n where
  ofNat := nat_equiv n

-- Now we can define `Nat` with a natural literal.
example : Nat := 5
example : (5 : Nat).val ∈ Nat := (5 : Nat).property

instance SetTheory.Set.instNatCast : NatCast Nat where
  natCast n := nat_equiv n

-- Now we can turn `ℕ` into `Nat`.
example (n : ℕ) : Nat := n
example (n : ℕ) : (n : Nat).val ∈ Nat := (n : Nat).property

instance SetTheory.Set.toNat : Coe Nat ℕ where
  coe n := nat_equiv.symm n

-- Now we can turn `Nat` into `ℕ`.
example (n : Nat) : ℕ := n

instance SetTheory.Object.instNatCast : NatCast Object where
  natCast n := (n:Nat).val

-- Now we can turn `ℕ` into an `Object`.
example (n: ℕ) : Object := n
example (n: ℕ) : Set := {(n: Object)}

instance SetTheory.Object.instOfNat {n:ℕ} : OfNat Object n where
  ofNat := ((n:Nat):Object)

-- Now we can define `Object` with a natural literal.
example : Object := 1
example : Set := {1, 2, 3}

@[simp]
lemma SetTheory.Object.ofnat_eq {n:ℕ} : ((n:Nat):Object) = (n:Object) := rfl

lemma SetTheory.Object.ofnat_eq' {n:ℕ} : (ofNat(n):Object) = (n:Object) := rfl

@[simp]
lemma SetTheory.Object.ofnat_eq'' {n:Nat} : ((n:ℕ):Object) = (n: Object) := by
  simp [instNatCast, Nat.cast, Set.instNatCast]

@[simp]
lemma SetTheory.Object.ofnat_eq''' {n:ℕ} {hn} : ((⟨(n:Object), hn⟩: nat): ℕ) = n := by
  simp [instNatCast, Nat.cast, Set.instNatCast]

lemma SetTheory.Set.nat_coe_eq {n:ℕ} : (n:Nat) = OfNat.ofNat n := rfl

@[simp]
lemma SetTheory.Set.nat_equiv_inj (n m:ℕ) : (n:Nat) = (m:Nat) ↔ n=m  :=
  Equiv.apply_eq_iff_eq nat_equiv

@[simp]
lemma SetTheory.Set.nat_equiv_symm_inj (n m:Nat) : (n:ℕ) = (m:ℕ) ↔ n = m :=
  Equiv.apply_eq_iff_eq nat_equiv.symm

@[simp]
theorem SetTheory.Set.ofNat_inj (n m:ℕ) :
    (ofNat(n) : Nat) = (ofNat(m) : Nat) ↔ ofNat(n) = ofNat(m) := by
      convert nat_equiv_inj _ _

example : (5:Nat) ≠ (3:Nat) := by
  simp

@[simp]
theorem SetTheory.Set.ofNat_inj' (n m:ℕ) :
    (ofNat(n) : Object) = (ofNat(m) : Object) ↔ ofNat(n) = ofNat(m) := by
      simp only [←Object.ofnat_eq, Object.ofnat_eq', Set.coe_inj, Set.nat_equiv_inj]
      rfl

example : (5:Object) ≠ (3:Object) := by
  simp

@[simp]
lemma SetTheory.Set.nat_coe_eq_iff {m n : ℕ} : (m:Object) = ofNat(n) ↔ m = n := by exact ofNat_inj' m n

example (n: ℕ) : (n: Object) = 2 ↔ n = 2 := by
  simp

@[simp]
theorem SetTheory.Object.natCast_inj (n m:ℕ) :
    (n : Object) = (m : Object) ↔ n = m := by
      simp [←ofnat_eq, Subtype.val_inj]

@[simp]
lemma SetTheory.Set.nat_equiv_coe_of_coe (n:ℕ) : ((n:Nat):ℕ) = n :=
  Equiv.symm_apply_apply nat_equiv n

@[simp]
lemma SetTheory.Set.nat_equiv_coe_of_coe' (n:Nat) : ((n:ℕ):Nat) = n :=
  Equiv.symm_apply_apply nat_equiv.symm n

@[simp]
lemma SetTheory.Set.nat_equiv_coe_of_coe'' (n:ℕ) : ((ofNat(n):Nat):ℕ) = n :=
  nat_equiv_coe_of_coe n

@[simp]
lemma SetTheory.Set.nat_coe_eq_iff' {m: Nat} {n : ℕ} : (m:Object) = (ofNat(n):Object) ↔ (m:ℕ) = ofNat(n) := by
  constructor <;> intro h <;> rw [show m = n by aesop]
  apply nat_equiv_coe_of_coe; rfl


/-- Example 3.1.16 (simplified).  -/
example : ({3, 5}:Set) ⊆ {1, 3, 5} := by
  simp only [subset_def, mem_pair, mem_triple]; tauto


/-- Example 3.1.17 (simplified). -/
example : ({3, 5}:Set).specify (fun x ↦ x.val ≠ 3) = ({5}:Set) := by
  ext
  simp only [mem_singleton, specification_axiom'']
  constructor
  · rintro ⟨h1, h2⟩; simp only [mem_pair] at h1; tauto
  rintro ⟨rfl⟩; norm_num

/-- Example 3.1.24 -/
example : ({1, 2, 4}:Set) ∩ {2,3,4} = {2, 4} := by
  ext x
  -- Instead of unfolding repetitive branches by hand like earlier,
  -- you can use the `aesop` tactic which does this automatically.
  aesop

/-- Example 3.1.24 -/

example : ({1, 2}:Set) ∩ {3,4} = ∅ := by
  rw [eq_empty_iff_forall_notMem]
  aesop

example : ¬ Disjoint ({1, 2, 3}:Set) {2,3,4} := by
  rw [disjoint_iff]
  intro h
  change {1, 2, 3} ∩ {2, 3, 4} = ∅ at h
  rw [eq_empty_iff_forall_notMem] at h
  aesop

example : Disjoint (∅:Set) ∅ := by
  simp only [disjoint_self]
  tauto


/-- Definition 3.1.26 example -/

example : ({1, 2, 3, 4}:Set) \ {2,4,6} = {1, 3} := by
  apply ext; aesop

/-- Example 3.1.30 -/
example : ({3,5,9}:Set).replace (P := fun x y ↦ ∃ (n:ℕ), x.val = n ∧ y = (n+1:ℕ)) (by aesop)
  = {4,6,10} := by
  ext x
  simp only [replacement_axiom]
  constructor
  · rintro ⟨a, ⟨x, ⟨hax, hxs⟩⟩⟩
    aesop
  aesop


/-- Example 3.1.31 -/
example : ({3,5,9}:Set).replace (P := fun _ y ↦ y=1) (by aesop) = {1} := by
  ext; simp only [replacement_axiom]; aesop

/-- Exercise 3.1.5.  One can use the `tfae_have` and `tfae_finish` tactics here. -/
theorem SetTheory.Set.subset_tfae (A B:Set) : [A ⊆ B, A ∪ B = B, A ∩ B = A].TFAE := by
  tfae_have 1 → 2:=by
    intro h
    ext x
    simp_all[subset_def,mem_union]
  tfae_have 2 → 3:=by
    intro h
    ext x
    simp_all[mem_inter]
    intro h2
    simp[Set.ext_iff] at h
    specialize h x
    apply h at h2
    exact h2
  tfae_have 3 → 1 :=by
    intro h
    simp_all[subset_def,Set.ext_iff]
  tfae_finish

/-- Exercise 3.1.7 -/
theorem SetTheory.Set.inter_subset_left (A B:Set) : A ∩ B ⊆ A := by
  intro x h
  simp_all only [mem_inter]

/-- Exercise 3.1.7 -/
theorem SetTheory.Set.inter_subset_right (A B:Set) : A ∩ B ⊆ B := by
  simp_all[subset_def,mem_inter]

/-- Exercise 3.1.7 -/
@[simp]
theorem SetTheory.Set.subset_inter_iff (A B C:Set) : C ⊆ A ∩ B ↔ C ⊆ A ∧ C ⊆ B := by
  simp[subset_def,mem_inter]
  apply Iff.intro
  · intro a
    simp_all only [implies_true, and_self]
  · intro a x a_1
    simp_all only [and_self]

/-- Exercise 3.1.7 -/
theorem SetTheory.Set.subset_union_left (A B:Set) : A ⊆ A ∪ B := by
  simp[subset_def,mem_union]
  intro x a
  simp_all only [true_or]

/-- Exercise 3.1.7 -/
theorem SetTheory.Set.subset_union_right (A B:Set) : B ⊆ A ∪ B := by
  simp[subset_def,mem_union]
  intro x a
  simp_all only [or_true]

/-- Exercise 3.1.7 -/
@[simp]
theorem SetTheory.Set.union_subset_iff (A B C:Set) : A ∪ B ⊆ C ↔ A ⊆ C ∧ B ⊆ C := by
  simp[subset_def,mem_union]
  apply Iff.intro
  · intro a
    simp_all only [true_or, implies_true, or_true, and_self]
  · intro a x a_1
    obtain ⟨left, right⟩ := a
    cases a_1 with
    | inl h => simp_all only
    | inr h_1 => simp_all only

/-- Exercise 3.1.8 -/
@[simp]
theorem SetTheory.Set.inter_union_cancel (A B:Set) : A ∩ (A ∪ B) = A := by
  simp[Set.ext_iff,mem_inter,mem_union]
  intro x a
  simp_all only [true_or]
/-- Exercise 3.1.8 -/
@[simp]
theorem SetTheory.Set.union_inter_cancel (A B:Set) : A ∪ (A ∩ B) = A := by
  ext x
  simp_all [mem_inter, mem_union]


/-- Exercise 3.1.9 -/
theorem SetTheory.Set.partition_left {A B X:Set} (h_union: A ∪ B = X) (h_inter: A ∩ B = ∅) :
    A = X \ B := by
    ext x
    simp_all[Set.ext_iff,mem_union,mem_inter]
    specialize h_union x
    specialize h_inter x
    apply Iff.intro
    · intro a
      simp_all only [or_false, true_iff, forall_const, not_false_eq_true, and_self]
    · intro a
      simp_all only [or_false, iff_true, not_false_eq_true, imp_self]


/-- Exercise 3.1.9 -/
theorem SetTheory.Set.partition_right {A B X:Set} (h_union: A ∪ B = X) (h_inter: A ∩ B = ∅) :
    B = X \ A := by
  ext x
  simp_all[Set.ext_iff,mem_union,mem_inter]
  specialize h_union x
  specialize h_inter x
  apply Iff.intro
  · intro a
    simp_all only [or_true, true_iff, not_true_eq_false, imp_false, not_false_eq_true, and_self]
  · intro a
    simp_all only [false_or, iff_true, not_true_eq_false, implies_true]

/--
  Exercise 3.1.10.
  You may find `Function.onFun_apply` and the `fin_cases` tactic useful.
-/
theorem SetTheory.Set.pairwise_disjoint (A B:Set) :
    Pairwise (Function.onFun Disjoint ![A \ B, A ∩ B, B \ A]) := by
  intro i j hij
  -- Split the problem into all possible index combinations (0, 1, 2) for i and j
  fin_cases i <;> fin_cases j
  -- Handle all 9 resulting goals
  all_goals
    -- 1. If i = j, the hypothesis hij (i ≠ j) creates a contradiction.

    -- 2. Expand definitions of Disjoint, set difference, and intersection.
    --    This reduces set notation (sets i) to logical propositions.
    simp [disjoint_iff, Set.ext_iff]
    aesop
    -- 3. Solve the logical contradictions (e.g., x ∈ B ∧ x ∉ B).
theorem SetTheory.Set.pairwise_disjoint2 (A B : Set) :
    Pairwise (Function.onFun Disjoint ![A \ B, A ∩ B, B \ A]) := by
  -- First prove the three basic disjointness statements between the pieces.
  have h01 : Disjoint (A \ B) (A ∩ B) := by
    rw [disjoint_iff]
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    -- x ∈ (A \ B) ∩ (A ∩ B)
    have hx' : x ∈ A \ B ∧ x ∈ A ∩ B := by
      simpa [mem_inter] using hx
    rcases hx' with ⟨hxAB, hxAintB⟩
    -- From x ∈ A \ B we get x ∈ A ∧ x ∉ B
    have hxAB' : x ∈ A ∧ x ∉ B := by
      simpa [mem_sdiff] using hxAB
    -- From x ∈ A ∩ B we get x ∈ A ∧ x ∈ B
    have hxAintB' : x ∈ A ∧ x ∈ B := by
      simpa [mem_inter] using hxAintB
    -- Contradiction: x ∉ B and x ∈ B
    exact hxAB'.2 hxAintB'.2

  have h02 : Disjoint (A \ B) (B \ A) := by
    rw [disjoint_iff]
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    -- x ∈ (A \ B) ∩ (B \ A)
    have hx' : x ∈ A \ B ∧ x ∈ B \ A := by
      simpa [mem_inter] using hx
    rcases hx' with ⟨hxAB, hxBA⟩
    -- From x ∈ A \ B we get x ∈ A ∧ x ∉ B
    have hxAB' : x ∈ A ∧ x ∉ B := by
      simpa [mem_sdiff] using hxAB
    -- From x ∈ B \ A we get x ∈ B ∧ x ∉ A
    have hxBA' : x ∈ B ∧ x ∉ A := by
      simpa [mem_sdiff] using hxBA
    -- Contradiction: x ∉ A and x ∈ A
    exact hxBA'.2 hxAB'.1

  have h12 : Disjoint (A ∩ B) (B \ A) := by
    rw [disjoint_iff]
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    -- x ∈ (A ∩ B) ∩ (B \ A)
    have hx' : x ∈ A ∩ B ∧ x ∈ B \ A := by
      simpa [mem_inter] using hx
    rcases hx' with ⟨hxAintB, hxBA⟩
    -- From x ∈ A ∩ B we get x ∈ A ∧ x ∈ B
    have hxAintB' : x ∈ A ∧ x ∈ B := by
      simpa [mem_inter] using hxAintB
    -- From x ∈ B \ A we get x ∈ B ∧ x ∉ A
    have hxBA' : x ∈ B ∧ x ∉ A := by
      simpa [mem_sdiff] using hxBA
    -- Contradiction: x ∉ A and x ∈ A
    exact hxBA'.2 hxAintB'.1

  -- Now use `fin_cases` to check all pairs of indices in `Fin 3`.
  intro n m hnm
  fin_cases n <;> fin_cases m
  · -- n = 0, m = 0
    -- Impossible because `Pairwise` assumes n ≠ m
    cases hnm rfl
  · -- n = 0, m = 1
    -- This is Disjoint (A \ B) (A ∩ B)
    simpa [Function.onFun_apply] using h01
  · -- n = 0, m = 2
    -- This is Disjoint (A \ B) (B \ A)
    simpa [Function.onFun_apply] using h02
  · -- n = 1, m = 0
    -- This is Disjoint (A ∩ B) (A \ B), use symmetry of disjointness
    simpa [Function.onFun_apply, disjoint_comm] using h01
  · -- n = 1, m = 1
    cases hnm rfl
  · -- n = 1, m = 2
    -- This is Disjoint (A ∩ B) (B \ A)
    simpa [Function.onFun_apply] using h12
  · -- n = 2, m = 0
    -- This is Disjoint (B \ A) (A \ B)
    simpa [Function.onFun_apply, disjoint_comm] using h02
  · -- n = 2, m = 1
    -- This is Disjoint (B \ A) (A ∩ B)
    simpa [Function.onFun_apply, disjoint_comm] using h12
  · -- n = 2, m = 2
    cases hnm rfl

/-- Exercise 3.1.10 -/
theorem SetTheory.Set.union_eq_partition (A B:Set) : A ∪ B = (A \ B) ∪ (A ∩ B) ∪ (B \ A) := by
  -- ext x
  -- -- x is amember of the union of A and B iff
  -- -- x is a member of the union of A \ B , A ∩ B and B \ a

  -- by_cases ha: x ∈ A
  -- constructor
  ext x
  have : x ∈ A ∨ x ∉ A := by tauto
  have : x ∉ B ∨ x ∈ B := by tauto
  aesop


/--
  Exercise 3.1.11.
  The challenge is to prove this without using `Set.specify`, `Set.specification_axiom`,
  `Set.specification_axiom'`, or anything built from them (like differences and intersections).
-/
theorem SetTheory.Set.specification_from_replacement {A:Set} {P: A → Prop} :
    ∃ B, B ⊆ A ∧ ∀ x, x.val ∈ B ↔ P x := by
  let Q x y := P x ∧ x.val = y
  have hQ : ∀ (x : A.toSubtype) (y y' : Object), Q x y ∧ Q x y' → y = y' := by aesop
  -- 3. Use the replacement axiom to construct the set B.
  use A.replace hQ
  constructor

  -- 4. Prove B ⊆ A
  · intro y hy
    -- Apply the replacement axiom to unpack membership in B
    rw [replacement_axiom] at hy
    obtain ⟨x, _, rfl⟩ := hy
    -- Since x comes from A (as a subtype), x.val is automatically in A
    exact x.property

  -- 5. Prove ∀ x, x.val ∈ B ↔ P x
  · intro x
    rw [replacement_axiom]
    constructor
    -- Forward direction: x.val ∈ B → P x
    · rintro ⟨x', hPx', h_eq⟩
      -- We have x'.val = x.val. By subtype injectivity, x' = x.
      rw [coe_inj] at h_eq
      subst h_eq
      exact hPx'

    -- Backward direction: P x → x.val ∈ B
    · intro hPx
      use x
      -- We need to show Q x x.val, which is (P x ∧ x.val = x.val)

/-- Exercise 3.1.12.-/
theorem SetTheory.Set.subset_union_subset {A B A' B':Set} (hA'A: A' ⊆ A) (hB'B: B' ⊆ B) :
    A' ∪ B' ⊆ A ∪ B := by
    intro x h
    simp_all only [mem_union,subset_def]
    specialize hA'A x
    specialize hB'B x
    cases h with
    | inl h_1 => simp_all only [forall_const, true_or]
    | inr h_2 => simp_all only [forall_const, or_true]


/-- Exercise 3.1.12.-/
-- Exercise 3.1.12 Suppose that A, B, A'
-- , B' are sets such that A' ⊆ A and B' ⊆ B.
theorem SetTheory.Set.subset_inter_subset {A B A' B':Set} (hA'A: A' ⊆ A) (hB'B: B' ⊆ B) :
    A' ∩ B' ⊆ A ∩ B := by
    intro x h
    simp_all only [mem_inter,subset_def]
    tauto

/-- Exercise 3.1.12.-/
-- Give a counterexample to show that the statement A'\B' ⊆ A\B is false. Can you find a
-- modification of this statement involving the set difference operation \ which is true given the
-- stated hypotheses? Justify your answer.

-- just show explicit example and simp takes care of the rest
theorem SetTheory.Set.subset_diff_subset_counter :
    ∃ (A B A' B':Set), (A' ⊆ A) ∧ (B' ⊆ B) ∧ ¬ (A' \ B') ⊆ (A \ B) := by
  use {1}
  use {1}
  use {1}
  use ∅
  simp[subset_def]
/-
  Final part of Exercise 3.1.12: state and prove a reasonable substitute positive result for the
  above theorem that involves set differences.
-/

-- Exercise 3.1.13 Euclid famously defined a point to be “that which has no part”. This exercise
-- should be reminiscent of that definition. Define a proper subset of a set A to be a subset B of A
-- with B ≠ A. Let A be a non-empty set. Show that A does not have any non-empty proper subsets
-- if and only if A is of the form A = {x} for some object x.
theorem SetTheory.Set.singleton_iff (A:Set) (hA: A ≠ ∅) : (¬∃ B ⊂ A, B ≠ ∅) ↔ ∃ x, A = {x} := by
  --set A has the property there does not exist a set B that is a strict subset of A, and B is not the empty set
  -- iff there exists an object x such that A is the singleton f

  constructor
  · intro h
    -- Logic: For all B, if B ⊂ A, then B = ∅
    push_neg at h

    -- Since A ≠ ∅, there exists some x ∈ A
    have ⟨x, hx⟩ := nonempty_def hA
    use x

    -- We know {x} ⊆ A
    have h_sub : {x} ⊆ A := by
      intro y hy
      rw [mem_singleton] at hy
      subst hy
      exact hx

    -- Case distinction: Either {x} = A (we are done) or {x} ≠ A
    by_cases heq : {x} = A
    · symm; assumption
    · -- If {x} ≠ A, then {x} is a proper subset (since we already know {x} ⊆ A)
      have h_ssub : {x} ⊂ A := by
        rw [ssubset_def]
        exact ⟨h_sub, heq⟩

      -- By our hypothesis h, since {x} ⊂ A, {x} must be empty
      specialize h {x} h_ssub

      -- But {x} is not empty (it contains x), so this is a contradiction
      rw [eq_empty_iff_forall_notMem] at h
      specialize h x
      rw [mem_singleton] at h
      contradiction

  · -- Direction 2: If A = {x}, then it has no non-empty proper subsets
    rintro ⟨x, rfl⟩
    push_neg
    intro B hB

    -- hB states that B ⊂ {x}, which means B ⊆ {x} and B ≠ {x}
    rw [ssubset_def] at hB
    obtain ⟨hB_sub, hB_ne⟩ := hB

    -- We assume B is not empty to derive a contradiction
    by_contra h_nonempty

    -- If B is not empty, it contains some element y
    obtain ⟨y, hy⟩ := nonempty_def h_nonempty

    -- Since B ⊆ {x}, y must be equal to x
    have hy_eq : y = x := by
      apply hB_sub at hy
      rwa [mem_singleton] at hy
    subst hy_eq

    -- Now we know x ∈ B. We can show {x} ⊆ B
    have h_eq : {y} ⊆ B := by
      intro z hz
      rw [mem_singleton] at hz
      subst hz
      exact hy

    -- If B ⊆ {x} and {x} ⊆ B, then B = {x}
    have B_eq_x : B = {y} := subset_antisymm B {y} hB_sub h_eq

    -- This contradicts the proper subset condition (B ≠ {x})
    contradiction


/-
  Now we introduce connections between this notion of a set, and Mathlib's notion.
  The exercise below will acquiant you with the API for Mathlib's sets.
-/

instance SetTheory.Set.inst_coe_set : Coe Set (_root_.Set Object) where
  coe X := { x | x ∈ X }

-- Now we can convert our `Set` into a Mathlib `_root_.Set`.
-- Notice that Mathlib sets are parameterized by the element type, in our case `Object`.
example (X: Set) : _root_.Set Object := X

/--
  Injectivity of
  the coercion. Note however that we do NOT assert that the coercion is surjective
  (and indeed Russell's paradox prevents this)
-/
@[simp]
theorem SetTheory.Set.coe_inj' (X Y:Set) :
    (X : _root_.Set Object) = (Y : _root_.Set Object) ↔ X = Y := by
  constructor
  . intro h; apply ext; intro x
    replace h := congr(x ∈ $h); simpa using h
  rintro rfl; rfl

/-- Compatibility of the membership operation ∈ -/
theorem SetTheory.Set.mem_coe (X:Set) (x:Object) : x ∈ (X : _root_.Set Object) ↔ x ∈ X := by
  simp

/-- Compatibility of the emptyset -/
theorem SetTheory.Set.coe_empty : ((∅:Set) : _root_.Set Object) = ∅ := by
  simp only [not_mem_empty, Set.setOf_false]

/-- Compatibility of subset -/
theorem SetTheory.Set.coe_subset (X Y:Set) :
    (X : _root_.Set Object) ⊆ (Y : _root_.Set Object) ↔ X ⊆ Y := by
    simp only [Set.setOf_subset_setOf]
    constructor
    · intro h y hy
      specialize h y
      apply h at hy
      exact hy
    · intro h x hx
      apply h
      exact hx

--https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Set/Basic.html
-- look up built in mathlib set library and find the appropriate theorems
theorem SetTheory.Set.coe_ssubset (X Y:Set) :
    (X : _root_.Set Object) ⊂ (Y : _root_.Set Object) ↔ X ⊂ Y := by
  simp only [Set.ssubset_iff_subset_ne]
  simp_all only [Set.setOf_subset_setOf, ne_eq, coe_inj']
  rfl





/-- Compatibility of singleton -/
theorem SetTheory.Set.coe_singleton (x: Object) : ({x} : _root_.Set Object) = {x} := by sorry

/-- Compatibility of union -/
theorem SetTheory.Set.coe_union (X Y: Set) :
    (X ∪ Y : _root_.Set Object) = (X : _root_.Set Object) ∪ (Y : _root_.Set Object) := by sorry

/-- Compatibility of pair -/
theorem SetTheory.Set.coe_pair (x y: Object) : ({x, y} : _root_.Set Object) = {x, y} := by sorry

/-- Compatibility of subtype -/
theorem SetTheory.Set.coe_subtype (X: Set) :  (X : _root_.Set Object) = X.toSubtype := by sorry

/-- Compatibility of intersection -/
theorem SetTheory.Set.coe_intersection (X Y: Set) :
    (X ∩ Y : _root_.Set Object) = (X : _root_.Set Object) ∩ (Y : _root_.Set Object) := by sorry

/-- Compatibility of set difference-/
theorem SetTheory.Set.coe_diff (X Y: Set) :
    (X \ Y : _root_.Set Object) = (X : _root_.Set Object) \ (Y : _root_.Set Object) := by sorry

/-- Compatibility of disjointness -/
theorem SetTheory.Set.coe_Disjoint (X Y: Set) :
    Disjoint (X : _root_.Set Object) (Y : _root_.Set Object) ↔ Disjoint X Y := by sorry

end Chapter3
