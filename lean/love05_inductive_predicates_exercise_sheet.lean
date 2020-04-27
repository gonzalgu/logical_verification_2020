import .love05_inductive_predicates_demo


/-! # LoVe Exercise 5: Inductive Predicates -/


set_option pp.beta true

namespace LoVe


/-! ## Question 1: Even and Odd

The `even` predicate is true for even numbers and false for odd numbers. -/

#check even

/-! We define `odd` as the negation of `even`: -/

def odd (n : ℕ) : Prop :=
  ¬ even n

/-! 1.1. Prove that 1 is odd and register this fact as a simp rule.

Hint: `cases` is useful to reason about hypotheses of the form `even …`. -/

@[simp] lemma odd_1 :
  odd 1 :=
begin
  unfold odd,
  intro h,
  cases h,
end

/-! 1.2. Prove that 3, 5, and 7 are odd. -/

-- enter your answer here
lemma odd_3 : 
  odd 3 := 
begin
  unfold odd,
  intro h,
  cases h,
  apply odd_1,
  assumption,
end

lemma odd_5 : 
  odd 5 := 
begin
  unfold odd,
  intro h,
  cases h,
  simp at h_a,
  apply odd_3,
  assumption,
end

lemma odd_7 : 
  odd 7 := 
begin
  unfold odd,
  intro h,
  cases h,
  simp at h_a,
  apply odd_5,
  assumption,
end

/-! 1.3. Complete the following proof by structural induction. -/

lemma even_two_times :
  ∀m : ℕ, even (2 * m)
| 0       := even.zero
| (m + 1) :=
  begin
    rw mul_add,
    simp,
    rw add_comm,
    apply even.add_two,
    apply even_two_times,
  end

/-! 1.4. Complete the following proof by rule induction.

Hint: You can use the `cases` tactic (or `match … with`) to destruct an
existential quantifier and extract the witness. -/

lemma even_imp_exists_two_times :
  ∀n : ℕ, even n → ∃m, n = 2 * m :=
begin
  intros n hen,
  induction hen,
  case even.zero {
    apply exists.intro 0,
    refl },
  case even.add_two : k hek ih {
    cases ih with m hkm,
    existsi (m+1),
    rw hkm,
    rw mul_add,
    refl,
    }
end

/-! 1.6. Using `even_two_times` and `even_imp_exists_two_times`, prove the
following equivalence. -/

lemma even_iff_exists_two_times (n : ℕ) :
  even n ↔ ∃m, n = 2 * m :=
begin
  split,
  { 
    apply even_imp_exists_two_times,
  },
  {
    intro h,
    cases h with m hnm,
    rw hnm,
    apply even_two_times,
  }
end

lemma even_iff_exists_two_times₂ (n : ℕ) : 
  even n ↔ ∃m, n = 2 * m := 
iff.intro 
  (assume hen : even n,
    show ∃m, n = 2 * m, 
    from even_imp_exists_two_times n hen 
  )
  (assume hex : (∃ (m : ℕ), n = 2 * m), 
    match hex with 
    | ⟨ m, hnx⟩ := 
      begin
        rw hnx,
        apply even_two_times
      end
    end)

lemma even_iff_exists_two_times₃ (n : ℕ) : 
  even n ↔ ∃m, n = 2 * m := 
⟨ λhen, even_imp_exists_two_times n hen, 
  λ⟨m,hnm⟩, 
  begin
    rw hnm,
    apply even_two_times,
  end ⟩ 


/-! ## Question 2: Binary Trees

2.1. Prove the converse of `is_full_mirror`. You may exploit already proved
lemmas (e.g., `is_full_mirror`, `mirror_mirror`). -/

#check is_full_mirror
#check mirror_mirror

lemma mirror_is_full {α : Type} :
  ∀t : btree α, is_full (mirror t) → is_full t :=
begin
  intro t,
  intro hfmt,
  rw ←mirror_mirror t,
  apply is_full_mirror,
  assumption,
end

lemma mirror_is_full₂ {α : Type} : 
  ∀t : btree α, is_full (mirror t) → is_full t := 
assume t : btree α, 
assume hfmt : is_full (mirror t),
have mmt : mirror(mirror t) = t, from mirror_mirror t, 
have hfmmt : is_full (mirror(mirror t)), from is_full_mirror _ hfmt,
show is_full t,
from eq.subst mmt hfmmt

/-! 2.2. Define a `map` function on binary trees, similar to `list.map`. -/

def btree.map {α β : Type} (f : α → β) : btree α → btree β
| btree.empty        := btree.empty
| (btree.node v l r) := btree.node (f v) (btree.map l) (btree.map r) 
-- enter the missing cases here

/-! 2.3. Prove the following lemma by case distinction. -/

lemma btree.map_eq_empty_iff {α β : Type} (f : α → β) :
  ∀t : btree α, btree.map f t = btree.empty ↔ t = btree.empty :=
begin
  intro t,
  split,
  {
    intro h,
    cases t with v l r,
    {
      refl,
    },
    {
      cases h,
    },
  },
  {
    intro h,
    rw h,
    refl,
  }
end



/-! 2.4. Prove the following lemma by rule induction. -/

lemma btree.map_mirror {α β : Type} (f : α → β) :
  ∀t : btree α, is_full t → is_full (btree.map f t) :=
begin
  intro t,
  intro hft,
  induction hft with v l r hfl hfr hiffe hfml hfmr,
  {
    simp [btree.map, is_full.empty],    
  },
  {
    apply is_full.node,    
    {
      exact hfml,
    },
    {
      exact hfmr,
    },
    {
      split,
      {
        cases hiffe,
        intro h,
        have l_empty := (btree.map_eq_empty_iff _ _).mp h,
        have r_empty := hiffe_mp l_empty,
        rw r_empty,
        refl,
      },
      {
        cases hiffe,
        intro h,
        have r_empty := (btree.map_eq_empty_iff _ _).mp h,
        have l_empty := hiffe_mpr r_empty,
        rw l_empty,
        refl,
      }
    }
  }
end

-- forward attempt
lemma btree.map_mirror₂  {α β : Type} (f : α → β) :
  ∀t : btree α, is_full t → is_full (btree.map f t) := 
  assume t : btree α,
  assume hft : is_full t, 
    match t, hft with 
    | _, is_full.empty := 
      begin
        rw btree.map,
        apply is_full.empty,
      end
    | _, (is_full.node v l r hfl hfr hiffe) := 
      sorry
    end
end LoVe
