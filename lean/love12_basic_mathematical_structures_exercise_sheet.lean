import .love12_basic_mathematical_structures_demo


/-! # LoVe Exercise 12: Basic Mathematical Structures -/


set_option pp.beta true

namespace LoVe


/-! ## Question 1: Type Classes

Recall the datatype `btree` we introduced earlier: -/

#check btree

/-! The following function takes two trees and attaches copies of the second
tree to each leaf of the first tree. -/

def btree.graft {α : Type} : btree α → btree α → btree α
| btree.empty        u := u
| (btree.node a l r) u := btree.node a (btree.graft l u) (btree.graft r u)

#reduce btree.graft (btree.node 1 btree.empty btree.empty)
  (btree.node 2 btree.empty btree.empty)

/-! 1.1. Prove the following two lemmas by structural induction on `t`. -/

lemma btree.graft_assoc {α : Type} (t u v : btree α) :
  btree.graft (btree.graft t u) v = btree.graft t (btree.graft u v) :=
begin
  induction t with a tl tr htl htr,
  {
    simp [btree.graft],
  },
  {
    simp [btree.graft, htl, htr],
  }
end

lemma btree.graft_empty {α : Type} (t : btree α) :
  btree.graft t btree.empty = t :=
begin
  induction t with a tl tr htl htr,
  {
    refl,
  },
  {
    simp [btree.graft, htl, htr],
  }
end

/-! 1.2. Declare btree an instance of `add_monoid` using `graft` as addition
operator. -/

#print add_monoid

@[instance] def btree.add_monid {α : Type} : add_monoid (btree α) :=
{
  add := btree.graft,
  add_assoc := btree.graft_assoc,
  zero := btree.empty,
  zero_add := 
    begin
      intro t,
      refl,      
    end,
  add_zero := btree.graft_empty,
}


/-! 1.3. Explain why `btree` with `graft` as addition cannot be declared an
instance of `add_group`. -/

#print add_group

/- For any btree t, there is no 'inverse tree' t⁻¹ such that btree.graft t t⁻¹ = btree.nil
   In other words, for a given tree t, there is no tree w that can be grafted onto t
   and produce an empty tree.
 -/

/-! 1.4 (**optional**). Prove the following lemma illustrating why `btree` with
`graft` as addition does not constitute an `add_group`. -/

lemma btree.add_left_neg_counterexample :
  ∃x : btree ℕ, ∀ y : btree ℕ, btree.graft y x ≠ btree.empty :=
⟨ (btree.node 1 btree.empty btree.empty),
  λ t : btree ℕ, 
    begin      
      induction t with a tl tr htl htr,
      {
        intro h,
        cases h,
      },
      {
        simp [btree.graft],
      }
    end 
 ⟩ 


/-! ## Question 2: Multisets and Finsets

Recall the following definitions from the lecture: -/

#check multiset.elems
#check finset.elems
#check list.elems

/-! 2.1. Prove that the multiset of nodes does not change when mirroring a tree.

Hints:

* Perform structural induction on `t`.

* The `cc` tactic also works with set operations. -/

lemma multiset.elems_mirror (t : btree ℕ) :
  multiset.elems (mirror t) = multiset.elems t :=
begin
  induction t with a tl tr htl htr,
  {
    simp [mirror],
  },
  {
    simp [mirror, multiset.elems, htl, htr],
    cc,
  }
end

/-! 2.2. Prove that the finite set of nodes does not change when mirroring a
tree. -/

lemma finset.elems_mirror (t : btree ℕ) :
  finset.elems (mirror t) = finset.elems t :=
begin
  induction t with a tl tr htl htr,
  {
    simp [mirror],
  },
  {
    simp [mirror, finset.elems, htl, htr],
  }
end

/-! 2.3. Show that this does not hold for the list of nodes by providing a
tree `t` for which `nodes_list t ≠ nodes_list (mirror t)`.

If you define a suitable counterexample, the proof below will succeed. -/

def rotten_tree : btree ℕ :=
(btree.node 1 (btree.node 5 btree.empty btree.empty) (btree.node 2 (btree.node 3 btree.empty btree.empty) btree.empty))

#print rotten_tree
#eval rotten_tree
#eval mirror rotten_tree

#eval list.elems rotten_tree
#eval list.elems (mirror rotten_tree)

lemma list.elems_mirror_counterexample :
  ∃t : btree ℕ, list.elems t ≠ list.elems (mirror t) :=
begin
  apply exists.intro rotten_tree,
  exact dec_trivial
end

end LoVe
