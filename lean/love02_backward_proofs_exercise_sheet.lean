
import .love02_backward_proofs_demo


/-! # LoVe Exercise 2: Backward Proofs -/


set_option pp.beta true

namespace LoVe


/-! ## Question 1: Connectives and Quantifiers

1.1. Carry out the following proofs using basic tactics.

Hint: Some strategies for carrying out such proofs are described at the end of
Section 2.3 in the Hitchhiker's Guide. -/

lemma I (a : Prop) :
  a → a :=
begin
  intro ha,
  assumption,
end

lemma K (a b : Prop) :
  a → b → b :=
begin
  intros ha hb,
  assumption,
end

lemma C (a b c : Prop) :
  (a → b → c) → b → a → c :=
begin
  intros f hb ha,
  exact f ha hb,
end

lemma proj_1st (a : Prop) :
  a → a → a :=
begin
  intros ha₁ ha₂,
  exact ha₁,
end

/-! Please give a different answer than for `proj_1st`: -/

lemma proj_2nd (a : Prop) :
  a → a → a :=
begin
  intros ha₁ ha₂,
  exact ha₂,
end

lemma some_nonsense (a b c : Prop) :
  (a → b → c) → a → (a → c) → b → c :=
begin
  intros f ha g hb,
  exact f ha hb,
end

/-! 1.2. Prove the contraposition rule using basic tactics. -/

lemma contrapositive (a b : Prop) :
  (a → b) → ¬ b → ¬ a :=
begin
  intros f hnb hna,
  apply hnb,
  exact f hna,
end

/-! 1.3. Prove the distributivity of `∀` over `∧` using basic tactics.

Hint: This exercise is tricky, especially the right-to-left direction. Some
forward reasoning, like in the proof of `and_swap₂` in the lecture, might be
necessary. -/

lemma forall_and {α : Type} (p q : α → Prop) :
  (∀x, p x ∧ q x) ↔ (∀x, p x) ∧ (∀x, q x) :=
begin
  split,
  intro h1,
  split,
  intro hx,
  apply (h1 hx).left,

  intro hx,
  apply (h1 hx).right,

  intro h2,
  intro hx,
  split,
  exact h2.left hx,
  exact h2.right hx,
end


/-! ## Question 2: Natural Numbers

2.1. Prove the following recursive equations on the first argument of the
`mul` operator defined in lecture 1. -/

#check mul

lemma mul_zero (n : ℕ) :
  mul 0 n = 0 :=
begin
  induction n,
  refl,
  simp [add,mul,n_ih],
end


lemma mul_succ (m n : ℕ) :
  mul (nat.succ m) n = add (mul m n) n :=
begin
  induction n with d hd,
  refl,
  simp [add,mul, hd],
  sorry,
end

/-! 2.2. Prove commutativity and associativity of multiplication using the
`induction` tactic. Choose the induction variable carefully. -/

lemma mul_comm (m n : ℕ) :
  mul m n = mul n m :=
begin
  induction n with d hd,
  rw mul_zero,
  refl,
  simp [add,mul,hd],
  rw mul_succ,
  rw add_comm,
end

lemma mul_assoc (l m n : ℕ) :
  mul (mul l m) n = mul l (mul m n) := 
begin
  induction n with d hd,
  refl,
  simp [add,mul],
  rw mul_add,
  rw hd,
end

/-! 2.3. Prove the symmetric variant of `mul_add` using `rewrite`. To apply
commutativity at a specific position, instantiate the rule by passing some
arguments (e.g., `mul_comm _ l`). -/

lemma add_mul (l m n : ℕ) :
  mul (add l m) n = add (mul n l) (mul n m) :=
begin
  rw mul_comm,
  rw mul_add,
end


/-! ## Question 3 (**optional**): Intuitionistic Logic

Intuitionistic logic is extended to classical logic by assuming a classical
axiom. There are several possibilities for the choice of axiom. In this
question, we are concerned with the logical equivalence of three different
axioms: -/

def excluded_middle :=
∀a : Prop, a ∨ ¬ a

def peirce :=
∀a b : Prop, ((a → b) → a) → a

def double_negation :=
∀a : Prop, (¬¬ a) → a

/-! For the proofs below, please avoid using lemmas from Lean's `classical`
namespace, because this would defeat the purpose of the exercise.

3.1 (**optional**). Prove the following implication using tactics.

Hint: You will need `or.elim` and `false.elim`. You can use
`simp [excluded_middle, peirce]` to unfold the definitions of `excluded_middle`
and `peirce`. -/

lemma peirce_of_em :
  excluded_middle → peirce :=
begin
  simp [excluded_middle, peirce],
  intro em,
  intros a b,
  intro f,
  apply or.elim (em a),
  intro ha,
  assumption,

  intro hna,
  cc,
end

--#print peirce_of_em

/-! 3.2 (**optional**). Prove the following implication using tactics. -/

lemma dn_of_peirce :
  peirce → double_negation :=
begin
  simp [peirce, double_negation],
  intro p,
  intro a,
  intro hnna,
  cc,
end

--#print dn_of_peirce

/-! We leave the missing implication for the homework: -/

namespace sorry_lemmas

lemma em_of_dn :
  double_negation → excluded_middle :=
begin
  simp [double_negation,excluded_middle],
  intro dn,
  intro a,
  have dna, from dn a,
  sorry,
  
end

end sorry_lemmas

end LoVe
