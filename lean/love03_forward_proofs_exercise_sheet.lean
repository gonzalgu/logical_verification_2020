import .lovelib


/-! # LoVe Exercise 3: Forward Proofs -/


set_option pp.beta true

namespace LoVe


/-! ## Question 1: Connectives and Quantifiers

1.1. Supply structured proofs of the following lemmas. -/

lemma I (a : Prop) :
  a → a :=
assume ha : a, 
show a, from ha

lemma K (a b : Prop) :
  a → b → b :=
assume ha : a,
assume hb : b,
show b, 
from hb

lemma C (a b c : Prop) :
  (a → b → c) → b → a → c :=
assume f : (a → b → c),
assume hb : b,
assume ha : a,
show c, 
from f ha hb

lemma proj_1st (a : Prop) :
  a → a → a :=
assume ha₁ : a,
assume ha₂ : a,
show a, 
from ha₁

/-! Please give a different answer than for `proj_1st`. -/

lemma proj_2nd (a : Prop) :
  a → a → a :=
assume ha₁ : a,
assume ha₂ : a,
show a, 
from ha₂ 

lemma some_nonsense (a b c : Prop) :
  (a → b → c) → a → (a → c) → b → c :=
assume f : a → b → c,
assume ha : a,
assume g : a → c,
assume hb : b,
show c, 
from f ha hb

/-! 1.2. Supply a structured proof of the contraposition rule. -/

lemma contrapositive (a b : Prop) :
  (a → b) → ¬ b → ¬ a :=
assume f : a → b,
assume hnb : ¬b,
assume ha : a,
have hb : b, from f ha,
show false, 
from hnb hb
  

/-! 1.3. Supply a structured proof of the distributivity of `∀` over `∧`. -/

lemma forall_and {α : Type} (p q : α → Prop) :
  (∀x, p x ∧ q x) ↔ (∀x, p x) ∧ (∀x, q x) :=
iff.intro 
  (assume hpq : ∀ x, p x ∧ q x, 
    show (∀ x, p x) ∧ (∀ x, q x), 
    from ⟨λ z, (hpq z).left, λ z, (hpq z).right⟩ ) 
  (assume hpandq : (∀ x, p x) ∧ (∀ x, q x), 
    show ∀ x, p x ∧ q x, 
    from λ z, ⟨ hpandq.left z, hpandq.right z⟩ )

/-! 1.4. Reuse, if possible, the lemma `forall_and` you proved above to prove
the following instance of the lemma. -/

lemma forall_and_inst {α : Type} (r s : α → α → Prop) :
  (∀x, r x x ∧ s x x) ↔ (∀x, r x x) ∧ (∀x, s x x) :=
iff.intro 
  (assume hrs : ∀ x, r x x ∧ s x x, 
    show (∀ x, r x x) ∧ (∀ x, s x x), 
    from ⟨ λ x, (hrs x).left, λ x, (hrs x).right⟩  )
  (assume hrands : (∀ x, r x x) ∧ (∀ x, s x x), 
    show ∀ x, r x x ∧ s x x, 
    from λ x, ⟨ hrands.left x,  hrands.right x ⟩ )  


/-! ## Question 2: Chain of Equalities

2.1. Write the following proof using `calc`.

      `(a + b) * (a + b)`
    `= a * (a + b) + b * (a + b)`
    `= a * a + a * b + b * a + b * b`
    `= a * a + a * b + a * b + b * b`
    `= a * a + 2 * a * b + b * b`

Hint: You might need the tactics `simp` and `cc` and the lemmas `mul_add`,
`add_mul`, and `two_mul`. -/

lemma binomial_square (a b : ℕ) :
  (a + b) * (a + b) = a * a + 2 * a * b + b * b :=
sorry

/-! 2.2. Prove the same argument again, this time as a structured proof. Try to
reuse as much of the above proof idea as possible. -/

lemma binomial_square₂ (a b : ℕ) :
  (a + b) * (a + b) = a * a + 2 * a * b + b * b :=
sorry

/-! 2.3. Prove the same lemma again, this time using tactics. -/

lemma binomial_square₃ (a b : ℕ) :
  (a + b) * (a + b) = a * a + 2 * a * b + b * b :=
begin
  sorry
end


/-! ## Question 3 (**optional**): One-Point Rules

3.1 (**optional**). Prove that the following wrong formulation of the one-point
rule for `∀` is inconsistent, using a structured proof. -/

axiom forall.one_point_wrong {α : Type} {t : α} {p : α → Prop} :
  (∀x : α, x = t ∧ p x) ↔ p t

lemma proof_of_false :
  false :=
sorry

/-! 3.2 (**optional**). Prove that the following wrong formulation of the
one-point rule for `∃` is inconsistent, using a tactical or structured proof. -/

axiom exists.one_point_wrong {α : Type} {t : α} {p : α → Prop} :
  (∃x : α, x = t → p x) ↔ p t

lemma proof_of_false₂ :
  false :=
sorry

end LoVe
