import .love11_logical_foundations_of_mathematics_demo


/-! # LoVe Exercise 11: Logical Foundations of Mathematics -/


set_option pp.beta true

namespace LoVe


/-! ## Question 1: Vectors as Subtypes

Recall the definition of vectors from the demo: -/

#check vector

/-! The following function adds two lists of integers elementwise. If one
function is longer than the other, the tail of the longer function is
truncated. -/

def list.add : list ℤ → list ℤ → list ℤ
| []        []        := []
| (x :: xs) (y :: ys) := (x + y) :: list.add xs ys
| []        (y :: ys) := []
| (x :: xs) []        := []

/-! 1.1. Show that if the lists have the same length, the resulting list also
has that length. -/

lemma list.length_add :
  ∀(xs : list ℤ) (ys : list ℤ) (h : list.length xs = list.length ys),
    list.length (list.add xs ys) = list.length xs
| []        []        :=
  begin
    simp,
    refl,
  end
| (x :: xs) (y :: ys) :=
  begin
    simp,
    intro h,
    rw list.add,
    rw list.length,
    simp,
    apply list.length_add,
    exact h,
  end
| []        (y :: ys) :=
  begin
    simp,
    intro h,
    refl,
  end
| (x :: xs) []        :=
  begin
    simp,
  end

/-! 1.2. Define componentwise addition on vectors using `list.add` and
`length.length_add`. -/

def vector.add {n : ℕ} : vector ℤ n → vector ℤ n → vector ℤ n :=
λ v1 v2, subtype.mk (list.add (subtype.val v1) (subtype.val v2)) 
  begin
    have hl1 : (list.length v1.val) = n := 
    begin
      apply subtype.property v1,
    end,
    have hl2 : (list.length v2.val) = n := 
    begin
      apply subtype.property v2,
    end,
    rw list.length_add,
    {
      assumption,
    },
    {
      cc,
    }    
  end

/-! 1.3. Show that `list.add` and `vector.add` are commutative. -/

lemma list.add.comm :
  ∀(xs : list ℤ) (ys : list ℤ), list.add xs ys = list.add ys xs 
| [] [] := 
  begin
    refl,
  end
| (x::xs) [] := 
  begin
    repeat { rw list.add},    
  end
| []      (y::ys) := 
  begin
    repeat { rw list.add},
  end
| (x::xs) (y::ys) := 
  begin
    rw list.add,
    rw list.add,
    rw add_comm,
    simp,
    apply list.add.comm,
  end


lemma vector.add.comm {n : ℕ} (x y : vector ℤ n) :
  vector.add x y = vector.add y x :=
begin
  apply subtype.eq,
  simp [vector.add],
  apply list.add.comm,
end


/-! ## Question 2: Integers as Quotients

Recall the construction of integers from the lecture, not to be confused with
Lean's predefined type `int` (= `ℤ`): -/

#check int.rel
#check int.rel_iff
#check int

/-! 2.1. Define negation on these integers. -/

def int.neg : int → int :=
quotient.lift (λ p : ℕ × ℕ, ⟦ (p.snd, p.fst)⟧)
  begin
    intros a b,
    intro h,
    apply quotient.sound,
    
    rw int.rel_iff at *,
    simp,
    rw h,    
  end

/-! 2.2. Prove the following lemmas about negation. -/

lemma int.neg_eq (p n : ℕ) :
  int.neg ⟦(p, n)⟧ = ⟦(n, p)⟧ :=
begin
  simp [int.neg],
end

lemma int.neg_neg (a : int) :
  int.neg (int.neg a) = a :=
begin
  apply quotient.induction_on a,
  intro pn,
  cases pn with p n,
  rw int.neg_eq,
  rw int.neg_eq,  
end

end LoVe
