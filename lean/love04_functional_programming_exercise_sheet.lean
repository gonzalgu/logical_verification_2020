import .love03_forward_proofs_demo


/-! # LoVe Exercise 4: Functional Programming -/


set_option pp.beta true

namespace LoVe


/-! ## Question 1: Reverse of a List

We define a new accumulator-based version of `reverse`. The first argument,
`as`, serves as the accumulator. This definition is __tail-recursive__, meaning
that compilers and interpreters can easily optimize the recursion away,
resulting in more efficient code. -/

def accurev {α : Type} : list α → list α → list α
| as []        := as
| as (x :: xs) := accurev (x :: as) xs

/-! 1.1. Our intention is that `accurev [] xs` should be equal to `reverse xs`.
But if we start an induction, we quickly see that the induction hypothesis is
not strong enough. Start by proving the following generalization (using the
`induction` tactic or pattern matching): -/

lemma accurev_eq_reverse_append {α : Type} :
  ∀as xs : list α, accurev as xs = reverse xs ++ as 
| [] [] := by refl
| _ [] := by refl
| [] (x::xs) := 
  begin
    simp [accurev, reverse],
    apply accurev_eq_reverse_append,
  end
| (a::as) (x::xs) := 
  begin
    simp [accurev, reverse],
    apply accurev_eq_reverse_append,
  end
/-! 1.2. Derive the desired equation. -/

lemma accurev_eq_reverse {α : Type} (xs : list α) :
  accurev [] xs = reverse xs :=
begin
  induction xs with x xs ih,
  { refl },
  { 
    simp [accurev,reverse],
    apply accurev_eq_reverse_append
  },  
end

/-! 1.3. Prove the following property.

Hint: A one-line inductionless proof is possible. -/

lemma accurev_accurev {α : Type} (xs : list α) :
  accurev [] (accurev [] xs) = xs := 
begin
  repeat {rw accurev_eq_reverse},
  apply reverse_reverse,  
end

/-! 1.4. Prove the following lemma by structural induction, as a "paper" proof.
This is a good exercise to develop a deeper understanding of how structural
induction works (and is good practice for the final exam).

    lemma accurev_eq_reverse_append {α : Type} :
      ∀as xs : list α, accurev as xs = reverse xs ++ as

Guidelines for paper proofs:

We expect detailed, rigorous, mathematical proofs. You are welcome to use
standard mathematical notation or Lean structured commands (e.g., `assume`,
`have`, `show`, `calc`). You can also use tactical proofs (e.g., `intro`,
`apply`), but then please indicate some of the intermediate goals, so that we
can follow the chain of reasoning.

Major proof steps, including applications of induction and invocation of the
induction hypothesis, must be stated explicitly. For each case of a proof by
induction, you must list the inductive hypotheses assumed (if any) and the goal
to be proved. Minor proof steps corresponding to `refl`, `simp`, or `cc` need
not be justified if you think they are obvious (to humans), but you should say
which key lemmas they depend on. You should be explicit whenever you use a
function definition or an introduction rule for an inductive predicate. -/

-- enter your paper proof here
lemma accurev_eq_reverse_append₂ { α : Type } : 
  ∀ as xs : list α, accurev as xs = reverse xs ++ as
-- the proof proceeds by induction on as and xs 
| []  []  := 
  -- when as = [] and xs = [], we have accurev [][] = reverse [] ++ []
  -- which is reduced to [] = [] ++ [] 
  -- which is trivial by computation.
  begin
    rw accurev,
    rw reverse,
    refl,
  end
| []     (x::xs) := 
  begin
    -- when as = [] and ys = (x::xs)
    -- we need to prove accurev [] (x::xs) = reverse (x::xs) ++ []
    -- by computation we have
    -- accurev [x] xs = reverse xs ++ [x]
    -- to which we can apply the inductive hypothesis
    --ih : ∀ xs, accurev [] xs = reverse xs ++ []
    rw accurev,
    rw reverse,
    simp,
    --apply inductive hypothesis
    apply accurev_eq_reverse_append₂ [x] xs,
  end
| (a::as)  [] := 
  begin
    -- this case is trivial by computation.
    --ih : ∀ as xs, accurev as xs = reverse xs ++ as
    rw accurev,
    rw reverse,
    refl,
  end
| (a::as) (x::xs) := 
  begin
    simp [accurev, reverse],
    -- apply inductive hypothesis
    apply accurev_eq_reverse_append₂,
  end





/-! ## Question 2: Drop and Take

The `drop` function removes the first `n` elements from the front of a list. -/

def drop {α : Type} : ℕ → list α → list α
| 0       xs        := xs
| (_ + 1) []        := []
| (m + 1) (x :: xs) := drop m xs

/-! Its relative `take` returns a list consisting of the the first `n` elements
at the front of a list.

2.1. Define `take`.

To avoid unpleasant surprises in the proofs, we recommend that you follow the
same recursion pattern as for `drop` above. -/

def take {α : Type} : ℕ → list α → list α 
| 0       _         := []
| (_ + 1) []        := []
| (m + 1) (x :: xs) := x :: take m xs 

#eval take 0 [3, 7, 11]   -- expected: []
#eval take 1 [3, 7, 11]   -- expected: [3]
#eval take 2 [3, 7, 11]   -- expected: [3, 7]
#eval take 3 [3, 7, 11]   -- expected: [3, 7, 11]
#eval take 4 [3, 7, 11]   -- expected: [3, 7, 11]

#eval take 2 ["a", "b", "c"]   -- expected: ["a", "b"]

/-! 2.2. Prove the following lemmas, using `induction` or pattern matching.
Notice that they are registered as simplification rules thanks to the `@[simp]`
attribute. -/

@[simp] lemma drop_nil {α : Type} :
  ∀n : ℕ, drop n ([] : list α) = [] :=
begin
  intro n,
  induction n with k ih,
  { refl },
  refl,
  --simp [drop, ih],
end

lemma drop_nil₂ {α : Type} : 
  ∀ n : ℕ, drop n ([] : list α) = []
| 0 := by refl
| (k+1) := by refl

@[simp] lemma take_nil {α : Type} :
  ∀n : ℕ, take n ([] : list α) = [] :=
begin
  intro n,  
  induction n with k ih,
  { refl },
  refl,
end

lemma take_nil₂ {α : Type} : 
  ∀ n : ℕ, take n ([] : list α) = [] 
| 0     := by refl
| (k+1) := by refl

/-! 2.3. Follow the recursion pattern of `drop` and `take` to prove the
following lemmas. In other words, for each lemma, there should be three cases,
and the third case will need to invoke the induction hypothesis.

The first case is shown for `drop_drop`. Beware of the fact that there are three
variables in the `drop_drop` lemma (but only two arguments to `drop`).

Hint: The `refl` tactic might be useful in the third case of `drop_drop`. -/

lemma drop_drop {α : Type} :
  ∀(m n : ℕ) (xs : list α), drop n (drop m xs) = drop (n + m) xs
| 0         n          xs := by refl
| m         0          xs := by simp[drop]
| (m+1) (n+1)          [] := by refl
| (m+1) (n+1)   (x::xs) := 
  begin
    simp [drop, drop_drop],
    refl,   
  end



-- supply the two missing cases here

lemma take_take {α : Type} :
  ∀(m : ℕ) (xs : list α), take m (take m xs) = take m xs 
| 0       xs    := 
  begin
    refl,
  end
| (k+1)   []    := 
  begin
    refl,
  end
| (k+1) (x::xs) :=
  begin
    simp [take, take_take],    
  end

lemma take_drop {α : Type} :
  ∀(n : ℕ) (xs : list α), take n xs ++ drop n xs = xs 
| 0       xs := 
  begin
    refl,
  end
| (k+1)   [] := 
  begin
    refl,
  end
| (k+1) (x :: xs) := 
  begin
    simp [take,drop, take_drop],
    /-
    rw take,
    rw drop,
    simp,
    apply take_drop, -/
  end




/-! ## Question 3: A Type of λ-Terms

3.1. Define an inductive type corresponding to the untyped λ-terms, as given
by the following context-free grammar:

    term ::= 'var' string        -- variable (e.g., `x`)
           | 'lam' string term   -- λ-expression (e.g., `λx, t`)
           | 'app' term term     -- application (e.g., `t u`) -/

/-
inductive list (T : Type u)
| nil {} : list
| cons (hd : T) (tl : list) : list
-/

-- enter your definition here
inductive term  
| var (name : string) : term
| lam (v : string) (body : term) : term
| app (e₁ : term) (e₂ : term) : term
/-! 3.2. Register a textual representation of the type `term` as an instance of
the `has_repr` type class. Make sure to supply enough parentheses to guarantee
that the output is unambiguous. -/

def term.repr : term → string
| (term.var n) := n
| (term.lam v b) := "(λ" ++ v ++ ", " ++ term.repr b ++ ")"
| (term.app e₁ e₂) := "(" ++ term.repr e₁ ++ " " ++ term.repr e₂ ++ ")"
-- enter your answer here

@[instance] def term.has_repr : has_repr term :=
{ repr := term.repr }

/-! 3.3. Test your textual representation: -/

#eval (term.lam "x" (term.app (term.app (term.var "y") (term.var "x"))
    (term.var "x")))
  -- should print something like `(λx, ((y x) x))`

end LoVe
