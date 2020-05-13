import .love09_hoare_logic_demo


/-! # LoVe Exercise 9: Hoare Logic -/


set_option pp.beta true

namespace LoVe


/-! ## Question 1: Program Verification

The following WHILE program is intended to compute the Gaussian sum up to `n`,
leaving the result in `r`. -/

def GAUSS : stmt :=
stmt.assign "r" (λs, 0) ;;
stmt.while (λs, s "n" ≠ 0)
  (stmt.assign "r" (λs, s "r" + s "n") ;;
   stmt.assign "n" (λs, s "n" - 1))

/-! The summation function: -/

def sum_upto : ℕ → ℕ
| 0       := 0
| (n + 1) := n + 1 + sum_upto n

#eval list.map sum_upto [5,4,3,2,1,0]

/- 
r = 0, n = 5, i=0, sum_upto 0 = 0
r = 5, n = 4, i=1, sum_upto 1 = 1
r = 9, n = 3, i=2, sum_upto 2 = 3
r = 12, n = 2,i=3, sum_upto 3 = 6
r = 14, n = 1,i=4, sum_upto 4 = 10
r = 15, n = 0.i=5, sum_upto 5 = 15
-/

/-! 1.1. Prove the correctness of `GAUSS` using `vcg`. The main challenge is to
figure out which invariant to use for the while loop. The invariant should
capture both the work that has been done already (the intermediate result) and
the work that remains to be done. -/

lemma GAUSS_correct (n₀ : ℕ) :
  {* λs, s "n" = n₀ *} GAUSS {* λs, s "r" = sum_upto n₀ *} :=
begin
  sorry,
end

/-! 1.2. The following WHILE program is intended to compute the product of `n`
and `m`, leaving the result in `r`. Prove its correctness using `vcg`.

Hint: If a variable `x` does not change in a program, it might be useful to
record this in the invariant, by adding a conjunct `s "x" = x₀`. -/

def MUL : stmt :=
stmt.assign "r" (λs, 0) ;;
stmt.while (λs, s "n" ≠ 0)
  (stmt.assign "r" (λs, s "r" + s "m") ;;
   stmt.assign "n" (λs, s "n" - 1))

lemma MUL_correct (n₀ m₀ : ℕ) :
  {* λs, s "n" = n₀ ∧ s "m" = m₀ *} MUL {* λs, s "r" = n₀ * m₀ *} :=
sorry


/-! ## Question 2: Hoare Triples for Total Correctness -/

def total_hoare (P : state → Prop) (S : stmt) (Q : state → Prop) : Prop :=
∀s, P s → ∃t, (S, s) ⟹ t ∧ Q t

notation `[* ` P : 1 ` *] ` S : 1 ` [* ` Q : 1 ` *]` :=
total_hoare P S Q

namespace total_hoare

/-! 2.1. Prove the consequence rule. -/
/- hEt : ∃ (t : state), (S, s) ⟹ t ∧ Q t,
  t0 : state,
  hSand : (S, s) ⟹ t0 ∧ Q t0,
  
  (hEt t0).right 

 -/
lemma consequence {P P' Q Q' : state → Prop} {S}
    (hS : [* P *] S [* Q *]) (hP : ∀s, P' s → P s) (hQ : ∀s, Q s → Q' s) :
  [* P' *] S [* Q' *] :=
fix s,
assume hP's : P' s, 
have hEt : ∃t, (S, s) ⟹ t ∧ Q t, from hS s (hP s hP's),
match hEt with
| ⟨t0,hSand⟩ := 
  have hQ't0 : Q' t0, from hQ t0 (hSand.right),
  exists.intro t0 ⟨hSand.left, hQ't0⟩ 
end

lemma tac_consequence {P P' Q Q' : state → Prop} {S}
  (hS : [* P *] S [* Q *]) (hP : ∀s, P' s → P s) (hQ : ∀s, Q s → Q' s) : 
  [* P' *] S [* Q' *] := 
begin
  intros s hP's,
  have hPs : P s :=  hP s hP's,
  have hex : ∃ (t : state), (S, s) ⟹ t ∧ Q t := hS s hPs,
  cases hex with t0 hand,
  have hQ' : Q' t0 := hQ t0 (hand.right),
  existsi t0,
  split,
  {
    exact hand.left,
  },
  {
    exact hQ',
  }
end

/-! 2.2. Prove the rule for `skip`. -/

lemma skip_intro {P} :
  [* P *] stmt.skip [* P *] :=
begin
  intros s hPs,
  existsi s,
  split,
  {
    apply big_step.skip,
  },
  {
    assumption,
  }
end

lemma fwd_skip_intro {P} : 
  [* P *] stmt.skip [* P *] := 
fix s,
assume hPs : P s , 
⟨ s, ⟨ big_step.skip, hPs⟩  ⟩ 

/-! 2.3. Prove the rule for `assign`. -/

lemma assign_intro {P : state → Prop} {x} {a : state → ℕ} :
  [* λs, P (s{x ↦ a s}) *] stmt.assign x a [* P *] :=
begin
  intros s hPs,
  existsi s{x ↦ a s},
  split,
  {
    simp,
  },
  {
    assumption,
  }
end

lemma fwd_assign_intro {P : state → Prop} {x} {a : state → ℕ} :
  [* λs, P (s{x ↦ a s}) *] stmt.assign x a [* P *] :=
fix s,
assume hPs : _, 
⟨ s{x ↦ a s}, ⟨ big_step.assign, hPs ⟩  ⟩ 

/-! 2.4. Prove the rule for `seq`. -/

lemma seq_intro {P Q R S T} (hS : [* P *] S [* Q *]) (hT : [* Q *] T [* R *]) :
  [* P *] S ;; T [* R *] :=
begin
  intros s hPs,
  have hSQ : _ := hS s hPs,
  cases hSQ with r hSQr,
  have hTR : _ := hT r hSQr.right,
  cases hTR with t hTRt,
  existsi t,
  split,
  {
    apply big_step.seq hSQr.left hTRt.left,
  },
  {
    exact hTRt.right,
  }
end

/-! 2.5. Complete the proof of the rule for `ite`.

Hint: This requires a case distinction on the truth value of `b s`. -/

lemma ite_intro {b P Q : state → Prop} {S T}
    (hS : [* λs, P s ∧ b s *] S [* Q *])
    (hT : [* λs, P s ∧ ¬ b s *] T [* Q *]) :
  [* P *] stmt.ite b S T [* Q *] :=
begin
  intros s hPs,
  cases classical.em (b s),
  {
    have hSQ : _ := hS s ⟨hPs, h⟩,
    cases hSQ with t hand,
    existsi t,
    split,
    {
      apply big_step.ite_true h hand.left,
    },
    {
      exact hand.right,
    }
  },
  {
    have hTQ : _ := hT s ⟨hPs, h⟩,
    cases hTQ with t hand,
    existsi t,
    split,
    {
      apply big_step.ite_false h hand.left,
    },
    {
      exact hand.right,
    }
  }
end

/-! 2.6 (**optional**). Try to prove the rule for `while`.

The rule is parameterized by a loop invariant `I` and by a variant `V` that
decreases with each iteration of the loop body.

Before we prove the desired lemma, we introduce an auxiliary lemma. Its proof
requires well-founded induction. When using `while_intro.aux` as induction
hypothesis we recommend to do it directly after proving that the argument is
less than `v₀`:

    have ih : ∃u, (stmt.while b S, t) ⟹ u ∧ I u ∧ ¬ b u :=
      have V t < v₀ :=
        …,
      while_intro.aux (V t) …,

Similarly to `ite`, the proof requires a case distinction on `b s ∨ ¬ b s`. -/

lemma while_intro.aux {b : state → Prop} (I : state → Prop) (V : state → ℕ) {S}
  (h_inv : ∀v₀, [* λs, I s ∧ b s ∧ V s = v₀ *] S [* λs, I s ∧ V s < v₀ *]) :
  ∀v₀ s, V s = v₀ → I s → ∃t, (stmt.while b S, s) ⟹ t ∧ I t ∧ ¬ b t
| v₀ s V_eq hs :=
sorry

lemma while_intro {b : state → Prop} (I : state → Prop) (V : state → ℕ) {S}
  (hinv : ∀v₀, [* λs, I s ∧ b s ∧ V s = v₀ *] S [* λs, I s ∧ V s < v₀ *]) :
  [* I *] stmt.while b S [* λs, I s ∧ ¬ b s *] :=
sorry

end total_hoare

end LoVe
