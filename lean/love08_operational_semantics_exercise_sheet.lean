import .love08_operational_semantics_demo


/-! # LoVe Exercise 8: Operational Semantics -/


set_option pp.beta true

namespace LoVe


/-! ## Question 1: Program Equivalence

For this question, we introduce the notion of program equivalence: `S₁ ≈ S₂`. -/

def big_step_equiv (S₁ S₂ : stmt) : Prop :=
∀s t, (S₁, s) ⟹ t ↔ (S₂, s) ⟹ t

infix ` ≈ ` := big_step_equiv

/-! Program equivalence is a equivalence relation, i.e., it is reflexive,
symmetric, and transitive. -/

@[refl] lemma big_step_equiv.refl {S : stmt} :
  S ≈ S :=
fix s t,
show (S, s) ⟹ t ↔ (S, s) ⟹ t, from
  by refl

@[symm] lemma big_step_equiv.symm {S₁ S₂ : stmt}:
  S₁ ≈ S₂ → S₂ ≈ S₁ :=
assume h : S₁ ≈ S₂,
fix s t,
show (S₂, s) ⟹ t ↔ (S₁, s) ⟹ t, from
  iff.symm (h s t)

@[trans] lemma big_step_equiv.trans {S₁ S₂ S₃ : stmt} (h₁₂ : S₁ ≈ S₂)
    (h₂₃ : S₂ ≈ S₃) :
  S₁ ≈ S₃ :=
fix s t,
show (S₁, s) ⟹ t ↔ (S₃, s) ⟹ t, from
  iff.trans (h₁₂ s t) (h₂₃ s t)


/-! 1.1. Prove the following program equivalences. -/

lemma big_step_equiv.skip_assign_id {x} :
  stmt.assign x (λs, s x) ≈ stmt.skip :=
begin
  unfold big_step_equiv,
  intros s t,
  apply iff.intro,
  {
    intro h,
    apply big_step_skip_iff.mpr,
    have h2 : t = s{x ↦ s x} := big_step_assign_iff.mp h,
    rw h2,
    simp,       
  },
  {
    intro h,
    apply big_step_assign_iff.mpr,
    have h2 :  t = s := big_step_skip_iff.mp h,
    rw h2,
    simp,    
  }
end

lemma big_step_equiv.skip_assign_id₂ {x} :
  stmt.assign x (λs, s x) ≈ stmt.skip :=
fix s t, 
iff.intro 
  (assume h : (stmt.assign x (λ (s : state), s x), s) ⟹ t,
  have h₂ : t = s{x ↦ (λ (s : state), s x) s}, 
  from (big_step_assign_iff.mp h),
  show (stmt.skip, s) ⟹ t, 
  from by simp [h₂]) 
  (assume h : (stmt.skip, s) ⟹ t, 
  have hst : t = s, from big_step_skip_iff.mp h,
  by simp [hst])



lemma big_step_equiv.seq_skip_left {S : stmt} :
  stmt.skip ;; S ≈ S :=
begin
  unfold big_step_equiv,
  intros s t,
  apply iff.intro,
  {
    intro h,
    cases h,
    cases h_hS,
    assumption,
  },
  {
    intro h,
    apply big_step_seq_iff.mpr,
    existsi s,
    split,
    {
      apply big_step_skip_iff.mpr,
      refl,
    },
    {
      assumption,
    }
  } 
end

lemma big_step_equiv.seq_skip_right {S : stmt} :
  S ;; stmt.skip ≈ S :=
begin
  unfold big_step_equiv,
  intros s t,
  apply iff.intro,
  {
    intro h,
    cases h,
    cases h_hT,
    assumption,
  },
  {
    intro h,
    apply big_step_seq_iff.mpr,
    existsi t,
    split,
    {
      assumption,
    },
    {
      apply big_step_skip_iff.mpr,
      refl,
    }
  }
end

lemma big_step_equiv.ite_seq_while {b} {S : stmt} :
  stmt.ite b (S ;; stmt.while b S) stmt.skip ≈ stmt.while b S :=
begin
  unfold big_step_equiv,
  intros s t,
  apply iff.intro,
  {
    intro h,
    cases h,
    {
      cases h_hbody,
      apply (big_step_while_true_iff h_hcond).mpr,
      existsi h_hbody_t,
      split,
      {
        assumption,
      },
      {
        assumption,
      }
    },
    {
      cases h_hbody,
      apply (big_step_while_false_iff h_hcond).mpr,
      refl,
    }
  },
  {
    intro h,
    cases h,
    {
      apply big_step.ite_true h_hcond _,
      apply big_step.seq h_hbody h_hrest,      
    },
    {
      apply big_step.ite_false h_hcond _,
      simp,
    }
  }
end

/-! 1.2. Program equivalence can be used to replace subprograms by other
subprograms with the same semantics. Prove the following so-called congruence
rules: -/

lemma big_step_equiv.seq_congr {S₁ S₂ T₁ T₂ : stmt} (hS : S₁ ≈ S₂)
    (hT : T₁ ≈ T₂) :
  S₁ ;; T₁ ≈ S₂ ;; T₂ :=
begin
  unfold big_step_equiv,
  intros s t,
  apply iff.intro,
  {
    intro h,
    cases h,
    unfold big_step_equiv at hS hT,
    have h_hS₂ : (S₂, s) ⟹ h_t := (hS s h_t).mp h_hS,
    have h_hT₂ : (T₂, h_t) ⟹ t := (hT h_t t).mp h_hT,
    apply big_step.seq h_hS₂,
    assumption,    
  },
  {
    intro h,
    cases h,
    unfold big_step_equiv at hS hT,
    have h_hS₁ : (S₁, s) ⟹ h_t := (hS s h_t).mpr h_hS,
    have h_hT₁ : (T₁, h_t) ⟹ t := (hT h_t t).mpr h_hT,
    apply big_step.seq h_hS₁,
    assumption,
  }
end

lemma big_step_equiv.ite_congr {b} {S₁ S₂ T₁ T₂ : stmt} (hS : S₁ ≈ S₂)
    (hT : T₁ ≈ T₂) :
  stmt.ite b S₁ T₁ ≈ stmt.ite b S₂ T₂ :=
begin
  unfold big_step_equiv,
  intros s t,
  apply iff.intro,
  {
    intro h,
    cases h,
    {
      apply big_step.ite_true h_hcond,
      unfold big_step_equiv at hS,
      apply (hS s t).mp,
      assumption,
    },
    {
      apply big_step.ite_false h_hcond,
      unfold big_step_equiv at hT,
      apply (hT s t).mp,
      assumption,
    }
  },
  {
    intro h,
    cases h,
    {
      apply big_step.ite_true h_hcond,
      unfold big_step_equiv at hS,
      apply (hS s t).mpr,
      assumption,
    },
    {
      apply big_step.ite_false h_hcond,
      unfold big_step_equiv at hT,
      apply (hT s t).mpr,
      assumption,
    }
  }
end

/-! 1.3 (**optional**): Prove one more congruence rule. This one is more
difficult. -/

lemma denote_equiv.while_congr {b} {S₁ S₂ : stmt} (hS : S₁ ≈ S₂) :
  stmt.while b S₁ ≈ stmt.while b S₂ :=
begin
  unfold big_step_equiv,
  intros s t,
  apply iff.intro,
  {
    intro h,    
    cases h,
    apply (big_step_while_true_iff h_hcond).mpr,
    existsi h_t,
    split,
    {
      apply (hS _ _).mp,
      assumption,
    },
    sorry,
  },
  sorry,
end


/-! ## Question 2: Guarded Command Language (GCL)

In 1976, E. W. Dijkstra introduced the guarded command language, a
minimalistic imperative language with built-in nondeterminism. A grammar for one
of its variants is given below:

    S  ::=  x := e       -- assignment
         |  assert b     -- assertion
         |  S ; S        -- sequential composition
         |  S | ⋯ | S    -- nondeterministic choice
         |  loop S       -- nondeterministic iteration

Assignment and sequential composition are as in the WHILE language. The other
statements have the following semantics:

* `assert b` aborts if `b` evaluates to false; otherwise, the command is a
  no-op.

* `S | ⋯ | S` chooses any of the branches and executes it, ignoring the other
  branches.

* `loop S` executes `S` any number of times.

In Lean, GCL is captured by the following inductive type: -/

namespace gcl

inductive stmt (σ : Type) : Type
| assign : string → (σ → ℕ) → stmt
| assert : (σ → Prop) → stmt
| seq    : stmt → stmt → stmt
| choice : list stmt → stmt
| loop   : stmt → stmt

infixr ` ;; ` : 90 := stmt.seq

/-! The parameter `σ` abstracts over the state type. It is necessary as a work
around for a Lean bug.

The big-step semantics is defined as follows: -/

inductive big_step : (stmt state × state) → state → Prop
| assign {x a s} :
  big_step (stmt.assign x a, s) (s{x ↦ a s})
| assert {b : state → Prop} {s} (hcond : b s) :
  big_step (stmt.assert b, s) s
| seq {S T s t u} (h₁ : big_step (S, s) t) (h₂ : big_step (T, t) u) :
  big_step (S ;; T, s) u
| choice {Ss s t} (i) (hless : i < list.length Ss)
    (hbody : big_step (list.nth_le Ss i hless, s) t) :
  big_step (stmt.choice Ss, s) t
| loop_base {S s} :
  big_step (stmt.loop S, s) s
| loop_step {S s u} (t) (hbody : big_step (S, s) t)
    (hrest : big_step (stmt.loop S, t) u) :
  big_step (stmt.loop S, s) u

infix ` ⟹ ` : 110 := big_step

/-! 2.1. Prove the following inversion rules, as we did in the lecture for the
WHILE language. -/

@[simp] lemma big_step_assign_iff {x a s t} :
  (stmt.assign x a, s) ⟹ t ↔ t = s{x ↦ a s} :=
begin
  apply iff.intro,
  {
    intro h,
    cases h,
    refl,
  },
  {
    intro h,
    rw h,
    exact big_step.assign,
  }
end


@[simp] lemma big_step_assert {b s t} :
  (stmt.assert b, s) ⟹ t ↔ t = s ∧ b s :=
begin
  apply iff.intro,
  {
    intro hassert,
    cases hassert,
    split,
    {
      refl,
    },
    {
      assumption,
    }
  },
  {
    intro hts_bs,
    cases hts_bs with hts hassert,
    rw hts,
    apply big_step.assert hassert,
  }
end

@[simp] lemma big_step_seq_iff {S₁ S₂ s t} :
  (stmt.seq S₁ S₂, s) ⟹ t ↔ (∃u, (S₁, s) ⟹ u ∧ (S₂, u) ⟹ t) :=
begin
  apply iff.intro,
  {
    intro hseq,
    cases hseq,
    existsi hseq_t,
    split;assumption,     
  },
  {
    intro hexistsu,
    cases hexistsu with st hS₁_S₂,
    cases hS₁_S₂ with hS₁ hS₂,   
    apply big_step.seq hS₁ hS₂,
  }
end

lemma big_step_loop {S s u} :
  (stmt.loop S, s) ⟹ u ↔
  (s = u ∨ (∃t, (S, s) ⟹ t ∧ (stmt.loop S, t) ⟹ u)) :=
begin
  apply iff.intro,
  {
    intro hloop,
    cases hloop,
    {
      left,
      refl,
    },
    {
      right,
      existsi hloop_t,
      split,
      {
        assumption,
      },
      {
        assumption,
      }
    }
  },
  {
    intro hor,
    cases hor,
    {
      rw hor,
      apply big_step.loop_base,
    },
    {
        cases hor with st hand,
        cases hand,
        apply big_step.loop_step st hand_left hand_right,        
    }
  }
end

@[simp] lemma big_step_choice {Ss s t} :
  (stmt.choice Ss, s) ⟹ t ↔
  (∃(i : ℕ) (hless : i < list.length Ss),
     (list.nth_le Ss i hless, s) ⟹ t) :=
begin
  apply iff.intro,
  {
    intro hchoice,
    cases hchoice,
    existsi hchoice_i,
    existsi hchoice_hless,
    assumption,      
  },
  {
    intro hexists,
    cases hexists with n hexists,
    cases hexists with hless hnth,
    apply big_step.choice n hless hnth,
  }
end

end gcl

/-! 2.2. Complete the translation below of a deterministic program to a GCL
program, by filling in the `sorry` placeholders below. -/

def gcl_of : stmt → gcl.stmt state
| stmt.skip         := gcl.stmt.assert (λ_, true)
| (stmt.assign x a) := gcl.stmt.assign x a
  
| (S ;; T)          := gcl.stmt.seq (gcl_of S) (gcl_of T)
| (stmt.ite b S T)  := gcl.stmt.choice [ 
  gcl.stmt.seq (gcl.stmt.assert b) (gcl_of S), 
  gcl_of T]
  
| (stmt.while b S)  :=
  gcl.stmt.loop (gcl.stmt.seq (gcl.stmt.assert b) (gcl_of S))

/-! 2.3. In the definition of `gcl_of` above, `skip` is translated to
`assert (λ_, true)`. Looking at the big-step semantics of both constructs, we
can convince ourselves that it makes sense. Can you think of other correct ways
to define the `skip` case? -/

-- enter your answer here

end LoVe
