variable {p q : Prop}

-- First, if we know a proposition (p ∨ q)
-- has been proved to be true, and once we
-- have proved (¬q), we must have (p).
example (hpq : p ∨ q) (hnq : ¬q) : p := by
  apply Or.elim hpq
  · intro p
    exact p
  · intro hq
    contradiction

-- "I don't know exactly Riemann Hypothesis
-- / Goldbach Conjecture / blablabla, but
-- I know it is either true or false."
--
-- This maybe a claim that widely accepted by
-- classical mathematicians / under classical
-- logic. That is, given a proposition
-- (p : Prop), they postulate that
-- (p ∨ ¬p) is true. This is usually called
-- the Law of Excluded Middle (LEM).
def LEM := ∀ (p : Prop), (p ∨ ¬p)

-- Law of excluded middle is useful. For
-- example, it allow us to prove by
-- contrapositive, which is used
-- extensively in classical logic.
example (hLEM : LEM) : (¬q → ¬p) → (p → q) := by
  intro hnqnp
  intro hp
  have hqnq : (q ∨ ¬q) := hLEM q
  apply Or.elim hqnq
  · intro hq
    exact hq
  · intro hnq
    exfalso
    have : ¬p := hnqnp hnq
    contradiction

-- On the other hand, in classical logic,
-- we widely accept that if we can prove
-- not not p, then we can prove p. That
-- is, given a proof of (hnn : ¬¬p), we
-- obtain a proof of (h : p). This is
-- usually called the law of Double
-- Negation Elimination (DNE).
def DNE := ∀ (p : Prop), (¬¬p → p)

-- It's sometimes written as (¬¬p ↔ p).
-- But I would say (p → ¬¬p) is
-- trivially provable.
theorem p_then_not_not_p : (p → ¬¬p) := by
  intro hp
  intro hnp
  contradiction

-- And (¬¬p ↔ p) and (¬¬p → p) are
-- fundamentally equivalent, but I
-- would preserve the direction from
-- ¬¬p to p to emphasize the process
-- of "elimination".
def DNE' := (∀ (p : Prop), ¬¬p ↔ p)
example : DNE' ↔ DNE := by
  apply Iff.intro
  · intro h p
    exact (h p).mp
  · intro hDNE p
    apply Iff.intro
    · exact hDNE p
    · exact p_then_not_not_p

-- Actually, with LEM, we can easily
-- qualify DNE.
theorem DNE_if_LEM : LEM → DNE := by
  intro hLEM
  intro p hnn
  have hpnp : p ∨ ¬p := hLEM p
  apply Or.elim hpnp
  · intro hp
    exact hp
  · intro hnp
    exfalso
    contradiction

-- On the other hand, once we accept
-- DNE, we do filthily accept LEM then.
--
-- To show, I have to mention that
-- ¬(p ∨ ¬p) will NEVER be true.
theorem not_p_or_not_p_impossible: ¬¬(p ∨ ¬p) := by
  intro hnpnp
  -- We can prove ¬p is true, since
  -- it's fundamentally p → False,
  -- given that it provides a proof
  -- of hp, it can be used to constuct
  -- a contradiction.
  have hnp : ¬p := by
    intro hp
    have : p ∨ ¬p := Or.inl hp
    contradiction
  -- However, it's still a contradictino
  -- since ¬p is true this time.
  have : p ∨ ¬p := Or.inr hnp
  contradiction

-- Then just apply DNE and we are done.
theorem LEM_if_DNE : DNE → LEM := by
  intro hDNE p
  have hnnLEM := not_p_or_not_p_impossible (p := p)
  exact hDNE (p ∨ ¬p) hnnLEM

-- Yes, DNE and LEM are fundamentally
-- equivalent. Assuming we can remove
-- double negation is equivalent to
-- assuming we know a proposition p
-- is either true or false before hand.
example : DNE ↔ LEM := by
  apply Iff.intro
  · exact LEM_if_DNE
  · exact DNE_if_LEM

-- However, it should also be mention
-- that it's safe to remove the leading
-- two negations when there are three or
-- more leading negations. We just can't
-- reduce it to zero.
example : ¬¬¬p → ¬p := by
  intro hnnn h
  have hnn := p_then_not_not_p h
  contradiction
