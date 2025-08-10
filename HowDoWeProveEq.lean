-- Proving equality is inevitable in Lean4, in this
-- file, we will demonstrate how do we prove some of
-- the most common objects to be equal.
--
-- I will first demonstrate how these proofs can
-- be done in principle, without using simp which
-- may hide some rewrite steps and makes Lean
-- mysterious / an oracle to us. Then I will show
-- the much simpler methods we are using in this
-- project, given that proving equality is generally
-- trivial and non-appealing to most users.

universe u
variable {α β : Type u}

-- Principly speaking, given lhs and rhs expressions
-- connected by equal sign, such that lhs and rhs are
-- the same expression, can be proved using rfl directly.
example {a : α} : a = a := by rfl

example {a b c : α} [Add α] : a + b + c = a + b + c := by rfl

-- Tactic rfl is usually the last step of those proofs
-- by reducing expressions to lhs = rhs.
example {a b : α} {f : α → β} : (a = b) → (f a = f b) := by
  intro h
  rewrite [h]
  rfl
  -- or rw [h], which will automatically tries to apply
  -- rfl after substitution.

-- The structures are defined to be equal if every
-- fields are equal.
structure Structure (α β : Type u) where
  a : α
  b : β

-- Let's have a look at a tedious but relatively
-- easy to comprehend way at first.
example (a b : Structure α β) :
  (a = b) ↔ (a.a = b.a) ∧ (a.b = b.b) := by
  apply Iff.intro
  · -- ⇒: simply substituting the objects in
    -- will complete the work.
    intro hab
    rw [hab]

    -- There're many ways to show
    -- (b.a = b.a) ∨ (b.b = b.b), just
    -- pick up the one you like.
    --
    -- constructor <;> rfl
    --
    -- apply And.intro
    -- · rfl
    -- · rfl
    --
    exact And.intro rfl rfl
  · -- ⇐: constructing the fields to its
    -- original one is more verbose.
    intro ha

    -- This will force Lean to unfold the
    -- hypothesis bound to a and b.
    rcases a with ⟨aa, ab⟩
    rcases b with ⟨ba, bb⟩

    -- You may use change to simplify ha
    -- manually, or use simp at ha.
    change (aa = ba) ∧ (ab = bb) at ha
    --simp at ha

    -- Now decompose ha into its component
    -- statements and rewrite the goal, and
    -- we are done with the proof.
    rcases ha with ⟨ha, hb⟩
    rw [ha, hb]

-- My recommended way, just unroll the
-- Structure and let Lean's simplifier tactic
-- to do the work for you. This is okay since
-- most people won't care about why two
-- structures are logically equal.
example (a b : Structure α β) :
  (a = b) ↔ (a.a = b.a) ∧ (a.b = b.b) := by
  rcases a with ⟨aa, ab⟩
  rcases b with ⟨ba, bb⟩
  -- WARN: single simp won't help, it will say
  -- "simp made no progress"
  simp

example (a b : Structure α β) :
  (a = b) ↔ (a.a = b.a) ∧ (a.b = b.b) := by
  -- The same as the one above actually.
  cases a
  cases b
  simp


-- The cartesian product of two types is nothing
-- more than a structure in the form of
--
-- structure CartesianProduct (α β : Type u) where
--  fst: α
--  snd: β
--
-- So the technique applicable to the structure
-- is naturally applicable to them.
example (a b : α × β) :
  (a = b) ↔ (a.fst = b.fst) ∧ (a.snd = b.snd) := by
  cases a
  cases b
  simp


-- Proving two functions to be equal are relatively
-- easy. Definitionally, two functions are equal
-- when they yields the same result for every input.
example (f g : α → β) :
  (∀ x, f x = g x) ↔ (f = g) := by
  apply Iff.intro
  · intro h
    funext x
    exact h x
  · intro h x
    rw [h]


-- The proof is more subtle when it involves a
-- proof of proposition about a.
structure ElemWithProof (α : Type u) (p: α → Prop) where
  elem : α
  proof : p elem

-- Remember, in Lean, every two proofs for the
-- same proposition are viewed as equal, so two
-- such structures are the same whenever the
-- element field are the same. But there's a
-- tricky stuff here, we will see.
example {p : α → Prop} (a b : ElemWithProof α p) :
  (a = b) ↔ (a.elem = b.elem) := by
  apply Iff.intro
  · -- ⇒ : Substituting a with b suffices.
    intro h
    rw [h]
  · -- ⇐ : Now comes the subtle part.
    intro h

    -- Decompose the structures, just like
    -- what we've done before.
    rcases a with ⟨a', pa'⟩
    rcases b with ⟨b', pb'⟩
    change a' = b' at h
    -- simp at h

    -- It's true that two proof of the same
    -- proposition are viewed as the same,
    -- but we can see pa' is p a', and
    -- pb' is p b'. That is, they are bound
    -- to different elements. To solve
    -- this problem, we will need to use subst.
    subst h
    -- We can see now the rhs has
    -- elem := a' and proof := pb', however
    -- pb' is of type p a' now. Since both
    -- pa' and pb' are the proof of the
    -- same proposition, we can use rfl
    -- to conclude this goal.
    rfl

-- Interestingly, the cases-then-simp method
-- is also applicable to this kind of proof.
example {p : α → Prop} (a b : ElemWithProof α p) :
  (a = b) ↔ (a.elem = b.elem) := by
  cases a
  cases b
  simp


-- Propositions themselves are also types, so
-- we are basically proving equality of types now.
example {p : α → Prop} (a b : α) :
  (a = b) → (p a = p b) := by
  intro hab
  rw [hab]


-- Inductive types are fundamentally a type
-- formed by constructor(s) mapping their input
-- into disjoint ranges injectively, and then
-- merge their ranges together to form the type.
--
-- By saying "injectively", it means for every
-- constructor f (a : α) of an inductive type,
-- we have (∀ (x y : α), (x = y) ↔ (f x = f y)).
-- And by saying "disjoint", it means different
-- constructor will never map to the same object.
inductive Inductive
  | f₁ (a : α)
  | f₂ (a : α)

example (x y : α) :
  (x = y) ↔ (Inductive.f₁ x = Inductive.f₁ y) := by
  apply Iff.intro
  · intro h
    rw [h]
  · intro h
    -- To move from the goal (x = y) to the goal
    -- (f₁ x = f₁ y), we must use the injection tactic.
    injection h

example (x : α) : (Inductive.f₁ x ≠ Inductive.f₂ x) := by
  intro h
  -- Tactic injection is also applicable to
  -- the case of mismatched constructors.
  injection h


-- Instances of type classes are fundamentally
-- object of instance type of single constructor mk.
-- So the tactic of proving Inductive types is
-- also applicable to them.
example (O₁ O₂ : LE α) : (O₁.le = O₂.le) ↔ (O₁ = O₂) := by
  rcases O₁ with ⟨R₁⟩
  rcases O₂ with ⟨R₂⟩
  change (R₁ = R₂) ↔ (LE.mk R₁ = LE.mk R₂)
  apply Iff.intro
  · intro h
    rw [h]
  · intro h
    injection h
