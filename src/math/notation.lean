import order.lattice


-- Module used solely for defining notation classes

class has_box (α : Type*) :=
  (box : α → Prop)

-- may change binding power in the future, depending on necessity
-- currently has the same power as logical negation
prefix `□`:40  := has_box.box

class has_black_box (α : Type*) :=
  (box : α → α)

-- may change binding power in the future, depending on necessity
-- currently has the same power as logical negation
prefix `◾`:40  := has_black_box.box

class has_diamond (α : Type*) :=
  (diamond : α → Prop)

prefix `⋄`:40  := has_diamond.diamond

class has_black_diamond (α : Type*) :=
  (diamond : α → α)

prefix `✦`:40  := has_black_diamond.diamond

class has_tilde (α : Type*) :=
  (tilde : α → α)

prefix `~` := has_tilde.tilde

class has_entailment (α : Type*) :=
  (entails : α → α → Prop)

infixr ` ⇒ ` := has_entailment.entails

def strict_entailment {α : Type*} [has_entailment α] (x y : α) := x ⇒ y ∧ x ≠ y

infixr ` ⇒' `:50 := strict_entailment

class has_local_entailment (α : Type*) :=
  (entails : α → α → α)

reserve infixr ` ▹ `:50
infixr ` ▹ ` := has_local_entailment.entails

def local_eq {α : Type*} [has_local_entailment α] [has_inf α] (x y : α) := (x ▹ y) ⊓ (y ▹ x) 

-- class has_local_eq (α : Type*) := (eq : α → α → α)
infixr ` ≡ ` := local_eq -- has_local_eq.eq

def local_neq {α : Type*} [has_local_entailment α] [has_inf α] [has_neg α] (x y : α) := -(x ≡ y)

-- class has_local_neq (α : Type*) := (neq : α → α → α)
infixr ` ≢ `:50 := local_neq -- has_local_neq.neq