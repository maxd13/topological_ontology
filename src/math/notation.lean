
-- Module used solely for defining notation classes

class has_box (α : Type*) :=
  (box : α → α)

-- may change binding power in the future, depending on necessity
-- currently has the same power as has_neg.neg
prefix `□`:100  := has_box.box

class has_diamond (α : Type*) :=
  (diamond : α → α)

prefix `⋄`:100  := has_diamond.diamond

class has_entailment (α : Type*) :=
  (entails : α → α)

infixr ` ⇒ `:50 := has_entailment.entails
