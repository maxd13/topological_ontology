import metaphysics.causality
open set topological_space classical
set_option pp.generalized_field_notation true
local attribute [instance] prop_decidable
noncomputable theory

namespace ontology

variables {ω : ontology}

structure belief (ω : ontology) :=
  (believes  : ω.substance → ω.event → ω.event)
  (cogito : ∀ {s e}, believes s e ⇒ s)
  (reflexive : ∀ {s}, (∃ e, ⋄believes s e) → s ⇒ believes s s)
  (transitive : ∀ {s e₁ e₂}, believes s (e₁ ⟶ e₂) ∩ believes s e₁ ⇒ believes s e₂)
  (idempotent : ∀ {s e}, believes s (believes s e) = believes s e)

structure knowledge (ω : ontology) extends belief ω :=
  (sound  : ∀ {s e}, believes s e → e)

@[reducible, simp, alias, inline]
def knowledge.knows (k : ω.knowledge) := k.believes

namespace substance

  variable (s : ω.substance)

  structure mact (s : ω.substance) (k : ω.knowledge) :=
    (p : ω.predicate)
    (proper : p.proper)
    (ratio : ω.predicate)
    (intrinsic : ratio.possessed)
    (extension : ∀ e, p e ⇒ ratio e)
    (idempotent : ∀ e (h : ⋄ratio e), ratio (intrinsic.sign h) = ratio e)
    (axiom₀ : ⋄ratio s)
    (axiom₁ : ratio s ⇒ k.knows s (ratio s))
    (axiom₂ : ∀ e, k.knows s (p e) ⇒ ratio s)
    (axiom₃ : ∀ e : ω.entity, ⋄p e → ⋄(k.knows s e) → ⋄k.knows s (p e))


  variables {s} {k : ω.knowledge} (m : s.mact k) (c : ω.cause)

  def eminently (p : ω.predicate) := ¬⋄p s ∧ ∃ m : s.mact k, m.p = p
  def mact.practical := ∃ e, ⋄c.fcauses s (m.p e) 

  -- def mact.mcontent := ∃ mcontent, s ⇒ ✦c.fcauses s (m.p mcontent)

  def substance.person (s : ω.substance) (c : ω.cause) (k : ω.knowledge) : Prop := 
    c.free s ∧ ∀ e, ⋄c.fcauses s e → 
    ∃ m : s.mact k, c.fcauses s e ⇒ m.ratio s ∧ c.fcauses s e ≠ m.ratio s


end substance

end ontology