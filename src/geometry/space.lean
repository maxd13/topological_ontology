import ontology
open set topological_space classical
set_option pp.generalized_field_notation true
local attribute [instance] prop_decidable
noncomputable theory
universe u

-- THIS FILE IS A WORK IN PROGRESS

namespace ontology

variable {ω : ontology}

structure geometry (ω : ontology) := 
  (space : ontology)
  (instant : space.world → ω.world)
  (continuous : continuous instant)
  (location : ω.event → space.event)
  (consistent : location ≤ preimage instant)
  (stronger_entailment : ∀ e₁ e₂ : ω.event, location e₁ ⇒ location e₂ → e₁ ⇒ e₂)
  (closed : ∀ e : ω.event, e.closed → location e = instant⁻¹' e)
  (finite : ∀ e : ω.event, e.finite → location e = instant⁻¹' e)
  (cofinite : ∀ e : ω.event, (-e).finite → location e = instant⁻¹' e)
  (inter_enclosement : ∀ e₁ e₂ : ω.event, location e₁ = instant⁻¹' e₁ → location e₂ = instant⁻¹' e₂ → location (e₁ ∩ e₂) = instant⁻¹' (e₁ ∩ e₂))
  (union_enclosement : ∀ e₁ e₂ : ω.event, location e₁ = instant⁻¹' e₁ → location e₂ = instant⁻¹' e₂ → location (e₁ ∪ e₂) = instant⁻¹' (e₁ ∪ e₂))
  (lem : ∀ e : ω.event, location e = instant⁻¹' e ∨ location (-e) = instant⁻¹' (-e))


end ontology