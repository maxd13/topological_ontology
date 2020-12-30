import substances
open set topological_space classical
local attribute [instance] prop_decidable

/-! # The Theory of Counterfactuals -/

namespace ontology

  variables (ω : ontology)

  /- **TODOs**
    TODO: consider changing the definition 
    below to use relations once they become 
    avaiable via relations.lean
  -/

  /-- **Counterfactual Relations** are simply 
  (dyadic) relations between events -/
  structure cfr := 
    (would : ω.event → ω.event → ω.event)

  instance has_coe_to_fun_cfr : has_coe_to_fun ω.cfr :=
    ⟨_, cfr.would⟩

  /-- **Closer_Than Relations (ctr)** are world-indexed pre-orders between worlds.
      They express that a world `w₁` is at least as close 
      to a reference world `w` than some other world `w₂`. -/
  structure ctr :=
    (closer : ω.world → ω.world → ω.world → Prop)
    (axiom₁ : ∀ w, reflexive $ closer w)
    (axiom₂ : ∀ w, transitive $ closer w)

  instance has_coe_to_fun_ctr : has_coe_to_fun ω.ctr :=
    ⟨_, ctr.closer⟩

  /- **TODOs** 
    TODO: One idea was to make
          the definition was supposed to be along the lines of
          "w₁ is at least as close to w than w₂ ↔ 
          the least cardinality of linear orders containing w and w₁ 
          is ≤ than the least cardinality of linear orders containing w and w₂"
          But the definition below is simpler than that.
          Revise this idea in the future.
  -/
  /-- the natural `ctr` is the one naturally defined by
      the specialization order of the ontology. -/
  def nctr : ω.ctr := 
    { closer := λ w w₁ w₂, w.entities ∩ w₂.entities ⊆ w.entities ∩ w₁.entities 
    , axiom₁ := λ_, by simp [reflexive]
    , axiom₂ := begin
                  intro w,
                  simp [transitive],
                  intros x y z h₁ h₂ e he,
                  specialize h₂ he,
                  apply h₁, clear h₁,
                  replace he := he.left,
                  exact ⟨he, h₂⟩,
                end    
    }

  instance default_ctr : inhabited ω.ctr :=
    -- comment out to change the `ctr`.
    ⟨ω.nctr⟩
    -- your new and improved `ctr` goes here:
    -- ⟨...⟩
    -- defining this thingy here ↑ 
    -- is what all philosophical 
    -- discussions boil down to.

  /- **TODOs**
     TODO: Define ` ▹+ ` notation as the 
     subjunctive implication arrow relative to a default
     choice of counterfactual relation.
     TODO: Define `x ▹- y` notation as `-x ▹+ -y`.

     TODO: Specify different ways with which counterfactual 
           relations (`cfrs`) can be 
           defined. The main one 
           (which should probably become the default)
           will be via Lewisian `ctrs`, or some such 
           (perhaps "Prussian") variation of it, 
           using the natural `ctr` as the 
           default. It remains to be investigated whether
           this is equivalent to what is currently defined in
           causality.lean for the `x ▹- y` case. 
           
           Some other
           such ways could be by the introduction of primitive
           projection operators `π` of signature 
           `event → world → world` or `event → world → set world`, 
           which for every pair `e, w` would define what the 
           world `w` would be like in case `e` were to occur.
           Then `e₁ ▹+ e₂` should reduce to {w | (π e₁ w) ∈ e₂}
           or to {w | (π e₁ w) ⊆ e₂}, respectively. 
           Compared to the `ctrs`, it does look harder to define
           such projections without assuming new primitives.


     TODO: Don't forget to set up defaults (inhabited) 
           for every type defined in this module. 
           This is important.
  -/

  
end ontology