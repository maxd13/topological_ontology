import universals
universe u
open set topological_space classical
local attribute [instance] prop_decidable

namespace ontology
  variables (ω : ontology)
  section matter

 
    -- We call any composite substance `physical`,
    -- or a `body`.
    
    @[reducible]
    def substance.physical {ω : ontology} (s : ω.substance) := composite s.val
    def cosmos_set := {s : ω.substance | s.physical}
    def body := subtype ω.cosmos_set
    
    -- The cosmos is the integral whole of all
    -- composite (physical) substances.
    def cosmos := integral_whole ω.cosmos_set
  
    -- Prime matter is the abstract whole of all
    -- composite (physical) substances.
    def prime_matter := abstract_whole ω.cosmos_set
    
    -- There are specifically two dual notions of `matter` that are obtained 
    -- by considering virtual substances (concepts) 
    -- as the totalities of both kinds of matter:
    
    -- (1) From the point of view of the whole, 
    -- matter can be thought of as that which 
    -- actively composes a thing, its substratum.
    -- This sense we will only cover in the next
    -- section, which is mereology.
    
    -- (2) From the point of view of matter itself,
    -- matter can be thought of as that which is in potency
    -- to a multiplicty of forms, in the sense of prime matter.
    -- Mathematically these two notions are dual, 
    -- with the duality of Π and Σ types, respectively.
  
    -- Notice, in the first notion matter is actual, 
    -- and in the second potential.
    
    -- Transcendent matter is the abstract whole of all
    -- substances.
    -- This is the virtual substance that is "in potency"
    -- for becoming any other substance.
    def transcendent_matter : ω.concept := abstract_whole univ
  
    -- The state space of a virtual, likely possible, substance
    -- corresponding to a concrete and immanent notion of matter.
    -- This virtual is the mereological sum of the set of all substances.
    -- It is the whole of reality.
    def reality : ω.concept := integral_whole univ
  
    -- Of course nothing in reality is an instance of
    -- prime or transcendent matter.
 
  end matter
  
  section mereology
 
    -- A substance s₁ is an integral part of another
    -- substance s₂ if there is a 
    -- (necessarilly nonempty) set S of substances 
    -- such that the integral whole of {s₁} ∪ S is
    -- homeomorphic to the state space of s₂ by
    -- means of a state-preserving homeomorphism
    def substance.part_of {ω : ontology} (s₁ s₂ : ω.substance) :=
      -- s₁ ≠ s₂ ∧
      ∃ S : set ω.substance, 
      S.nonempty ∧
      s₁ ∉ S ∧
      -- (∀ x ∈ S, x ≠ s₂) ∧
      ∃ hom :
          s₂.concept.state ≃ₜ
          (integral_whole $ S ∪ {s₁}).state,
      state_preserving hom.to_fun
  
    -- This is to say that if we know the state of the
    -- substance s₂ in a possible world w, then we
    -- already know the state of each of its parts,
    -- since there is a functional dependence between them.
    
    --  @[trans]
    --  lemma part_of_trans : ∀ s₁ s₂ s₃ : ω.substance, 
    --                        s₁.part_of s₂ →
    --                        s₂.part_of s₃ →
    --                        s₁.part_of s₃ :=
    --     begin
    --         intros s₁ s₂ s₃ h₁ h₂,
    --         -- simp [substance.part_of] at *,
    --         obtain ⟨S₁, ne₁, notin₁, hom₁, h₁⟩ := h₁,
    --         obtain ⟨S₂, ne₂, notin₂, hom₂, h₂⟩ := h₂,
    --         use S₁ ∪ S₂ ∪ {s₂},
    --         simp,
              -- TODO
    --     end
  
  end mereology
end ontology