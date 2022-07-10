import ontology 
       topology.metric_space.emetric_space
       geometry.manifold.manifold
       data.real.basic
universe u
open set topological_space classical
local attribute [instance] prop_decidable

-- THIS FILE IS A WORK IN PROGRESS

open ontology

-- TODO: Need to upgrade to latest version of mathlib before developing this file properly.

-- structure geometry extends ontology.{u+1} := 
--     (time : setoid world)
--     (simultaneity_of_space : ∀ w₁ w₂, space.rel w₁ w₂ → time.rel w₁ w₂)
    

--common sense geometry
-- class geometry.common (ω : geometry) (H : Type* := ℝ) [topological_space H] (n : ℕ := 3) extends ontology.common ω.to_ontology :=
--     (axiom₄ : nonempty (@manifold (fin n → H)  _ ω.world ω.space.to_uniform_space.to_topological_space))
    

-- I am not sure how to model time.
-- structure physics extends geometry := 
--     (time : emetric_space world)
