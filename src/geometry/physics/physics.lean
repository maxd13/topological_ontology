import ontology 
       topology.metric_space.emetric_space
       geometry.manifold.manifold
       data.real.basic
universe u
open set topological_space classical
local attribute [instance] prop_decidable

open ontology

structure geometry extends ontology := 
    (space : emetric_space world)



--common sense geometry
class geometry.common (ω : geometry) (H : Type* := ℝ) [topological_space H] (n : ℕ := 3) extends ontology.common ω.to_ontology :=
    (axiom₄ : nonempty (@manifold (fin n → H)  _ ω.world ω.space.to_uniform_space.to_topological_space))
    

-- I am not sure how to model time.
-- structure physics extends geometry := 
--     (time : emetric_space world)
