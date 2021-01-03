import ontology math.fuzzy
open set topological_space classical
local attribute [instance] prop_decidable

namespace ontology

-- TODO: consider redefining events as observables
-- later, and changing notation to support it.
-- This would be a major refactoring, but one
-- which does not change the essence of the system,
-- so we defer it to after the project is close
-- to the end.

  variables (ω : ontology)

  abbreviation observable (α : Sort*) 
                [topological_space α] 
                [has_none α]
                := ω.world → α

  abbreviation event' := ω.observable Prop

  @[simp]
  lemma event'_eq_event : ω.event' = ω.event := 
  by simp [ontology.event, set]

  abbreviation quantity := ω.observable (option ℝ)

section observables

  variables {ω} {α : Type*} [topological_space α] 
            [has_none α] (o : ω.observable α)

  abbreviation observable.perfect := continuous o

  /- observables are coerced to their domain of definition -/
  instance has_coe_observable_event : has_coe (ω.observable α) ω.event := ⟨λ f x, f x ≠ has_none.none⟩

end observables

  -- We now talk about analogical (fuzzy) events, or "aevents" TODO: revise this comment.
  abbreviation aevent :=  ω.observable fuzzy

namespace aevent

  variables {ω} (ae : ω.aevent)

  abbreviation aevent.possible := (↑ae : ω.event).possible 

  /-- Use `⋄ae` for "`ae` is possible" -/
  instance has_diamond_aevent : has_diamond ω.aevent := ⟨aevent.possible⟩

end aevent

end ontology