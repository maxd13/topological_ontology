import abstraction.concepts
       data.real.basic
       topology.instances.real
       measure_theory.borel_space
       measure_theory.measure_space
universe u
open set topological_space classical
local attribute [instance] prop_decidable

namespace ontology

  variable {ω : ontology}
  variable c : ω.concept
  
  -- A definition of the 10 Aristotelian Categories,
  -- and of the subcategories Aristotle mentions in his work.
  -- The Categories of Substance and Quality were already defined.
 
 
  -- A quantity for a concept is a continuous
  -- map from states of the concept to the reals.
  def concept.quantity := subtype {f : c.state → ℝ | continuous f }
 
  --  For some reason which is mind boggling, we couldn't
  --  find the definition of a probability measure in mathlib.
  instance concept.borel : measurable_space c.state := borel c.state
  def concept.probability_measure := {μ : measure_theory.measure c.state | μ.measure_of univ = 1} 
 
  -- A disposition is a partly state-indexed probability measure for a concept
  -- such that the preimage of every probability measure is either open or closed.
  def concept.disposition := 
     subtype {f : c.state →. c.probability_measure | ∀ p : c.probability_measure, is_open (f⁻¹' {roption.some p}) ∨ is_closed (f⁻¹' {roption.some p})}
 
  -- A habit is a "permanent" disposition. We take this to mean that
  -- it is constant in a dense open set.
  def concept.habit := 
     subtype {d : c.disposition | ∃ p : c.probability_measure,  closure (d.val⁻¹' {roption.some p}) = univ}
 
  -- a law of nature is a constant disposition, i.e. the same for every
  -- state. It is provably a habit as well. 
  -- The usual talks of "laws of nature" are laws of nature in the "cosmos"
  -- (to be defined later), assuming that these laws are necessary. But if
  -- they are contingent they are assumed to be habits.
 
  def concept.law := 
     subtype {d : c.disposition | ∃ p : c.probability_measure, ∀ x : c.state, p ∈ d.val x}
 
 
end ontology