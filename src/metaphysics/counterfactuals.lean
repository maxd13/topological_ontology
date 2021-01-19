import substances
open set topological_space classical
local attribute [instance] prop_decidable

/-! # The Theory of Counterfactuals -/

namespace ontology

variables (ω : ontology)

/- **TODOs**
  TODO: consider changing the structure 
  below to use relations once they become 
  avaiable via relations.lean
-/

/-- **Counterfactual Relations** are simply 
(dyadic) relations between events -/
structure cfr := 
  (entails : ω.event → ω.event → ω.event)
  /-- Subjunctive conditional/implication. -/
  add_decl_doc cfr.entails 

/-- Given `c : ω.cfr`, use `c e₁ e₂` instead of `c.entails e₁ e₂`. -/
instance has_coe_to_fun_cfr : has_coe_to_fun ω.cfr :=
  ⟨_, cfr.entails⟩

-- Natural examples of `cfrs`.
section cfr_examples

  /-- The naive way to define a `cfr` is to think that subjunctive implication 
      just reduces to normal implication in the context of some theory. 
      So that, e.g., "If I were to throw something up it would go down" is true
      because there exists some true theory of physics which contains 
      the law of universal gravitation from which it would be possible to prove
      this statement. 
      Because we can see a true theory as simply an event, 
      i.e. the event of the theory being true, this justifies our definition. -/
  def naive_cfr : ω.cfr := ⟨λe₁ e₂ w, ∃ e : ω.event, e.occurs w ∧ e ∩ e₁ ⇒ e₂⟩

  /- The previous definition contains a paradox, can you spot it? -/

  /-- `e₁` subjunctively entails `e₂` in world `w` if the removal of any entities from `w` 
      implies `e₁ ▹ e₂`. 
      Alternatively, if for any world "smaller" than `w`
      in which `e₁` happens, `e₂` also happens. -/
  def removal_cfr : ω.cfr := ⟨λe₁ e₂ w, w.ideal ⇒ e₁ ▹ e₂⟩
  /-- `e₁` subjunctively entails `e₂` in world `w` if the addition of any entities from `w` 
      implies `e₁ ▹ e₂`.
      Alternatively, if for any world "larger" than `w`
      in which `e₁` happens, `e₂` also happens. -/
  def addition_cfr : ω.cfr := ⟨λe₁ e₂ w, w.filter ⇒ e₁ ▹ e₂⟩
  /-- `e₁` subjunctively entails `e₂` in world `w` if the addition or removal of any entities from `w` 
      implies `e₁ ▹ e₂`. -/
  def arithmetic_cfr : ω.cfr := ⟨λe₁ e₂, ω.removal_cfr e₁ e₂ ∪ ω.addition_cfr e₁ e₂⟩

end cfr_examples

section cfr

  variables {ω} (c : ω.cfr) (e₁ e₂ : ω.event)

  /-- **Counterfactual dependence** relation.
    i.e. if `e₁` were not the case `e₂` would not be the case. -/
  @[reducible]
  def cfr.depends : ω.event := c (-e₁) (-e₂)
  
  -- counterfactual entanglement
  @[reducible]
  def cfr.entangled : ω.event := c.depends e₁ e₂ ∩ c.depends e₂ e₁

  /-- Counterfactual **strong** (or one sided) dependence.
      Could also be called "event causation", but we reserve
      the name "cause" for a more qualified definition. -/
  @[reducible]
  def cfr.sdepends : ω.event := c.depends e₁ e₂ - c.depends e₂ e₁

  -- counterfactual independence
  @[reducible]
  def cfr.independent : ω.event := -c.depends e₁ e₂ ∩ -c.depends e₂ e₁


  /-- If `e₁` subjunctively entails `e₂` in `w` and `e₁` occurs in `w`, `e₂` 
      should also occur in `w`. -/
  def cfr.postulate₁ : Prop := ∀ e₁ e₂, c e₁ e₂ ⇒ e₁ ▹ e₂

  /-- A `cfr` is paradoxical if the falsity of the antecedent of the subjunctive implication
      implies its truth. -/
  def cfr.paradox₁ : Prop := ∀ e₁ e₂, -e₁ ⇒ c e₁ e₂

  /-- The naive cfr is paradoxical, because if the antecedent of the subjunctive 
    implication is false the implication is always true. -/
  lemma naive_cfr_paradox₁ : ω.naive_cfr.paradox₁ :=
    begin
      intros e₁ e₂,
      unfold_coes,
      intros w hw,
      simp [naive_cfr, has_mem.mem, set.mem],
      use {w}, refine ⟨mem_singleton_iff.2 rfl, _⟩,
      replace hw := singleton_inter_eq_empty.2 hw,
      rw hw,
      tauto,
    end

end cfr

/-- **Closer_Than Relations (ctr)** are world-indexed pre-orders between worlds.
    They express that a world `w₁` is at least as close 
    to a reference world `w` than some other world `w₂`. -/
structure ctr :=
  (closer : ω.world → ω.world → ω.world → Prop)
  (axiom₁ : ∀ w, reflexive $ closer w)
  (axiom₂ : ∀ w, transitive $ closer w)

/-- Given `c : ω.ctr`, use `c w w₁ w₂` instead of `c.closer w w₁ w₂`. -/
instance has_coe_to_fun_ctr : has_coe_to_fun ω.ctr :=
  ⟨_, ctr.closer⟩

/-- Irreflexive version of `ctr.closer`. -/
def ctr.closer' {ω : ontology} (c : ω.ctr) : ω.world → ω.world → ω.world → Prop := 
  assume w w₁ w₂,
  c w w₁ w₂ ∧ ¬ c w w₂ w₁

/- **TODOs** 
  TODO: One idea was to construct
        the definition along the lines of
        "w₁ is at least as close to w than w₂ ↔ 
        the least cardinality/ordinality of linear orders/well-orders containing w and w₁ 
        is ≤ than the least cardinality/ordinality of linear orders/well-orders containing w and w₂"
        And maybe we could extend this to the sums of ordinals of multiple well-orders,
        for the case in which the possible worlds are incomparable. 
        But the definition below is much simpler than that.
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


/-- The **Lewisian** `cfr` is the `cfr` defined by a `ctr`. -/
def lcfr (c : ω.ctr := default ω.ctr) : ω.cfr := 
  ⟨ λ e₁ e₂ w, ¬⋄e₁ ∨ 
    (∃ w', w' ∈ (e₁ ∩ e₂) ∧ 
    (∀ w'', e₁.occurs w'' → ¬ e₂.occurs w'' → c.closer' w w' w'')
    ) ⟩

instance default_cfr : inhabited ω.cfr :=
  -- comment out to change the `cfr`.
  ⟨ω.lcfr⟩
  -- your new and improved `cfr` goes here:
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
          Yet another way could be by the introduction of a
          collection of events with which to restrict the 
          existential quantification of the `naive_cfr` 
          definition, so as to avoid `cfr.paradox₁` and 
          other such paradoxes.


    TODO: Don't forget to set up defaults (inhabited) 
          for every type defined in this module. 
          This is important.
-/

end ontology