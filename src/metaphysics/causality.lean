import properties metaphysics.counterfactuals
open set topological_space classical
set_option pp.generalized_field_notation true
local attribute [instance] prop_decidable
noncomputable theory


namespace ontology

variables {ω : ontology}

/-- Simultaneous Explanatory structure, used to define the Leibnizian concept of **explanation**. -/
structure explanation (ω : ontology) :=
  (explains : ω.event → ω.event → ω.event)
  (transitive : ∀ e₁ e₂ e₃, explains e₁ e₂ ∩ explains e₂ e₃ ⇒ explains e₁ e₃)
  (axiom₀ : ∀ {e w}, (∃ e', explains e' e w ∨ explains e e' w) → e.occurs w)
  /-- Events need to occur in order to be the explanation of something or to be explained
      by something. -/
  add_decl_doc explanation.axiom₀

namespace explanation 

  variable (ε : ω.explanation)

  /-- The (explanatory) **Principle of Sufficient Reason**, as an event. -/
  def epsr : ω.event := 
    {w : ω.world | ∀ (e : ω.event), e.contingent → e.occurs w → ∃ e', ε.explains e' e w}

  /-- The (explanatory) **Principle of Sufficient Reason**. -/
  def psr : Prop := □ε.epsr

  /-- A **stronger** version of the (explanatory) **Principle of Sufficient Reason**, as an event. -/
  def sepsr : ω.event := 
    {w : ω.world | ∀ (e : ω.event), e.occurs w → ∃ e', ε.explains e' e w}

  /-- A **stronger** version of the (explanatory) **Principle of Sufficient Reason**. -/
  def spsr : Prop := □ε.sepsr

end explanation

/-- Simultaneous Causal structure, used to define the concept of **hierarchical**
    or **vertical** causation. 
    A causal structure is an irreflexive explanatory structure. -/
structure cause (ω : ontology) extends explanation ω :=
  (irreflexive : ∀ e, ¬⋄to_explanation.explains e e)

namespace cause

  variable (c : ω.cause)

  def up := c.to_explanation
  def causes := c.up.explains
  @[reducible, simp]
  def transitive := c.up.transitive
  /-- Events need to occur in order to be the cause of something or to be caused
      by something. -/
  @[reducible, simp]
  def axiom₀ := c.up.axiom₀

  def caused (e : ω.event) : ω.event := {w | ∃ e', c.causes e' e w}
  def is_cause (e : ω.event) : ω.event := {w | ∃ e', c.causes e e' w}
  def uncaused (e : ω.event) : ω.event := -c.caused e

  /-- A **Cosubstantial cause** causes everything that is cosubstantial 
      to an entity in some possible world. -/
  def ccauses (e : ω.event) (e₁ : ω.entity) : ω.event := 
    {w | ∀ e₂ : ω.entity, e₂ ≈ e₁ → e₂.exists w → c.causes e e₂ w}

  def entitative : Prop := ∀ e, ⋄c.is_cause e → e.existential
  def substantive : Prop := ∀ e, ⋄c.is_cause e → e.existential ∧ e.dense
  
  def cosubstantial : Prop := ∀ e (e₁ : ω.entity), c.causes e e₁ ⇒ c.ccauses e e₁
  def conjunctive : Prop := ∀ e e₁ e₂, c.causes e (e₁ ∩ e₂) = c.causes e e₁ ∩ c.causes e e₂
  def conjunctive₁ : Prop := ∀ e e₁ e₂, c.causes e (e₁ ∩ e₂) ⇒ c.causes e e₁ ∩ c.causes e e₂
  def conjunctive₂ : Prop := ∀ e e₁ e₂, c.causes e e₁ ∩ c.causes e e₂ ⇒ c.causes e (e₁ ∩ e₂) 
  
  def disjunctive : Prop := ∀ e e₁ e₂, c.causes e (e₁ ∪ e₂) = c.causes e e₁ ∪ c.causes e e₂
  def subadditive : Prop := ∀ e e₁ e₂, c.causes e (e₁ ∪ e₂) ⇒ c.causes e e₁ ∪ c.causes e e₂
  def superadditive : Prop := ∀ e e₁ e₂, c.causes e e₁ ∪ c.causes e e₂ ⇒ c.causes e (e₁ ∪ e₂)

  def K : Prop := ∀ e e₁ e₂, c.causes e (e₁ ▹ e₂) ⇒ ((c.causes e e₁) ▹ c.causes e e₂)
  def axiom₄₀ : Prop := ∀ e₁ e₂, c.causes e₁ e₂ ⇒ c.causes e₁ (c.causes e₁ e₂)
  def axiom₄₁ : Prop := ∀ e, c.caused e ⇒ c.caused (c.caused e)
  def axiom₄₂ : Prop := ∀ e₁ e₂, c.causes e₁ e₂ = c.causes e₁ (c.caused e₂)
  lemma T : ∀ {e}, c.caused e ⇒ e := by
    rintros e w ⟨e₂, h⟩; exact c.axiom₀ ⟨e₂, or.inl h⟩

  @[simp]
  lemma caused_causes : ∀ {e₁ e₂}, c.causes e₁ e₂ ⇒ c.caused e₂ := 
    assume e₁ _ _ h, ⟨e₁,h⟩


  @[simp]
  lemma occured_causes : ∀ {e₁ e₂}, c.causes e₁ e₂ ⇒ e₂ := by
    intros e₁ e₂ w hw; apply c.T; apply c.caused_causes hw
  
  lemma singleton_uncaused_of_conjunctive₁ : c.conjunctive₁ → ∀ w, c.uncaused {w} w :=
    begin
      intros h w,
      simp [cause.uncaused, has_neg.neg, compl, set_of],
      by_contradiction c,
      obtain ⟨e, he⟩ := c,
      have c₀ : e.occurs w := c.axiom₀ ⟨{w}, or.inr he⟩,
      have c₁ : {w} = e ∩ {w},
        ext w', simp,
        exact ⟨λh, ⟨by convert c₀, h⟩, and.right⟩,
      rw c₁ at he, clear c₁ c₀,
      replace he := h e e {w} he,
      replace he : ⋄c.causes e e:= nonempty_of_mem he.1,
      have c₂ := c.irreflexive e,
      contradiction,
    end

  /-- A substance **Freely causes** some event if it causes it and it is possible
      for it to not have caused it even while remaining in the same state and in
      the same context in which the causation took place. -/
  def fcauses (s : ω.substance) (e : ω.event) : ω.event := 
    { w | c.causes s e w ∧ ∀ (context : ω.entity), 
      c.causes s e ⇒ context → c.causes s e ≠ context → ¬□context →
      ∃ w', w' ≠ w ∧ s.state w' = s.state w ∧ context.exists w' ∧
      ¬c.causes s e w'
    }
  
  def has_will (s : ω.substance) : Prop := ∃ e, ⋄c.fcauses s e
  def is_free (s : ω.substance) : Prop := ∀ w, s.exists w → ∃ e, ⋄(c.fcauses s e ∩ s.equiv w)

  /-- The causal version of the **Principle of Sufficient Reason**, as an event. -/
  @[reducible, simp]
  def epsr : ω.event := c.up.epsr
  /-- The causal version of the **Principle of Sufficient Reason**. -/
  def psr : Prop := □c.epsr

  -- Note: this lemma can be blocked for the `pc` below 
  -- due to the fact that a singleton event can only be
  -- an entity in case there is a best (greatest) of all possible worlds,
  -- which can simply be rejected due the immense amount
  -- of paradoxes that this generates, among which 
  -- "accidents cannot possibly exist" is included.
  lemma weak_modal_fatalism : c.conjunctive₁ → (∃ w₁ w₂ : ω.world, w₁ ≠ w₂) → ¬c.psr :=
    begin
      intros h₁ h₂ h₃,
      obtain ⟨w₁, w₂, h₂⟩ := h₂,
      simp [cause.psr, ext_iff] at h₃,
      specialize h₃ w₁,
      simp [explanation.epsr, set_of, has_mem.mem, set.mem] at h₃,
      -- the crucial step is specializing to {w₁},
      -- which works because we are not required to prove
      -- {w₁} is an existential event.
      specialize h₃ {w₁} (by simp [set.nonempty]) _, swap,
        simp [ext_iff],
        symmetry' at h₂,
        exact ⟨w₂,h₂⟩,
      specialize h₃ (mem_singleton_iff.2 rfl),
      obtain ⟨e, he⟩ := h₃,
      have c₀ := c.singleton_uncaused_of_conjunctive₁ h₁ w₁,
      replace he := c.caused_causes he,
      contradiction,
    end
  
  /-- The **Principle of Causality**, as an event. This is the `psr` restricted to entities. -/
  def epc : ω.event := 
    {w : ω.world | ∀ (e : ω.entity), e.contingent → e.exists w → c.caused e w}
  /-- The **Principle of Causality**. This is the `psr` restricted to entities. -/
  def pc : Prop := □c.epc

  /-- The **Platonic Principle** for events, as an event.
      This principle is a consequence of the doctrine
      of the impossibility of an infinite regress of 
      (*per se* ordered, simultaneous) causes. 
      It can be interpreted as a logically weaker form
      of stating essentially the same principle.
      It can be read as saying 
      "Everything that is caused is ultimately caused by something uncaused". -/
  def epp' : ω.event := 
    {w | ∀ e, c.caused e w → ∃ e', w ∈ c.uncaused e' ∩ c.causes e' e}
  /-- The **Platonic Principle** for events.
      This principle is a consequence of the doctrine
      of the impossibility of an infinite regress of 
      (*per se* ordered, simultaneous) causes. 
      It can be interpreted as a logically weaker form
      of stating essentially the same principle.
      It can be read as saying 
      "Everything that is caused is ultimately caused by something uncaused". -/
  def pp' : Prop := □c.epp'
  /-- The **Platonic Principle** (for entities), as an event.
      This principle is a consequence of the doctrine
      of the impossibility of an infinite regress of 
      (*per se* ordered, simultaneous) causes. 
      It can be interpreted as a logically weaker form
      of stating essentially the same principle.
      It can be read as saying 
      "Everything that is caused is ultimately caused by something uncaused". -/
  def epp : ω.event := 
    {w | ∀ e : ω.entity, c.caused e w → ∃ e', w ∈ c.uncaused e' ∩ c.causes e' e}
  /-- The **Platonic Principle** (for entities).
      This principle is a consequence of the doctrine
      of the impossibility of an infinite regress of 
      (*per se* ordered, simultaneous) causes. 
      It can be interpreted as a logically weaker form
      of stating essentially the same principle.
      It can be read as saying 
      "Everything that is caused is ultimately caused by something uncaused". -/
  def pp : Prop := □c.epp

  /- **Fun fact:** the platonic principle is also a way to state the impossibility of an infinite
     regress in a way to make the classical arguments which depend on it tractable within the
     confines of Aristotelian logic. Aristotelian logic is not really equipped to discuss 
     the order-theoretical questions which arise in the discussion of regress problems.
     For instance, it appears to be impossible to derive Zorn's lemma from the axiom 
     of choice using only Aristotelian syllogisms. However, using the platonic principle,
     many arguments can be exposed using simple BARBARA syllogisms. 
     
     We do not necessarily mean to imply, however, that this principle is more or less evident
     than the impossibility of regress. If the impossibility of regress seems more evident than this
     principle to the reader, we can use that assumption to prove the principle rather than to assume
     this principle as a premisse in our arguments. However, the proof of this principle does depend
     on Zorn's lemma, which is equivalent to the axiom of choice.
     Indeed, this proof can be seen as a mere restatement of the lemma. 
  -/

  /-- An `event` is said to be **Causally Grounded** w.r.t. a causal structure
      if there is some event which may possibly cause the event to occur. -/
  def cground (e : ω.event) : ω.event := {w | ∃ e' : ω.event, e'.occurs w ∧ ⋄c.causes e' e}

  /-- An **Aristotelian-Causal Account of Modality** for events is the set of all the possible worlds 
      `w` relative to which an event is possible if and only if either the event occurs or some event
      in `w` can possibly cause the event to occur. -/
  def acam' : ω.event := {w | ∀ e : ω.event, ⋄e → e.occurs w ∨ c.cground e w}
  -- Notice the converse of the (`→`) in the above definition is trivial.

  /-- An **Aristotelian-Causal Account of Modality** (for entities) is the set of all the possible worlds 
      `w` in which for any given possible entity `e`, it either exists in `w` or some event
      in `w` can possibly cause `e` to exist. -/
  def acam : ω.event := {w | ∀ (e : ω.entity), e.exists w ∨ c.cground e w}
     
  /-- This is an extra auxiliary principle that is needed in Pruss's 
      "nature of modality" argument.
      It reads "If all but one world satisfies the `psr`
      and the one that is left is also Aristotelian-Causal, then this world also satisfies the `psr`."
      The "Aristotelian-Causal" part is a weakening of the original thesis. -/
  def prussian_principle₁ : Prop := ∀ (w : ω.world), c.acam' w → (∀ w', w' ≠ w → c.epsr w') → c.epsr w
  /-- This is an extra auxiliary principle that is needed in Pruss's 
      "nature of modality" argument.
      It reads "If some world `w` is Aristotelian-Causal, and all worlds containing an entity not in the `w` 
      satisfy the `pc`, then `w` also satisfies the `pc`."
      The "Aristotelian-Causal" part is a weakening of the original thesis,
      but this principle appears to be stronger than `prussian_principle₁`. -/
  def prussian_principle₂ : Prop := ∀ (w : ω.world), c.acam w → (∀ w', (∃ e ∈ w', e ∉ w) → c.epc w') → c.epc w
  
  theorem pruss_nature_of_modality_argument₁ : c.conjunctive₁ → c.prussian_principle₁ → ⋄c.acam' → c.psr :=
    begin
      intros conj pruss h,
      obtain ⟨actual_world, ha⟩ := h,
      suffices c₀ : ∀ w', w' ≠ actual_world → c.epsr w',
        have c₁ := pruss actual_world ha c₀,
        simp [cause.psr, ext_iff], intro w,
        by_cases h : w = actual_world,
          rw h, exact c₁,
        exact c₀ w h,
      intros w hw,
      simp [explanation.epsr, set_of],
      by_contradiction contra,
      push_neg at contra,
      obtain ⟨e, pe, ce, he, h⟩ := contra,
      clear pe,
      have c₁ : ∃ F : ω.event, ⋄F ∧ ¬F.occurs actual_world ∧ ¬⋄c.cground F,
          symmetry' at hw,
          use {w}, simp [hw, set.nonempty],
          by_contradiction contra,
          push_neg at contra,
          obtain ⟨w', ⟨e',he', h'⟩⟩ := contra,
          obtain ⟨w'', hw''⟩ := h',
          have c₁ := c.occured_causes hw'',
          simp at c₁,
          rw c₁ at hw'', clear c₁ w'', rename hw'' c₁,
          replace conj := c.singleton_uncaused_of_conjunctive₁ conj w,
          replace c₁ := c.caused_causes c₁,
          contradiction,
      obtain ⟨F, pF, naF, hF⟩ := c₁,
      simp [cause.acam'] at ha,
      specialize ha F pF,
      simp at naF, simp [naF] at ha,
      simp [set.nonempty] at hF,
      specialize hF actual_world,
      contradiction,
    end

  -- Note: unlike the previous, the following theorem is actually philosophically relevant,
  -- since the premisses in this one are not inconsistent.
  -- theorem pruss_nature_of_modality_argument₂ : c.conjunctive₁ → c.prussian_principle₂ → ⋄c.acam → c.pc :=
  --     begin
  --       intros conj pruss h,
  --       obtain ⟨actual_world, ha⟩ := h,
  --       suffices c₀ : ∀ w', (∃ e ∈ w', e ∉ actual_world) → c.epc w',
  --         have c₁ := pruss actual_world ha c₀,
  --         simp [cause.pc, ext_iff], intro w,
  --         by_cases h : (∃ e ∈ w, e ∉ actual_world),
  --           rw h, exact c₁,
  --         exact c₀ w h,
  --       intros w hw,
  --       simp [cause.epc, set_of],
  --       by_contradiction contra,
  --       push_neg at contra,
  --       obtain ⟨e, ce, he, h⟩ := contra,
  --       have c₁ : ∃ F : ω.entity, ¬F.exists actual_world ∧ ¬⋄c.cground F,
  --           admit,
  --       obtain ⟨F, naF, hF⟩ := c₁,
  --       simp [cause.acam] at ha,
  --       specialize ha F,
  --       simp [naF] at ha,
  --       simp [set.nonempty] at hF,
  --       specialize hF actual_world,
  --       contradiction,
  --     end


end cause

section counterfactuals

  variable (ω)

  /- A **Counterfactual Theory of (Hierarchical) Causality** is one which, beginning from
      a theory of counterfactuals, defines hierarchical causality as "If `e₂` is removed, then `e₁` is removed",
      i.e. there is strong counterfactual dependence between `e₁` and `e₂`. -/
  -- def ctc (c : ω.cfr := default ω.cfr) : ω.cause := begin
  --   refine ⟨⟨c.sdepends, _, _⟩, _⟩,
  --    intros,
  --    simp [cfr.sdepends, cfr.depends],
  --    unfold_coes,
  -- end
  
  -- TODO: Another interpretation of "If `e₁` is removed, then `e₂` is removed" 
  -- could be given in terms of `entity.removed` for a causal relation in which
  -- only entities were involved in causation.

end counterfactuals

-- section four_causes

--   variables (s : ω.substance) (e : ω.entity)

--   -- integral parthood
--   def substance.part_of (s₁ s₂ : ω.substance) : ω.event := sorry

--   -- efficient vertical causation
--   def substance.ecauses : ω.event := 
--     s.causes e.exists ∩
--     -s.part_of e.substance ∩
--     -e.substance.part_of s


--   -- compositional causation (we say s "compositionally causes" e)
--   def substance.ccauses : ω.event := 
--     s.causes e.exists ∩
--     s.part_of e.substance ∩
--     -e.substance.part_of s

--   -- formal causation
--   def substance.forcauses : ω.event := 
--     s.ccauses e ∩
--     s.causes e.substance.exists

--   -- material causation
--   def substance.mcauses : ω.event := 
--     s.ccauses e ∩
--     -s.causes e.substance.exists

--   -- final causation
--   def substance.fincauses : ω.event := 
--     s.causes e.exists ∩
--     -s.part_of e.substance ∩
--     e.substance.part_of s

-- end four_causes

section principles

  variable (ω)

  -- -- the thomistic principle of sufficent reason/causality
  -- def tpsr : Prop := 
  --   ∀ (s : ω.substance) (p : ω.predicate) (h₁ : p.proper) (h₂ : ¬ p.dere_of s.up) (w ∈ p s.up), 
  --   ∃ c : ω.substance, c.causes (p s.up) w

  -- -- the efficient version of tpsr
  -- -- the thomistic principle of sufficent reason/causality
  -- def etpsr : Prop := 
  --   ∀ (s : ω.substance) (p : ω.predicate) (h₁ : p.proper) (h₂ : ¬ p.dere_of s.up) (w ∈ p s.up),
  --   -- p s.up cast to an entity
  --   let r := (entity.mk (p s.up) 
  --           (by apply h₁.axiom₂; exact e) 
  --           (by use w; assumption))
  --   in ∃ c : ω.substance, c.ecauses r w

end principles

end ontology