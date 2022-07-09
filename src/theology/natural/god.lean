import metaphysics.metaphysics states
open set topological_space classical
set_option pp.generalized_field_notation true
local attribute [instance] prop_decidable

namespace ontology

variable {ω : ontology}

section theism
  
  variable (ω)

  /-- **Theism** is the doctrine that the necessary being is simple. -/
  def theism := ω.nb.simple
  /-- Negation of `theism`. -/
  @[reducible, simp]
  def atheism := ¬ ω.theism
        
  /-- **Classical Theism** is an extension of theism which 
      furthermore claims that there is a possible world 
      in which the necessary being exists alone. -/
  def ctheism := ∃ (w : ω.world), ∀ e₁ e₂ : ω.entity, e₁.exists w → e₂.exists w → e₁ = e₂

  /-- this is a not so trivial proof that if the nb exists alone,
      then it has no accidents, because accidents are contingent. -/
  @[simp] lemma theism_of_ctheism {ω : ontology} : ω.ctheism → ω.theism :=
    begin
      rintros ⟨w, hw⟩,
      dunfold theism,
      by_contradiction h,
      replace h : ω.nb.composite,
        simp at h, simp [h],
      replace h := nb_acc_actual h w,
      obtain ⟨a, ha₁, ha₂⟩ := h,
      have ha₃ := a.contingent,
      simp at ha₃,
      specialize hw a ω.nb ha₂ (by simp [nb, nbe]),
      unfold_coes at hw,
      simp [nb] at hw,
      contradiction,
    end

  /-- **Greek Theism** is non-classical theism. -/
  def greek_theism := ω.theism ∧ ¬ ω.ctheism

  -- All 4 positions are logically consistent:

  -- lemma atheism_consistent : ∃ ω : ontology, ω.atheism := sorry
  -- lemma theism_consistent : ∃ ω : ontology, ω.theism := sorry
  -- lemma ctheism_consistent : ∃ ω : ontology, ω.ctheism := sorry
  -- lemma greek_theism_consistent : ∃ ω : ontology, ω.greek_theism := sorry

  -- It is actually considerably annoying to formally prove the previous results even though they are absolutely trivial,
  -- so we leave them commented out. But consider that, given our lemma `nb_simple_iff_space_connected`
  -- in substances.lean, any connected space is a model of theism, and any disconnected space a model of atheism. 
  -- Any connected space without a focal point is a model of greek theism (e.g. a sphere), and a
  -- space is a model of classical theism if and only if it has a focal point. Every partial order with a least
  -- element is a model of classical theism when given its Alexandroff topology.

  /-- The *second gap problem* is showing that God satisfies
      the properties prescribed to Him by classical theism
      under the assumption that God exists.
      This is not to be confused with the *first gap problem* 
      of showing that if the necessary being is a first cause of all 
      things in some possible world, then it is God.
      An ontology `ω` is said to contain **no second gap**
      if this gap problem admits a solution in `ω`.
      Solutions of the gap problem are proofs of the 
      `ω.nogap₂` proposition, and may be also called **(secondary) gap fillers**. -/
  def nogap₂ : Prop := ω.theism → ω.ctheism

  -- WORK IN PROGRESS (RELATED TO 4TH WAY).
  -- theorem qparticipated_of_theism : ω.theism → (∀ b : ω.being, b.qparticipated) := sorry

  theorem theism_iff_connected : ω.theism ↔ ω.connected := nb_simple_iff_space_connected

end theism

section divine_properties

  -- First we discuss pure actuality:
  variables (s : ω.substance) (e : ω.entity)

  /-- A substance is **Purely Actual** if it has no passive potentiality
      to be different from what it is, i.e. if it has a single state. -/
  def substance.purely_actual := ∀ w₁ w₂ : ω.world, s.state w₁ = s.state w₂
  
  /-- Only the necessary being can be purely actual, 
      in which case theism follows. -/
  theorem substance.eq_nb_of_purely_actual : s.purely_actual → s.necessary :=
  begin
      intros h,
      simp [substance.purely_actual] at h,
      ext w₁,
      simp [nb, nbe],
      obtain ⟨w₂, hw₂⟩ := s.possible,
      specialize h w₁ w₂,
      replace hw₂ := exists_iff_in_state.mp hw₂,
      rw ←h at hw₂,
      exact exists_iff_in_state.2 hw₂,
  end

  theorem substance.simple_of_purely_actual : s.purely_actual → s.simple :=
    begin
      intro h₀,
      by_contradiction h,
      simp [set.nonempty, accident.inheres] at h,
      obtain ⟨a, ha⟩ := h,
      obtain ⟨w₁, hw₁⟩ := a.possible,
      have h := a.contingent,
      simp [nb, nbe, ext_iff] at h,
      obtain ⟨w₂, hw₂⟩ := h,
      specialize h₀ w₁ w₂,
      simp [substance.state, ext_iff] at h₀,
      specialize h₀ a,
      unfold_coes at h₀,
      simp [ha, hw₁, hw₂] at h₀,
      contradiction,
    end

  theorem theism_iff_purely_actual : ω.theism ↔ ∃ s : ω.substance, s.purely_actual :=
    begin
      constructor; intro h,
        use ω.nb,
        intros w₁ w₂,
        transitivity ({ω.nbe} : set  ω.entity);
        simp [substance.state, ext_iff];
        intro x;
        by_cases hyp : x = ω.nbe,
          any_goals {rw hyp,
          simp [nb], constructor,
            apply self_subsist.mp,
            simp [entity.perfect, nbe], 
          },
          any_goals {simp [entity.perfect, nbe]},
        any_goals {simp [nb]},
        any_goals {
        have : ¬ x.subsists ω.nbe,
          intro h₀,
          simp [theism, set.nonempty] at h,
          have := imperfect_of_subsists_other h₀ hyp,
          let x' : ω.accident := ⟨x, this⟩,
          apply h x',
          simpa [x', accident.inheres, nb],
          simp [this],
          simp [nbe, ext_iff] at hyp,
          exact hyp,
        },
      obtain ⟨g, hg⟩ := h,
      have c₀ := g.eq_nb_of_purely_actual hg,
      simp [substance.necessary] at c₀,
      replace hg := g.simple_of_purely_actual hg,
      simp only [theism],
      rwa ←c₀ at *,
    end

  -- Then we discuss causal properties which properly belong to the divine being:
  variable (c : ω.cause)

  /-- A a causal structure `c` is **principled** (in the sense that it emanates from 
      a necessary first principle) just in case the necessary being can possibly be a `first_cause`
      with respect to `c`. Proofs that a causal structure is principled are called
      **(stage 1) cosmological arguments**. -/
  @[reducible, simp, alias]
  def cause.principled : Prop := c.dscotus

  /-- The *first gap problem* is showing that if 
      the necessary being is a first cause of all 
      things in some possible world, then it is God.
      A causal structure `c` is said to contain **no first gap**
      if this gap problem admits a solution with respect to `c`.
      Solutions of the gap problem are proofs of the 
      `c.nogap₂` proposition, and may be called **(primary) gap fillers**
      or **(stage 2) cosmological arguments**. -/
  def cause.nogap₁ : Prop := c.principled → ω.theism

  /-- The *conjoined gap problem* is showing that if 
      the necessary being is a first cause of all 
      things in some possible world, then it is **the classical theistic** God.
      A causal structure `c` is said to contain **no gap**
      if this gap problem admits a solution with respect to `c`.
      Solutions of the gap problem are proofs of the 
      `c.nogap₁₂` proposition, and may be called **(both primary and secondary) gap fillers**
      or **(stage 2) cosmological arguments**. -/
  def cause.nogap₁₂ : Prop := c.principled → ω.ctheism


end divine_properties

/-- A **Theos** is a conception of God compatible with `greek_theism`. 
    It is God from the point of view of classical pagan theology. -/
structure theos (ω : ontology) :=
  (s : ω.substance)
  (necessary : s.necessary)
  (simple : s.simple)

/-- A **God** is a **Theos** with the attribute of **Divine Aseity**.
    Assumption of aseity is sufficient for proving all the properties
    of the classical theistic God.
    God is here taken as a synonym for "Deus", 
    or "the classical latin, or scholastic, conception of God". -/
structure god (ω : ontology) extends theos ω :=
  (aseity : ∃ w : ω.world, ∀ s' ∈ w.substances, s' = s)

@[reducible, simp]
def god.up (g : ω.god) := g.to_theos 

section theos

  variable (g : ω.theos)

  @[simp]
  theorem theos_iff_theism : nonempty ω.theos ↔ ω.theism :=
    begin
      refine ⟨λne,_, λh,⟨⟨ω.nb, rfl, h⟩⟩⟩,
      obtain ⟨g⟩ := ne,
      simp [theism, -substance.simple],
      have c := g.necessary, simp [substance.necessary] at c,
      rw ←c, exact g.simple,
    end

  def theos.theism := theos_iff_theism.mp ⟨g⟩

  /-- God is a purely actual substance. -/
  lemma theos.purely_actual : g.s.purely_actual :=
    begin
      have c := g.theism,
      replace c := theism_iff_purely_actual.mp c,
      obtain ⟨s, hs⟩ := c,
      have c := g.necessary,
      simp [substance.necessary] at c, rw c, clear c,
      have c := s.eq_nb_of_purely_actual hs,
      simp [substance.necessary] at c, 
      rwa ←c,
    end
  
  theorem monotheism : ∀ g g' : ω.theos, g = g' :=
    begin
      intros g g',
      casesm* ω.theos, simp,
      simp [substance.necessary] at *,
      rw g_necessary,
      rw g'_necessary,
    end
  
  -- WORK IN PROGRESS (RELATED TO 4TH WAY).
  -- /-- God is a fixed point of any possessed property He may possibly exemplify.
  --     As such we say that He is his Omnipotence, His Omniscience, His benevolence,
  --     and whatever else is predicated of Him, *in the precise and non-paradoxical sense*
  --     that the *event* of God being (e.g.) Omnipotent is the *event* of God existing,
  --     and also the *event* of Him being Omniscient, etc...
  --     This would actually be valid for any simple substance as well.
  --     -/
  -- theorem divine_simplicity : ∀ p : ω.predicate, p.possessed → ⋄p g.s → p g.s = g.s.exists := sorry

  -- WORK IN PROGRESS (RELATED TO 4TH WAY).
  -- /-- God is maximally perfect w.r.t. any analogy of being. -/
  -- theorem theos.maximally_perfect : ∀ (g : ω.theos) (b : ω.being), g.s.up.mperfect b.is := sorry

end theos

section god

  variable (g : ω.god)

  @[simp]
  theorem god_iff_ctheism : nonempty ω.god ↔ ω.ctheism :=
    begin
      refine ⟨λh,_, λh,⟨⟨⟨ω.nb, rfl, _,⟩,_⟩⟩⟩,
        obtain ⟨g⟩ := h,
        obtain ⟨w, hw⟩ := g.aseity,
        use w, intros e₁ e₂ h₁ h₂,
        have c₀ : ∀ e : ω.entity, e.exists w → e.perfect,
          intros e he,
          by_contradiction c₀,
          let a : ω.accident := ⟨e, c₀⟩,
          specialize hw a.owner,
          simp [world.substances] at hw,
          specialize hw _, swap,
            exact entails_of_inheres a.inh_owner he,
          have c₁ := a.inh_owner, rw hw at c₁,
          have c₂ := g.simple, simp [substance.simple, set.nonempty] at c₂,
          specialize c₂ a,
          contradiction,
        have c₁ := c₀ e₁ h₁,
        have c₂ := c₀ e₂ h₂,
        clear c₀,
        let s₁ : ω.substance := ⟨e₁, c₁⟩,
        let s₂ : ω.substance := ⟨e₂, c₂⟩,
        simp [world.substances] at *,
        have c₃ := hw s₁ h₁, simp [s₁] at c₃,
        have c₄ := hw s₂ h₂, simp [s₂] at c₄,
        rw ← c₄ at c₃, simp at c₃,
        exact c₃,
      by_contradiction c,
      simp [substance.simple, ext_iff] at c,
      obtain ⟨a, ha⟩ := c,
      obtain ⟨w, hw⟩ := h,
      let a' := a.localize w,
      specialize hw a' ω.nbe (a.localize_exists _) (by simp [nbe]), swap,
        rw (unique_inheres a.inh_owner ha),
        simp [nb, nbe],
      unfold_coes at hw,
      simp [-entity_ext_iff] at hw,
      have c₁ := a'.imperfect,
      have c₂ := ω.nb.perfect, simp [nb, -self_subsist] at c₂,
      rw hw at c₁,
      contradiction,
        obtain ⟨w, hw⟩ := h,
        use w,
        intros s hs, simp,
        simp [world.substances] at hs,
        specialize hw s.up ω.nbe hs (by simp [nbe]),
        simp at hw,
        apply substance_ext,
        exact hw,
    end

  def god.ctheism := god_iff_ctheism.mp ⟨g⟩

  theorem uniqueness_of_god : ∀ g g' : ω.god, g = g' :=
    by intros g g'; casesm* ω.god; simp; apply monotheism
  
  /-- God is a purely actual substance. -/
  lemma god.purely_actual : g.s.purely_actual := g.up.purely_actual

  -- WORK IN PROGRESS (RELATED TO 4TH WAY).
  -- /-- God is maximally perfect w.r.t. any analogy of being. -/
  -- theorem god.maximally_perfect : ∀ (g : ω.god) (b : ω.being), g.s.up.mperfect b.is := sorry

  lemma weakly_parmenidean_iff₄ : ω.weakly_parmenidean ↔ ω.ctheism :=
    begin
      simp [weakly_parmenidean, ctheism, set.nonempty, parmenidean],
      constructor; rintros ⟨w, hw⟩; use w; intros,
        transitivity ω.nbe.exists, apply hw, assumption,
        symmetry, apply hw, assumption,
      apply hw, assumption,
      simp [nbe, ext_iff],
    end

  /-- God is absolutely real. -/
  theorem god.absolutely_real : g.s.up.absolutely_real :=
    begin
      convert weakly_parmenidean_iff₃.mp _,
        have := g.necessary,
        cases g.to_theos.s,
        simp [substance.necessary, nb] at this,
        simpa,
      apply weakly_parmenidean_iff₄.2,
      exact g.ctheism,
    end

  theorem ctheism_of_no_universe : (¬∃ e : ω.entity, e.contingent) → ω.ctheism :=
    begin
      intro h,
      push_neg at h,
      obtain ⟨w⟩ := ω.wne,
      use w,
      intros e₁ e₂ h₁ h₂, clear h₁ h₂,
      rw h e₁,
      rw h e₂,
    end 
  
  theorem ctheism_of_no_universe₂ : ∀ {w}, (¬∃ e : ω.entity, e.contingent ∧ e.exists w) → ω.ctheism :=
    begin
      intros w h,
      push_neg at h,
      use w,
      intros e₁ e₂ h₁ h₂,
      have c₁ := h e₁,
      have c₂ := h e₂,
      simp [h₁,h₂] at *, clear h h₁ h₂,
      rw c₁, rw c₂,
    end 

  /-- If there are contingent substances, `ω.ctheism` is true
      if and only if the universe is contingent, otherwise
      there is no universe (of contingent things) and in this case also
      `ω.ctheism` is true.
      -/
  theorem ctheism_iff_universe_contingent : (Sup $ @entity.contingent ω).contingent ∨ (¬∃ e : ω.entity, e.contingent) ↔ ω.ctheism :=
    begin
      by_cases c : (set.nonempty $ @entity.contingent ω);
      simp [Sup, c],
      swap,
      have c' := ctheism_of_no_universe c,
      simp [c'],
      simp [set.nonempty, has_mem.mem, set.mem] at c,
      right, exact c,
        constructor; intro h,
          cases h,
            simp [has_Sup.Sup, c, entity_Sup, ext_iff] at h,
            obtain ⟨w, hw⟩ := h,
            simp [nbe] at hw,
            use w, intros e₁ e₂ h₁ h₂,
            have c₁ := hw e₁, 
            replace c₁ : e₁ = ω.nbe, 
              finish [has_mem.mem, set.mem, h₁],
            have c₂ := hw e₂, 
            replace c₂ : e₂ = ω.nbe, 
              finish [has_mem.mem, set.mem, h₂],
            rw c₁, rw c₂,
          refine ctheism_of_no_universe _,
          push_neg,
          intro e,
          apply entity_ext,
          exact h e,
        left,
        simp [has_Sup.Sup, c, entity_Sup, nbe, ext_iff],
        obtain ⟨w, hw⟩ := h,
        use w, intros e he insanity,
        simp [has_mem.mem, set.mem, -entity_ext_iff] at he,
        specialize hw e ω.nbe insanity (by simp [nbe]),
        contradiction,
    end

  -- THIS SECTION IS A WORK IN PROGRESS.
  section power_and_will

    variables (c : ω.cause) (e : ω.entity)

    -- TODO: causal structures in this section will probably need to be constrained by
    -- some plausible assumptions in order to make the following theorems true.
    -- Figure out which assumptions before doing the proofs.

    -- theorem god.omnipotent : c.omnipotent g.s.up := sorry
    -- theorem to_be_is_to_be_caused_by_god : c.causes g.s e = e := sorry
    -- theorem creation_preceeds_matter : ¬∃ context : ω.event, c.causes g.s e ⇒ context ∧
    --                                     c.causes g.s e ≠ context ∧ ¬□context := sorry
    -- theorem god.free : c.is_free g.s := sorry


  end power_and_will

end god

section atheism

  /-- Atheism is committed to the existence of complemented entities. -/
  theorem atheism_positive_commitments : ω.atheism ↔ ∃ e : ω.entity, e.complemented :=
    begin
      simp [atheism, theism, set.nonempty],
      constructor; rintro ⟨a, ha⟩,
        have := compl_iff_inheres_nb.mp ha,
        exact ⟨a, this⟩,
      have : a.imperfect,
        have c := closure_eq_of_is_closed ha.2.2,
        replace ha := ha.1,
        simp [entity.contingent, nbe] at ha,
        simp [entity.imperfect, entity.perfect],
        rwa c,
      use ⟨a, this⟩,
      apply compl_iff_inheres_nb.2 _, 
      assumption,
    end

  lemma atheism_has_universe : ω.atheism → ∃ e : ω.entity, e.contingent :=
    by contrapose; intro h; simp; exact theism_of_ctheism (ctheism_of_no_universe h)

  lemma eq_nbe_Sup_of_atheism : ω.atheism → ω.nbe = Sup entity.contingent :=
    begin
      intro h,
      have c := (@ctheism_iff_universe_contingent ω).mp,
      replace c := λh₀, theism_of_ctheism (c h₀),
      replace c : ¬(Sup entity.contingent).contingent, finish,
      simp [-entity_ext_iff] at c,
      symmetry,
      exact c,
    end
    

end atheism

end ontology