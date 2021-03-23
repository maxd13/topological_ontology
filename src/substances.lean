import ontology
open set topological_space classical
local attribute [instance] prop_decidable
set_option pp.generalized_field_notation true
noncomputable theory


/-! # Substances and Accidents

  In this module we define the notions of `substance`, `accident`,
  `subsistence`, `inherence`, `cosubstantiality`, `simplicity` and 
  the distinction between `intrinsic` and `extrinsic` accidents.

  We also prove several lemmas associated with these concepts.

-/

namespace ontology

variable {ω : ontology}

-- We next define substances as particular kinds of entities.
-- Accidents are also defined here.
section substances 

  /-- An entity is said to be `perfect` if and only if the set of all possible worlds
      in which it exists is `dense` -/
  def entity.perfect (e : ω.entity) := e.exists.dense
  /-- Negation of `entity.perfect` -/
  def entity.imperfect (e : ω.entity) := ¬ e.perfect

  /-- Individual `substances` in the ontology are dense entities, 
      every other entity is an `accident`.
      We also call a dense entity a perfect entity.
      **Substances** are entities which do not have contraries, 
      and subsist in themselves. -/
  structure substance (ω : ontology) extends entity ω :=
    (perfect : to_entity.perfect)

  /-- An entity which is not a `substance` is an `accident`. 
      **Accidents** have contraries and do not subsist of themselves,
      but must always inhere in another, which is a substance.-/
  structure accident (ω : ontology) extends entity ω :=
    (imperfect : to_entity.imperfect)

  @[reducible, simp]
  def substance.up (s : ω.substance) := s.to_entity
  @[reducible, simp]
  def accident.up (a : ω.accident) := a.to_entity

  instance has_coe_substance₁ : has_coe ω.substance ω.entity := ⟨substance.up⟩
  instance has_coe_substance₂ : has_coe ω.substance ω.event := ⟨λ s, s.exists⟩
  instance has_coe_accident₁ : has_coe ω.accident ω.entity := ⟨accident.up⟩
  instance has_coe_accident₂ : has_coe ω.accident ω.event := ⟨λ a, a.exists⟩

  -- entailment tests:
  -- #reduce λ (s₁ : ω.substance) (s₂ : ω.substance), s₁ ⇒ s₂
  -- #reduce λ (s : ω.substance) (e : ω.entity), s ⇒ e
  -- #reduce λ (s : ω.substance) (e : ω.entity), e ⇒ s
  -- #reduce λ (s : ω.substance) (e : ω.event), s ⇒ e
  -- #reduce λ (s : ω.substance) (e : ω.event), e ⇒ s
  -- #reduce λ (a₁ : ω.accident) (a₂ : ω.accident), a₁ ⇒ a₂
  -- #reduce λ (a : ω.accident) (e : ω.entity), a ⇒ e
  -- #reduce λ (a : ω.accident) (e : ω.entity), e ⇒ a
  -- #reduce λ (a : ω.accident) (e : ω.event), a ⇒ e
  -- #reduce λ (a : ω.accident) (e : ω.event), e ⇒ a
  -- #reduce λ (s : ω.substance) (a : ω.accident), s ⇒ a
  -- #reduce λ (s : ω.substance) (a : ω.accident), a ⇒ s

  -- By this definition, it is obvious that any entity 
  -- is either a substance or an accident, therefore we can
  -- cast it to one of them.

  /-- The **antepredicament** of an `entity` is its status as either a `substance` or an `accident`.
      it casts the entity to either one of them. -/
  def entity.ante (e : ω.entity) : ω.substance ⊕ ω.accident :=
    if h : e.perfect then sum.inl ⟨e, h⟩ else sum.inr ⟨e, h⟩

  /-- An entitative event is substantive if it is dense. -/
  def event.substantive (e : ω.event) : Prop := e.entitative ∧ e.dense
  /-- An entitative event is accidental if it is not dense. -/
  def event.accidental (e : ω.event) : Prop := e.entitative ∧ ¬e.dense

  /-- The `necessary being` (substance) is the substance which exists in every possible world. -/
  def nb (ω : ontology) : ω.substance := ⟨ω.nbe, by simp [nbe, entity.perfect]⟩
  instance substance_inhabited : inhabited ω.substance := ⟨ω.nb⟩

  /-- A substance is `contingent` if it is not the necessary being (substance). -/
  @[reducible, simp]
  def substance.contingent (s : ω.substance) := s ≠ ω.nb
  /-- A substance is `necessary` if it is the necessary being (substance). -/
  @[reducible, simp]
  def substance.necessary (s : ω.substance) := s = ω.nb

  @[reducible, simp]
  def world.substances (w : ω.world) := {s : ω.substance | s.exists w}
  @[reducible, simp]
  def world.accidents (w : ω.world) := {a : ω.accident | a.exists w}

end substances

-- We then prove some very important lemmas for substances which
-- motivate their definition.
section substance_lemmas

  /-- The fundamental fact that justifies the definition of substances
      is that they admit no contrary entities, and this is a property
      explicitly mentioned in Aristotle's *Categories*, which suffices for
      their definition. -/
  lemma substance.nocontrary (s : ω.substance) : s.up.nocontrary :=
    begin
        intros h,
        obtain ⟨e, h⟩ := h,
        simp [entity.contrary] at h,
        rwa inter_comm s.exists e.exists at h,
        let α := e.exists ∩ s.exists, 
        replace h : α = ∅ := h,
        suffices c : α.nonempty,
            replace c := c.ne_empty,
            contradiction,
        apply dense_iff_inter_open.mp s.perfect,
            exact e.existential,
        exact e.possible,
    end

  lemma substance.compatible (s : ω.substance) (e : ω.entity) : s.up.compatible e := by
    have c := s.nocontrary; push_neg at c; exact event_possible_of_ne_empty (c e)


  /-- main extensionality lemma for substances. -/
  @[ext]
  lemma substance_ext {s₁ s₂ : ω.substance} (h : s₁.exists = s₂.exists) : s₁ = s₂ :=
  by cases_type* substance entity; simp at h; simpa

  lemma perfect_iff_nocontrary : ∀ e : ω.entity, e.nocontrary ↔ e.perfect :=
      begin
        intro e,
        constructor; intro h,
          simp [entity.perfect],
          simp [entity.nocontrary, entity.contrary] at h,
          apply dense_iff_inter_open.2,
          intros U h₁ h₂,
          specialize h ⟨U, h₁, h₂⟩, simp at h,
          rwa inter_comm e.exists U at h,
          exact event_possible_of_ne_empty h,
        exact substance.nocontrary ⟨e, h⟩,
      end

  /-- Any substance existentially depends only on other substances. -/
  lemma perfect_of_substance_entails : ∀{s : ω.substance}{e : ω.entity},
                                          s ⇒ e → e.perfect :=
    begin
        intros s e h,
        have c₀ : closure (s.exists) = univ := s.perfect,
        have c₁ := closure_mono h, unfold_coes at c₁,
        rw c₀ at c₁, clear c₀,
        refine subset.antisymm _ c₁, clear c₁,
        apply subset_univ,
    end

  /-- Arbitrary unions of substances are substances. -/
  def substance_Sup (S : set ω.substance) (h : S.nonempty) : ω.substance :=
    begin
      fconstructor,
          apply entity_Sup (substance.up '' S),
          simp,
          exact h,
      simp [entity.perfect, entity_Sup],
      let sup := ⋃ (s : substance ω) (H : s ∈ S), s.exists,
      suffices : closure sup = univ, exact this,
      obtain ⟨s, hs⟩ := h,
      have c : s.exists ⇒ sup,
          intros w h₂,
          simp, exact ⟨s, hs, h₂⟩,
      replace c := closure_mono c,
      have p : closure s.exists = univ := s.perfect,
      rw p at c,
      exact eq_univ_of_univ_subset c,
    end
    
  /-- Finite intersections of substances are substances. -/
  def substance.meet (s₁ s₂ : ω.substance) : ω.substance :=
    begin
      fconstructor,
          fconstructor,
              exact s₁.exists ∩ s₂.exists,
          exact is_open_and s₁.existential s₂.existential,
              apply dense_iff_inter_open.mp s₂.perfect s₁.exists,
                  exact s₁.existential,
                  exact s₁.possible,
      simp [entity.perfect],
      apply dense_iff_inter_open.2,
      intros U H ne,
      apply event_possible_of_ne_empty,
      intro h,
      let α := (U ∩ (s₁.up).exists) ∩ (s₂.up).exists,
      replace h : α = ∅,
          simp [α,inter_assoc, h],
      suffices c : α.nonempty,
          replace c := c.ne_empty,
          contradiction,
      apply dense_iff_inter_open.mp s₂.perfect,
          exact is_open_inter H s₁.up.existential,
      exact dense_iff_inter_open.mp s₁.perfect U H ne,
    end

  -- instance ccl_substance : conditionally_complete_lattice ω.substance := 
  -- { sup := _,
  -- --   le := infer_instance,
  --   lt := _,
  --   le_refl := _,
  --   le_trans := _,
  --   lt_iff_le_not_le := _,
  --   le_antisymm := _,
  --   le_sup_left := _,
  --   le_sup_right := _,
  --   sup_le := _,
  --   inf := _,
  --   inf_le_left := _,
  --   inf_le_right := _,
  --   le_inf := _,
  --   Sup := _,
  --   Inf := _,
  --   le_cSup := _,
  --   cSup_le := _,
  --   cInf_le := _,
  --   le_cInf := _ }

  --TODO: This proof requires some lemmas about the specialization order.
  /-- Any possible world in which a substance does not exist can be enlarged
      so as to contain the substance. -/
  lemma substance.addable (s : ω.substance) : -s.exists ⇒ s.up.addable := sorry

end substance_lemmas

-- We discuss the fundamental notions of subsistence,
-- inherence and cosubstantiality, 
-- which provide further justification for our definitions.
section subsistence

  /-- An entity `e₁` is said to `subsist` in another entity `e₂`
      if and only if `e₂` can be written as the union of `e₁`
      and its exterior; or alternatively, as the complement of its boundary.
      This entails that `e₂` is perfect. -/
  def entity.subsists (e₁ e₂ : ω.entity) := e₁.exists ∪ ~e₁.exists = e₂.exists

  @[reducible, simp]
  def entity.subsistents (e : ω.entity) := {x : ω.entity | x.subsists e}

  -- Inherence is the same relation defined between accidents and substances:
  /-- **Inherence** is the subsistence of accidents in substances. 
      This is the only possible kind of subsistence for distinct entities, so
      this is simply a type cast from `entity.subsists`. -/
  def accident.inheres (a : ω.accident) (s : ω.substance) := a.up.subsists s.up

  @[reducible, simp]
  def substance.accidents (s : ω.substance) := {a : ω.accident | a.inheres s}

  /-- Only substances can support accidents -/
  lemma sub_support :  ∀ {e₁}, (∃ e₂ : ω.entity, e₂.subsists e₁) → e₁.perfect :=
  begin
      intros e₁ h,
      obtain ⟨e₂, h⟩ := h,
      simp [entity.perfect],
      simp [entity.subsists] at h,
      rw ←h,
      simp [closure_union, ext_iff], intro w,
      by_cases w ∈ closure (e₂.exists),
          simp [h],
      right,
      intro h₃,
      replace h₃ := interior_subset h₃,
      contradiction,
  end

  /-- Every accident inheres into a single substance, 
      therefore we can construct this substance from the accident.
      This is called the **owner** of the accident. -/
  def accident.owner (a : ω.accident) : ω.substance := 
    let e : ω.entity := ⟨ a.exists ∪ ~a.exists
                        , event_union_exterior_open a.existential
                        , event_union_exterior_possible
                        ⟩
    in ⟨e, sub_support ⟨a.up, rfl⟩⟩

  /-- Any entity can be cast to the underlying `substance` in which it subsists. 
      The entity `e` is cast to itself if it is perfect,
      and is cast to its owner if it is imperfect. -/
  def entity.substance (e : ω.entity) : ω.substance :=
    if h : e.perfect then ⟨e, h⟩ else accident.owner ⟨e,h⟩

  /-- Two entities `e₁,e₂` are said to be **cosubstantial** when their underlying substance is the same,
      i.e. when they subsist in the same substance. -/
  def entity.cosubstantial (e₁ e₂ : ω.entity) := ∃ s, e₁.subsists s ∧ e₂.subsists s 

  @[ext]
  lemma cosub_ext {e₁ e₂ : ω.entity} (h : e₁.cosubstantial e₂) : e₁.substance = e₂.substance :=
    begin
      obtain ⟨s, h₁, h₂⟩ := h,
      simp [entity.subsists] at *,
      simp [entity.cosubstantial, entity.substance],
      by_cases c₁ : e₁.perfect;
      by_cases c₂ : e₂.perfect;
      simp [c₁, c₂, accident.owner];
      simp [entity.perfect] at *;
      finish [h₁,h₂,c₁,c₂],
    end

  lemma cosub_ext_iff (e₁ e₂ : ω.entity) : e₁.cosubstantial e₂ ↔ e₁.substance = e₂.substance :=
    begin
      constructor; intro h,
        exact cosub_ext h,
      use e₁.substance,
      simp [entity.subsists, entity.substance] at *,
      by_cases c₁ : e₁.perfect;
      by_cases c₂ : e₂.perfect;
      simp [c₁, c₂, accident.owner];
      simp [c₁, c₂, accident.owner] at h;
      simp [entity.perfect] at c₁;
      simp [entity.perfect] at c₂;
      unfold_coes;
      constructor;
      finish [h,c₁,c₂],
    end

  lemma cosub_ext_iff₂ (e₁ e₂ : ω.entity) : e₁.substance = e₂.substance ↔ e₁.cosubstantial e₂ := 
    by symmetry; exact cosub_ext_iff e₁ e₂

  /-- The set of entities cosubstantial to a given entity `e₁`.
      This is also an alias for `entity.cosubstantial`. -/
  @[reducible, simp, alias]
  def entity.cosubs (e₁ : ω.entity) := {e₂ | e₁.cosubstantial e₂}

  /-- Use `e₁ ≈ e₂` instead of `e₁.cosubstantial e₂` -/
  @[reducible, simp]
  instance setoid_entity : setoid ω.entity := 
    setoid.mk entity.cosubstantial
    ⟨ by simp [reflexive, cosub_ext_iff]
    , by finish [symmetric, entity.cosubstantial]
    , by finish [transitive, cosub_ext_iff]
    ⟩

end subsistence

-- We prove important lemmas about subsistence and inherence.
section subsistence_lemmas
 
  variables {e e₁ e₂ : ω.entity} {a : ω.accident} {s s₁ s₂ : ω.substance}
    
  @[simp]
  lemma entails_of_subsist : e₁.subsists e₂ → e₁ ⇒ e₂ :=
    begin
      intros h w hw,
      simp [entity.subsists] at h,
      unfold_coes,
      rw ←h,
      simp [hw],
    end

  lemma subsists.antisymm : e₁.subsists e₂ → e₂.subsists e₁ → e₁ = e₂ :=
    begin
      intros h₁ h₂,
      apply entity_ext,
      apply subset.antisymm,
        exact entails_of_subsist h₁,
      exact entails_of_subsist h₂,
    end

  @[simp]
  lemma entails_of_inheres : a.inheres s → a ⇒ s := 
    by simp [accident.inheres]; exact entails_of_subsist
    
  /-- An entity is a substance if and only if it subsists in itself. -/
  @[simp] 
  lemma self_subsist : e.perfect ↔ (e.subsists e) :=
    begin
      constructor; intro h,
        ext, constructor; intro h₂,
          cases h₂,
            exact h₂,
          simp [event.exterior, interior_compl] at h₂,
          simp [entity.perfect, event.dense] at h,
          rw h at h₂,
          simp at h₂,
          contradiction,
      simp [h₂],
      apply sub_support,
      use e,
      exact h,
    end

  @[simp]
  lemma substance.ssubsists (s : ω.substance) : s.up.subsists s.up := self_subsist.mp s.perfect

  @[simp]
  lemma accident.inh_owner (a : ω.accident) : a.inheres a.owner :=
    by simp [accident.inheres, accident.owner, entity.subsists]

  /-- An entity only subsists in a single substance -/
  lemma unique_subsists : e.subsists e₁ → e.subsists e₂ → e₁ = e₂ :=
    by intros h₁ h₂; simp [entity.subsists] at *; rwa h₁ at h₂
  
  lemma unique_inheres : a.inheres s₁ → a.inheres s₂ → s₁ = s₂ :=
    begin
      intros h₁ h₂,
      obtain ⟨⟨s₁, op₁, ne₁⟩, pe₁⟩ := s₁,
      obtain ⟨⟨s₂, op₂, ne₂⟩, pe₂⟩ := s₂,
      simp [accident.inheres, entity.subsists] at *,
      rwa h₁ at h₂,
    end

  /-- Only accidents subsist in another entity distinct from themselves -/
  lemma imperfect_of_subsists_other : e.subsists e₁ → e ≠ e₁ → e.imperfect :=
    begin
      intros h₁ h₂ h₃,
      simp at h₃,
      have c := unique_subsists h₃ h₁,
      contradiction,
    end

  @[simp]
  lemma cosub_iff_subsists : e ≈ s.up ↔ e.subsists s.up :=
    begin
      simp [has_equiv.equiv],
      constructor; intro h, swap,
        exact ⟨s, h, s.ssubsists⟩,
      obtain ⟨s₂, h₁, h₂⟩ := h,
      have c := unique_subsists h₂ s.ssubsists,
      rwa c at h₁,
    end

  lemma clopen_of_cosub_nbe : e ≈ ω.nbe → e.exists.clopen :=
    begin
      intros h,
      obtain ⟨s, h₁, h₂⟩ := h,
      have c₀ := unique_subsists h₂ ω.nb.ssubsists,
      rw c₀ at h₁,
      simp [entity.subsists, nb, nbe, ext_iff] at h₁,
      refine ⟨e.existential, _⟩,
      apply closure_eq_iff_is_closed.mp,
      ext w, specialize h₁ w,
      constructor; intro h, swap,
        exact subset_closure h,
      cases h₁, exact h₁,
      contradiction,
    end

  lemma cosub_nbe_of_clopen : e.exists.clopen → e ≈ ω.nbe :=
    begin
      intros h,
      replace h := closure_eq_iff_is_closed.2 h.2,
      simp [has_equiv.equiv],
      use ω.nb,
      refine ⟨_, ω.nb.ssubsists⟩,
      simp [entity.subsists, h],
      unfold_coes,
      simp [nb, nbe],
    end
  
  @[simp]
  lemma clopen_iff_cosub_nbe : ∀ (e : ω.entity), e.exists.clopen ↔ e ≈ ω.nbe :=
    assume e, ⟨cosub_nbe_of_clopen, clopen_of_cosub_nbe⟩

end subsistence_lemmas

-- We delve a little deeper in our definitions concerning accidents.
section accidents

  variables (a : ω.accident) (e : ω.entity) (s : ω.substance)

  /-- An entity is called `simple` if it has no accidents. -/
  @[reducible, simp]
  def entity.simple := ∀ e' : ω.entity, e'.subsists e → e' = e 
  /-- Negation of `entity.simple`. -/
  @[reducible, simp]
  def entity.composite := ¬ e.simple
  /-- A substance is called `simple` if it has no accidents. -/
  @[reducible, simp]
  def substance.simple := s.accidents = ∅
  /-- Negation of `substance.simple`. -/
  @[reducible, simp]
  def substance.composite := s.accidents.nonempty

  /-- `regular` accidents are called `intrinsic`
      and irregular accidents are called `extrinsic`. -/
  @[reducible]
  def accident.intrinsic := a.exists.regular
  /-- Negation of `accident.intrinsic`. -/
  @[reducible]
  def accident.extrinsic := ¬ a.intrinsic

  @[simp]
  def accident.compatible := a.up.compatible e

end accidents

-- And prove lemmas about them
section accident_lemmas

  variable (a : ω.accident)

  /-- All accidents are contingent. -/
  lemma accident.contingent : a.up.contingent := 
    begin
      simp [nbe],
      by_contradiction h,
      have c := a.imperfect,
      simp [entity.imperfect, entity.subsists] at c,
      rw h at c, simp at c,
      contradiction,
    end

  /-- All accidents are simple. -/
  lemma accident.simple : a.up.simple := 
    begin
      simp,
      intros e h,
      have c₁ := sub_support ⟨e, h⟩,
      have c₂ := a.imperfect,
      contradiction,
    end

  /-- Nonempty finite intersections of accidents are accidents. -/
  def accident.compatible.ainter {a₁ a₂ : ω.accident} (h : a₁.compatible a₂.up) : ω.accident :=
    begin
      refine ⟨h.inter, _⟩,
      simp [set_of, entity.imperfect],
      intro h₂,
      set α := h.inter,
      have c₁ : α.exists ⊆ a₁.up.exists,
        simp [α],
        dunfold entity.compatible.inter,
        simp,
      let β : ω.substance := ⟨α, self_subsist.2 h₂⟩,
      have c₂ := @perfect_of_substance_entails _ β a₁.up c₁,
      exact absurd c₂ a₁.imperfect,
    end

  def accident.exterior (a : ω.accident) : ω.accident := 
    begin
      fconstructor,
        fconstructor, 
          exact ~a.exists,
        simp,
          have c := a.imperfect, 
          simp [entity.imperfect, entity.subsists] at c,
          by_contradiction h, 
          simp [event.exterior, set.nonempty] at h,
          replace h := eq_univ_of_forall h,
          rw h at c, simp at c,
          contradiction,
        by_cases c : (~a.exists).dense,
          replace c := compl_inj_iff.2 c,
          simp [ext_iff] at c,
          obtain ⟨w, hw⟩ := a.possible,
          specialize c w,
          simp [interior] at c,
          specialize c a.exists a.existential subset_closure,
          contradiction,
        dunfold entity.imperfect entity.perfect,
        simp at c,
        simpa,
    end

  /-- Use `~e` for "the exterior of `e`" -/
  instance has_tilde_accident : has_tilde ω.accident := ⟨accident.exterior⟩

  @[simp]
  lemma accident.lem : (a.up ⊔ (~a).up) = a.owner := sorry

  lemma compl_iff_inheres_nb {a : ω.accident} : a.inheres ω.nb ↔ a.up.complemented :=
    begin
      simp [accident.inheres],
      constructor; intro h,
        refine ⟨a.contingent, _⟩,
        apply clopen_of_cosub_nbe,
        exact cosub_iff_subsists.2 h,
      apply cosub_iff_subsists.mp,
      apply cosub_nbe_of_clopen,
      exact h.2,
    end

  section extrinsic
  
    variables {a} (h : a.extrinsic)
    include h

    def accident.extrinsic.internalize : ω.accident :=
      begin
        have h₂ := a.owner.compatible (~a).up,
        refine ⟨h₂.inter, _⟩,
        by_contradiction c,
        simp [entity.imperfect, -self_subsist] at c,
        let s : ω.substance := ⟨h₂.inter,c⟩,
        suffices h : (~a).up.perfect,
          have absurdity := (~a).imperfect,
          contradiction,
        apply @perfect_of_substance_entails _ s,
        intro w, unfold_coes,
        intro hw,
        simp [s, entity.compatible.inter] at hw,
        exact hw.2,
      end

    def accident.extrinsic.internalize_inheres : h.internalize.inheres a.owner := sorry
    def accident.extrinsic.internalize_intrinsic : h.internalize.intrinsic := sorry

  end extrinsic

  section intrinsic

    variables {a} (h : a.intrinsic)
    include h

    lemma accident.intrinsic.exterior : (~a).intrinsic := sorry
    lemma accident.intrinsic.exterior_inheres : (~a).inheres a.owner := sorry

    omit h
    lemma intrinsic_of_inheres_nb : a.inheres ω.nb → a.intrinsic := sorry
  end intrinsic

  section localize

    variable (a)
    include a

    def accident.localize (w : ω.world) : ω.accident :=
      if a.exists w then a else 
      if h : a.intrinsic then ~a else
      accident.extrinsic.internalize h

    lemma accident.localize_exists {w : ω.world} : a.owner.exists w → (a.localize w).exists w := sorry
    lemma accident.localize_inheres (w : ω.world) : (a.localize w).inheres a.owner := sorry
    lemma accident.localize_intrinsic (w : ω.world) : (a.localize w).intrinsic := sorry  

  end localize


end accident_lemmas

/-- The Fundamental Theorem of Composites states that any 
    composite substance has an accident in any possible world in which it exists. -/
theorem ftcomposites : ∀ (s : ω.substance), s.composite → ∀ w, s.exists w → 
                       ∃ (a : ω.accident), a ∈ s.accidents ∧ a.exists w  :=
  begin
    intros s h₁ w h₂,
    obtain ⟨a, ha⟩ := h₁,
    use a.localize w,
    simp [substance.accidents] at *,
    have c₀ := a.localize_inheres w,
    have c₁ : s = a.owner,
      apply unique_inheres;
      assumption <|> simp,
    rw ←c₁ at c₀,
    rw c₁ at h₂,
    replace h₂ := a.localize_exists h₂,
    exact ⟨c₀, h₂⟩,
  end

section simplicity_lemmas

  variable (s : ω.substance)

  -- Conjecture: is the converse true?
  @[simp]
  lemma simple_of_connected : s.exists.connected → s.simple :=
    begin
      intro h,
      replace h := h.2,
      simp [is_preconnected] at h,
      simp [ext_iff],
      intros a c,
      specialize h a.exists a.exists.exterior,
      specialize h a.existential a.exterior.existential,
      specialize h _, swap,
        simp,
        simp [accident.inheres, entity.subsists] at c,
        rw c,
      specialize h _, swap,
        focus {
          rw inter_comm,
          apply dense_iff_inter_open.mp s.perfect,
            exact a.existential,
            exact a.possible,
        },
      specialize h _, swap,
        focus {
          rw inter_comm,
          apply dense_iff_inter_open.mp s.perfect,
            exact a.exterior.existential,
            exact a.exterior.possible,
        },
      obtain ⟨w, ⟨hw₀, hw₁, hw₂⟩⟩ := h,
      simp [closure] at hw₂,
      obtain ⟨S, hS, absurdity, insanity⟩ := hw₂,
      specialize absurdity hw₁,
      contradiction,
      -- TODO: once you become convinced
      -- you can't prove the converse,
      -- delete these comments.
      -- refine ⟨s.possible, _⟩,
      -- have c : preconnected_space s.exists → is_preconnected s.to_entity.exists,
      --   rintros ⟨hyp⟩,
      --   simp [is_preconnected] at hyp,
      --   admit,
      -- apply c,
      -- constructor,
      -- simp [is_preconnected],
      -- intros a a' open_a open_a',
      -- intros cover meet_a meet_a',
      -- rw inter_comm,
      -- apply dense_iff_inter_open.mp s.perfect,
      --   exact is_open_inter open_a open_a',
      -- obtain ⟨w, hw⟩ := meet_a,
      -- replace hw := nonempty_of_mem hw.2,
      -- obtain ⟨w', hw'⟩ := meet_a',
      -- replace hw' := nonempty_of_mem hw'.2,
      -- let a₂ : ω.accident,
      --   refine ⟨⟨a, open_a, hw⟩, _⟩,
      -- simp [ext_iff] at h,
      -- specialize h a,
      -- by_contradiction c,
      -- simp [set.nonempty] at c,
    end

  lemma nb_simp_iff_connected : ω.nb.simple ↔ ω.nb.exists.connected :=
    begin
      refine ⟨_, simple_of_connected ω.nb⟩,
      intro h,
      refine ⟨ω.nb.possible, _⟩,
      simp [is_preconnected],
      intros a₁ a₂ open_a₁ open_a₂,
      intros cover meet_a₁ meet_a₂,
      replace cover := subset.antisymm cover _,
        swap,
        simp [nb, nbe],
      simp [nb, nbe] at cover,
      rw inter_comm,
      apply dense_iff_inter_open.mp ω.nb.perfect,
        exact is_open_inter open_a₁ open_a₂,
      obtain ⟨w₁, hw₁⟩ := meet_a₁,
      replace hw₁ := nonempty_of_mem hw₁.2,
      obtain ⟨w₂, hw₂⟩ := meet_a₂,
      replace hw₂ := nonempty_of_mem hw₂.2,
      by_cases c₁ : closure a₁ = univ,
        rw inter_comm,
        apply dense_iff_inter_open.mp c₁; assumption,
      let ac₁ : ω.accident := ⟨⟨a₁, open_a₁, hw₁⟩, c₁⟩,
      simp [substance.simple, ext_iff] at h,
      specialize h ac₁,
      by_contradiction contra,
      suffices c : ac₁.exists.clopen,
        replace c := compl_iff_inheres_nb.2 ⟨ac₁.contingent, c⟩,
        contradiction,
      refine ⟨ac₁.existential, _⟩,
      simp [ac₁],
      dunfold is_closed,
      suffices c : -a₁ = a₂, rwa c,
      simp [ext_iff] at cover,
      simp [set.nonempty] at contra,
      ext w,
      specialize contra w,
      specialize cover w,
      cases cover; finish [cover],
    end

  def connected (ω : ontology) := connected_space ω.world  

  lemma nb_simp_iff_space_connected : ω.nb.simple ↔ ω.connected :=
    begin
      convert nb_simp_iff_connected,
      simp [nb, nbe],
      constructor; intro h,
        obtain ⟨⟨h⟩,⟨w⟩⟩ := h,
        refine ⟨_, h⟩,
        simp,
      exact { is_preconnected_univ := h.2
            , to_nonempty := ω.wne
            },
    end
    

end simplicity_lemmas

-- We also define the related notions for intensional entities:
namespace iontology

  variables {Ω : ω.iontology} (ie₁ ie₂ : Ω.ientity)

  /-- Two ientities `ie₁,ie₂` are said to be **cosubstantial** when their underlying substance is the same,
      i.e. when they subsist in the same substance. -/
  @[reducible, simp]
  def ientity.cosubstantial := ie₁.up.substance = ie₂.up.substance

  /-- The set of ientities cosubstantial to a given ientity `ie₁`.
      This is also an alias for `ientity.cosubstantial`. -/
  @[reducible, simp, alias]
  def ientity.cosubs := {ie₂ | ie₁.cosubstantial ie₂}

  /-- Use `ie₁ ≈ ie₂` instead of `ie₁.cosubstantial ie₂` -/
  @[reducible, simp]
  instance setoid_ientity : setoid Ω.ientity := 
    setoid.mk iontology.ientity.cosubstantial
    ⟨ by simp [reflexive, iontology.ientity.cosubstantial]
    , by finish [symmetric, iontology.ientity.cosubstantial]
    , by finish [transitive, iontology.ientity.cosubstantial]
    ⟩

end iontology

end ontology