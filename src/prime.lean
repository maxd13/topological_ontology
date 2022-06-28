import ontology
open set topological_space classical
set_option pp.generalized_field_notation true
local attribute [instance] prop_decidable
noncomputable theory

namespace ontology

variable {ω : ontology}

-- We discuss prime entities, topological subbasis, basis, open covers and some definitions involving compact sets.
section prime

  variables (e : ω.entity)

  /-- An entity `e` is said to be **meet prime**, 
      or **meet irreducible**, if 
      for any entities `e₁, e₂` whose
      nonempty conjunction entails `e`,
      one of them must entail `e`. 
      This is equivalent to the principal ideal of `e` in
      the partial order of opens being prime. -/
  def entity.mprime := 
    ∀ ⦃e₁ e₂ : ω.entity⦄ ⦃h : e₁.compatible e₂⦄,
    (h.inter ⇒ e) → (e₁ ⇒ e ∨ e₂ ⇒ e)

  /-- An entity `e` is said to be **join prime**, 
      or **join irreducible**, if 
      for any entities `e₁, e₂` whose
      disjunction is entailed by `e`,
      `e` must entail one of them. 
      This is equivalent to the principal filter of `e`
      in the partial order of opens being prime. -/
  def entity.jprime := ∀ ⦃e₁ e₂ : ω.entity⦄, (e ⇒ e₁ ⊔ e₂) → (e ⇒ e₁ ∨ e ⇒ e₂)

  /-- An entity is **completely join prime** if it is join prime and compact.
      This is also occasionally known as the property of being **supercompact**. -/
  def entity.cjprime := e.jprime ∧ e.compact

  /-- An entity `e` is said to be **prime** if it is both join prime and meet prime. -/
  def entity.prime := e.jprime ∧ e.mprime

  /-- An entity `e` is said to be **completely prime** if it is both prime and compact. -/
  def entity.cprime := e.prime ∧ e.compact
  
  /-- An entity is said to be **absolutely basic** if it belongs to every topological basis
      of open sets. -/
  def entity.abasic := ∀ {B : set ω.event}, is_topological_basis B → e.exists ∈ B

  /-- An entity is said to be **absolutely sub-basic** if it belongs to every `subbasis` -/
  def entity.asubasic := ∀ {B : set ω.event}, is_subbasis B → e.exists ∈ B
  
  /-- Definition of **open cover**. -/
  def entity.cover (S : set ω.event) : Prop := 
    (∀ (ev : ω.event), ev ∈ S → ev.entitative) ∧
    e ⇒ ⋃₀ S
  
  /-- Definition of **Minimal open cover**. -/
  def entity.mcover (S : set ω.event) : Prop := 
    e.cover S ∧ ∀ ev ∈ S, ¬ e.cover (S-{ev})

  
  /-- Definition of **Exact Minimal open cover**. -/
  def entity.emcover (S : set ω.event) : Prop := 
    e.mcover S ∧ ⋃₀ S ⇒ e

  -- TODO: change the definitions below to use covers.
  -- Also consider getting rid of the uncoverable' definition.
  -- In order to do that, it is necessary to change some proofs that need it,
  -- and they become more annoying due to the necessity of casting 
  -- entitative events to entities.

  /-- An entity `e` is said to be **uncoverable** if all of its open covers contain a superset of `e`.
      Notice that if the cover is a subset cover this implies that the cover must contain `e`,
      so any cover of `e` by its subsets must be trivial in this sense. -/
  def entity.uncoverable := ∀ ⦃S : set ω.event⦄, (∀ (ev : ω.event), ev ∈ S → ev.entitative) → S.nonempty → e ⇒ ⋃₀ S → ∃ e₂ ∈ S, e ⇒ e₂
  def entity.uncoverable' := ∀ ⦃S : set ω.entity⦄, S.nonempty → e ⇒ Sup S → ∃ e₂ ∈ S, e ⇒ e₂

  
  /-- An entity `e` is said to be **minimally uncoverable** if all of its minimal open covers contain a superset of `e`.
      Notice that if the cover is a subset cover this implies that the cover must contain `e`,
      so any minimal cover of `e` by its subsets must be trivial in this sense. -/
  def entity.muncoverable := ∀ ⦃S : set ω.event⦄, e.mcover S → ∃ ev ∈ S, e ⇒ ev

  /-! # The following definitions concern entities which are prime in a substantial sense: -/

  /-- Definition of a **Minimal Substantial Cover** of an entity. -/
  def entity.mscover (S : set ω.event) : Prop :=
    e.mcover S ∧ ∀ (s : ω.event), s ∈ S → s.dense

  /-- An entity `e` is said to be **substantially meet prime**,
      or **substantially meet irreducible**, if 
      for any substances `s₁, s₂` whose
      conjunction entails `e`,
      one of them must entail `e`. -/
  def entity.smprime := 
    ∀ ⦃e₁ e₂ : ω.entity⦄, e₁.exists.dense → e₂.exists.dense →
    (e₁.exists ∩ e₂ ⇒ e) → (e₁ ⇒ e ∨ e₂ ⇒ e)

  /-- An entity `e` is said to be **substantially join prime**,
      or **substantially join irreducible**, if 
      for any substances `s₁, s₂` whose
      disjunction is entailed by `e`,
      `e` must entail one of them. -/
  def entity.sjprime := 
    ∀ ⦃e₁ e₂ : ω.entity⦄, e₁.exists.dense → e₂.exists.dense →
    (e ⇒ e₁.exists ∪ e₂.exists) → (e ⇒ e₁ ∨ e ⇒ e₂)

  /-- An entity `e` is said to be **substantially prime** if it is both substantially join prime and substantially meet prime. -/
  def entity.sprime := e.sjprime ∧ e.smprime

end prime

-- We prove important properties concerning prime entities and basis and relate them to iontologies. 
section prime_lemmas
  variables (e : ω.entity)

  @[simp]
  lemma uncoverable'_iff_uncoverable : e.uncoverable' ↔ e.uncoverable :=
    sorry
    -- begin

    --   -- simp [entity.uncoverable, entity.uncoverable'],
    --   -- constructor; intros,
    -- end

  lemma entity.cprime.to_cjprime {e : ω.entity} : e.cprime → e.cjprime :=
    λ h, ⟨h.1.1, h.2⟩

  lemma entity.mprime.induction {e : ω.entity} : e.mprime → ∀ {S : set ω.event}, S.nonempty →
                              finite S → (⋂₀ S).nonempty → ⋂₀ S ⇒ e → ∃ e₂ ∈ S, e₂ ⇒ e :=
  sorry
  -- begin
  --   intros h₀ S ne h₁,
  --   revert ne,
  --   apply h₁.induction_on,
  --     intro absurd,
  --     simp [set.nonempty] at absurd,
  --     contradiction,
  --   intros e₂ s h₃ h₄ h₅ h₆ h₇, clear h₆,
  --   by_cases c : s.nonempty, swap,
  --     replace c := not_nonempty_iff_eq_empty.mp c,
  --     simp [c] at h₇,
  --     simp [c, h₇],
  --   specialize h₅ c, clear c,
  --   have aux : ⋂₀ insert e₂ s = e₂ ∩ ⋂₀ s,
  --     simp [insert, set.insert, sInter, Inf, has_Inf.Inf, complete_lattice.Inf],
  --     ext w, constructor; intro hyp; simp at *,
  --       have c := hyp e₂, simp at c,
  --       refine ⟨c, _⟩, intros t ht,
  --       exact hyp t (or.inr ht),
  --     rintros t (ht|ht),
  --       rw ht, exact hyp.1,
  --     apply hyp.2; assumption,
  --   rw aux at h₇,
  --   specialize h₅ (subset_inter_iff.mp h₇).2,
  --   obtain ⟨e₃, H, he₃⟩ := h₅,
  --   refine ⟨e₃, _, he₃⟩,
  --   apply mem_insert_of_mem; assumption,
  -- end


  lemma entity.jprime.induction {e : ω.entity} : e.jprime → ∀ {S : set ω.entity}, S.nonempty →
                              finite S → e ⇒ Sup S → ∃ e₂ ∈ S, e ⇒ e₂ :=
    begin
      intros h₀ S ne h₁,
      revert ne,
      apply h₁.induction_on,
        intro absurd,
        simp [set.nonempty] at absurd,
        contradiction,
      intros e₂ s h₃ h₄ h₅ h₆ h₇,
      simp [Sup, has_Sup.Sup, h₆] at *,
      simp [has_entailment.entails] at *,
      clear h₆,
      by_cases c : s.nonempty, swap,
        replace c := not_nonempty_iff_eq_empty.mp c,
        simp [entity_Sup] at h₇,
        rw c, rw c at h₇, simp at h₇,
        exact ⟨e₂, by simp, h₇⟩,
      specialize h₅ c,
      simp [c] at h₅,
      simp [entity.jprime, entity_sup] at h₀,
      simp [has_entailment.entails] at h₀,
      have aux : entity_Sup (insert e₂ s) h₆ = e₂ ⊔ entity_Sup s c, 
        simp [has_Sup.Sup, has_sup.sup, entity_Sup, entity_sup],
      rw aux at h₇,
      specialize h₀ h₇,
      cases h₀, exact ⟨e₂, by simp, h₀⟩,
      specialize h₅ h₀,
      obtain ⟨x, hx₁, hx₂⟩ := h₅,
      exact ⟨x, by simp [hx₁], hx₂⟩,
    end

  lemma jprime_iff_muncoverable : e.jprime ↔ e.muncoverable := 
    begin
      constructor; intro h,
        rintros S ⟨⟨h₁,h₂⟩, h₃⟩,
        have ne : S.nonempty, admit,
        obtain ⟨ev, hev⟩ := ne,
        by_cases c₀ : (S-{ev}).nonempty, swap,
          admit,
        by_cases c₁ : e ⇒ ev,
          exact ⟨ev, hev, c₁⟩,
        have c : ⋃₀ S = ev ∪ ⋃₀ (S-{ev}),
          admit,
        rw c at h₂, clear c,
        exfalso,
        specialize h₃ ev hev, simp [entity.cover] at h₃,
        apply h₃; clear h₃,
          intros ev' hev' aux, clear aux,
          exact h₁ ev' hev',
        have c₁ := h₁ ev hev,
        have c₂ : event.entitative (⋃₀ (S-{ev})), admit,
        let e₁ : ω.entity := ⟨ev, c₁.1, c₁.2⟩,
        let e₂ : ω.entity := ⟨⋃₀ (S-{ev}), c₂.1, c₂.2⟩,
        specialize @h e₁ e₂ h₂, cases h;
        simp [e₁, e₂, has_entailment.entails] at h, clear e₁ e₂,
          contradiction,
        exact h,
      intros e₁ e₂ h₀,
      by_contradiction contra, push_neg at contra,
      obtain ⟨h₁, h₂⟩ := contra,
      let S : set ω.event := {e₁, e₂},
      suffices c : e.mcover S,
        specialize h c,
        simp [S] at h,
        obtain ⟨ev, ⟨rfl⟩|⟨rfl⟩, absurd⟩ := h;
        contradiction,
      clear h, constructor, constructor;
        simp [S], rintros ev (⟨rfl⟩|⟨rfl⟩);
        unfold_coes; simp, unfold_coes,
        simp [has_sup.sup, entity_sup, has_entailment.entails] at h₀,
        convert h₀ using 1, exact sup_comm,
      simp [S], rintros ev (⟨rfl⟩|⟨rfl⟩);
      intros h; unfold_coes at h; replace h := h.2,
      -- by_cases c : e₁ = e₂;
      --     try {
      --       cases c,
      --       simp [has_entailment.entails, has_sup.sup, entity_sup] at h₀,
      --       contradiction,
      --     },
      replace h : e ⇒ e₁,
        admit,
        -- simp [has_entailment.entails] at h,
        -- simp [has_entailment.entails],
        -- convert h using 1,
        -- simp [ext_iff],
      swap, replace h : e ⇒ e₂, admit,
      all_goals {contradiction},
    end

  lemma cjprime_iff_uncoverable' : e.cjprime ↔ e.uncoverable' :=
    begin
      constructor; intro h,
        obtain ⟨pe, ce⟩ := h,
        intros S neS hS,
        replace ce := ce.elim neS hS,
        obtain ⟨s, sne, h₁, h₂, h₃⟩ := ce,
        replace pe := pe.induction sne h₂ h₃,
        obtain ⟨e₂, h₄, h₅⟩ := pe,
        exact ⟨e₂, h₁ h₄, h₅⟩,
      constructor,
        intros e₁ e₂ h₁,
        let s : set ω.entity := {e₁, e₂},
        have c : s.nonempty, use e₁, simp,
        specialize h c, simp [s, -entity_ext_iff] at h,
        specialize h h₁,
        obtain ⟨e',h|h, h₂⟩ := h; rw h at h₂; simp [h₂],
      apply compact_of_finite_subcover,
      intros type U hU h₁,
      let S : set ω.entity := {e : ω.entity | ∃ i, U i = e.exists},
      have ne : S.nonempty,
        simp [S, set.nonempty],
        by_contradiction contra,
        push_neg at contra,
        have c : ∀ i, U i = ∅,
          by_contradiction contra₂,
          push_neg at contra₂,
          obtain ⟨i, hi⟩ := contra₂,
          replace hi := ne_empty_iff_nonempty.mp hi,
          let e' : ω.entity := ⟨U i, hU i, hi⟩,
          specialize contra e' i,
          simp [e'] at contra,
          contradiction,
        obtain ⟨w, hw⟩ := e.possible,
        specialize h₁ hw, simp at h₁,
        obtain ⟨i, hi⟩ := h₁,
        specialize c i,
        rw c at hi, simp at hi,
        contradiction,
      specialize h ne _, swap,
        simp [Sup, has_Sup.Sup, entity_Sup, ne, has_entailment.entails, S, set.subset],
        intros w hw,
        specialize h₁ hw, simp at h₁,
        obtain ⟨i, hi⟩ := h₁,
        let e' : ω.entity := ⟨U i, hU i, ⟨w, hi⟩⟩,
        refine ⟨e', ⟨i, _⟩, _⟩; simp [e'],
        assumption,
      obtain ⟨e₂, ⟨i, hi⟩, h⟩ := h,
      use ({i} : finset type), simp,
      rwa hi,
    end

  lemma cjprime_iff_uncoverable : e.cjprime ↔ e.uncoverable :=
    by convert cjprime_iff_uncoverable' e; ext; symmetry; exact uncoverable'_iff_uncoverable e

  theorem asubasic_iff_cprime : e.asubasic ↔ e.cprime :=
    begin
      constructor; intro h,
        admit,
      intros B h,
      obtain ⟨h₁, h₂⟩ := h,
      specialize h₂ e,
      obtain ⟨I, ne, S, ⟨h₂, h₃⟩⟩ := h₂,
      unfold_coes at h₃,
      have imp_e : ∀ i, ⋂₀ S i ⇒ e,
        intro i,
        have c := subset_Union (λ i, ⋂₀ S i) i,
        simp at c,
        rwa h₃ at c,
      have c := (cjprime_iff_uncoverable' e).mp h.to_cjprime,
      simp at c,
      rw ←sUnion_range at h₃,
      set B' := { s | s ∈ range (λ (x : I), ⋂₀ S x) ∧ s.nonempty},
      have neB' : B'.nonempty,
        simp [B', range, set.nonempty],
        by_contradiction contra,
        push_neg at contra,
        have c : ∀ i, ⋂₀ S i = ∅,
          intro i,
          specialize contra (⋂₀ S i),
          cases contra,
            specialize contra i,
            contradiction,
          apply not_nonempty_iff_eq_empty.mp,
          rintro ⟨w, hw⟩,
          specialize contra w,
          contradiction,
        replace c : (λ (x : I), ⋂₀ S x) = (λ (x : I), ∅),
          funext i, exact c i,
        rw c at h₃,
        simp [range, sUnion, ext_iff] at h₃,
        obtain ⟨w, hw⟩ := e.possible,
        specialize h₃ w, simp [hw] at h₃,
        obtain ⟨empty, ⟨i, absurd⟩, insanity⟩ := h₃,
        specialize absurd w,
        contradiction,
        clear ne,
      have hB' : ∀ (ev : ω.event), ev ∈ B' → ev.entitative,
        intros ev hev,
        simp [B', range] at hev,
        obtain ⟨⟨i, hi⟩, ne⟩ := hev,
        refine ⟨_, ne⟩,
        rw ←hi,
        apply is_open_sInter (h₂ i).1,
        intros t ht,
        replace ht := (h₂ i).2.2 ht,
        replace ht := h₁ t ht,
        exact ht.1,
      replace c := c hB' neB',
      specialize c _, swap,
        simp [has_entailment.entails],
        rw ←h₃,
        simp [sUnion, set.subset],
        intros w S' i hS' hw,
        exact ⟨S',⟨⟨i,hS'⟩,⟨w,hw⟩⟩,hw⟩,
      obtain ⟨e₂, H, he₂⟩ := c,
      simp [B', range] at H,
      obtain ⟨⟨i, hi⟩, aux⟩ := H, clear aux,
      rw ←hi at he₂, clear hi e₂,
      clear h₁ h₃ neB' hB' B',
      specialize h₂ i,
      obtain ⟨h₁, h₂, h₃⟩ := h₂,
      have c : (⋂₀ S i).nonempty,
        obtain ⟨w, hw⟩ := e.possible,
        replace hw := he₂ hw,
        exact ⟨w, hw⟩,
      replace h := h.1.2.induction h₂ h₁ c (imp_e i),
      clear c,
      obtain ⟨e₂, H, h⟩ := h,
      have c : e ⇒ e₂,
        have c := sInter_subset_of_mem H,
        exact subset.trans he₂ c,
      replace c := eq_of_subset_of_subset c h,
      unfold_coes at c,
      specialize h₃ H,
      rwa c,
    end

  lemma absolutely_real_iff_asubasic : e.absolutely_real ↔ e.asubasic :=
    begin
      constructor; intros h,
        intros B basis,
        specialize h basis.intensionalize,
        simp [entity.real, iontology.ientity.up] at h,
        obtain ⟨ie, hie⟩ := h,
        rw ←hie,
        change (subtype B) at ie,
        exact ie.property,
      intros Ω,
      simp [entity.real],
      specialize h Ω.axiom₁,
      simp [range] at h,
      simpa [entity.real, iontology.ientity.up, iontology.ientity.exists],
    end
  
  lemma absolutely_real_iff_cprime : e.absolutely_real ↔ e.cprime := sorry

  -- theorem abasic_iff_cjprime : e.abasic ↔ e.cjprime :=
  --   begin
  --     simp [entity.abasic, entity.cjprime],
  --     constructor; intro h, swap,
  --       intros B hB,
  --   end
end prime_lemmas

-- lemmas involving prime entities and the necessary being
section nb_lemmas

  lemma nbe.mprime : ω.nbe.mprime := sorry

  theorem weakly_parmenidean_iff₀ : ω.weakly_parmenidean ↔ ω.nbe.uncoverable :=
    begin
      simp,
      constructor; intro h,
        obtain ⟨w, hw⟩ := h,
        simp [parmenidean] at hw,
        intros S hS₁ hS₂ h, clear hS₂,
        simp [nbe, has_entailment.entails, set.subset] at h,
        specialize @h w,
        obtain ⟨ev, hev, h⟩ := h,
        specialize hS₁ ev hev,
        specialize hw ⟨ev, hS₁.1, hS₁.2⟩ h, simp at hw,
        refine ⟨ev, hev, _⟩, rw hw,
        simp [has_entailment.entails, set.subset],
      let S := {ev : ω.event | ev.contingent ∧ ev.entitative},
      specialize @h S _, swap,
        intros ev hev, exact hev.2,
      simp [nbe, has_entailment.entails, set.subset] at h,
      simp [set.nonempty, parmenidean],
      by_contradiction contra, push_neg at contra,
      by_cases c : S.nonempty, swap,
        simp [set.nonempty] at c,
        obtain ⟨w⟩ := ω.wne,
        specialize contra w,
        obtain ⟨e, hw, he⟩ := contra,
        simp [nbe] at he,
        specialize c e.exists w hw he,
        have absurdity := e.entitative,
        contradiction,
      specialize h c, clear c,
      specialize h _, swap,
        intro w, specialize contra w,
        obtain ⟨e, hw, he⟩ := contra,
        simp [nbe] at he,
        exact ⟨e.exists, ⟨⟨⟨e.possible,he⟩,e.entitative⟩,hw⟩⟩,
      clear contra,
      obtain ⟨insanity, ⟨⟨sophistry, illusion⟩, gibberish⟩, nonsense⟩ := h,
      have absurdity : insanity = univ,
        simpa [ext_iff],
      contradiction,
    end
  theorem weakly_parmenidean_iff₁ : ω.weakly_parmenidean ↔ ω.nbe.cprime :=
    begin
      convert weakly_parmenidean_iff₀,
      ext, constructor; intro h,
        replace h := h.to_cjprime,
        replace h := (cjprime_iff_uncoverable' ω.nbe).mp h,
        simp at h, assumption,
      replace h := (cjprime_iff_uncoverable ω.nbe).2 h,
      exact ⟨⟨h.1, nbe.mprime⟩, h.2⟩,
    end
  theorem weakly_parmenidean_iff₂ : ω.weakly_parmenidean ↔ ω.nbe.asubasic := 
    by convert weakly_parmenidean_iff₁; ext; exact asubasic_iff_cprime ω.nbe
  theorem weakly_parmenidean_iff₃ : ω.weakly_parmenidean ↔ ω.nbe.absolutely_real :=
    by convert weakly_parmenidean_iff₂; ext; exact absolutely_real_iff_asubasic ω.nbe


end nb_lemmas

-- We discuss particulars, universals, optional entities, and some unique notions of covering related to them; 
-- in terms of which the notions of exemplification and subjective parthood can be defined.
section particulars
  
  variable (e : ω.entity)

  /-- An entity is **particular** if it is substantially join prime. -/
  @[reducible, simp]
  def entity.particular := e.sjprime
  /-- An entity is a **(Neo-Aristotelian) universal** if it is not particular. -/
  @[reducible, simp]
  def entity.universal := ¬ e.sjprime
  /-- An entity is said to be a **proper particular** if it is substantially prime. -/
  @[reducible, simp]
  def entity.pparticular := e.sprime
  /-- An entity is said to be an **aggregate**, or an **improper particular**,
      if it is particular but not a proper particular. -/
  @[reducible, simp]
  def entity.aggregate := e.sjprime ∧ ¬ e.smprime
  /-- An entity is said to be an **ultra-particular** if it is prime. -/
  @[reducible, simp]
  def entity.uparticular := e.prime
  /-- An entity is said to be **monadic**, or **point-like**, if it is 
      completely prime. -/
  @[reducible, simp]
  def entity.monadic := e.cprime
  /-- An entity is said to be **angelic (or Divine)** if it is 
      both monadic and dense. -/
  @[reducible, simp]
  def entity.angelic := e.monadic ∧ e.exists.dense

   /-- An entity `e` is said to be **(strictly) directly covered** by an entity `e'`
      if `e ⇒' e'` and for every entity `e''` in between `e` and `e'`, 
       `e''` is either equal to `e` or to `e'`. -/
  def entity.dcovered (e' : ω.entity) := 
    e ⇒' e' ∧ ∀ e'' : ω.entity, 
    e ⇒ e'' → e'' ⇒ e' → e'' = e ∨ e'' = e'

  infixr ` :⇒ `:50 := entity.dcovered

  /-- An entity `e` is said to be **optionally covered** by an entity `e'` 
      if it is uniquely pre-covered by `e'`, i.e. if it is pre-coverd by `e'` but
      not pre-covered by anything else. -/
  def entity.ocovered (e' : ω.entity) := 
    e :⇒ e' ∧ ∀ e'', e :⇒ e'' → e'' = e'

  infixr ` !:⇒ `:50 := entity.ocovered

  /-- An entity is said to be **optional** if it is optionally covered by another. -/
  def entity.optional := ∃ e', e !:⇒ e'

  /-- Definition of **Particular Exact Minimal open cover**. -/
  def entity.pemcover (S : set ω.event) : Prop := 
    e.emcover S ∧ ∀ (s : ω.event), s ∈ S → 
    ∃ e' : ω.entity, e.particular ∧ e'.exists = s
  
  /-- Definition of **Infinite Particular Exact Minimal open cover**. -/
  def entity.ipemcover (S : set ω.event) : Prop := 
    e.pemcover S ∧ S.infinite

  /-- A particular entity `e` is said to **exemplify** another 
      universal entity `u`, just in case there is an unique ipemcover of
      `u` containing `e` which has only perfect elements if `e` is perfect,
      and only imperfect elements if `e` is imperfect. -/
  def entity.exemplifies (u : ω.entity) : Prop := 
    e.particular ∧ u.universal ∧
    ∃! S, u.ipemcover S ∧ e.exists ∈ S ∧
    (e.exists.dense → ∀ s : ω.event, s ∈ S → s.dense) ∧
    (¬ e.exists.dense → ∀ s : ω.event, s ∈ S → ¬ s.dense)

  /-- A particular entity `e` is said to be a **subjective part** of another 
      universal entity `u`, just in case there is an unique pemcover of
      `u` containing `e` which has only perfect elements if `e` is perfect,
      and only imperfect elements if `e` is imperfect.
      "Subjective" comes from the fact that `e` is the subject of
      a predication. -/
  def entity.spart (u : ω.entity) : Prop := 
    e.particular ∧ u.universal ∧
    ∃! S, u.pemcover S ∧ e.exists ∈ S ∧
    (e.exists.dense → ∀ s : ω.event, s ∈ S → s.dense) ∧
    (¬ e.exists.dense → ∀ s : ω.event, s ∈ S → ¬ s.dense)
  
  /-- An entity is said to be a **true universal** if it can be exemplified. -/
  def entity.tuniversal := ∃ e' : ω.entity, e'.exemplifies e

  /-- An universal is said to be a **subjective whole (collection, or set)** 
      if it has subjective parts. -/
  def entity.swhole := ∃ e' : ω.entity, e'.spart e

end particulars

-- lemmas about direct coverings and optional entities
section dcovered_lemmas

  variables (e₁ e₂ : ω.entity) (h₁ : e₁.exists.dense) (h₂ : e₂.exists.dense)
  include h₁ h₂

  lemma ocovered_of_dcovered_smprime : e₁.smprime → e₁ :⇒ e₂ → e₁ !:⇒ e₂ :=
    begin
      intros h₃ h₄,
      refine ⟨h₄, _⟩, 
      intros e₃ h₅,
      admit,
    end


end dcovered_lemmas


end ontology