import Mathlib

-- ANCHOR: alpha
variable {α: Type*} [Lattice α] [OrderBot α]
-- ANCHOR_END: alpha

-- ANCHOR: Mesh_Props
def disjoint (𝒯 : Finset α): Prop := Set.Pairwise (𝒯 : Set α) Disjoint
def nobot (𝒯 : Finset α) : Prop := ⊥ ∉ 𝒯
-- ANCHOR_END: Mesh_Props

-- ANCHOR: Mesh
abbrev Mesh (α: Type*) [Lattice α] [OrderBot α] :=
  { 𝒯 : Finset α // disjoint 𝒯 ∧ nobot 𝒯 }
-- ANCHOR_END: Mesh

theorem disjoint_subset {s t : Finset α} (h : t ⊆ s) (hd : disjoint s) : disjoint t :=
  fun _ hat _ hbt hne => hd (h hat) (h hbt) hne

theorem nobot_subset {s t : Finset α} (h : t ⊆ s) (hn : nobot s) : nobot t :=
  fun hbot => hn (h hbot)

abbrev singletonMesh (t : α) (ht : t ≠ ⊥) : Mesh α := ⟨{t}, by
  constructor
  · unfold disjoint
    simp only [Finset.coe_singleton, Set.pairwise_singleton]
  · unfold nobot
    apply Finset.not_mem_singleton.mpr
    exact ht.symm⟩

instance : Coe (Mesh α) (Finset α) := ⟨Subtype.val⟩
instance : Membership α (Mesh α) := ⟨fun m x => x ∈ (m : Finset α)⟩
instance : HasSubset (Mesh α) := ⟨fun a b => (a : Finset α) ⊆ (b : Finset α)⟩
instance [DecidableEq α] (m : Mesh α) (x : α) : Decidable (x ∈ m) :=
  Finset.decidableMem x (m : Finset α)
instance : EmptyCollection (Mesh α) := ⟨⟨∅, by simp [disjoint, nobot]⟩⟩
instance [DecidableEq α] : DecidableEq (Mesh α) := Subtype.instDecidableEq
instance [DecidableEq α]: SDiff (Mesh α) := ⟨fun a b => ⟨(a : Finset α) \ (b : Finset α),
  disjoint_subset Finset.sdiff_subset a.2.1,
  nobot_subset Finset.sdiff_subset a.2.2⟩⟩
instance [DecidableEq α]: Inter (Mesh α) := ⟨fun a b => ⟨(a : Finset α) ∩ (b : Finset α),
  disjoint_subset Finset.inter_subset_left a.2.1,
  nobot_subset Finset.inter_subset_left a.2.2⟩⟩

def Mesh.card (m : Mesh α) : ℕ := (m : Finset α).card

-- ANCHOR: partitions
def partitions (𝒯 : Mesh α) (S : α) : Prop :=
  Finset.sup 𝒯 id = S
infix:50 " ↪ " => partitions
-- ANCHOR_END: partitions

-- ANCHOR: refines
def refines (𝒯' 𝒯 : Mesh α) : Prop :=
  ∀ T ∈ 𝒯, ∃ ℳ ⊆ 𝒯', ℳ ↪ T
-- ANCHOR_END: refines

-- instance : PartialOrder (Mesh α) where
--   le := (· ⊆ ·)
--   le_refl := fun a => Finset.Subset.refl a.1
--   le_trans := fun a b c hab hbc => Finset.Subset.trans hab hbc
--   le_antisymm := fun a b hab hba => Subtype.eq (Finset.Subset.antisymm hab hba)

lemma partitions_nonempty {M : Mesh α} {t : α} (ht : t ≠ ⊥) (hM : M ↪ t) :
  (M : Finset α) ≠ ∅ := by
  by_contra h
  have : Finset.sup (M : Finset α) id = ⊥ := by {
    rw [h]
    exact Finset.sup_empty
  }
  rw [hM] at this
  contradiction

lemma refines_trans_contruction [DecidableEq α] {X Y Z : Mesh α} (hxy: refines X Y) (hyz: refines Y Z):
  ∀ t ∈ Z, ∃ S,
    ∃ f : (s : α) → s ∈ S → Mesh α, ∃ U : Mesh α,
      (S ↪ t)
      ∧ (S ⊆ Y)
      ∧ (∀ (s : α) (a : s ∈ S), f s a ⊆ X ∧ f s a ↪ s)
      ∧ (U = (S : Finset α).attach.biUnion (fun x => (f x.1 x.2 : Finset α)))
      ∧ (U ↪ t)
      ∧ (U ⊆ X)
  := by
  intro t ht
  rcases hyz t ht with ⟨S, hS_subset, hS_part⟩
  -- S is the subset of Y refining t
  -- For each s in S, we have a refinement in X
  use S

  have : ∀ s ∈ S, ∃ M ⊆ X, M ↪ s := fun s hs => hxy s (hS_subset hs)
  choose f hf using this
  use f

  let U := (S : Finset α).attach.biUnion (fun x => (f x.1 x.2 : Finset α))

  have U_subset : U ⊆ X := by
    intro u hu
    simp [U] at hu
    rcases hu with ⟨s, hs, u_in_fs⟩
    exact (hf s hs).1 u_in_fs

  -- Because X is a mesh we get disjointness for U for free
  -- So we can construct the mesh U and use it for the existential quantifier
  use ⟨U, disjoint_subset U_subset X.2.1, nobot_subset U_subset X.2.2⟩

  refine ⟨hS_part, hS_subset, hf, by rfl, ?_, ?_⟩
  · unfold partitions
    rw [← hS_part]
    rw [Finset.sup_biUnion]
    conv =>
      lhs
      enter [2]
      ext x
      rw [(hf x.1 x.2).2]
    conv =>
      rhs
      rw [← Finset.sup_attach]
    simp only [id_eq, U]
  · exact U_subset

theorem refines_trans [DecidableEq α] (X Y Z : Mesh α) (hxy: refines X Y) (hyz: refines Y Z) :
    refines X Z := by
  intro t ht
  -- take U from the transitive construction
  rcases refines_trans_contruction hxy hyz t ht with
    ⟨S, f, U, _, _, _, _, _, _⟩
  use U

lemma mesh_mem_not_bot {M : Mesh α} {t : α} (ht : t ∈ M) :
  t ≠ ⊥ := by
  by_contra h
  have h₁ : ⊥ ∈ M := by
    rw [← h]
    exact ht
  -- bot cannot be in a mesh, a contradiction
  have h₂ := M.2.2
  contradiction

lemma disjoint_equality {x y: α} (M : Mesh α) (hx : x ∈ M) (hy : y ∈ M) (hxy : x ⊓ y = x):
  x = y := by
  have : ¬(Disjoint x y) := by
    unfold Disjoint
    simp
    use x
    refine ⟨by rfl, ?_, ?_⟩
    · exact left_eq_inf.mp (id (Eq.symm hxy))
    · exact mesh_mem_not_bot hx

  by_contra hne
  -- if they are not equal, they must be disjoint, a contradiction
  have contra := M.2.1 hx hy hne
  contradiction

lemma unique_part (M : Mesh α) (P : Mesh α) (s : α)
    (hs : s ∈ M) (hP_sub : P ⊆ M) (hP_nonempty : (P : Finset α) ≠ ∅)
    (hP_part : P ↪ s) :
    (P : Finset α) = {s} := by
  apply Finset.eq_singleton_iff_nonempty_unique_mem.mpr
  constructor
  · exact Finset.nonempty_iff_ne_empty.mpr hP_nonempty
  · intros p hp
    apply disjoint_equality M (hP_sub hp) hs
    apply inf_of_le_left
    rw [← hP_part]
    -- this is an example where exact does not work because Finset.le_sup
    -- gives id p ≤ Finset.sup P id instead of p ≤ Finset.sup P id
    apply Finset.le_sup hp

lemma biunion_is_singleton {α β : Type*} [DecidableEq β] {f : α → Finset β} {b : β}
  (A : Finset α) (h : A.biUnion f = {b}) :
      ∃ s ∈ A, f s = {b} := by
    have hb : b ∈ A.biUnion f := by simp [h]
    rcases Finset.mem_biUnion.mp hb with ⟨s, hsA, hbs⟩
    have hsub : f s ⊆ {b} := fun x hx =>
      by simpa [h] using Finset.mem_biUnion.mpr ⟨s, hsA, hx⟩
    exact ⟨s, hsA, Finset.eq_singleton_iff_unique_mem.mpr
    ⟨hbs, fun x hx => Finset.mem_singleton.1 (hsub hx)⟩⟩

lemma unique_element {s t : α} {M : Mesh α}
    (h1 : M ↪ s)
    (h2 : (M : Finset α) = {t}):
    s = t := by
  rw [← h1, h2]
  simp only [Finset.sup_singleton, id_eq]

lemma refines_antisymm_subset [DecidableEq α] (A B : Mesh α) (hAB: refines A B) (hBA: refines B A) :
    A ⊆ B := by
  intros t htA

  rcases refines_trans_contruction hAB hBA t htA with
    ⟨S, f, U, hS_part, hS_subset, hf, hU, hU_part, hU_subset⟩

  -- ANCHOR: refines_antisymm_subset_1
  have : (U : Finset α) = {t} := by
    apply unique_part A U t htA hU_subset _ hU_part
    -- remains to show that U is not empty
    apply partitions_nonempty _ hU_part
    -- t cannot be bot because meshes do not contain bot
    exact mesh_mem_not_bot htA
  -- ANCHOR_END: refines_antisymm_subset_1
  have : ∃ (s:α) (h : s ∈ S), (f s h : Finset α) = {t} := by
    rw [hU] at this
    obtain ⟨s,hs,hsf⟩ :=  biunion_is_singleton (S:Finset α).attach this
    use s.1, s.2
  rcases this with ⟨s, hs, hss⟩
  have := unique_element (hf s hs).2 hss
  subst this
  exact hS_subset hs

theorem refines_antisymm [DecidableEq α] (A B : Mesh α) (hAB: refines A B) (hBA: refines B A) :
    A = B := by
  apply Subtype.eq
  apply Finset.Subset.antisymm_iff.mpr
  exact ⟨refines_antisymm_subset A B hAB hBA, refines_antisymm_subset B A hBA hAB⟩

-- ANCHOR: Mesh_partialorder
instance : LE (Mesh α) := ⟨refines⟩
instance : LT (Mesh α) := ⟨fun f g => f ≤ g ∧ f ≠ g⟩

instance Mesh.partialOrder [DecidableEq α]: PartialOrder (Mesh α) where
  le := (· ≤ ·)
  lt := (· < ·)
  le_antisymm := refines_antisymm
  lt_iff_le_not_le a b := by
    constructor
    · intros h
      refine ⟨h.1, ?_⟩
      by_contra h₂
      have hc₁ := refines_antisymm a b h.1 h₂
      have hc₂ := h.2
      contradiction
    · intros h
      refine ⟨h.1, ?_⟩
      by_contra h₂
      rw [← h₂] at h
      rcases h with ⟨hc₁, hc₂⟩
      contradiction
  le_refl M t h := by
    use (singletonMesh t (mesh_mem_not_bot h))
    constructor
    · apply Finset.singleton_subset_set_iff.mpr h
    · unfold partitions
      simp only [Finset.sup_singleton, id_eq]
  le_trans := refines_trans
-- ANCHOR_END: Mesh_partialorder

-- ANCHOR: Mesh_Set_Example
def real_line_singleton_mesh : Mesh (Set ℝ) :=
  singletonMesh Set.univ (by
    simp only [
      Set.bot_eq_empty,
      ne_eq,
      Set.univ_eq_empty_iff,
      not_isEmpty_of_nonempty,
      not_false_eq_true
    ]
  )
-- ANCHOR_END: Mesh_Set_Example

-- ANCHOR: Mesh_Classical
open Classical
noncomputable def example_union :=
  real_line_singleton_mesh ∩ real_line_singleton_mesh
-- ANCHOR_END: Mesh_Classical
