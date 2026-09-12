import Mathlib


/-!
## Metered parking: direct histories and preference counts

Car `j : Fin m` has external label `j.val + 1`; a spot `s : Fin n`
has external label `s.val + 1`. The active interval includes the car at
distance exactly `t`: that car departs only after the arriving car parks.
The first-free conditions below concern every spot, not just outcome ranks.
No global injectivity is imposed on outcomes, so later reuse is allowed.

These definitions and lemmas allow all natural `t`, `m`, `n`, and `k`.
This phase does not assert a template bijection or a polynomial formula.
-/

namespace MeteredParking

/-- Earlier cars still present immediately before car `j` parks. -/
def Active {m : ℕ} (t : ℕ) (i j : Fin m) : Prop :=
  i < j ∧ (j : ℕ) ≤ (i : ℕ) + t

/-- The zero-based active window uses truncated natural subtraction. -/
theorem active_iff_sub_le {m t : ℕ} {i j : Fin m} :
    Active t i j ↔ i < j ∧ (j : ℕ) - t ≤ (i : ℕ) := by
  unfold Active
  omega

/-- In external labels the window is `max 1 (J - t) ≤ I < J`. -/
theorem active_iff_oneBased {m t : ℕ} {i j : Fin m} :
    Active t i j ↔
      max 1 ((j : ℕ) + 1 - t) ≤ (i : ℕ) + 1 ∧
        (i : ℕ) + 1 < (j : ℕ) + 1 := by
  change ((i : ℕ) < (j : ℕ) ∧ (j : ℕ) ≤ (i : ℕ) + t) ↔ _
  simp only [max_le_iff]
  omega

/-- A successful history of the original first-free process: every car parks
at or after its preference, its destination is free, and every skipped spot
is occupied by an earlier car that has not yet departed. -/
def IsParking {m n : ℕ} (t : ℕ) (a p : Fin m → Fin n) : Prop :=
  ∀ j : Fin m,
    a j ≤ p j ∧
      (∀ i : Fin m, Active t i j → p j ≠ p i) ∧
      ∀ q : Fin n, a j ≤ q → q < p j →
        ∃ i : Fin m, Active t i j ∧ p i = q

/-- Distinctness holds throughout the active window, including its endpoint;
there is no assertion of distinctness outside that window. -/
theorem IsParking.temporal_distinct {m n t : ℕ} {a p : Fin m → Fin n}
    (hp : IsParking t a p) {i j : Fin m}
    (hij : i < j) (hjt : (j : ℕ) ≤ (i : ℕ) + t) : p i ≠ p j := by
  intro heq
  exact (hp j).2.1 i ⟨hij, hjt⟩ heq.symm

private theorem IsParking.eq_at_of_agree_before {m n t : ℕ}
    {a p q : Fin m → Fin n} (hp : IsParking t a p) (hq : IsParking t a q)
    (j : Fin m) (ih : ∀ i : Fin m, i < j → p i = q i) : p j = q j := by
  rcases lt_trichotomy (p j) (q j) with hlt | heq | hgt
  · obtain ⟨i, hij, hi⟩ := (hq j).2.2 (p j) (hp j).1 hlt
    exact False.elim ((hp j).2.1 i hij ((ih i hij.1).trans hi).symm)
  · exact heq
  · obtain ⟨i, hij, hi⟩ := (hp j).2.2 (q j) (hq j).1 hgt
    exact False.elim ((hq j).2.1 i hij ((ih i hij.1).symm.trans hi).symm)

/-- Preferences determine the entire outcome, with no positivity or capacity
assumptions. The induction is on the natural value of the finite car label. -/
theorem IsParking.unique {m n t : ℕ} {a p q : Fin m → Fin n}
    (hp : IsParking t a p) (hq : IsParking t a q) : p = q := by
  have heq : ∀ r : ℕ, ∀ j : Fin m, (j : ℕ) = r → p j = q j := by
    intro r
    induction r using Nat.strong_induction_on with
    | h r ih =>
        intro j hj
        apply IsParking.eq_at_of_agree_before hp hq j
        intro i hij
        have hir : (i : ℕ) < r := by
          rw [← hj]
          exact hij
        exact ih (i : ℕ) hir i rfl
  funext j
  exact heq (j : ℕ) j rfl

/-- A preference is either the car's own outcome or an active earlier outcome. -/
theorem IsParking.preference_eq_or_active {m n t : ℕ} {a p : Fin m → Fin n}
    (hp : IsParking t a p) (j : Fin m) :
    a j = p j ∨ ∃ i : Fin m, Active t i j ∧ p i = a j := by
  rcases lt_or_eq_of_le (hp j).1 with hlt | heq
  · exact Or.inr ((hp j).2.2 (a j) le_rfl hlt)
  · exact Or.inl heq

/-- Every preferred spot occurs among the outcomes, even when outcomes repeat. -/
theorem IsParking.preference_mem_range {m n t : ℕ} {a p : Fin m → Fin n}
    (hp : IsParking t a p) (j : Fin m) : a j ∈ Set.range p := by
  rcases IsParking.preference_eq_or_active hp j with heq | ⟨i, _, hi⟩
  · exact ⟨j, heq.symm⟩
  · exact ⟨i, hi⟩

/-- Lucky cars are counted with their original car labels. -/
def luckyCount {m n : ℕ} (a p : Fin m → Fin n) : ℕ :=
  (Finset.univ.filter (fun j : Fin m => a j = p j)).card

/-- Success with exactly `k` lucky cars, as a predicate on preferences alone. -/
def SuccessfulPreference {m n : ℕ} (t k : ℕ) (a : Fin m → Fin n) : Prop :=
  ∃ p : Fin m → Fin n, IsParking t a p ∧ luckyCount a p = k

/-- Once an actual history is supplied, the successful-preference predicate
uses its lucky count; another history cannot change that count. -/
theorem successfulPreference_iff_luckyCount {m n t k : ℕ}
    {a p : Fin m → Fin n} (hp : IsParking t a p) :
    SuccessfulPreference t k a ↔ luckyCount a p = k := by
  constructor
  · rintro ⟨q, hq, hk⟩
    have hqp : q = p := IsParking.unique hq hp
    simpa only [hqp] using hk
  · intro hk
    exact ⟨p, hp, hk⟩

/-- The existential history in the success predicate has multiplicity one. -/
theorem successfulPreference_iff_existsUnique_history {m n t k : ℕ}
    {a : Fin m → Fin n} :
    SuccessfulPreference t k a ↔
      ∃! p : Fin m → Fin n, IsParking t a p ∧ luckyCount a p = k := by
  constructor
  · rintro ⟨p, hp, hk⟩
    refine ⟨p, ⟨hp, hk⟩, ?_⟩
    intro q hq
    exact IsParking.unique hq.1 hp
  · rintro ⟨p, hp, _⟩
    exact ⟨p, hp⟩

/-- A finite set of preference functions, not of preference/outcome pairs.
The order of parameters leaves the number of spots `n` last. -/
noncomputable def successfulPreferences (t m k n : ℕ) : Finset (Fin m → Fin n) := by
  classical
  exact Finset.univ.filter (fun a : Fin m → Fin n => SuccessfulPreference t k a)

theorem mem_successfulPreferences {t m k n : ℕ} (a : Fin m → Fin n) :
    a ∈ successfulPreferences t m k n ↔ SuccessfulPreference t k a := by
  classical
  simp only [successfulPreferences, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The original successful-preference count with exactly `k` lucky cars. -/
noncomputable def countSuccessfulPreferences (t m k n : ℕ) : ℕ :=
  (successfulPreferences t m k n).card

end MeteredParking

#check MeteredParking.IsParking.unique
#check MeteredParking.countSuccessfulPreferences
#print axioms MeteredParking.active_iff_sub_le
#print axioms MeteredParking.active_iff_oneBased
#print axioms MeteredParking.IsParking.temporal_distinct
#print axioms MeteredParking.IsParking.unique
#print axioms MeteredParking.IsParking.preference_eq_or_active
#print axioms MeteredParking.IsParking.preference_mem_range
#print axioms MeteredParking.successfulPreference_iff_luckyCount
#print axioms MeteredParking.successfulPreference_iff_existsUnique_history
#print axioms MeteredParking.mem_successfulPreferences

/-!
## Canonical outcome ranks and forced gaps

The ranks are obtained from the sorted set of distinct outcomes. They retain
all car labels and allow a rank to be reused outside the active window.
Template conditions and forced edges depend only on finite rank data, not on
the number of physical spots. A forced edge must have unit physical gap;
there is deliberately no converse condition on unforced edges.
-/

namespace MeteredParking

/-- Distinct physical outcomes, including positions reused at different times. -/
def outcomeSpots {m n : ℕ} (p : Fin m → Fin n) : Finset (Fin n) :=
  Finset.univ.image p

theorem mem_outcomeSpots {m n : ℕ} (p : Fin m → Fin n) (s : Fin n) :
    s ∈ outcomeSpots p ↔ ∃ i : Fin m, p i = s := by
  simp only [outcomeSpots, Finset.mem_image, Finset.mem_univ, true_and]

theorem outcomeSpots_card_le {m n : ℕ} (p : Fin m → Fin n) :
    (outcomeSpots p).card ≤ m := by
  calc
    (outcomeSpots p).card ≤ (Finset.univ : Finset (Fin m)).card :=
      Finset.card_image_le
    _ = m := by simp

theorem outcomeSpots_card_pos {m n : ℕ} (p : Fin m → Fin n) (hm : 0 < m) :
    0 < (outcomeSpots p).card := by
  apply Finset.card_pos.mpr
  exact ⟨p ⟨0, hm⟩, (mem_outcomeSpots p _).mpr ⟨⟨0, hm⟩, rfl⟩⟩

/-- The increasing list of distinct outcome spots. -/
noncomputable def outcomeEmbedding {m n : ℕ} (p : Fin m → Fin n) :
    Fin (outcomeSpots p).card ↪o Fin n :=
  (outcomeSpots p).orderEmbOfFin rfl

/-- The canonical outcome rank of each car. -/
noncomputable def outcomeRank {m n : ℕ} (p : Fin m → Fin n) :
    Fin m → Fin (outcomeSpots p).card :=
  fun j => ((outcomeSpots p).orderIsoOfFin rfl).symm
    ⟨p j, (mem_outcomeSpots p _).mpr ⟨j, rfl⟩⟩

/-- Preference ranks exist because every preference is an actual outcome. -/
noncomputable def preferenceRank {m n t : ℕ} {a p : Fin m → Fin n}
    (hp : IsParking t a p) : Fin m → Fin (outcomeSpots p).card :=
  fun j => ((outcomeSpots p).orderIsoOfFin rfl).symm
    ⟨a j, (mem_outcomeSpots p _).mpr (IsParking.preference_mem_range hp j)⟩

theorem outcomeEmbedding_outcomeRank {m n : ℕ} (p : Fin m → Fin n) (j : Fin m) :
    outcomeEmbedding p (outcomeRank p j) = p j := by
  unfold outcomeEmbedding outcomeRank
  rw [← Finset.coe_orderIsoOfFin_apply, OrderIso.apply_symm_apply]

theorem outcomeEmbedding_preferenceRank {m n t : ℕ} {a p : Fin m → Fin n}
    (hp : IsParking t a p) (j : Fin m) :
    outcomeEmbedding p (preferenceRank hp j) = a j := by
  unfold outcomeEmbedding preferenceRank
  rw [← Finset.coe_orderIsoOfFin_apply, OrderIso.apply_symm_apply]

/-- Every outcome rank is used by at least one car, without asserting injectivity. -/
theorem outcomeRank_surjective {m n : ℕ} (p : Fin m → Fin n) :
    Function.Surjective (outcomeRank p) := by
  intro q
  have hmem : outcomeEmbedding p q ∈ outcomeSpots p :=
    Finset.orderEmbOfFin_mem (outcomeSpots p) rfl q
  obtain ⟨j, hj⟩ := (mem_outcomeSpots p _).mp hmem
  refine ⟨j, ?_⟩
  apply (outcomeEmbedding p).injective
  exact (outcomeEmbedding_outcomeRank p j).trans hj

/-- Pulling a physical first-free history back along an increasing embedding
preserves the rankwise first-free relation. The reverse direction needs gaps. -/
theorem IsParking.of_orderEmbedding {m r n t : ℕ} {u v : Fin m → Fin r}
    (x : Fin r ↪o Fin n)
    (hp : IsParking t (fun j => x (u j)) (fun j => x (v j))) :
    IsParking t u v := by
  intro j
  refine ⟨x.le_iff_le.mp (hp j).1, ?_, ?_⟩
  · intro i hij heq
    exact (hp j).2.1 i hij (congrArg x heq)
  · intro q haq hqp
    obtain ⟨i, hij, hi⟩ := (hp j).2.2 (x q)
      (x.le_iff_le.mpr haq) (x.lt_iff_lt.mpr hqp)
    exact ⟨i, hij, x.injective hi⟩

/-- Canonical normalization satisfies precisely the phase1 relation on ranks. -/
theorem IsParking.rank_isParking {m n t : ℕ} {a p : Fin m → Fin n}
    (hp : IsParking t a p) :
    IsParking t (preferenceRank hp) (outcomeRank p) := by
  apply IsParking.of_orderEmbedding (outcomeEmbedding p)
  simpa only [outcomeEmbedding_preferenceRank, outcomeEmbedding_outcomeRank] using hp

/-- Normalization preserves each lucky car, not merely their total number. -/
theorem IsParking.rank_lucky_iff {m n t : ℕ} {a p : Fin m → Fin n}
    (hp : IsParking t a p) (j : Fin m) :
    preferenceRank hp j = outcomeRank p j ↔ a j = p j := by
  constructor
  · intro h
    have hx := congrArg (outcomeEmbedding p) h
    simpa only [outcomeEmbedding_preferenceRank, outcomeEmbedding_outcomeRank] using hx
  · intro h
    apply (outcomeEmbedding p).injective
    simpa only [outcomeEmbedding_preferenceRank, outcomeEmbedding_outcomeRank] using h

theorem IsParking.rank_luckyCount {m n t : ℕ} {a p : Fin m → Fin n}
    (hp : IsParking t a p) :
    luckyCount (preferenceRank hp) (outcomeRank p) = luckyCount a p := by
  unfold luckyCount
  apply congrArg Finset.card
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact IsParking.rank_lucky_iff hp j

/-- Template conditions (T1), including the rank bound and exact lucky count.
There is no physical-spot parameter and no extra distinctness condition. -/
def IsRankTemplate {m r : ℕ} (t k : ℕ) (u v : Fin m → Fin r) : Prop :=
  0 < r ∧ r ≤ m ∧ Function.Surjective v ∧ IsParking t u v ∧ luckyCount u v = k

/-- A bounded finite type of all templates, independent of the number of spots. -/
def RankTemplate (t m k : ℕ) :=
  Σ r : Fin (m + 1),
    {uv : (Fin m → Fin (r : ℕ)) × (Fin m → Fin (r : ℕ)) //
      IsRankTemplate t k uv.1 uv.2}

noncomputable instance rankTemplateFintype (t m k : ℕ) : Fintype (RankTemplate t m k) := by
  classical
  unfold RankTemplate
  infer_instance

theorem IsParking.rank_isRankTemplate {m n t : ℕ} {a p : Fin m → Fin n}
    (hp : IsParking t a p) (hm : 0 < m) :
    IsRankTemplate t (luckyCount a p) (preferenceRank hp) (outcomeRank p) := by
  exact ⟨outcomeSpots_card_pos p hm, outcomeSpots_card_le p,
    outcomeRank_surjective p, IsParking.rank_isParking hp, IsParking.rank_luckyCount hp⟩

/-- The actual canonical template; no template-existence premise is used. -/
noncomputable def IsParking.rankTemplate {m n t : ℕ} {a p : Fin m → Fin n}
    (hp : IsParking t a p) (hm : 0 < m) : RankTemplate t m (luckyCount a p) :=
  ⟨⟨(outcomeSpots p).card, Nat.lt_succ_of_le (outcomeSpots_card_le p)⟩,
    ⟨(preferenceRank hp, outcomeRank p), IsParking.rank_isRankTemplate hp hm⟩⟩

/-- An edge is forced exactly when some car traverses it in rank space.
The last rank cannot belong, as proved below. Physical adjacency is not used. -/
noncomputable def forcedEdges {m r : ℕ} (u v : Fin m → Fin r) : Finset (Fin r) := by
  classical
  exact Finset.univ.filter (fun q => ∃ j : Fin m, u j ≤ q ∧ q < v j)

theorem mem_forcedEdges {m r : ℕ} (u v : Fin m → Fin r) (q : Fin r) :
    q ∈ forcedEdges u v ↔ ∃ j : Fin m, u j ≤ q ∧ q < v j := by
  classical
  simp only [forcedEdges, Finset.mem_filter, Finset.mem_univ, true_and]

theorem succ_lt_of_mem_forcedEdges {m r : ℕ} {u v : Fin m → Fin r} {q : Fin r}
    (hq : q ∈ forcedEdges u v) : (q : ℕ) + 1 < r := by
  obtain ⟨j, _, hj⟩ := (mem_forcedEdges u v q).mp hq
  have hqv : (q : ℕ) < (v j : ℕ) := hj
  have hv := (v j).isLt
  omega

/-- Every traversed adjacent rank edge has unit physical gap. If a gap were
larger, the integer `x q + 1` would have to be an occupied outcome strictly
between the images of two adjacent ranks, which is impossible. -/
theorem IsParking.unit_gap_of_mem_forcedEdges {m r n t : ℕ}
    {u v : Fin m → Fin r} (x : Fin r ↪o Fin n)
    (hp : IsParking t (fun j => x (u j)) (fun j => x (v j)))
    {q q' : Fin r} (hadj : (q' : ℕ) = (q : ℕ) + 1)
    (hq : q ∈ forcedEdges u v) : (x q' : ℕ) = (x q : ℕ) + 1 := by
  obtain ⟨j, huj, hjv⟩ := (mem_forcedEdges u v q).mp hq
  have hqq' : q < q' := by
    change (q : ℕ) < (q' : ℕ)
    omega
  have hxx' : (x q : ℕ) < (x q' : ℕ) := x.lt_iff_lt.mpr hqq'
  have hq'v : q' ≤ v j := by
    change (q' : ℕ) ≤ (v j : ℕ)
    have hqv : (q : ℕ) < (v j : ℕ) := hjv
    omega
  by_contra hgap
  have hslt : (x q : ℕ) + 1 < (x q' : ℕ) := by omega
  let s : Fin n := ⟨(x q : ℕ) + 1, by
    have hbound := (x q').isLt
    omega⟩
  have hqs : x q < s := by
    change (x q : ℕ) < (x q : ℕ) + 1
    omega
  have hsq' : s < x q' := hslt
  have has : x (u j) ≤ s := le_trans (x.le_iff_le.mpr huj) (le_of_lt hqs)
  have hsp : s < x (v j) := lt_of_lt_of_le hsq' (x.le_iff_le.mpr hq'v)
  obtain ⟨i, _, his⟩ := (hp j).2.2 s has hsp
  change x (v i) = s at his
  have hqi : q < v i := x.lt_iff_lt.mp (by rw [his]; exact hqs)
  have hiq' : v i < q' := x.lt_iff_lt.mp (by rw [his]; exact hsq')
  have hqiNat : (q : ℕ) < (v i : ℕ) := hqi
  have hiq'Nat : (v i : ℕ) < (q' : ℕ) := hiq'
  omega

/-- The canonical increasing outcome list satisfies every forced unit gap.
The successor is a natural successor, never modular addition on `Fin`. -/
theorem IsParking.rank_forced_unit_gap {m n t : ℕ} {a p : Fin m → Fin n}
    (hp : IsParking t a p) (q : Fin (outcomeSpots p).card)
    (hq : q ∈ forcedEdges (preferenceRank hp) (outcomeRank p)) :
    (outcomeEmbedding p ⟨(q : ℕ) + 1, succ_lt_of_mem_forcedEdges hq⟩ : ℕ) =
      (outcomeEmbedding p q : ℕ) + 1 := by
  exact IsParking.unit_gap_of_mem_forcedEdges
    (u := preferenceRank hp) (v := outcomeRank p) (outcomeEmbedding p)
    (by simpa only [outcomeEmbedding_preferenceRank, outcomeEmbedding_outcomeRank] using hp)
    rfl hq

end MeteredParking

#check MeteredParking.IsParking.rankTemplate
#check MeteredParking.IsParking.rank_forced_unit_gap
#print axioms MeteredParking.mem_outcomeSpots
#print axioms MeteredParking.outcomeSpots_card_le
#print axioms MeteredParking.outcomeSpots_card_pos
#print axioms MeteredParking.outcomeEmbedding_outcomeRank
#print axioms MeteredParking.outcomeEmbedding_preferenceRank
#print axioms MeteredParking.outcomeRank_surjective
#print axioms MeteredParking.IsParking.of_orderEmbedding
#print axioms MeteredParking.IsParking.rank_isParking
#print axioms MeteredParking.IsParking.rank_lucky_iff
#print axioms MeteredParking.IsParking.rank_luckyCount
#print axioms MeteredParking.rankTemplateFintype
#print axioms MeteredParking.IsParking.rank_isRankTemplate
#print axioms MeteredParking.IsParking.rankTemplate
#print axioms MeteredParking.mem_forcedEdges
#print axioms MeteredParking.succ_lt_of_mem_forcedEdges
#print axioms MeteredParking.IsParking.unit_gap_of_mem_forcedEdges
#print axioms MeteredParking.IsParking.rank_forced_unit_gap

/-!
## Inflation and the preference/template correspondence

Legal embeddings require unit gaps only on the previously defined forced
edges. Inflation covers every skipped physical integer by induction on that
integer, not by restricting the first-free test to the image of the embedding.
Surjective outcome ranks recover the whole increasing embedding. Finally,
uniqueness of the original parking outcome makes inflation a bijection onto
successful preferences, rather than onto an additional history type.
-/

namespace MeteredParking

/-- Only traversed adjacent rank edges are required to have unit physical gap. -/
def HasForcedUnitGaps {m r n : ℕ} (u v : Fin m → Fin r) (x : Fin r ↪o Fin n) : Prop :=
  ∀ q q' : Fin r, (q' : ℕ) = (q : ℕ) + 1 → q ∈ forcedEdges u v →
    (x q' : ℕ) = (x q : ℕ) + 1

/-- Every physical spot between a car's inflated preference and outcome has a
rank in the traversed interval. The induction advances by one physical spot. -/
theorem HasForcedUnitGaps.spot_has_rank {m r n : ℕ} {u v : Fin m → Fin r}
    {x : Fin r ↪o Fin n} (hx : HasForcedUnitGaps u v x) (j : Fin m) (s : Fin n)
    (has : x (u j) ≤ s) (hsp : s < x (v j)) :
    ∃ q : Fin r, u j ≤ q ∧ q < v j ∧ x q = s := by
  have cover : ∀ b : ℕ, ∀ s : Fin n, (s : ℕ) = b →
      x (u j) ≤ s → s < x (v j) →
      ∃ q : Fin r, u j ≤ q ∧ q < v j ∧ x q = s := by
    intro b
    induction b using Nat.strong_induction_on with
    | h b ih =>
        intro s hs has hsp
        rcases lt_or_eq_of_le has with hlt | heq
        · have hltNat : (x (u j) : ℕ) < (s : ℕ) := hlt
          let z : Fin n := ⟨(s : ℕ) - 1, by
            have hsn := s.isLt
            omega⟩
          have hzb : (z : ℕ) < b := by
            change (s : ℕ) - 1 < b
            omega
          have haz : x (u j) ≤ z := by
            change (x (u j) : ℕ) ≤ (s : ℕ) - 1
            omega
          have hzs : z < s := by
            change (s : ℕ) - 1 < (s : ℕ)
            omega
          obtain ⟨q, huq, hqv, hxq⟩ :=
            ih (z : ℕ) hzb z rfl haz (lt_trans hzs hsp)
          have hqE : q ∈ forcedEdges u v :=
            (mem_forcedEdges u v q).mpr ⟨j, huq, hqv⟩
          let q' : Fin r := ⟨(q : ℕ) + 1, succ_lt_of_mem_forcedEdges hqE⟩
          have hgap : (x q' : ℕ) = (x q : ℕ) + 1 := hx q q' rfl hqE
          have hxq' : x q' = s := by
            apply Fin.ext
            have hxqNat : (x q : ℕ) = (s : ℕ) - 1 := congrArg Fin.val hxq
            omega
          refine ⟨q', ?_, ?_, hxq'⟩
          · change (u j : ℕ) ≤ (q : ℕ) + 1
            have huqNat : (u j : ℕ) ≤ (q : ℕ) := huq
            omega
          · exact x.lt_iff_lt.mp (by rw [hxq']; exact hsp)
        · refine ⟨u j, le_rfl, ?_, heq⟩
          exact x.lt_iff_lt.mp (by rw [heq]; exact hsp)
  exact cover (s : ℕ) s rfl has hsp

/-- A rankwise parking history inflates to the original first-free relation
when every traversed rank edge has unit gap. Outcome ranks may repeat. -/
theorem IsParking.inflate {m r n t : ℕ} {u v : Fin m → Fin r}
    (huv : IsParking t u v) (x : Fin r ↪o Fin n) (hx : HasForcedUnitGaps u v x) :
    IsParking t (fun j => x (u j)) (fun j => x (v j)) := by
  intro j
  refine ⟨x.le_iff_le.mpr (huv j).1, ?_, ?_⟩
  · intro i hij heq
    exact (huv j).2.1 i hij (x.injective heq)
  · intro s has hsp
    obtain ⟨q, huq, hqv, hxq⟩ := HasForcedUnitGaps.spot_has_rank hx j s has hsp
    obtain ⟨i, hij, hi⟩ := (huv j).2.2 q huq hqv
    exact ⟨i, hij, (congrArg x hi).trans hxq⟩

/-- Inflation preserves each lucky label by injectivity of the embedding. -/
theorem inflation_lucky_iff {m r n : ℕ} (u v : Fin m → Fin r)
    (x : Fin r ↪o Fin n) (j : Fin m) :
    x (u j) = x (v j) ↔ u j = v j :=
  ⟨fun h => x.injective h, fun h => congrArg x h⟩

theorem luckyCount_inflate {m r n : ℕ} (u v : Fin m → Fin r)
    (x : Fin r ↪o Fin n) :
    luckyCount (fun j => x (u j)) (fun j => x (v j)) = luckyCount u v := by
  unfold luckyCount
  apply congrArg Finset.card
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact inflation_lucky_iff u v x j

/-- The canonical embedding is legal for its canonical rank data. -/
theorem IsParking.rank_hasForcedUnitGaps {m n t : ℕ} {a p : Fin m → Fin n}
    (hp : IsParking t a p) :
    HasForcedUnitGaps (preferenceRank hp) (outcomeRank p) (outcomeEmbedding p) := by
  intro q q' hadj hq
  exact IsParking.unit_gap_of_mem_forcedEdges
    (u := preferenceRank hp) (v := outcomeRank p) (outcomeEmbedding p)
    (by simpa only [outcomeEmbedding_preferenceRank, outcomeEmbedding_outcomeRank] using hp)
    hadj hq

/-- Surjective outcome ranks use exactly the image of the physical embedding. -/
theorem outcomeSpots_inflate {m r n : ℕ} {v : Fin m → Fin r}
    (x : Fin r ↪o Fin n) (hv : Function.Surjective v) :
    outcomeSpots (fun j => x (v j)) = Finset.univ.image x := by
  ext s
  rw [mem_outcomeSpots]
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨v j, rfl⟩
  · rintro ⟨q, hq⟩
    obtain ⟨j, hj⟩ := hv q
    exact ⟨j, (congrArg x hj).trans hq⟩

theorem outcomeSpots_card_inflate {m r n : ℕ} {v : Fin m → Fin r}
    (x : Fin r ↪o Fin n) (hv : Function.Surjective v) :
    (outcomeSpots (fun j => x (v j))).card = r := by
  rw [outcomeSpots_inflate x hv]
  simpa using Finset.card_image_of_injective Finset.univ x.injective

/-- Sorting an inflated history recovers its increasing embedding, with only
the canonical equality of rank counts used to transport the finite index. -/
theorem outcomeEmbedding_inflate {m r n : ℕ} {v : Fin m → Fin r}
    (x : Fin r ↪o Fin n) (hv : Function.Surjective v)
    (q : Fin (outcomeSpots (fun j => x (v j))).card) :
    outcomeEmbedding (fun j => x (v j)) q =
      x (Fin.castOrderIso (outcomeSpots_card_inflate x hv) q) := by
  let h := outcomeSpots_card_inflate x hv
  have hx : x = (outcomeSpots (fun j => x (v j))).orderEmbOfFin h := by
    apply Finset.orderEmbOfFin_unique' h
    intro q
    obtain ⟨j, hj⟩ := hv q
    exact (mem_outcomeSpots _ _).mpr ⟨j, congrArg x hj⟩
  calc
    outcomeEmbedding (fun j => x (v j)) q =
        (outcomeSpots (fun j => x (v j))).orderEmbOfFin h (Fin.castOrderIso h q) := by
      unfold outcomeEmbedding
      exact Finset.orderEmbOfFin_eq_orderEmbOfFin_iff.mpr (by rfl)
    _ = x (Fin.castOrderIso h q) :=
      congrArg (fun f : Fin r ↪o Fin n => f (Fin.castOrderIso h q)) hx.symm

/-- Outcome ranks are recovered even if multiple cars use the same rank. -/
theorem outcomeRank_inflate {m r n : ℕ} {v : Fin m → Fin r}
    (x : Fin r ↪o Fin n) (hv : Function.Surjective v) (j : Fin m) :
    Fin.castOrderIso (outcomeSpots_card_inflate x hv)
      (outcomeRank (fun i => x (v i)) j) = v j := by
  apply x.injective
  exact (outcomeEmbedding_inflate x hv _).symm.trans
    (outcomeEmbedding_outcomeRank (fun i => x (v i)) j)

/-- The same rank-count transport recovers the preference ranks of any
successful inflated history, in particular the one constructed by inflation. -/
theorem preferenceRank_inflate {m r n t : ℕ} {u v : Fin m → Fin r}
    (x : Fin r ↪o Fin n) (hv : Function.Surjective v)
    (hp : IsParking t (fun j => x (u j)) (fun j => x (v j))) (j : Fin m) :
    Fin.castOrderIso (outcomeSpots_card_inflate x hv) (preferenceRank hp j) = u j := by
  apply x.injective
  exact (outcomeEmbedding_inflate x hv _).symm.trans
    (outcomeEmbedding_preferenceRank hp j)

/-- A template embedding consists only of an increasing map and the required
forced-gap proof. Unit gaps on unforced edges remain allowed. -/
def RankTemplate.LegalEmbedding {t m k : ℕ} (T : RankTemplate t m k) (n : ℕ) :=
  {x : Fin (T.1 : ℕ) ↪o Fin n // HasForcedUnitGaps T.2.1.1 T.2.1.2 x}

noncomputable instance legalEmbeddingFintype {t m k : ℕ}
    (T : RankTemplate t m k) (n : ℕ) : Fintype (T.LegalEmbedding n) := by
  classical
  exact Fintype.ofInjective
    (fun e : T.LegalEmbedding n => (e.1 : Fin (T.1 : ℕ) → Fin n))
    (by
      intro e f h
      apply Subtype.ext
      exact DFunLike.coe_injective h)

/-- Inflation maps a template and a legal embedding to an original successful
preference, with the template's prescribed lucky count. -/
def inflatePreference {t m k n : ℕ}
    (z : Σ T : RankTemplate t m k, T.LegalEmbedding n) :
    {a : Fin m → Fin n // SuccessfulPreference t k a} := by
  rcases z with ⟨⟨r, ⟨⟨u, v⟩, hT⟩⟩, ⟨x, hx⟩⟩
  exact ⟨fun j => x (u j), fun j => x (v j),
    IsParking.inflate hT.2.2.2.1 x hx,
    (luckyCount_inflate u v x).trans hT.2.2.2.2⟩

/-- No two template/embedding presentations produce the same preference.
Phase1 outcome uniqueness is essential before recovering the sorted image. -/
theorem inflatePreference_injective {t m k n : ℕ} :
    Function.Injective (@inflatePreference t m k n) := by
  rintro ⟨⟨r, ⟨⟨u, v⟩, hT⟩⟩, ⟨x, hx⟩⟩
    ⟨⟨r', ⟨⟨u', v'⟩, hT'⟩⟩, ⟨y, hy⟩⟩ h
  have ha : (fun j => x (u j)) = (fun j => y (u' j)) := congrArg Subtype.val h
  have hp := IsParking.inflate hT.2.2.2.1 x hx
  have hp' : IsParking t (fun j => x (u j)) (fun j => y (v' j)) := by
    rw [ha]
    exact IsParking.inflate hT'.2.2.2.1 y hy
  have hv : (fun j => x (v j)) = (fun j => y (v' j)) := IsParking.unique hp hp'
  have hrNat : (r : ℕ) = (r' : ℕ) := by
    calc
      (r : ℕ) = (outcomeSpots (fun j => x (v j))).card :=
        (outcomeSpots_card_inflate x hT.2.2.1).symm
      _ = (outcomeSpots (fun j => y (v' j))).card :=
        congrArg (fun p : Fin m → Fin n => (outcomeSpots p).card) hv
      _ = (r' : ℕ) := outcomeSpots_card_inflate y hT'.2.2.1
  have hr : r = r' := Fin.ext hrNat
  subst r'
  have hxy : x = y := by
    apply OrderEmbedding.range_eq_iff.mp
    ext s
    constructor
    · rintro ⟨q, hq⟩
      obtain ⟨j, hj⟩ := hT.2.2.1 q
      refine ⟨v' j, ?_⟩
      exact (congrFun hv j).symm.trans ((congrArg x hj).trans hq)
    · rintro ⟨q, hq⟩
      obtain ⟨j, hj⟩ := hT'.2.2.1 q
      refine ⟨v j, ?_⟩
      exact (congrFun hv j).trans ((congrArg y hj).trans hq)
  subst y
  have hu : u = u' := by
    funext j
    exact x.injective (congrFun ha j)
  have hv' : v = v' := by
    funext j
    exact x.injective (congrFun hv j)
  subst u'
  subst v'
  rfl

/-- Every original successful preference is obtained from its canonical ranks
and increasing outcome list. Positive car count gives a nonempty template. -/
theorem inflatePreference_surjective {t m k n : ℕ} (hm : 0 < m) :
    Function.Surjective (@inflatePreference t m k n) := by
  rintro ⟨a, p, hp, hk⟩
  subst k
  refine ⟨⟨IsParking.rankTemplate hp hm, ⟨outcomeEmbedding p, ?_⟩⟩, ?_⟩
  · exact IsParking.rank_hasForcedUnitGaps hp
  · apply Subtype.ext
    change (fun j => outcomeEmbedding p (preferenceRank hp j)) = a
    funext j
    exact outcomeEmbedding_preferenceRank hp j

/-- The original successful-preference subtype is equivalent to the disjoint
union of legal embeddings over finite rank templates. Bijectivity is proved
above, not assumed; the inverse laws are supplied by `Equiv.ofBijective`. -/
noncomputable def successfulPreferenceEquivTemplateEmbeddings
    (t m k n : ℕ) (hm : 0 < m) :
    {a : Fin m → Fin n // SuccessfulPreference t k a} ≃
      (Σ T : RankTemplate t m k, T.LegalEmbedding n) :=
  (Equiv.ofBijective (@inflatePreference t m k n)
    ⟨inflatePreference_injective, inflatePreference_surjective hm⟩).symm

end MeteredParking

#check MeteredParking.successfulPreferenceEquivTemplateEmbeddings
#print axioms MeteredParking.HasForcedUnitGaps.spot_has_rank
#print axioms MeteredParking.IsParking.inflate
#print axioms MeteredParking.inflation_lucky_iff
#print axioms MeteredParking.luckyCount_inflate
#print axioms MeteredParking.IsParking.rank_hasForcedUnitGaps
#print axioms MeteredParking.outcomeSpots_inflate
#print axioms MeteredParking.outcomeSpots_card_inflate
#print axioms MeteredParking.outcomeEmbedding_inflate
#print axioms MeteredParking.outcomeRank_inflate
#print axioms MeteredParking.preferenceRank_inflate
#print axioms MeteredParking.legalEmbeddingFintype
#print axioms MeteredParking.inflatePreference
#print axioms MeteredParking.inflatePreference_injective
#print axioms MeteredParking.inflatePreference_surjective
#print axioms MeteredParking.successfulPreferenceEquivTemplateEmbeddings

/-!
## Fixed-template gaps and finite counting

There are `r + 1` gap coordinates. In zero-based spots the left gap is
`x 0`, the gap after rank `q` is `x (q+1) - x q - 1`, and the right gap
is `n - (x last + 1)`. Only forced interior coordinates must vanish.
The correspondence with total `n-r` is used only when `r ≤ n`.
-/

namespace MeteredParking

open scoped BigOperators

/-- Cardinal transfer for the original filtered preference count, at every
capacity. Outcome uniqueness enters through the already-proved equivalence. -/
theorem countSuccessfulPreferences_eq_sum (t m k n : ℕ) (hm : 0 < m) :
    countSuccessfulPreferences t m k n =
      ∑ T : RankTemplate t m k, Fintype.card (T.LegalEmbedding n) := by
  classical
  let e : ↥(successfulPreferences t m k n) ≃
      {a : Fin m → Fin n // SuccessfulPreference t k a} :=
    { toFun := fun a => ⟨a.1, (mem_successfulPreferences a.1).mp a.2⟩
      invFun := fun a => ⟨a.1, (mem_successfulPreferences a.1).mpr a.2⟩
      left_inv := by intro a; rfl
      right_inv := by intro a; rfl }
  calc
    countSuccessfulPreferences t m k n =
        Fintype.card ↥(successfulPreferences t m k n) := by
      simp only [countSuccessfulPreferences, Fintype.card_coe]
    _ = Fintype.card (Σ T : RankTemplate t m k, T.LegalEmbedding n) :=
      Fintype.card_congr (e.trans (successfulPreferenceEquivTemplateEmbeddings t m k n hm))
    _ = _ := Fintype.card_sigma

/-- The final rank is not a forced edge, so at most `r-1` edges are forced. -/
theorem RankTemplate.forcedEdges_card_le {t m k : ℕ} (T : RankTemplate t m k) :
    (forcedEdges T.2.1.1 T.2.1.2).card ≤ (T.1 : ℕ) - 1 := by
  classical
  have hr : 0 < (T.1 : ℕ) := T.2.2.1
  let q : Fin (T.1 : ℕ) := ⟨(T.1 : ℕ) - 1, by omega⟩
  have hnot : q ∉ forcedEdges T.2.1.1 T.2.1.2 := by
    intro hq
    have h := succ_lt_of_mem_forcedEdges hq
    change (T.1 : ℕ) - 1 + 1 < (T.1 : ℕ) at h
    omega
  have hne : forcedEdges T.2.1.1 T.2.1.2 ≠ Finset.univ := by
    intro h
    exact hnot (h.symm ▸ Finset.mem_univ q)
  have hlt := Finset.card_lt_card
    (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, hne⟩)
  have hlt' : (forcedEdges T.2.1.1 T.2.1.2).card < (T.1 : ℕ) := by
    simpa only [Finset.card_univ, Fintype.card_fin] using hlt
  omega

/-- The number `r - |E|`, without introducing a graph representation. -/
noncomputable def RankTemplate.gapDimension {t m k : ℕ} (T : RankTemplate t m k) : ℕ :=
  (T.1 : ℕ) - (forcedEdges T.2.1.1 T.2.1.2).card

theorem RankTemplate.gapDimension_pos {t m k : ℕ} (T : RankTemplate t m k) :
    0 < T.gapDimension := by
  have hr : 0 < (T.1 : ℕ) := T.2.2.1
  have he := T.forcedEdges_card_le
  unfold RankTemplate.gapDimension
  omega

/-- No increasing list of `r` distinct spots fits into fewer than `r` spots. -/
theorem RankTemplate.card_legalEmbedding_of_lt {t m k n : ℕ}
    (T : RankTemplate t m k) (hn : n < (T.1 : ℕ)) :
    Fintype.card (T.LegalEmbedding n) = 0 := by
  letI : IsEmpty (T.LegalEmbedding n) :=
    ⟨fun e => (Nat.not_le_of_gt hn) (Fin.le_of_injective e.1 e.1.injective)⟩
  simp

/-- Gap coordinates not forced to zero. A forced edge `q` removes coordinate
`q.succ`, not coordinate `q`; both endpoint gaps are free. -/
noncomputable def RankTemplate.freeGapIndices {t m k : ℕ} (T : RankTemplate t m k) :
    Finset (Fin ((T.1 : ℕ) + 1)) :=
  (Finset.image Fin.succ (forcedEdges T.2.1.1 T.2.1.2))ᶜ

theorem RankTemplate.freeGapIndices_card {t m k : ℕ} (T : RankTemplate t m k) :
    T.freeGapIndices.card = T.gapDimension + 1 := by
  classical
  have hsucc : Function.Injective (Fin.succ : Fin (T.1 : ℕ) → Fin ((T.1 : ℕ) + 1)) := by
    intro i j h
    apply Fin.ext
    have hv := congrArg Fin.val h
    change (i : ℕ) + 1 = (j : ℕ) + 1 at hv
    omega
  rw [RankTemplate.freeGapIndices, Finset.card_compl,
    Finset.card_image_of_injective _ hsucc, Fintype.card_fin]
  have hr : 0 < (T.1 : ℕ) := T.2.2.1
  have he := T.forcedEdges_card_le
  unfold RankTemplate.gapDimension
  omega

theorem RankTemplate.zero_mem_freeGapIndices {t m k : ℕ} (T : RankTemplate t m k) :
    (0 : Fin ((T.1 : ℕ) + 1)) ∈ T.freeGapIndices := by
  classical
  rw [RankTemplate.freeGapIndices, Finset.mem_compl]
  intro hmem
  obtain ⟨q, _, hq⟩ := Finset.mem_image.mp hmem
  have h := congrArg Fin.val hq
  change (q : ℕ) + 1 = 0 at h
  omega

theorem RankTemplate.last_mem_freeGapIndices {t m k : ℕ} (T : RankTemplate t m k) :
    Fin.last (T.1 : ℕ) ∈ T.freeGapIndices := by
  classical
  rw [RankTemplate.freeGapIndices, Finset.mem_compl]
  intro h
  obtain ⟨q, hq, heq⟩ := Finset.mem_image.mp h
  have hbound := succ_lt_of_mem_forcedEdges hq
  have hval := congrArg Fin.val heq
  change (q : ℕ) + 1 = (T.1 : ℕ) at hval
  omega

private theorem RankTemplate.succ_not_mem_freeGapIndices {t m k : ℕ}
    (T : RankTemplate t m k) {q : Fin (T.1 : ℕ)}
    (hq : q ∈ forcedEdges T.2.1.1 T.2.1.2) : q.succ ∉ T.freeGapIndices := by
  classical
  simpa only [RankTemplate.freeGapIndices, Finset.mem_compl, not_not] using
    (Finset.mem_image.mpr ⟨q, hq, rfl⟩ :
      q.succ ∈ Finset.image Fin.succ (forcedEdges T.2.1.1 T.2.1.2))

/-- Nonnegative gaps with the required total and forced zeros; free gaps may
also vanish. No relation to embeddings is asserted below the rank capacity. -/
def RankTemplate.Gaps {t m k : ℕ} (T : RankTemplate t m k) (n : ℕ) :=
  {d : Fin ((T.1 : ℕ) + 1) → ℕ //
    (∑ i, d i) = n - (T.1 : ℕ) ∧
      ∀ q ∈ forcedEdges T.2.1.1 T.2.1.2, d q.succ = 0}

private def gapPrefix {r : ℕ} (d : Fin (r + 1) → ℕ) (b : ℕ) : ℕ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin (r + 1) => (i : ℕ) < b), d i

private theorem gapPrefix_zero {r : ℕ} (d : Fin (r + 1) → ℕ) :
    gapPrefix d 0 = 0 := by
  simp [gapPrefix]

private theorem gapPrefix_total {r : ℕ} (d : Fin (r + 1) → ℕ) :
    gapPrefix d (r + 1) = ∑ i, d i := by
  have hset : Finset.univ.filter (fun i : Fin (r + 1) => (i : ℕ) < r + 1) =
      Finset.univ := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    exact i.isLt
  unfold gapPrefix
  rw [hset]

private theorem gapPrefix_mono {r : ℕ} (d : Fin (r + 1) → ℕ)
    {a b : ℕ} (hab : a ≤ b) : gapPrefix d a ≤ gapPrefix d b := by
  unfold gapPrefix
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro i hi
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, lt_of_lt_of_le (Finset.mem_filter.mp hi).2 hab⟩
  · intro i _ _
    exact Nat.zero_le _

private theorem gapPrefix_succ {r : ℕ} (d : Fin (r + 1) → ℕ) (q : Fin (r + 1)) :
    gapPrefix d ((q : ℕ) + 1) = gapPrefix d (q : ℕ) + d q := by
  have hset : Finset.univ.filter (fun i : Fin (r + 1) => (i : ℕ) < (q : ℕ) + 1) =
      insert q (Finset.univ.filter (fun i : Fin (r + 1) => (i : ℕ) < (q : ℕ))) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro hi
      by_cases h : i = q
      · exact Or.inl h
      · right
        have hne : (i : ℕ) ≠ (q : ℕ) := fun he => h (Fin.ext he)
        omega
    · rintro (rfl | hi) <;> omega
  have hnot : q ∉ Finset.univ.filter (fun i : Fin (r + 1) => (i : ℕ) < (q : ℕ)) := by
    simp
  unfold gapPrefix
  rw [hset, Finset.sum_insert hnot, Nat.add_comm]

/-- Extract all `r+1` zero-based gaps from an increasing embedding. -/
def embeddingGaps {r n : ℕ} (hr : 0 < r) (x : Fin r ↪o Fin n) : Fin (r + 1) → ℕ :=
  fun i => if _h0 : (i : ℕ) = 0 then (x ⟨0, hr⟩ : ℕ)
    else if hi : (i : ℕ) < r then
      (x ⟨(i : ℕ), hi⟩ : ℕ) - (x ⟨(i : ℕ) - 1, by omega⟩ : ℕ) - 1
    else n - ((x ⟨r - 1, by omega⟩ : ℕ) + 1)

private theorem embeddingGaps_zero {r n : ℕ} (hr : 0 < r) (x : Fin r ↪o Fin n) :
    embeddingGaps hr x 0 = (x ⟨0, hr⟩ : ℕ) := by
  simp [embeddingGaps]

private theorem embeddingGaps_succ {r n : ℕ} (hr : 0 < r) (x : Fin r ↪o Fin n)
    (q q' : Fin r) (hadj : (q' : ℕ) = (q : ℕ) + 1) :
    embeddingGaps hr x q.succ = (x q' : ℕ) - (x q : ℕ) - 1 := by
  have h0 : (q.succ : ℕ) ≠ 0 := by change (q : ℕ) + 1 ≠ 0; omega
  have hi : (q.succ : ℕ) < r := by
    change (q : ℕ) + 1 < r
    have hq' := q'.isLt
    omega
  unfold embeddingGaps
  rw [dif_neg h0, dif_pos hi]
  have hl : (⟨(q.succ : ℕ), hi⟩ : Fin r) = q' := Fin.ext hadj.symm
  have hr' : (⟨(q.succ : ℕ) - 1, by omega⟩ : Fin r) = q := by
    apply Fin.ext
    change (q : ℕ) + 1 - 1 = (q : ℕ)
    omega
  rw [hl, hr']

private theorem embeddingGaps_last {r n : ℕ} (hr : 0 < r) (x : Fin r ↪o Fin n) :
    embeddingGaps hr x (Fin.last r) = n - ((x ⟨r - 1, by omega⟩ : ℕ) + 1) := by
  simp [embeddingGaps, Nat.ne_of_gt hr]

private theorem gapPrefix_embeddingGaps {r n : ℕ} (hr : 0 < r)
    (x : Fin r ↪o Fin n) (q : Fin r) :
    gapPrefix (embeddingGaps hr x) ((q : ℕ) + 1) + (q : ℕ) = (x q : ℕ) := by
  have h : ∀ b : ℕ, ∀ hb : b < r,
      gapPrefix (embeddingGaps hr x) (b + 1) + b = (x ⟨b, hb⟩ : ℕ) := by
    intro b
    induction b with
    | zero =>
        intro hb
        simpa only [Fin.val_zero, gapPrefix_zero, embeddingGaps_zero, zero_add, add_zero] using
          (gapPrefix_succ (embeddingGaps hr x) (0 : Fin (r + 1)))
    | succ b ih =>
        intro hb
        let q : Fin r := ⟨b, by omega⟩
        let q' : Fin r := ⟨b + 1, hb⟩
        have hprev : gapPrefix (embeddingGaps hr x) (b + 1) + b = (x q : ℕ) := ih q.isLt
        have hrec : gapPrefix (embeddingGaps hr x) (b + 1 + 1) =
            gapPrefix (embeddingGaps hr x) (b + 1) + embeddingGaps hr x q.succ :=
          gapPrefix_succ (embeddingGaps hr x) q.succ
        have hg := embeddingGaps_succ hr x q q' rfl
        have hlt : (x q : ℕ) < (x q' : ℕ) :=
          x.lt_iff_lt.mpr (by change b < b + 1; omega)
        change gapPrefix (embeddingGaps hr x) (b + 1 + 1) + (b + 1) = (x q' : ℕ)
        omega
  exact h (q : ℕ) q.isLt

/-- The sum includes both endpoint gaps and is exactly the unused capacity. -/
theorem embeddingGaps_sum {r n : ℕ} (hr : 0 < r) (x : Fin r ↪o Fin n) :
    (∑ i, embeddingGaps hr x i) = n - r := by
  have hrn := Fin.le_of_injective x x.injective
  let q : Fin r := ⟨r - 1, by omega⟩
  have hpre : gapPrefix (embeddingGaps hr x) r + (r - 1) = (x q : ℕ) := by
    have h := gapPrefix_embeddingGaps hr x q
    have hqr : (q : ℕ) + 1 = r := by change r - 1 + 1 = r; omega
    rw [hqr] at h
    exact h
  have hrec : (∑ i, embeddingGaps hr x i) =
      gapPrefix (embeddingGaps hr x) r + embeddingGaps hr x (Fin.last r) := by
    simpa only [Fin.val_last, gapPrefix_total] using
      (gapPrefix_succ (embeddingGaps hr x) (Fin.last r))
  have hlast : embeddingGaps hr x (Fin.last r) = n - ((x q : ℕ) + 1) :=
    embeddingGaps_last hr x
  have hbound := (x q).isLt
  omega

/-- Actual legal embeddings give gap vectors with precisely the forced zeros. -/
def RankTemplate.gapsOfEmbedding {t m k n : ℕ} (T : RankTemplate t m k)
    (e : T.LegalEmbedding n) : T.Gaps n := by
  refine ⟨embeddingGaps T.2.2.1 e.1, embeddingGaps_sum T.2.2.1 e.1, ?_⟩
  intro q hq
  let q' : Fin (T.1 : ℕ) := ⟨(q : ℕ) + 1, succ_lt_of_mem_forcedEdges hq⟩
  have hg := embeddingGaps_succ T.2.2.1 e.1 q q' rfl
  have hx := e.2 q q' rfl hq
  omega

/-- Reconstruct a zero-based spot as its rank plus all gaps through that rank.
The hypothesis `r ≤ n` is essential for converting total `n-r` into capacity. -/
def RankTemplate.embeddingOfGaps {t m k n : ℕ} (T : RankTemplate t m k)
    (hn : (T.1 : ℕ) ≤ n) (d : T.Gaps n) : T.LegalEmbedding n := by
  let f : Fin (T.1 : ℕ) → Fin n := fun q =>
    ⟨(q : ℕ) + gapPrefix d.1 ((q : ℕ) + 1), by
      have hpre := gapPrefix_mono d.1 (show (q : ℕ) + 1 ≤ (T.1 : ℕ) + 1 by omega)
      rw [gapPrefix_total, d.2.1] at hpre
      have hq := q.isLt
      omega⟩
  have hmono : StrictMono f := by
    intro i j hij
    have hijNat : (i : ℕ) < (j : ℕ) := hij
    have hpre := gapPrefix_mono d.1 (show (i : ℕ) + 1 ≤ (j : ℕ) + 1 by omega)
    change (i : ℕ) + gapPrefix d.1 ((i : ℕ) + 1) <
      (j : ℕ) + gapPrefix d.1 ((j : ℕ) + 1)
    omega
  let x : Fin (T.1 : ℕ) ↪o Fin n :=
    { toFun := f
      inj' := hmono.injective
      map_rel_iff' := by
        intro i j
        constructor
        · intro h
          by_contra hnot
          exact (not_le_of_gt (hmono (lt_of_not_ge hnot))) h
        · intro h
          exact hmono.monotone h }
  refine ⟨x, ?_⟩
  intro q q' hadj hq
  have hrec := gapPrefix_succ d.1 q'.castSucc
  have hcoord : q'.castSucc = q.succ := Fin.ext hadj
  have hz : d.1 q'.castSucc = 0 := by
    rw [hcoord]
    exact d.2.2 q hq
  rw [hz, add_zero] at hrec
  have hrec' : gapPrefix d.1 ((q' : ℕ) + 1) = gapPrefix d.1 (q' : ℕ) := hrec
  change (q' : ℕ) + gapPrefix d.1 ((q' : ℕ) + 1) =
    (q : ℕ) + gapPrefix d.1 ((q : ℕ) + 1) + 1
  rw [hrec', hadj]
  omega

theorem RankTemplate.embeddingOfGaps_gapsOfEmbedding {t m k n : ℕ}
    (T : RankTemplate t m k) (hn : (T.1 : ℕ) ≤ n) (e : T.LegalEmbedding n) :
    T.embeddingOfGaps hn (T.gapsOfEmbedding e) = e := by
  apply Subtype.ext
  apply DFunLike.ext
  intro q
  apply Fin.ext
  change (q : ℕ) + gapPrefix (embeddingGaps T.2.2.1 e.1) ((q : ℕ) + 1) = (e.1 q : ℕ)
  have h := gapPrefix_embeddingGaps T.2.2.1 e.1 q
  omega

theorem RankTemplate.gapsOfEmbedding_embeddingOfGaps {t m k n : ℕ}
    (T : RankTemplate t m k) (hn : (T.1 : ℕ) ≤ n) (d : T.Gaps n) :
    T.gapsOfEmbedding (T.embeddingOfGaps hn d) = d := by
  let e := T.embeddingOfGaps hn d
  let g := embeddingGaps T.2.2.1 e.1
  have hsum : (∑ i, g i) = ∑ i, d.1 i :=
    (embeddingGaps_sum T.2.2.1 e.1).trans d.2.1.symm
  have hpref : ∀ b : ℕ, b ≤ (T.1 : ℕ) + 1 → gapPrefix g b = gapPrefix d.1 b := by
    intro b hb
    by_cases hlast : b = (T.1 : ℕ) + 1
    · subst b
      simpa only [gapPrefix_total] using hsum
    · by_cases hzero : b = 0
      · subst b
        rw [gapPrefix_zero, gapPrefix_zero]
      · let q : Fin (T.1 : ℕ) := ⟨b - 1, by omega⟩
        have hq : (q : ℕ) + 1 = b := by change b - 1 + 1 = b; omega
        have h := gapPrefix_embeddingGaps T.2.2.1 e.1 q
        change gapPrefix g ((q : ℕ) + 1) + (q : ℕ) =
          (q : ℕ) + gapPrefix d.1 ((q : ℕ) + 1) at h
        rw [hq] at h
        omega
  apply Subtype.ext
  funext i
  change g i = d.1 i
  have hi := i.isLt
  have h0 := hpref (i : ℕ) (by omega)
  have h1 := hpref ((i : ℕ) + 1) (by omega)
  have hg := gapPrefix_succ g i
  have hd := gapPrefix_succ d.1 i
  omega

/-- The gap correspondence, with both inverse identities proved explicitly. -/
def RankTemplate.legalEmbeddingEquivGaps {t m k n : ℕ}
    (T : RankTemplate t m k) (hn : (T.1 : ℕ) ≤ n) : T.LegalEmbedding n ≃ T.Gaps n :=
  { toFun := T.gapsOfEmbedding
    invFun := T.embeddingOfGaps hn
    left_inv := T.embeddingOfGaps_gapsOfEmbedding hn
    right_inv := T.gapsOfEmbedding_embeddingOfGaps hn }

private theorem RankTemplate.gap_eq_zero_of_not_free {t m k n : ℕ}
    (T : RankTemplate t m k) (d : T.Gaps n) {i : Fin ((T.1 : ℕ) + 1)}
    (hi : i ∉ T.freeGapIndices) : d.1 i = 0 := by
  classical
  have hmem : i ∈ Finset.image Fin.succ (forcedEdges T.2.1.1 T.2.1.2) := by
    simpa only [RankTemplate.freeGapIndices, Finset.mem_compl, not_not] using hi
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hmem
  exact d.2.2 q hq

private theorem RankTemplate.gaps_sum_free {t m k n : ℕ}
    (T : RankTemplate t m k) (d : T.Gaps n) :
    (∑ i : ↥T.freeGapIndices, d.1 i) = ∑ i, d.1 i := by
  classical
  rw [Finset.sum_coe_sort]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro i _ hi
  exact T.gap_eq_zero_of_not_free d hi

/-- Restricting to free coordinates and extending by zero are inverse. This is
only removal of forced zeros, not an additional composition representation. -/
noncomputable def RankTemplate.gapsEquivFree {t m k : ℕ}
    (T : RankTemplate t m k) (n : ℕ) :
    T.Gaps n ≃ {g : ↥T.freeGapIndices → ℕ // (∑ i, g i) = n - (T.1 : ℕ)} := by
  classical
  let extend : (↥T.freeGapIndices → ℕ) → Fin ((T.1 : ℕ) + 1) → ℕ :=
    fun g i => if hi : i ∈ T.freeGapIndices then g ⟨i, hi⟩ else 0
  have hsum (g : ↥T.freeGapIndices → ℕ) : (∑ i, extend g i) = ∑ i, g i := by
    calc
      (∑ i, extend g i) = ∑ i ∈ T.freeGapIndices, extend g i := by
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro i _ hi
        simp only [extend, dif_neg hi]
      _ = ∑ i : ↥T.freeGapIndices, extend g i := (Finset.sum_coe_sort _ _).symm
      _ = ∑ i, g i := by
        apply Finset.sum_congr rfl
        intro i _
        simp only [extend, dif_pos i.2]
  refine
    { toFun := fun d => ⟨fun i => d.1 i, (T.gaps_sum_free d).trans d.2.1⟩
      invFun := fun g => ⟨extend g.1, (hsum g.1).trans g.2, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro q hq
    simp only [extend, dif_neg (T.succ_not_mem_freeGapIndices hq)]
  · intro d
    apply Subtype.ext
    funext i
    change extend (fun j => d.1 j) i = d.1 i
    by_cases hi : i ∈ T.freeGapIndices
    · simp only [extend, dif_pos hi]
    · simp only [extend, dif_neg hi]
      exact (T.gap_eq_zero_of_not_free d hi).symm
  · intro g
    apply Subtype.ext
    funext i
    change extend g.1 i = g.1 i
    simp only [extend, dif_pos i.2]

/-- Finiteness is transported from the existing symmetric-power model of
ordinary finite functions with a prescribed natural sum. -/
noncomputable instance gapsFintype {t m k : ℕ} (T : RankTemplate t m k) (n : ℕ) :
    Fintype (T.Gaps n) := by
  classical
  exact Fintype.ofEquiv (Sym ↥T.freeGapIndices (n - (T.1 : ℕ)))
    ((Sym.equivNatSumOfFintype ↥T.freeGapIndices (n - (T.1 : ℕ))).trans
      (T.gapsEquivFree n).symm)

/-- This counts gap assignments only. Its application to physical embeddings
below explicitly requires `r ≤ n`, even though the gap type exists for all n. -/
theorem RankTemplate.card_gaps {t m k : ℕ} (T : RankTemplate t m k) (n : ℕ) :
    Fintype.card (T.Gaps n) =
      (n - (T.1 : ℕ) + T.gapDimension).choose T.gapDimension := by
  classical
  calc
    Fintype.card (T.Gaps n) = Fintype.card (Sym ↥T.freeGapIndices (n - (T.1 : ℕ))) :=
      Fintype.card_congr ((T.gapsEquivFree n).trans
        (Sym.equivNatSumOfFintype ↥T.freeGapIndices (n - (T.1 : ℕ))).symm)
    _ = (Fintype.card ↥T.freeGapIndices + (n - (T.1 : ℕ)) - 1).choose (n - (T.1 : ℕ)) :=
      Sym.card_sym_eq_choose _
    _ = (n - (T.1 : ℕ) + T.gapDimension).choose (n - (T.1 : ℕ)) := by
      rw [Fintype.card_coe, T.freeGapIndices_card]
      congr 1
      omega
    _ = _ := Nat.choose_symm_add

/-- Exact fixed-template embedding count in the full-capacity range. The
undersized zero is the separate theorem `card_legalEmbedding_of_lt`. -/
theorem RankTemplate.card_legalEmbedding {t m k n : ℕ}
    (T : RankTemplate t m k) (hn : (T.1 : ℕ) ≤ n) :
    Fintype.card (T.LegalEmbedding n) =
      (n - (T.1 : ℕ) + T.gapDimension).choose T.gapDimension :=
  (Fintype.card_congr (T.legalEmbeddingEquivGaps hn)).trans (T.card_gaps n)

end MeteredParking

#check MeteredParking.RankTemplate.card_legalEmbedding
#print axioms MeteredParking.countSuccessfulPreferences_eq_sum
#print axioms MeteredParking.RankTemplate.forcedEdges_card_le
#print axioms MeteredParking.RankTemplate.gapDimension_pos
#print axioms MeteredParking.RankTemplate.card_legalEmbedding_of_lt
#print axioms MeteredParking.RankTemplate.freeGapIndices_card
#print axioms MeteredParking.RankTemplate.zero_mem_freeGapIndices
#print axioms MeteredParking.RankTemplate.last_mem_freeGapIndices
#print axioms MeteredParking.embeddingGaps_sum
#print axioms MeteredParking.RankTemplate.gapsOfEmbedding
#print axioms MeteredParking.RankTemplate.embeddingOfGaps
#print axioms MeteredParking.RankTemplate.embeddingOfGaps_gapsOfEmbedding
#print axioms MeteredParking.RankTemplate.gapsOfEmbedding_embeddingOfGaps
#print axioms MeteredParking.RankTemplate.legalEmbeddingEquivGaps
#print axioms MeteredParking.RankTemplate.gapsEquivFree
#print axioms MeteredParking.gapsFintype
#print axioms MeteredParking.RankTemplate.card_gaps
#print axioms MeteredParking.RankTemplate.card_legalEmbedding

/-!
## The dimension bound and an explicit top-dimensional template

Every rank is either a lucky outcome or follows a forced edge. This covering
argument bounds the gap dimension without requiring distinct lucky outcomes,
a disjoint cover, or a graph of components. The explicit template below uses
all car labels as outcome ranks, with the first `k` cars lucky and each later
car preferring its immediate predecessor's rank. No street capacity is used.
-/

namespace MeteredParking

/-- Every template has at most as many free dimensions as lucky cars. -/
theorem RankTemplate.gapDimension_le {t m k : ℕ} (T : RankTemplate t m k) :
    T.gapDimension ≤ k := by
  classical
  rcases T with ⟨r, ⟨⟨u, v⟩, hT⟩⟩
  let L : Finset (Fin m) := Finset.univ.filter (fun j => u j = v j)
  let A : Finset (Fin ((r : ℕ) + 1)) := L.image (fun j => (v j).castSucc)
  let B : Finset (Fin ((r : ℕ) + 1)) := (forcedEdges u v).image Fin.succ
  have hcover : (Finset.univ : Finset (Fin (r : ℕ))).image Fin.castSucc ⊆ A ∪ B := by
    intro z hz
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨j, hj⟩ := hT.2.2.1 q
    change v j = q at hj
    by_cases h : u j = v j
    · apply Finset.mem_union.mpr
      left
      exact Finset.mem_image.mpr
        ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩, congrArg Fin.castSucc hj⟩
    · have hlt : u j < v j := (lt_or_eq_of_le (hT.2.2.2.1 j).1).resolve_right h
      have hltq : (u j : ℕ) < (q : ℕ) := by
        rw [← hj]
        exact hlt
      let p : Fin (r : ℕ) := ⟨(q : ℕ) - 1, by
        have hqr := q.isLt
        omega⟩
      have hp : p ∈ forcedEdges u v := by
        apply (mem_forcedEdges u v p).mpr
        refine ⟨j, ?_, ?_⟩
        · change (u j : ℕ) ≤ (q : ℕ) - 1
          omega
        · change (q : ℕ) - 1 < (v j : ℕ)
          rw [hj]
          omega
      apply Finset.mem_union.mpr
      right
      refine Finset.mem_image.mpr ⟨p, hp, ?_⟩
      apply Fin.ext
      change (q : ℕ) - 1 + 1 = (q : ℕ)
      omega
  have hcast : Function.Injective
      (Fin.castSucc : Fin (r : ℕ) → Fin ((r : ℕ) + 1)) := by
    intro i j h
    have hv : (i : ℕ) = (j : ℕ) :=
      congrArg (fun z : Fin ((r : ℕ) + 1) => (z : ℕ)) h
    exact Fin.ext hv
  have hsucc : Function.Injective
      (Fin.succ : Fin (r : ℕ) → Fin ((r : ℕ) + 1)) := by
    intro i j h
    apply Fin.ext
    have hv := congrArg Fin.val h
    change (i : ℕ) + 1 = (j : ℕ) + 1 at hv
    omega
  have hcard : (r : ℕ) ≤ L.card + (forcedEdges u v).card := by
    calc
      (r : ℕ) = ((Finset.univ : Finset (Fin (r : ℕ))).image Fin.castSucc).card := by
        rw [Finset.card_image_of_injective _ hcast]
        simp
      _ ≤ (A ∪ B).card := Finset.card_le_card hcover
      _ ≤ A.card + B.card := Finset.card_union_le A B
      _ ≤ L.card + (forcedEdges u v).card := by
        dsimp only [A, B]
        rw [Finset.card_image_of_injective _ hsucc]
        exact Nat.add_le_add_right Finset.card_image_le _
  have hL : L.card = k := hT.2.2.2.2
  change (r : ℕ) - (forcedEdges u v).card ≤ k
  omega

/-- Preferences for the explicit template; outcomes will be the car labels.
The predecessor is taken in naturals, not by modular subtraction on `Fin`. -/
def topRankPreference {m : ℕ} (k : ℕ) (j : Fin m) : Fin m :=
  if (j : ℕ) < k then j else ⟨(j : ℕ) - 1, by
    have hj := j.isLt
    omega⟩

/-- With at least one prescribed lucky car, exactly the first `k` labels are lucky. -/
theorem topRankPreference_lucky_iff {m k : ℕ} (hk : 1 ≤ k) (j : Fin m) :
    topRankPreference k j = j ↔ (j : ℕ) < k := by
  unfold topRankPreference
  split_ifs with hj
  · exact ⟨fun _ => hj, fun _ => rfl⟩
  · constructor
    · intro heq
      have hv : (j : ℕ) - 1 = (j : ℕ) := congrArg Fin.val heq
      omega
    · intro h
      exact (hj h).elim

/-- Every skipped rank is the immediate predecessor and is still active for
all `t ≥ 1`. Destinations are new because the outcome of car `j` is `j`. -/
theorem topRankPreference_isParking {t m k : ℕ} (ht : 1 ≤ t) :
    IsParking t (topRankPreference (m := m) k) (fun j => j) := by
  intro j
  refine ⟨?_, ?_, ?_⟩
  · unfold topRankPreference
    split_ifs with hj
    · exact le_rfl
    · change (j : ℕ) - 1 ≤ (j : ℕ)
      omega
  · intro i hij heq
    exact (ne_of_gt hij.1) heq
  · intro q haq hqj
    change topRankPreference k j ≤ q at haq
    change q < j at hqj
    by_cases hj : (j : ℕ) < k
    · rw [topRankPreference, if_pos hj] at haq
      exact False.elim ((not_lt_of_ge haq) hqj)
    · rw [topRankPreference, if_neg hj] at haq
      have haqNat : (j : ℕ) - 1 ≤ (q : ℕ) := haq
      refine ⟨q, ⟨hqj, ?_⟩, rfl⟩
      omega

theorem topRankPreference_luckyCount {m k : ℕ} (hk : 1 ≤ k) (hkm : k ≤ m) :
    luckyCount (topRankPreference (m := m) k) (fun j => j) = k := by
  classical
  let f : Fin k → Fin m := fun i => ⟨(i : ℕ), lt_of_lt_of_le i.isLt hkm⟩
  have hf : Function.Injective f := by
    intro i j h
    have hv : (i : ℕ) = (j : ℕ) := congrArg (fun z : Fin m => (z : ℕ)) h
    exact Fin.ext hv
  have hset : Finset.univ.filter (fun j : Fin m => topRankPreference k j = j) =
      Finset.univ.image f := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      topRankPreference_lucky_iff hk, Finset.mem_image]
    constructor
    · intro hj
      exact ⟨⟨(j : ℕ), hj⟩, Fin.ext rfl⟩
    · rintro ⟨i, hi⟩
      have hv : (i : ℕ) = (j : ℕ) := congrArg Fin.val hi
      have hik := i.isLt
      omega
  change (Finset.univ.filter (fun j : Fin m => topRankPreference k j = j)).card = k
  rw [hset, Finset.card_image_of_injective _ hf]
  simp

/-- These are precisely the edges `k-1,...,m-2`, expressed without a modular
successor and with the endpoint bound explicit. -/
theorem mem_forcedEdges_topRankPreference {m k : ℕ} (q : Fin m) :
    q ∈ forcedEdges (topRankPreference k) (fun j => j) ↔
      k ≤ (q : ℕ) + 1 ∧ (q : ℕ) + 1 < m := by
  rw [mem_forcedEdges]
  constructor
  · rintro ⟨j, huq, hqj⟩
    change topRankPreference k j ≤ q at huq
    change q < j at hqj
    have hqjNat : (q : ℕ) < (j : ℕ) := hqj
    have hjm := j.isLt
    by_cases hj : (j : ℕ) < k
    · rw [topRankPreference, if_pos hj] at huq
      exact False.elim ((not_lt_of_ge huq) hqj)
    · rw [topRankPreference, if_neg hj] at huq
      have huqNat : (j : ℕ) - 1 ≤ (q : ℕ) := huq
      constructor <;> omega
  · rintro ⟨hkq, hqm⟩
    let j : Fin m := ⟨(q : ℕ) + 1, hqm⟩
    have hj : ¬(j : ℕ) < k := by
      change ¬(q : ℕ) + 1 < k
      omega
    refine ⟨j, ?_, ?_⟩
    · rw [topRankPreference, if_neg hj]
      change (q : ℕ) + 1 - 1 ≤ (q : ℕ)
      omega
    · change (q : ℕ) < (q : ℕ) + 1
      omega

theorem forcedEdges_topRankPreference_card {m k : ℕ} (hk : 1 ≤ k) :
    (forcedEdges (topRankPreference (m := m) k) (fun j => j)).card = m - k := by
  classical
  let f : Fin (m - k) → Fin m := fun i => ⟨(i : ℕ) + k - 1, by
    have hi := i.isLt
    omega⟩
  have hf : Function.Injective f := by
    intro i j h
    apply Fin.ext
    have hv : (i : ℕ) + k - 1 = (j : ℕ) + k - 1 := congrArg Fin.val h
    omega
  have hset : forcedEdges (topRankPreference (m := m) k) (fun j => j) =
      Finset.univ.image f := by
    ext q
    rw [mem_forcedEdges_topRankPreference]
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hkq, hqm⟩
      refine ⟨⟨(q : ℕ) + 1 - k, by omega⟩, ?_⟩
      apply Fin.ext
      change (q : ℕ) + 1 - k + k - 1 = (q : ℕ)
      omega
    · rintro ⟨i, hi⟩
      have hv : (i : ℕ) + k - 1 = (q : ℕ) := congrArg Fin.val hi
      have him := i.isLt
      constructor <;> omega
  rw [hset, Finset.card_image_of_injective _ hf]
  simp

/-- An actual template for every original parameter choice. Its outcome ranks
are all `m` car labels; no physical capacity or embedding premise is needed. -/
def topRankTemplate (t m k : ℕ) (ht : 1 ≤ t) (hm : 2 ≤ m)
    (hk : 1 ≤ k) (hkm : k ≤ m - 1) : RankTemplate t m k :=
  ⟨⟨m, Nat.lt_succ_self m⟩,
    ⟨(topRankPreference k, fun j => j),
      ⟨lt_of_lt_of_le (by decide : 0 < 2) hm, le_rfl, (fun q => ⟨q, rfl⟩),
        topRankPreference_isParking ht,
        topRankPreference_luckyCount hk (hkm.trans (Nat.sub_le m 1))⟩⟩⟩

theorem topRankTemplate_gapDimension (t m k : ℕ) (ht : 1 ≤ t) (hm : 2 ≤ m)
    (hk : 1 ≤ k) (hkm : k ≤ m - 1) :
    (topRankTemplate t m k ht hm hk hkm).gapDimension = k := by
  change m - (forcedEdges (topRankPreference (m := m) k) (fun j => j)).card = k
  rw [forcedEdges_topRankPreference_card hk]
  have hkm' : k ≤ m := hkm.trans (Nat.sub_le m 1)
  omega

/-- The dimension upper bound is attained throughout the original range. -/
theorem exists_rankTemplate_gapDimension_eq (t m k : ℕ)
    (ht : 1 ≤ t) (hm : 2 ≤ m) (hk : 1 ≤ k) (hkm : k ≤ m - 1) :
    ∃ T : RankTemplate t m k, T.gapDimension = k :=
  ⟨topRankTemplate t m k ht hm hk hkm, topRankTemplate_gapDimension t m k ht hm hk hkm⟩

end MeteredParking

#check MeteredParking.RankTemplate.gapDimension_le
#check MeteredParking.exists_rankTemplate_gapDimension_eq
#print axioms MeteredParking.RankTemplate.gapDimension_le
#print axioms MeteredParking.topRankPreference_lucky_iff
#print axioms MeteredParking.topRankPreference_isParking
#print axioms MeteredParking.topRankPreference_luckyCount
#print axioms MeteredParking.mem_forcedEdges_topRankPreference
#print axioms MeteredParking.forcedEdges_topRankPreference_card
#print axioms MeteredParking.topRankTemplate
#print axioms MeteredParking.topRankTemplate_gapDimension
#print axioms MeteredParking.exists_rankTemplate_gapDimension_eq

/-!
## The rational counting polynomial and Question 3

Each template contributes the falling-factorial polynomial with the shift
`X - r + c` performed in the rationals. At the undersized boundary `n+1=r`,
this shift is `c-1`, not the cast of the truncated natural expression `n-r+c`.
Only the coefficient at the target degree is used for positivity: coefficients
at smaller degrees are not asserted to be nonnegative.
-/

namespace MeteredParking

open scoped BigOperators

/-- The binomial polynomial associated to one actual rank template. -/
noncomputable def RankTemplate.countPolynomial {t m k : ℕ} (T : RankTemplate t m k) :
    Polynomial ℚ :=
  Polynomial.C ((T.gapDimension.factorial : ℚ)⁻¹) *
    (descPochhammer ℚ T.gapDimension).comp
      (Polynomial.X + Polynomial.C (-((T.1 : ℕ) : ℚ) + (T.gapDimension : ℚ)))

theorem RankTemplate.countPolynomial_natDegree {t m k : ℕ} (T : RankTemplate t m k) :
    T.countPolynomial.natDegree = T.gapDimension := by
  have hf : (T.gapDimension.factorial : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero T.gapDimension
  rw [RankTemplate.countPolynomial, Polynomial.natDegree_C_mul (inv_ne_zero hf),
    Polynomial.natDegree_comp, descPochhammer_natDegree ℚ T.gapDimension,
    Polynomial.natDegree_X_add_C, mul_one]

/-- Translation preserves monicity before multiplication by the inverse factorial. -/
theorem RankTemplate.countPolynomial_coeff_gapDimension {t m k : ℕ}
    (T : RankTemplate t m k) :
    T.countPolynomial.coeff T.gapDimension = (T.gapDimension.factorial : ℚ)⁻¹ := by
  let p : Polynomial ℚ := (descPochhammer ℚ T.gapDimension).comp
    (Polynomial.X + Polynomial.C (-((T.1 : ℕ) : ℚ) + (T.gapDimension : ℚ)))
  have hp : p.Monic := (monic_descPochhammer ℚ T.gapDimension).comp_X_add_C _
  have hd : p.natDegree = T.gapDimension := by
    dsimp only [p]
    rw [Polynomial.natDegree_comp, descPochhammer_natDegree ℚ T.gapDimension,
      Polynomial.natDegree_X_add_C, mul_one]
  have hc : p.coeff T.gapDimension = 1 := by
    simpa only [hd] using hp.coeff_natDegree
  change (Polynomial.C ((T.gapDimension.factorial : ℚ)⁻¹) * p).coeff T.gapDimension = _
  rw [Polynomial.coeff_C_mul, hc, mul_one]

/-- The coefficient at the common bound `k` is nonnegative: it is zero when
this template has smaller dimension, and an inverse factorial otherwise. -/
theorem RankTemplate.countPolynomial_coeff_nonneg {t m k : ℕ}
    (T : RankTemplate t m k) : 0 ≤ T.countPolynomial.coeff k := by
  rcases lt_or_eq_of_le T.gapDimension_le with hlt | heq
  · have hd : T.countPolynomial.natDegree < k := by
      rw [T.countPolynomial_natDegree]
      exact hlt
    exact le_of_eq (Polynomial.coeff_eq_zero_of_natDegree_lt hd).symm
  · have hc : T.countPolynomial.coeff k = (T.gapDimension.factorial : ℚ)⁻¹ :=
      (congrArg (fun d : ℕ => T.countPolynomial.coeff d) heq.symm).trans
        T.countPolynomial_coeff_gapDimension
    rw [hc]
    exact inv_nonneg.mpr (Nat.cast_nonneg _)

/-- Template evaluation equals the actual embedding cardinality on every
original capacity, including the only possible undersized case `n+1=r`. -/
theorem RankTemplate.countPolynomial_eval {t m k n : ℕ}
    (T : RankTemplate t m k) (hn : m - 1 ≤ n) :
    T.countPolynomial.eval (n : ℚ) = (Fintype.card (T.LegalEmbedding n) : ℚ) := by
  simp only [RankTemplate.countPolynomial, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X]
  by_cases hrn : (T.1 : ℕ) ≤ n
  · have hshift : (n : ℚ) + (-((T.1 : ℕ) : ℚ) + (T.gapDimension : ℚ)) =
        ((n - (T.1 : ℕ) + T.gapDimension : ℕ) : ℚ) := by
      rw [Nat.cast_add, Nat.cast_sub hrn]
      ring
    rw [hshift, T.card_legalEmbedding hrn,
      Nat.cast_choose_eq_descPochhammer_div ℚ (n - (T.1 : ℕ) + T.gapDimension)
        T.gapDimension]
    rw [div_eq_mul_inv, mul_comm]
  · have hnr : n < (T.1 : ℕ) := lt_of_not_ge hrn
    have hrm : (T.1 : ℕ) ≤ m := T.2.2.2.1
    have hnrEq : n + 1 = (T.1 : ℕ) := by omega
    have hnrRat : (n : ℚ) + 1 = ((T.1 : ℕ) : ℚ) := by
      exact_mod_cast hnrEq
    have hc : 1 ≤ T.gapDimension := T.gapDimension_pos
    have hshift : (n : ℚ) + (-((T.1 : ℕ) : ℚ) + (T.gapDimension : ℚ)) =
        ((T.gapDimension - 1 : ℕ) : ℚ) := by
      rw [Nat.cast_sub hc, Nat.cast_one]
      linarith
    have hroot : (descPochhammer ℚ T.gapDimension).eval
        ((T.gapDimension - 1 : ℕ) : ℚ) = 0 :=
      descPochhammer_eval_coe_nat_of_lt (by omega : T.gapDimension - 1 < T.gapDimension)
    rw [hshift, hroot, mul_zero, T.card_legalEmbedding_of_lt hnr, Nat.cast_zero]

/-- A finite sum over templates independent of the number of physical spots. -/
noncomputable def question3Polynomial (t m k : ℕ) : Polynomial ℚ :=
  ∑ T : RankTemplate t m k, T.countPolynomial

/-- Evaluation counts the original successful preferences, not presentations
or histories, using the previously established finite-sum identity. -/
theorem question3Polynomial_eval (t m k n : ℕ) (hm : 0 < m) (hn : m - 1 ≤ n) :
    (question3Polynomial t m k).eval (n : ℚ) =
      (countSuccessfulPreferences t m k n : ℚ) := by
  classical
  rw [question3Polynomial, Polynomial.eval_finsetSum,
    countSuccessfulPreferences_eq_sum t m k n hm, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro T _
  exact T.countPolynomial_eval hn

theorem question3Polynomial_natDegree_le (t m k : ℕ) :
    (question3Polynomial t m k).natDegree ≤ k := by
  classical
  unfold question3Polynomial
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro T _
  rw [T.countPolynomial_natDegree]
  exact T.gapDimension_le

/-- Nonnegative degree-`k` coefficients and an actual dimension-`k` template
ensure a positive coefficient of the sum, even when other summands give zero. -/
theorem question3Polynomial_coeff_pos (t m k : ℕ)
    (ht : 1 ≤ t) (hm : 2 ≤ m) (hk : 1 ≤ k) (hkm : k ≤ m - 1) :
    0 < (question3Polynomial t m k).coeff k := by
  classical
  rw [question3Polynomial, Polynomial.finsetSum_coeff]
  apply Finset.sum_pos'
  · intro T _
    exact T.countPolynomial_coeff_nonneg
  · obtain ⟨T, hT⟩ := exists_rankTemplate_gapDimension_eq t m k ht hm hk hkm
    refine ⟨T, Finset.mem_univ _, ?_⟩
    have hc : T.countPolynomial.coeff k = (T.gapDimension.factorial : ℚ)⁻¹ :=
      (congrArg (fun d : ℕ => T.countPolynomial.coeff d) hT.symm).trans
        T.countPolynomial_coeff_gapDimension
    rw [hc]
    apply inv_pos.mpr
    exact_mod_cast Nat.factorial_pos T.gapDimension

theorem question3Polynomial_natDegree (t m k : ℕ)
    (ht : 1 ≤ t) (hm : 2 ≤ m) (hk : 1 ≤ k) (hkm : k ≤ m - 1) :
    (question3Polynomial t m k).natDegree = k :=
  Polynomial.natDegree_eq_of_le_of_coeff_ne_zero (question3Polynomial_natDegree_le t m k)
    (ne_of_gt (question3Polynomial_coeff_pos t m k ht hm hk hkm))

/-- Question 3 for the original successful-preference count, with exact degree
and equality at every `n ≥ m-1`. All template and counting results used here
are proved above; none is an extra premise of this theorem. -/
theorem question3 (t m k : ℕ) (ht : 1 ≤ t) (hm : 2 ≤ m)
    (hk : 1 ≤ k) (hkm : k ≤ m - 1) :
    ∃ Q : Polynomial ℚ, Q.natDegree = k ∧
      ∀ n : ℕ, m - 1 ≤ n → Q.eval (n : ℚ) = (countSuccessfulPreferences t m k n : ℚ) := by
  refine ⟨question3Polynomial t m k, question3Polynomial_natDegree t m k ht hm hk hkm, ?_⟩
  intro n hn
  exact question3Polynomial_eval t m k n (by omega) hn

end MeteredParking

#check (MeteredParking.question3 :
  ∀ (t m k : ℕ), 1 ≤ t → 2 ≤ m → 1 ≤ k → k ≤ m - 1 →
    ∃ Q : Polynomial ℚ, Q.natDegree = k ∧
      ∀ n : ℕ, m - 1 ≤ n →
        Q.eval (n : ℚ) = (MeteredParking.countSuccessfulPreferences t m k n : ℚ))
#print axioms MeteredParking.RankTemplate.countPolynomial_natDegree
#print axioms MeteredParking.RankTemplate.countPolynomial_coeff_gapDimension
#print axioms MeteredParking.RankTemplate.countPolynomial_coeff_nonneg
#print axioms MeteredParking.RankTemplate.countPolynomial_eval
#print axioms MeteredParking.question3Polynomial_eval
#print axioms MeteredParking.question3Polynomial_natDegree_le
#print axioms MeteredParking.question3Polynomial_coeff_pos
#print axioms MeteredParking.question3Polynomial_natDegree
#print axioms MeteredParking.question3

/-!
## Relabeling ranks along forced intervals

A rank permutation need not preserve the global order. Preserving the oriented
unit step on every forced edge nevertheless makes it a translation on each
car's traversed interval. This suffices for the original first-free relation
and transports the forced-edge set exactly. No block decomposition or counting
claim is used in this local semantic gate.
-/

namespace MeteredParking

private theorem forcedEdges_relabel_translate {m r : ℕ} {u v : Fin m → Fin r}
    (e : Equiv.Perm (Fin r))
    (h_adj : ∀ q q' : Fin r, (q' : ℕ) = (q : ℕ) + 1 →
      q ∈ forcedEdges u v → (e q' : ℕ) = (e q : ℕ) + 1)
    (j : Fin m) (q : Fin r) (huq : u j ≤ q) (hqv : q ≤ v j) :
    (e q : ℕ) + (u j : ℕ) = (e (u j) : ℕ) + (q : ℕ) := by
  have translate : ∀ b : ℕ, ∀ q : Fin r, (q : ℕ) = b →
      u j ≤ q → q ≤ v j →
      (e q : ℕ) + (u j : ℕ) = (e (u j) : ℕ) + (q : ℕ) := by
    intro b
    induction b using Nat.strong_induction_on with
    | h b ih =>
        intro q hqb huq hqv
        by_cases hqu : q = u j
        · subst q
          rfl
        · have huqFin : u j < q := lt_of_le_of_ne huq (Ne.symm hqu)
          have huqNat : (u j : ℕ) < (q : ℕ) := huqFin
          let q₀ : Fin r := ⟨(q : ℕ) - 1, by
            have hqr := q.isLt
            omega⟩
          have hq₀q : (q₀ : ℕ) + 1 = (q : ℕ) := by
            change (q : ℕ) - 1 + 1 = (q : ℕ)
            omega
          have huq₀ : u j ≤ q₀ := by
            change (u j : ℕ) ≤ (q : ℕ) - 1
            omega
          have hq₀v : q₀ < v j := by
            have hqvNat : (q : ℕ) ≤ (v j : ℕ) := hqv
            change (q : ℕ) - 1 < (v j : ℕ)
            omega
          have hforced : q₀ ∈ forcedEdges u v :=
            (mem_forcedEdges u v q₀).mpr ⟨j, huq₀, hq₀v⟩
          have hprev := ih (q₀ : ℕ) (by omega) q₀ rfl huq₀ (le_of_lt hq₀v)
          have hstep := h_adj q₀ q hq₀q.symm hforced
          omega
  exact translate (q : ℕ) q rfl huq hqv

/-- Every rank in a relabeled traversal comes from its original traversal.
The inverse rank is constructed from the local translation, not from any
assumed global monotonicity or interval-coverage premise. -/
theorem relabel_interval_coverage {m r : ℕ} {u v : Fin m → Fin r}
    (e : Equiv.Perm (Fin r))
    (h_adj : ∀ q q' : Fin r, (q' : ℕ) = (q : ℕ) + 1 →
      q ∈ forcedEdges u v → (e q' : ℕ) = (e q : ℕ) + 1)
    (j : Fin m) (huv : u j ≤ v j) (s : Fin r)
    (has : e (u j) ≤ s) (hsv : s < e (v j)) :
    ∃ q : Fin r, u j ≤ q ∧ q < v j ∧ e q = s := by
  have hvtrans := forcedEdges_relabel_translate e h_adj j (v j) huv le_rfl
  have hasNat : (e (u j) : ℕ) ≤ (s : ℕ) := has
  have hsvNat : (s : ℕ) < (e (v j) : ℕ) := hsv
  have hqNat : (u j : ℕ) + ((s : ℕ) - (e (u j) : ℕ)) < (v j : ℕ) := by
    omega
  let q : Fin r :=
    ⟨(u j : ℕ) + ((s : ℕ) - (e (u j) : ℕ)), lt_trans hqNat (v j).isLt⟩
  have huq : u j ≤ q := by
    change (u j : ℕ) ≤ (u j : ℕ) + ((s : ℕ) - (e (u j) : ℕ))
    omega
  have hqv : q < v j := hqNat
  have hqtrans := forcedEdges_relabel_translate e h_adj j q huq (le_of_lt hqv)
  have hqval : (q : ℕ) = (u j : ℕ) + ((s : ℕ) - (e (u j) : ℕ)) := rfl
  refine ⟨q, huq, hqv, ?_⟩
  apply Fin.ext
  omega

/-- Forced oriented adjacency suffices to preserve all three first-free
conditions. Active car labels and the permission to reuse outcomes are unchanged. -/
theorem IsParking.relabel_of_forced_adj {t m r : ℕ} {u v : Fin m → Fin r}
    (hp : IsParking t u v) (e : Equiv.Perm (Fin r))
    (h_adj : ∀ q q' : Fin r, (q' : ℕ) = (q : ℕ) + 1 →
      q ∈ forcedEdges u v → (e q' : ℕ) = (e q : ℕ) + 1) :
    IsParking t (fun j => e (u j)) (fun j => e (v j)) := by
  intro j
  have hvtrans := forcedEdges_relabel_translate e h_adj j (v j) (hp j).1 le_rfl
  have huvNat : (u j : ℕ) ≤ (v j : ℕ) := (hp j).1
  refine ⟨?_, ?_, ?_⟩
  · change (e (u j) : ℕ) ≤ (e (v j) : ℕ)
    omega
  · intro i hij heq
    exact (hp j).2.1 i hij (e.injective heq)
  · intro s has hsv
    obtain ⟨q, huq, hqv, heq⟩ := relabel_interval_coverage e h_adj j (hp j).1 s has hsv
    obtain ⟨i, hij, hiq⟩ := (hp j).2.2 q huq hqv
    exact ⟨i, hij, (congrArg e hiq).trans heq⟩

/-- The relabeled forced edges are precisely the images of the old ones;
there are no additional forced edges between reordered intervals. -/
theorem forcedEdges_relabel_of_forced_adj {m r : ℕ} {u v : Fin m → Fin r}
    (e : Equiv.Perm (Fin r))
    (h_adj : ∀ q q' : Fin r, (q' : ℕ) = (q : ℕ) + 1 →
      q ∈ forcedEdges u v → (e q' : ℕ) = (e q : ℕ) + 1)
    (huv : ∀ j : Fin m, u j ≤ v j) :
    forcedEdges (fun j => e (u j)) (fun j => e (v j)) = (forcedEdges u v).image e := by
  classical
  ext s
  constructor
  · intro hs
    obtain ⟨j, has, hsv⟩ := (mem_forcedEdges _ _ s).mp hs
    obtain ⟨q, huq, hqv, heq⟩ := relabel_interval_coverage e h_adj j (huv j) s has hsv
    exact Finset.mem_image.mpr ⟨q, (mem_forcedEdges u v q).mpr ⟨j, huq, hqv⟩, heq⟩
  · intro hs
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨j, huq, hqv⟩ := (mem_forcedEdges u v q).mp hq
    have hqtrans := forcedEdges_relabel_translate e h_adj j q huq (le_of_lt hqv)
    have hvtrans := forcedEdges_relabel_translate e h_adj j (v j) (huv j) le_rfl
    have huqNat : (u j : ℕ) ≤ (q : ℕ) := huq
    have hqvNat : (q : ℕ) < (v j : ℕ) := hqv
    apply (mem_forcedEdges _ _ _).mpr
    refine ⟨j, ?_, ?_⟩
    · change (e (u j) : ℕ) ≤ (e q : ℕ)
      omega
    · change (e q : ℕ) < (e (v j) : ℕ)
      omega

/-- A rank permutation preserving the oriented unit step on every forced edge
preserves the full rank template, including surjectivity and exact lucky count,
and transports its forced-edge set by image. This is a conditional relabeling
lemma, not the integer-coefficient counting corollary. -/
theorem IsRankTemplate.relabel_of_forced_adj {t m k r : ℕ} {u v : Fin m → Fin r}
    (hT : IsRankTemplate t k u v) (e : Equiv.Perm (Fin r))
    (h_adj : ∀ q q' : Fin r, (q' : ℕ) = (q : ℕ) + 1 →
      q ∈ forcedEdges u v → (e q' : ℕ) = (e q : ℕ) + 1) :
    IsRankTemplate t k (fun j => e (u j)) (fun j => e (v j)) ∧
      forcedEdges (fun j => e (u j)) (fun j => e (v j)) = (forcedEdges u v).image e := by
  classical
  have hp : IsParking t u v := hT.2.2.2.1
  have hlucky : luckyCount (fun j => e (u j)) (fun j => e (v j)) = luckyCount u v := by
    unfold luckyCount
    apply congrArg Finset.card
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => e.injective h, fun h => congrArg e h⟩
  refine ⟨⟨hT.1, hT.2.1, ?_, IsParking.relabel_of_forced_adj hp e h_adj,
    hlucky.trans hT.2.2.2.2⟩,
    forcedEdges_relabel_of_forced_adj e h_adj (fun j => (hp j).1)⟩
  intro q
  obtain ⟨j, hj⟩ := hT.2.2.1 (e.symm q)
  exact ⟨j, (congrArg e hj).trans (e.apply_symm_apply q)⟩

end MeteredParking

#print axioms MeteredParking.relabel_interval_coverage
#print axioms MeteredParking.IsParking.relabel_of_forced_adj
#print axioms MeteredParking.forcedEdges_relabel_of_forced_adj
#print axioms MeteredParking.IsRankTemplate.relabel_of_forced_adj

/-!
## Derived block compositions and repacking

The free gap coordinates already specify all block boundaries, including both
endpoints. A permutation below sends each new block position to its old block
index. Repacking changes the prefix sums, retains each local coordinate, and
uses the previous semantic gate rather than reproving parking correctness.
-/

namespace MeteredParking

open scoped BigOperators

/-- The existing free gaps, viewed as boundaries; no extra boundary data is stored. -/
noncomputable def RankTemplate.blockCompositionAsSet {t m k : ℕ}
    (T : RankTemplate t m k) : CompositionAsSet (T.1 : ℕ) where
  boundaries := T.freeGapIndices
  zero_mem := T.zero_mem_freeGapIndices
  getLast_mem := T.last_mem_freeGapIndices

/-- The composition derived from the template's actual forced edges. -/
noncomputable def RankTemplate.blockComposition {t m k : ℕ}
    (T : RankTemplate t m k) : Composition (T.1 : ℕ) :=
  T.blockCompositionAsSet.toComposition

@[simp] theorem RankTemplate.blockComposition_boundaries {t m k : ℕ}
    (T : RankTemplate t m k) : T.blockComposition.boundaries = T.freeGapIndices :=
  CompositionAsSet.toComposition_boundaries T.blockCompositionAsSet

@[simp] theorem RankTemplate.blockComposition_length {t m k : ℕ}
    (T : RankTemplate t m k) : T.blockComposition.length = T.gapDimension := by
  have h := T.blockComposition.card_boundaries_eq_succ_length
  rw [T.blockComposition_boundaries, T.freeGapIndices_card] at h
  omega

theorem RankTemplate.mem_forcedEdges_iff_not_blockBoundary {t m k : ℕ}
    (T : RankTemplate t m k) (q : Fin (T.1 : ℕ)) :
    q ∈ forcedEdges T.2.1.1 T.2.1.2 ↔ q.succ ∉ T.blockComposition.boundaries := by
  classical
  rw [T.blockComposition_boundaries, RankTemplate.freeGapIndices,
    Finset.mem_compl, not_not]
  constructor
  · intro hq
    exact Finset.mem_image.mpr ⟨q, hq, rfl⟩
  · intro hq
    obtain ⟨p, hp, hpq⟩ := Finset.mem_image.mp hq
    have heq : p = q := by
      apply Fin.ext
      have h := congrArg Fin.val hpq
      change (p : ℕ) + 1 = (q : ℕ) + 1 at h
      omega
    simpa only [heq] using hp

private theorem composition_succ_not_boundary_iff_end {r : ℕ}
    (C : Composition r) (q : Fin r) :
    q.succ ∉ C.boundaries ↔ (q : ℕ) + 1 < C.sizeUpTo ((C.index q : ℕ) + 1) := by
  have hend : (q : ℕ) < C.sizeUpTo ((C.index q : ℕ) + 1) :=
    C.lt_sizeUpTo_index_succ q
  constructor
  · intro hnot
    by_contra hlt
    apply hnot
    change q.succ ∈ Finset.univ.map C.boundary.toEmbedding
    refine Finset.mem_map.mpr ⟨(C.index q).succ, Finset.mem_univ _, ?_⟩
    apply Fin.ext
    change C.sizeUpTo ((C.index q : ℕ) + 1) = (q : ℕ) + 1
    omega
  · intro hlt hmem
    change q.succ ∈ Finset.univ.map C.boundary.toEmbedding at hmem
    obtain ⟨i, _, hi⟩ := Finset.mem_map.mp hmem
    have hval : C.sizeUpTo (i : ℕ) = (q : ℕ) + 1 := congrArg Fin.val hi
    by_cases hle : (i : ℕ) ≤ (C.index q : ℕ)
    · have hmono := C.monotone_sizeUpTo hle
      have hstart := C.sizeUpTo_index_le q
      omega
    · have hmono := C.monotone_sizeUpTo
        (show (C.index q : ℕ) + 1 ≤ (i : ℕ) by omega)
      omega

private theorem composition_succ_not_boundary_iff_local {r : ℕ}
    (C : Composition r) (q : Fin r) :
    q.succ ∉ C.boundaries ↔
      (C.invEmbedding q : ℕ) + 1 < C.blocksFun (C.index q) := by
  rw [composition_succ_not_boundary_iff_end]
  have hstart := C.sizeUpTo_index_le q
  have hsize := C.sizeUpTo_succ' (C.index q)
  have hlocal := C.coe_invEmbedding q
  omega

/-- Natural-successor ranks share a block precisely when their separating
coordinate is not a boundary. The successor is required to remain in `Fin r`. -/
theorem composition_adj_same_block_iff {r : ℕ} (C : Composition r)
    (q q' : Fin r) (hadj : (q' : ℕ) = (q : ℕ) + 1) :
    C.index q' = C.index q ↔ q.succ ∉ C.boundaries := by
  rw [composition_succ_not_boundary_iff_end]
  constructor
  · intro hi
    have h : (q' : ℕ) < C.sizeUpTo ((C.index q' : ℕ) + 1) :=
      C.lt_sizeUpTo_index_succ q'
    rw [hi, hadj] at h
    exact h
  · intro h
    have hstart : C.sizeUpTo (C.index q) ≤ (q' : ℕ) := by
      have hq := C.sizeUpTo_index_le q
      omega
    have hend : (q' : ℕ) < C.sizeUpTo ((C.index q : ℕ) + 1) := by omega
    have hmem : q' ∈ Set.range (C.embedding (C.index q)) :=
      C.mem_range_embedding_iff.mpr ⟨hstart, hend⟩
    exact (C.mem_range_embedding_iff'.mp hmem).symm

section Repacking

variable {r : ℕ} (C : Composition r) (σ : Equiv.Perm (Fin C.length))

/-- New position `j` receives old block `σ j`, including its full length. -/
def reorderedComposition : Composition r where
  blocks := List.ofFn (fun j => C.blocksFun (σ j))
  blocks_pos := by
    simp only [List.forall_mem_ofFn_iff]
    intro j
    exact C.one_le_blocksFun (σ j)
  blocks_sum := by
    rw [List.sum_ofFn]
    calc
      (∑ i, C.blocksFun (σ i)) = ∑ i, C.blocksFun i :=
        Fintype.sum_equiv σ (fun i => C.blocksFun (σ i)) C.blocksFun (fun _ => rfl)
      _ = r := C.sum_blocksFun

@[simp] theorem reorderedComposition_length : (reorderedComposition C σ).length = C.length := by
  simp only [reorderedComposition, Composition.length, List.length_ofFn]

@[simp] theorem reorderedComposition_blocksFun
    (j : Fin (reorderedComposition C σ).length) :
    (reorderedComposition C σ).blocksFun j =
      C.blocksFun (σ (Fin.cast (reorderedComposition_length C σ) j)) := by
  let j₀ : Fin C.length := ⟨(j : ℕ), by
    exact lt_of_lt_of_eq j.isLt (reorderedComposition_length C σ)⟩
  have hj₀ : j₀ = Fin.cast (reorderedComposition_length C σ) j := Fin.ext rfl
  calc
    (reorderedComposition C σ).blocksFun j = C.blocksFun (σ j₀) := by
      simp [Composition.blocksFun, reorderedComposition, j₀]
    _ = C.blocksFun (σ (Fin.cast (reorderedComposition_length C σ) j)) :=
      congrArg (fun i : Fin C.length => C.blocksFun (σ i)) hj₀

/-- The old-to-new block index map. Keeping `σ` retains block identity even
when several block lengths coincide. -/
def repackBlockIndex : Fin C.length ≃ Fin (reorderedComposition C σ).length :=
  σ.symm.trans (finCongr (reorderedComposition_length C σ).symm)

@[simp] theorem repackBlockIndex_val (i : Fin C.length) :
    (repackBlockIndex C σ i : ℕ) = (σ.symm i : ℕ) := rfl

@[simp] theorem reorderedComposition_blocksFun_repackBlockIndex (i : Fin C.length) :
    (reorderedComposition C σ).blocksFun (repackBlockIndex C σ i) = C.blocksFun i := by
  rw [reorderedComposition_blocksFun]
  change C.blocksFun (σ (σ.symm i)) = C.blocksFun i
  rw [σ.apply_symm_apply]

/-- Unpack an old rank, move its block index, cast its unchanged local
coordinate, and repack using the new prefix sums. This is not an order embedding. -/
def repackRanks : Equiv.Perm (Fin r) :=
  C.blocksFinEquiv.symm.trans
    ((Equiv.sigmaCongr (repackBlockIndex C σ)
      (fun i => finCongr (reorderedComposition_blocksFun_repackBlockIndex C σ i).symm)).trans
        (reorderedComposition C σ).blocksFinEquiv)

theorem repackRanks_index (q : Fin r) :
    (reorderedComposition C σ).index (repackRanks C σ q) =
      repackBlockIndex C σ (C.index q) := by
  exact (reorderedComposition C σ).index_embedding _ _

theorem repackRanks_local (q : Fin r) :
    ((reorderedComposition C σ).invEmbedding (repackRanks C σ q) : ℕ) =
      (C.invEmbedding q : ℕ) := by
  exact (reorderedComposition C σ).invEmbedding_comp _ _

theorem repackRanks_val (q : Fin r) :
    (repackRanks C σ q : ℕ) =
      (reorderedComposition C σ).sizeUpTo (repackBlockIndex C σ (C.index q)) +
        (C.invEmbedding q : ℕ) := rfl

/-- An internal edge remains internal, and every internal edge at the new
rank comes from an old internal edge. No cross-block adjacency is imposed. -/
theorem repackRanks_succ_not_boundary (q : Fin r) :
    (repackRanks C σ q).succ ∉ (reorderedComposition C σ).boundaries ↔
      q.succ ∉ C.boundaries := by
  simp only [composition_succ_not_boundary_iff_local, repackRanks_local,
    repackRanks_index, reorderedComposition_blocksFun_repackBlockIndex]

theorem repackRanks_adj (q q' : Fin r) (hadj : (q' : ℕ) = (q : ℕ) + 1)
    (hnot : q.succ ∉ C.boundaries) :
    (repackRanks C σ q' : ℕ) = (repackRanks C σ q : ℕ) + 1 := by
  have hi := (composition_adj_same_block_iff C q q' hadj).mpr hnot
  have hlocal : (C.invEmbedding q' : ℕ) = (C.invEmbedding q : ℕ) + 1 := by
    simp only [Composition.coe_invEmbedding, hi]
    have hstart := C.sizeUpTo_index_le q
    omega
  simp only [repackRanks_val, hi, hlocal, Nat.add_assoc]

end Repacking

/-- The derived composition makes repacking satisfy the previous semantic gate. -/
theorem RankTemplate.repackRanks_forced_adj {t m k : ℕ} (T : RankTemplate t m k)
    (σ : Equiv.Perm (Fin T.blockComposition.length))
    (q q' : Fin (T.1 : ℕ)) (hadj : (q' : ℕ) = (q : ℕ) + 1)
    (hq : q ∈ forcedEdges T.2.1.1 T.2.1.2) :
    (repackRanks T.blockComposition σ q' : ℕ) =
      (repackRanks T.blockComposition σ q : ℕ) + 1 :=
  repackRanks_adj T.blockComposition σ q q' hadj
    ((T.mem_forcedEdges_iff_not_blockBoundary q).mp hq)

/-- Reorder whole blocks while retaining every car label and its local ranks.
Template validity is supplied by the already-proved relabeling theorem. -/
noncomputable def RankTemplate.reorderBlocks {t m k : ℕ} (T : RankTemplate t m k)
    (σ : Equiv.Perm (Fin T.blockComposition.length)) : RankTemplate t m k :=
  ⟨T.1, ⟨(fun j => repackRanks T.blockComposition σ (T.2.1.1 j),
            fun j => repackRanks T.blockComposition σ (T.2.1.2 j)),
    (IsRankTemplate.relabel_of_forced_adj T.2.2 (repackRanks T.blockComposition σ)
      (T.repackRanks_forced_adj σ)).1⟩⟩

@[simp] theorem RankTemplate.reorderBlocks_rank {t m k : ℕ} (T : RankTemplate t m k)
    (σ : Equiv.Perm (Fin T.blockComposition.length)) : (T.reorderBlocks σ).1 = T.1 := rfl

theorem RankTemplate.reorderBlocks_forcedEdges {t m k : ℕ} (T : RankTemplate t m k)
    (σ : Equiv.Perm (Fin T.blockComposition.length)) :
    forcedEdges (T.reorderBlocks σ).2.1.1 (T.reorderBlocks σ).2.1.2 =
      (forcedEdges T.2.1.1 T.2.1.2).image (repackRanks T.blockComposition σ) :=
  (IsRankTemplate.relabel_of_forced_adj T.2.2 (repackRanks T.blockComposition σ)
    (T.repackRanks_forced_adj σ)).2

/-- The composition derived from the new template's actual forced edges is
exactly the reordered composition, not merely one with the same length. -/
theorem RankTemplate.reorderBlocks_blockComposition {t m k : ℕ}
    (T : RankTemplate t m k) (σ : Equiv.Perm (Fin T.blockComposition.length)) :
    (T.reorderBlocks σ).blockComposition = reorderedComposition T.blockComposition σ := by
  classical
  have hbound : (T.reorderBlocks σ).blockComposition.boundaries =
      (reorderedComposition T.blockComposition σ).boundaries := by
    ext b
    refine Fin.cases ?_ (fun q => ?_) b
    · exact iff_of_true
        (by
          rw [(T.reorderBlocks σ).blockComposition_boundaries]
          exact (T.reorderBlocks σ).zero_mem_freeGapIndices)
        (reorderedComposition T.blockComposition σ).toCompositionAsSet.zero_mem
    · obtain ⟨p, rfl⟩ := (repackRanks T.blockComposition σ).surjective q
      have hedge : repackRanks T.blockComposition σ p ∈
          forcedEdges (T.reorderBlocks σ).2.1.1 (T.reorderBlocks σ).2.1.2 ↔
          p ∈ forcedEdges T.2.1.1 T.2.1.2 := by
        rw [T.reorderBlocks_forcedEdges σ]
        constructor
        · intro h
          obtain ⟨a, ha, heq⟩ := Finset.mem_image.mp h
          have hap : a = p := (repackRanks T.blockComposition σ).injective heq
          simpa only [hap] using ha
        · intro hp
          exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
      exact not_iff_not.mp
        (((T.reorderBlocks σ).mem_forcedEdges_iff_not_blockBoundary _).symm.trans
          (hedge.trans ((T.mem_forcedEdges_iff_not_blockBoundary p).trans
            (repackRanks_succ_not_boundary T.blockComposition σ p).symm)))
  apply (compositionEquiv (T.1 : ℕ)).injective
  apply CompositionAsSet.ext
  exact hbound

@[simp] theorem RankTemplate.reorderBlocks_gapDimension {t m k : ℕ}
    (T : RankTemplate t m k) (σ : Equiv.Perm (Fin T.blockComposition.length)) :
    (T.reorderBlocks σ).gapDimension = T.gapDimension := by
  calc
    (T.reorderBlocks σ).gapDimension = (T.reorderBlocks σ).blockComposition.length :=
      (T.reorderBlocks σ).blockComposition_length.symm
    _ = (reorderedComposition T.blockComposition σ).length :=
      congrArg Composition.length (T.reorderBlocks_blockComposition σ)
    _ = T.blockComposition.length := reorderedComposition_length T.blockComposition σ
    _ = T.gapDimension := T.blockComposition_length

/-- Block-index transport for the actual new template, stated in natural values
to avoid exposing a cast between its derived length and the old length. -/
theorem RankTemplate.reorderBlocks_index {t m k : ℕ} (T : RankTemplate t m k)
    (σ : Equiv.Perm (Fin T.blockComposition.length)) (q : Fin (T.1 : ℕ)) :
    ((T.reorderBlocks σ).blockComposition.index (repackRanks T.blockComposition σ q) : ℕ) =
      (σ.symm (T.blockComposition.index q) : ℕ) := by
  have hcomp := congrArg
    (fun C : Composition (T.1 : ℕ) =>
      (C.index (repackRanks T.blockComposition σ q) : ℕ))
    (T.reorderBlocks_blockComposition σ)
  have hindex := congrArg
    (fun i : Fin (reorderedComposition T.blockComposition σ).length => (i : ℕ))
    (repackRanks_index T.blockComposition σ q)
  exact hcomp.trans (hindex.trans
    (repackBlockIndex_val T.blockComposition σ (T.blockComposition.index q)))

theorem RankTemplate.reorderBlocks_local {t m k : ℕ} (T : RankTemplate t m k)
    (σ : Equiv.Perm (Fin T.blockComposition.length)) (q : Fin (T.1 : ℕ)) :
    ((T.reorderBlocks σ).blockComposition.invEmbedding
        (repackRanks T.blockComposition σ q) : ℕ) = (T.blockComposition.invEmbedding q : ℕ) := by
  rw [T.reorderBlocks_blockComposition σ]
  exact repackRanks_local T.blockComposition σ q

end MeteredParking

#print axioms MeteredParking.RankTemplate.blockComposition_boundaries
#print axioms MeteredParking.RankTemplate.blockComposition_length
#print axioms MeteredParking.RankTemplate.mem_forcedEdges_iff_not_blockBoundary
#print axioms MeteredParking.composition_adj_same_block_iff
#print axioms MeteredParking.reorderedComposition_length
#print axioms MeteredParking.reorderedComposition_blocksFun
#print axioms MeteredParking.repackRanks_index
#print axioms MeteredParking.repackRanks_local
#print axioms MeteredParking.repackRanks_val
#print axioms MeteredParking.repackRanks_succ_not_boundary
#print axioms MeteredParking.repackRanks_adj
#print axioms MeteredParking.RankTemplate.repackRanks_forced_adj
#print axioms MeteredParking.RankTemplate.reorderBlocks_rank
#print axioms MeteredParking.RankTemplate.reorderBlocks_forcedEdges
#print axioms MeteredParking.RankTemplate.reorderBlocks_blockComposition
#print axioms MeteredParking.RankTemplate.reorderBlocks_gapDimension
#print axioms MeteredParking.RankTemplate.reorderBlocks_index
#print axioms MeteredParking.RankTemplate.reorderBlocks_local

/-!
## Reassembly and whole-block car leaders

Length identifications below preserve natural values. They are not block
permutations: the latter are kept separately, including when lengths coincide.
Undoing a reordering reconstructs both the composition and every rank from its
block index and local coordinate. Leaders are minima of whole-block car fibers;
no luckiness assertion or canonical-template correspondence is assumed here.
-/

namespace MeteredParking

private theorem composition_eq_of_blocksFun_cast {r : ℕ} (C D : Composition r)
    (hlen : C.length = D.length)
    (hblocks : ∀ i : Fin C.length,
      C.blocksFun i = D.blocksFun (Fin.cast hlen i)) : C = D := by
  have ofFn_cast : ∀ {a b : ℕ} (h : a = b) (f : Fin b → ℕ),
      List.ofFn (fun i : Fin a => f (Fin.cast h i)) = List.ofFn f := by
    intro a b h f
    subst b
    rfl
  apply Composition.ext
  calc
    C.blocks = List.ofFn C.blocksFun := C.ofFn_blocksFun.symm
    _ = List.ofFn (fun i => D.blocksFun (Fin.cast hlen i)) :=
      congrArg List.ofFn (funext hblocks)
    _ = List.ofFn D.blocksFun := ofFn_cast hlen D.blocksFun
    _ = D.blocks := D.ofFn_blocksFun

private theorem composition_rank_eq_of_coordinates {r : ℕ} (C : Composition r)
    (p q : Fin r) (hi : (C.index p : ℕ) = (C.index q : ℕ))
    (ha : (C.invEmbedding p : ℕ) = (C.invEmbedding q : ℕ)) : p = q := by
  have hstart : C.sizeUpTo (C.index p : ℕ) = C.sizeUpTo (C.index q : ℕ) :=
    congrArg C.sizeUpTo hi
  have hp := congrArg Fin.val (C.embedding_comp_inv p)
  have hq := congrArg Fin.val (C.embedding_comp_inv q)
  simp only [Composition.coe_embedding] at hp hq
  apply Fin.ext
  omega

theorem reorderedComposition_refl {r : ℕ} (C : Composition r) :
    reorderedComposition C (Equiv.refl _) = C := by
  apply Composition.ext
  exact C.ofFn_blocksFun

theorem repackRanks_refl {r : ℕ} (C : Composition r) (q : Fin r) :
    repackRanks C (Equiv.refl _) q = q := by
  let p := repackRanks C (Equiv.refl _) q
  have hc := reorderedComposition_refl C
  apply composition_rank_eq_of_coordinates C p q
  · have htransport := congrArg (fun D : Composition r => (D.index p : ℕ)) hc
    have hindex := congrArg Fin.val (repackRanks_index C (Equiv.refl _) q)
    exact htransport.symm.trans
      (hindex.trans (repackBlockIndex_val C (Equiv.refl _) (C.index q)))
  · have htransport := congrArg (fun D : Composition r => (D.invEmbedding p : ℕ)) hc
    exact htransport.symm.trans (repackRanks_local C (Equiv.refl _) q)

theorem RankTemplate.reorderBlocks_refl {t m k : ℕ} (T : RankTemplate t m k) :
    T.reorderBlocks (Equiv.refl _) = T := by
  refine Sigma.ext rfl (heq_of_eq ?_)
  apply Subtype.ext
  apply Prod.ext
  · funext j
    exact repackRanks_refl T.blockComposition (T.2.1.1 j)
  · funext j
    exact repackRanks_refl T.blockComposition (T.2.1.2 j)

/-- The actual derived lengths agree; this equality induces only value-preserving casts. -/
theorem RankTemplate.reorderBlocks_length {t m k : ℕ} (T : RankTemplate t m k)
    (σ : Equiv.Perm (Fin T.blockComposition.length)) :
    (T.reorderBlocks σ).blockComposition.length = T.blockComposition.length :=
  ((T.reorderBlocks σ).blockComposition_length.trans (T.reorderBlocks_gapDimension σ)).trans
    T.blockComposition_length.symm

/-- Identify the new length with the old length without permuting block positions. -/
noncomputable def RankTemplate.reorderLengthEquiv {t m k : ℕ} (T : RankTemplate t m k)
    (σ : Equiv.Perm (Fin T.blockComposition.length)) :
    Fin (T.reorderBlocks σ).blockComposition.length ≃ Fin T.blockComposition.length :=
  finCongr (T.reorderBlocks_length σ)

theorem RankTemplate.reorderLengthEquiv_val {t m k : ℕ} (T : RankTemplate t m k)
    (σ : Equiv.Perm (Fin T.blockComposition.length))
    (i : Fin (T.reorderBlocks σ).blockComposition.length) :
    (T.reorderLengthEquiv σ i : ℕ) = (i : ℕ) :=
  finCongr_apply_coe (T.reorderBlocks_length σ) i

private theorem reordered_blocksFun_transport {r : ℕ} (C A : Composition r)
    (σ : Equiv.Perm (Fin C.length)) (h : A = reorderedComposition C σ)
    (e : Fin A.length → Fin C.length) (he : ∀ i, (e i : ℕ) = (i : ℕ))
    (i : Fin A.length) : A.blocksFun i = C.blocksFun (σ (e i)) := by
  subst A
  refine (reorderedComposition_blocksFun C σ i).trans ?_
  apply congrArg (fun b : Fin C.length => C.blocksFun (σ b))
  exact Fin.ext (he i).symm

/-- Indexed block-size transport for the actual derived composition. -/
theorem RankTemplate.reorderBlocks_blocksFun {t m k : ℕ} (T : RankTemplate t m k)
    (σ : Equiv.Perm (Fin T.blockComposition.length))
    (i : Fin (T.reorderBlocks σ).blockComposition.length) :
    (T.reorderBlocks σ).blockComposition.blocksFun i =
      T.blockComposition.blocksFun (σ (T.reorderLengthEquiv σ i)) := by
  exact reordered_blocksFun_transport T.blockComposition (T.reorderBlocks σ).blockComposition
    σ (T.reorderBlocks_blockComposition σ) (T.reorderLengthEquiv σ)
    (T.reorderLengthEquiv_val σ) i

/-- The inverse block permutation transported to the new template's actual length.
Its input is again a new position and its output an old position. -/
noncomputable def RankTemplate.undoBlockPermutation {t m k : ℕ} (T : RankTemplate t m k)
    (σ : Equiv.Perm (Fin T.blockComposition.length)) :
    Equiv.Perm (Fin (T.reorderBlocks σ).blockComposition.length) :=
  ((T.reorderLengthEquiv σ).trans σ.symm).trans (T.reorderLengthEquiv σ).symm

private theorem undo_block_index_cancel {a b : ℕ} (e : Fin a ≃ Fin b)
    (σ : Equiv.Perm (Fin b)) (i : Fin a) :
    σ (e (((e.trans σ.symm).trans e.symm) i)) = e i := by
  exact (congrArg σ (e.apply_symm_apply (σ.symm (e i)))).trans
    (σ.apply_symm_apply (e i))

private theorem undo_block_index_symm {a b : ℕ} (e : Fin a ≃ Fin b)
    (σ : Equiv.Perm (Fin b)) (i : Fin a) :
    e (((e.trans σ.symm).trans e.symm).symm i) = σ (e i) := by
  exact e.apply_symm_apply (σ (e i))

private theorem fin_comp_eq_cast_small {a b c : ℕ} (h : a = c)
    (e : Fin b → Fin c) (f : Fin a → Fin b)
    (he : ∀ j, (e j : ℕ) = (j : ℕ))
    (hf : ∀ i, (f i : ℕ) = (i : ℕ)) (i : Fin a) :
    e (f i) = Fin.cast h i := by
  apply Fin.ext
  exact (he (f i)).trans (hf i)

/-- Undoing the block order recovers every block length in its original position. -/
theorem RankTemplate.reorderBlocks_inverse_blockComposition {t m k : ℕ}
    (T : RankTemplate t m k) (σ : Equiv.Perm (Fin T.blockComposition.length)) :
    ((T.reorderBlocks σ).reorderBlocks (T.undoBlockPermutation σ)).blockComposition =
      T.blockComposition := by
  let U := T.reorderBlocks σ
  let η := T.undoBlockPermutation σ
  let e := T.reorderLengthEquiv σ
  let f := U.reorderLengthEquiv η
  have hlen : (U.reorderBlocks η).blockComposition.length = T.blockComposition.length :=
    (U.reorderBlocks_length η).trans (T.reorderBlocks_length σ)
  change (U.reorderBlocks η).blockComposition = T.blockComposition
  apply composition_eq_of_blocksFun_cast _ _ hlen
  intro i
  have hvalue : e (f i) = Fin.cast hlen i :=
    fin_comp_eq_cast_small
      (a := (U.reorderBlocks η).blockComposition.length)
      (b := U.blockComposition.length) (c := T.blockComposition.length)
      hlen e f (T.reorderLengthEquiv_val σ) (U.reorderLengthEquiv_val η) i
  have hi : σ (e (η (f i))) = Fin.cast hlen i :=
    (undo_block_index_cancel e σ (f i)).trans hvalue
  calc
    (U.reorderBlocks η).blockComposition.blocksFun i =
        U.blockComposition.blocksFun (η (f i)) := U.reorderBlocks_blocksFun η i
    _ = T.blockComposition.blocksFun (σ (e (η (f i)))) := T.reorderBlocks_blocksFun σ _
    _ = T.blockComposition.blocksFun (Fin.cast hlen i) := congrArg T.blockComposition.blocksFun hi

/-- Reassembly of ranks uses both the restored composition and the transported
index/local-coordinate pair, not just the number of blocks. -/
theorem RankTemplate.repackRanks_inverse {t m k : ℕ} (T : RankTemplate t m k)
    (σ : Equiv.Perm (Fin T.blockComposition.length)) (q : Fin (T.1 : ℕ)) :
    repackRanks (T.reorderBlocks σ).blockComposition (T.undoBlockPermutation σ)
      (repackRanks T.blockComposition σ q) = q := by
  let U := T.reorderBlocks σ
  let η := T.undoBlockPermutation σ
  let e := T.reorderLengthEquiv σ
  let p := repackRanks T.blockComposition σ q
  let z := repackRanks U.blockComposition η p
  have hi : e (U.blockComposition.index p) = σ.symm (T.blockComposition.index q) := by
    apply Fin.ext
    exact T.reorderBlocks_index σ q
  have hbackIndex : e (η.symm (U.blockComposition.index p)) = T.blockComposition.index q :=
    (undo_block_index_symm e σ (U.blockComposition.index p)).trans
      ((congrArg σ hi).trans (σ.apply_symm_apply (T.blockComposition.index q)))
  have hback : (η.symm (U.blockComposition.index p) : ℕ) =
      (T.blockComposition.index q : ℕ) :=
    (T.reorderLengthEquiv_val σ (η.symm (U.blockComposition.index p))).symm.trans
      (congrArg Fin.val hbackIndex)
  have hc : (U.reorderBlocks η).blockComposition = T.blockComposition :=
    T.reorderBlocks_inverse_blockComposition σ
  apply composition_rank_eq_of_coordinates T.blockComposition z q
  · have htransport := congrArg (fun C : Composition (T.1 : ℕ) => (C.index z : ℕ)) hc
    exact htransport.symm.trans ((U.reorderBlocks_index η p).trans hback)
  · have htransport := congrArg
      (fun C : Composition (T.1 : ℕ) => (C.invEmbedding z : ℕ)) hc
    exact htransport.symm.trans
      ((U.reorderBlocks_local η p).trans (T.reorderBlocks_local σ q))

/-- Concrete inverse cancellation, retaining all labeled preference and outcome ranks. -/
theorem RankTemplate.reorderBlocks_inverse {t m k : ℕ} (T : RankTemplate t m k)
    (σ : Equiv.Perm (Fin T.blockComposition.length)) :
    (T.reorderBlocks σ).reorderBlocks (T.undoBlockPermutation σ) = T := by
  refine Sigma.ext rfl (heq_of_eq ?_)
  apply Subtype.ext
  apply Prod.ext
  · funext j
    exact T.repackRanks_inverse σ (T.2.1.1 j)
  · funext j
    exact T.repackRanks_inverse σ (T.2.1.2 j)

/-- All cars whose outcomes are in a given whole block. Car labels are unchanged. -/
noncomputable def RankTemplate.blockCarFiber {t m k : ℕ} (T : RankTemplate t m k)
    (i : Fin T.blockComposition.length) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter (fun j => T.blockComposition.index (T.2.1.2 j) = i)

theorem RankTemplate.mem_blockCarFiber {t m k : ℕ} (T : RankTemplate t m k)
    (i : Fin T.blockComposition.length) (j : Fin m) :
    j ∈ T.blockCarFiber i ↔ T.blockComposition.index (T.2.1.2 j) = i := by
  classical
  simp only [RankTemplate.blockCarFiber, Finset.mem_filter, Finset.mem_univ, true_and]

theorem RankTemplate.blockCarFiber_nonempty {t m k : ℕ} (T : RankTemplate t m k)
    (i : Fin T.blockComposition.length) : (T.blockCarFiber i).Nonempty := by
  let a : Fin (T.blockComposition.blocksFun i) := ⟨0, T.blockComposition.one_le_blocksFun i⟩
  have hv : Function.Surjective T.2.1.2 := T.2.2.2.2.1
  obtain ⟨j, hj⟩ := hv (T.blockComposition.embedding i a)
  refine ⟨j, (T.mem_blockCarFiber i j).mpr ?_⟩
  rw [hj]
  exact T.blockComposition.index_embedding i a

/-- The least original car label in a whole block, with no luckiness claim. -/
noncomputable def RankTemplate.blockLeader {t m k : ℕ} (T : RankTemplate t m k)
    (i : Fin T.blockComposition.length) : Fin m :=
  (T.blockCarFiber i).min' (T.blockCarFiber_nonempty i)

theorem RankTemplate.blockLeader_mem {t m k : ℕ} (T : RankTemplate t m k)
    (i : Fin T.blockComposition.length) : T.blockLeader i ∈ T.blockCarFiber i :=
  Finset.min'_mem _ _

theorem RankTemplate.blockLeader_le {t m k : ℕ} (T : RankTemplate t m k)
    (i : Fin T.blockComposition.length) (j : Fin m) (hj : j ∈ T.blockCarFiber i) :
    T.blockLeader i ≤ j := Finset.min'_le _ _ hj

theorem RankTemplate.blockLeader_injective {t m k : ℕ} (T : RankTemplate t m k) :
    Function.Injective T.blockLeader := by
  intro i j hij
  have hi := (T.mem_blockCarFiber i _).mp (T.blockLeader_mem i)
  have hj := (T.mem_blockCarFiber j _).mp (T.blockLeader_mem j)
  rw [hij] at hi
  exact hi.symm.trans hj

/-- Exact whole-block fiber transport: new position `j` contains precisely the
old cars from block `σ j`, with the length cast made explicit. -/
theorem RankTemplate.reorderBlocks_blockCarFiber {t m k : ℕ} (T : RankTemplate t m k)
    (σ : Equiv.Perm (Fin T.blockComposition.length))
    (j : Fin (T.reorderBlocks σ).blockComposition.length) :
    (T.reorderBlocks σ).blockCarFiber j =
      T.blockCarFiber (σ (T.reorderLengthEquiv σ j)) := by
  classical
  let U := T.reorderBlocks σ
  let e := T.reorderLengthEquiv σ
  ext car
  rw [RankTemplate.mem_blockCarFiber, RankTemplate.mem_blockCarFiber]
  have hindex : e (U.blockComposition.index (U.2.1.2 car)) =
      σ.symm (T.blockComposition.index (T.2.1.2 car)) := by
    apply Fin.ext
    exact T.reorderBlocks_index σ (T.2.1.2 car)
  constructor
  · intro h
    have hi : σ.symm (T.blockComposition.index (T.2.1.2 car)) = e j :=
      hindex.symm.trans (congrArg e h)
    exact (σ.apply_symm_apply _).symm.trans (congrArg σ hi)
  · intro h
    apply e.injective
    calc
      e (U.blockComposition.index (U.2.1.2 car)) =
          σ.symm (T.blockComposition.index (T.2.1.2 car)) := hindex
      _ = e j := by rw [h, σ.symm_apply_apply]

/-- Leaders transport by the same block permutation, even for equal-sized blocks. -/
theorem RankTemplate.reorderBlocks_blockLeader {t m k : ℕ} (T : RankTemplate t m k)
    (σ : Equiv.Perm (Fin T.blockComposition.length))
    (j : Fin (T.reorderBlocks σ).blockComposition.length) :
    (T.reorderBlocks σ).blockLeader j = T.blockLeader (σ (T.reorderLengthEquiv σ j)) := by
  let i := σ (T.reorderLengthEquiv σ j)
  have hf : (T.reorderBlocks σ).blockCarFiber j = T.blockCarFiber i :=
    T.reorderBlocks_blockCarFiber σ j
  apply le_antisymm
  · apply (T.reorderBlocks σ).blockLeader_le j
    rw [hf]
    exact T.blockLeader_mem i
  · apply T.blockLeader_le i
    rw [← hf]
    exact (T.reorderBlocks σ).blockLeader_mem j

end MeteredParking

#print axioms MeteredParking.reorderedComposition_refl
#print axioms MeteredParking.repackRanks_refl
#print axioms MeteredParking.RankTemplate.reorderBlocks_refl
#print axioms MeteredParking.RankTemplate.reorderBlocks_length
#print axioms MeteredParking.RankTemplate.reorderLengthEquiv_val
#print axioms MeteredParking.RankTemplate.reorderBlocks_blocksFun
#print axioms MeteredParking.RankTemplate.reorderBlocks_inverse_blockComposition
#print axioms MeteredParking.RankTemplate.repackRanks_inverse
#print axioms MeteredParking.RankTemplate.reorderBlocks_inverse
#print axioms MeteredParking.RankTemplate.mem_blockCarFiber
#print axioms MeteredParking.RankTemplate.blockCarFiber_nonempty
#print axioms MeteredParking.RankTemplate.blockLeader_mem
#print axioms MeteredParking.RankTemplate.blockLeader_le
#print axioms MeteredParking.RankTemplate.blockLeader_injective
#print axioms MeteredParking.RankTemplate.reorderBlocks_blockCarFiber
#print axioms MeteredParking.RankTemplate.reorderBlocks_blockLeader

/-!
## Canonical templates and their reconstruction permutations

Canonical order is increasing order of the minimum original car label in each
whole block. Sorting acts on block identities, not merely on their lengths.
The correspondence is first proved at the actual composition length. Its final
boundary changes only the permutation index type to `Fin gapDimension`.
-/

namespace MeteredParking

/-- A canonical template has its whole-block leaders in increasing order. -/
def Canonical {t m k : ℕ} (T : RankTemplate t m k) : Prop :=
  StrictMono T.blockLeader

private noncomputable def RankTemplate.leaderImage {t m k : ℕ}
    (T : RankTemplate t m k) : Finset (Fin m) :=
  Finset.univ.image T.blockLeader

private theorem RankTemplate.leaderImage_card {t m k : ℕ} (T : RankTemplate t m k) :
    T.leaderImage.card = T.blockComposition.length := by
  classical
  rw [RankTemplate.leaderImage, Finset.card_image_of_injective _ T.blockLeader_injective]
  exact Fintype.card_fin _

private noncomputable def RankTemplate.leaderImageEquiv {t m k : ℕ}
    (T : RankTemplate t m k) : Fin T.blockComposition.length ≃ ↥T.leaderImage := by
  classical
  let f : Fin T.blockComposition.length → ↥T.leaderImage := fun i =>
    ⟨T.blockLeader i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
  apply Equiv.ofBijective f
  constructor
  · intro i j h
    exact T.blockLeader_injective (congrArg Subtype.val h)
  · rintro ⟨j, hj⟩
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hj
    exact ⟨i, Subtype.ext hi⟩

/-- New sorted position maps to the old block having that leader. -/
noncomputable def RankTemplate.sortBlocks {t m k : ℕ} (T : RankTemplate t m k) :
    Equiv.Perm (Fin T.blockComposition.length) :=
  (T.leaderImage.orderIsoOfFin T.leaderImage_card).toEquiv.trans T.leaderImageEquiv.symm

private theorem RankTemplate.blockLeader_sortBlocks {t m k : ℕ} (T : RankTemplate t m k)
    (i : Fin T.blockComposition.length) :
    T.blockLeader (T.sortBlocks i) = T.leaderImage.orderEmbOfFin T.leaderImage_card i :=
  congrArg Subtype.val (T.leaderImageEquiv.apply_symm_apply
    (T.leaderImage.orderIsoOfFin T.leaderImage_card i))

theorem RankTemplate.sortBlocks_strictMono {t m k : ℕ} (T : RankTemplate t m k) :
    StrictMono (fun i => T.blockLeader (T.sortBlocks i)) := by
  intro i j hij
  exact (T.blockLeader_sortBlocks i).trans_lt
    (((T.leaderImage.orderEmbOfFin T.leaderImage_card).strictMono hij).trans_eq
      (T.blockLeader_sortBlocks j).symm)

/-- Sorting is unique, including when different blocks have the same length. -/
theorem RankTemplate.sortBlocks_unique {t m k : ℕ} (T : RankTemplate t m k)
    (ρ : Equiv.Perm (Fin T.blockComposition.length)) :
    StrictMono (fun i => T.blockLeader (ρ i)) ↔ ρ = T.sortBlocks := by
  classical
  constructor
  · intro hρ
    have hfun : (fun i => T.blockLeader (ρ i)) =
        T.leaderImage.orderEmbOfFin T.leaderImage_card :=
      Finset.orderEmbOfFin_unique T.leaderImage_card
        (fun i => Finset.mem_image.mpr ⟨ρ i, Finset.mem_univ _, rfl⟩) hρ
    apply Equiv.ext
    intro i
    apply T.blockLeader_injective
    exact (congrFun hfun i).trans (T.blockLeader_sortBlocks i).symm
  · rintro rfl
    exact T.sortBlocks_strictMono

theorem RankTemplate.sortBlocks_eq_refl {t m k : ℕ} (T : RankTemplate t m k)
    (hT : Canonical T) : T.sortBlocks = Equiv.refl _ :=
  ((T.sortBlocks_unique (Equiv.refl _)).mp hT).symm

private theorem finMap_strictMono_of_value {a b : ℕ} (e : Fin a → Fin b)
    (he : ∀ i, (e i : ℕ) = (i : ℕ)) : StrictMono e := by
  intro i j hij
  change (e i : ℕ) < (e j : ℕ)
  rw [he i, he j]
  exact hij

private theorem RankTemplate.canonical_reorder_sorted {t m k : ℕ} (T : RankTemplate t m k)
    (σ : Equiv.Perm (Fin T.blockComposition.length))
    (hs : StrictMono (fun i => T.blockLeader (σ i))) : Canonical (T.reorderBlocks σ) := by
  have he := finMap_strictMono_of_value (T.reorderLengthEquiv σ) (T.reorderLengthEquiv_val σ)
  intro i j hij
  calc
    (T.reorderBlocks σ).blockLeader i = T.blockLeader (σ (T.reorderLengthEquiv σ i)) :=
      T.reorderBlocks_blockLeader σ i
    _ < T.blockLeader (σ (T.reorderLengthEquiv σ j)) := hs (he hij)
    _ = (T.reorderBlocks σ).blockLeader j := (T.reorderBlocks_blockLeader σ j).symm

/-- Sorting produces a canonical member of the existing template type. -/
noncomputable def RankTemplate.canonicalize {t m k : ℕ} (T : RankTemplate t m k) :
    {S : RankTemplate t m k // Canonical S} :=
  ⟨T.reorderBlocks T.sortBlocks, T.canonical_reorder_sorted T.sortBlocks T.sortBlocks_strictMono⟩

private theorem sorted_block_index_cancel {a b : ℕ} (e : Fin a ≃ Fin b)
    (σ s : Equiv.Perm (Fin b)) (i : Fin a) :
    σ (e ((((e.trans s).trans σ.symm).trans e.symm) i)) = s (e i) :=
  (congrArg σ (e.apply_symm_apply (σ.symm (s (e i))))).trans (σ.apply_symm_apply (s (e i)))

/-- Sorting after reordering uses inverse block transport, with only the
value-preserving length identification on the position arguments. -/
theorem RankTemplate.sortBlocks_reorder {t m k : ℕ} (T : RankTemplate t m k)
    (σ : Equiv.Perm (Fin T.blockComposition.length)) :
    (T.reorderBlocks σ).sortBlocks =
      (((T.reorderLengthEquiv σ).trans T.sortBlocks).trans σ.symm).trans
        (T.reorderLengthEquiv σ).symm := by
  let U := T.reorderBlocks σ
  let e := T.reorderLengthEquiv σ
  let ρ := ((e.trans T.sortBlocks).trans σ.symm).trans e.symm
  have he := finMap_strictMono_of_value e (T.reorderLengthEquiv_val σ)
  have hleader (i : Fin U.blockComposition.length) :
      U.blockLeader (ρ i) = T.blockLeader (T.sortBlocks (e i)) :=
    (T.reorderBlocks_blockLeader σ (ρ i)).trans
      (congrArg T.blockLeader (sorted_block_index_cancel e σ T.sortBlocks i))
  have hs : StrictMono (fun i => U.blockLeader (ρ i)) := by
    intro i j hij
    exact (hleader i).trans_lt
      ((T.sortBlocks_strictMono (he hij)).trans_eq (hleader j).symm)
  exact ((U.sortBlocks_unique ρ).mp hs).symm

private theorem RankTemplate.sortBlocks_reorder_canonical {t m k : ℕ}
    (T : RankTemplate t m k) (hT : Canonical T)
    (σ : Equiv.Perm (Fin T.blockComposition.length)) :
    (T.reorderBlocks σ).sortBlocks = T.undoBlockPermutation σ := by
  have hs := T.sortBlocks_reorder σ
  rw [T.sortBlocks_eq_refl hT] at hs
  exact hs

/-- Canonicalization of a reconstructed canonical template recovers that template. -/
theorem RankTemplate.canonicalize_reorder {t m k : ℕ} (T : RankTemplate t m k)
    (hT : Canonical T) (σ : Equiv.Perm (Fin T.blockComposition.length)) :
    (T.reorderBlocks σ).canonicalize = ⟨T, hT⟩ := by
  apply Subtype.ext
  change (T.reorderBlocks σ).reorderBlocks (T.reorderBlocks σ).sortBlocks = T
  exact (congrArg (fun ρ => (T.reorderBlocks σ).reorderBlocks ρ)
    (T.sortBlocks_reorder_canonical hT σ)).trans (T.reorderBlocks_inverse σ)

/-- Canonical template paired with its inverse reconstruction permutation,
still indexed internally by the actual composition length. -/
noncomputable def canonicalPresentation {t m k : ℕ} (T : RankTemplate t m k) :
    Σ S : {T : RankTemplate t m k // Canonical T}, Equiv.Perm (Fin S.1.blockComposition.length) :=
  ⟨T.canonicalize, T.undoBlockPermutation T.sortBlocks⟩

noncomputable def reconstructCanonical {t m k : ℕ}
    (z : Σ S : {T : RankTemplate t m k // Canonical T},
      Equiv.Perm (Fin S.1.blockComposition.length)) : RankTemplate t m k :=
  z.1.1.reorderBlocks z.2

/-- First roundtrip: the accepted concrete inverse reconstructs both labeled rank functions. -/
theorem reconstruct_canonicalPresentation {t m k : ℕ} (T : RankTemplate t m k) :
    reconstructCanonical (canonicalPresentation T) = T :=
  T.reorderBlocks_inverse T.sortBlocks

private theorem blockLeader_transport_eq {t m k : ℕ} {T U : RankTemplate t m k}
    (h : T = U) (i : Fin T.blockComposition.length) (j : Fin U.blockComposition.length)
    (hij : (i : ℕ) = (j : ℕ)) : T.blockLeader i = U.blockLeader j := by
  subst U
  exact congrArg T.blockLeader (Fin.ext hij)

/-- Reconstruction determines the whole dependent pair. Canonicalization
recovers its first component; injective leaders recover the second permutation. -/
theorem reconstructCanonical_injective {t m k : ℕ} :
    Function.Injective (@reconstructCanonical t m k) := by
  rintro ⟨⟨T, hT⟩, π⟩ ⟨⟨U, hU⟩, ρ⟩ h
  have hout : T.reorderBlocks π = U.reorderBlocks ρ := h
  have hbase : T = U := congrArg Subtype.val
    ((T.canonicalize_reorder hT π).symm.trans
      ((congrArg (fun V : RankTemplate t m k => V.canonicalize) hout).trans
        (U.canonicalize_reorder hU ρ)))
  subst U
  have hperm : π = ρ := by
    apply Equiv.ext
    intro i
    let e := T.reorderLengthEquiv π
    let f := T.reorderLengthEquiv ρ
    have hei : (e.symm i : ℕ) = (i : ℕ) :=
      finCongr_symm_apply_coe (T.reorderBlocks_length π) i
    have hfi : (f.symm i : ℕ) = (i : ℕ) :=
      finCongr_symm_apply_coe (T.reorderBlocks_length ρ) i
    have hleader := blockLeader_transport_eq hout (e.symm i) (f.symm i) (hei.trans hfi.symm)
    have hleft : (T.reorderBlocks π).blockLeader (e.symm i) = T.blockLeader (π i) :=
      (T.reorderBlocks_blockLeader π (e.symm i)).trans
        (congrArg (fun j => T.blockLeader (π j)) (e.apply_symm_apply i))
    have hright : (T.reorderBlocks ρ).blockLeader (f.symm i) = T.blockLeader (ρ i) :=
      (T.reorderBlocks_blockLeader ρ (f.symm i)).trans
        (congrArg (fun j => T.blockLeader (ρ j)) (f.apply_symm_apply i))
    exact T.blockLeader_injective (hleft.symm.trans (hleader.trans hright))
  cases hperm
  rfl

/-- Second roundtrip is equality of the entire Sigma value, including its
transported permutation component. It is not merely equality of templates. -/
theorem canonicalPresentation_reconstruct {t m k : ℕ}
    (z : Σ S : {T : RankTemplate t m k // Canonical T},
      Equiv.Perm (Fin S.1.blockComposition.length)) :
    canonicalPresentation (reconstructCanonical z) = z :=
  reconstructCanonical_injective (reconstruct_canonicalPresentation (reconstructCanonical z))

/-- The internal correspondence uses composition lengths throughout. -/
noncomputable def rankTemplateEquivCanonicalLength (t m k : ℕ) :
    RankTemplate t m k ≃
      Σ S : {T : RankTemplate t m k // Canonical T},
        Equiv.Perm (Fin S.1.blockComposition.length) where
  toFun := canonicalPresentation
  invFun := reconstructCanonical
  left_inv := reconstruct_canonicalPresentation
  right_inv := canonicalPresentation_reconstruct

/-- The only external index change: conjugate by the value-preserving equality
between the derived block count and `gapDimension`. Both directions are an Equiv. -/
noncomputable def RankTemplate.gapPermutationEquiv {t m k : ℕ} (T : RankTemplate t m k) :
    Equiv.Perm (Fin T.blockComposition.length) ≃ Equiv.Perm (Fin T.gapDimension) :=
  Equiv.equivCongr (finCongr T.blockComposition_length) (finCongr T.blockComposition_length)

/-- Every rank template has a unique canonical template and a reconstruction
permutation on its gap dimensions. No counting or coefficient claim is made here. -/
noncomputable def rankTemplateEquivCanonical (t m k : ℕ) :
    RankTemplate t m k ≃
      Σ S : {T : RankTemplate t m k // Canonical T}, Equiv.Perm (Fin S.1.gapDimension) :=
  (rankTemplateEquivCanonicalLength t m k).trans
    (Equiv.sigmaCongrRight (fun S => S.1.gapPermutationEquiv))

theorem rankTemplateEquivCanonical_left_inv {t m k : ℕ} (T : RankTemplate t m k) :
    (rankTemplateEquivCanonical t m k).symm (rankTemplateEquivCanonical t m k T) = T :=
  (rankTemplateEquivCanonical t m k).symm_apply_apply T

theorem rankTemplateEquivCanonical_right_inv {t m k : ℕ}
    (z : Σ S : {T : RankTemplate t m k // Canonical T}, Equiv.Perm (Fin S.1.gapDimension)) :
    rankTemplateEquivCanonical t m k ((rankTemplateEquivCanonical t m k).symm z) = z :=
  (rankTemplateEquivCanonical t m k).apply_symm_apply z

/-- Reconstruction preserves the rank-count projection needed for sum reindexing. -/
theorem rankTemplateEquivCanonical_symm_rank {t m k : ℕ}
    (z : Σ S : {T : RankTemplate t m k // Canonical T}, Equiv.Perm (Fin S.1.gapDimension)) :
    ((rankTemplateEquivCanonical t m k).symm z).1 = z.1.1.1 := by
  change (z.1.1.reorderBlocks (z.1.1.gapPermutationEquiv.symm z.2)).1 = z.1.1.1
  exact z.1.1.reorderBlocks_rank _

theorem rankTemplateEquivCanonical_symm_gapDimension {t m k : ℕ}
    (z : Σ S : {T : RankTemplate t m k // Canonical T}, Equiv.Perm (Fin S.1.gapDimension)) :
    ((rankTemplateEquivCanonical t m k).symm z).gapDimension = z.1.1.gapDimension := by
  change (z.1.1.reorderBlocks (z.1.1.gapPermutationEquiv.symm z.2)).gapDimension =
    z.1.1.gapDimension
  exact z.1.1.reorderBlocks_gapDimension _

end MeteredParking

#print axioms MeteredParking.RankTemplate.sortBlocks_strictMono
#print axioms MeteredParking.RankTemplate.sortBlocks_unique
#print axioms MeteredParking.RankTemplate.sortBlocks_eq_refl
#print axioms MeteredParking.RankTemplate.canonicalize
#print axioms MeteredParking.RankTemplate.sortBlocks_reorder
#print axioms MeteredParking.RankTemplate.canonicalize_reorder
#print axioms MeteredParking.reconstruct_canonicalPresentation
#print axioms MeteredParking.reconstructCanonical_injective
#print axioms MeteredParking.canonicalPresentation_reconstruct
#print axioms MeteredParking.rankTemplateEquivCanonicalLength
#print axioms MeteredParking.RankTemplate.gapPermutationEquiv
#print axioms MeteredParking.rankTemplateEquivCanonical
#print axioms MeteredParking.rankTemplateEquivCanonical_left_inv
#print axioms MeteredParking.rankTemplateEquivCanonical_right_inv
#print axioms MeteredParking.rankTemplateEquivCanonical_symm_rank
#print axioms MeteredParking.rankTemplateEquivCanonical_symm_gapDimension
