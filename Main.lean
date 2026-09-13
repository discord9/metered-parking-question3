import AiMathLab

/-!
## One-meter parking: preferences, histories, and one-step extensions

The public count is the cardinality of successful ordered preferences in the
existing first-free process, without fixing a lucky-car stratum. Histories are
an auxiliary finite type only: forgetting the outcome is proved bijective.
The extension theorem retains the two distinct preferences that can lead from
a previous outcome to its immediate successor. No state recurrence is assumed.
-/

namespace MeteredParking.OneMeter

/-- Successful preferences at arbitrary car length, with no lucky-count restriction. -/
def Successful (m n : ℕ) :=
  {a : Fin m → Fin n // ∃ p : Fin m → Fin n, IsParking 1 a p}

noncomputable instance successfulFintype (m n : ℕ) : Fintype (Successful m n) := by
  classical
  unfold Successful
  infer_instance

/-- The number of successful preference lists; car length precedes capacity. -/
noncomputable def totalCount (m n : ℕ) : ℕ :=
  Fintype.card (Successful m n)

/-- Auxiliary successful preference/outcome pairs for finite counting. -/
def History (m n : ℕ) :=
  {ap : (Fin m → Fin n) × (Fin m → Fin n) // IsParking 1 ap.1 ap.2}

noncomputable instance historyFintype (m n : ℕ) : Fintype (History m n) := by
  classical
  unfold History
  infer_instance

/-- Forget only the outcome, retaining the original ordered preference function. -/
def forgetHistory {m n : ℕ} (h : History m n) : Successful m n :=
  ⟨h.1.1, h.1.2, h.2⟩

private theorem forgetHistory_bijective (m n : ℕ) :
    Function.Bijective (@forgetHistory m n) := by
  constructor
  · rintro ⟨⟨a, p⟩, hp⟩ ⟨⟨b, q⟩, hq⟩ h
    have hab : a = b := congrArg Subtype.val h
    subst b
    have hpq : p = q := IsParking.unique hp hq
    subst q
    rfl
  · rintro ⟨a, p, hp⟩
    exact ⟨⟨(a, p), hp⟩, rfl⟩

/-- Outcome uniqueness makes histories equivalent to preferences, not a new count model. -/
noncomputable def historyEquivSuccessful (m n : ℕ) : History m n ≃ Successful m n :=
  Equiv.ofBijective (@forgetHistory m n) (forgetHistory_bijective m n)

theorem card_history (m n : ℕ) : Fintype.card (History m n) = totalCount m n :=
  Fintype.card_congr (historyEquivSuccessful m n)

/-- For meter duration one, the only active earlier car is the immediate predecessor. -/
theorem active_one_iff {m : ℕ} (i j : Fin m) :
    Active 1 i j ↔ (i : ℕ) + 1 = (j : ℕ) := by
  change ((i : ℕ) < (j : ℕ) ∧ (j : ℕ) ≤ (i : ℕ) + 1) ↔ _
  omega

/-- The empty history satisfies the process at every capacity, including zero. -/
theorem isParking_zero {n : ℕ} (a p : Fin 0 → Fin n) : IsParking 1 a p := by
  intro j
  exact Fin.elim0 j

/-- With one car, the outcome equals its preference. -/
theorem isParking_one_iff {n : ℕ} (a p : Fin 1 → Fin n) :
    IsParking 1 a p ↔ a = p := by
  constructor
  · intro hp
    funext j
    rcases IsParking.preference_eq_or_active hp j with heq | ⟨i, hij, _⟩
    · exact heq
    · have hactive := (active_one_iff i j).mp hij
      have hi := i.isLt
      have hj := j.isLt
      omega
  · intro h
    subst p
    intro j
    refine ⟨le_rfl, ?_, ?_⟩
    · intro i hij
      have hactive := (active_one_iff i j).mp hij
      have hi := i.isLt
      have hj := j.isLt
      omega
    · intro s has hsa
      exact False.elim ((not_lt_of_ge has) hsa)

theorem totalCount_zero (n : ℕ) : totalCount 0 n = 1 := by
  letI : Unique (Successful 0 n) :=
    { default := ⟨Fin.elim0, Fin.elim0, isParking_zero _ _⟩
      uniq := by
        intro a
        apply Subtype.ext
        funext j
        exact Fin.elim0 j }
  exact Fintype.card_unique

theorem totalCount_one (n : ℕ) : totalCount 1 n = n := by
  let e : Successful 1 n ≃ Fin n :=
    { toFun := fun a => a.1 0
      invFun := fun s =>
        ⟨fun _ => s, fun _ => s, (isParking_one_iff _ _).mpr rfl⟩
      left_inv := by
        intro a
        apply Subtype.ext
        funext j
        have hj : j = 0 := Subsingleton.elim _ _
        subst j
        rfl
      right_inv := by intro s; rfl }
  exact (Fintype.card_congr e).trans (Fintype.card_fin n)

private theorem active_one_before_castSucc {m : ℕ} {i : Fin (m + 1)} {j : Fin m}
    (h : Active 1 i j.castSucc) :
    ∃ i' : Fin m, i'.castSucc = i ∧ Active 1 i' j := by
  have hij : (i : ℕ) < (j : ℕ) := h.1
  let i' : Fin m := ⟨(i : ℕ), lt_trans hij j.isLt⟩
  exact ⟨i', Fin.ext rfl, ⟨h.1, h.2⟩⟩

/-- Removing the final car from a successful history preserves every earlier search. -/
theorem isParking_init {m n : ℕ} {a p : Fin (m + 1) → Fin n}
    (hp : IsParking 1 a p) : IsParking 1 (Fin.init a) (Fin.init p) := by
  intro j
  have hj := hp j.castSucc
  refine ⟨hj.1, ?_, ?_⟩
  · intro i hij
    exact hj.2.1 i.castSucc ⟨hij.1, hij.2⟩
  · intro s has hsp
    obtain ⟨i, hij, his⟩ := hj.2.2 s has hsp
    obtain ⟨i', hi'i, hi'j⟩ := active_one_before_castSucc hij
    refine ⟨i', hi'j, ?_⟩
    change p i'.castSucc = s
    rw [hi'i]
    exact his

private theorem active_one_last_iff {r : ℕ} (i : Fin (r + 1 + 1)) :
    Active 1 i (Fin.last (r + 1)) ↔ i = (Fin.last r).castSucc := by
  rw [active_one_iff]
  constructor
  · intro h
    apply Fin.ext
    change (i : ℕ) = r
    change (i : ℕ) + 1 = r + 1 at h
    omega
  · rintro rfl
    rfl

private theorem single_occupied_iff {n : ℕ} (i b q : Fin n) :
    (b ≤ q ∧ q ≠ i ∧ ∀ s : Fin n, b ≤ s → s < q → i = s) ↔
      (b = q ∧ q ≠ i) ∨ (b = i ∧ (q : ℕ) = (i : ℕ) + 1) := by
  constructor
  · rintro ⟨hbq, hqi, hcover⟩
    rcases lt_or_eq_of_le hbq with hlt | heq
    · have hib : i = b := hcover b le_rfl hlt
      refine Or.inr ⟨hib.symm, ?_⟩
      have hibNat : (i : ℕ) = (b : ℕ) := congrArg Fin.val hib
      have hltNat : (b : ℕ) < (q : ℕ) := hlt
      by_contra hstep
      let s : Fin n := ⟨(b : ℕ) + 1, by
        have hqn := q.isLt
        omega⟩
      have hbs : b ≤ s := by
        change (b : ℕ) ≤ (b : ℕ) + 1
        omega
      have hsq : s < q := by
        change (b : ℕ) + 1 < (q : ℕ)
        omega
      have his : (i : ℕ) = (b : ℕ) + 1 := congrArg Fin.val (hcover s hbs hsq)
      omega
    · exact Or.inl ⟨heq, hqi⟩
  · rintro (⟨hbq, hqi⟩ | ⟨hbi, hstep⟩)
    · subst b
      refine ⟨le_rfl, hqi, ?_⟩
      intro s hqs hsq
      exact False.elim ((not_lt_of_ge hqs) hsq)
    · subst b
      have hiq : i < q := by
        change (i : ℕ) < (q : ℕ)
        omega
      refine ⟨le_of_lt hiq, ne_of_gt hiq, ?_⟩
      intro s his hsq
      apply Fin.ext
      have hisNat : (i : ℕ) ≤ (s : ℕ) := his
      have hsqNat : (s : ℕ) < (q : ℕ) := hsq
      omega

/-- Exact extension of a nonempty history. The previous last car is still
present during the new search. The second branch uses natural-value successor,
so an occupied final spot cannot overflow or wrap around. -/
theorem isParking_snoc_iff {r n : ℕ} (a p : Fin (r + 1) → Fin n) (b q : Fin n) :
    IsParking 1 (Fin.snoc a b) (Fin.snoc p q) ↔
      IsParking 1 a p ∧
        ((b = q ∧ q ≠ p (Fin.last r)) ∨
          (b = p (Fin.last r) ∧ (q : ℕ) = (p (Fin.last r) : ℕ) + 1)) := by
  constructor
  · intro hp
    have hpref : IsParking 1 a p := by
      simpa only [Fin.init_snoc] using isParking_init hp
    refine ⟨hpref, (single_occupied_iff (p (Fin.last r)) b q).mp ?_⟩
    have hlast := hp (Fin.last (r + 1))
    simp only [Fin.snoc_last] at hlast
    refine ⟨hlast.1, ?_, ?_⟩
    · have hactive : Active 1 (Fin.last r).castSucc (Fin.last (r + 1)) :=
        (active_one_last_iff _).mpr rfl
      simpa only [Fin.snoc_castSucc] using hlast.2.1 (Fin.last r).castSucc hactive
    · intro s hbs hsq
      obtain ⟨i, hi, his⟩ := hlast.2.2 s hbs hsq
      have hieq := (active_one_last_iff i).mp hi
      simpa only [hieq, Fin.snoc_castSucc] using his
  · rintro ⟨hp, hstep⟩
    have hlocal := (single_occupied_iff (p (Fin.last r)) b q).mpr hstep
    intro j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [Fin.snoc_last]
      refine ⟨hlocal.1, ?_, ?_⟩
      · intro i hi
        have hieq := (active_one_last_iff i).mp hi
        rw [hieq, Fin.snoc_castSucc]
        exact hlocal.2.1
      · intro s hbs hsq
        refine ⟨(Fin.last r).castSucc, (active_one_last_iff _).mpr rfl, ?_⟩
        simpa only [Fin.snoc_castSucc] using hlocal.2.2 s hbs hsq
    · simp only [Fin.snoc_castSucc]
      refine ⟨(hp j).1, ?_, ?_⟩
      · intro i hij
        obtain ⟨i', hi'i, hi'j⟩ := active_one_before_castSucc hij
        rw [← hi'i, Fin.snoc_castSucc]
        exact (hp j).2.1 i' hi'j
      · intro s has hsp
        obtain ⟨i, hij, his⟩ := (hp j).2.2 s has hsp
        refine ⟨i.castSucc, ⟨hij.1, hij.2⟩, ?_⟩
        simpa only [Fin.snoc_castSucc] using his

end MeteredParking.OneMeter

#print axioms MeteredParking.OneMeter.historyEquivSuccessful
#print axioms MeteredParking.OneMeter.card_history
#print axioms MeteredParking.OneMeter.active_one_iff
#print axioms MeteredParking.OneMeter.isParking_zero
#print axioms MeteredParking.OneMeter.isParking_one_iff
#print axioms MeteredParking.OneMeter.totalCount_zero
#print axioms MeteredParking.OneMeter.totalCount_one
#print axioms MeteredParking.OneMeter.isParking_init
#print axioms MeteredParking.OneMeter.isParking_snoc_iff

/-!
## Last-outcome fibers and tagged extension counts

Every fiber consists of actual successful histories. The two summands of the
extension equivalence retain their tags: a prefix ending immediately before
`j` can occur in both, yielding the distinct appended preferences `j` and its
predecessor. Cardinalities transfer back to the direct preference count through
`card_history`. All balances in this section are in the natural numbers.
-/

namespace MeteredParking.OneMeter

open scoped BigOperators

/-- Only nonempty histories have a last outcome. -/
def lastOutcome {r n : ℕ} (H : History (r + 1) n) : Fin n :=
  H.1.2 (Fin.last r)

/-- Histories of length `r + 1` whose final outcome is `j`. -/
def LastFiber (r n : ℕ) (j : Fin n) :=
  {H : History (r + 1) n // lastOutcome H = j}

noncomputable instance lastFiberFintype (r n : ℕ) (j : Fin n) : Fintype (LastFiber r n j) := by
  classical
  unfold LastFiber
  infer_instance

private def prefixHistory {r n : ℕ} (H : History (r + 1 + 1) n) : History (r + 1) n :=
  ⟨(Fin.init H.1.1, Fin.init H.1.2), isParking_init H.2⟩

private theorem lastFiber_step {r n : ℕ} {j : Fin n} (H : LastFiber (r + 1) n j) :
    (H.1.1.1 (Fin.last (r + 1)) = j ∧ j ≠ lastOutcome (prefixHistory H.1)) ∨
      (H.1.1.1 (Fin.last (r + 1)) = lastOutcome (prefixHistory H.1) ∧
        (j : ℕ) = (lastOutcome (prefixHistory H.1) : ℕ) + 1) := by
  have hs := (isParking_snoc_iff (Fin.init H.1.1.1) (Fin.init H.1.1.2)
    (H.1.1.1 (Fin.last (r + 1))) (H.1.1.2 (Fin.last (r + 1)))).mp
      (by simpa only [Fin.snoc_init_self] using H.1.2)
  have hend : H.1.1.2 (Fin.last (r + 1)) = j := H.2
  simpa only [hend, prefixHistory, lastOutcome] using hs.2

private def extendLast {r n : ℕ} (j : Fin n) :
    ({H : History (r + 1) n // lastOutcome H ≠ j} ⊕
      {H : History (r + 1) n // (lastOutcome H : ℕ) + 1 = (j : ℕ)}) →
        LastFiber (r + 1) n j
  | Sum.inl H =>
      ⟨⟨(Fin.snoc H.1.1.1 j, Fin.snoc H.1.1.2 j),
        (isParking_snoc_iff H.1.1.1 H.1.1.2 j j).mpr
          ⟨H.1.2, Or.inl ⟨rfl, Ne.symm H.2⟩⟩⟩, by simp only [lastOutcome, Fin.snoc_last]⟩
  | Sum.inr H =>
      ⟨⟨(Fin.snoc H.1.1.1 (lastOutcome H.1), Fin.snoc H.1.1.2 j),
        (isParking_snoc_iff H.1.1.1 H.1.1.2 (lastOutcome H.1) j).mpr
          ⟨H.1.2, Or.inr ⟨rfl, H.2.symm⟩⟩⟩, by simp only [lastOutcome, Fin.snoc_last]⟩

/-- Data are chosen by decidable equality of the appended preference with `j`.
The propositional alternatives from parking are used only to prove membership. -/
private def splitLast {r n : ℕ} {j : Fin n} (H : LastFiber (r + 1) n j) :
    {H : History (r + 1) n // lastOutcome H ≠ j} ⊕
      {H : History (r + 1) n // (lastOutcome H : ℕ) + 1 = (j : ℕ)} := by
  let P := prefixHistory H.1
  exact if hb : H.1.1.1 (Fin.last (r + 1)) = j then
    Sum.inl ⟨P, by
      rcases lastFiber_step H with h | h
      · exact Ne.symm h.2
      · intro heq
        have hstep : (j : ℕ) = (lastOutcome P : ℕ) + 1 := h.2
        have hval := congrArg Fin.val heq
        omega⟩
  else
    Sum.inr ⟨P, by
      rcases lastFiber_step H with h | h
      · exact False.elim (hb h.1)
      · exact h.2.symm⟩

private theorem splitLast_extendLast {r n : ℕ} (j : Fin n)
    (z : {H : History (r + 1) n // lastOutcome H ≠ j} ⊕
      {H : History (r + 1) n // (lastOutcome H : ℕ) + 1 = (j : ℕ)}) :
    splitLast (extendLast j z) = z := by
  rcases z with ⟨⟨⟨a, p⟩, hp⟩, hne⟩ | ⟨⟨⟨a, p⟩, hp⟩, hstep⟩
  · simp [splitLast, extendLast, prefixHistory]
  · have hne : p (Fin.last r) ≠ j := by
      intro h
      have hval := congrArg Fin.val h
      change (p (Fin.last r) : ℕ) + 1 = (j : ℕ) at hstep
      omega
    simp [splitLast, extendLast, prefixHistory, lastOutcome, hne]

private theorem extendLast_splitLast {r n : ℕ} {j : Fin n} (H : LastFiber (r + 1) n j) :
    extendLast j (splitLast H) = H := by
  rcases H with ⟨⟨⟨a, p⟩, hp⟩, hpj⟩
  have hend : p (Fin.last (r + 1)) = j := hpj
  by_cases hb : a (Fin.last (r + 1)) = j
  · simp only [splitLast, dif_pos hb, extendLast]
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · change Fin.snoc (Fin.init a) j = a
      rw [← hb, Fin.snoc_init_self]
    · change Fin.snoc (Fin.init p) j = p
      rw [← hend, Fin.snoc_init_self]
  · have hbi : a (Fin.last (r + 1)) =
        lastOutcome (prefixHistory (⟨(a, p), hp⟩ : History (r + 1 + 1) n)) := by
      have hs := lastFiber_step (⟨⟨(a, p), hp⟩, hpj⟩ : LastFiber (r + 1) n j)
      exact (hs.resolve_left (fun h => hb h.1)).1
    simp only [splitLast, dif_neg hb, extendLast]
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · change Fin.snoc (Fin.init a)
        (lastOutcome (prefixHistory (⟨(a, p), hp⟩ : History (r + 1 + 1) n))) = a
      rw [← hbi, Fin.snoc_init_self]
    · change Fin.snoc (Fin.init p) j = p
      rw [← hend, Fin.snoc_init_self]

/-- The two tagged extension mechanisms count distinct appended preferences,
even when the same prefix belongs to both summands. -/
def lastFiberEquivExtensions (r n : ℕ) (j : Fin n) :
    LastFiber (r + 1) n j ≃
      ({H : History (r + 1) n // lastOutcome H ≠ j} ⊕
        {H : History (r + 1) n // (lastOutcome H : ℕ) + 1 = (j : ℕ)}) where
  toFun := splitLast
  invFun := extendLast j
  left_inv := extendLast_splitLast
  right_inv := splitLast_extendLast j

/-- Partition nonempty histories by their last outcome and transfer back to
ordered preferences using the already-proved forgetful equivalence. -/
theorem totalCount_eq_sum_lastFiber (r n : ℕ) :
    totalCount (r + 1) n = ∑ j : Fin n, Fintype.card (LastFiber r n j) := by
  classical
  calc
    totalCount (r + 1) n = Fintype.card (History (r + 1) n) := (card_history _ _).symm
    _ = Fintype.card (Σ j : Fin n, LastFiber r n j) :=
      (Fintype.card_congr (Equiv.sigmaFiberEquiv (@lastOutcome r n))).symm
    _ = _ := Fintype.card_sigma

/-- Exactly one one-car preference/history ends at a specified existing spot. -/
theorem card_lastFiber_zero (n : ℕ) (j : Fin n) : Fintype.card (LastFiber 0 n j) = 1 := by
  letI : Unique (LastFiber 0 n j) :=
    { default :=
        ⟨⟨(fun _ => j, fun _ => j), (isParking_one_iff _ _).mpr rfl⟩, rfl⟩
      uniq := by
        rintro ⟨⟨⟨a, p⟩, hp⟩, hj⟩
        have hap : a = p := (isParking_one_iff a p).mp hp
        have hpj : p = fun _ => j := by
          funext i
          have hi : i = Fin.last 0 := by
            apply Fin.ext
            have hiBound := i.isLt
            change (i : ℕ) = 0
            omega
          have hend : p (Fin.last 0) = j := hj
          exact (congrArg p hi).trans hend
        apply Subtype.ext
        apply Subtype.ext
        exact Prod.ext (hap.trans hpj) hpj }
  exact Fintype.card_unique

/-- An additive natural-number balance, with the complement bound proved before
cancelling truncated subtraction. The right side uses the direct preference count. -/
theorem card_lastFiber_balance (r n : ℕ) (j : Fin n) :
    Fintype.card (LastFiber (r + 1) n j) + Fintype.card (LastFiber r n j) =
      totalCount (r + 1) n +
        Fintype.card {H : History (r + 1) n // (lastOutcome H : ℕ) + 1 = (j : ℕ)} := by
  classical
  have hle : Fintype.card (LastFiber r n j) ≤ Fintype.card (History (r + 1) n) :=
    Fintype.card_subtype_le (fun H : History (r + 1) n => lastOutcome H = j)
  have hcompl : Fintype.card {H : History (r + 1) n // lastOutcome H ≠ j} =
      Fintype.card (History (r + 1) n) - Fintype.card (LastFiber r n j) :=
    Fintype.card_subtype_compl (fun H : History (r + 1) n => lastOutcome H = j)
  have hcount := Fintype.card_congr (lastFiberEquivExtensions r n j)
  rw [Fintype.card_sum] at hcount
  have htotal := card_history (r + 1) n
  omega

/-- The first physical spot has no predecessor outcome; no empty-history state is used. -/
theorem card_predecessor_zero {r n : ℕ} (j : Fin n) (hj : (j : ℕ) = 0) :
    Fintype.card {H : History (r + 1) n // (lastOutcome H : ℕ) + 1 = (j : ℕ)} = 0 := by
  letI : IsEmpty {H : History (r + 1) n // (lastOutcome H : ℕ) + 1 = (j : ℕ)} :=
    ⟨fun H => by
      have h := H.2
      omega⟩
  exact Fintype.card_eq_zero

/-- A valid natural successor identifies the predecessor subtype with the
corresponding equality fiber, including at the final physical spot. -/
theorem card_predecessor_of_adj {r n : ℕ} (k j : Fin n)
    (hadj : (k : ℕ) + 1 = (j : ℕ)) :
    Fintype.card {H : History (r + 1) n // (lastOutcome H : ℕ) + 1 = (j : ℕ)} =
      Fintype.card (LastFiber r n k) := by
  classical
  let e : {H : History (r + 1) n // (lastOutcome H : ℕ) + 1 = (j : ℕ)} ≃
      LastFiber r n k :=
    { toFun := fun H => ⟨H.1, by
        apply Fin.ext
        have h := H.2
        omega⟩
      invFun := fun H => ⟨H.1, by
        have h := congrArg Fin.val H.2
        omega⟩
      left_inv := by intro H; rfl
      right_inv := by intro H; rfl }
  exact Fintype.card_congr e

end MeteredParking.OneMeter

#print axioms MeteredParking.OneMeter.lastFiberEquivExtensions
#print axioms MeteredParking.OneMeter.totalCount_eq_sum_lastFiber
#print axioms MeteredParking.OneMeter.card_lastFiber_zero
#print axioms MeteredParking.OneMeter.card_lastFiber_balance
#print axioms MeteredParking.OneMeter.card_predecessor_zero
#print axioms MeteredParking.OneMeter.card_predecessor_of_adj

/-!
## Actual-count series and finite-state elimination

The total series uses the original preference counts. Physical state `p.succ`
uses the actual last-outcome fibers, shifted by `X`; state zero is the zero
series, not an outcome of an empty history. The finite state equations are
eliminated by polynomial ring identities before any inverse is introduced.
-/

namespace MeteredParking.OneMeter

open scoped BigOperators
open PowerSeries

/-- The generating series of the direct successful-preference counts. -/
noncomputable def generatingSeries (n : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk (fun m => (totalCount m n : ℤ))

/-- State zero is virtual; state `p.succ` counts nonempty histories ending at `p`. -/
noncomputable def stateSeries (n : ℕ) : Fin (n + 1) → PowerSeries ℤ := by
  classical
  exact Fin.cons 0 (fun p : Fin n =>
    X * PowerSeries.mk (fun r => (Fintype.card (LastFiber r n p) : ℤ)))

/-- The finite denominator polynomial; it is coerced to a series when needed. -/
noncomputable def denominator (n : ℕ) : Polynomial ℤ :=
  (1 - Polynomial.C (n : ℤ) * Polynomial.X + Polynomial.X ^ 2) *
      (1 + Polynomial.X) ^ n - Polynomial.X ^ (n + 2)

@[simp] theorem coeff_generatingSeries (m n : ℕ) :
    coeff m (generatingSeries n) = (totalCount m n : ℤ) :=
  PowerSeries.coeff_mk m _

@[simp] theorem stateSeries_zero (n : ℕ) : stateSeries n 0 = 0 := by
  simp only [stateSeries, Fin.cons_zero]

@[simp] theorem constantCoeff_stateSeries (n : ℕ) (j : Fin (n + 1)) :
    constantCoeff (stateSeries n j) = 0 := by
  refine Fin.cases ?_ (fun p => ?_) j
  · rw [stateSeries_zero, map_zero]
  · simp only [stateSeries, Fin.cons_succ, map_mul, constantCoeff_X, zero_mul]

@[simp] theorem coeff_stateSeries_succ (r n : ℕ) (p : Fin n) :
    coeff (r + 1) (stateSeries n p.succ) = (Fintype.card (LastFiber r n p) : ℤ) := by
  simp only [stateSeries, Fin.cons_succ, coeff_succ_X_mul, coeff_mk]

private theorem predecessor_card_eq_coeff (r n : ℕ) (p : Fin n) :
    (Fintype.card {H : History (r + 1) n // (lastOutcome H : ℕ) + 1 = (p : ℕ)} : ℤ) =
      coeff (r + 1) (stateSeries n p.castSucc) := by
  classical
  by_cases hp : (p : ℕ) = 0
  · have hcast : p.castSucc = (0 : Fin (n + 1)) := Fin.ext hp
    rw [card_predecessor_zero p hp, hcast, stateSeries_zero]
    simp
  · let k : Fin n := ⟨(p : ℕ) - 1, by
      have hpn := p.isLt
      omega⟩
    have hkp : (k : ℕ) + 1 = (p : ℕ) := by
      change (p : ℕ) - 1 + 1 = (p : ℕ)
      omega
    have hcast : p.castSucc = k.succ := Fin.ext hkp.symm
    rw [card_predecessor_of_adj k p hkp, hcast, coeff_stateSeries_succ]

/-- The nonconstant total series is the sum of the actual physical-state series. -/
theorem generatingSeries_sub_one (n : ℕ) :
    generatingSeries n - 1 = ∑ p : Fin n, stateSeries n p.succ := by
  classical
  apply PowerSeries.ext
  intro m
  cases m with
  | zero => simp [generatingSeries, totalCount_zero]
  | succ r =>
      simp only [map_sub, map_sum, coeff_generatingSeries, coeff_stateSeries_succ,
        coeff_one, Nat.succ_ne_zero, if_false, sub_zero]
      exact_mod_cast totalCount_eq_sum_lastFiber r n

/-- The local series equation follows coefficientwise from the additive natural
cardinality balance, preserving the two tagged preference extensions. -/
theorem stateSeries_step (n : ℕ) (p : Fin n) :
    (1 + X) * stateSeries n p.succ =
      X * generatingSeries n + X * stateSeries n p.castSucc := by
  classical
  apply PowerSeries.ext
  intro m
  cases m with
  | zero =>
      simp only [coeff_zero_eq_constantCoeff, map_mul, map_add, map_one,
        constantCoeff_X, constantCoeff_stateSeries, mul_zero, zero_mul, add_zero]
  | succ r =>
      rw [add_mul, one_mul]
      simp only [map_add, coeff_succ_X_mul, coeff_stateSeries_succ, coeff_generatingSeries]
      cases r with
      | zero =>
          simp [coeff_zero_eq_constantCoeff, card_lastFiber_zero, totalCount_zero]
      | succ r =>
          rw [coeff_stateSeries_succ, ← predecessor_card_eq_coeff]
          exact_mod_cast card_lastFiber_balance r n p

/-- Summing the finite state equations leaves only the final physical state. -/
theorem stateSeries_end (n : ℕ) :
    (1 - C (n : ℤ) * X) * generatingSeries n + X * stateSeries n (Fin.last n) = 1 := by
  classical
  have htel : (∑ p : Fin n, stateSeries n p.castSucc) + stateSeries n (Fin.last n) =
      ∑ p : Fin n, stateSeries n p.succ := by
    calc
      _ = ∑ j : Fin (n + 1), stateSeries n j := (Fin.sum_univ_castSucc _).symm
      _ = stateSeries n 0 + ∑ p : Fin n, stateSeries n p.succ := Fin.sum_univ_succ _
      _ = _ := by rw [stateSeries_zero, zero_add]
  have hsum : (1 + X) * (∑ p : Fin n, stateSeries n p.succ) =
      C (n : ℤ) * (X * generatingSeries n) + X * (∑ p : Fin n, stateSeries n p.castSucc) := by
    calc
      _ = ∑ p : Fin n, (1 + X) * stateSeries n p.succ := Finset.mul_sum _ _ _
      _ = ∑ p : Fin n, (X * generatingSeries n + X * stateSeries n p.castSucc) := by
        apply Finset.sum_congr rfl
        intro p _
        exact stateSeries_step n p
      _ = _ := by
        simp only [Finset.sum_add_distrib, Fin.sum_const, nsmul_eq_mul,
          ← Finset.mul_sum, map_natCast]
        ring
  rw [← generatingSeries_sub_one n] at hsum htel
  linear_combination hsum + X * htel

/-- Bounded induction over the actual state indices eliminates each state
without cancelling or inverting `1 + X`. -/
theorem stateSeries_power (n : ℕ) (j : Fin (n + 1)) :
    (1 + X) ^ (j : ℕ) * stateSeries n j =
      X * generatingSeries n * ((1 + X) ^ (j : ℕ) - X ^ (j : ℕ)) := by
  have h : ∀ k : ℕ, ∀ hk : k < n + 1,
      (1 + X) ^ k * stateSeries n ⟨k, hk⟩ =
        X * generatingSeries n * ((1 + X) ^ k - X ^ k) := by
    intro k
    induction k with
    | zero =>
        intro hk
        have hz : (⟨0, hk⟩ : Fin (n + 1)) = 0 := Fin.ext rfl
        simp only [hz, stateSeries_zero, pow_zero, mul_zero, sub_self]
    | succ k ih =>
        intro hk
        let p : Fin n := ⟨k, by omega⟩
        have hi : (1 + X) ^ k * stateSeries n p.castSucc =
            X * generatingSeries n * ((1 + X) ^ k - X ^ k) := ih (by omega)
        have hs := stateSeries_step n p
        change (1 + X) ^ (k + 1) * stateSeries n p.succ =
          X * generatingSeries n * ((1 + X) ^ (k + 1) - X ^ (k + 1))
        calc
          (1 + X) ^ (k + 1) * stateSeries n p.succ =
              (1 + X) ^ k * ((1 + X) * stateSeries n p.succ) := by
            rw [pow_succ, mul_assoc]
          _ = (1 + X) ^ k * (X * generatingSeries n + X * stateSeries n p.castSucc) :=
            congrArg (fun F : PowerSeries ℤ => (1 + X) ^ k * F) hs
          _ = X * generatingSeries n * (1 + X) ^ k +
              X * ((1 + X) ^ k * stateSeries n p.castSucc) := by ring
          _ = X * generatingSeries n * (1 + X) ^ k +
              X * (X * generatingSeries n * ((1 + X) ^ k - X ^ k)) := by rw [hi]
          _ = X * generatingSeries n * ((1 + X) ^ (k + 1) - X ^ (k + 1)) := by
            simp only [pow_succ]
            ring
  exact h (j : ℕ) j.isLt

/-- The denominator identity is obtained from the actual-count state equations
by finite elimination. It is not an assumed scalar recurrence. -/
theorem generatingSeries_mul_denominator (n : ℕ) :
    (denominator n : PowerSeries ℤ) * generatingSeries n = (1 + X) ^ n := by
  have hend := stateSeries_end n
  have hpower : (1 + X) ^ n * stateSeries n (Fin.last n) =
      X * generatingSeries n * ((1 + X) ^ n - X ^ n) :=
    stateSeries_power n (Fin.last n)
  simp only [denominator, Polynomial.coe_sub, Polynomial.coe_mul, Polynomial.coe_add,
    Polynomial.coe_one, Polynomial.coe_C, Polynomial.coe_X, Polynomial.coe_pow]
  rw [pow_add]
  linear_combination (1 + X) ^ n * hend - X * hpower

/-- The denominator has constant term one, so the unit inverse is genuine. -/
@[simp] theorem denominator_constantCoeff (n : ℕ) :
    constantCoeff (denominator n : PowerSeries ℤ) = 1 := by
  simp only [denominator, Polynomial.coe_sub, Polynomial.coe_mul, Polynomial.coe_add,
    Polynomial.coe_one, Polynomial.coe_C, Polynomial.coe_X, Polynomial.coe_pow]
  simp

/-- The formal-series quotient over the integers. The inverse identities use
the proved constant coefficient, with no field division or convergence premise. -/
theorem generatingSeries_eq_quotient (n : ℕ) :
    generatingSeries n =
      (1 + X) ^ n * PowerSeries.invOfUnit (denominator n : PowerSeries ℤ) (1 : ℤˣ) := by
  have hinv : PowerSeries.invOfUnit (denominator n : PowerSeries ℤ) (1 : ℤˣ) *
      (denominator n : PowerSeries ℤ) = 1 :=
    PowerSeries.invOfUnit_mul _ _ (denominator_constantCoeff n)
  calc
    generatingSeries n =
        (PowerSeries.invOfUnit (denominator n : PowerSeries ℤ) (1 : ℤˣ) *
          (denominator n : PowerSeries ℤ)) * generatingSeries n := by rw [hinv, one_mul]
    _ = PowerSeries.invOfUnit (denominator n : PowerSeries ℤ) (1 : ℤˣ) *
        ((denominator n : PowerSeries ℤ) * generatingSeries n) := mul_assoc _ _ _
    _ = (1 + X) ^ n * PowerSeries.invOfUnit (denominator n : PowerSeries ℤ) (1 : ℤˣ) := by
      rw [generatingSeries_mul_denominator, mul_comm]

end MeteredParking.OneMeter

#print axioms MeteredParking.OneMeter.coeff_generatingSeries
#print axioms MeteredParking.OneMeter.stateSeries_zero
#print axioms MeteredParking.OneMeter.constantCoeff_stateSeries
#print axioms MeteredParking.OneMeter.coeff_stateSeries_succ
#print axioms MeteredParking.OneMeter.generatingSeries_sub_one
#print axioms MeteredParking.OneMeter.stateSeries_step
#print axioms MeteredParking.OneMeter.stateSeries_end
#print axioms MeteredParking.OneMeter.stateSeries_power
#print axioms MeteredParking.OneMeter.generatingSeries_mul_denominator
#print axioms MeteredParking.OneMeter.denominator_constantCoeff
#print axioms MeteredParking.OneMeter.generatingSeries_eq_quotient
