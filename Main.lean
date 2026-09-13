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
