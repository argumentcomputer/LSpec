module
public import LSpec.Runner

/-!
# Formal Correctness of `TestFilter`, `filterTree`, and `listTests`

Direct kernel-checked theorems on the executable functions in `LSpec.Runner`:
- Soundness & completeness of `filterTree` relative to `listTests`
- Empty filter identity and exclusion dominance
- Exact `none` characterization (no matching leaves)
- Non-emptiness of every surviving `withResource` / `group` subtree (filtered-out
  resources are never acquired)
- Idempotence of `filterTree`
-/

namespace LSpec.Proofs
public section

open LSpec

private theorem array_toList_sizeOf_lt [SizeOf α] (a : Array α) :
    sizeOf a.toList < sizeOf a := by
  cases a; simp

private theorem array_any_empty {α : Type _} (a : Array α) (p : α → Bool)
    (h : a.isEmpty = true) : a.any p = false := by
  cases a with
  | mk xs =>
    cases xs with
    | nil => simp
    | cons _ _ => simp [Array.isEmpty] at h

/-! ## `TestFilter.matchesTest` Properties -/

theorem matchesTest_empty (f : TestFilter) (h : f.isEmpty = true)
    (path tags : Array String) : f.matchesTest path tags = true := by
  simp only [TestFilter.isEmpty, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hInc, hEx⟩, hExc⟩, hIT⟩, hET⟩ := h
  simp only [TestFilter.matchesTest, hInc, hEx, hIT]
  rw [array_any_empty f.excludes _ hExc, array_any_empty f.excludeTags _ hET]
  simp

theorem matchesTest_excludeTag_rejects (f : TestFilter) (path tags : Array String)
    {t : String} (htf : t ∈ f.excludeTags.toList) (htt : t ∈ tags.toList) :
    f.matchesTest path tags = false := by
  simp only [TestFilter.matchesTest]
  have hContains : tags.contains t = true := by
    rw [Array.contains_iff_exists_mem_beq]
    exact ⟨t, Array.mem_def.mpr htt, beq_self_eq_true t⟩
  have hAny : f.excludeTags.any (tags.contains ·) = true := by
    rw [Array.any_eq_true]
    have hMem : t ∈ f.excludeTags := Array.mem_def.mpr htf
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hMem
    exact ⟨i, hi, hContains⟩
  rw [hAny]
  simp

theorem matchesTest_exclude_rejects (f : TestFilter) (path tags : Array String)
    {pat : String} (hpf : pat ∈ f.excludes.toList)
    (hSub : containsSubstr ("/".intercalate path.toList) pat = true) :
    f.matchesTest path tags = false := by
  simp only [TestFilter.matchesTest]
  have hAny : f.excludes.any (containsSubstr ("/".intercalate path.toList) ·) = true := by
    rw [Array.any_eq_true]
    have hMem : pat ∈ f.excludes := Array.mem_def.mpr hpf
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hMem
    exact ⟨i, hi, hSub⟩
  rw [hAny]
  simp

/-! ## `filterTree` Soundness & Completeness -/

theorem filterTree_empty (f : TestFilter) (h : f.isEmpty = true) (t : TestTree) :
    filterTree f t = some t := by
  simp [filterTree, h]

mutual

theorem listTestsGo_filterTreeGo (f : TestFilter) (path tags : Array String)
    (mode : ExecutionMode) (t : TestTree) :
    ((filterTreeGo f path tags t).map (listTestsGo path tags mode)).getD [] =
      (listTestsGo path tags mode t).filter (fun lt => f.matchesTest lt.path lt.tags) := by
  cases t with
  | leaf name leafTags exec =>
    simp only [filterTreeGo, listTestsGo]
    cases hM : f.matchesTest (if name.isEmpty then path else path.push name) (tags ++ leafTags) with
    | true => simp only [ite_true, Option.map_some, Option.getD_some, listTestsGo, List.filter, hM]
    | false => simp only [Bool.false_eq_true, ite_false, Option.map_none, Option.getD_none, List.filter, hM]
  | group name children =>
    simp only [filterTreeGo, listTestsGo]
    have ih := listTestsChildren_filterTreeChildren f
      (if name.isEmpty then path else path.push name) tags mode children.toList
    cases hKept : filterTreeChildren f (if name.isEmpty then path else path.push name) tags children.toList with
    | nil =>
      rw [hKept] at ih
      simp only [listTestsChildren] at ih
      simp [ih]
    | cons c cs =>
      rw [hKept] at ih
      simp only [List.isEmpty_cons, Bool.false_eq_true, ite_false, Option.map_some,
        Option.getD_some, listTestsGo]
      exact ih
  | withMode m child =>
    have ih := listTestsGo_filterTreeGo f path tags (ExecutionMode.combine mode m) child
    simp only [filterTreeGo, listTestsGo]
    cases h : filterTreeGo f path tags child with
    | none => rw [h] at ih; simpa using ih
    | some c' => rw [h] at ih; simpa [listTestsGo] using ih
  | withTags more child =>
    have ih := listTestsGo_filterTreeGo f path (tags ++ more) mode child
    simp only [filterTreeGo, listTestsGo]
    cases h : filterTreeGo f path (tags ++ more) child with
    | none => rw [h] at ih; simpa using ih
    | some c' => rw [h] at ih; simpa [listTestsGo] using ih
  | withOptions optFn child =>
    have ih := listTestsGo_filterTreeGo f path tags mode child
    simp only [filterTreeGo, listTestsGo]
    cases h : filterTreeGo f path tags child with
    | none => rw [h] at ih; simpa using ih
    | some c' => rw [h] at ih; simpa [listTestsGo] using ih
  | aroundEach wrap child =>
    have ih := listTestsGo_filterTreeGo f path tags mode child
    simp only [filterTreeGo, listTestsGo]
    cases h : filterTreeGo f path tags child with
    | none => rw [h] at ih; simpa using ih
    | some c' => rw [h] at ih; simpa [listTestsGo] using ih
  | withResource desc acq child =>
    have ih := listTestsGo_filterTreeGo f path tags mode child
    simp only [filterTreeGo, listTestsGo]
    cases h : filterTreeGo f path tags child with
    | none => rw [h] at ih; simpa using ih
    | some c' => rw [h] at ih; simpa [listTestsGo] using ih
termination_by sizeOf t
decreasing_by all_goals (simp_wf; first | done | omega | (have := array_toList_sizeOf_lt children; omega))

theorem listTestsChildren_filterTreeChildren (f : TestFilter) (path tags : Array String)
    (mode : ExecutionMode) (cs : List TestTree) :
    listTestsChildren path tags mode (filterTreeChildren f path tags cs) =
      (listTestsChildren path tags mode cs).filter (fun lt => f.matchesTest lt.path lt.tags) := by
  cases cs with
  | nil => simp [filterTreeChildren, listTestsChildren]
  | cons c rest =>
    have ihHead := listTestsGo_filterTreeGo f path tags mode c
    have ihTail := listTestsChildren_filterTreeChildren f path tags mode rest
    simp only [filterTreeChildren, listTestsChildren, List.filter_append]
    cases h : filterTreeGo f path tags c with
    | none =>
      rw [h] at ihHead
      simp only [Option.map_none, Option.getD_none] at ihHead
      rw [← ihHead, List.nil_append, ihTail]
    | some c' =>
      rw [h] at ihHead
      simp only [Option.map_some, Option.getD_some] at ihHead
      simp only [listTestsChildren, ihHead, ihTail]
termination_by sizeOf cs
decreasing_by all_goals (simp_wf; omega)

end

/-- **Main Filter Soundness & Completeness Theorem**:
    Listing tests after `filterTree f t` yields the exact declaration-ordered
    subsequence of `listTests t` satisfying `f.matchesTest`. -/
theorem listTests_filterTree_eq (f : TestFilter) (t : TestTree)
    (mode : ExecutionMode := .parallel) :
    ((filterTree f t).map (listTests · mode)).getD #[] =
      (listTests t mode).filter (fun lt => f.matchesTest lt.path lt.tags) := by
  unfold filterTree listTests
  by_cases hEmpty : f.isEmpty = true
  · simp only [hEmpty, ite_true, Option.map_some, Option.getD_some]
    apply Array.ext'
    simp only [Array.toList_filter]
    symm
    apply List.filter_eq_self.mpr
    intro lt _
    exact matchesTest_empty f hEmpty lt.path lt.tags
  · have hFalse : f.isEmpty = false := Bool.eq_false_iff.mpr hEmpty
    simp only [hFalse, Bool.false_eq_true, ite_false]
    have hGo := listTestsGo_filterTreeGo f #[] #[] mode t
    cases h : filterTreeGo f #[] #[] t with
    | none =>
      rw [h] at hGo
      simp only [Option.map_none, Option.getD_none] at hGo
      apply Array.ext'
      simp [← hGo]
    | some t' =>
      rw [h] at hGo
      simp only [Option.map_some, Option.getD_some] at hGo
      apply Array.ext'
      simp [hGo]

/-! ## Non-emptiness & Zero Filtered-Out Resource Acquisition -/

mutual

/-- Structural predicate stating that every `.group` and `.withResource` node
    in `t` contains at least one leaf (so no empty resource block can be acquired). -/
def NoEmptyScopes : TestTree → Prop
  | .leaf _ _ _ => True
  | .group _ children => children.toList ≠ [] ∧ NoEmptyScopesChildren children.toList
  | .withMode _ child => NoEmptyScopes child
  | .withTags _ child => NoEmptyScopes child
  | .withOptions _ child => NoEmptyScopes child
  | .aroundEach _ child => NoEmptyScopes child
  | .withResource _ _ child => NoEmptyScopes child
termination_by t => sizeOf t
decreasing_by all_goals (simp_wf; first | done | omega | (have := array_toList_sizeOf_lt children; omega))

def NoEmptyScopesChildren : List TestTree → Prop
  | [] => True
  | c :: cs => NoEmptyScopes c ∧ NoEmptyScopesChildren cs
termination_by cs => sizeOf cs
decreasing_by all_goals (simp_wf; omega)

end

theorem listTestsGo_nonempty_of_noEmptyScopes (path tags : Array String) (mode : ExecutionMode) :
    (t : TestTree) → NoEmptyScopes t → listTestsGo path tags mode t ≠ []
  | .leaf name leafTags exec, _ => by simp [listTestsGo]
  | .group name children, h => by
    simp only [NoEmptyScopes] at h
    obtain ⟨hNe, hKids⟩ := h
    cases hList : children.toList with
    | nil => exact absurd hList hNe
    | cons c cs =>
      rw [hList] at hKids
      simp only [NoEmptyScopesChildren] at hKids
      have hHead := listTestsGo_nonempty_of_noEmptyScopes
        (if name.isEmpty then path else path.push name) tags mode c hKids.1
      simp only [listTestsGo, hList, listTestsChildren]
      intro hApp
      exact hHead (List.append_eq_nil_iff.mp hApp).1
  | .withMode m child, h => by
    simp only [NoEmptyScopes] at h
    simp only [listTestsGo]
    exact listTestsGo_nonempty_of_noEmptyScopes path tags (ExecutionMode.combine mode m) child h
  | .withTags more child, h => by
    simp only [NoEmptyScopes] at h
    simp only [listTestsGo]
    exact listTestsGo_nonempty_of_noEmptyScopes path (tags ++ more) mode child h
  | .withOptions _ child, h => by
    simp only [NoEmptyScopes] at h
    simp only [listTestsGo]
    exact listTestsGo_nonempty_of_noEmptyScopes path tags mode child h
  | .aroundEach _ child, h => by
    simp only [NoEmptyScopes] at h
    simp only [listTestsGo]
    exact listTestsGo_nonempty_of_noEmptyScopes path tags mode child h
  | .withResource _ _ child, h => by
    simp only [NoEmptyScopes] at h
    simp only [listTestsGo]
    exact listTestsGo_nonempty_of_noEmptyScopes path tags mode child h
termination_by t => sizeOf t
decreasing_by
  all_goals
    simp_wf
    first
      | done
      | omega
      | (have h1 := array_toList_sizeOf_lt children; rw [hList] at h1; simp at h1; omega)

mutual

theorem filterTreeGo_noEmptyScopes (f : TestFilter) (path tags : Array String) :
    (t : TestTree) → (t' : TestTree) → filterTreeGo f path tags t = some t' → NoEmptyScopes t'
  | .leaf name leafTags exec, t', h => by
    simp only [filterTreeGo] at h
    cases hM : f.matchesTest (if name.isEmpty then path else path.push name) (tags ++ leafTags) with
    | true =>
      rw [hM] at h
      simp only [ite_true, Option.some.injEq] at h
      subst h
      simp [NoEmptyScopes]
    | false =>
      rw [hM] at h
      simp at h
  | .group name children, t', h => by
    simp only [filterTreeGo] at h
    cases hKept : filterTreeChildren f (if name.isEmpty then path else path.push name) tags children.toList with
    | nil => rw [hKept] at h; simp at h
    | cons c cs =>
      rw [hKept] at h
      simp only [List.isEmpty_cons, Bool.false_eq_true, ite_false, Option.some.injEq] at h
      subst h
      have hKids := filterTreeChildren_noEmptyScopes f
        (if name.isEmpty then path else path.push name) tags children.toList
      rw [hKept] at hKids
      simp [NoEmptyScopes, hKids]
  | .withMode m child, t', h => by
    simp only [filterTreeGo, Option.map_eq_some_iff] at h
    obtain ⟨c', hc', rfl⟩ := h
    simp only [NoEmptyScopes]
    exact filterTreeGo_noEmptyScopes f path tags child c' hc'
  | .withTags more child, t', h => by
    simp only [filterTreeGo, Option.map_eq_some_iff] at h
    obtain ⟨c', hc', rfl⟩ := h
    simp only [NoEmptyScopes]
    exact filterTreeGo_noEmptyScopes f path (tags ++ more) child c' hc'
  | .withOptions optFn child, t', h => by
    simp only [filterTreeGo, Option.map_eq_some_iff] at h
    obtain ⟨c', hc', rfl⟩ := h
    simp only [NoEmptyScopes]
    exact filterTreeGo_noEmptyScopes f path tags child c' hc'
  | .aroundEach wrap child, t', h => by
    simp only [filterTreeGo, Option.map_eq_some_iff] at h
    obtain ⟨c', hc', rfl⟩ := h
    simp only [NoEmptyScopes]
    exact filterTreeGo_noEmptyScopes f path tags child c' hc'
  | .withResource desc acq child, t', h => by
    simp only [filterTreeGo, Option.map_eq_some_iff] at h
    obtain ⟨c', hc', rfl⟩ := h
    simp only [NoEmptyScopes]
    exact filterTreeGo_noEmptyScopes f path tags child c' hc'
termination_by t => sizeOf t
decreasing_by all_goals (simp_wf; first | done | omega | (have := array_toList_sizeOf_lt children; omega))

theorem filterTreeChildren_noEmptyScopes (f : TestFilter) (path tags : Array String)
    (cs : List TestTree) :
    NoEmptyScopesChildren (filterTreeChildren f path tags cs) := by
  cases cs with
  | nil => simp [filterTreeChildren, NoEmptyScopesChildren]
  | cons c rest =>
    simp only [filterTreeChildren]
    cases h : filterTreeGo f path tags c with
    | none => exact filterTreeChildren_noEmptyScopes f path tags rest
    | some c' =>
      simp only [NoEmptyScopesChildren]
      exact ⟨filterTreeGo_noEmptyScopes f path tags c c' h,
             filterTreeChildren_noEmptyScopes f path tags rest⟩
termination_by sizeOf cs
decreasing_by all_goals (simp_wf; omega)

end

/-- When `filterTreeGo` returns `some t'`, `t'` contains at least one matching leaf. -/
theorem filterTreeGo_some_nonempty (f : TestFilter) (path tags : Array String)
    (mode : ExecutionMode) (t t' : TestTree) (h : filterTreeGo f path tags t = some t') :
    listTestsGo path tags mode t' ≠ [] :=
  listTestsGo_nonempty_of_noEmptyScopes path tags mode t'
    (filterTreeGo_noEmptyScopes f path tags t t' h)

/-- Exact characterization of when `filterTreeGo` prunes a subtree completely. -/
theorem filterTreeGo_eq_none_iff (f : TestFilter) (path tags : Array String)
    (mode : ExecutionMode) (t : TestTree) :
    filterTreeGo f path tags t = none ↔
      ∀ lt ∈ listTestsGo path tags mode t, f.matchesTest lt.path lt.tags = false := by
  have hList := listTestsGo_filterTreeGo f path tags mode t
  constructor
  · intro hNone
    rw [hNone] at hList
    simp only [Option.map_none, Option.getD_none] at hList
    intro lt hMem
    cases hMatch : f.matchesTest lt.path lt.tags with
    | false => rfl
    | true =>
      have hIn : lt ∈ (listTestsGo path tags mode t).filter (fun lt => f.matchesTest lt.path lt.tags) :=
        List.mem_filter.mpr ⟨hMem, hMatch⟩
      rw [← hList] at hIn
      cases hIn
  · intro hAllFalse
    cases hRes : filterTreeGo f path tags t with
    | none => rfl
    | some t' =>
      have hNonEmpty := filterTreeGo_some_nonempty f path tags mode t t' hRes
      rw [hRes] at hList
      simp only [Option.map_some, Option.getD_some] at hList
      have hFilterNil : (listTestsGo path tags mode t).filter (fun lt => f.matchesTest lt.path lt.tags) = [] := by
        rw [List.filter_eq_nil_iff]
        intro lt hMem
        simp [hAllFalse lt hMem]
      rw [hFilterNil] at hList
      exact absurd hList hNonEmpty

/-- For any non-empty filter, `filterTree f t = none` iff no leaf in `t` matches `f`.
    In particular, `runTree` never executes `compilePlan` or acquires any `withResource`
    when no leaf matches. -/
theorem filterTree_eq_none_iff (f : TestFilter) (hNe : f.isEmpty = false)
    (t : TestTree) (mode : ExecutionMode := .parallel) :
    filterTree f t = none ↔
      ∀ lt ∈ (listTests t mode).toList, f.matchesTest lt.path lt.tags = false := by
  simp only [filterTree, hNe, Bool.false_eq_true, ite_false, listTests, List.toList_toArray]
  exact filterTreeGo_eq_none_iff f #[] #[] mode t

/-- Every surviving `.withResource` in a filtered tree has at least one matching leaf. -/
theorem filterTree_withResource_has_leaf (f : TestFilter) (hNe : f.isEmpty = false)
    (t : TestTree) {desc : String} {acq : IO (IO Unit)} {child : TestTree}
    (h : filterTree f t = some (.withResource desc acq child))
    (mode : ExecutionMode := .parallel) :
    (listTests child mode).size > 0 := by
  simp only [filterTree, hNe, Bool.false_eq_true, ite_false] at h
  have hNeList := filterTreeGo_some_nonempty f #[] #[] mode t (.withResource desc acq child) h
  simp only [listTestsGo] at hNeList
  simp only [listTests, List.size_toArray]
  exact List.length_pos_iff.mpr hNeList

/-! ## `filterTree` Idempotence -/

mutual

theorem filterTreeGo_idempotent (f : TestFilter) (path tags : Array String) (t : TestTree) :
    (filterTreeGo f path tags t).bind (filterTreeGo f path tags) = filterTreeGo f path tags t := by
  cases t with
  | leaf name leafTags exec =>
    simp only [filterTreeGo]
    cases hM : f.matchesTest (if name.isEmpty then path else path.push name) (tags ++ leafTags) with
    | true =>
      simp only [ite_true, Option.bind_some, filterTreeGo, hM]
    | false =>
      simp only [Bool.false_eq_true, ite_false, Option.bind_none]
  | group name children =>
    simp only [filterTreeGo]
    have ih := filterTreeChildren_idempotent f
      (if name.isEmpty then path else path.push name) tags children.toList
    cases hKept : filterTreeChildren f (if name.isEmpty then path else path.push name) tags children.toList with
    | nil => simp
    | cons c cs =>
      rw [hKept] at ih
      simp only [List.isEmpty_cons, Bool.false_eq_true, ite_false, Option.bind_some,
        filterTreeGo, ih]
  | withMode m child =>
    have ih := filterTreeGo_idempotent f path tags child
    simp only [filterTreeGo]
    cases h : filterTreeGo f path tags child with
    | none => simp
    | some c' =>
      rw [h] at ih
      simp only [Option.bind_some] at ih
      simp [filterTreeGo, ih]
  | withTags more child =>
    have ih := filterTreeGo_idempotent f path (tags ++ more) child
    simp only [filterTreeGo]
    cases h : filterTreeGo f path (tags ++ more) child with
    | none => simp
    | some c' =>
      rw [h] at ih
      simp only [Option.bind_some] at ih
      simp [filterTreeGo, ih]
  | withOptions optFn child =>
    have ih := filterTreeGo_idempotent f path tags child
    simp only [filterTreeGo]
    cases h : filterTreeGo f path tags child with
    | none => simp
    | some c' =>
      rw [h] at ih
      simp only [Option.bind_some] at ih
      simp [filterTreeGo, ih]
  | aroundEach wrap child =>
    have ih := filterTreeGo_idempotent f path tags child
    simp only [filterTreeGo]
    cases h : filterTreeGo f path tags child with
    | none => simp
    | some c' =>
      rw [h] at ih
      simp only [Option.bind_some] at ih
      simp [filterTreeGo, ih]
  | withResource desc acq child =>
    have ih := filterTreeGo_idempotent f path tags child
    simp only [filterTreeGo]
    cases h : filterTreeGo f path tags child with
    | none => simp
    | some c' =>
      rw [h] at ih
      simp only [Option.bind_some] at ih
      simp [filterTreeGo, ih]
termination_by sizeOf t
decreasing_by all_goals (simp_wf; first | done | omega | (have := array_toList_sizeOf_lt children; omega))

theorem filterTreeChildren_idempotent (f : TestFilter) (path tags : Array String)
    (cs : List TestTree) :
    filterTreeChildren f path tags (filterTreeChildren f path tags cs) =
      filterTreeChildren f path tags cs := by
  cases cs with
  | nil => simp [filterTreeChildren]
  | cons c rest =>
    have ihHead := filterTreeGo_idempotent f path tags c
    have ihTail := filterTreeChildren_idempotent f path tags rest
    simp only [filterTreeChildren]
    cases h : filterTreeGo f path tags c with
    | none => exact ihTail
    | some c' =>
      rw [h] at ihHead
      simp only [Option.bind_some] at ihHead
      simp only [filterTreeChildren, ihHead, ihTail]
termination_by sizeOf cs
decreasing_by all_goals (simp_wf; omega)

end

/-- Filtering twice with the same `TestFilter` is identical to filtering once. -/
theorem filterTree_idempotent (f : TestFilter) (t : TestTree) :
    (filterTree f t).bind (filterTree f) = filterTree f t := by
  unfold filterTree
  by_cases hEmpty : f.isEmpty = true
  · simp [hEmpty]
  · have hFalse : f.isEmpty = false := Bool.eq_false_iff.mpr hEmpty
    simp only [hFalse, Bool.false_eq_true, ite_false]
    exact filterTreeGo_idempotent f #[] #[] t

end
end LSpec.Proofs
