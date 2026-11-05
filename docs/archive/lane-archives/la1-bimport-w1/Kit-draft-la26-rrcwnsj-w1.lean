/-! # Kit-draft — lane la26-rrcwnsj-w1 (`RRCWNSJ_p26`, LA26:829 @8c003d0d)

NOT landed: the target is BLOCKED (see DELIVERY.md §0/§3), so per the lane
contract this block stays out of the kit and the target body keeps its
original single `sorry`.

What this block is: the **verified reduction step** of the HOL body
`RRCWNSJ.hl:248-273`. It shows that, under `MMsV39 s v` and `3 < s.k`, the
goal `scsGeneric v` follows from `¬Circular` (`JKQEWGV2_p23`) through the
`CIZMRRH` generic/circular/lunar trichotomy (LA3) applied to the fan bridge
`localFan_p3.of_LocalFan_noIso`. The remaining obligation is exactly one
mathematical statement:

  `hnoLunar : ¬ ∃ v' w : V3, Lunar v' w (Set.range v)
      (Set.range fun i : ℕ => ({v i, v (i + 1)} : Set V3))`

HOL proves `hnoLunar` by the 624-line case bash RRCWNSJ.hl:274-861, whose
norm/ears inputs are `ODXLSTCv2` (HOL hits :345, :615) and `IMJXPHRv2`
(HOL hits :511, :802). Lean twins in LocalAuto1 (`ODXLSTCv2_concl` :2917,
`IMJXPHRv2_concl` :2928) are `sorryAx` at HEAD; the clean forms
(`ODXLSTCv2_p28` LA28:8077, `IMJXPHRv2_p28` LA28:8057) are outside
LocalAuto26's import closure (`#check` = unknown identifier).

Compile evidence for this block: whole-file `lean LocalAuto26.lean` RC=0,
0 errors, `#print axioms w5sgd_generic_of_no_lunar_p26` =
`[propext, choice, Quot.sound]` (logs work3.log / ax1.log).
-/

/-- Reduction skeleton for `RRCWNSJ` (RRCWNSJ.hl:248), lane
la26-rrcwnsj-w1 feasibility probe: under `MMs` the realisation is not circular
(`JKQEWGV2_p23`), and the `CIZMRRH` trichotomy of the local fan (LA3) reduces
`scsGeneric` to the single no-lunar-pair obligation `hnoLunar`.
The HOL body (RRCWNSJ.hl:248-861) proves `hnoLunar` by a giant k=6 lunar case
bash whose norm/ears inputs come from the minimality engines `ODXLSTCv2_concl`
and `IMJXPHRv2_concl` (LocalAuto1:2917/2928, both still `sorry` at this HEAD),
which is why the target itself remains pending. -/
private theorem w5sgd_generic_of_no_lunar_p26 (s : ScsV39) (v : ℕ → V3)
    (hs : isScsV39 s) (hv : MMsV39 s v) (hk : 3 < s.k)
    (hnoLunar : ¬ ∃ v' w : V3, Lunar v' w (Set.range v)
      (Set.range fun i : ℕ => ({v i, v (i + 1)} : Set V3))) :
    scsGeneric v := by
  set V : Set V3 := Set.range v with hV
  set E : Set (Set V3) := Set.range fun i : ℕ => ({v i, v (i + 1)} : Set V3) with hE
  set FF : Set (V3 × V3) := Set.range fun i : ℕ => (v i, v (i + 1)) with hFF
  have hBB : BBsV39 s v := w5sg_mms_bbs_p26 s v hv
  have hta : taustarV39 s v < 0 := w5sg_mms_taustar_neg_p26 s v hv
  have hncV : ¬ Circular (Set.range v)
      (Set.range fun i : ℕ => ({v i, v (i + 1)} : Set V3)) := by
    rw [← Set.image_univ (f := fun i : ℕ => ({v i, v (i + 1)} : Set V3))]
    exact JKQEWGV2_p23 s v hs hk hBB hta
  have hnc : ¬ Circular V E := by
    rw [hV, hE]
    exact hncV
  have hclf : ConvexLocalFan V E FF := w5sg_bbs_convexlocalfan_p26 s s.k v hk rfl hBB
  obtain ⟨hfan, x, hx, hFFeq, hDih, h2reg⟩ := hclf.1
  have hlf : LocalFan V E FF := ⟨hfan, x, hx, hFFeq, hDih, h2reg⟩
  have hlf3 : localFan_p3 V E FF :=
    localFan_p3.of_LocalFan_noIso hlf (w5sg_hedge_p26 h2reg)
  rcases CIZMRRH hlf3 with hgen | hcirc | hlun
  · simpa only [scsGeneric, Generic, generic_p3, ← hV, ← hE] using hgen.1
  · exact absurd (by simpa only [circular_p3, Circular] using hcirc.1) hnc
  · obtain ⟨v', w, hlun'⟩ := hlun.1
    exact absurd ⟨v', w,
      (w5sg_lunar_p3_p26 (V := V) (E := E) (a := v') (b := w)).mp hlun'⟩ hnoLunar
